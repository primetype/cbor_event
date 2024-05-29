//! CBOR deserialisation tooling

#[cfg(feature = "alloc")]
use alloc::collections::BTreeMap;
#[cfg(feature = "alloc")]
use alloc::string::String;
#[cfg(feature = "alloc")]
use alloc::string::ToString;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use core::fmt::{Display, Formatter};
use error::Error;
use len::{Len, LenSz, StringLenSz, Sz};
use result::Result;
use types::{Special, Type};

pub trait Deserialize<'a>: Sized {
    /// method to implement to deserialise an object from the given
    /// `Deserializer`.
    fn deserialize(reader: &mut Deserializer<'a>) -> Result<Self>;
}

impl<'a> Deserialize<'a> for u8 {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        let n = raw.unsigned_integer()?;
        if n > u8::MAX as u64 {
            Err(Error::ExpectedU8)
        } else {
            Ok(n as Self)
        }
    }
}

impl<'a> Deserialize<'a> for u16 {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        let n = raw.unsigned_integer()?;
        if n > u16::MAX as u64 {
            Err(Error::ExpectedU16)
        } else {
            Ok(n as Self)
        }
    }
}

impl<'a> Deserialize<'a> for u32 {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        let n = raw.unsigned_integer()?;
        if n > u32::MAX as u64 {
            Err(Error::ExpectedU32)
        } else {
            Ok(n as Self)
        }
    }
}

impl<'a> Deserialize<'a> for u64 {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        raw.unsigned_integer()
    }
}

impl<'a> Deserialize<'a> for bool {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        raw.bool()
    }
}

impl<'a> Deserialize<'a> for f32 {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        raw.float().map(|f| f as f32)
    }
}

impl<'a> Deserialize<'a> for f64 {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        raw.float()
    }
}

impl<'a> Deserialize<'a> for &'a str {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        raw.text()
    }
}

#[cfg(feature = "alloc")]
impl<'a> Deserialize<'a> for String {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        raw.text().map(move |s| s.to_string())
    }
}

#[cfg(feature = "alloc")]
impl<'a, T: Deserialize<'a>> Deserialize<'a> for Vec<T> {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        let mut vec = Vec::new();
        raw.array_with(|raw| {
            vec.push(Deserialize::deserialize(raw)?);
            Ok(())
        })?;
        Ok(vec)
    }
}
#[cfg(feature = "alloc")]
impl<'a, K: Deserialize<'a> + Ord, V: Deserialize<'a>> Deserialize<'a> for BTreeMap<K, V> {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        let mut vec = BTreeMap::new();
        raw.map_with(|raw| {
            let k = Deserialize::deserialize(raw)?;
            let v = Deserialize::deserialize(raw)?;
            vec.insert(k, v);
            Ok(())
        })?;
        Ok(vec)
    }
}

impl<'a, T: Deserialize<'a>> Deserialize<'a> for Option<T> {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<Self> {
        match raw.array()? {
            Len::Len(0) => Ok(None),
            Len::Len(1) => Ok(Some(raw.deserialize()?)),
            len => Err(Error::CustomError(
                format_args!("Invalid Option<T>: received array of {:?} elements", len)
                    .as_str()
                    .unwrap(),
            )),
        }
    }
}

/// [`Deserialize`]: ./trait.Deserialize.html
/// [`Error`]: ../enum.Error.html
/// [`Type`]: ../enum.Type.html
/// [`Bytes`]: ../struct.Bytes.html
/// [`cbor_type`]: #method.cbor_type
/// [`cbor_len`]: #method.cbor_len
/// [`Len`]: ../enum.Len.html
///
/// `Deserializer` represents a chunk of bytes believed to be cbor object.
/// The validity of the cbor bytes is known only when trying
/// to get meaningful cbor objects from it.
///
/// # Examples
///
/// If you already know the CBOR Primary [`Type`] you are expecting, you
/// can efficiently use the appropriate commands:
///
/// ```
/// use cbor_event::de::*;
///
/// let vec = vec![0x18, 0x40];
/// let mut raw = Deserializer::from(vec);
///
/// assert!(raw.unsigned_integer().is_ok());
/// ```
///
/// ```
/// use cbor_event::de::*;
///
/// let vec = vec![0x18, 0x40];
/// let mut raw = Deserializer::from(vec);
///
/// assert!(raw.array().is_err());
/// ```
///
/// If you don't know the [`Type`] and are only analyzing the structure, you
/// can use [`cbor_type`] to get the type of the next object to parse.
///
/// # Error
///
/// When deserialising from `Deserializer` it is possible to see the following
/// [`Error`]s:
///
/// - `Error::NotEnough(current_size, needed_size)`: meaning we are expecting
///   a more bytes to parse the CBOR properly;
/// - `Error::Expected(expected_type, current_type)`: the current cbor primary
///   [`Type`] is different from the expected [`Type`];
/// - `Error::UnknownLenType(byte)`: the CBOR is serialized in an unknown
///   or unsupported format;
/// - `Error::IndefiniteLenUnsupported(t)`: the Indefinite length is not
///   supported for the given [`Type`] `t`;
/// - `Error::IoError(io_error)`: error due relating to buffer management;
///
/// # Panic
///
/// There is no explicit `panic!` in this code, except a few `unreachable!`.
///
pub struct Deserializer<'a> {
    data: &'a [u8],
    pos: usize,
    allocate: Option<fn(usize) -> &'a mut [u8]>,
}

impl<'a> From<&'a [u8]> for Deserializer<'a> {
    fn from(r: &'a [u8]) -> Self {
        Deserializer {
            data: r,
            pos: 0,
            allocate: None,
        }
    }
}

impl<'a> AsRef<[u8]> for Deserializer<'a> {
    fn as_ref(&self) -> &[u8] {
        self.data
    }
}

impl<'a> Display for Deserializer<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.data
            .iter()
            .try_for_each(|b| f.write_fmt(format_args!("{:02x}", b)))
    }
}

impl<'a> Deserializer<'a> {
    pub fn inner(self) -> &'a [u8] {
        self.data
    }

    #[inline]
    fn get(&mut self, index: usize) -> Result<&u8> {
        match self.data.get(self.pos + index) {
            None => Err(Error::NotEnough(self.data.len(), index)),
            Some(b) => Ok(b),
        }
    }
    #[inline]
    fn u8(&mut self, index: usize) -> Result<u64> {
        let b = self.get(index)?;
        Ok(*b as u64)
    }
    #[inline]
    fn u16(&mut self, index: usize) -> Result<u64> {
        let b1 = self.u8(index)?;
        let b2 = self.u8(index + 1)?;
        Ok(b1 << 8 | b2)
    }
    #[inline]
    fn u32(&mut self, index: usize) -> Result<u64> {
        let b1 = self.u8(index)?;
        let b2 = self.u8(index + 1)?;
        let b3 = self.u8(index + 2)?;
        let b4 = self.u8(index + 3)?;
        Ok(b1 << 24 | b2 << 16 | b3 << 8 | b4)
    }
    #[inline]
    fn u64(&mut self, index: usize) -> Result<u64> {
        let b1 = self.u8(index)?;
        let b2 = self.u8(index + 1)?;
        let b3 = self.u8(index + 2)?;
        let b4 = self.u8(index + 3)?;
        let b5 = self.u8(index + 4)?;
        let b6 = self.u8(index + 5)?;
        let b7 = self.u8(index + 6)?;
        let b8 = self.u8(index + 7)?;
        Ok(b1 << 56 | b2 << 48 | b3 << 40 | b4 << 32 | b5 << 24 | b6 << 16 | b7 << 8 | b8)
    }

    /// function to extract the type of the given `Deserializer`.
    ///
    /// This function does not consume the underlying buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use cbor_event::{de::*, Type};
    ///
    /// let vec = vec![0x18, 0x40];
    /// let mut raw = Deserializer::from(vec);
    /// let cbor_type = raw.cbor_type().unwrap();
    ///
    /// assert!(cbor_type == Type::UnsignedInteger);
    /// ```
    #[inline]
    pub fn cbor_type(&mut self) -> Result<Type> {
        Ok(Type::from(self.get(0)?))
    }
    #[inline]
    fn cbor_expect_type(&mut self, t: Type) -> Result<()> {
        let t_ = self.cbor_type()?;
        if t_ != t {
            Err(Error::Expected(t, t_))
        } else {
            Ok(())
        }
    }

    /// function to extract the length parameter of
    /// the given cbor object. The returned tuple contains
    ///
    /// [`Type`]: ../enum.Type.html
    /// [`Len`]: ../enum.Len.html
    ///
    /// * the [`Len`];
    /// * the size of the encoded length (the number of bytes the data was encoded in).
    ///   `0` means the length is `< 24` and was encoded along the `Type`.
    ///
    /// If you are expecting a `Type` `UnsignedInteger` or `NegativeInteger` the meaning of
    /// the length is slightly different:
    ///
    /// * `Len::Indefinite` is an error;
    /// * `Len::Len(len)` is the read value of the integer.
    ///
    /// This function does not consume the underlying buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use cbor_event::{de::*, Len};
    ///
    /// let vec = vec![0x83, 0x01, 0x02, 0x03];
    /// let mut raw = Deserializer::from(vec);
    /// let (len, len_sz) = raw.cbor_len().unwrap();
    ///
    /// assert_eq!(len, Len::Len(3));
    /// assert_eq!(len_sz, 0);
    /// ```
    ///
    #[inline]
    pub fn cbor_len(&mut self) -> Result<(Len, usize)> {
        let b: u8 = self.get(0)? & 0b0001_1111;
        match b {
            0x00..=0x17 => Ok((Len::Len(b as u64), 0)),
            0x18 => self.u8(1).map(|v| (Len::Len(v), 1)),
            0x19 => self.u16(1).map(|v| (Len::Len(v), 2)),
            0x1a => self.u32(1).map(|v| (Len::Len(v), 4)),
            0x1b => self.u64(1).map(|v| (Len::Len(v), 8)),
            0x1c..=0x1e => Err(Error::UnknownLenType(b)),
            0x1f => Ok((Len::Indefinite, 0)),

            // since the value `b` has been masked to only consider the first 5 lowest bits
            // all value above 0x1f are unreachable.
            _ => unreachable!(),
        }
    }

    /// function to extract the length parameter of
    /// the given cbor object as well as the encoding details of the length.
    ///
    /// [`LenSz`]: ../enum.LenSz.html
    #[inline]
    pub fn cbor_len_sz(&mut self) -> Result<LenSz> {
        let b: u8 = self.get(0)? & 0b0001_1111;
        match b {
            0x00..=0x17 => Ok(LenSz::Len(b as u64, Sz::Inline)),
            0x18 => self.u8(1).map(|v| LenSz::Len(v, Sz::One)),
            0x19 => self.u16(1).map(|v| LenSz::Len(v, Sz::Two)),
            0x1a => self.u32(1).map(|v| LenSz::Len(v, Sz::Four)),
            0x1b => self.u64(1).map(|v| LenSz::Len(v, Sz::Eight)),
            0x1c..=0x1e => Err(Error::UnknownLenType(b)),
            0x1f => Ok(LenSz::Indefinite),

            // since the value `b` has been masked to only consider the first 5 lowest bits
            // all value above 0x1f are unreachable.
            _ => unreachable!(),
        }
    }

    /// consume the given `len` from the underlying buffer
    #[inline]
    pub fn advance(&mut self, len: usize) -> Result<()> {
        self.pos += len;

        Ok(())
    }

    #[inline]
    pub fn position(&self) -> usize {
        self.pos
    }

    #[inline]
    pub fn seek(&mut self, pos: usize) -> Result<()> {
        if pos > self.data.len() {
            Err(Error::NotEnough(self.data.len(), pos))
        } else {
            self.pos = pos;
            Ok(())
        }
    }

    /// Read an `UnsignedInteger` from the `Deserializer`
    ///
    /// The function fails if the type of the given Deserializer is not `Type::UnsignedInteger`.
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::de::{*};
    ///
    /// let vec = vec![0x18, 0x40];
    /// let mut raw = Deserializer::from(vec);
    ///
    /// let integer = raw.unsigned_integer().unwrap();
    ///
    /// assert_eq!(integer, 64);
    /// ```
    ///
    /// ```should_panic
    /// use cbor_event::de::{*};
    ///
    /// let vec = vec![0x83, 0x01, 0x02, 0x03];
    /// let mut raw = Deserializer::from(vec);
    ///
    /// // the following line will panic:
    /// let integer = raw.unsigned_integer().unwrap();
    /// ```
    pub fn unsigned_integer(&mut self) -> Result<u64> {
        Ok(self.unsigned_integer_sz()?.0)
    }

    /// Read an `UnsignedInteger` from the `Deserializer` with encoding information
    ///
    /// Same as `unsigned_integer` but returns the `Sz` (bytes used) in the encoding
    pub fn unsigned_integer_sz(&mut self) -> Result<(u64, Sz)> {
        self.cbor_expect_type(Type::UnsignedInteger)?;
        let len_sz = self.cbor_len_sz()?;
        match len_sz {
            LenSz::Indefinite => Err(Error::IndefiniteLenNotSupported(Type::UnsignedInteger)),
            LenSz::Len(v, sz) => {
                self.advance(1 + sz.bytes_following())?;
                Ok((v, sz))
            }
        }
    }

    /// Read a `NegativeInteger` from the `Deserializer`
    ///
    /// The function fails if the type of the given Deserializer is not `Type::NegativeInteger`.
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::de::{*};
    ///
    /// let vec = vec![0x38, 0x29];
    /// let mut raw = Deserializer::from(vec);
    ///
    /// let integer = raw.negative_integer().unwrap();
    ///
    /// assert_eq!(integer, -42);
    /// ```
    pub fn negative_integer(&mut self) -> Result<i64> {
        self.cbor_expect_type(Type::NegativeInteger)?;
        let (len, len_sz) = self.cbor_len()?;
        match len {
            Len::Indefinite => Err(Error::IndefiniteLenNotSupported(Type::NegativeInteger)),
            Len::Len(v) => {
                self.advance(1 + len_sz)?;
                Ok(-(v as i64) - 1)
            }
        }
    }

    /// Read a `NegativeInteger` from the `Deserializer` with encoding information
    ///
    /// Same as `negative_integer` but returns the `Sz` (bytes used)
    /// in the encoding as well as using a `i128` return type as `i64`
    /// does not cover the entire CBOR `nint` range.
    pub fn negative_integer_sz(&mut self) -> Result<(i128, Sz)> {
        self.cbor_expect_type(Type::NegativeInteger)?;
        let len_sz = self.cbor_len_sz()?;
        match len_sz {
            LenSz::Indefinite => Err(Error::IndefiniteLenNotSupported(Type::NegativeInteger)),
            LenSz::Len(v, sz) => {
                self.advance(1 + sz.bytes_following())?;
                Ok((-(v as i128) - 1, sz))
            }
        }
    }

    /// Read a Bytes from the Deserializer
    ///
    /// The function fails if the type of the given Deserializer is not `Type::Bytes`.
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::de::{*};
    ///
    /// let vec = vec![0x52, 0x73, 0x6F, 0x6D, 0x65, 0x20, 0x72, 0x61, 0x6E, 0x64, 0x6F, 0x6D, 0x20, 0x73, 0x74, 0x72, 0x69, 0x6E, 0x67];
    /// let mut raw = Deserializer::from(vec);
    ///
    /// let bytes = raw.bytes().unwrap();
    /// ```
    pub fn bytes(&mut self) -> Result<&'a [u8]> {
        Ok(self.bytes_sz(None)?.0)
    }

    /// Read a Bytes from the Deserializer with encoding information
    ///
    /// Same as `bytes` but also returns `StringLenSz` for details about the encoding used.
    pub fn bytes_sz(
        &mut self,
        sz_alloc: Option<fn(usize) -> &'a mut [(u64, Sz)]>,
    ) -> Result<(&'a [u8], StringLenSz)> {
        self.cbor_expect_type(Type::Bytes)?;
        let len_sz = self.cbor_len_sz()?;
        self.advance(1 + len_sz.bytes_following())?;
        match len_sz {
            LenSz::Indefinite => {
                if self.allocate.is_none() {
                    return Err(Error::NoAllocator);
                }
                let start = self.pos;
                let mut chunks = 0;
                while self.cbor_type()? != Type::Special || !self.special_break()? {
                    self.cbor_expect_type(Type::Bytes)?;
                    let chunk_len_sz = self.cbor_len_sz()?;
                    match chunk_len_sz {
                        LenSz::Indefinite => return Err(Error::InvalidIndefiniteString),
                        LenSz::Len(len, sz) => {
                            self.advance(1 + sz.bytes_following())?;
                            self.advance(len as usize)?;
                            chunks += 1;
                        }
                    }
                }
                let size = self.pos - start;
                self.pos -= size;
                let bytes = self.allocate.unwrap()(size);
                let mut array_pos: usize = 0;
                let mut chunk_pos: usize = 0;
                let mut chunk_lens = sz_alloc.map(|f| f(chunks));
                while self.cbor_type()? != Type::Special || !self.special_break()? {
                    self.cbor_expect_type(Type::Bytes)?;
                    let chunk_len_sz = self.cbor_len_sz()?;
                    match chunk_len_sz {
                        LenSz::Indefinite => return Err(Error::InvalidIndefiniteString),
                        LenSz::Len(len, sz) => {
                            self.advance(1 + sz.bytes_following())?;
                            bytes[array_pos..array_pos + len as usize]
                                .copy_from_slice(&self.data[self.pos..self.pos + len as usize]);
                            array_pos += len as usize;
                            self.advance(len as usize)?;
                            if let Some(ref mut c) = chunk_lens {
                                c[chunk_pos..chunk_pos + 1].fill((len, sz));
                                chunk_pos += 1;
                            }
                        }
                    }
                }
                Ok((
                    bytes,
                    StringLenSz::Indefinite(chunk_lens.unwrap_or(&mut [])),
                ))
            }
            LenSz::Len(len, sz) => {
                let bytes = &self.data[self.pos..self.pos + len as usize];
                self.advance(len as usize)?;
                Ok((bytes, StringLenSz::Len(sz)))
            }
        }
    }

    /// Read a Text from the Deserializer
    ///
    /// The function fails if the type of the given Deserializer is not `Type::Text`.
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::de::{*};
    ///
    /// let vec = vec![0x64, 0x74, 0x65, 0x78, 0x74];
    /// let mut raw = Deserializer::from(vec);
    ///
    /// let text = raw.text().unwrap();
    ///
    /// assert!(&*text == "text");
    /// ```
    pub fn text(&mut self) -> Result<&'a str> {
        Ok(self.text_sz(None)?.0)
    }

    /// Read a Text from the Deserializer with encoding information
    ///
    /// Same as `text` but also returns `StringLenSz` for details about the encoding used.
    pub fn text_sz(
        &mut self,
        sz_alloc: Option<fn(usize) -> &'a mut [(u64, Sz)]>,
    ) -> Result<(&'a str, StringLenSz)> {
        self.cbor_expect_type(Type::Text)?;
        let len_sz = self.cbor_len_sz()?;
        self.advance(1 + len_sz.bytes_following())?;
        match len_sz {
            LenSz::Indefinite => {
                if self.allocate.is_none() {
                    return Err(Error::NoAllocator);
                }
                let start = self.pos;
                let mut chunks = 0;
                while self.cbor_type()? != Type::Special || !self.special_break()? {
                    self.cbor_expect_type(Type::Text)?;
                    let chunk_len = self.cbor_len_sz()?;
                    match chunk_len {
                        LenSz::Indefinite => return Err(Error::InvalidIndefiniteString),
                        LenSz::Len(len, sz) => {
                            // rfc7049 forbids splitting UTF-8 characters across chunks so we must
                            // read each chunk separately as a definite encoded UTF-8 string
                            self.advance(1 + sz.bytes_following())?;
                            self.advance(len as usize)?;
                            chunks += 1;
                        }
                    }
                }
                let size = self.pos - start;
                self.pos -= size;
                let bytes = self.allocate.unwrap()(size);
                let mut array_pos: usize = 0;
                let mut chunk_pos: usize = 0;
                let mut chunk_lens = sz_alloc.map(|f| f(chunks));
                while self.cbor_type()? != Type::Special || !self.special_break()? {
                    self.cbor_expect_type(Type::Text)?;
                    let chunk_len = self.cbor_len_sz()?;
                    match chunk_len {
                        LenSz::Indefinite => return Err(Error::InvalidIndefiniteString),
                        LenSz::Len(len, sz) => {
                            // rfc7049 forbids splitting UTF-8 characters across chunks so we must
                            // read each chunk separately as a definite encoded UTF-8 string
                            self.advance(1 + sz.bytes_following())?;
                            bytes[array_pos..array_pos + len as usize]
                                .copy_from_slice(&self.data[self.pos..self.pos + len as usize]);
                            array_pos += len as usize;
                            self.advance(len as usize)?;
                            if let Some(ref mut c) = chunk_lens {
                                c[chunk_pos..chunk_pos + 1].fill((len, sz));
                                chunk_pos += 1;
                            }
                        }
                    }
                }
                Ok((
                    core::str::from_utf8(bytes)?,
                    StringLenSz::Indefinite(chunk_lens.unwrap_or(&mut [])),
                ))
            }
            LenSz::Len(len, sz) => {
                let bytes = &self.data[self.pos..self.pos + len as usize];
                let text = core::str::from_utf8(bytes)?;
                self.advance(len as usize)?;
                Ok((text, StringLenSz::Len(sz)))
            }
        }
    }

    // Internal helper to decode a series of `len` items using a function. If
    // `len` is indefinite, decode until a `Special::Break`. If `len` is
    // definite, decode that many items.
    fn internal_items_with<F>(&mut self, len: Len, mut f: F) -> Result<()>
    where
        F: FnMut(&mut Self) -> Result<()>,
    {
        match len {
            Len::Indefinite => {
                while !self.special_break()? {
                    f(self)?;
                }
            }
            Len::Len(len) => {
                for _ in 0..len {
                    f(self)?;
                }
            }
        }
        Ok(())
    }

    /// cbor array of cbor objects
    ///
    /// The function fails if the type of the given Deserializer is not `Type::Array`.
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::{de::{*}, Len};
    ///
    /// let vec = vec![0x86, 0,1,2,3,4,5];
    /// let mut raw = Deserializer::from(vec);
    ///
    /// let len = raw.array().unwrap();
    ///
    /// assert_eq!(len, Len::Len(6));
    /// ```
    ///
    pub fn array(&mut self) -> Result<Len> {
        self.cbor_expect_type(Type::Array)?;
        let (len, sz) = self.cbor_len()?;
        self.advance(1 + sz)?;
        Ok(len)
    }

    /// cbor array of cbor objects with length encoding information
    ///
    /// Same as `array` but returns the `LenSz` instead which contains
    /// additional information about the encoding used for the length
    pub fn array_sz(&mut self) -> Result<LenSz> {
        self.cbor_expect_type(Type::Array)?;
        let len_sz = self.cbor_len_sz()?;
        self.advance(1 + len_sz.bytes_following())?;
        Ok(len_sz)
    }

    /// Helper to decode a cbor array using a specified function.
    ///
    /// This works with either definite or indefinite arrays. Each call to the
    /// function should decode one item. If the function returns an error,
    /// decoding stops and returns that error.
    pub fn array_with<F>(&mut self, f: F) -> Result<()>
    where
        F: FnMut(&mut Self) -> Result<()>,
    {
        let len = self.array()?;
        self.internal_items_with(len, f)
    }

    /// Expect an array of a specified length. Must be a definite-length array.
    pub fn tuple(&mut self, expected_len: u64, error_location: &'static str) -> Result<()> {
        let actual_len = self.array()?;
        match actual_len {
            Len::Len(len) if expected_len == len => Ok(()),
            _ => Err(Error::WrongLen(expected_len, actual_len, error_location)),
        }
    }

    /// cbor map
    ///
    /// The function fails if the type of the given Deserializer is not `Type::Map`.
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::{de::{*}, Len};
    ///
    /// let vec = vec![0xA2, 0x00, 0x64, 0x74, 0x65, 0x78, 0x74, 0x01, 0x18, 0x2A];
    /// let mut raw = Deserializer::from(vec);
    ///
    /// let len = raw.map().unwrap();
    ///
    /// assert_eq!(len, Len::Len(2));
    /// ```
    ///
    pub fn map(&mut self) -> Result<Len> {
        self.cbor_expect_type(Type::Map)?;
        let (len, sz) = self.cbor_len()?;
        self.advance(1 + sz)?;
        Ok(len)
    }

    /// cbor map with length encoding information
    ///
    /// Same as `map` but returns the `LenSz` instead which contains
    /// additional information about the encoding used for the length
    pub fn map_sz(&mut self) -> Result<LenSz> {
        self.cbor_expect_type(Type::Map)?;
        let len_sz = self.cbor_len_sz()?;
        self.advance(1 + len_sz.bytes_following())?;
        Ok(len_sz)
    }

    /// Helper to decode a cbor map using a specified function
    ///
    /// This works with either definite or indefinite maps. Each call to the
    /// function should decode one key followed by one value. If the function
    /// returns an error, decoding stops and returns that error.
    pub fn map_with<F>(&mut self, f: F) -> Result<()>
    where
        F: FnMut(&mut Self) -> Result<()>,
    {
        let len = self.map()?;
        self.internal_items_with(len, f)
    }

    /// Cbor Tag
    ///
    /// The function fails if the type of the given Deserializer is not `Type::Tag`.
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::{de::{*}, Len};
    ///
    /// let vec = vec![0xD8, 0x18, 0x64, 0x74, 0x65, 0x78, 0x74];
    /// let mut raw = Deserializer::from(vec);
    ///
    /// let tag = raw.tag().unwrap();
    ///
    /// assert_eq!(24, tag);
    /// assert_eq!("text", &*raw.text().unwrap());
    /// ```
    ///
    pub fn tag(&mut self) -> Result<u64> {
        Ok(self.tag_sz()?.0)
    }

    /// CBOR Tag with encoding information
    ///
    /// Same as `tag` but returns the `Sz` (bytes used) in the encoding
    pub fn tag_sz(&mut self) -> Result<(u64, Sz)> {
        self.cbor_expect_type(Type::Tag)?;
        match self.cbor_len_sz()? {
            LenSz::Indefinite => Err(Error::IndefiniteLenNotSupported(Type::Tag)),
            LenSz::Len(len, sz) => {
                self.advance(1 + sz.bytes_following())?;
                Ok((len, sz))
            }
        }
    }

    pub fn set_tag(&mut self) -> Result<()> {
        let tag = self.tag()?;
        if tag != 258 {
            return Err(Error::ExpectedSetTag);
        }
        Ok(())
    }

    /// If the next byte is a `Special::Break`, advance past it and return `true`; otherwise,
    /// return `false` without advancing.
    ///
    /// Useful when decoding a variable-length array or map where the items may themselves use
    /// `Special`, such as bool values.
    pub fn special_break(&mut self) -> Result<bool> {
        self.cbor_expect_type(Type::Special)?;
        let b = self.get(0)? & 0b0001_1111;
        if b == 0x1f {
            self.advance(1)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub fn special(&mut self) -> Result<Special> {
        self.cbor_expect_type(Type::Special)?;
        let b = self.get(0)? & 0b0001_1111;
        match b {
            0x00..=0x13 => {
                self.advance(1)?;
                Ok(Special::Unassigned(b))
            }
            0x14 => {
                self.advance(1)?;
                Ok(Special::Bool(false))
            }
            0x15 => {
                self.advance(1)?;
                Ok(Special::Bool(true))
            }
            0x16 => {
                self.advance(1)?;
                Ok(Special::Null)
            }
            0x17 => {
                self.advance(1)?;
                Ok(Special::Undefined)
            }
            0x18 => {
                let b = self.u8(1)?;
                self.advance(2)?;
                Ok(Special::Unassigned(b as u8))
            }
            0x19 => {
                let f = self.u16(1)?;
                self.advance(3)?;
                Ok(Special::Float(f as f64))
            }
            0x1a => {
                let f = self.u32(1)? as u32;
                self.advance(5)?;
                Ok(Special::Float(f32::from_bits(f) as f64))
            }
            0x1b => {
                let f = self.u64(1)?;
                self.advance(9)?;
                Ok(Special::Float(f64::from_bits(f)))
            }
            0x1c..=0x1e => {
                self.advance(1)?;
                Ok(Special::Unassigned(b))
            }
            0x1f => {
                self.advance(1)?;
                Ok(Special::Break)
            }
            _ => unreachable!(),
        }
    }

    pub fn bool(&mut self) -> Result<bool> {
        self.special()?.unwrap_bool()
    }

    pub fn float(&mut self) -> Result<f64> {
        self.special()?.unwrap_float()
    }

    pub fn deserialize<T>(&mut self) -> Result<T>
    where
        T: Deserialize<'a>,
    {
        Deserialize::deserialize(self)
    }

    /// Deserialize a value of type `T` and check that there is no
    /// trailing data.
    pub fn deserialize_complete<T>(&mut self) -> Result<T>
    where
        T: Deserialize<'a>,
    {
        let v = self.deserialize()?;
        if self.pos < self.data.len() {
            Ok(v)
        } else {
            Err(Error::TrailingData)
        }
    }
}

// deserialisation macro

macro_rules! deserialize_array {
    ( $( $x:expr ),* ) => {
        $(
            impl<'a> Deserialize<'a> for [u8; $x] {
                fn deserialize(raw: &mut Deserializer<'a>) ->  Result<Self> {
                    let mut bytes = [0u8; $x];

                    let len = raw.array()?;
                    match len {
                        Len::Indefinite => {
                            return Err(Error::WrongLen($x, len, "static array"));
                        },
                        Len::Len(x) => {
                            if x != $x {
                                return Err(Error::WrongLen($x, len, "static array"));
                            }
                        }
                    }

                    for byte in bytes.iter_mut() {
                        *byte = Deserialize::deserialize(raw)?;
                    }
                    Ok(bytes)
                }
            }
        )*
    }
}

deserialize_array!(
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
    51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
);

#[cfg(test)]
#[allow(clippy::bool_assert_comparison)]
mod test {
    use super::*;
    use alloc::collections::BTreeMap;
    use alloc::vec;
    use alloc::vec::Vec;

    #[test]
    fn negative_integer() {
        let vec = [0x38, 0x29].as_ref();
        let mut raw = Deserializer::from(vec);

        let integer = raw.negative_integer().unwrap();

        assert_eq!(integer, -42);
    }

    #[test]
    fn bytes() {
        let vec = [
            0x52, 0x73, 0x6F, 0x6D, 0x65, 0x20, 0x72, 0x61, 0x6E, 0x64, 0x6F, 0x6D, 0x20, 0x73,
            0x74, 0x72, 0x69, 0x6E, 0x67,
        ]
        .as_ref();
        let mut raw = Deserializer::from(vec);

        let bytes = raw.bytes().unwrap();
        assert_eq!(&vec[1..], &*bytes);
    }
    #[test]
    fn bytes_indefinite() {
        let chunks = [
            [
                0x52, 0x73, 0x6F, 0x6D, 0x65, 0x20, 0x72, 0x61, 0x6E, 0x64, 0x6F, 0x6D, 0x20, 0x73,
                0x74, 0x72, 0x69, 0x6E, 0x67,
            ]
            .as_ref(),
            [0x44, 0x01, 0x02, 0x03, 0x04].as_ref(),
        ];
        let mut expected = Vec::new();
        for chunk in chunks.iter() {
            expected.extend_from_slice(&chunk[1..]);
        }
        let mut vec = vec![0x5f];
        for mut chunk in chunks {
            vec.extend_from_slice(&mut chunk);
        }
        vec.push(0xff);
        let mut raw = Deserializer::from(vec.as_slice());
        let found = raw.bytes().unwrap();
        assert_eq!(found, expected);
    }
    #[test]
    fn bytes_empty() {
        let vec = [0x40].as_ref();
        let mut raw = Deserializer::from(vec);

        let bytes = raw.bytes().unwrap();
        assert!(bytes.is_empty());
    }

    #[test]
    fn text() {
        let vec = [0x64, 0x74, 0x65, 0x78, 0x74].as_ref();
        let mut raw = Deserializer::from(vec);

        let text = raw.text().unwrap();

        assert_eq!(text, "text");
    }
    #[test]
    fn text_indefinite() {
        let chunks = [
            [0x64, 0x49, 0x45, 0x54, 0x46].as_ref(),
            [0x61, 0x61].as_ref(),
        ];
        let expected = "IETFa";
        let mut vec = vec![0x7f];
        for mut chunk in chunks {
            vec.extend_from_slice(&mut chunk);
        }
        vec.push(0xff);
        let mut raw = Deserializer::from(vec.as_slice());
        let found = raw.text().unwrap();
        assert_eq!(found, expected);
    }
    #[test]
    fn text_empty() {
        let vec = [0x60].as_ref();
        let mut raw = Deserializer::from(vec);

        let text = raw.text().unwrap();

        assert_eq!(text, "");
    }

    #[test]
    fn float64() {
        let vec = [0xfb, 0x3f, 0xf1, 0x99, 0x99, 0x99, 0x99, 0x99, 0x9a].as_ref();
        let mut raw = Deserializer::from(vec);

        let float = raw.float().unwrap();

        assert_eq!(float, 1.1);
    }

    #[test]
    fn float32() {
        let vec = [0xfa, 0x47, 0xc3, 0x50, 0x00].as_ref();
        let mut raw = Deserializer::from(vec);

        let float = raw.float().unwrap();

        assert_eq!(float, 100000.0);
    }

    #[test]
    fn array() {
        let vec = [0x86, 0, 1, 2, 3, 4, 5].as_ref();
        let mut raw = Deserializer::from(vec);

        let len = raw.array().unwrap();

        assert_eq!(len, Len::Len(6));
        // assert_eq!(&*raw, &[0, 1, 2, 3, 4, 5][..]);

        assert_eq!(0, raw.unsigned_integer().unwrap());
        assert_eq!(1, raw.unsigned_integer().unwrap());
        assert_eq!(2, raw.unsigned_integer().unwrap());
        assert_eq!(3, raw.unsigned_integer().unwrap());
        assert_eq!(4, raw.unsigned_integer().unwrap());
        assert_eq!(5, raw.unsigned_integer().unwrap());
    }
    #[test]
    fn array_empty() {
        let vec = [0x80].as_ref();
        let mut raw = Deserializer::from(vec);

        let len = raw.array().unwrap();

        assert_eq!(len, Len::Len(0));
        // assert_eq!(&*raw, &[][..]);
    }
    #[test]
    fn array_indefinite() {
        let vec = [0x9F, 0x01, 0x02, 0xFF].as_ref();
        let mut raw = Deserializer::from(vec);

        let len = raw.array().unwrap();

        assert_eq!(len, Len::Indefinite);
        // assert_eq!(&*raw, &[0x01, 0x02, 0xFF][..]);

        let i = raw.unsigned_integer().unwrap();
        assert_eq!(i, 1);
        let i = raw.unsigned_integer().unwrap();
        assert_eq!(i, 2);
        assert_eq!(Special::Break, raw.special().unwrap());
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn vec_bool_definite() {
        let vec = [0x83, 0xf4, 0xf5, 0xf4].as_ref();
        let mut raw = Deserializer::from(vec);
        let bools = Vec::<bool>::deserialize(&mut raw).unwrap();
        assert_eq!(bools, &[false, true, false]);
    }
    #[test]
    #[cfg(feature = "alloc")]
    fn vec_bool_indefinite() {
        let vec = [0x9f, 0xf4, 0xf5, 0xf4, 0xff].as_ref();
        let mut raw = Deserializer::from(vec);
        let bools = Vec::<bool>::deserialize(&mut raw).unwrap();
        assert_eq!(bools, &[false, true, false]);
    }

    #[test]
    fn complex_array() {
        let vec = [
            0x85, 0x64, 0x69, 0x6F, 0x68, 0x6B, 0x01, 0x20, 0x84, 0, 1, 2, 3, 0x10,
            /* garbage... */ 0, 1, 2, 3, 4, 5, 6,
        ]
        .as_ref();
        let mut raw = Deserializer::from(vec);

        let len = raw.array().unwrap();

        assert_eq!(len, Len::Len(5));

        assert_eq!("iohk", raw.text().unwrap());
        assert_eq!(1, raw.unsigned_integer().unwrap());
        assert_eq!(-1, raw.negative_integer().unwrap());

        let nested_array_len = raw.array().unwrap();
        assert_eq!(nested_array_len, Len::Len(4));
        assert_eq!(0, raw.unsigned_integer().unwrap());
        assert_eq!(1, raw.unsigned_integer().unwrap());
        assert_eq!(2, raw.unsigned_integer().unwrap());
        assert_eq!(3, raw.unsigned_integer().unwrap());

        assert_eq!(0x10, raw.unsigned_integer().unwrap());

        // const GARBAGE_LEN: usize = 7;
        // assert_eq!(GARBAGE_LEN, raw.len());
    }

    #[test]
    fn map() {
        let vec = [0xA2, 0x00, 0x64, 0x74, 0x65, 0x78, 0x74, 0x01, 0x18, 0x2A].as_ref();
        let mut raw = Deserializer::from(vec);

        let len = raw.map().unwrap();

        assert_eq!(len, Len::Len(2));

        let k = raw.unsigned_integer().unwrap();
        let v = raw.text().unwrap();
        assert_eq!(0, k);
        assert_eq!("text", v);

        let k = raw.unsigned_integer().unwrap();
        let v = raw.unsigned_integer().unwrap();
        assert_eq!(1, k);
        assert_eq!(42, v);
    }

    #[test]
    fn map_empty() {
        let vec = [0xA0].as_ref();
        let mut raw = Deserializer::from(vec);

        let len = raw.map().unwrap();

        assert_eq!(len, Len::Len(0));
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn btreemap_bool_definite() {
        let vec = [0xa2, 0xf4, 0xf5, 0xf5, 0xf4].as_ref();
        let mut raw = Deserializer::from(vec);
        let boolmap = BTreeMap::<bool, bool>::deserialize(&mut raw).unwrap();
        assert_eq!(boolmap.len(), 2);
        assert_eq!(boolmap[&false], true);
        assert_eq!(boolmap[&true], false);
    }
    #[test]
    #[cfg(feature = "alloc")]
    fn btreemap_bool_indefinite() {
        let vec = [0xbf, 0xf4, 0xf5, 0xf5, 0xf4, 0xff].as_ref();
        let mut raw = Deserializer::from(vec);
        let boolmap = BTreeMap::<bool, bool>::deserialize(&mut raw).unwrap();
        assert_eq!(boolmap.len(), 2);
        assert_eq!(boolmap[&false], true);
        assert_eq!(boolmap[&true], false);
    }

    #[test]
    fn tag() {
        let vec = [
            0xD8, 0x18, 0x52, 0x73, 0x6F, 0x6D, 0x65, 0x20, 0x72, 0x61, 0x6E, 0x64, 0x6F, 0x6D,
            0x20, 0x73, 0x74, 0x72, 0x69, 0x6E, 0x67,
        ]
        .as_ref();
        let mut raw = Deserializer::from(vec);

        let tag = raw.tag().unwrap();

        assert_eq!(24, tag);
        let tagged = raw.bytes().unwrap();
        assert_eq!(b"some random string", &*tagged);
    }

    #[test]
    fn tag2() {
        let vec = [
            0x82, 0xd8, 0x18, 0x53, 0x52, 0x73, 0x6f, 0x6d, 0x65, 0x20, 0x72, 0x61, 0x6e, 0x64,
            0x6f, 0x6d, 0x20, 0x73, 0x74, 0x72, 0x69, 0x6e, 0x67, 0x1a, 0x71, 0xad, 0x58, 0x36,
        ]
        .as_ref();
        let mut raw = Deserializer::from(vec);

        let len = raw.array().unwrap();
        assert_eq!(len, Len::Len(2));

        let tag = raw.tag().unwrap();
        assert_eq!(tag, 24);
        let _ = raw.bytes().unwrap();

        let crc = raw.unsigned_integer().unwrap();
        assert_eq!(crc as u32, 0x71AD5836);
    }

    #[test]
    fn uint_sz() {
        let vec = [
            0x09, 0x18, 0x09, 0x19, 0x00, 0x09, 0x1a, 0x00, 0x00, 0x00, 0x09, 0x1b, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x09,
        ]
        .as_ref();
        let mut raw = Deserializer::from(vec);
        assert_eq!(raw.unsigned_integer_sz().unwrap(), (9, Sz::Inline));
        assert_eq!(raw.unsigned_integer_sz().unwrap(), (9, Sz::One));
        assert_eq!(raw.unsigned_integer_sz().unwrap(), (9, Sz::Two));
        assert_eq!(raw.unsigned_integer_sz().unwrap(), (9, Sz::Four));
        assert_eq!(raw.unsigned_integer_sz().unwrap(), (9, Sz::Eight));
    }

    #[test]
    fn nint_sz() {
        let vec = [
            0x28, 0x38, 0x08, 0x39, 0x00, 0x08, 0x3a, 0x00, 0x00, 0x00, 0x08, 0x3b, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x08,
        ]
        .as_ref();
        let mut raw = Deserializer::from(vec);
        assert_eq!(raw.negative_integer_sz().unwrap(), (-9, Sz::Inline));
        assert_eq!(raw.negative_integer_sz().unwrap(), (-9, Sz::One));
        assert_eq!(raw.negative_integer_sz().unwrap(), (-9, Sz::Two));
        assert_eq!(raw.negative_integer_sz().unwrap(), (-9, Sz::Four));
        assert_eq!(raw.negative_integer_sz().unwrap(), (-9, Sz::Eight));
    }

    #[test]
    fn bytes_sz() {
        let def_parts: Vec<Vec<u8>> = vec![
            vec![0x44, 0xBA, 0xAD, 0xF0, 0x0D],
            vec![0x58, 0x04, 0xCA, 0xFE, 0xD0, 0x0D],
            vec![0x59, 0x00, 0x04, 0xDE, 0xAD, 0xBE, 0xEF],
            vec![0x5a, 0x00, 0x00, 0x00, 0x02, 0xCA, 0xFE],
            vec![
                0x5b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xBE, 0xEF,
            ],
        ];
        let mut vec: Vec<u8> = def_parts.iter().flatten().cloned().collect();
        // also make an indefinite encoded one out all the definite-encoded parts
        vec.push(0x5F);
        for slice in def_parts.iter() {
            vec.extend_from_slice(&slice[..]);
        }
        vec.push(0xFF);
        let mut raw = Deserializer::from(vec.as_slice());
        let indef_bytes = [
            0xBA, 0xAD, 0xF0, 0x0D, 0xCA, 0xFE, 0xD0, 0x0D, 0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE,
            0xBE, 0xEF,
        ]
        .as_ref();
        let indef_lens = [
            (4, Sz::Inline),
            (4, Sz::One),
            (4, Sz::Two),
            (2, Sz::Four),
            (2, Sz::Eight),
        ]
        .as_ref();
        assert_eq!(
            raw.bytes_sz(None).unwrap(),
            (
                [0xBA, 0xAD, 0xF0, 0x0D].as_ref(),
                StringLenSz::Len(Sz::Inline)
            )
        );
        assert_eq!(
            raw.bytes_sz(None).unwrap(),
            ([0xCA, 0xFE, 0xD0, 0x0D].as_ref(), StringLenSz::Len(Sz::One))
        );
        assert_eq!(
            raw.bytes_sz(None).unwrap(),
            ([0xDE, 0xAD, 0xBE, 0xEF].as_ref(), StringLenSz::Len(Sz::Two))
        );
        assert_eq!(
            raw.bytes_sz(None).unwrap(),
            ([0xCA, 0xFE].as_ref(), StringLenSz::Len(Sz::Four))
        );
        assert_eq!(
            raw.bytes_sz(None).unwrap(),
            ([0xBE, 0xEF].as_ref(), StringLenSz::Len(Sz::Eight))
        );
        assert_eq!(
            raw.bytes_sz(None).unwrap(),
            (indef_bytes, StringLenSz::Indefinite(indef_lens))
        );
    }

    #[test]
    fn text_sz() {
        let def_parts: Vec<Vec<u8>> = vec![
            vec![0x65, 0x48, 0x65, 0x6c, 0x6c, 0x6f],
            vec![0x78, 0x05, 0x57, 0x6f, 0x72, 0x6c, 0x64],
            vec![
                0x79, 0x00, 0x09, 0xE6, 0x97, 0xA5, 0xE6, 0x9C, 0xAC, 0xE8, 0xAA, 0x9E,
            ],
            vec![0x7a, 0x00, 0x00, 0x00, 0x01, 0x39],
            vec![
                0x7b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x41, 0x42, 0x43,
            ],
        ];
        let mut vec: Vec<u8> = def_parts.iter().flatten().cloned().collect();
        // also make an indefinite encoded one out all the definite-encoded parts
        vec.push(0x7F);
        for slice in def_parts.iter() {
            vec.extend_from_slice(&slice[..]);
        }
        vec.push(0xFF);
        let mut raw = Deserializer::from(vec.as_slice());
        let indef_lens = &[
            (5, Sz::Inline),
            (5, Sz::One),
            (9, Sz::Two),
            (1, Sz::Four),
            (3, Sz::Eight),
        ];
        assert_eq!(
            raw.text_sz(None).unwrap(),
            ("Hello".into(), StringLenSz::Len(Sz::Inline))
        );
        assert_eq!(
            raw.text_sz(None).unwrap(),
            ("World".into(), StringLenSz::Len(Sz::One))
        );
        assert_eq!(
            raw.text_sz(None).unwrap(),
            ("日本語".into(), StringLenSz::Len(Sz::Two))
        );
        assert_eq!(
            raw.text_sz(None).unwrap(),
            ("9".into(), StringLenSz::Len(Sz::Four))
        );
        assert_eq!(
            raw.text_sz(None).unwrap(),
            ("ABC".into(), StringLenSz::Len(Sz::Eight))
        );
        assert_eq!(
            raw.text_sz(None).unwrap(),
            (
                "HelloWorld日本語9ABC".into(),
                StringLenSz::Indefinite(indef_lens)
            )
        );
    }

    #[test]
    fn array_sz() {
        let vec = [
            0x80, 0x98, 0x01, 0x99, 0x00, 0x02, 0x9a, 0x00, 0x00, 0x00, 0x03, 0x9b, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x9f,
        ]
        .as_ref();
        let mut raw = Deserializer::from(vec);
        assert_eq!(raw.array_sz().unwrap(), LenSz::Len(0, Sz::Inline));
        assert_eq!(raw.array_sz().unwrap(), LenSz::Len(1, Sz::One));
        assert_eq!(raw.array_sz().unwrap(), LenSz::Len(2, Sz::Two));
        assert_eq!(raw.array_sz().unwrap(), LenSz::Len(3, Sz::Four));
        assert_eq!(raw.array_sz().unwrap(), LenSz::Len(4, Sz::Eight));
        assert_eq!(raw.array_sz().unwrap(), LenSz::Indefinite);
    }

    #[test]
    fn map_sz() {
        let vec = [
            0xa0, 0xb8, 0x01, 0xb9, 0x00, 0x02, 0xba, 0x00, 0x00, 0x00, 0x03, 0xbb, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0xbf,
        ]
        .as_ref();
        let mut raw = Deserializer::from(vec);
        assert_eq!(raw.map_sz().unwrap(), LenSz::Len(0, Sz::Inline));
        assert_eq!(raw.map_sz().unwrap(), LenSz::Len(1, Sz::One));
        assert_eq!(raw.map_sz().unwrap(), LenSz::Len(2, Sz::Two));
        assert_eq!(raw.map_sz().unwrap(), LenSz::Len(3, Sz::Four));
        assert_eq!(raw.map_sz().unwrap(), LenSz::Len(4, Sz::Eight));
        assert_eq!(raw.map_sz().unwrap(), LenSz::Indefinite);
    }

    #[test]
    fn tag_sz() {
        let vec = [
            0xc9, 0xd8, 0x01, 0xd9, 0x00, 0x02, 0xda, 0x00, 0x00, 0x00, 0x04, 0xdb, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x08,
        ]
        .as_ref();
        let mut raw = Deserializer::from(vec);
        assert_eq!(raw.tag_sz().unwrap(), (9, Sz::Inline));
        assert_eq!(raw.tag_sz().unwrap(), (1, Sz::One));
        assert_eq!(raw.tag_sz().unwrap(), (2, Sz::Two));
        assert_eq!(raw.tag_sz().unwrap(), (4, Sz::Four));
        assert_eq!(raw.tag_sz().unwrap(), (8, Sz::Eight));
    }
}
