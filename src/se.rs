//! CBOR serialisation tooling
#[cfg(feature = "alloc")]
use alloc::string::String;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use core::convert::TryInto;

use error::Error;
use len::{Len, LenSz, StringLenSz, Sz};
use result::Result;
use types::{Special, Type};

pub trait Serialize {
    fn serialize<'a>(
        &'a self,
        serializer: &'a mut Serializer<'a>,
    ) -> Result<&'a mut Serializer<'a>>;
}
impl<'a, T: Serialize> Serialize for &'a T {
    fn serialize<'se>(
        &'se self,
        serializer: &'se mut Serializer<'se>,
    ) -> Result<&'se mut Serializer<'se>> {
        serializer.serialize(*self)
    }
}
impl Serialize for u64 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer<'a>) -> Result<&'a mut Serializer<'a>> {
        serializer.write_unsigned_integer(*self)
    }
}
impl Serialize for u32 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer<'a>) -> Result<&'a mut Serializer<'a>> {
        serializer.write_unsigned_integer((*self) as u64)
    }
}
impl Serialize for u16 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer<'a>) -> Result<&'a mut Serializer<'a>> {
        serializer.write_unsigned_integer((*self) as u64)
    }
}
impl Serialize for u8 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer<'a>) -> Result<&'a mut Serializer<'a>> {
        serializer.write_unsigned_integer((*self) as u64)
    }
}
impl Serialize for bool {
    fn serialize<'a>(&self, serializer: &'a mut Serializer<'a>) -> Result<&'a mut Serializer<'a>> {
        serializer.write_special(Special::Bool(*self))
    }
}
impl Serialize for f32 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer<'a>) -> Result<&'a mut Serializer<'a>> {
        serializer.write_special(Special::Float((*self) as f64))
    }
}
impl Serialize for f64 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer<'a>) -> Result<&'a mut Serializer<'a>> {
        serializer.write_special(Special::Float(*self))
    }
}
#[cfg(feature = "alloc")]
impl Serialize for String {
    fn serialize<'a>(&self, serializer: &'a mut Serializer<'a>) -> Result<&'a mut Serializer<'a>> {
        serializer.write_text(self)
    }
}
impl<'b> Serialize for &'b [u8] {
    fn serialize<'a>(&self, serializer: &'a mut Serializer<'a>) -> Result<&'a mut Serializer<'a>> {
        serializer.write_bytes(self)
    }
}
impl<'a, A, B> Serialize for (&'a A, &'a B)
where
    A: Serialize,
    B: Serialize,
{
    fn serialize<'b>(
        &'b self,
        serializer: &'b mut Serializer<'b>,
    ) -> Result<&'b mut Serializer<'b>> {
        serializer
            .write_array(Len::Len(2))?
            .serialize(self.0)?
            .serialize(self.1)
    }
}
impl<'a, A, B, C> Serialize for (&'a A, &'a B, &'a C)
where
    A: Serialize,
    B: Serialize,
    C: Serialize,
{
    fn serialize<'b>(
        &'b self,
        serializer: &'b mut Serializer<'b>,
    ) -> Result<&'b mut Serializer<'b>> {
        serializer
            .write_array(Len::Len(3))?
            .serialize(self.0)?
            .serialize(self.1)?
            .serialize(self.2)
    }
}

impl<T> Serialize for Option<T>
where
    T: Serialize,
{
    fn serialize<'a>(
        &'a self,
        serializer: &'a mut Serializer<'a>,
    ) -> Result<&'a mut Serializer<'a>> {
        match self {
            None => serializer.write_array(Len::Len(0)),
            Some(x) => serializer.write_array(Len::Len(1))?.serialize(x),
        }
    }
}

/// helper function to serialise a map of fixed size.
///
/// i.e. the size must be known ahead of time
///
pub fn serialize_fixed_map<'a, C, K, V, W>(
    data: C,
    serializer: &'a mut Serializer<'a>,
) -> Result<&'a mut Serializer<'a>>
where
    K: 'a + Serialize,
    V: 'a + Serialize,
    C: Iterator<Item = (&'a K, &'a V)> + ExactSizeIterator,
{
    let mut s = serializer.write_map(Len::Len(data.len() as u64))?;
    for element in data {
        s = Serialize::serialize(element.0, s)?;
        s = Serialize::serialize(element.1, s)?;
    }
    Ok(s)
}

/// helper function to serialise a collection of T as a fixed number of element
///
/// i.e. the size must be known ahead of time
///
pub fn serialize_fixed_array<'a, C, T>(
    data: C,
    serializer: &'a mut Serializer<'a>,
) -> Result<&'a mut Serializer<'a>>
where
    T: 'a + Serialize,
    C: Iterator<Item = &'a T> + ExactSizeIterator,
{
    let mut s = serializer.write_array(Len::Len(data.len() as u64))?;
    for element in data {
        s = Serialize::serialize(element, s)?;
    }
    Ok(s)
}

/// helper function to serialise a map of indefinite number of elements.
///
pub fn serialize_indefinite_map<'a, C, K, V, W>(
    data: C,
    serializer: &'a mut Serializer<'a>,
) -> Result<&'a mut Serializer<'a>>
where
    K: 'a + Serialize,
    V: 'a + Serialize,
    C: Iterator<Item = (&'a K, &'a V)>,
{
    let mut s = serializer.write_map(Len::Indefinite)?;
    for element in data {
        s = Serialize::serialize(element.0, s)?;
        s = Serialize::serialize(element.1, s)?;
    }
    s.write_special(Special::Break)
}

/// helper function to serialise a collection of T as a indefinite number of element
///
pub fn serialize_indefinite_array<'a, C, T, W>(
    data: C,
    serializer: &'a mut Serializer<'a>,
) -> Result<&'a mut Serializer<'a>>
where
    T: 'a + Serialize,
    C: Iterator<Item = &'a T>,
{
    let mut s = serializer.write_array(Len::Indefinite)?;
    for element in data {
        s = Serialize::serialize(element, s)?;
    }
    s.write_special(Special::Break)
}

/// helper function to serialise cbor in cbor
///
/// The existence of this function is questionable as it does not make sense, from the
/// CBOR protocol point of view, to encode cbor inside cbor. However it is the way
/// the haskell base code is serialising some objects so we need to comply here too
///
/// This function is a more efficient version of:
///
/// ```
/// # use cbor_event::se::{Serializer, Serialize};
/// let mut serializer = Serializer::new();
/// let mut se = Serializer::new();
/// 0u32.serialize(&mut se).unwrap();
/// serializer.write_bytes(&se.finalize()).unwrap();
/// ```
///
#[cfg(feature = "alloc")]
pub fn serialize_cbor_in_cbor<'a, T>(
    data: T,
    serializer: &'a mut Serializer<'a>,
    buffer: &'a mut [u8],
) -> Result<&'a mut Serializer<'a>>
where
    T: Serialize + 'a,
{
    let mut se = Serializer::new(buffer);
    serializer.write_bytes(data.serialize(&mut se)?.finalize())
}

// use a default capacity when allocating the Serializer to avoid small reallocation
// at the beginning of the serialisation process as Vec grows by 2, starting from a
// small or an empty serializer will only increase the number of realloc called at
// every _reserve_ calls.
const DEFAULT_CAPACITY: usize = 512;

/// simple CBOR serializer into any
/// [`std::io::Write`](https://doc.rust-lang.org/std/io/trait.Write.html).
///
#[derive(Debug)]
pub struct Serializer<'a> {
    data: &'a mut [u8],
    pos: usize,
}

impl<'a> Serializer<'a> {
    /// extend the serializer with the given bytes
    ///
    /// This is not encoding the given bytes in the CBOR format. More a way
    /// to add already CBOR encoded data or to add any bytes that may suite
    /// your protocol.
    pub fn write_raw_bytes(&mut self, bytes: &[u8]) -> Result<&mut Self> {
        self.data[self.pos..self.pos + bytes.len()].copy_from_slice(bytes);
        self.pos += bytes.len();
        Ok(self)
    }

    /// create a new serializer.
    ///
    /// ```
    /// use cbor_event::se::{Serializer};
    /// let mut vec = vec![];
    /// let serializer = Serializer::new(vec.as_mut_slice());
    /// ```
    #[inline]
    pub fn new(w: &'a mut [u8]) -> Self {
        Serializer { data: w, pos: 0 }
    }

    /// finalize the serializer, returning the serializer bytes
    ///
    /// ```
    /// use cbor_event::se::{Serializer};
    ///
    /// let serializer = Serializer::new();
    ///
    /// let bytes = serializer.finalize();
    ///
    /// # assert!(bytes.is_empty());
    /// ```
    #[inline]
    pub fn finalize(&'a self) -> &'a [u8] {
        self.data
    }

    #[inline]
    fn write_u8(&mut self, value: u8) -> Result<&mut Self> {
        self.write_raw_bytes(&[value][..])
    }

    #[inline]
    fn write_u16(&mut self, value: u16) -> Result<&mut Self> {
        self.write_raw_bytes(&[((value & 0xFF_00) >> 8) as u8, (value & 0x00_FF) as u8][..])
    }

    #[inline]
    fn write_u32(&mut self, value: u32) -> Result<&mut Self> {
        self.write_raw_bytes(
            &[
                ((value & 0xFF_00_00_00) >> 24) as u8,
                ((value & 0x00_FF_00_00) >> 16) as u8,
                ((value & 0x00_00_FF_00) >> 8) as u8,
                (value & 0x00_00_00_FF) as u8,
            ][..],
        )
    }

    #[inline]
    fn write_u64(&mut self, value: u64) -> Result<&mut Self> {
        self.write_raw_bytes(
            &[
                ((value & 0xFF_00_00_00_00_00_00_00) >> 56) as u8,
                ((value & 0x00_FF_00_00_00_00_00_00) >> 48) as u8,
                ((value & 0x00_00_FF_00_00_00_00_00) >> 40) as u8,
                ((value & 0x00_00_00_FF_00_00_00_00) >> 32) as u8,
                ((value & 0x00_00_00_00_FF_00_00_00) >> 24) as u8,
                ((value & 0x00_00_00_00_00_FF_00_00) >> 16) as u8,
                ((value & 0x00_00_00_00_00_00_FF_00) >> 8) as u8,
                (value & 0x00_00_00_00_00_00_00_FF) as u8,
            ][..],
        )
    }

    #[inline]
    fn write_f64(&mut self, value: f64) -> Result<&mut Self> {
        self.write_raw_bytes(&value.to_be_bytes())
    }

    /// Writes a CBOR type with the extra `len` information
    ///
    /// if `sz` is passed in, it will use that length/data encoding
    /// otherwise the minimum size (e.g. canonical) encoding will be used
    #[inline]
    fn write_type_definite(
        &mut self,
        cbor_type: Type,
        len: u64,
        sz: Option<Sz>,
    ) -> Result<&mut Self> {
        let extra_sz = match sz {
            None => Sz::canonical(len),
            Some(sz) => {
                let fits = match sz {
                    Sz::Inline => len <= super::MAX_INLINE_ENCODING,
                    Sz::One => len < 0x1_00,
                    Sz::Two => len < 0x1_00_00,
                    Sz::Four => len < 0x1_00_00_00_00,
                    Sz::Eight => true,
                };
                if !fits {
                    return Err(Error::InvalidLenPassed(sz));
                }
                sz
            }
        };
        match extra_sz {
            Sz::Inline => self.write_u8(cbor_type.to_byte(len as u8)),
            Sz::One => self
                .write_u8(cbor_type.to_byte(super::CBOR_PAYLOAD_LENGTH_U8))
                .and_then(|s| s.write_u8(len as u8)),
            Sz::Two => self
                .write_u8(cbor_type.to_byte(super::CBOR_PAYLOAD_LENGTH_U16))
                .and_then(|s| s.write_u16(len as u16)),
            Sz::Four => self
                .write_u8(cbor_type.to_byte(super::CBOR_PAYLOAD_LENGTH_U32))
                .and_then(|s| s.write_u32(len as u32)),
            Sz::Eight => self
                .write_u8(cbor_type.to_byte(super::CBOR_PAYLOAD_LENGTH_U64))
                .and_then(|s| s.write_u64(len)),
        }
    }

    /// serialise the given unsigned integer
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::se::{Serializer};
    ///
    /// let mut serializer = Serializer::new();
    /// serializer.write_unsigned_integer(0x12)
    ///     .expect("write a negative integer");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0x12].as_ref());
    /// ```
    pub fn write_unsigned_integer(&mut self, value: u64) -> Result<&mut Self> {
        self.write_type_definite(Type::UnsignedInteger, value, None)
    }

    /// serialise the given unsigned integer using a specific encoding
    ///
    /// see `write_unsigned_integer` and `Sz`
    pub fn write_unsigned_integer_sz(&mut self, value: u64, sz: Sz) -> Result<&mut Self> {
        self.write_type_definite(Type::UnsignedInteger, value, Some(sz))
    }

    /// write a negative integer
    ///
    /// This function fails if one tries to write a non negative value.
    ///
    /// ```
    /// use cbor_event::se::{Serializer};
    ///
    /// let mut serializer = Serializer::new();
    /// serializer.write_negative_integer(-12)
    ///     .expect("write a negative integer");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0x2b].as_ref());
    /// ```
    pub fn write_negative_integer(&mut self, value: i64) -> Result<&mut Self> {
        self.write_type_definite(Type::NegativeInteger, (-value - 1) as u64, None)
    }

    /// write a negative integer using a specific encoding
    ///
    /// see `write_negative_integer` and `Sz`
    ///
    /// `value` must be within -1 and -u64::MAX -1 to fit into CBOR nint
    pub fn write_negative_integer_sz(&mut self, value: i128, sz: Sz) -> Result<&mut Self> {
        let value_u64 = (-value - 1)
            .try_into()
            .map_err(|_| Error::InvalidNint(value))?;
        self.write_type_definite(Type::NegativeInteger, value_u64, Some(sz))
    }

    /// write the given object as bytes
    ///
    /// ```
    /// use cbor_event::se::{Serializer};
    ///
    /// let mut serializer = Serializer::new();
    /// serializer.write_bytes(vec![0,1,2,3])
    ///     .expect("write bytes");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0x44, 0,1,2,3].as_ref());
    /// ```
    pub fn write_bytes<B: AsRef<[u8]>>(&mut self, bytes: B) -> Result<&mut Self> {
        let bytes = bytes.as_ref();
        self.write_type_definite(Type::Bytes, bytes.len() as u64, None)
            .map(|s| {
                s.write_raw_bytes(bytes).unwrap();
                s
            })
    }

    /// write the given object as bytes using a specific bytestring encoding
    ///
    /// see `write_bytes` and `StringLenSz`
    pub fn write_bytes_sz<B: AsRef<[u8]>>(
        &mut self,
        bytes: B,
        sz: StringLenSz,
    ) -> Result<&mut Self> {
        let bytes = bytes.as_ref();
        match sz {
            StringLenSz::Len(sz) => self
                .write_type_definite(Type::Bytes, bytes.len() as u64, Some(sz))
                .map(|s| {
                    s.write_raw_bytes(bytes).unwrap();
                    s
                }),
            StringLenSz::Indefinite(lens) => {
                let sz_sum = lens.iter().fold(0, |sum, len| sum + len.0);
                if sz_sum != bytes.len() as u64 {
                    return Err(Error::InvalidIndefiniteString);
                }
                let mut me = self.write_u8(Type::Bytes.to_byte(0x1f))?;
                let mut start = 0;
                for (len, sz) in lens {
                    let end = start + *len as usize;
                    let chunk = &bytes[start..end];
                    me = me.write_bytes_sz(chunk, StringLenSz::Len(*sz))?;
                    start = end;
                }
                me = me.write_u8(Type::Special.to_byte(0x1f))?;
                Ok(me)
            }
        }
    }

    /// write the given object as text
    ///
    /// ```
    /// use cbor_event::se::{Serializer};
    ///
    /// let mut serializer = Serializer::new();
    /// serializer.write_text(r"hello world")
    ///     .expect("write text");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0x6b, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0x77, 0x6F, 0x72, 0x6C, 0x64].as_ref());
    /// ```
    pub fn write_text<S: AsRef<str>>(&mut self, text: S) -> Result<&mut Self> {
        let bytes = text.as_ref().as_bytes();
        self.write_type_definite(Type::Text, bytes.len() as u64, None)
            .map(|s| s.write_raw_bytes(bytes).unwrap())
    }

    /// write the given object as text using a specific string encoding
    ///
    /// see `write_text` and `StringLenSz`
    pub fn write_text_sz<S: AsRef<str>>(&mut self, text: S, sz: StringLenSz) -> Result<&mut Self> {
        let bytes = text.as_ref().as_bytes();
        match sz {
            StringLenSz::Len(sz) => self
                .write_type_definite(Type::Text, bytes.len() as u64, Some(sz))
                .map(|s| s.write_raw_bytes(bytes).unwrap()),
            StringLenSz::Indefinite(lens) => {
                let sz_sum = lens.iter().fold(0, |sum, len| sum + len.0);
                if sz_sum != bytes.len() as u64 {
                    return Err(Error::InvalidIndefiniteString);
                }
                let mut me = self.write_u8(Type::Text.to_byte(0x1f))?;
                let mut start = 0;
                for (len, sz) in lens {
                    let end = start + *len as usize;
                    let chunk = &bytes[start..end];
                    let chunk_str =
                        core::str::from_utf8(chunk).map_err(|_| Error::InvalidLenPassed(*sz))?;
                    me = me.write_text_sz(chunk_str, StringLenSz::Len(*sz))?;
                    start = end;
                }
                me = me.write_u8(Type::Special.to_byte(0x1f))?;
                Ok(me)
            }
        }
    }

    /// start to write an array
    ///
    /// Either you know the length of your array and you can pass it to the funtion
    /// or use an indefinite length.
    ///
    /// - if you set a fixed length of element, you are responsible to set the correct
    ///   amount of elements.
    /// - if you set an indefinite length, you are responsible to write the `Special::Break`
    ///   when your stream ends.
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::{se::{Serializer}, Len};
    ///
    /// let mut serializer = Serializer::new();
    /// serializer
    ///     .write_array(Len::Len(2)).expect("write an array")
    ///     .write_text(r"hello").expect("write text")
    ///     .write_text(r"world").expect("write text");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0x82, 0x65, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x65, 0x77, 0x6F, 0x72, 0x6C, 0x64].as_ref());
    /// ```
    ///
    /// ```
    /// use cbor_event::{se::{Serializer}, Len, Special};
    ///
    /// let mut serializer = Serializer::new();
    /// serializer
    ///     .write_array(Len::Indefinite).expect("write an array")
    ///     .write_text(r"hello").expect("write text")
    ///     .write_text(r"world").expect("write text")
    ///     .write_special(Special::Break).expect("write break");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0x9f, 0x65, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x65, 0x77, 0x6F, 0x72, 0x6C, 0x64, 0xff].as_ref());
    /// ```
    ///
    pub fn write_array(&mut self, len: Len) -> Result<&mut Self> {
        match len {
            Len::Indefinite => self.write_u8(Type::Array.to_byte(0x1f)),
            Len::Len(len) => self.write_type_definite(Type::Array, len, None),
        }
    }

    /// start to write an array using a specific length encoding
    ///
    /// see `write_array` and `LenSz`
    pub fn write_array_sz(&mut self, len: LenSz) -> Result<&mut Self> {
        match len {
            LenSz::Indefinite => self.write_u8(Type::Array.to_byte(0x1f)),
            LenSz::Len(len, sz) => self.write_type_definite(Type::Array, len, Some(sz)),
        }
    }

    /// start to write a map
    ///
    /// Either you know the length of your map and you can pass it to the funtion
    /// or use an indefinite length.
    ///
    /// - if you set a fixed length of element, you are responsible to set the correct
    ///   amount of elements.
    /// - if you set an indefinite length, you are responsible to write the `Special::Break`
    ///   when your stream ends.
    ///
    /// A map is like an array but works by pair of element, so the length is half of the
    /// number of element you are going to write, i.e. the number of pairs, not the number
    /// of elements.
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::{se::{Serializer}, Len};
    ///
    /// let mut serializer = Serializer::new();
    /// serializer
    ///     .write_map(Len::Len(2)).expect("write a map")
    ///     .write_unsigned_integer(1).expect("write unsigned integer")
    ///     .write_text(r"hello").expect("write text")
    ///     .write_unsigned_integer(2).expect("write unsigned integer")
    ///     .write_text(r"world").expect("write text");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0xA2, 01, 0x65, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x02, 0x65, 0x77, 0x6F, 0x72, 0x6C, 0x64].as_ref());
    /// ```
    ///
    /// ```
    /// use cbor_event::{se::{Serializer}, Len, Special};
    ///
    /// let mut serializer = Serializer::new();
    /// serializer
    ///     .write_map(Len::Indefinite).expect("write a map")
    ///     .write_unsigned_integer(1).expect("write unsigned integer")
    ///     .write_text(r"hello").expect("write text")
    ///     .write_unsigned_integer(2).expect("write unsigned integer")
    ///     .write_text(r"world").expect("write text")
    ///     .write_special(Special::Break).expect("write the break");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0xbf, 01, 0x65, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x02, 0x65, 0x77, 0x6F, 0x72, 0x6C, 0x64, 0xff].as_ref());
    /// ```
    ///
    pub fn write_map(&mut self, len: Len) -> Result<&mut Self> {
        match len {
            Len::Indefinite => self.write_u8(Type::Map.to_byte(0x1f)),
            Len::Len(len) => self.write_type_definite(Type::Map, len, None),
        }
    }

    /// start to write a map using a specific length encoding
    ///
    /// see `write_map` and `LenSz`
    pub fn write_map_sz(&mut self, len: LenSz) -> Result<&mut Self> {
        match len {
            LenSz::Indefinite => self.write_u8(Type::Map.to_byte(0x1f)),
            LenSz::Len(len, sz) => self.write_type_definite(Type::Map, len, Some(sz)),
        }
    }

    /// write a tag
    ///
    /// in cbor a tag should be followed by a tagged object. You are responsible
    /// to making sure you are writing the tagged object just after this
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::{se::{Serializer}, Len};
    ///
    /// let mut serializer = Serializer::new();
    /// serializer
    ///     .write_tag(24).expect("write a tag")
    ///     .write_text(r"hello").expect("write text");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0xd8, 0x18, 0x65, 0x68, 0x65, 0x6C, 0x6C, 0x6F].as_ref());
    /// ```
    ///
    pub fn write_tag(&mut self, tag: u64) -> Result<&mut Self> {
        self.write_type_definite(Type::Tag, tag, None)
    }

    /// write a tag using a specific encoding
    ///
    /// see `write_tag` and `Sz`
    pub fn write_tag_sz(&mut self, tag: u64, sz: Sz) -> Result<&mut Self> {
        self.write_type_definite(Type::Tag, tag, Some(sz))
    }

    /// Write a tag that indicates that the following list is a finite
    /// set. See https://www.iana.org/assignments/cbor-tags/cbor-tags.xhtml.
    pub fn write_set_tag(&mut self) -> Result<&mut Self> {
        self.write_type_definite(Type::Tag, 258, None)
    }

    /// write a special value in cbor
    ///
    /// # Example
    ///
    /// ```
    /// use cbor_event::{se::{Serializer}, Len, Special};
    ///
    /// let mut serializer = Serializer::new();
    /// serializer
    ///     .write_array(Len::Indefinite).expect("write an array")
    ///     .write_special(Special::Bool(false)).expect("write false")
    ///     .write_special(Special::Bool(true)).expect("write true")
    ///     .write_special(Special::Null).expect("write null")
    ///     .write_special(Special::Undefined).expect("write undefined")
    ///     .write_special(Special::Break).expect("write the break");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0x9f, 0xf4, 0xf5, 0xf6, 0xf7, 0xff].as_ref());
    /// ```
    pub fn write_special(&mut self, special: Special) -> Result<&mut Self> {
        match special {
            Special::Unassigned(v @ 0..=0x13) => self.write_u8(Type::Special.to_byte(v)),
            Special::Bool(false) => self.write_u8(Type::Special.to_byte(0x14)),
            Special::Bool(true) => self.write_u8(Type::Special.to_byte(0x15)),
            Special::Null => self.write_u8(Type::Special.to_byte(0x16)),
            Special::Undefined => self.write_u8(Type::Special.to_byte(0x17)),
            Special::Unassigned(v) => self
                .write_u8(Type::Special.to_byte(0x18))
                .and_then(|s| s.write_u8(v)),
            Special::Float(f) => self
                .write_u8(Type::Special.to_byte(0x1b))
                .and_then(|s| s.write_f64(f)),
            Special::Break => self.write_u8(Type::Special.to_byte(0x1f)),
        }
    }

    /// Convenient member function to chain serialisation
    pub fn serialize<T: Serialize>(&'a mut self, t: &'a T) -> Result<&mut Self> {
        Serialize::serialize(t, self)
    }
}

// macro derivation for rust array of bytes

macro_rules! serialize_array {
    ( $( $x:expr ),* ) => {
        $(
            impl<T: Serialize> Serialize for [T; $x] {
                fn serialize<'b>(
                    &'b self,
                    serializer: &'b mut Serializer<'b>,
                ) -> Result<&'b mut Serializer<'b>> {
                    serialize_fixed_array(self.iter(), serializer)
                }
            }
        )*
    }
}

serialize_array!(
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
    51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
);

#[cfg(test)]
#[cfg(feature = "alloc")]
mod test {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;

    #[test]
    fn unsigned_integer_0() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_unsigned_integer(0x12)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x12].as_ref());
    }

    #[test]
    fn unsigned_integer_1() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_unsigned_integer(0x20)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x18, 0x20].as_ref());
    }

    #[test]
    fn unsigned_integer_2() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_unsigned_integer(0x2021)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x19, 0x20, 0x21].as_ref());
    }

    #[test]
    fn unsigned_integer_3() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_unsigned_integer(0x20212223)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x1a, 0x20, 0x21, 0x22, 0x23].as_ref());
    }

    #[test]
    fn unsigned_integer_4() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_unsigned_integer(0x2021222324252627)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(
            bytes,
            [0x1b, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27].as_ref()
        );
    }

    #[test]
    fn negative_integer_0() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_negative_integer(-12)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x2b].as_ref());
    }

    #[test]
    fn negative_integer_1() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_negative_integer(-200)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x38, 0xc7].as_ref());
    }

    #[test]
    fn negative_integer_2() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_negative_integer(-13201)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x39, 0x33, 0x90].as_ref());
    }

    #[test]
    fn negative_integer_3() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_negative_integer(-13201782)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x3a, 0x00, 0xc9, 0x71, 0x75].as_ref());
    }

    #[test]
    fn negative_integer_4() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_negative_integer(-9902201782)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(
            bytes,
            [0x3b, 0x00, 0x00, 0x00, 0x02, 0x4E, 0x37, 0x9B, 0xB5].as_ref()
        );
    }

    #[test]
    fn bytes_0() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_bytes(&vec![])
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x40].as_ref());
    }

    #[test]
    fn bytes_1() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_bytes(&vec![0b101010])
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x41, 0b101010].as_ref());
    }

    fn test_special(cbor_type: Special, result: &[u8]) -> bool {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_special(cbor_type)
            .expect("serialize a special");
        let bytes = serializer.finalize();
        bytes == result
    }

    #[test]
    fn special_false() {
        assert!(test_special(Special::Bool(false), [0xf4].as_ref()))
    }
    #[test]
    fn special_true() {
        assert!(test_special(Special::Bool(true), [0xf5].as_ref()))
    }
    #[test]
    fn special_null() {
        assert!(test_special(Special::Null, [0xf6].as_ref()))
    }
    #[test]
    fn special_undefined() {
        assert!(test_special(Special::Undefined, [0xf7].as_ref()))
    }
    #[test]
    fn special_break() {
        assert!(test_special(Special::Break, [0xff].as_ref()))
    }
    #[test]
    fn special_unassigned() {
        assert!(test_special(Special::Unassigned(0), [0xe0].as_ref()));
        assert!(test_special(Special::Unassigned(1), [0xe1].as_ref()));
        assert!(test_special(Special::Unassigned(10), [0xea].as_ref()));
        assert!(test_special(Special::Unassigned(19), [0xf3].as_ref()));
        assert!(test_special(Special::Unassigned(24), [0xf8, 0x18].as_ref()));
    }

    #[test]
    fn special_float() {
        assert!(test_special(
            Special::Float(1.1),
            [0xfb, 0x3f, 0xf1, 0x99, 0x99, 0x99, 0x99, 0x99, 0x9a].as_ref()
        ));
        assert!(test_special(
            Special::Float(-4.1),
            [0xfb, 0xc0, 0x10, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66].as_ref()
        ));
        assert!(test_special(
            Special::Float(f64::INFINITY),
            [0xfb, 0x7f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00].as_ref()
        ));
        assert!(test_special(
            Special::Float(f64::NAN),
            [0xfb, 0x7f, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00].as_ref()
        ));
        assert!(test_special(
            Special::Float(f64::NEG_INFINITY),
            [0xfb, 0xff, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00].as_ref()
        ));
    }

    #[test]
    fn uint_sz() {
        let expected_bytes = vec![
            0x09, 0x18, 0x09, 0x19, 0x00, 0x09, 0x1a, 0x00, 0x00, 0x00, 0x09, 0x1b, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x09,
        ];
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_unsigned_integer_sz(9, Sz::Inline)
            .unwrap()
            .write_unsigned_integer_sz(9, Sz::One)
            .unwrap()
            .write_unsigned_integer_sz(9, Sz::Two)
            .unwrap()
            .write_unsigned_integer_sz(9, Sz::Four)
            .unwrap()
            .write_unsigned_integer_sz(9, Sz::Eight)
            .unwrap();
        let bytes = serializer.finalize();
        assert_eq!(bytes, expected_bytes);
    }

    #[test]
    fn nint_sz() {
        let expected_bytes = vec![
            0x28, 0x38, 0x08, 0x39, 0x00, 0x08, 0x3a, 0x00, 0x00, 0x00, 0x08, 0x3b, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x08,
        ];
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_negative_integer_sz(-9, Sz::Inline)
            .unwrap()
            .write_negative_integer_sz(-9, Sz::One)
            .unwrap()
            .write_negative_integer_sz(-9, Sz::Two)
            .unwrap()
            .write_negative_integer_sz(-9, Sz::Four)
            .unwrap()
            .write_negative_integer_sz(-9, Sz::Eight)
            .unwrap();

        // just outside of cbor NINT range
        let big_nint = -(u64::MAX as i128) - 2;
        assert!(serializer
            .write_negative_integer_sz(big_nint, Sz::Eight)
            .is_err());

        let bytes = serializer.finalize();
        assert_eq!(bytes, expected_bytes);
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
        let mut expected_bytes: Vec<u8> = def_parts.iter().flatten().cloned().collect();
        // also make an indefinite encoded one out all the definite-encoded parts
        expected_bytes.push(0x5F);
        for slice in def_parts.iter() {
            expected_bytes.copy_from_slice(&slice[..]);
        }
        expected_bytes.push(0xFF);
        let indef_bytes = vec![
            0xBA, 0xAD, 0xF0, 0x0D, 0xCA, 0xFE, 0xD0, 0x0D, 0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE,
            0xBE, 0xEF,
        ];
        let indef_lens = &[
            (4, Sz::Inline),
            (4, Sz::One),
            (4, Sz::Two),
            (2, Sz::Four),
            (2, Sz::Eight),
        ];
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_bytes_sz(vec![0xBA, 0xAD, 0xF0, 0x0D], StringLenSz::Len(Sz::Inline))
            .unwrap()
            .write_bytes_sz(vec![0xCA, 0xFE, 0xD0, 0x0D], StringLenSz::Len(Sz::One))
            .unwrap()
            .write_bytes_sz(vec![0xDE, 0xAD, 0xBE, 0xEF], StringLenSz::Len(Sz::Two))
            .unwrap()
            .write_bytes_sz(vec![0xCA, 0xFE], StringLenSz::Len(Sz::Four))
            .unwrap()
            .write_bytes_sz(vec![0xBE, 0xEF], StringLenSz::Len(Sz::Eight))
            .unwrap()
            .write_bytes_sz(indef_bytes, StringLenSz::Indefinite(indef_lens))
            .unwrap();
        let bytes = serializer.finalize();
        assert_eq!(bytes, expected_bytes);
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
        let mut expected_bytes: Vec<u8> = def_parts.iter().flatten().cloned().collect();
        // also make an indefinite encoded one out all the definite-encoded parts
        expected_bytes.push(0x7F);
        for slice in def_parts.iter() {
            expected_bytes.copy_from_slice(&slice[..]);
        }
        expected_bytes.push(0xFF);
        let indef_lens = &[
            (5, Sz::Inline),
            (5, Sz::One),
            (9, Sz::Two),
            (1, Sz::Four),
            (3, Sz::Eight),
        ];
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_text_sz("Hello", StringLenSz::Len(Sz::Inline))
            .unwrap()
            .write_text_sz("World", StringLenSz::Len(Sz::One))
            .unwrap()
            .write_text_sz("日本語", StringLenSz::Len(Sz::Two))
            .unwrap()
            .write_text_sz("9", StringLenSz::Len(Sz::Four))
            .unwrap()
            .write_text_sz("ABC", StringLenSz::Len(Sz::Eight))
            .unwrap()
            .write_text_sz("HelloWorld日本語9ABC", StringLenSz::Indefinite(indef_lens))
            .unwrap();
        let bytes = serializer.finalize();
        assert_eq!(bytes, expected_bytes);
    }

    #[test]
    fn array_sz() {
        let expected_bytes = vec![
            0x80, 0x98, 0x01, 0x99, 0x00, 0x02, 0x9a, 0x00, 0x00, 0x00, 0x03, 0x9b, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x9f,
        ];
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_array_sz(LenSz::Len(0, Sz::Inline))
            .unwrap()
            .write_array_sz(LenSz::Len(1, Sz::One))
            .unwrap()
            .write_array_sz(LenSz::Len(2, Sz::Two))
            .unwrap()
            .write_array_sz(LenSz::Len(3, Sz::Four))
            .unwrap()
            .write_array_sz(LenSz::Len(4, Sz::Eight))
            .unwrap()
            .write_array_sz(LenSz::Indefinite)
            .unwrap();
        let bytes = serializer.finalize();
        assert_eq!(bytes, expected_bytes);
    }

    #[test]
    fn map_sz() {
        let expected_bytes = vec![
            0xa0, 0xb8, 0x01, 0xb9, 0x00, 0x02, 0xba, 0x00, 0x00, 0x00, 0x03, 0xbb, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0xbf,
        ];
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_map_sz(LenSz::Len(0, Sz::Inline))
            .unwrap()
            .write_map_sz(LenSz::Len(1, Sz::One))
            .unwrap()
            .write_map_sz(LenSz::Len(2, Sz::Two))
            .unwrap()
            .write_map_sz(LenSz::Len(3, Sz::Four))
            .unwrap()
            .write_map_sz(LenSz::Len(4, Sz::Eight))
            .unwrap()
            .write_map_sz(LenSz::Indefinite)
            .unwrap();
        let bytes = serializer.finalize();
        assert_eq!(bytes, expected_bytes);
    }

    #[test]
    fn tag_sz() {
        let expected_bytes = vec![
            0x09, 0x18, 0x09, 0x19, 0x00, 0x09, 0x1a, 0x00, 0x00, 0x00, 0x09, 0x1b, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x09,
        ];
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        serializer
            .write_unsigned_integer_sz(9, Sz::Inline)
            .unwrap()
            .write_unsigned_integer_sz(9, Sz::One)
            .unwrap()
            .write_unsigned_integer_sz(9, Sz::Two)
            .unwrap()
            .write_unsigned_integer_sz(9, Sz::Four)
            .unwrap()
            .write_unsigned_integer_sz(9, Sz::Eight)
            .unwrap();
        let bytes = serializer.finalize();
        assert_eq!(bytes, expected_bytes);
    }

    #[test]
    fn write_type_doesnt_fit() {
        let mut vec = vec![];
        let mut serializer = Serializer::new(vec.as_mut_slice());
        assert!(serializer
            .write_type_definite(Type::UnsignedInteger, 23, Some(Sz::Inline))
            .is_ok());
        assert!(serializer
            .write_type_definite(Type::UnsignedInteger, 24, Some(Sz::Inline))
            .is_err());
        assert!(serializer
            .write_type_definite(Type::UnsignedInteger, u8::MAX as u64, Some(Sz::One))
            .is_ok());
        assert!(serializer
            .write_type_definite(Type::UnsignedInteger, u8::MAX as u64 + 1, Some(Sz::One))
            .is_err());
        assert!(serializer
            .write_type_definite(Type::UnsignedInteger, u16::MAX as u64, Some(Sz::Two))
            .is_ok());
        assert!(serializer
            .write_type_definite(Type::UnsignedInteger, u16::MAX as u64 + 1, Some(Sz::Two))
            .is_err());
        assert!(serializer
            .write_type_definite(Type::UnsignedInteger, u32::MAX as u64, Some(Sz::Four))
            .is_ok());
        assert!(serializer
            .write_type_definite(Type::UnsignedInteger, u32::MAX as u64 + 1, Some(Sz::Four))
            .is_err());
        assert!(serializer
            .write_type_definite(Type::UnsignedInteger, u64::MAX as u64, Some(Sz::Eight))
            .is_ok());
    }
}
