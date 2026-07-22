//! CBOR serialisation tooling
use alloc::string::String;
use alloc::vec::Vec;
use core::convert::TryInto;

use crate::error::Error;
use crate::len::{Len, LenSz, StringLenSz, Sz};
use crate::result::Result;
use crate::types::{Special, Type};

/// Exact f64 -> IEEE 754 binary16 narrowing: `Some` only when every bit of
/// `value` survives, i.e. the result decodes back to the identical f64
/// (sign, subnormals and NaN payloads included).
///
/// In software: rust's native f16 is not yet stable (rust-lang/rust#116909)
/// and hardware NaN conversions are not fully specified across platforms
fn f64_to_f16_bits_exact(value: f64) -> Option<u16> {
    let bits = value.to_bits();
    let sign = ((bits >> 63) as u16) << 15;
    let exp = ((bits >> 52) & 0x7ff) as i32;
    let mant = bits & 0x000f_ffff_ffff_ffff;
    match exp {
        0x7ff if mant == 0 => Some(sign | 0x7c00), // ±inf
        // NaN: the payload must fit the 10-bit mantissa. `mant != 0` with
        // the low 42 bits clear guarantees `mant >> 42 != 0`, so the
        // result never aliases the infinity pattern
        0x7ff => (mant & ((1 << 42) - 1) == 0).then_some(sign | 0x7c00 | (mant >> 42) as u16),
        0 if mant == 0 => Some(sign), // ±0
        // f64 subnormals are < 2^-1022, far below the f16 range
        0 => None,
        _ => {
            let e = exp - 1023;
            if (-14..=15).contains(&e) {
                // normal f16: 10 explicit mantissa bits
                (mant & ((1 << 42) - 1) == 0)
                    .then(|| sign | ((e + 15) as u16) << 10 | (mant >> 42) as u16)
            } else if (-24..=-15).contains(&e) {
                // subnormal f16: value = m * 2^-24 for integer m in 1..=0x3ff
                let full = 1 << 52 | mant; // implied leading one
                let shift = 52 - (e + 24); // 43..=52
                (full & ((1u64 << shift) - 1) == 0).then(|| sign | (full >> shift) as u16)
            } else {
                None
            }
        }
    }
}

/// Exact f64 -> IEEE 754 binary32 narrowing, `Some` only when lossless
/// (see [`f64_to_f16_bits_exact`])
fn f64_to_f32_bits_exact(value: f64) -> Option<u32> {
    if value.is_nan() {
        let bits = value.to_bits();
        let mant = bits & 0x000f_ffff_ffff_ffff;
        // payload must fit the 23-bit mantissa; cannot alias infinity
        // (same argument as the f16 NaN case)
        return (mant & ((1 << 29) - 1) == 0)
            .then_some(((bits >> 63) as u32) << 31 | 0x7f80_0000 | (mant >> 29) as u32);
    }
    // non-NaN f64 -> f32 rounding is fully specified by IEEE 754;
    // exact iff widening back is bit-identical
    let narrowed = value as f32;
    (f64::from(narrowed).to_bits() == value.to_bits()).then(|| narrowed.to_bits())
}

/// Smallest CBOR float width that encodes `value` with no loss:
/// every bit, NaN payloads included, survives
/// `write_float_sz(value, smallest_float_sz(value))`.
/// Pair the two for
/// preferred serialization of floats (RFC 8949 §4.2.1).
///
/// Note: a NaN whose payload fits a smaller width shortens to *that
/// payload*, not to the canonical half-width quiet NaN `0xf9 0x7e00`;
/// strictly canonical writers must map NaN to their canonical pattern
/// before calling.
pub fn smallest_float_sz(value: f64) -> Sz {
    if f64_to_f16_bits_exact(value).is_some() {
        Sz::Two
    } else if f64_to_f32_bits_exact(value).is_some() {
        Sz::Four
    } else {
        Sz::Eight
    }
}

pub trait Serialize {
    fn serialize<'a>(&self, serializer: &'a mut Serializer) -> Result<&'a mut Serializer>;
}
impl<T: Serialize> Serialize for &T {
    fn serialize<'se>(&self, serializer: &'se mut Serializer) -> Result<&'se mut Serializer> {
        serializer.serialize(*self)
    }
}
impl Serialize for u64 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer) -> Result<&'a mut Serializer> {
        serializer.write_unsigned_integer(*self)
    }
}
impl Serialize for u32 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer) -> Result<&'a mut Serializer> {
        serializer.write_unsigned_integer(u64::from(*self))
    }
}
impl Serialize for u16 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer) -> Result<&'a mut Serializer> {
        serializer.write_unsigned_integer(u64::from(*self))
    }
}
impl Serialize for u8 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer) -> Result<&'a mut Serializer> {
        serializer.write_unsigned_integer(u64::from(*self))
    }
}
impl Serialize for bool {
    fn serialize<'a>(&self, serializer: &'a mut Serializer) -> Result<&'a mut Serializer> {
        serializer.write_special(Special::Bool(*self))
    }
}
impl Serialize for f32 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer) -> Result<&'a mut Serializer> {
        serializer.write_special(Special::Float(f64::from(*self)))
    }
}
impl Serialize for f64 {
    fn serialize<'a>(&self, serializer: &'a mut Serializer) -> Result<&'a mut Serializer> {
        serializer.write_special(Special::Float(*self))
    }
}
impl Serialize for String {
    fn serialize<'a>(&self, serializer: &'a mut Serializer) -> Result<&'a mut Serializer> {
        serializer.write_text(self)
    }
}
impl Serialize for &[u8] {
    fn serialize<'b>(&self, serializer: &'b mut Serializer) -> Result<&'b mut Serializer> {
        serializer.write_bytes(self)
    }
}
impl<'a, A, B> Serialize for (&'a A, &'a B)
where
    A: Serialize,
    B: Serialize,
{
    fn serialize<'b>(&self, serializer: &'b mut Serializer) -> Result<&'b mut Serializer> {
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
    fn serialize<'b>(&self, serializer: &'b mut Serializer) -> Result<&'b mut Serializer> {
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
    fn serialize<'a>(&self, serializer: &'a mut Serializer) -> Result<&'a mut Serializer> {
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
pub fn serialize_fixed_map<'a, C, K, V>(
    data: C,
    serializer: &mut Serializer,
) -> Result<&mut Serializer>
where
    K: 'a + Serialize,
    V: 'a + Serialize,
    C: Iterator<Item = (&'a K, &'a V)> + ExactSizeIterator,
{
    serializer.write_map(Len::Len(data.len() as u64))?;
    for element in data {
        Serialize::serialize(element.0, serializer)?;
        Serialize::serialize(element.1, serializer)?;
    }
    Ok(serializer)
}

/// helper function to serialise a collection of T as a fixed number of element
///
/// i.e. the size must be known ahead of time
///
pub fn serialize_fixed_array<'a, C, T>(
    data: C,
    serializer: &mut Serializer,
) -> Result<&mut Serializer>
where
    T: 'a + Serialize,
    C: Iterator<Item = &'a T> + ExactSizeIterator,
{
    serializer.write_array(Len::Len(data.len() as u64))?;
    for element in data {
        Serialize::serialize(element, serializer)?;
    }
    Ok(serializer)
}

/// helper function to serialise a map of indefinite number of elements.
///
pub fn serialize_indefinite_map<'a, C, K, V>(
    data: C,
    serializer: &mut Serializer,
) -> Result<&mut Serializer>
where
    K: 'a + Serialize,
    V: 'a + Serialize,
    C: Iterator<Item = (&'a K, &'a V)>,
{
    serializer.write_map(Len::Indefinite)?;
    for element in data {
        Serialize::serialize(element.0, serializer)?;
        Serialize::serialize(element.1, serializer)?;
    }
    serializer.write_special(Special::Break)
}

/// helper function to serialise a collection of T as a indefinite number of element
///
pub fn serialize_indefinite_array<'a, C, T>(
    data: C,
    serializer: &mut Serializer,
) -> Result<&mut Serializer>
where
    T: 'a + Serialize,
    C: Iterator<Item = &'a T>,
{
    serializer.write_array(Len::Indefinite)?;
    for element in data {
        Serialize::serialize(element, serializer)?;
    }
    serializer.write_special(Special::Break)
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
/// let mut serializer = Serializer::new_vec();
/// let mut se = Serializer::new_vec();
/// 0u32.serialize(&mut se).unwrap();
/// serializer.write_bytes(&se.finalize()).unwrap();
/// ```
///
pub fn serialize_cbor_in_cbor<T>(data: T, serializer: &mut Serializer) -> Result<&mut Serializer>
where
    T: Serialize,
{
    let mut se = Serializer::new_vec();
    data.serialize(&mut se)?;
    serializer.write_bytes(se.finalize())
}

// use a default capacity when allocating the Serializer to avoid small reallocation
// at the beginning of the serialisation process as Vec grows by 2, starting from a
// small or an empty serializer will only increase the number of realloc called at
// every _reserve_ calls.
const DEFAULT_CAPACITY: usize = 512;

/// whether `len` is representable with the given length encoding
const fn sz_fits(sz: Sz, len: u64) -> bool {
    match sz {
        Sz::Inline => len <= super::MAX_INLINE_ENCODING,
        Sz::One => len < 0x1_00,
        Sz::Two => len < 0x1_00_00,
        Sz::Four => len < 0x1_00_00_00_00,
        Sz::Eight => true,
    }
}

fn checked_lens_sum(lens: &[(u64, Sz)], expected_len: usize) -> Result<()> {
    let expected_len = u64::try_from(expected_len).map_err(|_| Error::InvalidIndefiniteString)?;
    let actual_len = lens.iter().try_fold(0u64, |sum, (len, _)| {
        sum.checked_add(*len).ok_or(Error::InvalidIndefiniteString)
    })?;
    if actual_len == expected_len {
        Ok(())
    } else {
        Err(Error::InvalidIndefiniteString)
    }
}

fn checked_chunk_end(bytes_len: usize, start: usize, len: u64) -> Result<usize> {
    let len = usize::try_from(len).map_err(|_| Error::InvalidIndefiniteString)?;
    start
        .checked_add(len)
        .filter(|end| *end <= bytes_len)
        .ok_or(Error::InvalidIndefiniteString)
}

/// simple CBOR serializer into an owned byte buffer.
///
/// # Error recovery
///
/// A failed write leaves the output buffer unchanged: arguments are validated
/// before any bytes are emitted, so it is safe to keep using the serializer
/// after handling an error. (Contrast with [`crate::de::Deserializer`], where
/// a failed parse leaves the read position mid-item and the caller rewinds
/// via `set_position`.)
#[derive(Debug)]
pub struct Serializer {
    data: Vec<u8>,
}

impl Serializer {
    /// extend the serializer with the given bytes
    ///
    /// This is not encoding the given bytes in the CBOR format. More a way
    /// to add already CBOR encoded data or to add any bytes that may suite
    /// your protocol.
    pub fn write_raw_bytes(&mut self, bytes: &[u8]) -> Result<&mut Self> {
        self.data.extend_from_slice(bytes);
        Ok(self)
    }

    /// create a new serializer.
    ///
    /// ```
    /// use cbor_event::se::{Serializer};
    ///
    /// let serializer = Serializer::new_vec();
    /// ```
    #[inline]
    #[must_use]
    pub fn new_vec() -> Self {
        Serializer::new(Vec::with_capacity(DEFAULT_CAPACITY))
    }

    #[inline]
    #[must_use]
    pub const fn new(w: Vec<u8>) -> Self {
        Serializer { data: w }
    }

    /// finalize the serializer, returning the serializer bytes
    ///
    /// ```
    /// use cbor_event::se::{Serializer};
    ///
    /// let serializer = Serializer::new_vec();
    ///
    /// let bytes = serializer.finalize();
    ///
    /// # assert!(bytes.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub fn finalize(self) -> Vec<u8> {
        self.data
    }

    #[inline]
    fn write_u8(&mut self, value: u8) -> Result<&mut Self> {
        self.data.push(value);
        Ok(self)
    }

    #[inline]
    fn write_u16(&mut self, value: u16) -> Result<&mut Self> {
        self.data.extend_from_slice(&value.to_be_bytes());
        Ok(self)
    }

    #[inline]
    fn write_u32(&mut self, value: u32) -> Result<&mut Self> {
        self.data.extend_from_slice(&value.to_be_bytes());
        Ok(self)
    }

    #[inline]
    fn write_u64(&mut self, value: u64) -> Result<&mut Self> {
        self.data.extend_from_slice(&value.to_be_bytes());
        Ok(self)
    }

    #[inline]
    fn write_f64(&mut self, value: f64) -> Result<&mut Self> {
        self.data.extend_from_slice(&value.to_be_bytes());
        Ok(self)
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
                if !sz_fits(sz, len) {
                    return Err(Error::InvalidLenPassed(sz));
                }
                sz
            }
        };
        match extra_sz {
            Sz::Inline => {
                let len = u8::try_from(len).map_err(|_| Error::InvalidLenPassed(Sz::Inline))?;
                self.write_u8(cbor_type.to_byte(len))
            }
            Sz::One => {
                let len = u8::try_from(len).map_err(|_| Error::InvalidLenPassed(Sz::One))?;
                self.write_u8(cbor_type.to_byte(super::CBOR_PAYLOAD_LENGTH_U8))?
                    .write_u8(len)
            }
            Sz::Two => {
                let len = u16::try_from(len).map_err(|_| Error::InvalidLenPassed(Sz::Two))?;
                self.write_u8(cbor_type.to_byte(super::CBOR_PAYLOAD_LENGTH_U16))?
                    .write_u16(len)
            }
            Sz::Four => {
                let len = u32::try_from(len).map_err(|_| Error::InvalidLenPassed(Sz::Four))?;
                self.write_u8(cbor_type.to_byte(super::CBOR_PAYLOAD_LENGTH_U32))?
                    .write_u32(len)
            }
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
    /// let mut serializer = Serializer::new_vec();
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
    /// let mut serializer = Serializer::new_vec();
    /// serializer.write_negative_integer(-12)
    ///     .expect("write a negative integer");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0x2b].as_ref());
    /// ```
    pub fn write_negative_integer(&mut self, value: i64) -> Result<&mut Self> {
        // RFC 8949 §3.1: major type 1 encodes only the range -2^64..=-1
        if value >= 0 {
            return Err(Error::InvalidNint(i128::from(value)));
        }
        // computed in i128: `-value` overflows i64 for value == i64::MIN
        let argument =
            u64::try_from(-i128::from(value) - 1).expect("i64 nint argument always fits u64");
        self.write_type_definite(Type::NegativeInteger, argument, None)
    }

    /// write a negative integer using a specific encoding
    ///
    /// see `write_negative_integer` and `Sz`
    ///
    /// `value` must be within the CBOR nint range -2^64..=-1 (RFC 8949 §3.1);
    /// anything else returns `Error::InvalidNint`
    pub fn write_negative_integer_sz(&mut self, value: i128, sz: Sz) -> Result<&mut Self> {
        // RFC 8949 §3.1: major type 1 encodes only the range -2^64..=-1
        if value >= 0 {
            return Err(Error::InvalidNint(value));
        }
        // `-(value + 1)` rather than `-value - 1`:
        // the latter overflows i128 for value == i128::MIN
        // (and with `value < 0` guaranteed above, `value + 1` cannot overflow either).
        // Values below -2^64 yield an argument that fails the u64 conversion.
        let value_u64 = (-(value + 1))
            .try_into()
            .map_err(|_| Error::InvalidNint(value))?;
        self.write_type_definite(Type::NegativeInteger, value_u64, Some(sz))
    }

    /// write the given object as bytes
    ///
    /// ```
    /// use cbor_event::se::{Serializer};
    ///
    /// let mut serializer = Serializer::new_vec();
    /// serializer.write_bytes(vec![0,1,2,3])
    ///     .expect("write bytes");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0x44, 0,1,2,3].as_ref());
    /// ```
    pub fn write_bytes<B: AsRef<[u8]>>(&mut self, bytes: B) -> Result<&mut Self> {
        let bytes = bytes.as_ref();
        self.write_type_definite(Type::Bytes, bytes.len() as u64, None)?;
        self.data.extend_from_slice(bytes);
        Ok(self)
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
            StringLenSz::Len(sz) => {
                self.write_type_definite(Type::Bytes, bytes.len() as u64, Some(sz))?;
                self.data.extend_from_slice(bytes);
                Ok(self)
            }
            StringLenSz::Indefinite(lens) => {
                checked_lens_sum(&lens, bytes.len())?;
                // validate all chunks before writing anything so an error
                // can't leave a partial (unterminated) string in the buffer
                for (len, sz) in lens.iter() {
                    if !sz_fits(*sz, *len) {
                        return Err(Error::InvalidLenPassed(*sz));
                    }
                }
                self.write_u8(Type::Bytes.to_byte(0x1f))?;
                let mut start = 0;
                for (len, sz) in lens {
                    let end = checked_chunk_end(bytes.len(), start, len)?;
                    let chunk = &bytes[start..end];
                    self.write_bytes_sz(chunk, StringLenSz::Len(sz))?;
                    start = end;
                }
                self.write_u8(Type::Special.to_byte(0x1f))?;
                Ok(self)
            }
        }
    }

    /// write the given object as text
    ///
    /// ```
    /// use cbor_event::se::{Serializer};
    ///
    /// let mut serializer = Serializer::new_vec();
    /// serializer.write_text(r"hello world")
    ///     .expect("write text");
    ///
    /// # let bytes = serializer.finalize();
    /// # assert_eq!(bytes, [0x6b, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0x77, 0x6F, 0x72, 0x6C, 0x64].as_ref());
    /// ```
    pub fn write_text<S: AsRef<str>>(&mut self, text: S) -> Result<&mut Self> {
        let bytes = text.as_ref().as_bytes();
        self.write_type_definite(Type::Text, bytes.len() as u64, None)?;
        self.data.extend_from_slice(bytes);
        Ok(self)
    }

    /// write the given object as text using a specific string encoding
    ///
    /// see `write_text` and `StringLenSz`
    pub fn write_text_sz<S: AsRef<str>>(&mut self, text: S, sz: StringLenSz) -> Result<&mut Self> {
        let bytes = text.as_ref().as_bytes();
        match sz {
            StringLenSz::Len(sz) => {
                self.write_type_definite(Type::Text, bytes.len() as u64, Some(sz))?;
                self.data.extend_from_slice(bytes);
                Ok(self)
            }
            StringLenSz::Indefinite(lens) => {
                checked_lens_sum(&lens, bytes.len())?;
                // validate all chunks before writing anything so an error
                // can't leave a partial (unterminated) string in the buffer.
                let mut start = 0;
                for (len, sz) in lens.iter() {
                    let end = checked_chunk_end(bytes.len(), start, *len)?;
                    // used for validation only (dropped right after) and doesn't modify bytes.
                    // String::from_utf8 (not str::from_utf8) to preserve FromUtf8Error
                    String::from_utf8(bytes[start..end].to_vec())?;
                    if !sz_fits(*sz, *len) {
                        return Err(Error::InvalidLenPassed(*sz));
                    }
                    start = end;
                }
                self.write_u8(Type::Text.to_byte(0x1f))?;
                let mut start = 0;
                for (len, sz) in lens {
                    let end = checked_chunk_end(bytes.len(), start, len)?;
                    self.write_type_definite(Type::Text, len, Some(sz))?;
                    self.data.extend_from_slice(&bytes[start..end]);
                    start = end;
                }
                self.write_u8(Type::Special.to_byte(0x1f))?;
                Ok(self)
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
    /// let mut serializer = Serializer::new_vec();
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
    /// let mut serializer = Serializer::new_vec();
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
    /// let mut serializer = Serializer::new_vec();
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
    /// let mut serializer = Serializer::new_vec();
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
    /// let mut serializer = Serializer::new_vec();
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
    /// let mut serializer = Serializer::new_vec();
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
            // 20..=23 are assigned (the Bool/Null/Undefined arms above);
            // encoding them as Unassigned would alias those variants and
            // break round-tripping. 24..=31 have no well-formed encoding
            // at all (RFC 8949 §3.3)
            Special::Unassigned(v @ 0x14..=0x1f) => Err(Error::InvalidSimpleValue(v)),
            Special::Unassigned(v) => self
                .write_u8(Type::Special.to_byte(0x18))
                .and_then(|s| s.write_u8(v)),
            Special::Float(f) => self
                .write_u8(Type::Special.to_byte(0x1b))
                .and_then(|s| s.write_f64(f)),
            Special::Break => self.write_u8(Type::Special.to_byte(0x1f)),
        }
    }

    /// write a float using a specific encoding
    ///
    /// see `write_special` ([`Special::Float`]) and `Sz`. Floats only have
    /// 2, 4 and 8 byte encodings (RFC 8949 §3.3), so `sz` must be
    /// `Sz::Two`, `Sz::Four` or `Sz::Eight` and `value` must be exactly
    /// representable at that width (NaN payload included); anything else
    /// returns `Error::InvalidLenPassed`. Round-trips byte-exactly through
    /// [`Deserializer::float_sz`].
    ///
    /// [`Deserializer::float_sz`]: crate::de::Deserializer::float_sz
    pub fn write_float_sz(&mut self, value: f64, sz: Sz) -> Result<&mut Self> {
        match sz {
            Sz::Inline | Sz::One => Err(Error::InvalidLenPassed(sz)),
            Sz::Two => {
                let bits = f64_to_f16_bits_exact(value).ok_or(Error::InvalidLenPassed(sz))?;
                self.write_u8(Type::Special.to_byte(0x19))
                    .and_then(|s| s.write_u16(bits))
            }
            Sz::Four => {
                let bits = f64_to_f32_bits_exact(value).ok_or(Error::InvalidLenPassed(sz))?;
                self.write_u8(Type::Special.to_byte(0x1a))
                    .and_then(|s| s.write_u32(bits))
            }
            Sz::Eight => self
                .write_u8(Type::Special.to_byte(0x1b))
                .and_then(|s| s.write_f64(value)),
        }
    }

    /// Convenient member function to chain serialisation
    pub fn serialize<T: Serialize>(&mut self, t: &T) -> Result<&mut Self> {
        Serialize::serialize(t, self)
    }
}

// macro derivation for rust array of bytes

macro_rules! serialize_array {
    ( $( $x:expr ),* ) => {
        $(
            impl<T: Serialize> Serialize for [T; $x] {
                fn serialize<'b>(
                    &self,
                    serializer: &'b mut Serializer,
                ) -> Result<&'b mut Serializer> {
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
mod test {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;
    use core::assert_matches;

    #[test]
    fn unsigned_integer_0() {
        let mut serializer = Serializer::new_vec();
        serializer
            .write_unsigned_integer(0x12)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x12].as_ref());
    }

    #[test]
    fn unsigned_integer_1() {
        let mut serializer = Serializer::new_vec();
        serializer
            .write_unsigned_integer(0x20)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x18, 0x20].as_ref());
    }

    #[test]
    fn unsigned_integer_2() {
        let mut serializer = Serializer::new_vec();
        serializer
            .write_unsigned_integer(0x2021)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x19, 0x20, 0x21].as_ref());
    }

    #[test]
    fn unsigned_integer_3() {
        let mut serializer = Serializer::new_vec();
        serializer
            .write_unsigned_integer(0x20212223)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x1a, 0x20, 0x21, 0x22, 0x23].as_ref());
    }

    #[test]
    fn unsigned_integer_4() {
        let mut serializer = Serializer::new_vec();
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
    fn negative_integer_sz_bounds() {
        // RFC 8949 §3.1: major type 1 covers exactly -2^64..=-1
        let min_nint = -i128::from(u64::MAX) - 1; // -2^64
        let mut serializer = Serializer::new_vec();
        serializer
            .write_negative_integer_sz(min_nint, Sz::Eight)
            .expect("write -2^64");
        assert_eq!(
            serializer.finalize(),
            [0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff].as_ref()
        );
        // below -2^64 needs a bignum (tag 3), not major type 1
        let mut serializer = Serializer::new_vec();
        assert_matches!(
            serializer.write_negative_integer_sz(min_nint - 1, Sz::Eight),
            Err(Error::InvalidNint(_))
        );
        // i128::MIN doesn't panic (i.e.: no `-value - 1` bug)
        assert_matches!(
            serializer.write_negative_integer_sz(i128::MIN, Sz::Eight),
            Err(Error::InvalidNint(i128::MIN))
        );
        // non-negative is rejected like the i64 variant; i128::MAX would
        // overflow in `value + 1` if it reached the argument computation
        assert_matches!(
            serializer.write_negative_integer_sz(0, Sz::One),
            Err(Error::InvalidNint(0))
        );
        assert_matches!(
            serializer.write_negative_integer_sz(i128::MAX, Sz::Eight),
            Err(Error::InvalidNint(i128::MAX))
        );
    }

    #[test]
    fn negative_integer_rejects_non_negative() {
        // RFC 8949 §3.1: major type 1 encodes only -2^64..=-1
        let mut serializer = Serializer::new_vec();
        assert_matches!(
            serializer.write_negative_integer(0),
            Err(Error::InvalidNint(0))
        );
        assert_matches!(
            serializer.write_negative_integer(42),
            Err(Error::InvalidNint(42))
        );
    }

    #[test]
    fn negative_integer_i64_min() {
        // -(i64::MIN) overflows i64, so the argument computation must not
        // be done in i64; i64::MIN encodes as argument 2^63 - 1
        let mut serializer = Serializer::new_vec();
        serializer
            .write_negative_integer(i64::MIN)
            .expect("write i64::MIN");
        let bytes = serializer.finalize();
        assert_eq!(
            bytes,
            [0x3b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff].as_ref()
        );
    }

    #[test]
    fn negative_integer_0() {
        let mut serializer = Serializer::new_vec();
        serializer
            .write_negative_integer(-12)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x2b].as_ref());
    }

    #[test]
    fn negative_integer_1() {
        let mut serializer = Serializer::new_vec();
        serializer
            .write_negative_integer(-200)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x38, 0xc7].as_ref());
    }

    #[test]
    fn negative_integer_2() {
        let mut serializer = Serializer::new_vec();
        serializer
            .write_negative_integer(-13201)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x39, 0x33, 0x90].as_ref());
    }

    #[test]
    fn negative_integer_3() {
        let mut serializer = Serializer::new_vec();
        serializer
            .write_negative_integer(-13201782)
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x3a, 0x00, 0xc9, 0x71, 0x75].as_ref());
    }

    #[test]
    fn negative_integer_4() {
        let mut serializer = Serializer::new_vec();
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
        let mut serializer = Serializer::new_vec();
        serializer
            .write_bytes(vec![])
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x40].as_ref());
    }

    #[test]
    fn bytes_1() {
        let mut serializer = Serializer::new_vec();
        serializer
            .write_bytes(vec![0b101010])
            .expect("write unsigned integer");
        let bytes = serializer.finalize();
        assert_eq!(bytes, [0x41, 0b101010].as_ref());
    }

    fn test_special(cbor_type: Special, result: &[u8]) -> bool {
        let mut serializer = Serializer::new_vec();
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
        assert!(test_special(Special::Unassigned(32), [0xf8, 0x20].as_ref()));
        assert!(test_special(
            Special::Unassigned(255),
            [0xf8, 0xff].as_ref()
        ));
    }

    #[test]
    fn special_unassigned_no_well_formed_encoding() {
        for v in 20..=31 {
            assert!(
                Serializer::new_vec()
                    .write_special(Special::Unassigned(v))
                    .is_err()
            );
        }
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

    fn float_sz_bytes(value: f64, sz: Sz) -> Result<Vec<u8>> {
        let mut se = Serializer::new_vec();
        se.write_float_sz(value, sz)?;
        Ok(se.finalize())
    }

    #[test]
    fn write_float_sz() {
        // the same value at every width (RFC 8949 Appendix A: 1.5 = 0xf93e00)
        assert_eq!(float_sz_bytes(1.5, Sz::Two).unwrap(), [0xf9, 0x3e, 0x00]);
        assert_eq!(
            float_sz_bytes(1.5, Sz::Four).unwrap(),
            [0xfa, 0x3f, 0xc0, 0x00, 0x00]
        );
        assert_eq!(
            float_sz_bytes(1.5, Sz::Eight).unwrap(),
            [0xfb, 0x3f, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
        );
        // edge cases at f16: min subnormal, max finite, ±0, ±inf
        assert_eq!(
            float_sz_bytes(5.960464477539063e-8, Sz::Two).unwrap(),
            [0xf9, 0x00, 0x01]
        );
        assert_eq!(
            float_sz_bytes(65504.0, Sz::Two).unwrap(),
            [0xf9, 0x7b, 0xff]
        );
        assert_eq!(float_sz_bytes(-0.0, Sz::Two).unwrap(), [0xf9, 0x80, 0x00]);
        assert_eq!(
            float_sz_bytes(f64::NEG_INFINITY, Sz::Two).unwrap(),
            [0xf9, 0xfc, 0x00]
        );
        // NaN payloads narrow when they fit the smaller mantissa
        let nan16 = f64::from_bits(0x7ff0_0000_0000_0000 | 0x201 << 42);
        assert_eq!(float_sz_bytes(nan16, Sz::Two).unwrap(), [0xf9, 0x7e, 0x01]);
        let nan32 = f64::from_bits(0xfff0_0000_0000_0000 | 0x40_0001 << 29);
        assert_eq!(
            float_sz_bytes(nan32, Sz::Four).unwrap(),
            [0xfa, 0xff, 0xc0, 0x00, 0x01]
        );
        // f32 subnormal boundaries: min subnormal 2^-149 and multiples
        // are exact, values needing finer precision are rejected
        let min_sub = f64::from(f32::from_bits(1));
        assert_eq!(
            float_sz_bytes(min_sub, Sz::Four).unwrap(),
            [0xfa, 0x00, 0x00, 0x00, 0x01]
        );
        assert_eq!(
            float_sz_bytes(min_sub * 3.0, Sz::Four).unwrap(),
            [0xfa, 0x00, 0x00, 0x00, 0x03]
        );
        assert!(float_sz_bytes(min_sub / 2.0, Sz::Four).is_err()); // 2^-150
        assert!(float_sz_bytes(min_sub * 1.5, Sz::Four).is_err()); // midpoint
    }

    quickcheck! {
        // differential against the half crate (the reference f16
        // implementation): our exact-narrowing decision must match
        // "does half's rounding round-trip x unchanged?", and on success
        // produce the same bits
        fn property_f16_narrowing_matches_half(bits: crate::types::AnyBits, from_f16: bool) -> bool {
            // random f64 bit patterns are almost never f16-representable,
            // so half the cases start from a genuine f16 widened by half
            // itself (also exercising the reference widening path)
            let x = if from_f16 {
                half::f16::from_bits(bits.0 as u16).to_f64()
            } else {
                f64::from_bits(bits.0)
            };
            if x.is_nan() {
                // NaN exactness is about payload width, where half is not
                // a fair oracle (it quiets signaling NaNs); NaNs are
                // covered by the exhaustive byte round-trip test instead
                return true;
            }
            let h = half::f16::from_f64(x);
            let exact_per_half = h.to_f64().to_bits() == x.to_bits();
            match f64_to_f16_bits_exact(x) {
                Some(b) => exact_per_half && b == h.to_bits(),
                None => !exact_per_half,
            }
        }
    }

    #[test]
    fn smallest_float_sz_picks_tightest_lossless_width() {
        let cases: &[(f64, Sz)] = &[
            (0.0, Sz::Two),
            (-0.0, Sz::Two),
            (1.5, Sz::Two),
            (65504.0, Sz::Two), // max finite f16
            (f64::INFINITY, Sz::Two),
            (f64::NAN, Sz::Two),
            (65520.0, Sz::Four), // just above f16 range, f32-exact
            (100000.0, Sz::Four),
            (f64::from(f32::MAX), Sz::Four),
            (f64::from(f32::from_bits(1)), Sz::Four), // min f32 subnormal
            (1.1, Sz::Eight),
            (1e300, Sz::Eight),
            (f64::MIN_POSITIVE, Sz::Eight),
        ];
        for (v, expected) in cases {
            assert_eq!(smallest_float_sz(*v), *expected, "value: {}", v);
        }
    }

    quickcheck! {
        // the chosen width is lossless (bit-exact through a byte round
        // trip) and minimal (every smaller width fails)
        fn property_smallest_float_sz(bits: crate::types::AnyBits, mode: u8) -> bool {
            // random f64 bits are almost always Sz::Eight; derive some
            // values from f32/f16 space so Two/Four get real coverage
            let v = match mode % 3 {
                0 => f64::from_bits(bits.0),
                1 => f64::from(f32::from_bits(bits.0 as u32)),
                _ => half::f16::from_bits(bits.0 as u16).to_f64(),
            };
            let sz = smallest_float_sz(v);
            let mut se = Serializer::new_vec();
            se.write_float_sz(v, sz).unwrap();
            let mut raw = crate::de::Deserializer::from(se.finalize());
            let (back, back_sz) = raw.float_sz().unwrap();
            if back.to_bits() != v.to_bits() || back_sz != sz {
                return false;
            }
            let smaller: &[Sz] = match sz {
                Sz::Four => &[Sz::Two],
                Sz::Eight => &[Sz::Two, Sz::Four],
                _ => &[],
            };
            smaller
                .iter()
                .all(|s| Serializer::new_vec().write_float_sz(v, *s).is_err())
        }
    }

    #[test]
    fn write_float_sz_rejects_inexact() {
        // not exactly representable at the requested width
        assert_matches!(
            float_sz_bytes(1.1, Sz::Two),
            Err(Error::InvalidLenPassed(Sz::Two))
        );
        assert_matches!(float_sz_bytes(1.1, Sz::Four), Err(_));
        // magnitude out of range: overflow and underflow
        assert_matches!(float_sz_bytes(65520.0, Sz::Two), Err(_));
        assert_matches!(float_sz_bytes(1e39, Sz::Four), Err(_));
        assert_matches!(float_sz_bytes(2.9802322387695312e-8, Sz::Two), Err(_)); // 2^-25
        assert_matches!(float_sz_bytes(1e-50, Sz::Four), Err(_));
        // f64 subnormals are below every f16/f32 subnormal
        assert_matches!(float_sz_bytes(f64::MIN_POSITIVE / 2.0, Sz::Two), Err(_));
        // NaN payload that does not fit the narrower mantissa
        let nan = f64::from_bits(0x7ff8_0000_0000_0001);
        assert_matches!(float_sz_bytes(nan, Sz::Two), Err(_));
        assert_matches!(float_sz_bytes(nan, Sz::Four), Err(_));
        // floats have no 0, 1 byte encodings (RFC 8949 §3.3)
        assert_matches!(
            float_sz_bytes(1.5, Sz::Inline),
            Err(Error::InvalidLenPassed(Sz::Inline))
        );
        assert_matches!(
            float_sz_bytes(1.5, Sz::One),
            Err(Error::InvalidLenPassed(Sz::One))
        );
    }

    #[test]
    fn uint_sz() {
        let expected_bytes = vec![
            0x09, 0x18, 0x09, 0x19, 0x00, 0x09, 0x1a, 0x00, 0x00, 0x00, 0x09, 0x1b, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x09,
        ];
        let mut serializer = Serializer::new_vec();
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
        let mut serializer = Serializer::new_vec();
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
        let big_nint = -i128::from(u64::MAX) - 2;
        assert!(
            serializer
                .write_negative_integer_sz(big_nint, Sz::Eight)
                .is_err()
        );

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
            expected_bytes.extend_from_slice(&slice[..]);
        }
        expected_bytes.push(0xFF);
        let indef_bytes = vec![
            0xBA, 0xAD, 0xF0, 0x0D, 0xCA, 0xFE, 0xD0, 0x0D, 0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE,
            0xBE, 0xEF,
        ];
        let indef_lens = vec![
            (4, Sz::Inline),
            (4, Sz::One),
            (4, Sz::Two),
            (2, Sz::Four),
            (2, Sz::Eight),
        ];
        let mut serializer = Serializer::new_vec();
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
            expected_bytes.extend_from_slice(&slice[..]);
        }
        expected_bytes.push(0xFF);
        let indef_lens = vec![
            (5, Sz::Inline),
            (5, Sz::One),
            (9, Sz::Two),
            (1, Sz::Four),
            (3, Sz::Eight),
        ];
        let mut serializer = Serializer::new_vec();
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
    fn text_sz_chunk_split_inside_utf8_char() {
        // 'é' is 2 bytes; chunk lens 1/1 would split it mid-character
        let mut serializer = Serializer::new_vec();
        let result = serializer.write_text_sz(
            "é",
            StringLenSz::Indefinite(vec![(1, Sz::Inline), (1, Sz::Inline)]),
        );
        assert_matches!(result, Err(Error::InvalidTextError(_)));
        // the failed write must not leave partial output in the buffer
        serializer.write_unsigned_integer(1).expect("write uint");
        assert_eq!(serializer.finalize(), vec![0x01]);
    }

    #[test]
    fn bytes_sz_error_leaves_no_partial_output() {
        let mut serializer = Serializer::new_vec();
        // 300 doesn't fit Sz::Inline (max 23), but only fails inside the chunk loop
        let result = serializer.write_bytes_sz(
            vec![0u8; 300],
            StringLenSz::Indefinite(vec![(300, Sz::Inline)]),
        );
        assert_matches!(result, Err(Error::InvalidLenPassed(Sz::Inline)));
        serializer.write_unsigned_integer(1).expect("write uint");
        assert_eq!(serializer.finalize(), vec![0x01]);
    }

    #[test]
    fn indefinite_string_length_overflow_errors_without_partial_output() {
        let mut serializer = Serializer::new_vec();
        let result = serializer.write_bytes_sz(
            [],
            StringLenSz::Indefinite(vec![(u64::MAX, Sz::Eight), (1, Sz::Inline)]),
        );
        assert_matches!(result, Err(Error::InvalidIndefiniteString));
        assert_eq!(serializer.finalize(), Vec::<u8>::new());

        let mut serializer = Serializer::new_vec();
        let result = serializer.write_text_sz(
            "",
            StringLenSz::Indefinite(vec![(u64::MAX, Sz::Eight), (1, Sz::Inline)]),
        );
        assert_matches!(result, Err(Error::InvalidIndefiniteString));
        assert_eq!(serializer.finalize(), Vec::<u8>::new());
    }

    #[test]
    fn array_sz() {
        let expected_bytes = vec![
            0x80, 0x98, 0x01, 0x99, 0x00, 0x02, 0x9a, 0x00, 0x00, 0x00, 0x03, 0x9b, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x9f,
        ];
        let mut serializer = Serializer::new_vec();
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
        let mut serializer = Serializer::new_vec();
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
        let mut serializer = Serializer::new_vec();
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
        let mut serializer = Serializer::new_vec();
        assert!(
            serializer
                .write_type_definite(Type::UnsignedInteger, 23, Some(Sz::Inline))
                .is_ok()
        );
        assert!(
            serializer
                .write_type_definite(Type::UnsignedInteger, 24, Some(Sz::Inline))
                .is_err()
        );
        assert!(
            serializer
                .write_type_definite(Type::UnsignedInteger, u64::from(u8::MAX), Some(Sz::One))
                .is_ok()
        );
        assert!(
            serializer
                .write_type_definite(Type::UnsignedInteger, u64::from(u8::MAX) + 1, Some(Sz::One))
                .is_err()
        );
        assert!(
            serializer
                .write_type_definite(Type::UnsignedInteger, u64::from(u16::MAX), Some(Sz::Two))
                .is_ok()
        );
        assert!(
            serializer
                .write_type_definite(
                    Type::UnsignedInteger,
                    u64::from(u16::MAX) + 1,
                    Some(Sz::Two)
                )
                .is_err()
        );
        assert!(
            serializer
                .write_type_definite(Type::UnsignedInteger, u64::from(u32::MAX), Some(Sz::Four))
                .is_ok()
        );
        assert!(
            serializer
                .write_type_definite(
                    Type::UnsignedInteger,
                    u64::from(u32::MAX) + 1,
                    Some(Sz::Four)
                )
                .is_err()
        );
        assert!(
            serializer
                .write_type_definite(Type::UnsignedInteger, u64::MAX, Some(Sz::Eight))
                .is_ok()
        );
    }
}
