use crate::error::Error;
use crate::result::Result;
use alloc::format;
use core::convert::TryFrom;
#[cfg(test)]
use quickcheck::{Arbitrary, Gen};

/// CBOR Major Types
///
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum Type {
    UnsignedInteger,
    NegativeInteger,
    Bytes,
    Text,
    Array,
    Map,
    Tag,
    Special,
}
impl Type {
    #[must_use]
    pub fn to_byte(self, len: u8) -> u8 {
        assert!(len <= 0b0001_1111);

        len | match self {
            Type::UnsignedInteger => 0b0000_0000,
            Type::NegativeInteger => 0b0010_0000,
            Type::Bytes => 0b0100_0000,
            Type::Text => 0b0110_0000,
            Type::Array => 0b1000_0000,
            Type::Map => 0b1010_0000,
            Type::Tag => 0b1100_0000,
            Type::Special => 0b1110_0000,
        }
    }

    #[must_use]
    pub fn from_byte(byte: u8) -> Type {
        match byte & 0b1110_0000 {
            0b0000_0000 => Type::UnsignedInteger,
            0b0010_0000 => Type::NegativeInteger,
            0b0100_0000 => Type::Bytes,
            0b0110_0000 => Type::Text,
            0b1000_0000 => Type::Array,
            0b1010_0000 => Type::Map,
            0b1100_0000 => Type::Tag,
            0b1110_0000 => Type::Special,
            _ => unreachable!(),
        }
    }
}
impl From<u8> for Type {
    fn from(byte: u8) -> Type {
        Type::from_byte(byte)
    }
}

/// CBOR special (as in Special Primary Type).
#[derive(Debug, PartialEq, PartialOrd, Copy, Clone)]
pub enum Special {
    Bool(bool),
    Null,
    Undefined,
    /// unassigned simple values: `[0..=19]` and `[32..=255]`
    /// (RFC 8949 §3.3; 20..=23 are bool/null/undefined, 24..=31 are
    /// argument widths, reserved, or Break)
    Unassigned(u8),

    /// floats decode from any width (f16/f32/f64) but always serialize
    /// as f64
    Float(f64),
    /// mark the stop of a given indefinite-length item
    Break,
}
impl Special {
    #[inline]
    pub fn unwrap_bool(&self) -> Result<bool> {
        match self {
            Special::Bool(b) => Ok(*b),
            _ => Err(Error::CustomError(format!(
                "Expected Special::Bool, received {:?}",
                self
            ))),
        }
    }

    #[inline]
    pub fn unwrap_null(&self) -> Result<()> {
        match self {
            Special::Null => Ok(()),
            _ => Err(Error::CustomError(format!(
                "Expected Special::Null, received {:?}",
                self
            ))),
        }
    }

    #[inline]
    pub fn unwrap_undefined(&self) -> Result<()> {
        match self {
            Special::Undefined => Ok(()),
            _ => Err(Error::CustomError(format!(
                "Expected Special::Undefined, received {:?}",
                self
            ))),
        }
    }

    #[inline]
    pub fn unwrap_unassigned(&self) -> Result<u8> {
        match self {
            Special::Unassigned(v) => Ok(*v),
            _ => Err(Error::CustomError(format!(
                "Expected Special::Unassigned, received {:?}",
                self
            ))),
        }
    }

    #[inline]
    pub fn unwrap_float(&self) -> Result<f64> {
        match self {
            Special::Float(f) => Ok(*f),
            _ => Err(Error::CustomError(format!(
                "Expected Special::Float, received {:?}",
                self
            ))),
        }
    }

    #[inline]
    pub fn unwrap_break(&self) -> Result<()> {
        match self {
            Special::Break => Ok(()),
            _ => Err(Error::CustomError(format!(
                "Expected Special::Break, received {:?}",
                self
            ))),
        }
    }
}

/// CBOR special values as they exist in the data model (RFC 8949 §2):
/// [`Special`] minus `Break`. Break is a wire-level terminator for
/// indefinite-length containers, not a data item (RFC 8949 Appendix C),
/// so [`Value`](crate::Value) stores this type instead, making a
/// dangling Break unrepresentable.
#[derive(Debug, PartialEq, PartialOrd, Copy, Clone)]
pub enum SpecialValue {
    Bool(bool),
    Null,
    Undefined,
    /// unassigned simple values: `[0..=19]` and `[32..=255]`
    /// (RFC 8949 §3.3; 20..=23 are bool/null/undefined, 24..=31 are
    /// argument widths, reserved, or Break)
    Unassigned(u8),

    /// floats decode from any width (f16/f32/f64) but always serialize
    /// as f64
    Float(f64),
}

impl From<SpecialValue> for Special {
    fn from(v: SpecialValue) -> Special {
        match v {
            SpecialValue::Bool(b) => Special::Bool(b),
            SpecialValue::Null => Special::Null,
            SpecialValue::Undefined => Special::Undefined,
            SpecialValue::Unassigned(u) => Special::Unassigned(u),
            SpecialValue::Float(f) => Special::Float(f),
        }
    }
}

impl TryFrom<Special> for SpecialValue {
    type Error = Error;
    fn try_from(s: Special) -> Result<SpecialValue> {
        match s {
            Special::Bool(b) => Ok(SpecialValue::Bool(b)),
            Special::Null => Ok(SpecialValue::Null),
            Special::Undefined => Ok(SpecialValue::Undefined),
            Special::Unassigned(u) => Ok(SpecialValue::Unassigned(u)),
            Special::Float(f) => Ok(SpecialValue::Float(f)),
            Special::Break => Err(Error::UnexpectedBreak),
        }
    }
}

/// an unassigned simple value with a well-formed encoding:
/// `[0..=19]` or `[32..=255]` (RFC 8949 §3.3)
#[cfg(test)]
fn arbitrary_unassigned<G: Gen>(g: &mut G) -> u8 {
    match u8::arbitrary(g) {
        v @ 0x14..=0x1f => v + 12,
        v => v,
    }
}

#[cfg(test)]
impl Arbitrary for SpecialValue {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        match u8::arbitrary(g) % 5 {
            0 => SpecialValue::Bool(Arbitrary::arbitrary(g)),
            1 => SpecialValue::Null,
            2 => SpecialValue::Undefined,
            3 => SpecialValue::Unassigned(arbitrary_unassigned(g)),
            4 => SpecialValue::Null, // TODO: Float...
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
impl Arbitrary for Special {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        match u8::arbitrary(g) % 6 {
            0 => Special::Bool(Arbitrary::arbitrary(g)),
            1 => Special::Null,
            2 => Special::Undefined,
            3 => Special::Unassigned(arbitrary_unassigned(g)),
            4 => Special::Null, // TODO: Float...
            5 => Special::Break,
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn major_type_byte_encoding() {
        for i in 0b0000_0000..=0b0001_1111 {
            assert!(
                Type::UnsignedInteger == Type::from_byte(Type::to_byte(Type::UnsignedInteger, i))
            );
            assert!(
                Type::NegativeInteger == Type::from_byte(Type::to_byte(Type::NegativeInteger, i))
            );
            assert!(Type::Bytes == Type::from_byte(Type::to_byte(Type::Bytes, i)));
            assert!(Type::Text == Type::from_byte(Type::to_byte(Type::Text, i)));
            assert!(Type::Array == Type::from_byte(Type::to_byte(Type::Array, i)));
            assert!(Type::Map == Type::from_byte(Type::to_byte(Type::Map, i)));
            assert!(Type::Tag == Type::from_byte(Type::to_byte(Type::Tag, i)));
            assert!(Type::Special == Type::from_byte(Type::to_byte(Type::Special, i)));
        }
    }
}
