use error::Error;
#[cfg(test)]
use quickcheck::{Arbitrary, Gen};
use result::Result;

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
    pub fn from_byte(byte: &u8) -> Type {
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
impl From<&u8> for Type {
    fn from(byte: &u8) -> Type {
        Type::from_byte(byte)
    }
}

/// CBOR special (as in Special Primary Type).
#[derive(Debug, PartialEq, PartialOrd, Copy, Clone)]
pub enum Special {
    Bool(bool),
    Null,
    Undefined,
    /// Free to use values within: `[0..=13]` and `[24..=31]`
    Unassigned(u8),

    /// Float is not fully supported in this library and it is advised
    /// to avoid using it for now.
    Float(f64),
    /// mark the stop of a given indefinite-length item
    Break,
}
impl Special {
    #[inline]
    pub fn unwrap_bool(self) -> Result<bool> {
        match self {
            Special::Bool(b) => Ok(b),
            _ => Err(Error::CustomError(
                format_args!("Expected Special::Bool, received {:?}", self)
                    .as_str()
                    .unwrap(),
            )),
        }
    }

    #[inline]
    pub fn unwrap_null(self) -> Result<()> {
        match self {
            Special::Null => Ok(()),
            _ => Err(Error::CustomError(
                format_args!("Expected Special::Null, received {:?}", self)
                    .as_str()
                    .unwrap(),
            )),
        }
    }

    #[inline]
    pub fn unwrap_undefined(self) -> Result<()> {
        match self {
            Special::Undefined => Ok(()),
            _ => Err(Error::CustomError(
                format_args!("Expected Special::Undefined, received {:?}", self)
                    .as_str()
                    .unwrap(),
            )),
        }
    }

    #[inline]
    pub fn unwrap_unassigned(self) -> Result<u8> {
        match self {
            Special::Unassigned(v) => Ok(v),
            _ => Err(Error::CustomError(
                format_args!("Expected Special::Unassigned, received {:?}", self)
                    .as_str()
                    .unwrap(),
            )),
        }
    }

    #[inline]
    pub fn unwrap_float(self) -> Result<f64> {
        match self {
            Special::Float(f) => Ok(f),
            _ => Err(Error::CustomError(
                format_args!("Expected Special::Float, received {:?}", self)
                    .as_str()
                    .unwrap(),
            )),
        }
    }

    #[inline]
    pub fn unwrap_break(self) -> Result<()> {
        match self {
            Special::Break => Ok(()),
            _ => Err(Error::CustomError(
                format_args!("Expected Special::Break, received {:?}", self)
                    .as_str()
                    .unwrap(),
            )),
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
            3 => Special::Unassigned(Arbitrary::arbitrary(g)),
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
            assert_eq!(
                Type::UnsignedInteger,
                Type::from_byte(&Type::to_byte(Type::UnsignedInteger, i))
            );
            assert_eq!(
                Type::NegativeInteger,
                Type::from_byte(&Type::to_byte(Type::NegativeInteger, i))
            );
            assert_eq!(Type::Bytes, Type::from_byte(&Type::to_byte(Type::Bytes, i)));
            assert_eq!(Type::Text, Type::from_byte(&Type::to_byte(Type::Text, i)));
            assert_eq!(Type::Array, Type::from_byte(&Type::to_byte(Type::Array, i)));
            assert_eq!(Type::Map, Type::from_byte(&Type::to_byte(Type::Map, i)));
            assert_eq!(Type::Tag, Type::from_byte(&Type::to_byte(Type::Tag, i)));
            assert_eq!(
                Type::Special,
                Type::from_byte(&Type::to_byte(Type::Special, i))
            );
        }
    }
}
