//! CBOR Value object representation
//!
//! While it is handy to be able to construct into the intermediate value
//! type it is also not recommended to use it as an intermediate type
//! before deserialising concrete type:
//!
//! - it is slow and bloated;
//! - it takes a lot dynamic memory and may not be compatible with the targeted environment;
//!
//! This is why all the objects here are marked as deprecated

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
#[cfg(test)]
use core::iter::repeat_with;

#[cfg(test)]
use quickcheck::{Arbitrary, Gen};

use de::*;
use error::Error;
use len::Len;
use result::Result;
use se::*;
use types::{Special, Type};

/// CBOR Object key, represents the possible supported values for
/// a CBOR key in a CBOR Map.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ObjectKey {
    Integer(u64),
    Bytes(Vec<u8>),
    Text(String),
}
impl ObjectKey {
    /// convert the given `ObjectKey` into a CBOR [`Value`](./struct.Value.html)
    pub fn value(self) -> Value {
        match self {
            ObjectKey::Integer(v) => Value::U64(v),
            ObjectKey::Bytes(v) => Value::Bytes(v),
            ObjectKey::Text(v) => Value::Text(v),
        }
    }
}
impl Serialize for ObjectKey {
    fn serialize<'se>(&self, serializer: &'se mut Serializer) -> Result<&'se mut Serializer> {
        match self {
            ObjectKey::Integer(ref v) => serializer.write_unsigned_integer(*v),
            ObjectKey::Bytes(ref v) => serializer.write_bytes(v),
            ObjectKey::Text(ref v) => serializer.write_text(v),
        }
    }
}
impl Deserialize for ObjectKey {
    fn deserialize(raw: &mut Deserializer) -> Result<Self> {
        match raw.cbor_type()? {
            Type::UnsignedInteger => Ok(ObjectKey::Integer(raw.unsigned_integer()?)),
            Type::Bytes => Ok(ObjectKey::Bytes(raw.bytes()?)),
            Type::Text => Ok(ObjectKey::Text(raw.text()?)),
            t => Err(Error::CustomError(format!(
                "Type `{:?}' is not a support type for CBOR Map's key",
                t
            ))),
        }
    }
}

/// All possible CBOR supported values.
///
/// We advise not to use these objects as an intermediary representation before
/// retrieving custom types as it is a slow and not memory efficient way to do
/// so. However it is handy for debugging or reverse a given protocol.
///
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Value {
    U64(u64),
    I64(i64),
    Bytes(Vec<u8>),
    Text(String),
    Array(Vec<Value>),
    IArray(Vec<Value>),
    Object(BTreeMap<ObjectKey, Value>),
    IObject(BTreeMap<ObjectKey, Value>),
    Tag(u64, Box<Value>),
    Special(Special),
}

impl Serialize for Value {
    fn serialize<'se>(&self, serializer: &'se mut Serializer) -> Result<&'se mut Serializer> {
        match self {
            Value::U64(ref v) => serializer.write_unsigned_integer(*v),
            // RFC 8949 §3.1: CBOR has no signed-integer type; the sign picks
            // the major type. Non-negative values must be major type 0
            Value::I64(ref v) if *v >= 0 => serializer.write_unsigned_integer(*v as u64),
            Value::I64(ref v) => serializer.write_negative_integer(*v),
            Value::Bytes(ref v) => serializer.write_bytes(v),
            Value::Text(ref v) => serializer.write_text(v),
            Value::Array(ref v) => {
                serializer.write_array(Len::Len(v.len() as u64))?;
                for element in v {
                    serializer.serialize(element)?;
                }
                Ok(serializer)
            }
            Value::IArray(ref v) => {
                serializer.write_array(Len::Indefinite)?;
                for element in v {
                    serializer.serialize(element)?;
                }
                serializer.write_special(Special::Break)
            }
            Value::Object(ref v) => {
                serializer.write_map(Len::Len(v.len() as u64))?;
                for element in v {
                    serializer.serialize(element.0)?.serialize(element.1)?;
                }
                Ok(serializer)
            }
            Value::IObject(ref v) => {
                serializer.write_map(Len::Indefinite)?;
                for element in v {
                    serializer.serialize(element.0)?.serialize(element.1)?;
                }
                serializer.write_special(Special::Break)
            }
            Value::Tag(ref tag, ref v) => serializer.write_tag(*tag)?.serialize(v.as_ref()),
            Value::Special(ref v) => serializer.write_special(*v),
        }
    }
}
impl Deserialize for Value {
    fn deserialize(raw: &mut Deserializer) -> Result<Self> {
        match raw.cbor_type()? {
            Type::UnsignedInteger => Ok(Value::U64(raw.unsigned_integer()?)),
            Type::NegativeInteger => Ok(Value::I64(raw.negative_integer()?)),
            Type::Bytes => Ok(Value::Bytes(raw.bytes()?)),
            Type::Text => Ok(Value::Text(raw.text()?)),
            Type::Array => {
                let len = raw.array()?;
                let mut vec = Vec::new();
                match len {
                    Len::Indefinite => {
                        while raw.cbor_type()? != Type::Special || !raw.special_break()? {
                            vec.push(Deserialize::deserialize(raw)?);
                        }
                        Ok(Value::IArray(vec))
                    }
                    Len::Len(len) => {
                        for _ in 0..len {
                            vec.push(Deserialize::deserialize(raw)?);
                        }
                        Ok(Value::Array(vec))
                    }
                }
            }
            Type::Map => {
                let len = raw.map()?;
                let mut vec = BTreeMap::new();
                match len {
                    Len::Indefinite => {
                        while raw.cbor_type()? != Type::Special || !raw.special_break()? {
                            let k = Deserialize::deserialize(raw)?;
                            let v = Deserialize::deserialize(raw)?;
                            vec.insert(k, v);
                        }
                        Ok(Value::IObject(vec))
                    }
                    Len::Len(len) => {
                        for _ in 0..len {
                            let k = Deserialize::deserialize(raw)?;
                            let v = Deserialize::deserialize(raw)?;
                            vec.insert(k, v);
                        }
                        Ok(Value::Object(vec))
                    }
                }
            }
            Type::Tag => {
                let tag = raw.tag()?;
                Ok(Value::Tag(tag, Box::new(Deserialize::deserialize(raw)?)))
            }
            Type::Special => Ok(Value::Special(raw.special()?)),
        }
    }
}

#[cfg(test)]
impl Arbitrary for ObjectKey {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        match u8::arbitrary(g) % 3 {
            0 => ObjectKey::Integer(Arbitrary::arbitrary(g)),
            1 => ObjectKey::Bytes(Arbitrary::arbitrary(g)),
            2 => ObjectKey::Text(Arbitrary::arbitrary(g)),
            _ => unreachable!(),
        }
    }
}

// canonical Value integers: non-negative integers are U64 (major type 0),
// so generated I64 must be negative or the round-trip property would
// compare I64(n) against the U64(n) it decodes to
#[cfg(test)]
fn arbitrary_negative_i64<G: Gen>(g: &mut G) -> i64 {
    let v = i64::arbitrary(g);
    if v < 0 {
        v
    } else {
        -v - 1
    }
}

// Break is a wire-level terminator, not a data value: inside an indefinite
// container it changes the structure and cannot round-trip
#[cfg(test)]
fn arbitrary_special_non_break<G: Gen>(g: &mut G) -> Special {
    match Special::arbitrary(g) {
        Special::Break => Special::Null,
        s => s,
    }
}

#[cfg(test)]
fn arbitrary_value_finite<G: Gen>(g: &mut G) -> Value {
    match u8::arbitrary(g) % 5 {
        0 => Value::U64(Arbitrary::arbitrary(g)),
        1 => Value::I64(arbitrary_negative_i64(g)),
        2 => Value::Bytes(Arbitrary::arbitrary(g)),
        3 => Value::Text(Arbitrary::arbitrary(g)),
        4 => Value::Special(arbitrary_special_non_break(g)),
        _ => unreachable!(),
    }
}

#[cfg(test)]
fn arbitrary_value_indefinite<G: Gen>(counter: usize, g: &mut G) -> Value {
    if counter == 0 {
        arbitrary_value_finite(g)
    } else {
        match u8::arbitrary(g) % 10 {
            0 => Value::U64(u64::arbitrary(g)),
            1 => Value::I64(arbitrary_negative_i64(g)),
            2 => Value::Bytes(Arbitrary::arbitrary(g)),
            3 => Value::Text(Arbitrary::arbitrary(g)),
            4 => {
                let size = usize::arbitrary(g);
                Value::Array(
                    repeat_with(|| arbitrary_value_indefinite(counter - 1, g))
                        .take(size)
                        .collect(),
                )
            }
            5 => {
                let size = usize::arbitrary(g);
                Value::IArray(
                    repeat_with(|| arbitrary_value_indefinite(counter - 1, g))
                        .take(size)
                        .collect(),
                )
            }
            6 => {
                let size = usize::arbitrary(g);
                Value::Object(
                    repeat_with(|| {
                        (
                            ObjectKey::arbitrary(g),
                            arbitrary_value_indefinite(counter - 1, g),
                        )
                    })
                    .take(size)
                    .collect(),
                )
            }
            7 => {
                let size = usize::arbitrary(g);
                Value::IObject(
                    repeat_with(|| {
                        (
                            ObjectKey::arbitrary(g),
                            arbitrary_value_indefinite(counter - 1, g),
                        )
                    })
                    .take(size)
                    .collect(),
                )
            }
            8 => Value::Tag(
                u64::arbitrary(g),
                arbitrary_value_indefinite(counter - 1, g).into(),
            ),
            9 => Value::Special(arbitrary_special_non_break(g)),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
impl Arbitrary for Value {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        arbitrary_value_indefinite(3, g)
    }
}

#[cfg(test)]
mod test {
    use alloc::borrow::ToOwned;
    use alloc::vec;

    use super::super::test_encode_decode;
    use super::*;

    #[test]
    fn u64() {
        assert!(test_encode_decode(&Value::U64(0)).unwrap());
        assert!(test_encode_decode(&Value::U64(23)).unwrap());
        assert!(test_encode_decode(&Value::U64(0xff)).unwrap());
        assert!(test_encode_decode(&Value::U64(0x100)).unwrap());
        assert!(test_encode_decode(&Value::U64(0xffff)).unwrap());
        assert!(test_encode_decode(&Value::U64(0x10000)).unwrap());
        assert!(test_encode_decode(&Value::U64(0xffffffff)).unwrap());
        assert!(test_encode_decode(&Value::U64(0x100000000)).unwrap());
        assert!(test_encode_decode(&Value::U64(0xffffffffffffffff)).unwrap());
    }

    #[test]
    fn i64() {
        assert!(test_encode_decode(&Value::I64(-99)).unwrap());
        assert!(test_encode_decode(&Value::I64(-9999999)).unwrap());
        assert!(test_encode_decode(&Value::I64(-283749237289)).unwrap());
        assert!(test_encode_decode(&Value::I64(i64::MIN)).unwrap());
        // non-negative I64 encodes as major type 0 (RFC 8949 §3.1),
        // so it decodes as U64
        for v in [0i64, 23, 99999, 93892929229] {
            let mut se = Serializer::new_vec();
            Value::I64(v).serialize(&mut se).unwrap();
            let mut raw = Deserializer::from(se.finalize());
            let decoded: Value = Deserialize::deserialize(&mut raw).unwrap();
            assert_eq!(decoded, Value::U64(v as u64));
        }
        // nints below i64::MIN cannot be represented by Value::I64,
        // so they fail to deserialize
        let mut raw =
            Deserializer::from(vec![0x3b, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
        let decoded: Result<Value> = Deserialize::deserialize(&mut raw);
        assert!(matches!(decoded, Err(Error::ExpectedI64)));
    }

    #[test]
    fn text_invalid_utf8_rejected() {
        // regression guard: Value/ObjectKey text decoding must stay strict
        // even if text_sz() internals change
        let mut raw = Deserializer::from(vec![0x62, 0xff, 0xfe]);
        let decoded: Result<Value> = Deserialize::deserialize(&mut raw);
        assert!(matches!(decoded, Err(Error::InvalidTextError(_))));

        // map with an invalid-UTF-8 text key (exercises ObjectKey)
        let mut raw = Deserializer::from(vec![0xa1, 0x62, 0xff, 0xfe, 0x01]);
        let decoded: Result<Value> = Deserialize::deserialize(&mut raw);
        assert!(matches!(decoded, Err(Error::InvalidTextError(_))));
    }

    #[test]
    fn bytes() {
        assert!(test_encode_decode(&Value::Bytes(vec![])).unwrap());
        assert!(test_encode_decode(&Value::Bytes(vec![0; 23])).unwrap());
        assert!(test_encode_decode(&Value::Bytes(vec![0; 24])).unwrap());
        assert!(test_encode_decode(&Value::Bytes(vec![0; 256])).unwrap());
        assert!(test_encode_decode(&Value::Bytes(vec![0; 10293])).unwrap());
        assert!(test_encode_decode(&Value::Bytes(vec![0; 99999000])).unwrap());
    }

    #[test]
    fn text() {
        assert!(test_encode_decode(&Value::Text("".to_owned())).unwrap());
        assert!(test_encode_decode(&Value::Text("hellow world".to_owned())).unwrap());
        assert!(test_encode_decode(&Value::Text("some sentence, some sentence... some sentence...some sentence, some sentence... some sentence...".to_owned())).unwrap());
    }

    #[test]
    fn array() {
        assert!(test_encode_decode(&Value::Array(vec![])).unwrap());
        assert!(test_encode_decode(&Value::Array(vec![
            Value::U64(0),
            Value::Text("some text".to_owned())
        ]))
        .unwrap());
    }

    #[test]
    fn iarray() {
        assert!(test_encode_decode(&Value::IArray(vec![])).unwrap());
        assert!(test_encode_decode(&Value::IArray(vec![
            Value::U64(0),
            Value::Text("some text".to_owned())
        ]))
        .unwrap());
    }

    #[test]
    fn tag() {
        assert!(test_encode_decode(&Value::Tag(23, Box::new(Value::U64(0)))).unwrap());
        assert!(test_encode_decode(&Value::Tag(24, Box::new(Value::Bytes(vec![0; 32])))).unwrap());
        assert!(
            test_encode_decode(&Value::Tag(0x1ff, Box::new(Value::Bytes(vec![0; 624])))).unwrap()
        );
    }

    quickcheck! {
        fn property_encode_decode(value: Value) -> bool {
            test_encode_decode(&value).unwrap()
        }

        // speculative parsing: a wrong-typed parse fails without consuming,
        // and rewinding with set_position replays to an identical parse
        fn property_cursor_rewind(value: Value) -> bool {
            let mut se = Serializer::new_vec();
            value.serialize(&mut se).unwrap();
            let bytes = se.finalize();
            let original_len = bytes.len();
            let mut raw = Deserializer::from(bytes);

            let start = raw.position();
            // pick the wrong parser from the actual type so it is
            // guaranteed to fail whatever the arbitrary value is
            let wrong_parse_failed = if raw.cbor_type().unwrap() == Type::UnsignedInteger {
                raw.text().is_err()
            } else {
                raw.unsigned_integer().is_err()
            };
            let nothing_consumed = raw.position() == start;

            let first: Value = raw.deserialize().unwrap();
            let end = raw.position();
            raw.set_position(start).unwrap();
            let second: Value = raw.deserialize().unwrap();

            wrong_parse_failed
                && nothing_consumed
                && first == second
                && raw.position() == end
                && raw.as_slice().len() + raw.position() == original_len
        }
    }
}
