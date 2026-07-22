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
use alloc::string::String;
use alloc::vec::Vec;
#[cfg(test)]
use core::iter::repeat_with;

#[cfg(test)]
use quickcheck::{Arbitrary, Gen};

use crate::de::*;
#[cfg(test)]
use crate::error::Error;
use crate::len::Len;
use crate::result::Result;
use crate::se::*;
use crate::types::{Special, SpecialValue, Type};
use core::convert::TryFrom;

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
    /// maps are key-order-preserving pairs of arbitrary `Value`s: RFC 8949
    /// §3.1 allows any type as a map key, and §5.6 leaves duplicate-key
    /// handling to the protocol, so the decoder passes every entry through
    /// in wire order rather than deduplicating or sorting
    Object(Vec<(Value, Value)>),
    IObject(Vec<(Value, Value)>),
    Tag(u64, Box<Value>),
    /// holds [`SpecialValue`], not [`Special`]:
    /// Break is a wire-level terminator, not a data item, so a `Value` cannot contain one
    Special(SpecialValue),
}

impl Serialize for Value {
    fn serialize<'se>(&self, serializer: &'se mut Serializer) -> Result<&'se mut Serializer> {
        match self {
            Value::U64(v) => serializer.write_unsigned_integer(*v),
            // RFC 8949 §3.1: CBOR has no signed-integer type; the sign picks
            // the major type. Non-negative values must be major type 0
            Value::I64(v) if *v >= 0 => serializer
                .write_unsigned_integer(u64::try_from(*v).expect("non-negative i64 fits u64")),
            Value::I64(v) => serializer.write_negative_integer(*v),
            Value::Bytes(v) => serializer.write_bytes(v),
            Value::Text(v) => serializer.write_text(v),
            Value::Array(v) => {
                serializer.write_array(Len::Len(v.len() as u64))?;
                for element in v {
                    serializer.serialize(element)?;
                }
                Ok(serializer)
            }
            Value::IArray(v) => {
                serializer.write_array(Len::Indefinite)?;
                for element in v {
                    serializer.serialize(element)?;
                }
                serializer.write_special(Special::Break)
            }
            Value::Object(v) => {
                serializer.write_map(Len::Len(v.len() as u64))?;
                for (key, value) in v {
                    serializer.serialize(key)?.serialize(value)?;
                }
                Ok(serializer)
            }
            Value::IObject(v) => {
                serializer.write_map(Len::Indefinite)?;
                for (key, value) in v {
                    serializer.serialize(key)?.serialize(value)?;
                }
                serializer.write_special(Special::Break)
            }
            Value::Tag(tag, v) => serializer.write_tag(*tag)?.serialize(v.as_ref()),
            Value::Special(v) => serializer.write_special(Special::from(*v)),
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
                let mut vec = Vec::new();
                match len {
                    Len::Indefinite => {
                        while raw.cbor_type()? != Type::Special || !raw.special_break()? {
                            let k = Deserialize::deserialize(raw)?;
                            let v = Deserialize::deserialize(raw)?;
                            vec.push((k, v));
                        }
                        Ok(Value::IObject(vec))
                    }
                    Len::Len(len) => {
                        for _ in 0..len {
                            let k = Deserialize::deserialize(raw)?;
                            let v = Deserialize::deserialize(raw)?;
                            vec.push((k, v));
                        }
                        Ok(Value::Object(vec))
                    }
                }
            }
            Type::Tag => {
                let tag = raw.tag()?;
                Ok(Value::Tag(tag, Box::new(Deserialize::deserialize(raw)?)))
            }
            // rejects Break: not well-formed as a data item (RFC 8949 App. C).
            // The indefinite-length loops above consume the terminating Break
            // before recursing, so a Break reaching this arm is always dangling
            Type::Special => Ok(Value::Special(SpecialValue::try_from(raw.special()?)?)),
        }
    }
}

// canonical Value integers: non-negative integers are U64 (major type 0),
// so generated I64 must be negative or the round-trip property would
// compare I64(n) against the U64(n) it decodes to
#[cfg(test)]
fn arbitrary_negative_i64<G: Gen>(g: &mut G) -> i64 {
    let v = i64::arbitrary(g);
    if v < 0 { v } else { -v - 1 }
}

#[cfg(test)]
fn arbitrary_value_finite<G: Gen>(g: &mut G) -> Value {
    match u8::arbitrary(g) % 5 {
        0 => Value::U64(Arbitrary::arbitrary(g)),
        1 => Value::I64(arbitrary_negative_i64(g)),
        2 => Value::Bytes(Arbitrary::arbitrary(g)),
        3 => Value::Text(Arbitrary::arbitrary(g)),
        4 => Value::Special(Arbitrary::arbitrary(g)),
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
                            arbitrary_value_indefinite(counter - 1, g),
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
                            arbitrary_value_indefinite(counter - 1, g),
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
            9 => Value::Special(Arbitrary::arbitrary(g)),
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
    use core::assert_matches;

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
    fn float() {
        for f in [
            0.0,
            -0.0,
            1.1,
            f64::MIN,
            f64::MAX,
            f64::INFINITY,
            f64::MIN_POSITIVE,
        ] {
            assert!(test_encode_decode(&Value::Special(SpecialValue::Float(f))).unwrap());
        }
    }

    // NaN != NaN, so the PartialEq-based round-trip property can't cover
    // it; the bits (payload included) must still survive the round-trip
    #[test]
    fn float_nan_roundtrip_bits() {
        for bits in [
            f64::NAN.to_bits(),
            0x7ff8_dead_beef_cafe,
            0xfff0_0000_0000_0001,
        ] {
            let mut se = Serializer::new_vec();
            Value::Special(SpecialValue::Float(f64::from_bits(bits)))
                .serialize(&mut se)
                .unwrap();
            let mut raw = Deserializer::from(se.finalize());
            let decoded: Value = Deserialize::deserialize(&mut raw).unwrap();
            match decoded {
                Value::Special(SpecialValue::Float(f)) => assert_eq!(f.to_bits(), bits),
                other => panic!("decoded {:?}", other),
            }
        }
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
            assert_eq!(decoded, Value::U64(u64::try_from(v).unwrap()));
        }
        // nints below i64::MIN cannot be represented by Value::I64,
        // so they fail to deserialize
        let mut raw =
            Deserializer::from(vec![0x3b, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
        let decoded: Result<Value> = Deserialize::deserialize(&mut raw);
        assert_matches!(decoded, Err(Error::ExpectedI64));
    }

    #[test]
    fn text_invalid_utf8_rejected() {
        // regression guard: Value text decoding must stay strict
        // even if text_sz() internals change
        let mut raw = Deserializer::from(vec![0x62, 0xff, 0xfe]);
        let decoded: Result<Value> = Deserialize::deserialize(&mut raw);
        assert_matches!(decoded, Err(Error::InvalidTextError(_)));

        // map with an invalid-UTF-8 text key (exercises key decoding)
        let mut raw = Deserializer::from(vec![0xa1, 0x62, 0xff, 0xfe, 0x01]);
        let decoded: Result<Value> = Deserialize::deserialize(&mut raw);
        assert_matches!(decoded, Err(Error::InvalidTextError(_)));
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
        assert!(
            test_encode_decode(&Value::Array(vec![
                Value::U64(0),
                Value::Text("some text".to_owned())
            ]))
            .unwrap()
        );
    }

    #[test]
    fn iarray() {
        assert!(test_encode_decode(&Value::IArray(vec![])).unwrap());
        assert!(
            test_encode_decode(&Value::IArray(vec![
                Value::U64(0),
                Value::Text("some text".to_owned())
            ]))
            .unwrap()
        );
    }

    #[test]
    fn tag() {
        assert!(test_encode_decode(&Value::Tag(23, Box::new(Value::U64(0)))).unwrap());
        assert!(test_encode_decode(&Value::Tag(24, Box::new(Value::Bytes(vec![0; 32])))).unwrap());
        assert!(
            test_encode_decode(&Value::Tag(0x1ff, Box::new(Value::Bytes(vec![0; 624])))).unwrap()
        );
    }

    // RFC 8949 §3.1 allows any type as a map key
    #[test]
    fn map_with_arbitrary_key_types() {
        // a1 20 01 = {-1: 1} (e.g. COSE negative integer labels)
        let mut raw = Deserializer::from(vec![0xa1, 0x20, 0x01]);
        let decoded: Value = raw.deserialize().unwrap();
        assert_eq!(
            decoded,
            Value::Object(vec![(Value::I64(-1), Value::U64(1))])
        );

        // a1 81 01 02 = {[1]: 2}, a container as key
        let mut raw = Deserializer::from(vec![0xa1, 0x81, 0x01, 0x02]);
        let decoded: Value = raw.deserialize().unwrap();
        assert_eq!(
            decoded,
            Value::Object(vec![(Value::Array(vec![Value::U64(1)]), Value::U64(2))])
        );

        assert!(test_encode_decode(&decoded).unwrap());
    }

    // RFC 8949 §5.6: duplicate-key handling belongs to the protocol, so the
    // decoder passes all entries through; wire order must survive re-encoding
    #[test]
    fn map_preserves_duplicate_keys_and_order() {
        // a3 02 02 01 01 02 03 = {2: 2, 1: 1, 2: 3}
        let mut raw = Deserializer::from(vec![0xa3, 0x02, 0x02, 0x01, 0x01, 0x02, 0x03]);
        let decoded: Value = raw.deserialize().unwrap();
        assert_eq!(
            decoded,
            Value::Object(vec![
                (Value::U64(2), Value::U64(2)),
                (Value::U64(1), Value::U64(1)),
                (Value::U64(2), Value::U64(3)),
            ])
        );

        let mut se = Serializer::new_vec();
        decoded.serialize(&mut se).unwrap();
        assert_eq!(
            se.finalize(),
            vec![0xa3, 0x02, 0x02, 0x01, 0x01, 0x02, 0x03]
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
