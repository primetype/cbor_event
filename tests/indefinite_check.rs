//! Regression tests for indefinite-length container decoding.
//!
//! Two decode loops used to mishandle elements while scanning for the Break
//! terminator (0xff):
//!   - `Value::deserialize` (src/value.rs) panicked on any Special element
//!     that was not Break, e.g. `false`;
//!   - `internal_items_with` (src/de.rs, backing `Vec<T>`/`BTreeMap`) errored
//!     on any element that was NOT Special.
//!
//! At the top of each loop iteration the next item is in exactly one of four
//! classes, which is the coverage argument for these tests: each class is
//! exercised in array and map position, for both the `Value` decoder and the
//! typed decoders.
//!   1. Break               -> terminates the container
//!   2. Special, not Break  -> an element (false/true/null/...)
//!   3. not Special         -> an element
//!   4. end of input        -> error, never a panic
//!
//! Vector provenance: byte strings marked "RFC 8949" are copied verbatim from
//! RFC 8949 Appendix A (the official test vectors). The rest were checked
//! against the `cbor2` Python library as an independent implementation.
//! Comments show CBOR diagnostic notation: `[_ ...]` / `{_ ...}` denote
//! indefinite-length containers (RFC 8949 section 8.1); any vector can be
//! re-checked by pasting the hex into https://cbor.me.

extern crate cbor_event;
use cbor_event::de::Deserializer;
use cbor_event::{SpecialValue, Value};
use std::collections::BTreeMap;

fn de_value(bytes: &[u8]) -> cbor_event::Result<Value> {
    Deserializer::from(bytes.to_vec()).deserialize::<Value>()
}

fn text_key(s: &str) -> Value {
    Value::Text(s.to_owned())
}

// class 1 (Break as first item): 9fff = [_ ], RFC 8949
#[test]
fn value_empty_indefinite_array() {
    assert_eq!(de_value(&[0x9f, 0xff]).unwrap(), Value::IArray(vec![]));
}

// class 1, map position: bfff = {_ }
#[test]
fn value_empty_indefinite_map() {
    assert_eq!(de_value(&[0xbf, 0xff]).unwrap(), Value::IObject(vec![]));
}

// class 2: 9ff4ff = [_ false] -- used to panic on the Break assertion
#[test]
fn value_indefinite_array_with_bool() {
    assert_eq!(
        de_value(&[0x9f, 0xf4, 0xff]).unwrap(),
        Value::IArray(vec![Value::Special(SpecialValue::Bool(false))])
    );
}

// classes 2+3 in map position: bf6346756ef563416d7421ff = {_ "Fun": true, "Amt": -2}, RFC 8949
#[test]
fn value_indefinite_map_rfc_vector() {
    // entries appear in wire order
    let expected = vec![
        (text_key("Fun"), Value::Special(SpecialValue::Bool(true))),
        (text_key("Amt"), Value::I64(-2)),
    ];
    assert_eq!(
        de_value(&[0xbf, 0x63, 0x46, 0x75, 0x6e, 0xf5, 0x63, 0x41, 0x6d, 0x74, 0x21, 0xff])
            .unwrap(),
        Value::IObject(expected)
    );
}

// class 3, nested, definite/indefinite mixed:
// 9f018202039f0405ffff = [_ 1, [2, 3], [_ 4, 5]], RFC 8949
// also checks the definite/indefinite distinction survives the round through Value
#[test]
fn value_nested_mixed_arrays_rfc_vector() {
    assert_eq!(
        de_value(&[0x9f, 0x01, 0x82, 0x02, 0x03, 0x9f, 0x04, 0x05, 0xff, 0xff]).unwrap(),
        Value::IArray(vec![
            Value::U64(1),
            Value::Array(vec![Value::U64(2), Value::U64(3)]),
            Value::IArray(vec![Value::U64(4), Value::U64(5)]),
        ])
    );
}

// bf61610161629f0203ffff = {_ "a": 1, "b": [_ 2, 3]}, RFC 8949
#[test]
fn value_indefinite_map_nested_rfc_vector() {
    let expected = vec![
        (text_key("a"), Value::U64(1)),
        (
            text_key("b"),
            Value::IArray(vec![Value::U64(2), Value::U64(3)]),
        ),
    ];
    assert_eq!(
        de_value(&[0xbf, 0x61, 0x61, 0x01, 0x61, 0x62, 0x9f, 0x02, 0x03, 0xff, 0xff]).unwrap(),
        Value::IObject(expected)
    );
}

// bff401ff = {_ false: 1} -- RFC 8949 §3.1 allows any type as a map key;
// used to error because map keys were the restricted ObjectKey enum
#[test]
fn value_indefinite_map_with_special_key() {
    assert_eq!(
        de_value(&[0xbf, 0xf4, 0x01, 0xff]).unwrap(),
        Value::IObject(vec![(
            Value::Special(SpecialValue::Bool(false)),
            Value::U64(1)
        )])
    );
}

// class 4: 9ff4 = [_ false <EOF, Break and any further elements missing
#[test]
fn value_truncated_indefinite_array_errors() {
    assert!(de_value(&[0x9f, 0xf4]).is_err());
}

// class 4, map position: bf01f4 = {_ 1: false <EOF
#[test]
fn value_truncated_indefinite_map_errors() {
    assert!(de_value(&[0xbf, 0x01, 0xf4]).is_err());
}

// class 3 through the typed decoder: 9f0102ff = [_ 1, 2]
// used to fail with Expected(Special, UnsignedInteger)
#[test]
fn vec_indefinite_with_ints() {
    let v = Deserializer::from(vec![0x9f, 0x01, 0x02, 0xff])
        .deserialize::<Vec<u64>>()
        .unwrap();
    assert_eq!(v, vec![1, 2]);
}

// class 2 through the typed decoder: 9ff4f5ff = [_ false, true]
// elements are Special but not Break
#[test]
fn vec_indefinite_with_bools() {
    let v = Deserializer::from(vec![0x9f, 0xf4, 0xf5, 0xff])
        .deserialize::<Vec<bool>>()
        .unwrap();
    assert_eq!(v, vec![false, true]);
}

// RFC 8949 Appendix C: Break (0xff) is only well-formed directly inside an
// indefinite-length container, terminating it. As a data item it must be
// rejected. These decoded to Ok(..Special(Break)..) before Value stored the
// Break-less SpecialValue type.

// ff = <break> at the top level
#[test]
fn value_top_level_break_errors() {
    assert!(de_value(&[0xff]).is_err());
}

// 81ff = [<break>], definite array element
#[test]
fn value_break_in_definite_array_errors() {
    assert!(de_value(&[0x81, 0xff]).is_err());
}

// bf01ffff = {_ 1: <break>}, map-value position (first ff is not scanned
// for by the terminator loop, which only looks at key position)
#[test]
fn value_break_in_map_value_position_errors() {
    assert!(de_value(&[0xbf, 0x01, 0xff, 0xff]).is_err());
}

// c1ff = 1(<break>), tag content
#[test]
fn value_break_as_tag_content_errors() {
    assert!(de_value(&[0xc1, 0xff]).is_err());
}

// map position of the typed decoder (same loop, map_with entry point):
// bf0102ff = {_ 1: 2}
#[test]
fn btreemap_indefinite_with_ints() {
    let m = Deserializer::from(vec![0xbf, 0x01, 0x02, 0xff])
        .deserialize::<BTreeMap<u64, u64>>()
        .unwrap();
    let mut expected = BTreeMap::new();
    expected.insert(1u64, 2u64);
    assert_eq!(m, expected);
}
