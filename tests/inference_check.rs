use cbor_event::se::{
    Serializer, serialize_fixed_map, serialize_indefinite_array, serialize_indefinite_map,
};
use std::collections::BTreeMap;

#[test]
fn helpers_callable_without_turbofish() {
    let mut map: BTreeMap<u64, u64> = BTreeMap::new();
    map.insert(1, 2);
    let vec = vec![1u64, 2];
    let mut s = Serializer::new_vec();
    serialize_fixed_map(map.iter(), &mut s).unwrap();
    serialize_indefinite_map(map.iter(), &mut s).unwrap();
    serialize_indefinite_array(vec.iter(), &mut s).unwrap();
}
