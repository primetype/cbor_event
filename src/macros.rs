/// macro to efficiently serialise the given structure into
/// cbor binary.
///
/// This performs an in memory serialisation and returns the
/// buffer wrapped in a [`Result`](../enum.Result.html).
///
/// ```
/// #[macro_use]
/// extern crate cbor_event;
///
/// # fn main() {
/// let value = 0u64;
/// let bytes = cbor!(value).unwrap();
/// # assert_eq!(bytes, vec![0])
/// # }
/// ```
#[macro_export]
macro_rules! cbor {
    ($x:expr) => {{
        let mut se = ::cbor_event::se::Serializer::new_vec();
        let err = se.serialize(&$x).map(|_| ());
        err.map(|_| se.finalize())
    }};
}

#[test]
fn test_macro() {}
