use Error;

/// `Result` type for CBOR serialisation and deserialisation.
pub type Result<T> = core::result::Result<T, Error>;
