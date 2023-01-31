use core::error::Error;

/// `Result` type for CBOR serialisation and deserialisation.
pub type Result<T> = core::result::Result<T, dyn Error>;
