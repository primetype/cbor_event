//! # CBOR event library
//!
//! [`Deserializer`]: ./de/struct.Deserializer.html
//! [`Deserialize`]: ./de/trait.Deserialize.html
//! [`Serializer`]: ./se/struct.Serializer.html
//! [`Serialize`]: ./se/trait.Serialize.html
//! [`std::io::Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
//! [`Error`]: ./enum.Error.html
//! [`Type`]: ./enum.Type.html
//!
//! `cbor_event` is a minimalist CBOR implementation of the CBOR binary
//! serialisation format. It provides a simple yet efficient way to parse
//! CBOR without the need for an intermediate type representation.
//!
//! Here is the list of supported CBOR primary [`Type`]:
//!
//! - Unsigned and Negative Integers;
//! - Bytes and UTF8 String (**finite length only**);
//! - Array and Map (of finite and indefinite size);
//! - Tag;
//! - Specials (`bool`, `null`... **except floating points**).
//!
//! ## Raw deserialisation: [`Deserializer`]
//!
//! Deserialisation works by consuming a `Deserializer` content. To avoid
//! performance issues some objects use a reference to the original
//! source [`Deserializer`] internal buffer. They are then linked to the object
//! by an associated lifetime, this is true for `Bytes`.
//!
//! ```
//! use cbor_event::de::*;
//!
//! let vec = vec![0x43, 0x01, 0x02, 0x03];
//! let mut raw = Deserializer::from(vec);
//! let bytes = raw.bytes().unwrap();
//!
//! # assert_eq!(bytes.as_slice(), [1,2,3].as_ref());
//! ```
//!
//! For convenience, we provide the trait [`Deserialize`] to help writing
//! simpler deserializers for your types.
//!
//! ## Serialisation: [`Serializer`]
//!
//! To serialise your objects into CBOR we provide a simple object
//! [`Serializer`]. It is configurable with any [`std::io::Write`]
//! objects. [`Serializer`] is meant to be simple to use and to have
//! limited overhead.
//!
//! ```
//! use cbor_event::se::{Serializer};
//!
//! let mut serializer = Serializer::new_vec();
//! serializer.write_negative_integer(-12)
//!     .expect("write a negative integer");
//!
//! # let bytes = serializer.finalize();
//! # assert_eq!(bytes, [0x2b].as_ref());
//! ```

#![no_std]
#[cfg(any(feature = "alloc", test))]
extern crate alloc;
#[cfg(test)]
#[macro_use]
extern crate quickcheck;

pub use de::Deserialize;
pub use error::Error;
pub use len::*;
pub use result::Result;
pub use se::Serialize;
pub use types::*;

pub mod de;
mod error;
mod len;
mod macros;
mod result;
pub mod se;
mod types;
mod value;

const MAX_INLINE_ENCODING: u64 = 23;

const CBOR_PAYLOAD_LENGTH_U8: u8 = 24;
const CBOR_PAYLOAD_LENGTH_U16: u8 = 25;
const CBOR_PAYLOAD_LENGTH_U32: u8 = 26;
const CBOR_PAYLOAD_LENGTH_U64: u8 = 27;

/// exported as a convenient function to test the implementation of
/// [`Serialize`](./se/trait.Serialize.html) and
/// [`Deserialize`](./de/trait.Deserialize.html).
///
#[cfg(test)]
pub fn test_encode_decode<'a, V: Sized + PartialEq + Serialize + Deserialize<'a>>(
    v: &'a V,
    data: &'a mut [u8],
) -> Result<bool> {
    let mut se = se::Serializer::new(data);
    let bytes = v.serialize(&mut se)?.finalize();

    let mut raw = de::Deserializer::from(bytes);
    let v_ = Deserialize::deserialize(&mut raw)?;

    Ok(v == &v_)
}
