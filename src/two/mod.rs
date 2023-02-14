use crate::{Error, LenSz, Result, Sz, Type};

#[derive(Default)]
pub struct Deserializer;

impl Deserializer {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    fn u8(&self, bytes: &[u8]) -> Result<u64> {
        if bytes.is_empty() {
            Err(Error::NotEnough(bytes.len(), 1))
        } else {
            Ok(bytes[0] as u64)
        }
    }
    #[inline]
    fn u16(&self, bytes: &[u8]) -> Result<u64> {
        if bytes.len() < 2 {
            Err(Error::NotEnough(bytes.len(), 2))
        } else {
            let b1 = bytes[0] as u64;
            let b2 = bytes[1] as u64;
            Ok(b1 << 8 | b2)
        }
    }
    #[inline]
    fn u32(&self, bytes: &[u8]) -> Result<u64> {
        if bytes.len() < 4 {
            Err(Error::NotEnough(bytes.len(), 4))
        } else {
            let b1 = bytes[0] as u64;
            let b2 = bytes[1] as u64;
            let b3 = bytes[2] as u64;
            let b4 = bytes[3] as u64;
            Ok(b1 << 24 | b2 << 16 | b3 << 8 | b4)
        }
    }
    #[inline]
    fn u64(&self, bytes: &[u8]) -> Result<u64> {
        if bytes.len() < 8 {
            Err(Error::NotEnough(bytes.len(), 8))
        } else {
            let b1 = bytes[0] as u64;
            let b2 = bytes[1] as u64;
            let b3 = bytes[2] as u64;
            let b4 = bytes[3] as u64;
            let b5 = bytes[4] as u64;
            let b6 = bytes[5] as u64;
            let b7 = bytes[6] as u64;
            let b8 = bytes[7] as u64;
            Ok(b1 << 56 | b2 << 48 | b3 << 40 | b4 << 32 | b5 << 24 | b6 << 16 | b7 << 8 | b8)
        }
    }

    /// extract the CBOR [`Type`] from the given bytes as well as the associated
    /// metadata value.
    ///
    /// The following data will be at the `bytes[1 + len_sz.bytes_following()]`.
    /// This will be either the bytes/text/array/map content or the next cbor
    /// object depending on the content of the returned [`Type`].
    ///
    /// # Errors
    ///
    /// * if not enough bytes to extract a header (array is empty)
    ///
    pub fn read_header(&self, bytes: &[u8]) -> Result<(Type, LenSz)> {
        if bytes.is_empty() {
            return Err(Error::NotEnough(bytes.len(), 1));
        }
        let header = bytes[0];
        let cbor_type = Type::from_byte(header & 0b1110_0000);
        match header & 0b0001_1111 {
            b @ 0x00..=0x17 => Ok((cbor_type, LenSz::Len(b as u64, Sz::Inline))),
            0x18 => self
                .u8(&bytes[1..])
                .map(|v| (cbor_type, LenSz::Len(v, Sz::One))),
            0x19 => self
                .u16(&bytes[1..])
                .map(|v| (cbor_type, LenSz::Len(v, Sz::Two))),
            0x1a => self
                .u32(&bytes[1..])
                .map(|v| (cbor_type, LenSz::Len(v, Sz::Four))),
            0x1b => self
                .u64(&bytes[1..])
                .map(|v| (cbor_type, LenSz::Len(v, Sz::Eight))),
            b @ 0x1c..=0x1e => Err(Error::UnknownLenType(b)),
            0x1f => Ok((cbor_type, LenSz::Indefinite)),

            // since the value `header` has been masked to only consider the first 5 lowest bits
            // all value above 0x1f are unreachable.
            _ => unreachable!(),
        }
    }
}
