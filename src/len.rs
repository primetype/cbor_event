/// CBOR len: either a fixed size or an indefinite length.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum Len {
    Indefinite,
    Len(u64),
}
impl Len {
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Len(0))
    }
    pub fn non_null(self) -> Option<Self> {
        if self.is_null() {
            None
        } else {
            Some(self)
        }
    }

    pub fn indefinite(&self) -> bool {
        self == &Len::Indefinite
    }
}

/// How many bytes are used in CBOR encoding for a major type/length
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum Sz {
    /// Length/data is encoded inside of the type information
    Inline,
    /// Lnegth/data is in 1 byte following the type information
    One,
    /// Lnegth/data is in 2 bytes following the type information
    Two,
    /// Lnegth/data is in 4 bytes following the type information
    Four,
    /// Lnegth/data is in 8 bytes following the type information
    Eight,
}

impl Sz {
    pub fn canonical(len: u64) -> Self {
        if len <= super::MAX_INLINE_ENCODING {
            Sz::Inline
        } else if len < 0x1_00 {
            Sz::One
        } else if len < 0x1_00_00 {
            Sz::Two
        } else if len < 0x1_00_00_00_00 {
            Sz::Four
        } else {
            Sz::Eight
        }
    }

    pub fn bytes_following(&self) -> usize {
        match self {
            Self::Inline => 0,
            Self::One => 1,
            Self::Two => 2,
            Self::Four => 4,
            Self::Eight => 8,
        }
    }
}

/// CBOR length with encoding details
///
/// Definite lengths can be encoded using a variable amount of bytes
/// see `Sz` for more information
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum LenSz {
    Indefinite,
    Len(u64, Sz),
}

impl LenSz {
    pub fn bytes_following(&self) -> usize {
        match self {
            Self::Indefinite => 0,
            Self::Len(_, sz) => sz.bytes_following(),
        }
    }
}

/// Encoding for the length of a string (text or bytes)
///
/// Indefinite encoding strings contain the indefinite marker followed
/// by a series of definite encoded strings and then a break
///
/// Definite encoding strings can vary by how many bytes are used to encode
/// the length e.g. 4 can be represented inline in the type, or in 1/2/4/8
/// additional bytes
#[derive(Debug, PartialEq, Eq)]
pub enum StringLenSz<'a> {
    Indefinite(&'a [(u64, Sz)]),
    Len(Sz),
}
