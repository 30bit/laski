//! A library that provides specialized ASCII-only string and character types.
//!
//! The types [`PackedStr12`] and [`PackedStr24`] are meant to be used as a fast and small representation for strings. Both traits are achieved by representing them as integers used in an endianness-agnostic way.
//!
//! Strings are padded to their capacity by ASCII whitespace characters. These can be removed by the trimming functions. Additionally, almost every function is `const`.
//!
//! | String type   | Inner type    | Chars | Bytes |
//! | ------------- | ------------- | ----- | ----- |
//! | [`PackedStr12`] | [`NonZeroU64`] | 12    | 8     |
//! | [`PackedStr24`] | [`NonZeroU128`] | 24    | 16    |
//!
//! Note that packing and unpacking the strings has some overhead. To take advantage of this crate, use the packed type extensively after packing once upon obtaining a string, unpacking only for debug or trace.
//!
//! [`NonZeroU64`]: core::num::NonZeroU64
//! [`NonZeroU128`]: core::num::NonZeroU128

#![no_std]

macro_rules! char_impl {
    (
        Self = $Self:ty,
        Other = $Other:ty,
        case_predicate = $case_predicate:path,
        to_other_fn = $to_other_fn:ident,
    ) => {
        impl $Self {
            #[must_use]
            pub const fn from_char(ch: char) -> Option<Self> {
                if (ch == ' ') | ch.is_ascii_digit() | $case_predicate(&ch) {
                    Some(unsafe { core::mem::transmute_copy(&(ch as u8)) })
                } else {
                    None
                }
            }

            #[must_use]
            pub const fn as_char(&self) -> char {
                *self as u8 as char
            }

            #[must_use]
            pub const fn $to_other_fn(&self) -> $Other {
                let changed_case = *self as u8 ^ 0x20;
                unsafe { core::mem::transmute_copy(&changed_case) }
            }
        }

        impl core::fmt::Debug for $Self {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Debug::fmt(&self.as_char(), f)
            }
        }

        impl core::fmt::Display for $Self {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Display::fmt(&self.as_char(), f)
            }
        }
    };
}

/// ASCII lowercase alphanumeric and space.
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Default)]
#[repr(u8)]
pub enum LowerChar {
    #[default]
    Space = 32,
    Digit0 = 48,
    Digit1 = 49,
    Digit2 = 50,
    Digit3 = 51,
    Digit4 = 52,
    Digit5 = 53,
    Digit6 = 54,
    Digit7 = 55,
    Digit8 = 56,
    Digit9 = 57,
    SmallA = 97,
    SmallB = 98,
    SmallC = 99,
    SmallD = 100,
    SmallE = 101,
    SmallF = 102,
    SmallG = 103,
    SmallH = 104,
    SmallI = 105,
    SmallJ = 106,
    SmallK = 107,
    SmallL = 108,
    SmallM = 109,
    SmallN = 110,
    SmallO = 111,
    SmallP = 112,
    SmallQ = 113,
    SmallR = 114,
    SmallS = 115,
    SmallT = 116,
    SmallU = 117,
    SmallV = 118,
    SmallW = 119,
    SmallX = 120,
    SmallY = 121,
    SmallZ = 122,
}

char_impl! {
    Self = LowerChar,
    Other = UpperChar,
    case_predicate = char::is_ascii_lowercase,
    to_other_fn = to_uppercase,
}

/// ASCII uppercase alphanumeric and space.
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Default)]
#[repr(u8)]
pub enum UpperChar {
    #[default]
    Space = 32,
    Digit0 = 48,
    Digit1 = 49,
    Digit2 = 50,
    Digit3 = 51,
    Digit4 = 52,
    Digit5 = 53,
    Digit6 = 54,
    Digit7 = 55,
    Digit8 = 56,
    Digit9 = 57,
    CapitalA = 65,
    CapitalB = 66,
    CapitalC = 67,
    CapitalD = 68,
    CapitalE = 69,
    CapitalF = 70,
    CapitalG = 71,
    CapitalH = 72,
    CapitalI = 73,
    CapitalJ = 74,
    CapitalK = 75,
    CapitalL = 76,
    CapitalM = 77,
    CapitalN = 78,
    CapitalO = 79,
    CapitalP = 80,
    CapitalQ = 81,
    CapitalR = 82,
    CapitalS = 83,
    CapitalT = 84,
    CapitalU = 85,
    CapitalV = 86,
    CapitalW = 87,
    CapitalX = 88,
    CapitalY = 89,
    CapitalZ = 90,
}

char_impl! {
    Self = UpperChar,
    Other = LowerChar,
    case_predicate = char::is_ascii_uppercase,
    to_other_fn = to_lowercase,
}

/// Returns a position where to trim **from** or the default value if it's all whitespace.
const fn trim_left_position_or<const N: usize>(arr: &[u8; N], default: usize) -> usize {
    let mut pos = default;
    let mut i = N;

    while i != 0 {
        i -= 1;
        if arr[i] != b' ' {
            pos = i;
        }
    }

    pos
}

/// Returns a position where to trim **to** or the default value if it's all whitespace.
const fn trim_right_position_or<const N: usize>(arr: &[u8; N], default: usize) -> usize {
    let mut pos = default;
    let mut i = 0;

    while i != N {
        if arr[i] != b' ' {
            pos = i + 1;
        }
        i += 1;
    }

    pos
}

/// Remove left whitespace characters.
const fn trim_left<const N: usize>(bytes: &[u8; N]) -> &[u8] {
    let pos = trim_left_position_or(bytes, N);
    bytes.split_at(pos).1
}

/// Remove right whitespace characters.
const fn trim_right<const N: usize>(bytes: &[u8; N]) -> &[u8] {
    let pos = trim_right_position_or(bytes, 0);
    bytes.split_at(pos).0
}

/// Remove left and right whitespace characters.
const fn trim<const N: usize>(bytes: &[u8; N]) -> &[u8] {
    let left_pos = trim_left_position_or(bytes, 0);
    let right_pos = trim_right_position_or(bytes, 0);
    bytes.split_at(right_pos).0.split_at(left_pos).1
}

macro_rules! char_array_impl {
    (
        Self = $Self:ty,
        Char = $Char:ty,
        LENGTH = $LENGTH:literal,
    ) => {
        impl $Self {
            /// Returns an underlying char array.
            #[must_use]
            #[inline(always)]
            pub const fn as_chars(&self) -> &[$Char; $LENGTH] {
                &self.0
            }

            /// Returns an underlying char array mapped to bytes and trimmed from left.
            #[must_use]
            pub const fn as_chars_trim_left(&self) -> &[$Char] {
                unsafe { core::mem::transmute(self.as_bytes_trim_left()) }
            }

            /// Returns an underlying char array mapped to bytes and trimmed from left.
            #[must_use]
            pub const fn as_chars_trim_right(&self) -> &[$Char] {
                unsafe { core::mem::transmute(self.as_bytes_trim_right()) }
            }

            /// Returns an underlying char array mapped to bytes and trimmed from left.
            #[must_use]
            pub const fn as_chars_trim(&self) -> &[$Char] {
                unsafe { core::mem::transmute(self.as_bytes_trim()) }
            }

            /// Returns an underlying char array mapped to bytes.
            #[must_use]
            #[inline(always)]
            pub const fn as_bytes(&self) -> &[u8; $LENGTH] {
                unsafe { core::mem::transmute(&self.0) }
            }

            /// Returns an underlying char array mapped to bytes and trimmed from left.
            #[must_use]
            pub const fn as_bytes_trim_left(&self) -> &[u8] {
                trim_left(self.as_bytes())
            }

            /// Returns an underlying char array mapped to bytes and trimmed from left.
            #[must_use]
            pub const fn as_bytes_trim_right(&self) -> &[u8] {
                trim_right(self.as_bytes())
            }

            /// Returns an underlying char array mapped to bytes and trimmed from left.
            #[must_use]
            pub const fn as_bytes_trim(&self) -> &[u8] {
                trim(self.as_bytes())
            }

            /// Returns a [`str`] view of underlying char array.
            /// Note that the returned [`str`] is not trimmed.
            #[must_use]
            #[inline(always)]
            pub const fn as_str(&self) -> &str {
                unsafe { core::str::from_utf8_unchecked(self.as_bytes()) }
            }

            /// Returns an underlying char array mapped to bytes and trimmed from left.
            #[must_use]
            pub const fn as_str_trim_left(&self) -> &str {
                unsafe { core::str::from_utf8_unchecked(self.as_bytes_trim_left()) }
            }

            /// Returns an underlying char array mapped to bytes and trimmed from left.
            #[must_use]
            pub const fn as_str_trim_right(&self) -> &str {
                unsafe { core::str::from_utf8_unchecked(self.as_bytes_trim_right()) }
            }

            /// Returns an underlying char array mapped to bytes and trimmed from left.
            #[must_use]
            pub const fn as_str_trim(&self) -> &str {
                unsafe { core::str::from_utf8_unchecked(self.as_bytes_trim()) }
            }
        }

        impl core::fmt::Debug for $Self {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Debug::fmt(self.as_str(), f)
            }
        }

        impl core::fmt::Display for $Self {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Display::fmt(self.as_str_trim(), f)
            }
        }
    };
}

/// Lowercase [`PackedStr12`] representation.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct LowerStr12(pub [LowerChar; 12]);

char_array_impl! {
    Self = LowerStr12,
    Char = LowerChar,
    LENGTH = 12,
}

/// Uppercase [`PackedStr12`] representation.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct UpperStr12(pub [UpperChar; 12]);

char_array_impl! {
    Self = UpperStr12,
    Char = UpperChar,
    LENGTH = 12,
}

/// Lowercase [`PackedStr24`] representation.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct LowerStr24(pub [LowerChar; 24]);

char_array_impl! {
    Self = LowerStr24,
    Char = LowerChar,
    LENGTH = 24,
}

/// Uppercase [`PackedStr24`] representation.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct UpperStr24(pub [UpperChar; 24]);

char_array_impl! {
    Self = UpperStr24,
    Char = UpperChar,
    LENGTH = 24,
}

/// An error returned when parsing a string fails.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum ParseError {
    /// Provided string was too long. Length should be within the packing capacity.
    TooLong,
    /// Invalid character found in string. Characters should be ASCII alphanumeric or whitespace.
    InvalidChar,
}

impl core::fmt::Display for ParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ParseError::TooLong => f.write_str("provided string was too long"),
            ParseError::InvalidChar => f.write_str("invalid character found in string"),
        }
    }
}

impl core::error::Error for ParseError {}

/// Checks that the byte represents an alphanumeric ASCII character or ASCII whitespace.
const fn is_alphanumeric_or_space(ch: u8) -> bool {
    (ch == b' ') | ch.is_ascii_alphanumeric()
}

/// Saturates an ASCII character into `0..37` value range.
/// - Replaces non-alphanumeric characters with `0`.
/// - Maps alphabetic characters into `1..27` values.
/// - Maps digit characters into `27..37` values.
const fn to_base37(mut ch: u8) -> u8 {
    let mut res = 0;
    if ch.is_ascii_lowercase() {
        ch ^= 0x20;
    }
    if ch.is_ascii_uppercase() {
        res = ch ^ 0x40;
    }
    if ch.is_ascii_digit() {
        res = ch - 21;
    }
    res
}

/// Inversed [`to_base37`].
const fn from_base37(ch: u8, case: u8) -> u8 {
    if matches!(ch, 1..=26) {
        ch | 0x40 | case
    } else if matches!(ch, 27..37) {
        ch + 21
    } else {
        0x20
    }
}

/// Generic algorithm implementation, where `N` is `3M`.
struct Impl<const N: usize, const M: usize>;

impl<const N: usize, const M: usize> Impl<N, M> {
    /// Copies at most `N` bytes onto an array and applies [`to_base37`] to them.
    const fn resize_to_base37(s: &[u8]) -> [u8; N] {
        let bounded_len = if s.len() < N { s.len() } else { N };
        let (bounded, _) = s.split_at(bounded_len);
        let mut res = [0; N];
        let mut i = 0;
        while i != bounded_len {
            res[i] = bounded[i];
            i += 1;
        }
        i = 0;
        while i != N {
            res[i] = to_base37(res[i]);
            i += 1;
        }
        res
    }

    /// Checks [`ParseError`] constraints.
    const fn check(s: &[u8]) -> Result<(), ParseError> {
        if s.len() > N {
            return Err(ParseError::TooLong);
        }
        let mut i = 0;
        while i != s.len() {
            if !is_alphanumeric_or_space(s[i]) {
                return Err(ParseError::InvalidChar);
            }
            i += 1;
        }
        Ok(())
    }

    /// Packs every 3 base37 chars into a single [`u16`].
    const fn base37_pack(s: &[u8; N]) -> [u16; M] {
        let mut res = [0; M];
        let mut i = 0;
        while i != M {
            res[i] = s[i * 3] as u16 + s[i * 3 + 1] as u16 * 37 + s[i * 3 + 2] as u16 * 37 * 37;
            #[cfg(target_endian = "big")]
            {
                // Ensuring consistent byte repr (little endian) as opposed to consistent int value.
                res[i] = res[i].swap_bytes();
            }
            i += 1;
        }
        res
    }

    const fn pack_lossy(s: &[u8]) -> [u16; M] {
        Self::base37_pack(&Self::resize_to_base37(s))
    }

    const fn pack(s: &[u8]) -> Result<[u16; M], ParseError> {
        match Self::check(s) {
            Ok(()) => Ok(Self::pack_lossy(s)),
            Err(err) => Err(err),
        }
    }

    /// Inverses [`Self::base37_pack`] and restores ASCII bytes with [`from_base37`].
    const fn unpack(mut s: [u16; M], case: u8) -> [u8; N] {
        let mut res = [0; N];
        let mut i = 0;
        while i != M {
            #[cfg(target_endian = "big")]
            {
                // Restoring an integer value from little endian bytes.
                s[i] = s[i].swap_bytes();
            }
            let mut j = 0;
            while j != 3 {
                let ch = s[i] % 37;
                s[i] /= 37;
                res[i * 3 + j] = from_base37(ch as u8, case);
                j += 1;
            }
            i += 1;
        }
        res
    }

    const fn unpack_lowercase(s: [u16; M]) -> [LowerChar; N] {
        let bytes = Self::unpack(s, 0x20);
        unsafe { core::mem::transmute_copy(&bytes) }
    }

    const fn unpack_uppercase(s: [u16; M]) -> [UpperChar; N] {
        let bytes = Self::unpack(s, 0);
        unsafe { core::mem::transmute_copy(&bytes) }
    }
}

macro_rules! convert_nonmax_impl {
    (
        N = $N:literal,
        M = $M:literal,
        Uint = $Uint:ty,
    ) => {
        impl Impl<$N, $M> {
            /// Converts packed array to nonzero uint.
            const unsafe fn array_to_nonmax(s: &[u16; $M]) -> core::num::NonZero<$Uint> {
                // Integers treated as bytes.
                let uint: $Uint = unsafe { core::mem::transmute_copy(s) };
                unsafe { core::num::NonZero::new_unchecked(uint ^ <$Uint>::MAX) }
            }

            /// Converts nonzero uint to packed array.
            const fn array_from_nonmax(u: core::num::NonZero<$Uint>) -> [u16; $M] {
                // Bitwise operation is not affected by endianness.
                unsafe { core::mem::transmute_copy(&(u.get() ^ <$Uint>::MAX)) }
            }

            const fn pack_lossy_to_nonmax(s: &[u8]) -> core::num::NonZero<$Uint> {
                unsafe { Self::array_to_nonmax(&Self::pack_lossy(s)) }
            }

            const fn pack_to_nonmax(s: &[u8]) -> Result<core::num::NonZero<$Uint>, ParseError> {
                match Self::pack(s) {
                    Ok(packed) => Ok(unsafe { Self::array_to_nonmax(&packed) }),
                    Err(err) => Err(err),
                }
            }

            const fn unpack_lowercase_from_nonmax(s: core::num::NonZero<$Uint>) -> [LowerChar; $N] {
                Self::unpack_lowercase(Self::array_from_nonmax(s))
            }

            const fn unpack_uppercase_from_nonmax(s: core::num::NonZero<$Uint>) -> [UpperChar; $N] {
                Self::unpack_uppercase(Self::array_from_nonmax(s))
            }

            /// Get an integer value independent from endianness.
            const fn to_le_nonmax(s: core::num::NonZero<$Uint>) -> core::num::NonZero<$Uint> {
                let uint = <$Uint>::from_le_bytes(s.get().to_ne_bytes());
                unsafe { core::num::NonZero::<$Uint>::new_unchecked(uint) }
            }
        }
    };
}

type Impl12 = Impl<12, 4>;

convert_nonmax_impl! {
    N = 12,
    M = 4,
    Uint = u64,
}

type Impl24 = Impl<24, 8>;

convert_nonmax_impl! {
    N = 24,
    M = 8,
    Uint = u128,
}

macro_rules! impl_packed {
    (
        Self = $Self:ty,
        Impl = $Impl:ty,
        Uint = $Uint:ty,
        UpperStr = $UpperStr:path,
        LowerStr = $LowerStr:path,
    ) => {
        impl $Self {
            /// All chars set to the ascii whitespaces.
            pub const SPACE: Self = Self(core::num::NonZero::<$Uint>::MAX);

            /// Converts up to 24 ASCII bytes into `Self`.
            ///
            /// # Errors
            ///
            /// - Slice length isn't within the packing capacity.
            /// - Bytes are not ASCII alphanumeric or whitespace.
            pub const fn from_ascii(s: &[u8]) -> Result<Self, ParseError> {
                match <$Impl>::pack_to_nonmax(s) {
                    Ok(ok) => Ok(Self(ok)),
                    Err(err) => Err(err),
                }
            }

            /// Converts up to 24 bytes into `Self` with the remaining bytes ignored.
            ///
            /// Each byte is treated as an ASCII character.
            /// Non-ascii and non-alphanumeric bytes are turned into whitespace characters.
            ///
            /// This is a lossy conversion, so a roundtrip isn't guaranteed to produce the same result.
            #[must_use]
            pub const fn from_ascii_lossy(s: &[u8]) -> Self {
                Self(<$Impl>::pack_lossy_to_nonmax(s))
            }

            /// Returns ASCII lowercase representation.
            #[must_use]
            pub const fn to_lowercase(self) -> $LowerStr {
                $LowerStr(<$Impl>::unpack_lowercase_from_nonmax(self.0))
            }

            /// Returns ASCII uppercase representation.
            #[must_use]
            pub const fn to_uppercase(self) -> $UpperStr {
                $UpperStr(<$Impl>::unpack_uppercase_from_nonmax(self.0))
            }
        }

        impl Default for $Self {
            #[inline(always)]
            fn default() -> Self {
                Self::SPACE
            }
        }

        impl core::str::FromStr for $Self {
            type Err = ParseError;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                Self::from_ascii(s.as_bytes())
            }
        }

        impl PartialOrd for $Self {
            #[inline(always)]
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Ord for $Self {
            #[inline(always)]
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                <$Impl>::to_le_nonmax(self.0).cmp(&<$Impl>::to_le_nonmax(other.0))
            }
        }

        impl core::hash::Hash for $Self {
            #[inline(always)]
            fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
                core::hash::Hash::hash(&<$Impl>::to_le_nonmax(self.0), h)
            }
        }

        impl core::fmt::Debug for $Self {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                if f.alternate() {
                    core::fmt::Debug::fmt(&self.to_uppercase(), f)
                } else {
                    core::fmt::Debug::fmt(&self.to_lowercase(), f)
                }
            }
        }

        impl core::fmt::Display for $Self {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                if f.alternate() {
                    core::fmt::Display::fmt(&self.to_uppercase(), f)
                } else {
                    core::fmt::Display::fmt(&self.to_lowercase(), f)
                }
            }
        }
    };
}

/// 12 ASCII alphanumeric and whitespace characters packed into 8 non-zero bytes.
#[derive(Copy, Clone, Eq, PartialEq)]
#[repr(transparent)]
pub struct PackedStr12(core::num::NonZeroU64);

impl_packed! {
    Self = PackedStr12,
    Impl = Impl12,
    Uint = u64,
    UpperStr = UpperStr12,
    LowerStr = LowerStr12,
}

/// 24 ASCII alphanumeric and whitespace characters packed into 16 non-zero bytes.
#[derive(Copy, Clone, Eq, PartialEq)]
#[repr(transparent)]
pub struct PackedStr24(core::num::NonZeroU128);

impl_packed! {
    Self = PackedStr24,
    Impl = Impl24,
    Uint = u128,
    UpperStr = UpperStr24,
    LowerStr = LowerStr24,
}

#[cfg(test)]
mod tests {
    extern crate alloc;

    use alloc::{string::String, vec::Vec};
    use quickcheck::{TestResult, quickcheck};

    const fn is_base37(byte: u8) -> bool {
        byte < 37
    }

    const fn is_alphanumeric_or_space(ch: u8, is_lowercase: bool) -> bool {
        (ch == b' ')
            | ch.is_ascii_digit()
            | (is_lowercase && ch.is_ascii_lowercase())
            | (!is_lowercase && ch.is_ascii_uppercase())
    }

    fn is_alphanumeric_or_space_str_case_insensitive(s: &str) -> bool {
        s.bytes().all(super::is_alphanumeric_or_space)
    }

    const fn case_bit(is_lowercase: bool) -> u8 {
        if is_lowercase { 0x20 } else { 0 }
    }

    quickcheck! {
        fn lower_char_from_alphanumeric_or_space(ch: u8) -> TestResult {
            if !is_alphanumeric_or_space(ch, true) {
                return TestResult::discard();
            }
            let lch = super::LowerChar::from_char(ch as char);
            TestResult::from_bool(lch.is_some())
        }
    }

    quickcheck! {
        fn upper_char_from_alphanumeric_or_space(ch: u8) -> TestResult {
            if !is_alphanumeric_or_space(ch, false) {
                return TestResult::discard();
            }
            let uch = super::UpperChar::from_char(ch as char);
            TestResult::from_bool(uch.is_some())
        }
    }

    quickcheck! {
        fn to_base37_is_base37(ch: u8) -> bool {
            is_base37(super::to_base37(ch))
        }
    }

    quickcheck! {
        fn from_not_alphanumeric_to_base37_is_zero(ch: u8) -> TestResult {
             if ch.is_ascii_alphanumeric() {
                return TestResult::discard();
            }
            TestResult::from_bool(super::to_base37(ch as u8) == 0)
        }
    }

    quickcheck! {
        fn from_base37_is_alphanumeric_or_space(byte: u8, is_lowercase: bool) -> TestResult {
            let ch = super::from_base37(byte, case_bit(is_lowercase));
            TestResult::from_bool(is_alphanumeric_or_space(ch, is_lowercase))
        }
    }

    quickcheck! {
        fn from_zero_is_space(is_lowercase: bool) -> TestResult {
            let ch = super::from_base37(0, case_bit(is_lowercase));
            TestResult::from_bool(ch == b' ')
        }
    }

    quickcheck! {
        fn from_not_base37_is_whitespace(byte: u8, is_lowercase: bool) -> TestResult {
            if is_base37(byte) {
                return TestResult::discard();
            }
            let ch = super::from_base37(byte, case_bit(is_lowercase));
            TestResult::from_bool(ch == b' ')
        }
    }

    quickcheck! {
        fn impl12_resize_to_base37_is_all_base37(bytes: Vec<u8>) -> bool {
            let res = super::Impl12::resize_to_base37(bytes.as_slice());
            res.iter().copied().all(is_base37)
        }
    }

    quickcheck! {
        fn impl24_resize_to_base37_is_all_base37(bytes: Vec<u8>) -> bool {
            let res = super::Impl24::resize_to_base37(bytes.as_slice());
            res.iter().copied().all(is_base37)
        }
    }

    quickcheck! {
        fn impl12_pack_lossy_is_all_nonmax_u16(bytes: Vec<u8>) -> bool {
            let res = super::Impl12::pack_lossy(bytes.as_slice());
            res.iter().all(|&ch| ch < u16::MAX)
        }
    }

    quickcheck! {
        fn impl24_pack_lossy_is_all_nonmax_u16(bytes: Vec<u8>) -> bool {
            let res = super::Impl24::pack_lossy(bytes.as_slice());
            res.iter().all(|&ch| ch < u16::MAX)
        }
    }

    quickcheck! {
        fn impl12_unpack_is_all_alphanumeric_or_space(bytes: Vec<u16>, is_lowercase: bool) -> TestResult {
            let Some(bytes) = <[u16; 4]>::try_from(bytes).ok() else {
                return TestResult::discard();
            };
            let res = super::Impl12::unpack(bytes, case_bit(is_lowercase));
            let ok = res.iter().all(|&ch| is_alphanumeric_or_space(ch, is_lowercase));
            TestResult::from_bool(ok)
        }
    }

    quickcheck! {
        fn impl24_unpack_is_all_alphanumeric_or_space(bytes: Vec<u16>, is_lowercase: bool) -> TestResult {
            let Some(bytes) = <[u16; 8]>::try_from(bytes).ok() else {
                return TestResult::discard();
            };
            let res = super::Impl24::unpack(bytes, case_bit(is_lowercase));
            let ok = res.iter().all(|&ch| is_alphanumeric_or_space(ch, is_lowercase));
            TestResult::from_bool(ok)
        }
    }

    quickcheck! {
        fn impl12_roundtrip_is_all_base_37(string: String) -> TestResult {
            if !is_alphanumeric_or_space_str_case_insensitive(&string) {
                return TestResult::discard();
            }
            let mut original = string;
            let packed = super::Impl12::pack_lossy(original.as_bytes());
            let unpack = super::Impl12::unpack(packed, case_bit(false));

            original.make_ascii_uppercase();
            let ok = original.as_bytes().starts_with(&unpack) | unpack.starts_with(original.as_bytes());
            TestResult::from_bool(ok)
        }
    }

    quickcheck! {
        fn impl24_roundtrip_is_all_base_37(string: String, to_lowercase: bool) -> TestResult {
            if !is_alphanumeric_or_space_str_case_insensitive(&string) {
                return TestResult::discard();
            }
            let mut original = string;
            let packed = super::Impl24::pack_lossy(original.as_bytes());
            let unpack = super::Impl24::unpack(packed, case_bit(to_lowercase));

            if to_lowercase {
                original.make_ascii_lowercase();
            } else {
                original.make_ascii_uppercase();
            }

            let ok = original.as_bytes().starts_with(&unpack) | unpack.starts_with(original.as_bytes());
            TestResult::from_bool(ok)
        }
    }

    quickcheck! {
        fn impl12_roundtrip_space_is_space(string: String, to_lowercase: bool) -> TestResult {
           if string.chars().any(|ch| ch != ' ') {
                return TestResult::discard();
            }
            let packed = super::Impl12::pack_lossy(string.as_bytes());
            let unpack = super::Impl12::unpack(packed, case_bit(to_lowercase));

            let ok = unpack.iter().all(|&ch| ch == b' ');
            TestResult::from_bool(ok)
        }
    }

    quickcheck! {
        fn impl24_roundtrip_space_is_space(string: String, to_lowercase: bool) -> TestResult {
            if string.chars().any(|ch| ch != ' ') {
                return TestResult::discard();
            }
            let packed = super::Impl24::pack_lossy(string.as_bytes());
            let unpack = super::Impl24::unpack(packed, case_bit(to_lowercase));

            let ok = unpack.iter().all(|&ch| ch == b' ');
            TestResult::from_bool(ok)
        }
    }

    quickcheck! {
        fn impl12_roundtrip_not_alphanumeric_is_space(string: String, to_lowercase: bool) -> TestResult {
           if string.chars().any(char::is_alphanumeric) {
                return TestResult::discard();
            }
            let packed = super::Impl12::pack_lossy(string.as_bytes());
            let unpack = super::Impl12::unpack(packed, case_bit(to_lowercase));

            let ok = unpack.iter().all(|&ch| ch == b' ');
            TestResult::from_bool(ok)
        }
    }

    quickcheck! {
        fn impl24_roundtrip_not_alphanumeric_is_space(string: String, to_lowercase: bool) -> TestResult {
            if string.chars().any(char::is_alphanumeric) {
                return TestResult::discard();
            }
            let packed = super::Impl24::pack_lossy(string.as_bytes());
            let unpack = super::Impl24::unpack(packed, case_bit(to_lowercase));

            let ok = unpack.iter().all(|&ch| ch == b' ');
            TestResult::from_bool(ok)
        }
    }
}
