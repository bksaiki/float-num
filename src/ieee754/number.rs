/*
    Definition of `Float<E, N>` struct
*/

use super::*;

macro_rules! bitvec {
    [ $($t:tt)* ] => {
        {
            bitvec::bitvec![u32, Lsb0; $($t)*]
        }
    };
}

macro_rules! assert_valid_format {
    ($E:expr, $N:expr) => {
        assert!(
            (2 <= $E) && ($E <= 60),
            "invalid exponent width, must be 2 <= E <= 60: {}",
            $E
        );
        assert!(
            (2 <= ($N - $E)),
            "invalid total width, must be 2 + E <= N: {}",
            $N
        );
    };
}

// Format parameters
impl<const E: usize, const N: usize> Float<E, N> {
    /// Bitwidth of the representation.
    pub const N: usize = N;

    /// Bitwidth of the exponent field.
    pub const E: usize = E;

    /// Radix, in this case, 2.
    pub const B: usize = 2;

    /// Number of (binary) digits when the significand is expressed
    /// as an integer. This is just `Self::M + 1`.
    pub const PREC: usize = N - E;

    /// Bitwidth of the mantissa field.
    pub const M: usize = Self::PREC - 1;

    /// Exponent of the largest finite floating-point value in
    /// this representation when it is in the form `(-1)^s b^e m`
    /// where `m` is a fraction between 1 and 2.
    pub const EMAX: i64 = i64::pow(2, (E - 1) as u32) - 1;

    /// Exponent of the smallest normal floating-point value in
    /// this representation when it is in the form `(-1)^s b^e m`
    /// where `m` is a fraction between 1 and 2.
    /// This is just `1 - Self::EMAX`.
    pub const EMIN: i64 = 1 - Self::EMAX;

    /// Exponent of the largest finite floating-point value in
    /// this representation when it is in the form `(-1)^s b^e c`
    /// where `c` is an integer.
    /// This is just `Self::EMAX - Self::M`.
    pub const EXPMAX: i64 = Self::EMAX - Self::M as i64;

    /// Exponent of the smallest normal floating-point value in
    /// this representation when it is in the form `(-1)^s b^e c`
    /// where `c` is an integer.
    /// This is just `Self::EMIN - Self::M`.
    pub const EXPMIN: i64 = Self::EMIN - Self::M as i64;

    /// Bitwidth of the NaN payload.
    /// This is just `Self::M - 1`.
    pub const NAN_PAYLOAD_SIZE: usize = Self::M - 1;

    /// The exponent field bias.
    /// This is just `Self::EMAX`.
    pub const BIAS: i64 = Self::EMAX;
}

// Constructors and getters
impl<const E: usize, const N: usize> Float<E, N> {
    /// Creates a new `Float` with `E` exponent bits and `N` total bits.
    /// Initializes the `Float` to +0.
    pub fn new() -> Self {
        assert_valid_format!(E, N);
        Self {
            num: FloatNum::Number(false, 0, bitvec![0; Self::PREC]),
            flags: Exceptions::default(),
        }
    }

    /// Returns an infinity with a particular sign
    /// using the same width parameters as this `Float`.
    pub fn infinity(sign: bool) -> Self {
        Self {
            num: FloatNum::Infinity(sign),
            flags: Exceptions::default(),
        }
    }

    /// Returns a zero with a particular sign
    /// using the same width parameters as this `Float`.
    pub fn zero(sign: bool) -> Self {
        Self {
            num: FloatNum::Number(sign, 0, bitvec![0; Self::PREC]),
            flags: Exceptions::default(),
        }
    }

    /// Returns an NaN value based on the specified sign, signaling status
    /// and payload using the same width parameters as this `Float`.
    pub fn nan(sign: bool, signaling: bool, payload: impl Into<BitVec>) -> Self {
        let bv = payload.into();
        assert_eq!(
            bv.len(),
            Self::NAN_PAYLOAD_SIZE,
            "expected a payload size of {}, received {}",
            Self::NAN_PAYLOAD_SIZE,
            bv.len()
        );
        Self {
            num: FloatNum::Nan(sign, signaling, bv),
            flags: Exceptions::default(),
        }
    }

    /// Returns the sign of this `Float`.
    pub fn sign(&self) -> bool {
        match self.num {
            FloatNum::Number(s, _, _) => s,
            FloatNum::Infinity(s) => s,
            FloatNum::Nan(s, _, _) => s,
        }
    }

    /// Returns the exponent of this `Float`.
    /// The result is wrapped in an option since only finite
    /// numbers have a valid exponent.
    pub fn exponent(&self) -> Option<i64> {
        match self.num {
            FloatNum::Number(_, exp, _) => Some(exp),
            _ => None,
        }
    }

    /// Returns the (integer) mantissa of this `Float` as a `Bitvec`.
    /// The result is wrapped in an option since only finite numbers
    /// have a valid exponent.
    pub fn significand(&self) -> Option<BitVec> {
        match &self.num {
            FloatNum::Number(_, _, c) => Some(c.clone()),
            _ => None,
        }
    }

    /// Returns true if this `Float` encodes a zero.
    pub fn is_zero(&self) -> bool {
        match &self.num {
            FloatNum::Number(_, e, c) => *e == 0 && c.not_any(),
            _ => false,
        }
    }

    /// Returns true if this `Float` encodes a subnormal number
    pub fn is_subnormal(&self) -> bool {
        match &self.num {
            FloatNum::Number(_, e, _) => *e < Self::EXPMIN,
            _ => false,
        }
    }

    /// Returns true if this `Float` encodes a normal number
    pub fn is_normal(&self) -> bool {
        match &self.num {
            FloatNum::Number(_, e, c) => *e >= Self::EXPMIN && (*e != 0 || c.some()),
            _ => false,
        }
    }

    /// Returns true if this `Float` encodes an infinity.
    pub fn is_infinity(&self) -> bool {
        matches!(self.num, FloatNum::Infinity(_))
    }

    /// Returns true if this `Float` encodes a NaN.
    pub fn is_nan(&self) -> bool {
        matches!(self.num, FloatNum::Nan(_, _, _))
    }

    /// Returns true if this `Float` encodes a signaling NaN.
    /// The result is wrapped in an option since only NaNs can be signaling.
    pub fn is_signaling_nan(&self) -> Option<bool> {
        match self.num {
            FloatNum::Nan(_, signal, _) => Some(signal),
            _ => None,
        }
    }

    /// Returns the NaN payload of this `Float` as a `Bitvec`.
    /// The result is wrapped in an option since only a NaN has a payload.
    pub fn nan_payload(&self) -> Option<BitVec> {
        match &self.num {
            FloatNum::Nan(_, _, payload) => Some(payload.clone()),
            _ => None,
        }
    }

    /// Returns the state of all flags raised during
    /// the operation that created this `Float`.
    pub fn flags(&self) -> Exceptions {
        self.flags
    }

    /// Returns true if the `invalid` flag was raised
    /// during the operation that created this `Float`.
    pub fn invalid_flag(&self) -> bool {
        self.flags.invalid
    }

    /// Returns true if the `div_by_zero` flag was raised
    /// during the operation that created this `Float`.
    pub fn div_by_zero_flag(&self) -> bool {
        self.flags.div_by_zero
    }

    /// Returns true if the `overflow` flag was raised
    /// during the operation that created this `Float`.
    pub fn overflow_flag(&self) -> bool {
        self.flags.overflow
    }

    /// Returns true if the `underflow` flag was raised
    /// during the operation that created this `Float`.
    pub fn underflow_flag(&self) -> bool {
        self.flags.underflow
    }

    /// Returns true if the `inexact` flag was raised
    /// during the operation that created this `Float`.
    pub fn inexact_flag(&self) -> bool {
        self.flags.inexact
    }

    /// Returns true if the `carry` flag was raised
    /// during the operation that created this `Float`.
    pub fn carry_flag(&self) -> bool {
        self.flags.carry
    }
}

// Implementing `Default` for `Float`
impl<const E: usize, const N: usize> Default for Float<E, N> {
    fn default() -> Self {
        Self::new()
    }
}
