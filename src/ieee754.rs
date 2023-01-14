use std::ops::ShlAssign;

use bitvec::*;
use bitvec::prelude::Lsb0;
use num_bigint::*;
use num_traits::cast::ToPrimitive;

type BitVec = bitvec::prelude::BitVec<u32, Lsb0>;

// Converts a `BitVec` to `BitUint`
// TODO: this is really dumb
fn bitvec_to_biguint(mut bv: BitVec) -> BigUint {
    let mut i = BigUint::default();
    bv.reverse();
    for b in bv {
        i.shl_assign(1);
        i.set_bit(0, b);
    }
    i
}

// Minimal floating-point encoding grouped by classification
enum FloatNum {
    // signed zero or finite number
    // => (sign, exponent, mantissa)
    Number(bool, i64, BitVec),
    // infinity (+/-)
    // => (sign)
    Infinity(bool),
    // not-a-number
    // => (sign, signaling, payload)
    Nan(bool, bool, BitVec),
}

/** Exception flags as specified by the IEEE-754 standard.
 *
 * Besides returning a (possibly) numerical result, any computation with
 * floating-point numbers may also raise exceptions depending on certain conditions.
 * These exceptions include:
 *
 *  - invalid: no useful definable result;
 *  - division by zero: an infinite result for finite arguments;
 *  - overflow: result exceeded in magnitude what would have been the rounded result
 *      had the exponent range been unbounded;
 *  - underflow: non-zero result that either (a) would lie strictly between
 *      `-b^emin` and `+b^emin` had the exponent range been unbounded,
 *      or (b) would lie strictly between `-b^emin` and `+b^emin`
 *      had the exponent range and precision been unbounded;
 *  - inexact: result would be different had both the exponent range and precision been unbounded.
 *
 */
#[derive(Copy, Clone, Default)]
pub struct Exceptions {
    invalid: bool,
    div_by_zero: bool,
    overflow: bool,
    underflow: bool,
    inexact: bool,
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

/** A floating-point number as specified by the IEEE-754 standard.
 *
 * The generics `E` and `N` specify the number of bits in the
 * exponent field and in the entire float overall.
 *
 */
pub struct Float<const E: usize, const N: usize> {
    num: FloatNum,     // number encoding
    flags: Exceptions, // exceptions
}

// Format parameters
impl<const E: usize, const N: usize> Float<E, N> {
    /// Returns the width of the exponent field for this `Float`.
    #[inline(always)]
    pub const fn exponent_size() -> usize {
        E
    }

    /// Returns the bitwidth for this `Float`.
    #[inline(always)]
    pub const fn total_size() -> usize {
        N
    }

    /// Returns the radix of this `Float`, in this case, 2.
    #[inline(always)]
    pub const fn radix() -> usize {
        2
    }

    /// Returns the number of (binary digits) in the signficand for this `Float`.
    /// This is just `Self::mantissa_size() + 1`.
    #[inline(always)]
    pub const fn prec() -> usize {
        N - E
    }

    /// Returns maximum exponent value of this `Float` when in normalized form.
    #[inline(always)]
    pub const fn emax() -> i64 {
        i64::pow(2, (E - 1) as u32) - 1
    }

    /// Returns minimum exponent value of this `Float` when in normalized form.
    /// This will always be `1 - Self::emax()`.
    #[inline(always)]
    pub const fn emin() -> i64 {
        1 - Self::emax()
    }

    /// Returns the size of the mantissa for this `Float`.
    #[inline(always)]
    pub const fn mantissa_size() -> usize {
        N - E - 1
    }

    /// Returns the size of the NaN payload for this `Float`.
    #[inline(always)]
    pub const fn nan_payload_size() -> usize {
        N - E - 2
    }

    /// Returns the exponent bias.
    #[inline(always)]
    pub const fn bias() -> i64 {
        Self::emax()
    }
}

// Constructors and getters
impl<const E: usize, const N: usize> Float<E, N> {
    /// Creates a new `Float` with `E` exponent bits and `N` total bits.
    /// Initializes the `Float` to +0.
    pub fn new() -> Self {
        assert_valid_format!(E, N);
        Self {
            num: FloatNum::Number(false, 0, bitvec![u32, Lsb0; 0; Self::prec()]),
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
            num: FloatNum::Number(sign, 0, bitvec![u32, Lsb0; 0; Self::prec()]),
            flags: Exceptions::default(),
        }
    }

    /// Returns an NaN value based on the specified sign, signaling status
    /// and payload using the same width parameters as this `Float`.
    pub fn nan(sign: bool, signaling: bool, payload: BitVec) -> Self {
        assert_eq!(
            payload.len(),
            Self::nan_payload_size(),
            "expected a payload size of {}, received {}",
            Self::nan_payload_size(),
            payload.len()
        );
        Self {
            num: FloatNum::Nan(sign, signaling, payload),
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

    /// Returns true if this `Float` encodes an infinity.
    pub fn is_infinity(&self) -> bool {
        matches!(self.num, FloatNum::Infinity(_))
    }

    /// Returns true if this `Float` encodes a NaN.
    pub fn is_nan(&self) -> bool {
        matches!(self.num, FloatNum::Nan(_, _, _))
    }

    /// Returns true if this `Float` encodes a signaling NaN.
    /// The result is wrapped in an option since only NaNs
    /// can be signaling.
    pub fn is_signaling(&self) -> Option<bool> {
        match self.num {
            FloatNum::Nan(_, signal, _) => Some(signal),
            _ => None,
        }
    }

    /// Returns the NaN payload of this `Float` as a `Bitvec`.
    /// The result is wrapped in an option since only a NaN
    /// has a payload.
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
        return self.flags.invalid;
    }

    /// Returns true if the `div_by_zero` flag was raised
    /// during the operation that created this `Float`.
    pub fn div_by_zero_flag(&self) -> bool {
        return self.flags.div_by_zero;
    }

    /// Returns true if the `overflow` flag was raised
    /// during the operation that created this `Float`.
    pub fn overflow_flag(&self) -> bool {
        return self.flags.overflow;
    }

    /// Returns true if the `underflow` flag was raised
    /// during the operation that created this `Float`.
    pub fn underflow_flag(&self) -> bool {
        return self.flags.underflow;
    }

    /// Returns true if the `inexact` flag was raised
    /// during the operation that created this `Float`.
    pub fn inexact_flag(&self) -> bool {
        return self.flags.inexact;
    }
}

// Implementing `Default`
impl<const E: usize, const N: usize> Default for Float<E, N> {
    fn default() -> Self {
        Self::new()
    }
}

// Packed float utilities
impl<const E: usize, const N: usize> Float<E, N> {
    // Splices a packed floating-point representation into
    // the sign, exponent, and mantissa field.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn split_packed(bv: &BitVec) -> (bool, BitVec, BitVec) {
        (Self::packed_sign(bv), Self::packed_exponent(bv), Self::packed_mantissa(bv))
    }

    // Returns the sign field from a packed floating-point representation.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn packed_sign(bv: &BitVec) -> bool {
        bv[N-1]
    }

    // Returns the exponent field from a packed floating-point representation.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn packed_exponent(bv: &BitVec) -> BitVec {
        BitVec::from(&bv[(N - E - 1) .. (N - 1)])
    }

    // Returns the mantissa field from a packed floating-point representation.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn packed_mantissa(bv: &BitVec) -> BitVec {
        BitVec::from(&bv[.. (N - E - 1)])
    }
}

// Implementing `From<Bitvec>` for `Float`
impl<const E: usize, const N: usize> From<BitVec> for Float<E, N> {
    fn from(bv: BitVec) -> Self {
        assert_valid_format!(E, N);
        assert_eq!(
            bv.len(),
            N,
            "expected a BitVec of length {}, received {}",
            N,
            bv.len()
        );

        let (s, e, mut m) = Self::split_packed(&bv);
        let mut exponent = bitvec_to_biguint(e).to_i64().unwrap() - Self::bias();
        // let mut mantissa = bitvec_to_biguint(m);

        if exponent > Self::emax() {
            if m.not_any() {
                // infinity
                Self::infinity(s)
            } else {
                // NaN
                Self::nan(s, m[N - E - 2], BitVec::from(&m[.. N - E - 2]))
            }
        } else if exponent < Self::emin() {
            // subnormal or zero
            if m.not_any() {
                // zero
                Self::zero(s)
            } else {
                // subnormal
                Self::default()
            }
        } else {
            // normal
            m.push(true);
            Self {
                num: FloatNum::Number(s, exponent, m),
                flags: Exceptions::default(),
            }
        }
    }
}

// Implementing `From<f64>` for `Float<11, 64>
impl From<f64> for Float<11, 64> {
    fn from(f: f64) -> Self {
        let (_, mut v) = BigInt::from(f.to_bits()).to_u32_digits();
        while v.len() < 2 {
            v.push(0);
        }

        Self::from(BitVec::from_vec(v))
    }
}

/// Alias for `Float<15, 128>` (quad-precision number)
pub type Quad = Float<15, 128>;
/// Alias for `Float<11, 64>` (double-precision number)
pub type Double = Float<11, 64>;
/// Alias for `Float<8, 32>` (single-precision number)
pub type Single = Float<8, 32>;
/// Alias for `Float<5, 16>` (half-precision number)
pub type Half = Float<5, 16>;
