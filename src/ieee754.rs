use std::ops::ShlAssign;

use bitvec::{field::BitField, prelude::Lsb0};
use num_bigint::*;
use num_traits::cast::ToPrimitive;

type BitVec = bitvec::prelude::BitVec<u32, Lsb0>;

macro_rules! bitvec {
    [ $($t:tt)* ] => {
        {
            bitvec::bitvec![u32, Lsb0; $($t)*]
        }
    };
}

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

/** Rounding modes
 *
 * The IEEE-754 standard specifies five rounding modes:
 *
 *  - two nearest modes:
 *    - _roundTiesToEven_: rounds to the nearest representable floating-point value.
 *       In this case there is a tie, round to the floating-point value whose
 *       mantissa has a least significant bit of 0.
 *    - _roundTiesToAway_: rounds to the nearest representable floating-point value.
 *       In this case there is a tie, round to the floating-point value with greater magnitude.
 *  - three directed modes:
 *    - _roundTowardPositive_: rounds to the closest representable floating-point value
 *      in the direction of positive infinity.
 *    - _roundTowardNegative_: rounds to the closest representable floating-point value
 *      in the direction of negative infinity.
 *    - _roundTowardZero_: rounds to the closest representable floating-point value
 *      in the direction of zero.
 *
 * This module defines a sixth:
 *  - _roundToOdd_: rounds to the closest representable floating-point value
 *      whose mantissa has a least significant bit of 1.
 *
 * The rounding behavior of zero, signed zero, positive infinity, negative infinity,
 * and all encodings of NaN  will be unaffected by rounding mode.
 */
pub enum RoundingMode {
    // nearest modes
    RoundNearestEven,
    RoundNearestAway,
    // directed
    RoundToPositive,
    RoundToNegative,
    RoundToZero,
    // strange
    RoundToOdd,
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

    /// Bitwidth of the NaN payload.
    /// This is just `Self::M - 1`.
    pub const NAN_PAYLOAD_SIZE: usize = Self::M - 1;

    /// Returns the exponent bias.
    /// This is just `Self::EMAX`.
    #[inline(always)]
    pub const fn bias() -> i64 {
        Self::EMAX
    }
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
    pub fn nan(sign: bool, signaling: bool, payload: BitVec) -> Self {
        assert_eq!(
            payload.len(),
            Self::NAN_PAYLOAD_SIZE,
            "expected a payload size of {}, received {}",
            Self::NAN_PAYLOAD_SIZE,
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
            FloatNum::Number(_, e, _) => *e != 0 && *e < Self::EMIN,
            _ => false,
        }
    }

    /// Returns true if this `Float` encodes a normal number
    pub fn is_normal(&self) -> bool {
        match &self.num {
            FloatNum::Number(_, e, _) => *e >= Self::EMIN,
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
    /// The result is wrapped in an option since only NaNs
    /// can be signaling.
    pub fn is_signaling_nan(&self) -> Option<bool> {
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
}

// Packed float utilities
impl<const E: usize, const N: usize> Float<E, N> {
    // Splices a packed floating-point representation into
    // the sign, exponent, and mantissa field.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn split_packed(bv: &BitVec) -> (bool, BitVec, BitVec) {
        (
            Self::packed_sign(bv),
            Self::packed_exponent(bv),
            Self::packed_mantissa(bv),
        )
    }

    #[inline]
    fn pack_components(s: bool, e: BitVec, m: BitVec) -> BitVec {
        assert_eq!(
            e.len(),
            E,
            "trying to pack a float with exponent width: {}, expected {}",
            e.len(),
            E
        );
        assert_eq!(
            m.len(),
            Self::M,
            "trying to pack a float with mantissa width: {}, expected {}",
            m.len(),
            Self::M
        );

        let mut bv = bitvec![0; N];
        for (i, b) in m.iter().enumerate() {
            bv.set(i, *b);
        }
        for (i, b) in e.iter().enumerate() {
            bv.set(i + Self::M, *b);
        }
        bv.set(N - 1, s);
        bv
    }

    // Returns the sign field from a packed floating-point representation.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn packed_sign(bv: &BitVec) -> bool {
        bv[N - 1]
    }

    // Returns the exponent field from a packed floating-point representation.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn packed_exponent(bv: &BitVec) -> BitVec {
        bv[(N - E - 1)..(N - 1)].into()
    }

    // Returns the mantissa field from a packed floating-point representation.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn packed_mantissa(bv: &BitVec) -> BitVec {
        bv[..(N - E - 1)].into()
    }
}

// Rounding (casts)
impl<const E: usize, const N: usize> Float<E, N> {
    /// Rounds this `Float` to the representation specified by `Float<E2, N2>`.
    pub fn round<const E2: usize, const N2: usize>(&self, rm: RoundingMode) -> Float<E2, N2> {
        match &self.num {
            FloatNum::Number(s, _, _) => {
                if self.is_zero() {
                    // easy case: also a zero in the new representation
                    Float::<E2, N2>::zero(*s)
                } else {
                    // hard case: need to actually round
                    Self::round_finite(self, rm)
                }
            }
            FloatNum::Infinity(s) => Float::<E2, N2>::infinity(*s),
            FloatNum::Nan(s, signal, payload) => {
                let payload = if Self::NAN_PAYLOAD_SIZE < Float::<E2, N2>::NAN_PAYLOAD_SIZE {
                    // expand the payload with zeros
                    // payload is put in the most signficant bits
                    let diff = Float::<E2, N2>::NAN_PAYLOAD_SIZE - Self::NAN_PAYLOAD_SIZE;
                    let mut p = BitVec::repeat(false, Float::<E2, N2>::NAN_PAYLOAD_SIZE);
                    for (i, b) in payload.iter().enumerate() {
                        p.set(diff + i, *b);
                    }
                    p
                } else {
                    // truncate the payload
                    // only keep the most signficant bits
                    let size = Float::<E2, N2>::NAN_PAYLOAD_SIZE;
                    let diff = Self::NAN_PAYLOAD_SIZE - size;
                    let mut p = BitVec::repeat(false, size);
                    for i in 0..size {
                        p.set(i, *payload.get(i + diff).unwrap());
                    }
                    p
                };
                Float::<E2, N2>::nan(*s, *signal, payload)
            }
        }
    }

    // Rounds a finite, non-zero number in the representation specified
    // by `Float<E2, N2>` using the rounding mode `rm`.
    fn round_finite<const E2: usize, const N2: usize>(&self, rm: RoundingMode) -> Float<E2, N2> {
        // unpack
        let (s, mut exp, m) = match &self.num {
            FloatNum::Number(s, exp, m) => (*s, *exp, m),
            _ => panic!("called on a non-finite float"),
        };

        // We will construct the new mantissa with two rounding bits (RS).
        // Then we'll call the (rounding) finalizer to complete the rounding
        // process and raise the correct exception flags.
        let mut m2 = BitVec::repeat(false, Float::<E2, N2>::M);
        let mut half_bit = false;
        let mut quarter_bit = false;

        if m.len() < Float::<E2, N2>::M {
            // the current mantissa will fit entirely in the new mantissa
            // insert most significant bits, then fill with zeros
            // `half_bit` and `quarter_bit` are clearly zero
            // adjust `exp` accordingly
            let diff = m2.len() - m.len();
            for (i, b) in m.iter().enumerate() {
                m2.set(i + diff, *b);
            }
        }

        todo!()
    }
}

// Implementing `Default` for `Float`
impl<const E: usize, const N: usize> Default for Float<E, N> {
    fn default() -> Self {
        Self::new()
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

        // split fields
        let (s, e, mut m) = Self::split_packed(&bv);
        let mut exponent = bitvec_to_biguint(e).to_i64().unwrap() - Self::bias();

        // branch on exponent
        if exponent > Self::EMAX {
            if m.not_any() {
                // infinity
                Self::infinity(s)
            } else {
                // NaN
                Self::nan(s, m[N - E - 2], m[..N - E - 2].into())
            }
        } else if exponent < Self::EMIN {
            // subnormal or zero
            if m.not_any() {
                // zero
                Self::zero(s)
            } else {
                // subnormal
                let exp_diff = 1 + m.trailing_zeros();
                m.push(false);
                m.shift_right(exp_diff);
                exponent -= exp_diff as i64;
                assert_eq!(m.len(), Self::PREC);
                Self {
                    num: FloatNum::Number(s, exponent, m),
                    flags: Exceptions::default(),
                }
            }
        } else {
            // normal
            m.push(true);
            assert_eq!(m.len(), Self::PREC);
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
        let mut bv = bitvec![0; 64];
        let b = f.to_bits();
        bv.store(b);
        Self::from(bv)
    }
}

// Implementing `Float<E, N>` for `f64`
impl<const E: usize, const N: usize> From<Float<E, N>> for BitVec {
    fn from(f: Float<E, N>) -> Self {
        match f.num {
            FloatNum::Number(s, exp, m) => {
                if exp == 0 && m.not_any() {
                    let m = bitvec![0; Float::<E, N>::M];
                    let e = bitvec![0; E];
                    Float::<E, N>::pack_components(s, e, m)
                } else if exp < Float::<E, N>::EMIN {
                    // subnormal
                    let mut m = m;
                    let e = bitvec![0; E];
                    let diff = Float::<E, N>::EMIN - exp - 1;
                    m.shift_left(diff as usize);
                    m.pop(); // leading one is now a leading zero
                    Float::<E, N>::pack_components(s, e, m)
                } else {
                    // normal
                    let mut exponent = exp + Float::<E, N>::bias();
                    let m: BitVec = m[..N - E - 1].into(); // remove leading 1
                    let mut e = bitvec![0; E];
                    for i in 0..E {
                        e.set(i, (exponent % 2) != 0);
                        exponent >>= 1;
                    }

                    Float::<E, N>::pack_components(s, e, m)
                }
            }
            FloatNum::Infinity(s) => {
                let m = bitvec![0; Float::<E, N>::M];
                let e = bitvec![1; E];
                Float::<E, N>::pack_components(s, e, m)
            }
            FloatNum::Nan(s, signal, payload) => {
                let mut m = payload;
                let e = bitvec![1; E];
                m.push(signal); // mantissa = signal | payload
                Float::<E, N>::pack_components(s, e, m)
            }
        }
    }
}

// Implementing `Float<11, 64>` for `f64`
impl From<Float<11, 64>> for f64 {
    fn from(f: Float<11, 64>) -> Self {
        let bv: BitVec = f.into();
        f64::from_bits(bv[..64].load())
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
