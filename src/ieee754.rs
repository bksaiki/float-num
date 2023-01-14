use bitvec::{*, vec::BitVec};

/// Alias for `Float<15, 128>` (quad-precision number)
pub type Quad = Float<15, 128>;
/// Alias for `Float<11, 64>` (double-precision number)
pub type Double = Float<11, 64>;
/// Alias for `Float<8, 32>` (single-precision number)
pub type Single = Float<8, 32>;
/// Alias for `Float<5, 16>` (half-precision number)
pub type Half = Float<5, 16>;

/** A floating-point number as specified by the IEEE-754 standard.
 * 
 * The generics `E` and `N` specify the number of bits in the
 * exponent field and in the entire float overall.
 * 
 */
#[derive(Clone)]
pub struct Float<const E: usize, const N: usize> {
    // numerical data
    s: bool,
    exp: usize,
    c: BitVec,

    // class info
    inf: bool,
    nan: bool,

    // NaN data
    signaling_nan: bool,
    nan_payload: BitVec,
}

impl<const E: usize, const N: usize> Float<E, N> {
    /// Creates a new `Float` with `E` exponent bits and `N` total bits.
    /// Initializes the `Float` to 0.
    pub fn new() -> Self {
        assert!((2 <= E) && (E <= 60));
        Self {
            s: false,
            exp: 0,
            c: bitvec![0; Self::prec()],
            inf: false,
            nan: false,
            signaling_nan: false,
            nan_payload: bitvec![0; Self::nan_payload_size()],
        }
    }

    /// Returns an infinity value with a particular sign
    /// using the same width parameters as this `Float`.
    #[inline]
    pub fn infinity(sign: bool) -> Self {
        Self {
            s: sign,
            exp: 0,
            c: bitvec![0; Self::prec()],
            inf: true,
            nan: false,
            signaling_nan: false,
            nan_payload: bitvec![0; Self::nan_payload_size()],
        }
    }

    /// Returns the sign of this `Float`.
    #[inline]
    pub fn sign(&self) -> bool {
        self.s
    }

    /// Returns the exponent of this `Float`.
    #[inline]
    pub fn exponent(&self) -> usize {
        self.exp
    }

    /// Returns the (integer) mantissa of this `Float` as a `Bitvec`.
    #[inline]
    pub fn significand(&self) -> BitVec {
        self.c.clone()
    }

    /// Returns true if this `Float` encodes an infinity.
    #[inline]
    pub fn is_inf(&self) -> bool {
        self.inf
    }

    /// Returns true if this `Float` encodes a NaN.
    #[inline]
    pub fn is_nan(&self) -> bool {
        self.nan
    }

    /// Returns true if this `Float` encodes a signaling NaN.
    #[inline]
    pub fn is_signaling(&self) -> bool {
        self.signaling_nan
    }

    /// Returns the NaN payload of this `Float` as a `Bitvec`.
    #[inline]
    pub fn nan_payload(&self) -> BitVec {
        self.nan_payload.clone()
    }

    /// Returns the radix of this `Float`, in this case, 2.
    #[inline(always)]
    pub const fn radix() -> usize {
        2
    }

    /// Returns the number of (binary digits) in the signficand for this `Float`.
    /// This is just `Self::mantissa_size() + 1`.
    #[inline(always)]
    const fn prec() -> usize {
        N - E
    }

    /// Returns maximum exponent value of this `Float` when in normalized form.
    #[inline(always)]
    pub const fn emax() -> usize {
        usize::pow(2, E as u32) - 1
    }

    /// Returns minimum exponent value of this `Float` when in normalized form.
    /// This will always be `1 - Self::emax()`.
    #[inline(always)]
    pub const fn emin() -> usize {
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
        N - E - 3
    }
}
