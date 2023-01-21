/*
    Defines a number
*/

/// The number type, the central type of this library.
///
/// A `Number` encodes a number with some exceptions, say NaN from IEEE-754.
/// This is just a bare-bones storage type
pub trait Number: Clone + Default {
    /// Returns true if this `Number` encodes a zero.
    fn is_zero(&self) -> bool;

    /// Returns true if this `Number` encodes an infinity.
    fn is_infinity(&self) -> bool;

    /// Returns true if this `Number` does not encode a number.
    fn is_nan(&self) -> bool;

    /// Returns true if this `Number` encodes a finite number.
    fn is_finite(&self) -> bool;

    /// Returns true if this `Number` encodes a rational number.
    fn is_rational(&self) -> bool;
}
