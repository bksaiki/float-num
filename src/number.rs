/*
    Defines a number
*/

/// The number type.
///
/// The central type of this library.
/// A `Number` encodes a number with some exceptions, say NaN from IEEE-754.
/// This is just a bare-bones storage type
pub trait Number: Clone + Default {
    /// The rounding context associated with this `Number`.
    type Ctx: Context;

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

    /// Negates this `Number`, rounding the result according
    /// to the provided context.
    fn neg(&self, ctx: &Self::Ctx) -> Self;

    /// Takes the absolute value for `Number`, rounding the
    /// result according to the provided context.
    fn abs(&self, ctx: &Self::Ctx) -> Self;

    /// Adds this `Number` and another, rounding the result
    /// according to the provided context.
    fn add(&self, other: &Self, ctx: &Self::Ctx) -> Self;

    /// Multiplies this `Number` and another, rounding the result
    /// according to the provided context.
    fn mul(&self, other: &Self, ctx: &Self::Ctx) -> Self;
}

/// A specification for rounding behavior.
///
/// For any computer number system, most mathematical operators
/// can be decomposed into two operations:
///  - a real number operation: `R^n -> R`, and
///  - a rounding operation: `R -> R`.
/// A `Context` describes the second operation, the rounding behavior that
/// should be used to apply a "fit-to-representation" on a real number output.
pub trait Context {}
