/*
    Traits relevant to rounding
*/

/// A mathematical operation on computer number types.
///
/// For any computer number system, most mathematical operators
/// can be decomposed into two operations:
///  - a real number operation: `R^n -> R`, and
///  - a rounding operation: `R -> R`.
/// An `Operation` describes the entire operation
pub trait Operation {}

/// A specification for rounding behavior.
///
/// For any computer number system, most mathematical operators
/// can be decomposed into two operations:
///  - a real number operation: `R^n -> R`, and
///  - a rounding operation: `R -> R`.
/// A `Context` describes the second operation, the rounding behavior that
/// should be used to apply a "fit-to-representation" on a real number output.
pub trait Context: Sized {}
