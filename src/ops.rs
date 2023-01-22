/*
    Operations
*/

use crate::Number;

/// The result of `Round::round_exact`.
/// The rounded result was either exactly representable
/// or is different than the original result.
pub enum RoundResult<N: Number> {
    Exact(N),
    Inexact(N),
}

impl<N: Number> RoundResult<N> {
    /// Extracts the number stored within.
    pub fn value(self) -> N {
        match self {
            Self::Exact(v) => v,
            Self::Inexact(v) => v,
        }
    }
}

pub trait Round<N: Number>: Number {
    /// The error type of `try_round`
    type Error;

    /// Performs a rounding operation returning the result.
    /// The output type may differ from the input type.
    fn round(&self, ctx: &Self::Ctx) -> N;

    /// Performs a rounding operation returning the result
    /// wrapped in a `RoundResult<N>`.
    fn round_exact(&self, ctx: &Self::Ctx) -> RoundResult<N>;

    /// Performs a rounding operation, returning the result as `Option<RoundResult<N>>`.
    /// The result will be `None` if the operation failed.
    fn try_round(&self, ctx: &Self::Ctx) -> Result<RoundResult<N>, Self::Error>;
}
