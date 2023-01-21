/*
    Operations
*/

use crate::Number;

pub trait Round<N: Number>: Number {
    /// Performs a rounding operation returning the result.
    /// The output type may differ from the input type.
    fn round(&self, ctx: &Self::Ctx) -> N;
}
