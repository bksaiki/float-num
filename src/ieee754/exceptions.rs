/*
    Exceptions
*/

use super::*;

impl Exceptions {
    /// Clears all exceptions.
    pub fn clear(&mut self) {
        self.invalid = false;
        self.div_by_zero = false;
        self.overflow = false;
        self.underflow = false;
        self.inexact = false;
        self.carry = false;
    }

    /// Sets the `invalid` field.
    pub fn with_invalid(mut self, raised: bool) -> Self {
        self.invalid = raised;
        self
    }

    /// Sets the `div_by_zero` field.
    pub fn with_div_by_zero(mut self, raised: bool) -> Self {
        self.div_by_zero = raised;
        self
    }

    /// Sets the `overflow` field.
    pub fn with_overflow(mut self, raised: bool) -> Self {
        self.overflow = raised;
        self
    }

    /// Sets the `underflow` field.
    pub fn with_underflow(mut self, raised: bool) -> Self {
        self.underflow = raised;
        self
    }

    /// Sets the `inexact` field.
    pub fn with_inexact(mut self, raised: bool) -> Self {
        self.inexact = raised;
        self
    }

    /// Sets the `carry` field.
    pub fn with_carry(mut self, raised: bool) -> Self {
        self.carry = raised;
        self
    }
}
