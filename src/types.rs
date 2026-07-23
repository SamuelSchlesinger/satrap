use std::fmt;
use std::ops::Not;

pub(crate) const MAX_VARIABLES: usize = (u32::MAX as usize / 2) + 1;

/// A zero-based Boolean variable identifier.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Var(u32);

impl Var {
    /// Creates a variable from its zero-based index.
    ///
    /// # Panics
    ///
    /// Panics if the index cannot be packed into a [`Lit`].
    #[must_use]
    pub const fn new(index: u32) -> Self {
        assert!(
            index <= u32::MAX >> 1,
            "variable index exceeds packed literal range"
        );
        Self(index)
    }

    /// Returns the variable's zero-based index.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) const fn raw(self) -> u32 {
        self.0
    }
}

/// A compact Boolean literal.
///
/// The low bit stores the sign, so negation is a single XOR. Positive literals
/// have an even representation and negative literals have an odd one.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lit(u32);

impl Lit {
    /// Creates a positive literal.
    #[must_use]
    pub const fn positive(var: Var) -> Self {
        Self(var.raw() << 1)
    }

    /// Creates a negative literal.
    #[must_use]
    pub const fn negative(var: Var) -> Self {
        Self((var.raw() << 1) | 1)
    }

    /// Creates a literal with the requested polarity.
    #[must_use]
    pub const fn new(var: Var, positive: bool) -> Self {
        if positive {
            Self::positive(var)
        } else {
            Self::negative(var)
        }
    }

    /// Returns the literal's variable.
    #[must_use]
    pub const fn var(self) -> Var {
        Var(self.0 >> 1)
    }

    /// Returns whether this literal is positive.
    #[must_use]
    pub const fn is_positive(self) -> bool {
        self.0 & 1 == 0
    }

    /// Returns the packed literal index used by watch lists.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) const fn raw(self) -> u32 {
        self.0
    }

    pub(crate) const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    /// Converts a nonzero DIMACS literal to the compact representation.
    #[must_use]
    pub fn from_dimacs(value: i64) -> Option<Self> {
        if value == 0 || value.unsigned_abs() > MAX_VARIABLES as u64 {
            return None;
        }
        let variable = u32::try_from(value.unsigned_abs() - 1).ok()?;
        Some(Self::new(Var::new(variable), value > 0))
    }

    /// Converts the literal to DIMACS's signed, one-based representation.
    #[must_use]
    pub fn to_dimacs(self) -> i64 {
        let variable = i64::from(self.var().raw()) + 1;
        if self.is_positive() {
            variable
        } else {
            -variable
        }
    }
}

impl Not for Lit {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(self.0 ^ 1)
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.to_dimacs())
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.to_dimacs())
    }
}

#[cfg(test)]
mod tests {
    use super::{Lit, Var};

    #[test]
    fn dimacs_round_trip_and_negation() {
        for value in [-100, -1, 1, 2, 100] {
            let literal = Lit::from_dimacs(value).unwrap();
            assert_eq!(literal.to_dimacs(), value);
            assert_eq!((!literal).to_dimacs(), -value);
            assert_eq!(!(!literal), literal);
        }
        assert_eq!(Lit::from_dimacs(0), None);
        assert_eq!(
            Lit::from_dimacs(-2_147_483_648),
            Some(Lit::negative(Var::new(2_147_483_647)))
        );
        assert_eq!(Lit::from_dimacs(2_147_483_649), None);
        assert_eq!(Lit::positive(Var::new(7)).index(), 14);
    }
}
