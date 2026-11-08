//! **Shears** (N7): the reversible primitive `(x, y) ↦ (x, y + f(x))`, invertible for any `f`, rounded or
//! not. A shear carries its inverse, so an adjoint built of shears needs no tape. The only irreversible event
//! is a merge (a release that drops its remainder), whose least cost is the log of its fibre.

use super::value::Value;
use super::Result;

/// A reversible update that carries its own inverse.
pub trait Shear {
    fn apply(&mut self) -> Result<()>;
    fn undo(&mut self) -> Result<()>;
}

/// **The additive shear** `y ← y + d`, its inverse `y ← y − d`: the class of `y` returns (its width,
/// a need, may have grown).
#[derive(Clone, Debug)]
pub struct AddShear {
    pub y: Value,
    pub d: Value,
}

impl Shear for AddShear {
    fn apply(&mut self) -> Result<()> {
        self.y = self.y.add(&self.d)?;
        Ok(())
    }

    fn undo(&mut self) -> Result<()> {
        self.y = self.y.sub(&self.d)?;
        Ok(())
    }
}
