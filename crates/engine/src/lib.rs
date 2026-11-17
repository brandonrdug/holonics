//! The engine: the built attempt that trains, its law and its host reference (docs/plans/THE_CONSOLIDATION.md, D1 and D2).
//! Its guide is docs/THE_ENGINE.md. The modules are cut by object (§5): each holds one object's law, and `field` re-exports the law's modules.
//! The items the engine took from the October machine stand in the module of their object since C5's second part (#603):
//! the grains and the refusal in `width`, the release, the exponential and logarithm faces and the ratio's adjoint in `ratio`,
//! the tower's face and its codes in `face`, the maps and the covector in `adjoint`, the deposit's step in `deposit`, the
//! receiver's coupling at temperature one in `coupling` and the width census in `census`.

pub mod adjoint;
pub mod carry;
pub mod codec;
pub mod constitution;
pub mod contact;
pub mod declaration;
pub mod deposit;
pub mod face;
pub mod field;
pub mod founding;
pub mod census;
pub mod closed;
pub mod coupling;
pub mod learner;
pub mod level;
pub mod moment;
pub mod navigator;
pub mod passage;
pub mod ratio;
pub mod realization;
pub mod region;
pub mod release;
pub mod ruler;
pub mod units;
pub mod width;
