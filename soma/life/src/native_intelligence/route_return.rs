//! The world return derives the returned interaction. Nothing here is typed by an operator.
//!
//! A conducted route carried declarations into emissions; each emission crossed the kernel
//! boundary once and returned one face. The junction counts crossings: `R` emissions incident,
//! `M` admitted, with `Γ = (R − M) : (R + M)` and `T = 4RM : (R + M)²` carried as integer pairs
//! and never divided until the exact rational current is formed. A match (every emission
//! admitted) deposits the unit current with storage one and halts. A partial reflection deposits
//! `(T, Γ)` with storage `1 / service rounds`; its cone is what the admitted emissions carried,
//! and the declarations carried only by reflected emissions re-enter. A boundary that admitted
//! nothing is a terminus by type: no deposit, an obstruction naming what reflected, and the next
//! entering occurrence founded from the proof it names when the corpus carries one.
//!
//! Jurisdiction: the kernel, its diagnostics, and the cold witness are world and observer
//! apparatus. They enter only through this derivation and never route conduct.

use std::collections::BTreeSet;
use std::fmt;

use holonic_engine::{
    receiver_history_compression::NativeStateId, BoundaryId, EventId, ExactComplexWaveCurrent,
};
use holonic_structure::CountedCrossing;
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};

use crate::lean_mathematics::kernel_returns::LeanKernelReturnFamily;
use crate::lean_mathematics::LeanLatticeColdWitness;

use super::{NativeCirculationBoundary, ReturnedScaffoldInteraction, ScaffoldCultivationError};

/// One kernel return read as faces: whether the kernel admitted it, the declarations the route
/// carried into it, and the diagnostic the kernel returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct KernelReturnFace {
    pub admitted: bool,
    pub carried: BTreeSet<String>,
    pub diagnostic: String,
}

/// Read one kernel return family as faces.
pub fn kernel_return_faces(family: &LeanKernelReturnFamily) -> Vec<KernelReturnFace> {
    family
        .members()
        .iter()
        .map(|returned| KernelReturnFace {
            admitted: returned.kernel_admitted(),
            carried: returned
                .candidate()
                .declaration_lineage
                .iter()
                .map(|name| name.to_string())
                .collect(),
            diagnostic: returned.diagnostic().to_owned(),
        })
        .collect()
}

/// The junction between the incident emissions and the admitted emissions, as exact pairs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RouteJunction {
    pub incident: u64,
    pub transmitted: u64,
    pub reflection: (i128, u128),
    pub transmission: (u128, u128),
    pub service_rounds: u128,
}

impl RouteJunction {
    fn from_crossing(crossing: CountedCrossing) -> Self {
        Self {
            incident: crossing.incident(),
            transmitted: crossing.transmitted(),
            reflection: crossing.reflection_pair(),
            transmission: crossing.power_transmission_pair(),
            service_rounds: crossing.service_rounds(),
        }
    }

    pub const fn matched(&self) -> bool {
        self.incident == self.transmitted
    }

    pub fn reflection_current(&self) -> Rat {
        Rat::new(
            BigInt::from(self.reflection.0),
            BigInt::from(self.reflection.1),
        )
    }

    pub fn transmission_current(&self) -> Rat {
        Rat::new(
            BigInt::from(self.transmission.0),
            BigInt::from(self.transmission.1),
        )
    }

    pub fn storage(&self) -> Rat {
        Rat::new(BigInt::from(1), BigInt::from(self.service_rounds))
    }
}

/// A boundary that admitted nothing: the obstruction carries what reflected.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RouteObstruction {
    pub carried: BTreeSet<String>,
    pub named_by_diagnostic: BTreeSet<String>,
    pub next_entering: Option<EventId>,
}

/// What the world return did to the continuing body and what continues.
#[derive(Debug)]
pub enum WorldReturnDisposition {
    /// Every emission was admitted through: deposit with storage one and halt.
    Matched {
        returned: ReturnedScaffoldInteraction,
        junction: RouteJunction,
        survived: BTreeSet<String>,
    },
    /// Some emissions reflected: deposit `(T, Γ)` with storage `1 / rounds` on what the admitted
    /// emissions carried; the declarations carried only by reflected emissions re-enter.
    Reflected {
        returned: ReturnedScaffoldInteraction,
        junction: RouteJunction,
        survived: BTreeSet<String>,
        reflected: BTreeSet<String>,
        next_entering: Option<EventId>,
    },
    /// Nothing was admitted: a terminus by type, no deposit.
    Terminus(RouteObstruction),
}

/// The termination law read off the disposition. No count, threshold, or chooser appears.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Termination {
    Halt,
    Reenter(EventId),
    Open,
}

impl WorldReturnDisposition {
    pub fn termination(&self) -> Termination {
        match self {
            Self::Matched { .. } => Termination::Halt,
            Self::Reflected { next_entering, .. } | Self::Terminus(RouteObstruction {
                next_entering,
                ..
            }) => next_entering.map_or(Termination::Open, Termination::Reenter),
        }
    }

    pub fn returned(&self) -> Option<&ReturnedScaffoldInteraction> {
        match self {
            Self::Matched { returned, .. } | Self::Reflected { returned, .. } => Some(returned),
            Self::Terminus(_) => None,
        }
    }
}

#[derive(Debug)]
pub enum RouteReturnError {
    NoCarriedDeclarations,
    UnknownDeclaration(String),
    Return(ScaffoldCultivationError),
}

impl fmt::Display for RouteReturnError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoCarriedDeclarations => {
                write!(formatter, "the kernel returns carried no declaration")
            }
            Self::UnknownDeclaration(name) => {
                write!(formatter, "the carried declaration {name} has no carrier")
            }
            Self::Return(error) => write!(formatter, "the returned interaction refused: {error}"),
        }
    }
}

impl std::error::Error for RouteReturnError {}

fn named_in(diagnostic: &str, carried: &BTreeSet<String>) -> BTreeSet<String> {
    carried
        .iter()
        .filter(|name| diagnostic.contains(name.as_str()))
        .cloned()
        .collect()
}

/// The next entering occurrence founded from the proofs that reflected: the smallest occurrence
/// whose referring declaration is one of them, when the corpus carries one.
fn next_entering(witness: &LeanLatticeColdWitness, reflected: &BTreeSet<String>) -> Option<EventId> {
    witness
        .reference_by_occurrence
        .iter()
        .find(|(_, reference)| reflected.contains(&reference.referring))
        .map(|(occurrence, _)| EventId(*occurrence))
}

/// Derive the returned interaction from one conducted boundary and the kernel faces its route
/// returned. `returned_occurrence` is the world-return event, later than the boundary's ingress.
pub fn derive_world_return(
    boundary: &NativeCirculationBoundary,
    witness: &LeanLatticeColdWitness,
    faces: &[KernelReturnFace],
    returned_occurrence: EventId,
    emitting_boundary: BoundaryId,
) -> Result<WorldReturnDisposition, RouteReturnError> {
    let carried = faces
        .iter()
        .flat_map(|face| face.carried.iter().cloned())
        .collect::<BTreeSet<_>>();
    if carried.is_empty() {
        return Err(RouteReturnError::NoCarriedDeclarations);
    }
    let survived = faces
        .iter()
        .filter(|face| face.admitted)
        .flat_map(|face| face.carried.iter().cloned())
        .collect::<BTreeSet<_>>();
    let named_by_diagnostic = faces
        .iter()
        .filter(|face| !face.admitted)
        .flat_map(|face| named_in(&face.diagnostic, &face.carried))
        .collect::<BTreeSet<_>>();
    let states = survived
        .iter()
        .map(|name| {
            witness
                .state_of(name)
                .ok_or_else(|| RouteReturnError::UnknownDeclaration(name.clone()))
        })
        .collect::<Result<BTreeSet<NativeStateId>, _>>()?;
    let admitted = faces.iter().filter(|face| face.admitted).count() as u64;

    let Some(crossing) = CountedCrossing::meet(faces.len() as u64, admitted) else {
        let reflected = &carried | &named_by_diagnostic;
        return Ok(WorldReturnDisposition::Terminus(RouteObstruction {
            next_entering: next_entering(witness, &reflected),
            carried,
            named_by_diagnostic,
        }));
    };
    let junction = RouteJunction::from_crossing(crossing);
    let (current, storage) = if junction.matched() {
        (ExactComplexWaveCurrent::one(), Rat::from_integer(BigInt::from(1)))
    } else {
        (
            ExactComplexWaveCurrent::new(
                junction.transmission_current(),
                junction.reflection_current(),
            ),
            junction.storage(),
        )
    };
    let returned = ReturnedScaffoldInteraction::found(
        boundary.emission.address.clone(),
        returned_occurrence,
        emitting_boundary,
        current,
        storage,
        states,
    )
    .map_err(RouteReturnError::Return)?;
    if junction.matched() {
        return Ok(WorldReturnDisposition::Matched {
            returned,
            junction,
            survived,
        });
    }
    let reflected = &(&carried - &survived) | &named_by_diagnostic;
    Ok(WorldReturnDisposition::Reflected {
        next_entering: next_entering(witness, &reflected),
        returned,
        junction,
        survived,
        reflected,
    })
}
