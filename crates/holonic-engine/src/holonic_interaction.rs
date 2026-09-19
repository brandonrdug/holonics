//! **The Holonic Interaction unit: `|source⟩`, a standing medium `H_int`, a dynamic `H_pert`, and
//! `⟨perspective|` — with the exchange at a medium's contact faces and the modal response derived
//! from that same dynamics.**
//!
//! [definition] This module is the executable owner of the **unit and its media** half of the
//! Holonic Interaction subject named in
//! `docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. The derivation it
//! implements is the linear dissipative specialization written out in
//! `docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md` under "The general embedding and
//! its consuming composition". Its Lean counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Transport/HolonicInteraction.lean`
//! (namespace `Soma.Holonics.Transport.HolonicInteraction`), and the correspondence is the
//! deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `quad`, `quad_add`, `quad_neg`, `quad_smul` | [`ContactDissipation::power`] and [`ClockedEnergy`] |
//! | `faceForm`, `contactForm` | [`ContactFace`] and [`ContactDissipation::assemble`] |
//! | `quad_faceForm`, `quad_contactForm` | [`ContactDissipation::power_by_face`], which returns the face population and never only its sum |
//! | `contactForm_nonneg` | [`ContactDissipation`]'s constructor, which certifies positive semidefiniteness through [`crate::inertia::inertia`] and refuses otherwise |
//! | `contactForm_quad_eq_zero_iff`, `contactForm_quad_eq_zero_iff_no_slip` | [`ContactDissipation::zero_slip_kernel`] |
//! | `contactForm_mulVec_eq_zero_of_no_slip`, `contactForm_kernel_iff` | [`ContactDissipation::kernel_basis`] compared against the zero-slip kernel |
//! | `clockedEnergy`, `clockedEnergy_eq_duration_times_power`, `clockedEnergy_scales_inversely` | [`ContactDissipation::clocked_energy`] and [`Clock`] |
//! | `rateFormQ`, `portGenerator`, `port_storage_rate` | [`Medium::generator`] and [`StorageRateReading`], read through [`crate::causal_chord::rate_form`] |
//! | `port_storage_rate_zero_of_no_dissipation` | [`StorageRateReading::is_conservative`] |
//! | `quad_congruence`, `storage_rate_reading`, `storage_rate_nonpos`, `storage_rate_neg_of_active_slip` | [`StorageRateReading::predicted`] and [`SpectralReading`] |
//! | `indefiniteStorage_rate_form_vanishes`, `swapGenerator_has_a_right_half_plane_mode`, `vanishing_rate_form_places_no_spectrum` | [`SpectralReading::NoLicenceWithoutDefiniteStorage`] |
//! | `interface_tangential_agreement_retains_normal_remainder` | [`InterfaceReading`], whose normal half is [`crate::junction_law::check_junction`] |
//! | `tangentialConservation_retainsNormalRemainder`, `snellCompatible_iff`, `finiteInterfaceChain_eq_exterior` | the same reading's retained normal remainder |
//!
//! # What a medium is
//!
//! [definition] A [`Medium`] is a standing `H_int`: a configuration space of declared dimension,
//! a **storage form** `G` — symmetric, exact, and *not* assumed definite — a skew structure `Ω`,
//! and the contact faces at which it exchanges. Every one of those enters through a checked
//! constructor, and the declared dimension is bounded before anything is sized by it.
//!
//! [definition] A [`ContactFace`] is the place the exchange happens. It carries an exact slip map
//! `J_f` (relative slip `s_f = J_f v`), a constitutive response `D_f` giving the traction
//! `t_f = −D_f s_f`, and a declared positive weight `w_f` — the face's area or measure. `D_f` is
//! **checked** positive semidefinite in the declared pairing through
//! [`crate::inertia::inertia`], and a face whose response is indefinite is refused by name.
//!
//! # The contact exchange
//!
//! [proved-derived; implemented-exact] The carrier plan's derivation, exactly:
//!
//! ```text
//!   M_contact = Σ_f w_f J_fᵀ D_f J_f          P_diss(v) = ⟨v, M_contact v⟩ ≥ 0
//! ```
//!
//! [`ContactDissipation`] assembles it, certifies the positive semidefiniteness rather than
//! asserting it, and returns the kernel — the motions with zero slip on every dissipative face —
//! as a basis rather than as a dimension.
//!
//! [definition] **A position edit is not an energy until its clock is declared.** Over a duration
//! `h > 0` at the constant velocity `v = δq/h`, the dissipated energy is
//! `⟨δq, M_contact δq⟩ / h`, and [`ClockedEnergy`] carries the duration and the unit tag with the
//! number. [`compare_edit_metric`] is the reading that says when T4's [`crate::edit_rigidity::
//! ExactMetric`] — the metric [`crate::edit_rigidity::rethreading_work`] takes, whose `W²` is a
//! squared norm in it — **is** `M_contact/h` for a declared clock and when it is only an authored
//! edit metric. It returns a typed reading and never a boolean, because the third answer —
//! `M_contact` is degenerate, so it is not a metric at any clock — is neither of the first two.
//!
//! # The derived modal response
//!
//! [agent-inferred] The joint local dynamics is taken in the **port-Hamiltonian** form
//!
//! ```text
//!   q̇ = A q + B u,       A = (Ω − M_contact) G,       Ω ᵀ = −Ω,   Gᵀ = G,   M_contactᵀ = M_contact
//! ```
//!
//! inferred from the mathematics rather than declared by the contract: the skew/symmetric
//! splitting is the only one in which the assembled contact form enters the generator as itself
//! and the storage rate comes out as exactly `−2` times the dissipated power. The Lean owner's
//! `port_storage_rate` is that identity:
//!
//! ```text
//!   Aᵀ G + G A = −2 G M_contact G
//! ```
//!
//! [`HolonicInteraction::linearization`] hands `(A, B, C_R)` to
//! [`crate::causal_chord::Linearization::declared`], so the transfer function, the pole atlas and
//! the rate form are **read from that owner** and not re-implemented here.
//! [`HolonicInteraction::storage_rate`] calls [`crate::causal_chord::rate_form`] and compares it
//! with `−2 G M G` entry by entry; conservation at `M = 0` and strict decay on the slip-active
//! subspace are consequences of the identity, not separate code.
//!
//! # The defect this owner refuses to repeat
//!
//! [proved-derived] `G = diag(1, −1)` with `A = [[0,1],[1,0]]` has `AᵀG + GA = 0` and eigenvalues
//! `±1`. **A vanishing or negative-semidefinite rate form licenses no spectral placement without
//! positive definiteness of `G`.** [`SpectralReading`] is therefore a three-armed typed return
//! guarded by [`crate::inertia::inertia`], and its licensed arm additionally cross-checks the
//! exact half-plane count against the licence it claims, refusing on contradiction.
//!
//! # The interface between two media
//!
//! [implemented-exact] [`InterfaceReading`] composes [`crate::junction_law::check_junction`] at
//! the shared face of two consecutive media: tangential agreement, normal jump and source balance
//! at the joint. Its Lean connection is `Transport/JunctionLaw.lean::balanced_iff_divergence` for
//! the discrete half and `HolonicSnellInteraction.lean`'s
//! `tangentialConservation_retainsNormalRemainder` for the retained normal remainder.
//!
//! [definition] [`classify_convergence`] types every apparent convergence of two carriers as
//! exactly one of the 2026-08-24 record's three populations — shared incidence, a receiver
//! caustic with its retained fibre, or a declared constitutive coupling with an off-diagonal
//! response term **and a returned later consequence** — and names the others it also satisfies
//! rather than hiding them.
//!
//! # Nothing here is approximate
//!
//! [implemented-exact] Every carried and deciding value is an exact `Rat`. No `f32`, `f64` or
//! float literal appears on any path. Every declared size is bounded before the work it sizes,
//! against the ceilings below. Every value enters through its constructor; no struct in this
//! module has a public field, and none derives `Deserialize`, so no wire can bypass a check.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde::Serialize;
use thiserror::Error;

use crate::causal_chord::{
    ChordRefusal, HalfPlaneCount, Linearization, PoleAtlas, PoleReading, TransferFunction,
    half_plane_count, pole_atlas, rate_form, transfer_function,
};
use crate::edit_rigidity::{EditRigidityRefusal, ExactMetric};
use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::hodge_receiver::HodgeOperator;
use crate::inertia::{Inertia, InertiaError, SymmetricForm, inertia};
use crate::junction_law::{
    Interface, JointUnits, JunctionField, JunctionRefusal, JunctionVerdict, check_junction,
};

pub const HOLONIC_INTERACTION_SCHEMA: &str = "holonic-engine.holonic-interaction.v1";

// ===============================================================================================
// 0. ceilings and refusals
// ===============================================================================================

/// **The ceiling on one medium's declared configuration dimension.**
///
/// [definition] Every face map, storage form and generator below is sized by it, and the product
/// is checked against [`DECLARED_ASSEMBLY_CEILING`] *before* any allocation.
pub const DECLARED_MODE_CEILING: usize = 1024;

/// The ceiling on the number of contact faces one medium or one interaction declares.
pub const DECLARED_FACE_CEILING: usize = 4096;

/// The ceiling on the number of media a single chain declares.
pub const DECLARED_MEDIUM_CEILING: usize = 256;

/// The ceiling on the arithmetic work of one contact assembly, `faces × slip × dimension²`.
pub const DECLARED_ASSEMBLY_CEILING: usize = 1 << 26;

/// Every way this module declines to answer. A refusal is a return; nothing here panics.
#[derive(Debug, Error)]
pub enum InteractionRefusal {
    /// A declared size exceeded its ceiling. Nothing was allocated.
    #[error("{what} declares {declared}, above the ceiling {ceiling}")]
    DeclarationAboveCeiling {
        what: &'static str,
        declared: usize,
        ceiling: usize,
    },
    /// A product of declared sizes overflowed before it could be compared with its ceiling.
    #[error("the declared work for {what} overflows")]
    WorkOverflows { what: &'static str },
    /// A declared population was empty where a reading over nothing would pass vacuously.
    #[error("{what} is empty, and a reading over nothing is not a reading")]
    EmptyDeclaration { what: &'static str },
    /// Two declared shapes disagree.
    #[error("{what}: declared {declared}, found {found}")]
    WidthDisagrees {
        what: &'static str,
        declared: usize,
        found: usize,
    },
    /// A face's constitutive response is not positive semidefinite in the declared pairing.
    #[error(
        "the contact face `{face}` declares a response of signature ({positive}, {negative}) with \
         nullity {nullity}; a dissipative response must be positive semidefinite"
    )]
    ResponseNotPositiveSemidefinite {
        face: String,
        positive: usize,
        negative: usize,
        nullity: usize,
    },
    /// A face weight, a clock duration or another declared measure is not strictly positive.
    #[error("{what} declares `{value}`, which is not strictly positive")]
    NotStrictlyPositive { what: &'static str, value: String },
    /// A declared structure matrix is not skew-symmetric.
    #[error("the structure matrix `{structure}` is not skew at ({row}, {column})")]
    StructureNotSkew {
        structure: String,
        row: usize,
        column: usize,
    },
    /// The assembled contact form failed its own positive-semidefiniteness certificate. This is a
    /// cross-check on the exact arithmetic and it can fail.
    #[error(
        "the assembled contact form `{lineage}` reads signature ({positive}, {negative}); the \
         assembly of positive semidefinite faces must be positive semidefinite"
    )]
    AssemblyNotPositiveSemidefinite {
        lineage: String,
        positive: usize,
        negative: usize,
    },
    /// A carrier index names a medium the interaction does not carry, or the perspective's own
    /// block when the perspective declares none.
    #[error("the carrier {carrier} is not a block of this interaction")]
    CarrierAbsent { carrier: String },
    /// An embedding named the same joint coordinate twice, or a coordinate outside the chart.
    #[error("the embedding names the joint coordinate {coordinate} of a chart of extent {extent}")]
    EmbeddingCoordinate { coordinate: usize, extent: usize },
    /// A licence disagreed with the exact half-plane count: eigenvalues in the open right half
    /// plane beside a negative semidefinite rate form, or on the axis beside a negative definite
    /// one. The licence and the measurement cannot both be right, and neither is discarded.
    #[error(
        "the storage form is positive definite and the rate form forbids them, yet {right} \
         eigenvalues sit where the exact half-plane count found them"
    )]
    SpectralContradiction { right: usize },
    /// The exact linear carrier refused.
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    /// The signature owner refused.
    #[error(transparent)]
    Signature(#[from] InertiaError),
    /// The causal chord owner refused.
    #[error(transparent)]
    Chord(#[from] ChordRefusal),
    /// The edit-rigidity owner refused.
    #[error(transparent)]
    EditRigidity(#[from] EditRigidityRefusal),
    /// The junction owner refused.
    #[error(transparent)]
    Junction(#[from] JunctionRefusal),
}

fn bounded(
    what: &'static str,
    declared: usize,
    ceiling: usize,
) -> Result<(), InteractionRefusal> {
    if declared > ceiling {
        return Err(InteractionRefusal::DeclarationAboveCeiling {
            what,
            declared,
            ceiling,
        });
    }
    Ok(())
}

fn bounded_product(
    what: &'static str,
    factors: &[usize],
    ceiling: usize,
) -> Result<usize, InteractionRefusal> {
    let mut work = 1usize;
    for factor in factors {
        work = work
            .checked_mul(*factor)
            .ok_or(InteractionRefusal::WorkOverflows { what })?;
    }
    bounded(what, work, ceiling)?;
    Ok(work)
}

/// An exact rational from an integer. The only numeric literal path in this module.
fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

/// The dense rows of a symmetric form, as a matrix.
fn form_matrix(form: &SymmetricForm) -> Result<ExactRatMatrix, InteractionRefusal> {
    let extent = form.extent();
    let rows: Vec<Vec<Rat>> = (0..extent)
        .map(|row| {
            (0..extent)
                .map(|column| form.at(row, column).clone())
                .collect()
        })
        .collect();
    Ok(ExactRatMatrix::shaped(extent, extent, rows)?)
}

/// A square matrix read as a symmetric form. **Asymmetry is a refusal, never a symmetrization.**
fn matrix_form(matrix: &ExactRatMatrix) -> Result<SymmetricForm, InteractionRefusal> {
    Ok(SymmetricForm::from_rows(matrix.to_rows())?)
}

/// `⟨left, M right⟩`, exact.
fn pairing(
    matrix: &ExactRatMatrix,
    left: &[Rat],
    right: &[Rat],
) -> Result<Rat, InteractionRefusal> {
    let image = matrix.apply(right)?;
    if left.len() != image.len() {
        return Err(InteractionRefusal::WidthDisagrees {
            what: "a pairing against an assembled form",
            declared: image.len(),
            found: left.len(),
        });
    }
    Ok(left
        .iter()
        .zip(&image)
        .fold(Rat::zero(), |sum, (one, other)| sum + one * other))
}

// ===============================================================================================
// 1. the declared clock
// ===============================================================================================

/// **A declared duration with its unit tag.**
///
/// [definition] `⟨δq, M δq⟩` is a number of unknown dimension; `⟨δq, M δq⟩ / h` is an energy only
/// once `h` is named and its unit is carried. There is no default clock: a caller who wants one
/// declares it, and a non-positive duration is refused by name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Clock {
    lineage: String,
    duration: Rat,
    unit: String,
}

impl Clock {
    /// Declare a clock. The duration must be strictly positive; the unit tag is the caller's
    /// declaration and is carried through unread.
    pub fn declared(
        lineage: impl Into<String>,
        duration: Rat,
        unit: impl Into<String>,
    ) -> Result<Self, InteractionRefusal> {
        if !duration.is_positive() {
            return Err(InteractionRefusal::NotStrictlyPositive {
                what: "a declared clock duration",
                value: duration.to_string(),
            });
        }
        Ok(Self {
            lineage: lineage.into(),
            duration,
            unit: unit.into(),
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn duration(&self) -> &Rat {
        &self.duration
    }

    /// The declared unit of the energy this clock produces. Carried, never parsed into a number.
    pub fn unit(&self) -> &str {
        &self.unit
    }
}

// ===============================================================================================
// 2. the contact face
// ===============================================================================================

/// **A contact face: where a medium exchanges.**
///
/// [definition] `s_f = J_f v` is the relative slip of the motion `v` at this face, and
/// `t_f = −D_f s_f` is the constitutive traction opposing it. `D_f` is checked positive
/// semidefinite in the declared pairing through [`crate::inertia::inertia`]; the weight `w_f` is
/// the face's declared area or measure and must be strictly positive.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ContactFace {
    lineage: String,
    slip: ExactRatMatrix,
    response: SymmetricForm,
    weight: Rat,
    response_inertia: Inertia,
}

impl ContactFace {
    /// Declare a contact face, checking the response's signature and the weight's sign.
    pub fn declared(
        lineage: impl Into<String>,
        slip: ExactRatMatrix,
        response: SymmetricForm,
        weight: Rat,
    ) -> Result<Self, InteractionRefusal> {
        let lineage = lineage.into();
        let slip_extent = slip.rows();
        let dimension = slip.columns();
        if slip_extent == 0 {
            return Err(InteractionRefusal::EmptyDeclaration {
                what: "a contact face's slip map",
            });
        }
        if dimension == 0 {
            return Err(InteractionRefusal::EmptyDeclaration {
                what: "a contact face's configuration chart",
            });
        }
        bounded("a contact face's slip extent", slip_extent, DECLARED_MODE_CEILING)?;
        bounded(
            "a contact face's configuration dimension",
            dimension,
            DECLARED_MODE_CEILING,
        )?;
        if response.extent() != slip_extent {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a face response against its slip map",
                declared: slip_extent,
                found: response.extent(),
            });
        }
        if !weight.is_positive() {
            return Err(InteractionRefusal::NotStrictlyPositive {
                what: "a contact face weight",
                value: weight.to_string(),
            });
        }
        // The dissipative half of the constitutive law is a *claim about material*, so it is read
        // through the signature owner and never assumed from the shape of the expression.
        let response_inertia = inertia(&response);
        if !response_inertia.is_positive_semidefinite() {
            return Err(InteractionRefusal::ResponseNotPositiveSemidefinite {
                face: lineage,
                positive: response_inertia.positive,
                negative: response_inertia.negative,
                nullity: response_inertia.zero,
            });
        }
        Ok(Self {
            lineage,
            slip,
            response,
            weight,
            response_inertia,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// `J_f`, of shape `slip_extent × dimension`.
    pub fn slip(&self) -> &ExactRatMatrix {
        &self.slip
    }

    /// `D_f`, the constitutive response.
    pub fn response(&self) -> &SymmetricForm {
        &self.response
    }

    /// `w_f`, the declared face measure.
    pub fn weight(&self) -> &Rat {
        &self.weight
    }

    /// The signature that certified the response. Its nullity is the face's own null slip
    /// directions, which is why a semidefinite face is not a *dissipative* face.
    pub fn response_inertia(&self) -> &Inertia {
        &self.response_inertia
    }

    /// The configuration dimension this face is declared over.
    pub fn dimension(&self) -> usize {
        self.slip.columns()
    }

    /// How many slip coordinates the face carries.
    pub fn slip_extent(&self) -> usize {
        self.slip.rows()
    }

    /// **Whether this face is dissipative rather than merely non-generating.** A positive definite
    /// response reads strictly positive power on every nonzero slip; a semidefinite one has its
    /// own null directions and contributes nothing on them.
    pub fn is_dissipative(&self) -> bool {
        self.response_inertia.is_positive_definite()
    }

    /// `s_f = J_f v`.
    pub fn slip_of(&self, motion: &[Rat]) -> Result<Vec<Rat>, InteractionRefusal> {
        if motion.len() != self.dimension() {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a motion against a contact face",
                declared: self.dimension(),
                found: motion.len(),
            });
        }
        Ok(self.slip.apply(motion)?)
    }

    /// `t_f = −D_f s_f`, the constitutive traction at this face.
    pub fn traction_of(&self, motion: &[Rat]) -> Result<Vec<Rat>, InteractionRefusal> {
        let slip = self.slip_of(motion)?;
        let response = form_matrix(&self.response)?;
        Ok(response
            .apply(&slip)?
            .into_iter()
            .map(|entry| -entry)
            .collect())
    }

    /// `w_f ⟨s_f, D_f s_f⟩`, this face's own contribution to the dissipated power.
    pub fn power(&self, motion: &[Rat]) -> Result<Rat, InteractionRefusal> {
        let slip = self.slip_of(motion)?;
        let response = form_matrix(&self.response)?;
        Ok(&self.weight * pairing(&response, &slip, &slip)?)
    }

    /// `w_f J_fᵀ D_f J_f`, this face's contribution to the configuration-space dissipation form.
    pub fn face_form(&self) -> Result<ExactRatMatrix, InteractionRefusal> {
        let response = form_matrix(&self.response)?;
        let pulled = self
            .slip
            .transpose()?
            .multiply(&response)?
            .multiply(&self.slip)?;
        Ok(pulled.scaled(&self.weight))
    }

    /// **The same face, re-declared on a wider chart.**
    ///
    /// [definition] Column `i` of this face's slip map is placed at joint coordinate
    /// `coordinates[i]`. An interface face declared on the pair of blocks it joins is embedded
    /// into the joint chart this way, and the embedding goes back through
    /// [`ContactFace::declared`] so the response and the weight are checked again.
    pub fn embedded(
        &self,
        extent: usize,
        coordinates: &[usize],
    ) -> Result<Self, InteractionRefusal> {
        if coordinates.len() != self.dimension() {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "an embedding against the face it embeds",
                declared: self.dimension(),
                found: coordinates.len(),
            });
        }
        bounded("an embedding chart extent", extent, DECLARED_MODE_CEILING)?;
        let mut seen = BTreeSet::new();
        for coordinate in coordinates {
            if *coordinate >= extent || !seen.insert(*coordinate) {
                return Err(InteractionRefusal::EmbeddingCoordinate {
                    coordinate: *coordinate,
                    extent,
                });
            }
        }
        bounded_product(
            "an embedded slip map",
            &[self.slip_extent(), extent],
            DECLARED_ASSEMBLY_CEILING,
        )?;
        let mut rows = vec![vec![Rat::zero(); extent]; self.slip_extent()];
        for (at, coordinate) in coordinates.iter().enumerate() {
            for (row, entries) in rows.iter_mut().enumerate() {
                entries[*coordinate] = self.slip.get(row, at)?.clone();
            }
        }
        Self::declared(
            format!("{}|embedded@{extent}", self.lineage),
            ExactRatMatrix::shaped(self.slip_extent(), extent, rows)?,
            self.response.clone(),
            self.weight.clone(),
        )
    }
}

// ===============================================================================================
// 3. the assembled contact dissipation
// ===============================================================================================

/// **`M_contact = Σ_f w_f J_fᵀ D_f J_f`, with its certified signature.**
///
/// [proved-derived; implemented-exact] This is the carrier plan's derived configuration-space
/// dissipation form. Its positive semidefiniteness is the Lean owner's `contactForm_nonneg` and
/// is **certified here** through [`crate::inertia::inertia`] rather than inherited from the
/// faces' own certificates: the assembly is where exact arithmetic could go wrong, so that is
/// where it is checked.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ContactDissipation {
    lineage: String,
    dimension: usize,
    form: SymmetricForm,
    signature: Inertia,
    faces: Vec<ContactFace>,
}

impl ContactDissipation {
    /// Assemble the dissipation form from a face population declared over one chart.
    pub fn assemble(
        lineage: impl Into<String>,
        dimension: usize,
        faces: Vec<ContactFace>,
    ) -> Result<Self, InteractionRefusal> {
        let lineage = lineage.into();
        if dimension == 0 {
            return Err(InteractionRefusal::EmptyDeclaration {
                what: "a contact chart",
            });
        }
        bounded("a contact chart dimension", dimension, DECLARED_MODE_CEILING)?;
        bounded("a contact face population", faces.len(), DECLARED_FACE_CEILING)?;
        let widest = faces.iter().map(ContactFace::slip_extent).max().unwrap_or(1);
        // The triple product below is `faces × slip × dimension²`; the whole of it is bounded
        // before the first entry is formed.
        bounded_product(
            "a contact assembly",
            &[faces.len().max(1), widest, dimension, dimension],
            DECLARED_ASSEMBLY_CEILING,
        )?;
        for face in &faces {
            if face.dimension() != dimension {
                return Err(InteractionRefusal::WidthDisagrees {
                    what: "a contact face against the assembly chart",
                    declared: dimension,
                    found: face.dimension(),
                });
            }
        }
        let mut assembled = ExactRatMatrix::zero(dimension, dimension)?;
        for face in &faces {
            assembled = assembled.add(&face.face_form()?)?;
        }
        // `from_rows` refuses an asymmetric matrix, so this conversion *is* the symmetry check on
        // the assembled sum; it is not a cast.
        let form = matrix_form(&assembled)?;
        let signature = inertia(&form);
        if !signature.is_positive_semidefinite() {
            return Err(InteractionRefusal::AssemblyNotPositiveSemidefinite {
                lineage,
                positive: signature.positive,
                negative: signature.negative,
            });
        }
        Ok(Self {
            lineage,
            dimension,
            form,
            signature,
            faces,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// `M_contact` as a symmetric form.
    pub fn form(&self) -> &SymmetricForm {
        &self.form
    }

    /// `M_contact` as a matrix.
    pub fn matrix(&self) -> Result<ExactRatMatrix, InteractionRefusal> {
        form_matrix(&self.form)
    }

    /// The certified signature. Its nullity is the dimension of the zero-dissipation subspace.
    pub fn signature(&self) -> &Inertia {
        &self.signature
    }

    /// The faces it was assembled from, in declaration order.
    pub fn faces(&self) -> &[ContactFace] {
        &self.faces
    }

    /// **`P_diss(v) = ⟨v, M_contact v⟩ ≥ 0`.**
    pub fn power(&self, motion: &[Rat]) -> Result<Rat, InteractionRefusal> {
        if motion.len() != self.dimension {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a motion against the contact form",
                declared: self.dimension,
                found: motion.len(),
            });
        }
        let matrix = self.matrix()?;
        pairing(&matrix, motion, motion)
    }

    /// **The dissipated power face by face, not only its sum.** This is the Lean owner's
    /// `quad_contactForm`; the sum of the returned values is [`ContactDissipation::power`], and
    /// the two are cross-checked by the tests rather than by one calling the other.
    pub fn power_by_face(&self, motion: &[Rat]) -> Result<Vec<(String, Rat)>, InteractionRefusal> {
        self.faces
            .iter()
            .map(|face| Ok((face.lineage().to_owned(), face.power(motion)?)))
            .collect()
    }

    /// A basis of `ker M_contact`, through the exact linear owner.
    pub fn kernel_basis(&self) -> Result<Vec<Vec<Rat>>, InteractionRefusal> {
        Ok(self.matrix()?.kernel_basis()?)
    }

    /// **A basis of the motions that slip on no face at all**, which is the intersection of the
    /// faces' slip kernels. The Lean owner's `contactForm_kernel_iff` says this equals
    /// [`ContactDissipation::kernel_basis`] when every face is dissipative; when some face is
    /// only semidefinite the two can differ, and this owner returns both rather than one.
    pub fn zero_slip_kernel(&self) -> Result<Vec<Vec<Rat>>, InteractionRefusal> {
        let stacked_rows: usize = self
            .faces
            .iter()
            .map(ContactFace::slip_extent)
            .try_fold(0usize, |sum, extent| sum.checked_add(extent))
            .ok_or(InteractionRefusal::WorkOverflows {
                what: "a stacked slip map",
            })?;
        if stacked_rows == 0 {
            // No face at all: every motion slips on no face, so the kernel is the whole chart.
            return Ok(ExactRatMatrix::zero(1, self.dimension)?.kernel_basis()?);
        }
        bounded_product(
            "a stacked slip map",
            &[stacked_rows, self.dimension],
            DECLARED_ASSEMBLY_CEILING,
        )?;
        let mut rows: Vec<Vec<Rat>> = Vec::with_capacity(stacked_rows);
        for face in &self.faces {
            rows.extend(face.slip().to_rows());
        }
        Ok(ExactRatMatrix::shaped(stacked_rows, self.dimension, rows)?.kernel_basis()?)
    }

    /// **Whether every declared face is dissipative**, which is the hypothesis under which the
    /// kernel and the zero-slip kernel are the same subspace.
    pub fn every_face_is_dissipative(&self) -> bool {
        !self.faces.is_empty() && self.faces.iter().all(ContactFace::is_dissipative)
    }

    /// **`⟨δq, M_contact δq⟩ / h`, the clocked edit energy.**
    pub fn clocked_energy(
        &self,
        edit: &[Rat],
        clock: &Clock,
    ) -> Result<ClockedEnergy, InteractionRefusal> {
        let quadratic = self.power(edit)?;
        let energy = &quadratic / clock.duration();
        Ok(ClockedEnergy {
            lineage: format!("{}|{}", self.lineage, clock.lineage()),
            quadratic,
            duration: clock.duration().clone(),
            unit: clock.unit().to_owned(),
            energy,
        })
    }

    /// `M_contact / h` as a symmetric form: the candidate edit metric this clock declares.
    pub fn clocked_form(&self, clock: &Clock) -> Result<SymmetricForm, InteractionRefusal> {
        let scaled = self.matrix()?.scaled(&(integer(1) / clock.duration()));
        matrix_form(&scaled)
    }

    /// **`M_contact / h` as T4's declared edit metric.**
    ///
    /// [definition] This is the composition point with
    /// [`crate::edit_rigidity::rethreading_work`]: the `ExactMetric` that function takes is
    /// exactly this one when the caller means the dissipated energy of a clocked edit, and `W²`
    /// is then [`ContactDissipation::clocked_energy`] of the minimizing compensation.
    /// [`crate::edit_rigidity::ExactMetric::declared`] refuses a degenerate contact form through
    /// its own `LDLᵀ` certificate, so a medium with a zero-slip motion cannot become a metric by
    /// being passed along.
    pub fn clocked_metric(&self, clock: &Clock) -> Result<ExactMetric, InteractionRefusal> {
        let name = format!("{}|clocked@{}", self.lineage, clock.lineage());
        let form = self.clocked_form(clock)?;
        Ok(ExactMetric::declared(name, form_matrix(&form)?)?)
    }
}

/// **A dissipated energy with its clock and its declared unit.**
///
/// [definition] The number alone is not the reading. `quadratic` is `⟨δq, M δq⟩`, `duration` is
/// the declared `h`, `unit` is the tag the clock carried, and `energy` is the quotient. A receipt
/// that quotes `energy` without `duration` and `unit` names no physical quantity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ClockedEnergy {
    lineage: String,
    quadratic: Rat,
    duration: Rat,
    unit: String,
    energy: Rat,
}

impl ClockedEnergy {
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// `⟨δq, M_contact δq⟩`, before the clock.
    pub fn quadratic(&self) -> &Rat {
        &self.quadratic
    }

    /// The declared duration `h`.
    pub fn duration(&self) -> &Rat {
        &self.duration
    }

    /// The declared unit tag, carried and never parsed.
    pub fn unit(&self) -> &str {
        &self.unit
    }

    /// `⟨δq, M_contact δq⟩ / h`.
    pub fn energy(&self) -> &Rat {
        &self.energy
    }
}

// ===============================================================================================
// 4. how this differs from T4's `W²`
// ===============================================================================================

/// **What a declared edit metric turned out to be.**
///
/// [definition] T4's [`crate::edit_rigidity::rethreading_work`] minimizes `‖δ‖²_M` over a
/// compensating family, and `M` there is a declared [`crate::edit_rigidity::ExactMetric`]: a
/// positive definite Gram matrix with an `LDLᵀ` certificate. This reading answers whether that
/// metric **is** the clocked contact form `M_contact / h`, and the third arm is the reason it is
/// not a boolean: a contact form with a nontrivial zero-slip kernel is not positive definite, so
/// it is not an `ExactMetric` at any clock and the question "does the declared metric equal it"
/// has no yes-or-no answer.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum EditMetricReading {
    /// The declared metric's Gram matrix is exactly `M_contact / h`. T4's `W²` at this metric
    /// **is** the clocked contact energy of this medium for this clock.
    ClockedContactMetric {
        /// The metric's declared name.
        metric: String,
        /// The clock's declared name.
        clock: String,
        /// The clock's declared duration.
        duration: Rat,
    },
    /// `M_contact / h` is positive definite but is not the declared metric. The complete residual
    /// `G_metric − M_contact/h` is returned, with every coordinate at which it is nonzero.
    /// T4's `W²` here is an authored edit metric's squared norm and is not this energy.
    AuthoredEditMetric {
        metric: String,
        clock: String,
        residual: SymmetricForm,
        offending: Vec<(usize, usize)>,
    },
    /// `M_contact` is degenerate — some motion slips on no dissipative face — so it is not a
    /// metric at any clock. The zero-dissipation kernel is returned, and no comparison is made.
    ContactFormIsDegenerate {
        metric: String,
        nullity: usize,
        kernel: Vec<Vec<Rat>>,
    },
}

impl EditMetricReading {
    /// Whether this reading is the one that licenses calling `W²` a dissipated energy.
    pub fn is_clocked_contact_metric(&self) -> bool {
        matches!(self, Self::ClockedContactMetric { .. })
    }
}

/// **The comparison.** Returns a typed reading, never a boolean.
pub fn compare_edit_metric(
    dissipation: &ContactDissipation,
    clock: &Clock,
    metric: &ExactMetric,
) -> Result<EditMetricReading, InteractionRefusal> {
    if metric.extent() != dissipation.dimension() {
        return Err(InteractionRefusal::WidthDisagrees {
            what: "a declared edit metric against the contact chart",
            declared: dissipation.dimension(),
            found: metric.extent(),
        });
    }
    if dissipation.signature().is_degenerate() {
        return Ok(EditMetricReading::ContactFormIsDegenerate {
            metric: metric.name().to_owned(),
            nullity: dissipation.signature().zero,
            kernel: dissipation.kernel_basis()?,
        });
    }
    let clocked = dissipation.clocked_form(clock)?;
    let extent = clocked.extent();
    let mut offending = Vec::new();
    let mut residual_rows = vec![vec![Rat::zero(); extent]; extent];
    for row in 0..extent {
        for column in 0..extent {
            let difference = metric.gram().get(row, column)?.clone() - clocked.at(row, column);
            if !difference.is_zero() {
                offending.push((row, column));
            }
            residual_rows[row][column] = difference;
        }
    }
    if offending.is_empty() {
        return Ok(EditMetricReading::ClockedContactMetric {
            metric: metric.name().to_owned(),
            clock: clock.lineage().to_owned(),
            duration: clock.duration().clone(),
        });
    }
    Ok(EditMetricReading::AuthoredEditMetric {
        metric: metric.name().to_owned(),
        clock: clock.lineage().to_owned(),
        residual: SymmetricForm::from_rows(residual_rows)?,
        offending,
    })
}

// ===============================================================================================
// 5. the medium
// ===============================================================================================

/// **A medium: a standing `H_int` with its constitutive law and its contact faces.**
///
/// [definition] The storage form `G` is symmetric and **may be indefinite** — a Hodge-shaped or
/// Lorentzian medium is exactly the case that matters — so its signature is read and carried, and
/// nothing in this module treats it as definite without saying so. The structure `Ω` is checked
/// skew. The faces are the medium's own, declared over its own chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Medium {
    lineage: String,
    dimension: usize,
    storage: SymmetricForm,
    storage_inertia: Inertia,
    structure: ExactRatMatrix,
    faces: Vec<ContactFace>,
}

impl Medium {
    /// Declare a medium, checking every shape against every other.
    pub fn declared(
        lineage: impl Into<String>,
        storage: SymmetricForm,
        structure: ExactRatMatrix,
        faces: Vec<ContactFace>,
    ) -> Result<Self, InteractionRefusal> {
        let lineage = lineage.into();
        let dimension = storage.extent();
        if dimension == 0 {
            return Err(InteractionRefusal::EmptyDeclaration {
                what: "a medium's configuration chart",
            });
        }
        bounded(
            "a medium's configuration dimension",
            dimension,
            DECLARED_MODE_CEILING,
        )?;
        bounded("a medium's face population", faces.len(), DECLARED_FACE_CEILING)?;
        if structure.rows() != dimension || structure.columns() != dimension {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a medium's structure matrix against its storage form",
                declared: dimension,
                found: structure.rows().max(structure.columns()),
            });
        }
        for row in 0..dimension {
            for column in 0..dimension {
                let entry = structure.get(row, column)?;
                let mirrored = structure.get(column, row)?;
                if *entry != -mirrored {
                    return Err(InteractionRefusal::StructureNotSkew {
                        structure: lineage,
                        row,
                        column,
                    });
                }
            }
        }
        for face in &faces {
            if face.dimension() != dimension {
                return Err(InteractionRefusal::WidthDisagrees {
                    what: "a contact face against its medium",
                    declared: dimension,
                    found: face.dimension(),
                });
            }
        }
        let storage_inertia = inertia(&storage);
        Ok(Self {
            lineage,
            dimension,
            storage,
            storage_inertia,
            structure,
            faces,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// `G`, the standing constitutive storage form.
    pub fn storage(&self) -> &SymmetricForm {
        &self.storage
    }

    /// **The storage form's signature, read and never assumed.** An indefinite reading is a
    /// lawful medium; it is only a licence for a spectral claim that it withholds.
    pub fn storage_inertia(&self) -> &Inertia {
        &self.storage_inertia
    }

    /// `Ω`, the checked-skew structure.
    pub fn structure(&self) -> &ExactRatMatrix {
        &self.structure
    }

    pub fn faces(&self) -> &[ContactFace] {
        &self.faces
    }

    /// `M_contact` for this medium alone.
    pub fn contact_dissipation(&self) -> Result<ContactDissipation, InteractionRefusal> {
        ContactDissipation::assemble(
            format!("{}|contact", self.lineage),
            self.dimension,
            self.faces.clone(),
        )
    }

    /// **`A = (Ω − M_contact) G`, the port-Hamiltonian generator of this medium alone.**
    pub fn generator(&self) -> Result<ExactRatMatrix, InteractionRefusal> {
        let dissipation = self.contact_dissipation()?;
        port_generator(&self.structure, &dissipation.matrix()?, &form_matrix(&self.storage)?)
    }
}

/// `A = (Ω − M) G`. The one place the port-Hamiltonian form is written.
fn port_generator(
    structure: &ExactRatMatrix,
    dissipation: &ExactRatMatrix,
    storage: &ExactRatMatrix,
) -> Result<ExactRatMatrix, InteractionRefusal> {
    Ok(structure.subtract(dissipation)?.multiply(storage)?)
}

// ===============================================================================================
// 6. the source, the perspective and the participating receiver
// ===============================================================================================

/// Which block of the joint chart a declaration lives on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Carrier {
    /// The `k`th declared medium.
    Medium(usize),
    /// The perspective's own coordinates, present only when the perspective participates.
    Perspective,
}

impl Carrier {
    fn name(&self) -> String {
        match self {
            Self::Medium(at) => format!("medium[{at}]"),
            Self::Perspective => "perspective".to_owned(),
        }
    }
}

/// **`|source⟩`: an object emanating current, with its incidence on one medium.**
///
/// [definition] The excitation map `B` of the joint linearization is this incidence embedded into
/// the joint chart. The port names are declarations checked against the matrix shape, never
/// trusted: they become the source names [`crate::causal_chord::Linearization`] carries.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceCurrent {
    lineage: String,
    carrier: Carrier,
    incidence: ExactRatMatrix,
    ports: Vec<String>,
}

impl SourceCurrent {
    /// Declare the source. `incidence` has one row per coordinate of the carrier it excites and
    /// one column per declared port.
    pub fn declared(
        lineage: impl Into<String>,
        carrier: Carrier,
        incidence: ExactRatMatrix,
        ports: Vec<String>,
    ) -> Result<Self, InteractionRefusal> {
        if incidence.columns() == 0 || ports.is_empty() {
            return Err(InteractionRefusal::EmptyDeclaration {
                what: "a source's port population",
            });
        }
        bounded("a source's port population", ports.len(), DECLARED_MODE_CEILING)?;
        if ports.len() != incidence.columns() {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a source's port names against its incidence",
                declared: ports.len(),
                found: incidence.columns(),
            });
        }
        Ok(Self {
            lineage: lineage.into(),
            carrier,
            incidence,
            ports,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn carrier(&self) -> Carrier {
        self.carrier
    }

    pub fn incidence(&self) -> &ExactRatMatrix {
        &self.incidence
    }

    pub fn ports(&self) -> &[String] {
        &self.ports
    }
}

/// **The perspective's own body: its coordinates, storage and structure.**
///
/// [definition] A *participating* receiver is one whose coordinates join the state. It then has
/// its own storage form and its own skew structure, exactly as a medium does, and the interaction
/// with what it receives is a declared [`Coupling`] — an off-diagonal response term — rather than
/// an unexplained passive screen.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiverBody {
    lineage: String,
    dimension: usize,
    storage: SymmetricForm,
    storage_inertia: Inertia,
    structure: ExactRatMatrix,
}

impl ReceiverBody {
    /// Declare the receiver's own body. The structure is checked skew, as a medium's is.
    pub fn declared(
        lineage: impl Into<String>,
        storage: SymmetricForm,
        structure: ExactRatMatrix,
    ) -> Result<Self, InteractionRefusal> {
        let medium = Medium::declared(lineage, storage, structure, Vec::new())?;
        Ok(Self {
            lineage: medium.lineage().to_owned(),
            dimension: medium.dimension(),
            storage: medium.storage().clone(),
            storage_inertia: *medium.storage_inertia(),
            structure: medium.structure().clone(),
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn dimension(&self) -> usize {
        self.dimension
    }

    pub fn storage(&self) -> &SymmetricForm {
        &self.storage
    }

    pub fn storage_inertia(&self) -> &Inertia {
        &self.storage_inertia
    }

    pub fn structure(&self) -> &ExactRatMatrix {
        &self.structure
    }
}

/// **`⟨perspective|`: the receiver with its own aperture.**
///
/// [definition] The aperture is the receiver differential `C_R`, declared over one carrier block.
/// When the perspective carries a [`ReceiverBody`] the aperture is declared over its **own**
/// coordinates and the perspective participates in the joint state; what it then reads of the
/// media is whatever the declared couplings carry into its block, which is the point.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Perspective {
    lineage: String,
    chart: ApertureChart,
    aperture: ExactRatMatrix,
    ports: Vec<String>,
    body: Option<ReceiverBody>,
}

/// **Which chart a perspective's aperture is declared over.**
///
/// [definition] An aperture that reads one block is the common case and its embedding into the
/// joint chart is zero elsewhere. An aperture that reads the **whole** joint chart is the case a
/// receiver caustic needs: two carriers can only project to the same face of a receiver that sees
/// them both, and a single-block aperture cannot express that.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ApertureChart {
    /// One block of the joint chart.
    Block(Carrier),
    /// The whole joint chart, in declaration order.
    Joint,
}

impl Perspective {
    /// Declare a perspective that does not participate: it reads a medium and has no coordinates.
    pub fn standing(
        lineage: impl Into<String>,
        carrier: Carrier,
        aperture: ExactRatMatrix,
        ports: Vec<String>,
    ) -> Result<Self, InteractionRefusal> {
        Self::found(lineage, ApertureChart::Block(carrier), aperture, ports, None)
    }

    /// Declare a perspective whose aperture reads the whole joint chart. Its column count is
    /// checked against the joint dimension by [`HolonicInteraction::declared`], which is the only
    /// place that dimension is known.
    pub fn over_joint(
        lineage: impl Into<String>,
        aperture: ExactRatMatrix,
        ports: Vec<String>,
    ) -> Result<Self, InteractionRefusal> {
        Self::found(lineage, ApertureChart::Joint, aperture, ports, None)
    }

    /// Declare a participating perspective: its own body joins the state and its aperture is
    /// declared over its own coordinates.
    pub fn participating(
        lineage: impl Into<String>,
        aperture: ExactRatMatrix,
        ports: Vec<String>,
        body: ReceiverBody,
    ) -> Result<Self, InteractionRefusal> {
        if aperture.columns() != body.dimension() {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a participating aperture against the receiver's own chart",
                declared: body.dimension(),
                found: aperture.columns(),
            });
        }
        Self::found(
            lineage,
            ApertureChart::Block(Carrier::Perspective),
            aperture,
            ports,
            Some(body),
        )
    }

    fn found(
        lineage: impl Into<String>,
        chart: ApertureChart,
        aperture: ExactRatMatrix,
        ports: Vec<String>,
        body: Option<ReceiverBody>,
    ) -> Result<Self, InteractionRefusal> {
        if aperture.rows() == 0 || ports.is_empty() {
            return Err(InteractionRefusal::EmptyDeclaration {
                what: "a perspective's port population",
            });
        }
        bounded(
            "a perspective's port population",
            ports.len(),
            DECLARED_MODE_CEILING,
        )?;
        if ports.len() != aperture.rows() {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a perspective's port names against its aperture",
                declared: ports.len(),
                found: aperture.rows(),
            });
        }
        Ok(Self {
            lineage: lineage.into(),
            chart,
            aperture,
            ports,
            body,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// Which chart the aperture is declared over.
    pub fn chart(&self) -> ApertureChart {
        self.chart
    }

    /// The single block this aperture reads, when it reads one.
    pub fn carrier(&self) -> Option<Carrier> {
        match self.chart {
            ApertureChart::Block(carrier) => Some(carrier),
            ApertureChart::Joint => None,
        }
    }

    /// `C_R`, the receiver differential over its declared chart.
    pub fn aperture(&self) -> &ExactRatMatrix {
        &self.aperture
    }

    pub fn ports(&self) -> &[String] {
        &self.ports
    }

    /// The receiver's own body, when it participates.
    pub fn body(&self) -> Option<&ReceiverBody> {
        self.body.as_ref()
    }

    /// Whether the receiver's own coordinates join the state.
    pub fn participates(&self) -> bool {
        self.body.is_some()
    }
}

// ===============================================================================================
// 7. couplings, contacts and the dynamic `H_pert`
// ===============================================================================================

/// **A declared constitutive coupling: the off-diagonal response term.**
///
/// [definition] The 2026-08-24 record's third population of apparent convergence. The block `K`
/// is placed in the joint skew structure as `Ω[to, from] = K` and `Ω[from, to] = −Kᵀ`, which is
/// the port-Hamiltonian interconnection: it transports without dissipating, and it is what makes
/// a later consequence appear in a carrier that is not in contact with the one that moved.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Coupling {
    lineage: String,
    from: Carrier,
    to: Carrier,
    block: ExactRatMatrix,
}

impl Coupling {
    /// Declare the coupling. Its shape is checked against the two blocks by
    /// [`HolonicInteraction::declared`], which is the only place both extents are known.
    pub fn declared(
        lineage: impl Into<String>,
        from: Carrier,
        to: Carrier,
        block: ExactRatMatrix,
    ) -> Result<Self, InteractionRefusal> {
        if block.rows() == 0 || block.columns() == 0 {
            return Err(InteractionRefusal::EmptyDeclaration {
                what: "a coupling block",
            });
        }
        if from == to {
            return Err(InteractionRefusal::CarrierAbsent {
                carrier: format!("{} coupled to itself", from.name()),
            });
        }
        Ok(Self {
            lineage: lineage.into(),
            from,
            to,
            block,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn from(&self) -> Carrier {
        self.from
    }

    pub fn to(&self) -> Carrier {
        self.to
    }

    pub fn block(&self) -> &ExactRatMatrix {
        &self.block
    }

    /// Whether the declared block carries anything at all. A zero block is a declaration of no
    /// coupling and is not the third population.
    pub fn is_active(&self) -> bool {
        self.block.entries().iter().any(|entry| !entry.is_zero())
    }
}

/// **A contact between two carriers: the shared face of consecutive media.**
///
/// [definition] The face's slip map is declared over the concatenated chart
/// `(left coordinates, right coordinates)` and is embedded into the joint chart by
/// [`HolonicInteraction::joint_faces`]. This is where the exchange between two media happens, and
/// it is the first of the record's three populations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MediumContact {
    lineage: String,
    left: Carrier,
    right: Carrier,
    face: ContactFace,
}

impl MediumContact {
    /// Declare the contact. The face's chart must be the two blocks' concatenation, which
    /// [`HolonicInteraction::declared`] checks.
    pub fn declared(
        lineage: impl Into<String>,
        left: Carrier,
        right: Carrier,
        face: ContactFace,
    ) -> Result<Self, InteractionRefusal> {
        if left == right {
            return Err(InteractionRefusal::CarrierAbsent {
                carrier: format!("{} in contact with itself", left.name()),
            });
        }
        Ok(Self {
            lineage: lineage.into(),
            left,
            right,
            face,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn left(&self) -> Carrier {
        self.left
    }

    pub fn right(&self) -> Carrier {
        self.right
    }

    pub fn face(&self) -> &ContactFace {
        &self.face
    }

    /// Whether this contact joins exactly the two named carriers, in either order.
    pub fn joins(&self, one: Carrier, other: Carrier) -> bool {
        (self.left == one && self.right == other) || (self.left == other && self.right == one)
    }
}

/// **`H_pert`: the dynamic modulating field, as an admitted change of declared data.**
///
/// [definition] The perturbation is not a new kind of object. It is a replacement of a medium's
/// constitutive data or of a face map, and every replacement value enters through the same
/// checked constructor its standing counterpart did. [`HolonicInteraction::modulated`] applies it
/// by re-running [`HolonicInteraction::declared`], so a perturbation cannot install a value the
/// standing unit would have refused.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum Perturbation {
    /// Replace a medium's storage form `G`.
    Storage {
        medium: usize,
        storage: SymmetricForm,
    },
    /// Replace a medium's skew structure `Ω`.
    Structure {
        medium: usize,
        structure: ExactRatMatrix,
    },
    /// Replace one of a medium's own contact faces.
    Face {
        medium: usize,
        face: usize,
        replacement: ContactFace,
    },
    /// Replace the face of one declared interface contact.
    Contact {
        contact: usize,
        replacement: ContactFace,
    },
}

// ===============================================================================================
// 8. the unit
// ===============================================================================================

/// **The Holonic Interaction: `|source⟩`, an ordered chain of media, `H_pert`, `⟨perspective|`.**
///
/// [definition] The joint chart is the media's charts in declaration order, followed by the
/// perspective's own coordinates when it participates. Every declared shape is checked against
/// the joint chart at construction, and the joint dimension is bounded before anything is sized
/// by it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HolonicInteraction {
    schema: String,
    lineage: String,
    source: SourceCurrent,
    media: Vec<Medium>,
    contacts: Vec<MediumContact>,
    couplings: Vec<Coupling>,
    perturbation: Option<Perturbation>,
    perspective: Perspective,
}

impl HolonicInteraction {
    /// Declare the unit, checking every shape against the joint chart.
    #[allow(clippy::too_many_arguments)]
    pub fn declared(
        lineage: impl Into<String>,
        source: SourceCurrent,
        media: Vec<Medium>,
        contacts: Vec<MediumContact>,
        couplings: Vec<Coupling>,
        perturbation: Option<Perturbation>,
        perspective: Perspective,
    ) -> Result<Self, InteractionRefusal> {
        let lineage = lineage.into();
        if media.is_empty() {
            return Err(InteractionRefusal::EmptyDeclaration {
                what: "a chain of media",
            });
        }
        bounded("a chain of media", media.len(), DECLARED_MEDIUM_CEILING)?;
        bounded(
            "an interaction's contact population",
            contacts.len(),
            DECLARED_FACE_CEILING,
        )?;
        bounded(
            "an interaction's coupling population",
            couplings.len(),
            DECLARED_FACE_CEILING,
        )?;
        let mut extent = 0usize;
        for medium in &media {
            extent = extent
                .checked_add(medium.dimension())
                .ok_or(InteractionRefusal::WorkOverflows {
                    what: "a joint chart",
                })?;
        }
        if let Some(body) = perspective.body() {
            extent =
                extent
                    .checked_add(body.dimension())
                    .ok_or(InteractionRefusal::WorkOverflows {
                        what: "a joint chart",
                    })?;
        }
        bounded("a joint chart", extent, DECLARED_MODE_CEILING)?;
        bounded_product(
            "a joint assembly",
            &[extent, extent],
            DECLARED_ASSEMBLY_CEILING,
        )?;

        let declared = Self {
            schema: HOLONIC_INTERACTION_SCHEMA.to_owned(),
            lineage,
            source,
            media,
            contacts,
            couplings,
            perturbation,
            perspective,
        };
        declared.validate()?;
        Ok(declared)
    }

    /// Every cross-shape obligation of the declaration, checked. Called by the constructor and by
    /// [`HolonicInteraction::modulated`]; nothing reaches a reading without passing it.
    fn validate(&self) -> Result<(), InteractionRefusal> {
        let extent = self.joint_dimension();
        let source_extent = self.block_extent(self.source.carrier())?;
        if self.source.incidence().rows() != source_extent {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a source's incidence against the carrier it excites",
                declared: source_extent,
                found: self.source.incidence().rows(),
            });
        }
        let perspective_extent = match self.perspective.chart() {
            ApertureChart::Block(carrier) => self.block_extent(carrier)?,
            ApertureChart::Joint => extent,
        };
        if self.perspective.aperture().columns() != perspective_extent {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a perspective's aperture against the chart it reads",
                declared: perspective_extent,
                found: self.perspective.aperture().columns(),
            });
        }
        for contact in &self.contacts {
            let left = self.block_extent(contact.left())?;
            let right = self.block_extent(contact.right())?;
            let joined = left
                .checked_add(right)
                .ok_or(InteractionRefusal::WorkOverflows {
                    what: "a contact's joined chart",
                })?;
            if contact.face().dimension() != joined {
                return Err(InteractionRefusal::WidthDisagrees {
                    what: "an interface face against the two blocks it joins",
                    declared: joined,
                    found: contact.face().dimension(),
                });
            }
        }
        for coupling in &self.couplings {
            let from = self.block_extent(coupling.from())?;
            let to = self.block_extent(coupling.to())?;
            if coupling.block().rows() != to || coupling.block().columns() != from {
                return Err(InteractionRefusal::WidthDisagrees {
                    what: "a coupling block against the two blocks it joins",
                    declared: to,
                    found: coupling.block().rows(),
                });
            }
        }
        if let Some(perturbation) = &self.perturbation {
            self.validate_perturbation(perturbation)?;
        }
        bounded("a joint chart", extent, DECLARED_MODE_CEILING)?;
        Ok(())
    }

    fn validate_perturbation(
        &self,
        perturbation: &Perturbation,
    ) -> Result<(), InteractionRefusal> {
        match perturbation {
            Perturbation::Storage { medium, storage } => {
                let carried = self.medium_at(*medium)?;
                if storage.extent() != carried.dimension() {
                    return Err(InteractionRefusal::WidthDisagrees {
                        what: "a perturbed storage form against its medium",
                        declared: carried.dimension(),
                        found: storage.extent(),
                    });
                }
            }
            Perturbation::Structure { medium, structure } => {
                let carried = self.medium_at(*medium)?;
                if structure.rows() != carried.dimension()
                    || structure.columns() != carried.dimension()
                {
                    return Err(InteractionRefusal::WidthDisagrees {
                        what: "a perturbed structure against its medium",
                        declared: carried.dimension(),
                        found: structure.rows(),
                    });
                }
            }
            Perturbation::Face {
                medium,
                face,
                replacement,
            } => {
                let carried = self.medium_at(*medium)?;
                if *face >= carried.faces().len() {
                    return Err(InteractionRefusal::CarrierAbsent {
                        carrier: format!("face {face} of {}", carried.lineage()),
                    });
                }
                if replacement.dimension() != carried.dimension() {
                    return Err(InteractionRefusal::WidthDisagrees {
                        what: "a perturbed face against its medium",
                        declared: carried.dimension(),
                        found: replacement.dimension(),
                    });
                }
            }
            Perturbation::Contact {
                contact,
                replacement,
            } => {
                let carried = self.contacts.get(*contact).ok_or_else(|| {
                    InteractionRefusal::CarrierAbsent {
                        carrier: format!("contact {contact}"),
                    }
                })?;
                if replacement.dimension() != carried.face().dimension() {
                    return Err(InteractionRefusal::WidthDisagrees {
                        what: "a perturbed interface face against the contact it replaces",
                        declared: carried.face().dimension(),
                        found: replacement.dimension(),
                    });
                }
            }
        }
        Ok(())
    }

    pub fn schema(&self) -> &str {
        &self.schema
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn source(&self) -> &SourceCurrent {
        &self.source
    }

    pub fn media(&self) -> &[Medium] {
        &self.media
    }

    pub fn contacts(&self) -> &[MediumContact] {
        &self.contacts
    }

    pub fn couplings(&self) -> &[Coupling] {
        &self.couplings
    }

    /// `H_pert`, the admitted change, when one is declared.
    pub fn perturbation(&self) -> Option<&Perturbation> {
        self.perturbation.as_ref()
    }

    pub fn perspective(&self) -> &Perspective {
        &self.perspective
    }

    fn medium_at(&self, at: usize) -> Result<&Medium, InteractionRefusal> {
        self.media
            .get(at)
            .ok_or_else(|| InteractionRefusal::CarrierAbsent {
                carrier: Carrier::Medium(at).name(),
            })
    }

    /// The dimension of one block of the joint chart.
    pub fn block_extent(&self, carrier: Carrier) -> Result<usize, InteractionRefusal> {
        match carrier {
            Carrier::Medium(at) => Ok(self.medium_at(at)?.dimension()),
            Carrier::Perspective => self.perspective.body().map(ReceiverBody::dimension).ok_or(
                InteractionRefusal::CarrierAbsent {
                    carrier: "perspective (which declares no body of its own)".to_owned(),
                },
            ),
        }
    }

    /// Where one block starts in the joint chart.
    pub fn block_offset(&self, carrier: Carrier) -> Result<usize, InteractionRefusal> {
        match carrier {
            Carrier::Medium(at) => {
                if at >= self.media.len() {
                    return Err(InteractionRefusal::CarrierAbsent {
                        carrier: carrier.name(),
                    });
                }
                Ok(self.media[..at].iter().map(Medium::dimension).sum())
            }
            Carrier::Perspective => {
                if self.perspective.body().is_none() {
                    return Err(InteractionRefusal::CarrierAbsent {
                        carrier: "perspective (which declares no body of its own)".to_owned(),
                    });
                }
                Ok(self.media.iter().map(Medium::dimension).sum())
            }
        }
    }

    /// The joint chart's dimension: every medium, then the receiver's own coordinates.
    pub fn joint_dimension(&self) -> usize {
        self.media.iter().map(Medium::dimension).sum::<usize>()
            + self.perspective.body().map_or(0, ReceiverBody::dimension)
    }

    fn block_coordinates(&self, carrier: Carrier) -> Result<Vec<usize>, InteractionRefusal> {
        let offset = self.block_offset(carrier)?;
        let extent = self.block_extent(carrier)?;
        Ok((offset..offset + extent).collect())
    }

    /// **Every contact face of the interaction, embedded into the joint chart.**
    pub fn joint_faces(&self) -> Result<Vec<ContactFace>, InteractionRefusal> {
        let extent = self.joint_dimension();
        let mut faces = Vec::new();
        for (at, medium) in self.media.iter().enumerate() {
            let coordinates = self.block_coordinates(Carrier::Medium(at))?;
            for face in medium.faces() {
                faces.push(face.embedded(extent, &coordinates)?);
            }
        }
        for contact in &self.contacts {
            let mut coordinates = self.block_coordinates(contact.left())?;
            coordinates.extend(self.block_coordinates(contact.right())?);
            faces.push(contact.face().embedded(extent, &coordinates)?);
        }
        bounded(
            "an interaction's joint face population",
            faces.len(),
            DECLARED_FACE_CEILING,
        )?;
        Ok(faces)
    }

    /// `M_contact` over the joint chart.
    pub fn joint_dissipation(&self) -> Result<ContactDissipation, InteractionRefusal> {
        ContactDissipation::assemble(
            format!("{}|joint-contact", self.lineage),
            self.joint_dimension(),
            self.joint_faces()?,
        )
    }

    /// `G` over the joint chart: the media's storage forms in order, then the receiver's own.
    pub fn joint_storage(&self) -> Result<SymmetricForm, InteractionRefusal> {
        let extent = self.joint_dimension();
        let mut rows = vec![vec![Rat::zero(); extent]; extent];
        for (at, medium) in self.media.iter().enumerate() {
            let offset = self.block_offset(Carrier::Medium(at))?;
            for row in 0..medium.dimension() {
                for column in 0..medium.dimension() {
                    rows[offset + row][offset + column] =
                        medium.storage().at(row, column).clone();
                }
            }
        }
        if let Some(body) = self.perspective.body() {
            let offset = self.block_offset(Carrier::Perspective)?;
            for row in 0..body.dimension() {
                for column in 0..body.dimension() {
                    rows[offset + row][offset + column] = body.storage().at(row, column).clone();
                }
            }
        }
        Ok(SymmetricForm::from_rows(rows)?)
    }

    /// `Ω` over the joint chart: the blocks' own structures, plus each declared coupling placed
    /// antisymmetrically so that the assembled matrix is skew by construction — and then checked.
    pub fn joint_structure(&self) -> Result<ExactRatMatrix, InteractionRefusal> {
        let extent = self.joint_dimension();
        let mut rows = vec![vec![Rat::zero(); extent]; extent];
        for (at, medium) in self.media.iter().enumerate() {
            let offset = self.block_offset(Carrier::Medium(at))?;
            for row in 0..medium.dimension() {
                for column in 0..medium.dimension() {
                    rows[offset + row][offset + column] =
                        medium.structure().get(row, column)?.clone();
                }
            }
        }
        if let Some(body) = self.perspective.body() {
            let offset = self.block_offset(Carrier::Perspective)?;
            for row in 0..body.dimension() {
                for column in 0..body.dimension() {
                    rows[offset + row][offset + column] =
                        body.structure().get(row, column)?.clone();
                }
            }
        }
        for coupling in &self.couplings {
            let to = self.block_offset(coupling.to())?;
            let from = self.block_offset(coupling.from())?;
            for row in 0..coupling.block().rows() {
                for column in 0..coupling.block().columns() {
                    let entry = coupling.block().get(row, column)?.clone();
                    rows[to + row][from + column] += &entry;
                    rows[from + column][to + row] -= &entry;
                }
            }
        }
        let assembled = ExactRatMatrix::shaped(extent, extent, rows)?;
        for row in 0..extent {
            for column in 0..extent {
                if *assembled.get(row, column)? != -assembled.get(column, row)?.clone() {
                    return Err(InteractionRefusal::StructureNotSkew {
                        structure: format!("{}|joint", self.lineage),
                        row,
                        column,
                    });
                }
            }
        }
        Ok(assembled)
    }

    /// **`A = (Ω − M_contact) G` over the joint chart.**
    pub fn generator(&self) -> Result<ExactRatMatrix, InteractionRefusal> {
        port_generator(
            &self.joint_structure()?,
            &self.joint_dissipation()?.matrix()?,
            &form_matrix(&self.joint_storage()?)?,
        )
    }

    /// `B` over the joint chart: the source's incidence, zero-padded onto its carrier's block.
    pub fn excitation(&self) -> Result<ExactRatMatrix, InteractionRefusal> {
        let extent = self.joint_dimension();
        let offset = self.block_offset(self.source.carrier())?;
        let ports = self.source.incidence().columns();
        bounded_product("a joint excitation", &[extent, ports], DECLARED_ASSEMBLY_CEILING)?;
        let mut rows = vec![vec![Rat::zero(); ports]; extent];
        for row in 0..self.source.incidence().rows() {
            for column in 0..ports {
                rows[offset + row][column] = self.source.incidence().get(row, column)?.clone();
            }
        }
        Ok(ExactRatMatrix::shaped(extent, ports, rows)?)
    }

    /// `C_R` over the joint chart: the perspective's aperture, zero-padded onto its block.
    pub fn readout(&self) -> Result<ExactRatMatrix, InteractionRefusal> {
        let extent = self.joint_dimension();
        let offset = match self.perspective.chart() {
            ApertureChart::Block(carrier) => self.block_offset(carrier)?,
            // An aperture over the whole joint chart is already the readout; its column count was
            // checked against the joint dimension at declaration.
            ApertureChart::Joint => return Ok(self.perspective.aperture().clone()),
        };
        let ports = self.perspective.aperture().rows();
        bounded_product("a joint readout", &[extent, ports], DECLARED_ASSEMBLY_CEILING)?;
        let mut rows = vec![vec![Rat::zero(); extent]; ports];
        for row in 0..ports {
            for column in 0..self.perspective.aperture().columns() {
                rows[row][offset + column] = self.perspective.aperture().get(row, column)?.clone();
            }
        }
        Ok(ExactRatMatrix::shaped(ports, extent, rows)?)
    }

    /// **The derived linearization, handed to the causal chord owner.**
    ///
    /// `A` is the port-Hamiltonian generator, `B` the source's incidence and `C_R` the
    /// perspective's aperture — all three derived from this unit's declared data and none of them
    /// supplied. [`crate::causal_chord::Linearization::declared`] re-checks every shape.
    pub fn linearization(&self) -> Result<Linearization, InteractionRefusal> {
        Ok(Linearization::declared(
            format!("{}|port-hamiltonian", self.lineage),
            self.generator()?,
            self.excitation()?,
            self.readout()?,
            self.source.ports().to_vec(),
            self.perspective.ports().to_vec(),
        )?)
    }

    /// `C_R (sI − A)^{-1} B`, through the existing owner.
    pub fn transfer(&self) -> Result<TransferFunction, InteractionRefusal> {
        Ok(transfer_function(&self.linearization()?)?)
    }

    /// The pole atlas of the transfer function's denominator, through the existing owner.
    pub fn poles(&self, reading: PoleReading) -> Result<PoleAtlas, InteractionRefusal> {
        let transfer = self.transfer()?;
        Ok(pole_atlas(&transfer.atlas_denominator, reading)?)
    }

    /// **The storage-rate reading: `AᵀG + GA` against `−2 G M G`.**
    pub fn storage_rate(&self) -> Result<StorageRateReading, InteractionRefusal> {
        let storage = self.joint_storage()?;
        let storage_matrix = form_matrix(&storage)?;
        let dissipation = self.joint_dissipation()?;
        let dissipation_matrix = dissipation.matrix()?;
        let generator = port_generator(
            &self.joint_structure()?,
            &dissipation_matrix,
            &storage_matrix,
        )?;
        // The rate form is READ from the causal chord owner, not recomputed here.
        let rate = rate_form(&generator, &storage)?;
        let congruent = storage_matrix
            .multiply(&dissipation_matrix)?
            .multiply(&storage_matrix)?;
        let predicted_matrix = congruent.scaled(&integer(-2));
        let predicted = matrix_form(&predicted_matrix)?;
        let agrees = rate == predicted;
        Ok(StorageRateReading {
            lineage: format!("{}|storage-rate", self.lineage),
            storage_inertia: inertia(&storage),
            dissipation_inertia: *dissipation.signature(),
            congruent_inertia: inertia(&matrix_form(&congruent)?),
            rate_inertia: inertia(&rate),
            rate,
            predicted,
            agrees,
        })
    }

    /// **What, if anything, the rate form licenses about the spectrum.**
    pub fn spectral_reading(&self) -> Result<SpectralReading, InteractionRefusal> {
        let reading = self.storage_rate()?;
        let generator = self.generator()?;
        let characteristic = generator.characteristic_polynomial()?;
        let half_plane = half_plane_count(&characteristic)?;
        let storage = reading.storage_inertia;
        let rate = reading.rate_inertia;
        if !storage.is_positive_definite() {
            return Ok(SpectralReading::NoLicenceWithoutDefiniteStorage {
                storage,
                rate,
                half_plane,
            });
        }
        if rate.positive > 0 {
            return Ok(SpectralReading::StorageGrows {
                storage,
                rate,
                half_plane,
            });
        }
        // `G ≻ 0` and `AᵀG + GA ⪯ 0` force `Re λ ≤ 0` for every eigenvalue. The exact half-plane
        // count is the independent measurement of the same fact, and a disagreement is a defect
        // in the exact arithmetic, not a rounding difference: it is refused by name.
        if half_plane.right > 0 {
            return Err(InteractionRefusal::SpectralContradiction {
                right: half_plane.right,
            });
        }
        // Non-growth is all the rate form gives. `M = 0` is the conservative oscillator: `G ≻ 0`,
        // a vanishing rate form, and every eigenvalue on the axis. Decay is licensed only when
        // the exact count finds no eigenvalue on the axis; a negative DEFINITE rate form forces
        // that, and an axis eigenvalue beside one is refused by name.
        if half_plane.axis > 0 {
            if rate.is_negative_definite() {
                return Err(InteractionRefusal::SpectralContradiction {
                    right: half_plane.axis,
                });
            }
            return Ok(SpectralReading::NonGrowthLicensed {
                storage,
                rate,
                half_plane,
            });
        }
        Ok(SpectralReading::DecayLicensed {
            storage,
            rate,
            half_plane,
        })
    }

    /// **The standing unit: `H_int` alone, with `H_pert` set aside.**
    pub fn standing(&self) -> Result<Self, InteractionRefusal> {
        Self::declared(
            format!("{}|standing", self.lineage),
            self.source.clone(),
            self.media.clone(),
            self.contacts.clone(),
            self.couplings.clone(),
            None,
            self.perspective.clone(),
        )
    }

    /// **The modulated unit: `H_pert` applied, through the same constructors.**
    ///
    /// A perturbation replaces declared constitutive data or a face map, and the result is built
    /// by [`HolonicInteraction::declared`], so nothing a perturbation installs escapes the checks
    /// the standing unit passed.
    pub fn modulated(&self) -> Result<Self, InteractionRefusal> {
        let Some(perturbation) = &self.perturbation else {
            return self.standing();
        };
        let mut media = self.media.clone();
        let mut contacts = self.contacts.clone();
        match perturbation {
            Perturbation::Storage { medium, storage } => {
                let carried = self.medium_at(*medium)?;
                media[*medium] = Medium::declared(
                    format!("{}|perturbed-storage", carried.lineage()),
                    storage.clone(),
                    carried.structure().clone(),
                    carried.faces().to_vec(),
                )?;
            }
            Perturbation::Structure { medium, structure } => {
                let carried = self.medium_at(*medium)?;
                media[*medium] = Medium::declared(
                    format!("{}|perturbed-structure", carried.lineage()),
                    carried.storage().clone(),
                    structure.clone(),
                    carried.faces().to_vec(),
                )?;
            }
            Perturbation::Face {
                medium,
                face,
                replacement,
            } => {
                let carried = self.medium_at(*medium)?;
                let mut faces = carried.faces().to_vec();
                if *face >= faces.len() {
                    return Err(InteractionRefusal::CarrierAbsent {
                        carrier: format!("face {face} of {}", carried.lineage()),
                    });
                }
                faces[*face] = replacement.clone();
                media[*medium] = Medium::declared(
                    format!("{}|perturbed-face", carried.lineage()),
                    carried.storage().clone(),
                    carried.structure().clone(),
                    faces,
                )?;
            }
            Perturbation::Contact {
                contact,
                replacement,
            } => {
                let carried =
                    self.contacts
                        .get(*contact)
                        .ok_or_else(|| InteractionRefusal::CarrierAbsent {
                            carrier: format!("contact {contact}"),
                        })?;
                contacts[*contact] = MediumContact::declared(
                    format!("{}|perturbed", carried.lineage()),
                    carried.left(),
                    carried.right(),
                    replacement.clone(),
                )?;
            }
        }
        Self::declared(
            format!("{}|modulated", self.lineage),
            self.source.clone(),
            media,
            contacts,
            self.couplings.clone(),
            None,
            self.perspective.clone(),
        )
    }
}

// ===============================================================================================
// 9. the storage-rate and spectral readings
// ===============================================================================================

/// **`AᵀG + GA` read from the causal chord owner, against `−2 G M G` derived here.**
///
/// [proved-derived; implemented-exact] The Lean owner's `port_storage_rate` says the two are
/// equal for the port-Hamiltonian generator. This struct carries both and the exact verdict, so
/// the identity is a *checked* fact of each reading and not a comment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct StorageRateReading {
    lineage: String,
    rate: SymmetricForm,
    predicted: SymmetricForm,
    agrees: bool,
    storage_inertia: Inertia,
    dissipation_inertia: Inertia,
    congruent_inertia: Inertia,
    rate_inertia: Inertia,
}

impl StorageRateReading {
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// `Σ_G = AᵀG + GA`, from [`crate::causal_chord::rate_form`].
    pub fn rate(&self) -> &SymmetricForm {
        &self.rate
    }

    /// `−2 G M_contact G`, the Lean identity's right-hand side.
    pub fn predicted(&self) -> &SymmetricForm {
        &self.predicted
    }

    /// Whether the two agree entry by entry.
    pub fn agrees(&self) -> bool {
        self.agrees
    }

    /// The storage form's signature. **Indefinite is lawful and withholds no reading but the
    /// spectral one.**
    pub fn storage_inertia(&self) -> &Inertia {
        &self.storage_inertia
    }

    /// The contact form's signature. Its nullity is the zero-dissipation subspace.
    pub fn dissipation_inertia(&self) -> &Inertia {
        &self.dissipation_inertia
    }

    /// The signature of `G M G`, the dissipation as the storage reading sees it.
    pub fn congruent_inertia(&self) -> &Inertia {
        &self.congruent_inertia
    }

    /// The rate form's own signature.
    pub fn rate_inertia(&self) -> &Inertia {
        &self.rate_inertia
    }

    /// **Conservation**: the storage form's rate vanishes identically. The Lean owner's
    /// `port_storage_rate_zero_of_no_dissipation` is the statement that this holds exactly when
    /// the contact form does — for any storage form, definite or not.
    pub fn is_conservative(&self) -> bool {
        self.rate_inertia.rank() == 0
    }

    /// **Strict decay of the storage reading along a motion**, which is
    /// `⟨v, Σ_G v⟩ = −2 ⟨G v, M (G v)⟩ < 0`. The sign is read from the rate form itself.
    pub fn rate_at(&self, motion: &[Rat]) -> Result<Rat, InteractionRefusal> {
        let matrix = form_matrix(&self.rate)?;
        if motion.len() != matrix.rows() {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a motion against the rate form",
                declared: matrix.rows(),
                found: motion.len(),
            });
        }
        pairing(&matrix, motion, motion)
    }
}

/// **What the rate form licenses about the spectrum — and what it does not.**
///
/// [definition] The three arms exist because the September 18 review corrected exactly this
/// defect: a vanishing or negative-semidefinite rate form says nothing about eigenvalues unless
/// the storage form is positive definite. `G = diag(1, −1)` with `A = [[0,1],[1,0]]` has
/// `AᵀG + GA = 0` and eigenvalues `±1`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum SpectralReading {
    /// `G ≻ 0`, `AᵀG + GA ⪯ 0`, and the exact half-plane count finds **no eigenvalue on the axis
    /// or to its right**: every eigenvalue satisfies `Re λ < 0` and every motion decays. The
    /// strictness comes from the count (or from a negative definite rate form, which forces it),
    /// never from semidefiniteness alone.
    DecayLicensed {
        storage: Inertia,
        rate: Inertia,
        half_plane: HalfPlaneCount,
    },
    /// `G ≻ 0` and `AᵀG + GA ⪯ 0` with eigenvalues on the axis: every eigenvalue satisfies
    /// `Re λ ≤ 0` and the storage reading never grows, **which is not decay**. The undamped
    /// oscillator (`M = 0`) lands here, as does any chain whose dissipation leaves a conservative
    /// invariant subspace untouched.
    NonGrowthLicensed {
        storage: Inertia,
        rate: Inertia,
        half_plane: HalfPlaneCount,
    },
    /// `G ≻ 0` but the rate form has a positive direction: the storage reading grows along it and
    /// nothing is licensed. The measured half-plane count is returned as a measurement.
    StorageGrows {
        storage: Inertia,
        rate: Inertia,
        half_plane: HalfPlaneCount,
    },
    /// **`G` is not positive definite, so the rate form places no spectrum at all.** The
    /// half-plane count is returned because it was measured, not because it follows.
    NoLicenceWithoutDefiniteStorage {
        storage: Inertia,
        rate: Inertia,
        half_plane: HalfPlaneCount,
    },
}

impl SpectralReading {
    /// The exact half-plane count, in every arm. It is a measurement of the characteristic
    /// polynomial and never a consequence of the rate form outside [`SpectralReading::
    /// DecayLicensed`].
    pub fn half_plane(&self) -> &HalfPlaneCount {
        match self {
            Self::DecayLicensed { half_plane, .. }
            | Self::NonGrowthLicensed { half_plane, .. }
            | Self::StorageGrows { half_plane, .. }
            | Self::NoLicenceWithoutDefiniteStorage { half_plane, .. } => half_plane,
        }
    }

    /// The storage form's signature, in every arm.
    pub fn storage(&self) -> &Inertia {
        match self {
            Self::DecayLicensed { storage, .. }
            | Self::NonGrowthLicensed { storage, .. }
            | Self::StorageGrows { storage, .. }
            | Self::NoLicenceWithoutDefiniteStorage { storage, .. } => storage,
        }
    }

    /// **Whether asymptotic decay is licensed.** Only the arm whose exact count found every
    /// eigenvalue strictly in the left half plane.
    pub fn licenses_decay(&self) -> bool {
        matches!(self, Self::DecayLicensed { .. })
    }

    /// **Whether non-growth (`Re λ ≤ 0`) is licensed**: either licensed arm. Strictly weaker than
    /// [`SpectralReading::licenses_decay`].
    pub fn licenses_non_growth(&self) -> bool {
        matches!(
            self,
            Self::DecayLicensed { .. } | Self::NonGrowthLicensed { .. }
        )
    }
}

// ===============================================================================================
// 10. the interface between two media
// ===============================================================================================

/// **The junction reading at the shared face of two consecutive media.**
///
/// [implemented-exact] The normal half — `[[n · flux]] = σ` at every joint cell — is
/// [`crate::junction_law::check_junction`]'s verdict, computed by that owner and carried here
/// whole. The tangential half is its `tangential` cochain, and the Lean connection to
/// `HolonicSnellInteraction.lean`'s `tangentialConservation_retainsNormalRemainder` is that
/// agreement on the tangential face leaves the normal face's remainder explicit rather than
/// collapsing it.
#[derive(Clone, Debug)]
pub struct InterfaceReading {
    lineage: String,
    left: Carrier,
    right: Carrier,
    verdict: JunctionVerdict,
}

impl InterfaceReading {
    /// Read the junction law at a declared interface between two carriers.
    pub fn read(
        lineage: impl Into<String>,
        left: Carrier,
        right: Carrier,
        operator: &HodgeOperator,
        interface: &Interface,
        field: &JunctionField<'_>,
        units: &JointUnits,
    ) -> Result<Self, InteractionRefusal> {
        let verdict = check_junction(operator, interface, field, units)?;
        Ok(Self {
            lineage: lineage.into(),
            left,
            right,
            verdict,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn left(&self) -> Carrier {
        self.left
    }

    pub fn right(&self) -> Carrier {
        self.right
    }

    /// The junction owner's verdict, whole.
    pub fn verdict(&self) -> &JunctionVerdict {
        &self.verdict
    }

    /// Whether the normal half of the law holds at every joint cell that was checked.
    pub fn balances(&self) -> bool {
        self.verdict.is_balanced()
    }

    /// **The retained normal remainder**: the residual cochain the balanced law does *not* say is
    /// zero, returned as the owner computed it. An `Open` family returns nothing rather than a
    /// default.
    pub fn normal_remainder(&self) -> Option<BTreeMap<crate::algebraic::CausalCellId, Rat>> {
        match &self.verdict {
            JunctionVerdict::Balanced { law, .. } => Some(law.residual()),
            JunctionVerdict::Unbalanced { residual, .. } => Some(residual.clone()),
            JunctionVerdict::Open { .. } => None,
        }
    }
}

// ===============================================================================================
// 11. the three typed populations of apparent convergence
// ===============================================================================================

/// Which of the 2026-08-24 record's populations a convergence belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum PopulationTag {
    /// Shared source incidence or contact.
    SharedIncidence,
    /// A receiver caustic: an equal projected face with a retained fibre.
    ReceiverCaustic,
    /// A declared constitutive coupling with an off-diagonal response term.
    ConstitutiveCoupling,
}

/// **Exactly one typed population, with its witness.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum ConvergencePopulation {
    /// The two carriers share a declared contact whose slip map is nonzero on both blocks. The
    /// declared contact is named and its slip supports on the two blocks are returned.
    SharedIncidence {
        contact: usize,
        left_support: Vec<usize>,
        right_support: Vec<usize>,
    },
    /// The receiver's aperture reads two distinct directions — one in each block — identically,
    /// and their difference is the retained reconstruction fibre. **Depth is retained, not lost:
    /// the fibre is returned.**
    ReceiverCaustic {
        left_coordinate: usize,
        right_coordinate: usize,
        retained_fibre: Vec<Rat>,
    },
    /// A declared coupling joins the two carriers with a nonzero off-diagonal block **and** the
    /// derived generator carries a nonzero block between them, which is the returned later
    /// consequence the record requires. A coupling without that consequence is not this
    /// population.
    ConstitutiveCoupling {
        coupling: usize,
        response: ExactRatMatrix,
        later_consequence: ExactRatMatrix,
    },
    /// None of the three: the two carriers converge only in the rendering. The record's rule is
    /// that a raster crossing mints no source law, and this arm is that refusal.
    NoSourceRelation,
}

/// **The classification, with everything it also satisfies named.**
///
/// [definition] The record says every apparent convergence is to be lifted and classified as
/// exactly one typed population *before* it is used. The populations are checked in the record's
/// own order and the first that holds is the answer; the others that also hold are listed rather
/// than hidden, because a convergence that is both a contact and a caustic is a fact about the
/// configuration and not an ambiguity in the classifier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ConvergenceClassification {
    lineage: String,
    left: Carrier,
    right: Carrier,
    population: ConvergencePopulation,
    also_satisfied: Vec<PopulationTag>,
}

impl ConvergenceClassification {
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn left(&self) -> Carrier {
        self.left
    }

    pub fn right(&self) -> Carrier {
        self.right
    }

    /// The one population this convergence is classified as.
    pub fn population(&self) -> &ConvergencePopulation {
        &self.population
    }

    /// The other populations the same pair also satisfies, in the record's order.
    pub fn also_satisfied(&self) -> &[PopulationTag] {
        &self.also_satisfied
    }
}

/// Which coordinates of a face's slip map are supported inside a block.
fn slip_support(
    face: &ContactFace,
    offset: usize,
    extent: usize,
) -> Result<Vec<usize>, InteractionRefusal> {
    let mut support = Vec::new();
    for column in offset..offset + extent {
        let mut carries = false;
        for row in 0..face.slip_extent() {
            if !face.slip().get(row, column)?.is_zero() {
                carries = true;
                break;
            }
        }
        if carries {
            support.push(column - offset);
        }
    }
    Ok(support)
}

/// **Classify the apparent convergence of two carriers.**
pub fn classify_convergence(
    interaction: &HolonicInteraction,
    left: Carrier,
    right: Carrier,
) -> Result<ConvergenceClassification, InteractionRefusal> {
    if left == right {
        return Err(InteractionRefusal::CarrierAbsent {
            carrier: format!("{} converging with itself", left.name()),
        });
    }
    let left_extent = interaction.block_extent(left)?;
    let right_extent = interaction.block_extent(right)?;
    let left_offset = interaction.block_offset(left)?;
    let right_offset = interaction.block_offset(right)?;

    // Population 1: shared incidence/contact.
    let mut incidence: Option<ConvergencePopulation> = None;
    for (at, contact) in interaction.contacts().iter().enumerate() {
        if !contact.joins(left, right) {
            continue;
        }
        let extent = interaction.joint_dimension();
        let mut coordinates = interaction.block_coordinates(contact.left())?;
        coordinates.extend(interaction.block_coordinates(contact.right())?);
        let embedded = contact.face().embedded(extent, &coordinates)?;
        let left_support = slip_support(&embedded, left_offset, left_extent)?;
        let right_support = slip_support(&embedded, right_offset, right_extent)?;
        if !left_support.is_empty() && !right_support.is_empty() {
            incidence = Some(ConvergencePopulation::SharedIncidence {
                contact: at,
                left_support,
                right_support,
            });
            break;
        }
    }

    // Population 2: a receiver caustic — one direction in each block with the same reading.
    bounded_product(
        "a caustic search",
        &[left_extent, right_extent],
        DECLARED_ASSEMBLY_CEILING,
    )?;
    let readout = interaction.readout()?;
    let extent = interaction.joint_dimension();
    let mut caustic: Option<ConvergencePopulation> = None;
    'search: for one in 0..left_extent {
        for other in 0..right_extent {
            let mut agrees = true;
            let mut carries = false;
            for port in 0..readout.rows() {
                let read_left = readout.get(port, left_offset + one)?;
                let read_right = readout.get(port, right_offset + other)?;
                if read_left != read_right {
                    agrees = false;
                    break;
                }
                if !read_left.is_zero() {
                    carries = true;
                }
            }
            if agrees && carries {
                let mut fibre = vec![Rat::zero(); extent];
                fibre[left_offset + one] = integer(1);
                fibre[right_offset + other] = integer(-1);
                caustic = Some(ConvergencePopulation::ReceiverCaustic {
                    left_coordinate: one,
                    right_coordinate: other,
                    retained_fibre: fibre,
                });
                break 'search;
            }
        }
    }

    // Population 3: a declared constitutive coupling with a returned later consequence.
    let generator = interaction.generator()?;
    let mut constitutive: Option<ConvergencePopulation> = None;
    for (at, coupling) in interaction.couplings().iter().enumerate() {
        let joins = (coupling.from() == left && coupling.to() == right)
            || (coupling.from() == right && coupling.to() == left);
        if !joins || !coupling.is_active() {
            continue;
        }
        // The later consequence: the derived generator's off-diagonal block from `from` to `to`.
        let from_offset = interaction.block_offset(coupling.from())?;
        let to_offset = interaction.block_offset(coupling.to())?;
        let from_extent = interaction.block_extent(coupling.from())?;
        let to_extent = interaction.block_extent(coupling.to())?;
        let mut rows = vec![vec![Rat::zero(); from_extent]; to_extent];
        let mut carries = false;
        for row in 0..to_extent {
            for column in 0..from_extent {
                let entry = generator.get(to_offset + row, from_offset + column)?.clone();
                if !entry.is_zero() {
                    carries = true;
                }
                rows[row][column] = entry;
            }
        }
        if carries {
            constitutive = Some(ConvergencePopulation::ConstitutiveCoupling {
                coupling: at,
                response: coupling.block().clone(),
                later_consequence: ExactRatMatrix::shaped(to_extent, from_extent, rows)?,
            });
            break;
        }
    }

    let mut also = Vec::new();
    let population = if let Some(shared) = incidence {
        if caustic.is_some() {
            also.push(PopulationTag::ReceiverCaustic);
        }
        if constitutive.is_some() {
            also.push(PopulationTag::ConstitutiveCoupling);
        }
        shared
    } else if let Some(shadow) = caustic {
        if constitutive.is_some() {
            also.push(PopulationTag::ConstitutiveCoupling);
        }
        shadow
    } else if let Some(coupled) = constitutive {
        coupled
    } else {
        ConvergencePopulation::NoSourceRelation
    };

    Ok(ConvergenceClassification {
        lineage: format!("{}|convergence", interaction.lineage()),
        left,
        right,
        population,
        also_satisfied: also,
    })
}

#[cfg(test)]
#[path = "holonic_interaction/tests.rs"]
mod tests;
