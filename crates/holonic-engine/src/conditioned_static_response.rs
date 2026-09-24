//! **The conditioned static response: a declared elastic energy, a declared forcing, and the
//! displacement it returns together with its full null fibre and its residual.**
//!
//! [definition] This module owns the equations of
//! `docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md#the-conditioned-structural-response-consumer`.
//! It is the consumer side of issue #55. It generates a response; it does not read one that some
//! other predictor produced, and it is **not** general structure prediction. Everything below is
//! exact over `ℚ`: no `f32` and no `f64` occurs anywhere in this file.
//!
//! # What has to be declared before a comparison structure is received
//!
//! [definition] Four things, and a reading that skips any one of them is not this receiver:
//!
//! 1. the source configuration `|q₀⟩` and its residue correspondence — owned by
//!    [`crate::rigidity_receiver::ExactConfiguration`];
//! 2. the elastic energy, its stiffness and its units — [`ElasticDeclaration`];
//! 3. the forcing map `B` and the force family `|u⟩`, with `|f⟩ = B|u⟩` — [`ForcingDeclaration`];
//! 4. the metric and the gauge — [`DeclaredMetric`] and [`ResponseGauge`].
//!
//! # The stiffness, and why it may not be inherited
//!
//! [proved-derived; implemented-exact] The declared energy is the elastic-network form
//!
//! ```text
//! E(q) = ½ Σ_c γ_c ( ℓ_c(q) − ℓ_c(q₀) )²,     γ_c ≥ 0,   [γ] = energy / length²
//! ```
//!
//! whose Hessian at `q₀` is `Σ_c γ_c ∇ℓ_c ∇ℓ_c*`. The rigidity receiver differentiates the
//! *squared* length, `F_c(q) = |q_i − q_j|² − ℓ_c²`, so its row is `∇F_c = 2 ℓ_c ∇ℓ_c` and
//!
//! ```text
//! K = Hess E(q₀) = J* W J,     W = diag( γ_c / (4 ℓ_c²) ),    [W] = energy / length⁴
//! ```
//!
//! `ℓ_c²` is the exact rational [`crate::rigidity_receiver::DistanceConstraint::squared_length`],
//! so `W` is exact, `W = W* ⪰ 0`, and `K = K*` in the declared coordinate pairing — checked entry
//! by entry at construction, never assumed.
//!
//! [counterexample; source-inspected] **`crate::holonic_chain::elastic_chain` builds the same
//! matrix expression `A = −J*J` as a *dissipation* form with `Ω = 0, G = I`.** Reading that
//! expression as a physical stiffness is a change of physical content, not a change of notation:
//! it requires the energy, the units and the pairing above. [`ElasticDeclaration`] carries them
//! as data so the reading cannot be inherited silently.
//!
//! # The full kernel, not only the rigid motions
//!
//! [proved-derived; implemented-exact] `Z` spans the **whole** of `ker K`. For strictly positive
//! `γ_c`, `v*Kv = (Jv)* W (Jv) = 0` forces `Jv = 0`, so `ker K = ker J` exactly — verified, not
//! asserted, by [`NullFibre::equals_constraint_kernel`]. That kernel contains the trivial motions
//! measured by [`crate::rigidity_receiver::TrivialMotionReading`] **and** every internal floppy
//! mode of the bounded window, and [`NullFibre::internal_floppy_dimension`] names the difference.
//! A reading that takes `Z` to be the six rigid motions of space is wrong on any window whose
//! contact graph does not brace itself.
//!
//! # Compatibility, the gauge, and what is retained when the forcing is incompatible
//!
//! [proved-standard] `K` is self-adjoint, so `image K = (ker K)^⊥` in the same pairing and a static
//! equilibrium exists **iff** `Z* f = 0`. [`StaticResponse`] tests that exactly before it solves.
//!
//! * compatible: `K δq = f` is solved through [`holonics::exact_linear::ExactRatMatrix::preimage_fibre`],
//!   which returns the complete affine fibre `δq₀ + ker K` and selects nothing. The declared gauge
//!   [`ResponseGauge::MetricComplement`] then picks the representative with `Z* G δq = 0`. Both
//!   `K δq − f` and `Z* G δq` are returned and both are exactly zero.
//! * incompatible: the response is **refused** and `(I − P) f`, the part of the forcing no static
//!   equilibrium answers, is retained together with the cokernel covector witnessing it. Solving
//!   `K δq = P f` instead is a **different receiver**; it is available as
//!   [`StaticResponse::least_squares_projection`] and it is labelled as one everywhere it appears.
//!
//! # The neck claim is withheld, and here is the counterexample that withholds it
//!
//! [counterexample; computational-witness] `crate::holonic_chain::HolonicChain::transfer_at` takes
//! an ordinary inverse and refuses a pole. `K` is singular on every configuration with a rigid
//! motion, so `C K⁺ B` is **not** `H(0) = C(−A)⁻¹B` and the off-pole neck theorem may not be copied
//! onto it. [`neck_cross_block_counterexample`] recomputes the audit's four-site witness exactly:
//! with
//!
//! ```text
//! K = [[1,−1,0,0],[−1,2,−1,0],[0,−1,2,−1],[0,0,−1,1]],   cut {1,2}|{3,4}
//! ```
//!
//! the stiffness cross block has rank **1** while the Moore–Penrose cross block `[[−3,−1],[−5,−3]]/8`
//! has rank **2**. [`NeckIdentification`] is therefore returned as *withheld* by every family
//! reading in this module. What **is** returned is the certified statement
//! [`ResponseFamilyReading`] proves: on the admissible subspace the gauge-fixed response map is a
//! linear bijection onto the gauge complement, so its rank is `rank K`. One observed displacement
//! tests membership and residual against that image; it does not test its rank.
//!
//! # The receiver reports a sign
//!
//! [definition] [`QuadranceResponse`] returns the **oriented** pairwise-quadrance change, both the
//! linearized `2⟨q_i − q_j, δq_i − δq_j⟩` and the finite change that adds `|δq_i − δq_j|²`.
//! [`OrientedAgreement`] returns the exact pairing, the exact sign, and `cos²` **beside** the sign
//! and never instead of it: `cos²` scores `−p` identically to `p`, so it is an additional
//! unoriented face and is not sufficient.
//!
//! # Prior art
//!
//! [source-audit 2026-09-20 27c72825] `prior-art 'conditioned static response|ConditionedStaticResponse|conditioned_static_response|linear response stiffness'`
//! returned 0 files, and `prior-art 'pairwise distance change|squared length difference|displacement residual|response operator|stiffness matrix'`
//! returned 0 files: **the repository has no static-response, response-operator, stiffness-matrix
//! or pairwise-quadrance-change owner**. `prior-art 'elastic stiffness|forcing map|null fibre|preimage_fibre|rigidity kernel'`
//! returned 60 files whose actual owners are named and composed here rather than reimplemented:
//! `exact_linear::ExactRatMatrix::{preimage_fibre, preimage_obstruction, kernel_basis, rank, inverse}`
//! and `rigidity_receiver::{RigidityJacobian, TrivialMotionReading}`.

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use holonics::exact_linear::{ExactLinearError, ExactRatMatrix};
use holonics::exact_work::ExactWork;
use crate::rigidity_receiver::{
    ConfigurationDegeneracy, ExactConfiguration, RigidityError, RigidityJacobian,
    TrivialMotionReading,
};

pub const CONDITIONED_STATIC_RESPONSE_SCHEMA: &str =
    "holonic-engine.conditioned-static-response.v1";

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn dot(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter()
        .zip(right)
        .fold(Rat::zero(), |sum, (a, b)| sum + a * b)
}

// -------------------------------------------------------------------------------------------
// 1. the declared elastic energy, its stiffness and its units
// -------------------------------------------------------------------------------------------

/// **The declared elastic energy, stiffness and units — carried as data, never inherited.**
///
/// The `Ω = 0, G = I` dissipation reading of `−J*J` in `crate::holonic_chain::elastic_chain` is a
/// different physical statement about the same matrix expression. This declaration is what makes
/// the present reading a stiffness, and it travels with every `K` built from it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ElasticDeclaration {
    pub schema: String,
    /// `γ_c ≥ 0`, one per constraint, in `stiffness_unit`.
    pub stiffness: Vec<Rat>,
    pub stiffness_unit: String,
    pub length_unit: String,
    pub energy_unit: String,
    pub energy_law: String,
    pub weight_law: String,
    pub pairing: String,
    /// The sentence that refuses the silent inheritance.
    pub not_inherited_from_the_dissipation_form: String,
}

impl ElasticDeclaration {
    /// A uniform spring constant `γ` over every constraint, in a declared unit.
    ///
    /// Uniformity is the standard elastic-network reading and it is a *declaration*, not a
    /// derivation: nothing in the source configuration selects it.
    pub fn uniform(
        constraint_count: usize,
        gamma: Rat,
        stiffness_unit: impl Into<String>,
        length_unit: impl Into<String>,
        energy_unit: impl Into<String>,
    ) -> Result<Self, StaticResponseError> {
        if gamma.is_negative() {
            return Err(StaticResponseError::NegativeStiffness { constraint: 0 });
        }
        Ok(Self {
            schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
            stiffness: vec![gamma; constraint_count],
            stiffness_unit: stiffness_unit.into(),
            length_unit: length_unit.into(),
            energy_unit: energy_unit.into(),
            energy_law: "E(q) = 1/2 sum_c gamma_c (l_c(q) - l_c(q0))^2".to_owned(),
            weight_law: "W = diag(gamma_c / (4 l_c^2)); K = J* W J = Hess E(q0)".to_owned(),
            pairing: "the standard pairing on the declared Cartesian coordinate basis, in which \
                      K = K* holds entry by entry"
                .to_owned(),
            not_inherited_from_the_dissipation_form:
                "holonic_chain::elastic_chain builds the same matrix expression as a dissipation \
                 form with Omega = 0, G = I; reading it as physical stiffness requires this \
                 energy/units declaration and does not follow from the expression"
                    .to_owned(),
        })
    }

    /// A declared per-constraint spring constant.
    pub fn per_constraint(
        stiffness: Vec<Rat>,
        stiffness_unit: impl Into<String>,
        length_unit: impl Into<String>,
        energy_unit: impl Into<String>,
    ) -> Result<Self, StaticResponseError> {
        if let Some(constraint) = stiffness.iter().position(Rat::is_negative) {
            return Err(StaticResponseError::NegativeStiffness { constraint });
        }
        let mut declaration =
            Self::uniform(0, Rat::zero(), stiffness_unit, length_unit, energy_unit)?;
        declaration.stiffness = stiffness;
        Ok(declaration)
    }

    pub fn every_constraint_is_loaded(&self) -> bool {
        self.stiffness.iter().all(|gamma| gamma.is_positive())
    }
}

/// **`K = J* W J`: the declared stiffness, self-adjoint by construction and checked.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ConditionedStiffness {
    schema: String,
    presentation_lineage: String,
    declaration: ElasticDeclaration,
    /// `w_c = γ_c / (4 ℓ_c²)`, exact.
    weights: Vec<Rat>,
    matrix: ExactRatMatrix,
    coordinate_freedoms: usize,
    constraint_count: usize,
    rank: usize,
    /// `Σ_{i<j} |K_ij − K_ji|`, returned so the self-adjointness is a number and not a promise.
    self_adjoint_defect: Rat,
    work: ExactWork,
}

impl ConditionedStiffness {
    pub fn schema(&self) -> &str {
        &self.schema
    }
    pub fn presentation_lineage(&self) -> &str {
        &self.presentation_lineage
    }
    pub fn declaration(&self) -> &ElasticDeclaration {
        &self.declaration
    }
    pub fn weights(&self) -> &[Rat] {
        &self.weights
    }
    pub fn matrix(&self) -> &ExactRatMatrix {
        &self.matrix
    }
    pub fn coordinate_freedoms(&self) -> usize {
        self.coordinate_freedoms
    }
    pub fn constraint_count(&self) -> usize {
        self.constraint_count
    }
    pub fn rank(&self) -> usize {
        self.rank
    }
    pub fn self_adjoint_defect(&self) -> &Rat {
        &self.self_adjoint_defect
    }
    pub fn work(&self) -> &ExactWork {
        &self.work
    }

    /// Build `K` from a rigidity Jacobian and a declared energy.
    ///
    /// Refuses a coincident constraint with positive stiffness: `ℓ_c² = 0` has no `γ_c/(4ℓ_c²)`,
    /// and a zero-length spring is a modelling question, not a division to be attempted.
    pub fn declared(
        jacobian: &RigidityJacobian,
        declaration: ElasticDeclaration,
    ) -> Result<Self, StaticResponseError> {
        jacobian.validated()?;
        let constraint_count = jacobian.constraint_count();
        if declaration.stiffness.len() != constraint_count {
            return Err(StaticResponseError::StiffnessPopulationDisagrees {
                declared: declaration.stiffness.len(),
                constraints: constraint_count,
            });
        }
        let four = integer(4);
        let mut weights = Vec::with_capacity(constraint_count);
        for (at, constraint) in jacobian.constraints.iter().enumerate() {
            let gamma = &declaration.stiffness[at];
            if gamma.is_negative() {
                return Err(StaticResponseError::NegativeStiffness { constraint: at });
            }
            if constraint.squared_length.is_zero() {
                if gamma.is_zero() {
                    weights.push(Rat::zero());
                    continue;
                }
                return Err(StaticResponseError::CoincidentConstraintIsLoaded { constraint: at });
            }
            weights.push(gamma / (&four * &constraint.squared_length));
        }

        let mut work = ExactWork::nothing();
        let rows = jacobian.matrix.to_rows();
        let width = jacobian.coordinate_freedoms();
        let mut scaled = Vec::with_capacity(rows.len());
        for (row, weight) in rows.iter().zip(&weights) {
            let mut line = Vec::with_capacity(width);
            for entry in row {
                let value = entry * weight;
                work.multiplied(1);
                work.wrote(&value);
                line.push(value);
            }
            scaled.push(line);
        }
        let weighted = ExactRatMatrix::shaped(rows.len(), width, scaled)?;
        let transpose = jacobian.matrix.transpose()?;
        let (matrix, product_work) = transpose.multiply_with_work(&weighted)?;
        work = work.then(&product_work);

        let mut defect = Rat::zero();
        for row in 0..width {
            for column in (row + 1)..width {
                let difference = matrix.get(row, column)? - matrix.get(column, row)?;
                if !difference.is_zero() {
                    return Err(StaticResponseError::StiffnessIsNotSelfAdjoint { row, column });
                }
                defect += difference.abs();
            }
        }

        let rank = matrix.rank()?;
        Ok(Self {
            schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
            presentation_lineage: jacobian.presentation_lineage.clone(),
            declaration,
            weights,
            matrix,
            coordinate_freedoms: width,
            constraint_count,
            rank,
            self_adjoint_defect: defect,
            work,
        })
    }

    /// The elastic energy `½ δq* K δq` of a displacement, exact, in the declared energy unit.
    pub fn energy(&self, displacement: &[Rat]) -> Result<Rat, StaticResponseError> {
        let image = self.matrix.apply(displacement)?;
        Ok(dot(displacement, &image) / integer(2))
    }
}

// -------------------------------------------------------------------------------------------
// 2. the full null fibre
// -------------------------------------------------------------------------------------------

/// **`Z`: a basis of the whole of `ker K`, with the rigid motions separated from the floppy ones.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NullFibre {
    pub schema: String,
    /// The columns of `Z`, one vector each.
    pub basis: Vec<Vec<Rat>>,
    pub dimension: usize,
    /// `dim T(q₀)`, measured by the rigidity receiver at this configuration and never assumed to
    /// be `d(d+1)/2`.
    pub trivial_dimension: usize,
    /// `dim ker K − dim T(q₀)`: the internal floppy modes of the bounded window. A reading that
    /// takes `Z` to be the rigid motions alone is wrong exactly when this is positive.
    pub internal_floppy_dimension: usize,
    pub degeneracy: ConfigurationDegeneracy,
    /// `ker K = ker J`, **verified** by applying `J` to every kernel vector rather than argued
    /// from `γ_c > 0` alone.
    pub equals_constraint_kernel: bool,
    pub constraint_kernel_dimension: usize,
}

impl NullFibre {
    pub fn measure(
        stiffness: &ConditionedStiffness,
        jacobian: &RigidityJacobian,
    ) -> Result<Self, StaticResponseError> {
        let basis = stiffness.matrix.kernel_basis()?;
        let dimension = basis.len();
        let trivial = TrivialMotionReading::measure(jacobian)?;
        if trivial.dimension_of_span > dimension {
            return Err(StaticResponseError::TrivialMotionOutsideStiffnessKernel);
        }
        let constraint_kernel_dimension = jacobian.matrix.kernel_basis()?.len();
        let mut equals_constraint_kernel = dimension == constraint_kernel_dimension;
        if equals_constraint_kernel {
            for vector in &basis {
                if jacobian.matrix.apply(vector)?.iter().any(|e| !e.is_zero()) {
                    equals_constraint_kernel = false;
                    break;
                }
            }
        }
        Ok(Self {
            schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
            basis,
            dimension,
            trivial_dimension: trivial.dimension_of_span,
            internal_floppy_dimension: dimension - trivial.dimension_of_span,
            degeneracy: trivial.degeneracy,
            equals_constraint_kernel,
            constraint_kernel_dimension,
        })
    }

    /// `Z* f`, the exact compatibility pairing. A static equilibrium exists iff it vanishes.
    pub fn compatibility_pairing(&self, force: &[Rat]) -> Result<Vec<Rat>, StaticResponseError> {
        let mut pairing = Vec::with_capacity(self.dimension);
        for vector in &self.basis {
            if vector.len() != force.len() {
                return Err(StaticResponseError::Linear(ExactLinearError::ShapeMismatch));
            }
            pairing.push(dot(vector, force));
        }
        Ok(pairing)
    }

    /// Validate that this serialized or caller-supplied basis is the complete kernel of `K`.
    ///
    /// The dimension alone is insufficient: two different subspaces can have the same dimension,
    /// and using one of them for compatibility or gauge selection changes the receiver.  Every
    /// basis vector must be in the actual kernel, the vectors must be independent, and their count
    /// must equal the kernel dimension.  Those conditions make their span the complete kernel.
    pub fn validate_against(
        &self,
        stiffness: &ConditionedStiffness,
    ) -> Result<(), StaticResponseError> {
        let width = stiffness.coordinate_freedoms;
        if self.dimension != self.basis.len() {
            return Err(StaticResponseError::NullFibreDimensionFieldDisagrees {
                declared: self.dimension,
                basis: self.basis.len(),
            });
        }
        for vector in &self.basis {
            if vector.len() != width {
                return Err(StaticResponseError::Linear(ExactLinearError::ShapeMismatch));
            }
            if stiffness
                .matrix
                .apply(vector)?
                .iter()
                .any(|entry| !entry.is_zero())
            {
                return Err(StaticResponseError::NullFibreBasisVectorNotInKernel);
            }
        }
        let basis_rank = if self.basis.is_empty() {
            0
        } else {
            ExactRatMatrix::shaped(self.basis.len(), width, self.basis.clone())?.rank()?
        };
        if basis_rank != self.basis.len() {
            return Err(StaticResponseError::NullFibreBasisIsDependent);
        }
        let actual_dimension = stiffness.matrix.kernel_basis()?.len();
        if actual_dimension != self.basis.len() {
            return Err(StaticResponseError::NullFibreDisagrees {
                measured: self.basis.len(),
                returned: actual_dimension,
            });
        }
        Ok(())
    }
}

// -------------------------------------------------------------------------------------------
// 3. the declared metric and gauge
// -------------------------------------------------------------------------------------------

/// **The metric `G` on configuration space, declared and never defaulted.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DeclaredMetric {
    schema: String,
    name: String,
    unit: String,
    matrix: ExactRatMatrix,
}

impl DeclaredMetric {
    pub fn schema(&self) -> &str {
        &self.schema
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn unit(&self) -> &str {
        &self.unit
    }
    pub fn matrix(&self) -> &ExactRatMatrix {
        &self.matrix
    }

    /// `G = I` on the declared Cartesian coordinate basis. This is a **declaration** that the
    /// coordinate basis is the one the gauge is orthogonal in, not an absence of one.
    pub fn cartesian_identity(
        extent: usize,
        unit: impl Into<String>,
    ) -> Result<Self, StaticResponseError> {
        Ok(Self {
            schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
            name: "the identity on the declared Cartesian coordinate basis".to_owned(),
            unit: unit.into(),
            matrix: ExactRatMatrix::identity(extent)?,
        })
    }

    /// A declared metric, refused unless it is square and symmetric.
    pub fn declared(
        name: impl Into<String>,
        unit: impl Into<String>,
        matrix: ExactRatMatrix,
    ) -> Result<Self, StaticResponseError> {
        if !matrix.is_square() {
            return Err(StaticResponseError::MetricIsNotSquare);
        }
        for row in 0..matrix.rows() {
            for column in (row + 1)..matrix.columns() {
                if matrix.get(row, column)? != matrix.get(column, row)? {
                    return Err(StaticResponseError::MetricIsNotSymmetric { row, column });
                }
            }
        }
        Ok(Self {
            schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
            name: name.into(),
            unit: unit.into(),
            matrix,
        })
    }
}

/// **Which representative of the affine fibre `δq₀ + ker K` the response returns.**
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ResponseGauge {
    /// `Z* G δq = 0`: the representative `G`-orthogonal to the entire null fibre — rigid motions
    /// and internal floppy modes alike. Well posed exactly when `Z* G Z` is invertible, which is
    /// checked rather than assumed.
    MetricComplement,
}

impl ResponseGauge {
    pub fn name(&self) -> &'static str {
        match self {
            Self::MetricComplement => "Z* G dq = 0, the G-orthogonal complement of the full kernel",
        }
    }
}

// -------------------------------------------------------------------------------------------
// 4. the forcing map and the force family
// -------------------------------------------------------------------------------------------

/// One column of `B`, with its provenance.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForcingGenerator {
    pub description: String,
    /// The configuration blocks this generator loads.
    pub loaded_blocks: Vec<usize>,
}

/// **`B` and the provenance of everything it carries.**
///
/// A contact site is a *support*. It fixes neither a direction nor a magnitude, and this type
/// records those three caller-declared provenances separately. The fields are testimony carried
/// to the receiver; this API cannot prove that a caller did not inspect a held-out displacement
/// while choosing a support, direction or magnitude.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForcingDeclaration {
    pub schema: String,
    /// `B`, `coordinate_freedoms × generators`.
    pub matrix: ExactRatMatrix,
    pub generators: Vec<ForcingGenerator>,
    pub support_provenance: String,
    pub direction_provenance: String,
    pub magnitude_provenance: String,
    /// Caller testimony about held-out use. `true` records declared leakage; `false` does not prove
    /// its absence because provenance cannot be established mechanically at this boundary.
    pub held_out_displacement_used: bool,
    /// `true` when every column is exactly orthogonal to every trivial motion — proved by
    /// construction for [`Self::pinch_family`] and **checked** by [`Self::self_equilibrated`].
    pub self_equilibrated: bool,
}

impl ForcingDeclaration {
    /// **The self-equilibrated pinch family.**
    ///
    /// [proved-derived; implemented-exact] Generator `(i, j)` places `+(q_j − q_i)` in block `i`
    /// and `−(q_j − q_i)` in block `j`. Its net force is `f_i + f_j = 0`, and its net moment about
    /// any origin is `q_i × f_i + q_j × f_j = (q_i − q_j) × f_i = −(q_j − q_i) × (q_j − q_i) = 0`.
    /// So every column is exactly orthogonal to every translation *and* every rotation generator
    /// linearized at `q₀`, and the compatibility `Z* f = 0` can fail only against an **internal
    /// floppy mode** of the window. The direction is read from `|q₀⟩` alone; only the choice of
    /// which pairs are loaded carries the support's provenance.
    ///
    /// [proved-derived] **When the loaded pair `(i,j)` is itself a constraint `c` of the same
    /// Jacobian, the column is exactly `−½ J* e_c`** — the constraint row carries `2(q_i − q_j)`
    /// at block `i` and its negative at block `j`. Such a forcing therefore lies in
    /// `image J* = (ker J)^⊥ = image K`, and its compatibility is a *theorem*, not a finding:
    /// `Z* f = 0` holds against every floppy mode too. The forcings whose compatibility can
    /// genuinely fail are the ones **off the bars**, between two loaded sites that are not in
    /// contact. A reading that only ever pinches along its own bars has not tested compatibility
    /// at all, and this sentence is here so that it cannot be mistaken for one that has.
    pub fn pinch_family(
        configuration: &ExactConfiguration,
        pairs: &[(usize, usize)],
        support_provenance: impl Into<String>,
        magnitude_provenance: impl Into<String>,
    ) -> Result<Self, StaticResponseError> {
        configuration.validated()?;
        let dimension = configuration.dimension();
        let places = configuration.ordered_places();
        let width = dimension
            .checked_mul(places.len())
            .ok_or(ExactLinearError::ExtentOverflow)?;
        if pairs.is_empty() {
            return Err(StaticResponseError::EmptyForcingFamily);
        }

        let mut columns: Vec<Vec<Rat>> = Vec::with_capacity(pairs.len());
        let mut generators = Vec::with_capacity(pairs.len());
        for (lower, upper) in pairs {
            if lower == upper {
                return Err(StaticResponseError::PinchIsNotAPair { block: *lower });
            }
            let lower_place = places
                .get(*lower)
                .ok_or(StaticResponseError::BlockOutsideConfiguration { block: *lower })?;
            let upper_place = places
                .get(*upper)
                .ok_or(StaticResponseError::BlockOutsideConfiguration { block: *upper })?;
            let mut column = vec![Rat::zero(); width];
            let mut vanishes = true;
            for axis in 0..dimension {
                let difference = &upper_place[axis] - &lower_place[axis];
                if !difference.is_zero() {
                    vanishes = false;
                }
                column[lower * dimension + axis] = difference.clone();
                column[upper * dimension + axis] = -difference;
            }
            if vanishes {
                return Err(StaticResponseError::PinchIsCoincident {
                    lower: *lower,
                    upper: *upper,
                });
            }
            columns.push(column);
            generators.push(ForcingGenerator {
                description: format!(
                    "pinch along the source segment from block {lower} to block {upper}: \
                     +(q_{upper} - q_{lower}) at {lower} and its negative at {upper}"
                ),
                loaded_blocks: vec![*lower, *upper],
            });
        }

        let rows = (0..width)
            .map(|row| columns.iter().map(|column| column[row].clone()).collect())
            .collect();
        let matrix = ExactRatMatrix::shaped(width, columns.len(), rows)?;
        Ok(Self {
            schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
            matrix,
            generators,
            support_provenance: support_provenance.into(),
            direction_provenance:
                "along the source segment of |q0> alone; no bound structure and no held-out \
                 displacement enters a direction"
                    .to_owned(),
            magnitude_provenance: magnitude_provenance.into(),
            held_out_displacement_used: false,
            self_equilibrated: true,
        })
    }

    /// A forcing map declared column by column, with its three provenances stated separately.
    pub fn declared(
        matrix: ExactRatMatrix,
        generators: Vec<ForcingGenerator>,
        support_provenance: impl Into<String>,
        direction_provenance: impl Into<String>,
        magnitude_provenance: impl Into<String>,
    ) -> Result<Self, StaticResponseError> {
        if matrix.columns() != generators.len() {
            return Err(StaticResponseError::ForcingPopulationDisagrees {
                columns: matrix.columns(),
                generators: generators.len(),
            });
        }
        Ok(Self {
            schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
            matrix,
            generators,
            support_provenance: support_provenance.into(),
            direction_provenance: direction_provenance.into(),
            magnitude_provenance: magnitude_provenance.into(),
            held_out_displacement_used: false,
            self_equilibrated: false,
        })
    }

    /// `|f⟩ = B|u⟩`.
    pub fn force(&self, magnitudes: &[Rat]) -> Result<Vec<Rat>, StaticResponseError> {
        if magnitudes.len() != self.matrix.columns() {
            return Err(StaticResponseError::ForceFamilyDisagrees {
                declared: magnitudes.len(),
                generators: self.matrix.columns(),
            });
        }
        Ok(self.matrix.apply(magnitudes)?)
    }

    /// **Check** — do not assume — that every column is orthogonal to every trivial motion.
    pub fn self_equilibrated(
        &mut self,
        trivial: &TrivialMotionReading,
    ) -> Result<bool, StaticResponseError> {
        let mut equilibrated = true;
        for column in 0..self.matrix.columns() {
            let vector: Vec<Rat> = (0..self.matrix.rows())
                .map(|row| self.matrix.get(row, column).cloned())
                .collect::<Result<_, _>>()?;
            for generator in &trivial.generators {
                if generator.len() != vector.len() {
                    return Err(StaticResponseError::Linear(ExactLinearError::ShapeMismatch));
                }
                if !dot(generator, &vector).is_zero() {
                    equilibrated = false;
                }
            }
        }
        self.self_equilibrated = equilibrated;
        Ok(equilibrated)
    }
}

// -------------------------------------------------------------------------------------------
// 5. the static response
// -------------------------------------------------------------------------------------------

/// **`K δq = f` on the complement of the full kernel, with its gauge, its null fibre and its
/// residual — or the refusal, with the part of the forcing that no equilibrium answers.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StaticResponse {
    pub schema: String,
    pub gauge: String,
    pub metric: String,
    pub force: Vec<Rat>,
    /// `Z* f`. Exactly zero iff a static equilibrium exists.
    pub compatibility_pairing: Vec<Rat>,
    pub compatible: bool,
    /// `(I − P) f`, the component of the forcing inside `ker K`. **Retained, never projected
    /// away.** Zero when the forcing is compatible.
    pub retained_incompatible_force: Vec<Rat>,
    /// A covector `w` with `w* K = 0` and `⟨w, f⟩ ≠ 0`, from
    /// [`holonics::exact_linear::ExactRatMatrix::preimage_obstruction`]. An obstruction is a return.
    pub obstruction: Option<Vec<Rat>>,
    /// The gauge-fixed displacement, present exactly when `compatible`.
    pub displacement: Option<Vec<Rat>>,
    /// `K δq − f`, exactly zero when a displacement is returned.
    pub equilibrium_residual: Vec<Rat>,
    /// `Z* G δq`, exactly zero when a displacement is returned.
    pub gauge_residual: Vec<Rat>,
    /// The null fibre the returned representative was chosen out of: `δq + span Z`.
    pub null_fibre_dimension: usize,
    pub elastic_energy: Option<Rat>,
    pub work: ExactWork,
}

impl StaticResponse {
    /// Solve for one declared forcing.
    pub fn solve(
        stiffness: &ConditionedStiffness,
        null: &NullFibre,
        metric: &DeclaredMetric,
        gauge: ResponseGauge,
        force: &[Rat],
    ) -> Result<Self, StaticResponseError> {
        let width = stiffness.coordinate_freedoms;
        if force.len() != width || metric.matrix.rows() != width {
            return Err(StaticResponseError::Linear(ExactLinearError::ShapeMismatch));
        }
        null.validate_against(stiffness)?;
        let pairing = null.compatibility_pairing(force)?;
        let compatible = pairing.iter().all(Rat::is_zero);

        let mut work = ExactWork::nothing();
        let zero_vector = vec![Rat::zero(); width];

        if !compatible {
            // `(I − P) f = Z (Z*Z)^{-1} Z* f` — the part of the forcing that lives in the kernel.
            // It is returned, not removed: solving `K dq = P f` instead is a different receiver.
            let retained = kernel_component(&null.basis, force)?;
            let obstruction = stiffness.matrix.preimage_obstruction(force)?;
            return Ok(Self {
                schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
                gauge: gauge.name().to_owned(),
                metric: metric.name.clone(),
                force: force.to_vec(),
                compatibility_pairing: pairing,
                compatible: false,
                retained_incompatible_force: retained,
                obstruction,
                displacement: None,
                equilibrium_residual: zero_vector.clone(),
                gauge_residual: zero_vector,
                null_fibre_dimension: null.dimension,
                elastic_energy: None,
                work,
            });
        }

        let (fibre, solve_work) = stiffness.matrix.preimage_fibre_with_work(force)?;
        work = work.then(&solve_work);
        let (particular, fibre_kernel) =
            fibre.ok_or(StaticResponseError::CompatibleForcingHasNoPreimage)?;
        if fibre_kernel.len() != null.dimension {
            return Err(StaticResponseError::NullFibreDisagrees {
                measured: null.dimension,
                returned: fibre_kernel.len(),
            });
        }

        let displacement = match gauge {
            ResponseGauge::MetricComplement => gauge_fix(&null.basis, &metric.matrix, &particular)?,
        };

        let image = stiffness.matrix.apply(&displacement)?;
        let equilibrium_residual: Vec<Rat> = image
            .iter()
            .zip(force)
            .map(|(left, right)| left - right)
            .collect();
        if equilibrium_residual.iter().any(|entry| !entry.is_zero()) {
            return Err(StaticResponseError::EquilibriumResidualIsNotZero);
        }
        let metric_image = metric.matrix.apply(&displacement)?;
        let gauge_residual = {
            let mut residual = Vec::with_capacity(null.dimension);
            for vector in &null.basis {
                residual.push(dot(vector, &metric_image));
            }
            residual
        };
        if gauge_residual.iter().any(|entry| !entry.is_zero()) {
            return Err(StaticResponseError::GaugeResidualIsNotZero);
        }
        let energy = stiffness.energy(&displacement)?;

        Ok(Self {
            schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
            gauge: gauge.name().to_owned(),
            metric: metric.name.clone(),
            force: force.to_vec(),
            compatibility_pairing: pairing,
            compatible: true,
            retained_incompatible_force: zero_vector,
            obstruction: None,
            displacement: Some(displacement),
            equilibrium_residual,
            gauge_residual,
            null_fibre_dimension: null.dimension,
            elastic_energy: Some(energy),
            work,
        })
    }

    /// **A different receiver, labelled as one.**
    ///
    /// Solves `K δq = P f` for the *Euclidean* projected forcing in the standard coordinate
    /// pairing. This answers a question the declared one did not ask: it silently replaces the
    /// forcing by its compatible shadow. The declared metric is used only for the returned gauge;
    /// this receiver deliberately does not claim a metric-weighted least-squares projection.
    pub fn least_squares_projection(
        stiffness: &ConditionedStiffness,
        null: &NullFibre,
        metric: &DeclaredMetric,
        gauge: ResponseGauge,
        force: &[Rat],
    ) -> Result<(Self, Vec<Rat>, &'static str), StaticResponseError> {
        let retained = kernel_component(&null.basis, force)?;
        let projected: Vec<Rat> = force
            .iter()
            .zip(&retained)
            .map(|(left, right)| left - right)
            .collect();
        let response = Self::solve(stiffness, null, metric, gauge, &projected)?;
        Ok((
            response,
            retained,
            "LEAST-SQUARES PROJECTION RECEIVER (EUCLIDEAN; standard coordinate pairing): the \
             declared forcing was replaced by P f. This is not the declared static response and it \
             does not answer the declared forcing.",
        ))
    }
}

/// `(I − P) f = Z (Z*Z)^{-1} Z* f`, the component of `f` inside `span Z`.
fn kernel_component(basis: &[Vec<Rat>], force: &[Rat]) -> Result<Vec<Rat>, StaticResponseError> {
    if basis.is_empty() {
        return Ok(vec![Rat::zero(); force.len()]);
    }
    let dimension = basis.len();
    let gram_rows: Vec<Vec<Rat>> = basis
        .iter()
        .map(|left| basis.iter().map(|right| dot(left, right)).collect())
        .collect();
    let gram = ExactRatMatrix::shaped(dimension, dimension, gram_rows)?;
    let inverse = gram
        .inverse()
        .map_err(|_| StaticResponseError::NullFibreBasisIsDependent)?;
    let pairing: Vec<Rat> = basis.iter().map(|vector| dot(vector, force)).collect();
    let coefficients = inverse.apply(&pairing)?;
    let mut component = vec![Rat::zero(); force.len()];
    for (vector, coefficient) in basis.iter().zip(&coefficients) {
        for (slot, entry) in component.iter_mut().zip(vector) {
            *slot += entry * coefficient;
        }
    }
    Ok(component)
}

/// `δq = x₀ − Z (Z* G Z)^{-1} Z* G x₀`: the representative of `x₀ + span Z` with `Z* G δq = 0`.
fn gauge_fix(
    basis: &[Vec<Rat>],
    metric: &ExactRatMatrix,
    particular: &[Rat],
) -> Result<Vec<Rat>, StaticResponseError> {
    if basis.is_empty() {
        return Ok(particular.to_vec());
    }
    let dimension = basis.len();
    let metric_basis: Vec<Vec<Rat>> = basis
        .iter()
        .map(|vector| metric.apply(vector))
        .collect::<Result<_, _>>()?;
    let gram_rows: Vec<Vec<Rat>> = basis
        .iter()
        .map(|left| metric_basis.iter().map(|right| dot(left, right)).collect())
        .collect();
    let gram = ExactRatMatrix::shaped(dimension, dimension, gram_rows)?;
    let inverse = gram
        .inverse()
        .map_err(|_| StaticResponseError::GaugeIsDegenerate)?;
    let pairing: Vec<Rat> = metric_basis
        .iter()
        .map(|vector| dot(vector, particular))
        .collect();
    let coefficients = inverse.apply(&pairing)?;
    let mut displacement = particular.to_vec();
    for (vector, coefficient) in basis.iter().zip(&coefficients) {
        for (slot, entry) in displacement.iter_mut().zip(vector) {
            *slot -= entry * coefficient;
        }
    }
    Ok(displacement)
}

// -------------------------------------------------------------------------------------------
// 6. the oriented quadrance receiver
// -------------------------------------------------------------------------------------------

/// **The oriented pairwise-quadrance change of a predicted displacement, linearized and finite.**
///
/// The quadrance `Q_ij = |q_i − q_j|²` is invariant under every rigid motion of space, so the
/// comparison below never needs a superposition and never inherits one. Both changes are exact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuadranceResponse {
    pub schema: String,
    /// Block ordinals, in the order the entries below are written.
    pub pairs: Vec<(usize, usize)>,
    /// `2⟨q_i − q_j, δq_i − δq_j⟩`: the linearized change, the first-order content of the model.
    pub linearized: Vec<Rat>,
    /// `|δq_i − δq_j|²`: the quadratic term the linearization drops.
    pub quadratic_term: Vec<Rat>,
    /// `linearized + quadratic_term`: the finite change of the displaced configuration, exact.
    pub finite: Vec<Rat>,
    pub unit: String,
}

impl QuadranceResponse {
    pub fn measure(
        configuration: &ExactConfiguration,
        displacement: &[Rat],
        pairs: &[(usize, usize)],
        unit: impl Into<String>,
    ) -> Result<Self, StaticResponseError> {
        configuration.validated()?;
        let dimension = configuration.dimension();
        let places = configuration.ordered_places();
        if displacement.len() != dimension * places.len() {
            return Err(StaticResponseError::Linear(ExactLinearError::ShapeMismatch));
        }
        let two = integer(2);
        let mut linearized = Vec::with_capacity(pairs.len());
        let mut quadratic = Vec::with_capacity(pairs.len());
        let mut finite = Vec::with_capacity(pairs.len());
        for (lower, upper) in pairs {
            let lower_place = places
                .get(*lower)
                .ok_or(StaticResponseError::BlockOutsideConfiguration { block: *lower })?;
            let upper_place = places
                .get(*upper)
                .ok_or(StaticResponseError::BlockOutsideConfiguration { block: *upper })?;
            let mut first = Rat::zero();
            let mut second = Rat::zero();
            for axis in 0..dimension {
                let separation = &lower_place[axis] - &upper_place[axis];
                let relative = &displacement[lower * dimension + axis]
                    - &displacement[upper * dimension + axis];
                first += &two * &separation * &relative;
                second += &relative * &relative;
            }
            finite.push(&first + &second);
            linearized.push(first);
            quadratic.push(second);
        }
        Ok(Self {
            schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
            pairs: pairs.to_vec(),
            linearized,
            quadratic_term: quadratic,
            finite,
            unit: unit.into(),
        })
    }

    /// The measured change between two configurations over the same pair list: `Q(q₁) − Q(q₀)`.
    ///
    /// This needs no displacement correspondence and no superposition — only the two quadrances.
    /// It is the identity-alignment convenience route; callers comparing differently ordered
    /// configurations must use [`Self::between_with_correspondence`].
    pub fn between(
        source: &ExactConfiguration,
        target: &ExactConfiguration,
        pairs: &[(usize, usize)],
    ) -> Result<Vec<Rat>, StaticResponseError> {
        let correspondence = BlockCorrespondence::identity(
            source.ordered_places().len(),
            target.ordered_places().len(),
        )?;
        Self::between_with_correspondence(source, target, &correspondence, pairs)
    }

    /// The measured change between two configurations using an explicit block correspondence.
    ///
    /// The map is supplied by the caller because block position is a chart address, not semantic
    /// identity. It carries no persistent identity of its own; it only states how this comparison
    /// aligns the two declared configurations.
    pub fn between_with_correspondence(
        source: &ExactConfiguration,
        target: &ExactConfiguration,
        correspondence: &BlockCorrespondence,
        pairs: &[(usize, usize)],
    ) -> Result<Vec<Rat>, StaticResponseError> {
        source.validated()?;
        target.validated()?;
        if source.dimension() != target.dimension() {
            return Err(StaticResponseError::Linear(ExactLinearError::ShapeMismatch));
        }
        correspondence.validate(source.ordered_places().len(), target.ordered_places().len())?;
        let dimension = source.dimension();
        let from = source.ordered_places();
        let to = target.ordered_places();
        let mut changes = Vec::with_capacity(pairs.len());
        for (lower, upper) in pairs {
            let target_lower = correspondence.target_for(*lower)?;
            let target_upper = correspondence.target_for(*upper)?;
            let quadrance = |places: &[Vec<Rat>],
                             lower: usize,
                             upper: usize|
             -> Result<Rat, StaticResponseError> {
                let a = places
                    .get(lower)
                    .ok_or(StaticResponseError::BlockOutsideConfiguration { block: lower })?;
                let b = places
                    .get(upper)
                    .ok_or(StaticResponseError::BlockOutsideConfiguration { block: upper })?;
                let mut total = Rat::zero();
                for axis in 0..dimension {
                    let difference = &a[axis] - &b[axis];
                    total += &difference * &difference;
                }
                Ok(total)
            };
            changes.push(
                quadrance(&to, target_lower, target_upper)? - quadrance(&from, *lower, *upper)?,
            );
        }
        Ok(changes)
    }
}

/// A caller-declared alignment from source block ordinals to target block ordinals.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockCorrespondence {
    source_to_target: Vec<usize>,
}

impl BlockCorrespondence {
    pub fn identity(
        source_blocks: usize,
        target_blocks: usize,
    ) -> Result<Self, StaticResponseError> {
        if source_blocks != target_blocks {
            return Err(StaticResponseError::CorrespondenceIsNotInjective);
        }
        Ok(Self {
            source_to_target: (0..source_blocks).collect(),
        })
    }

    /// Declare a source-block to target-block map. Every source block must be mapped exactly once;
    /// target blocks may contain additional unresolved material outside the compared source chart.
    pub fn declared(
        source_blocks: usize,
        target_blocks: usize,
        source_to_target: Vec<usize>,
    ) -> Result<Self, StaticResponseError> {
        let correspondence = Self { source_to_target };
        correspondence.validate(source_blocks, target_blocks)?;
        Ok(correspondence)
    }

    fn validate(
        &self,
        source_blocks: usize,
        target_blocks: usize,
    ) -> Result<(), StaticResponseError> {
        let mut seen = std::collections::BTreeSet::new();
        if self.source_to_target.len() != source_blocks
            || self
                .source_to_target
                .iter()
                .any(|target| *target >= target_blocks)
            || self
                .source_to_target
                .iter()
                .any(|target| !seen.insert(*target))
        {
            return Err(StaticResponseError::CorrespondenceIsNotInjective);
        }
        Ok(())
    }

    fn target_for(&self, source_block: usize) -> Result<usize, StaticResponseError> {
        self.source_to_target.get(source_block).copied().ok_or(
            StaticResponseError::BlockOutsideConfiguration {
                block: source_block,
            },
        )
    }
}

/// **Signed agreement between a predicted and a measured quadrance change.**
///
/// `cosine_square` is reported **beside** `sign` and never instead of it: it scores `−p`
/// identically to `p`, so on its own it cannot tell a response from its opposite.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrientedAgreement {
    pub schema: String,
    pub entries: usize,
    /// `⟨p, m⟩`, exact.
    pub pairing: Rat,
    /// `‖p‖²`, exact.
    pub predicted_quadrance: Rat,
    /// `‖m‖²`, exact.
    pub measured_quadrance: Rat,
    /// The exact sign of the pairing: `+1` agreement, `−1` opposition, `0` orthogonal.
    pub sign: i8,
    /// `⟨p,m⟩² / (‖p‖² ‖m‖²)`, exact — the **unoriented** face, additional and not sufficient.
    pub cosine_square: Option<Rat>,
    /// `‖m − p‖²` at the declared scale.
    pub residual_quadrance: Rat,
    /// `⟨p,m⟩/‖p‖²` — the scale the declared response would need. **A diagnostic only.** It is
    /// computed from the held-out measurement, so it enters no score here and no forcing.
    pub scale_diagnostic: Option<Rat>,
    /// `‖m − s p‖²` at that diagnostic scale, reported so the diagnostic cannot masquerade as the
    /// residual of the declared response.
    pub residual_quadrance_at_diagnostic_scale: Option<Rat>,
    pub unoriented_face_is_not_sufficient: String,
}

impl OrientedAgreement {
    pub fn between(predicted: &[Rat], measured: &[Rat]) -> Result<Self, StaticResponseError> {
        if predicted.len() != measured.len() {
            return Err(StaticResponseError::Linear(ExactLinearError::ShapeMismatch));
        }
        let pairing = dot(predicted, measured);
        let predicted_quadrance = dot(predicted, predicted);
        let measured_quadrance = dot(measured, measured);
        let sign = if pairing.is_zero() {
            0
        } else if pairing.is_positive() {
            1
        } else {
            -1
        };
        let cosine_square = if predicted_quadrance.is_zero() || measured_quadrance.is_zero() {
            None
        } else {
            Some((&pairing * &pairing) / (&predicted_quadrance * &measured_quadrance))
        };
        let residual_quadrance = predicted
            .iter()
            .zip(measured)
            .fold(Rat::zero(), |sum, (p, m)| {
                let difference = m - p;
                sum + &difference * &difference
            });
        let (scale_diagnostic, residual_at_scale) = if predicted_quadrance.is_zero() {
            (None, None)
        } else {
            let scale = &pairing / &predicted_quadrance;
            let residual = predicted
                .iter()
                .zip(measured)
                .fold(Rat::zero(), |sum, (p, m)| {
                    let difference = m - &scale * p;
                    sum + &difference * &difference
                });
            (Some(scale), Some(residual))
        };
        Ok(Self {
            schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
            entries: predicted.len(),
            pairing,
            predicted_quadrance,
            measured_quadrance,
            sign,
            cosine_square,
            residual_quadrance,
            scale_diagnostic,
            residual_quadrance_at_diagnostic_scale: residual_at_scale,
            unoriented_face_is_not_sufficient:
                "cos^2 scores an opposite response identically; the sign is the oriented reading \
                 and cos^2 is an additional unoriented face"
                    .to_owned(),
        })
    }
}

// -------------------------------------------------------------------------------------------
// 7. the response family, and the neck identification that is withheld
// -------------------------------------------------------------------------------------------

/// **Why no neck section may be read off this response.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NeckIdentification {
    /// `K` is singular, so `H(0) = C(−A)⁻¹B` does not exist and `C K⁺ B` is a different operator.
    WithheldSingularStiffness {
        null_dimension: usize,
        counterexample: String,
    },
}

/// **The full admissible forcing family and the exact rank of the response it generates.**
///
/// [proved-derived; implemented-exact] The certified statement is about the *operator*: restricted
/// to `{f : Z* f = 0}` the gauge-fixed response `f ↦ δq` is a linear bijection onto
/// `{δq : Z* G δq = 0}`, so its rank is `rank K`. For a declared `B`, admissible parameters are
/// the full kernel of `Z*B`; an individual column can be incompatible while a linear combination
/// of incompatible columns is compatible. This is read by solving a basis of `ker(Z*B)` and then
/// taking the exact rank of the resulting force and displacement families. A single observed
/// displacement cannot produce this number; it tests membership and residual against the image.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResponseFamilyReading {
    pub schema: String,
    /// Dimension of the admissible parameter family `ker(Z*B)`, not merely individually compatible
    /// columns.
    pub admissible_generators: usize,
    pub inadmissible_generators: Vec<usize>,
    /// `rank` of the forces generated by a basis of `ker(Z*B)`.
    pub force_rank: usize,
    /// `rank` of the displacements they generate.
    pub response_rank: usize,
    /// `rank K`, which the response rank must equal when the admissible span is all of `image K`.
    pub stiffness_rank: usize,
    pub response_rank_equals_force_rank: bool,
    pub neck: NeckIdentification,
    pub one_displacement_does_not_read_a_rank: String,
}

impl ResponseFamilyReading {
    pub fn read(
        stiffness: &ConditionedStiffness,
        null: &NullFibre,
        metric: &DeclaredMetric,
        gauge: ResponseGauge,
        forcing: &ForcingDeclaration,
    ) -> Result<Self, StaticResponseError> {
        let generators = forcing.matrix.columns();
        let width = stiffness.coordinate_freedoms;
        null.validate_against(stiffness)?;
        if forcing.matrix.rows() != width {
            return Err(StaticResponseError::Linear(ExactLinearError::ShapeMismatch));
        }

        // The admissible parameter family is ker(Z*B), not the subset of B's columns that happen
        // to be compatible one at a time. A linear combination of individually incompatible
        // columns can be a valid static forcing.
        let mut compatibility_rows = vec![vec![Rat::zero(); generators]; null.dimension];
        for (row, vector) in null.basis.iter().enumerate() {
            for column in 0..generators {
                let force: Vec<Rat> = (0..width)
                    .map(|at| forcing.matrix.get(at, column).cloned())
                    .collect::<Result<_, _>>()?;
                compatibility_rows[row][column] = dot(vector, &force);
            }
        }
        let compatibility = ExactRatMatrix::shaped(null.dimension, generators, compatibility_rows)?;
        let admissible_parameters = compatibility.kernel_basis()?;
        let mut admissible_forces: Vec<Vec<Rat>> = Vec::new();
        let mut displacements: Vec<Vec<Rat>> = Vec::new();
        let mut inadmissible = Vec::new();

        // Retain the per-column diagnostic for report compatibility; the actual family below is
        // generated from the full nullspace.
        for column in 0..generators {
            let force: Vec<Rat> = (0..width)
                .map(|row| forcing.matrix.get(row, column).cloned())
                .collect::<Result<_, _>>()?;
            let pairing = null.compatibility_pairing(&force)?;
            if !pairing.iter().all(Rat::is_zero) {
                inadmissible.push(column);
            }
        }
        for parameters in &admissible_parameters {
            let force = forcing.matrix.apply(parameters)?;
            let response = StaticResponse::solve(stiffness, null, metric, gauge, &force)?;
            let displacement = response
                .displacement
                .ok_or(StaticResponseError::CompatibleForcingHasNoPreimage)?;
            admissible_forces.push(force);
            displacements.push(displacement);
        }

        let rank_of = |rows: &[Vec<Rat>]| -> Result<usize, StaticResponseError> {
            if rows.is_empty() {
                return Ok(0);
            }
            let matrix = ExactRatMatrix::shaped(rows.len(), width, rows.to_vec())?;
            Ok(matrix.rank()?)
        };
        let force_rank = rank_of(&admissible_forces)?;
        let response_rank = rank_of(&displacements)?;

        Ok(Self {
            schema: CONDITIONED_STATIC_RESPONSE_SCHEMA.to_owned(),
            admissible_generators: admissible_parameters.len(),
            inadmissible_generators: inadmissible,
            force_rank,
            response_rank,
            stiffness_rank: stiffness.rank,
            response_rank_equals_force_rank: force_rank == response_rank,
            neck: NeckIdentification::WithheldSingularStiffness {
                null_dimension: null.dimension,
                counterexample: "on the connected four-site path with K = [[1,-1,0,0],[-1,2,-1,0],\
                     [0,-1,2,-1],[0,0,-1,1]] and cut {1,2}|{3,4} the stiffness cross block has \
                     rank 1 while the Moore-Penrose cross block [[-3,-1],[-5,-3]]/8 has rank 2, \
                     so C K^+ B is not H(0) = C(-A)^{-1} B and the off-pole neck theorem does not \
                     transfer"
                    .to_owned(),
            },
            one_displacement_does_not_read_a_rank:
                "a rank statement needs a basis of the full admissible parameter family ker(Z*B) \
                 or a certified operator factorization; one observed displacement tests membership \
                 and residual against the image"
                    .to_owned(),
        })
    }
}

/// The audit's four-site witness, recomputed exactly: `(stiffness cross rank, pseudoinverse cross
/// rank, the pseudoinverse cross block)`.
///
/// [counterexample; computational-witness] `K⁺ = (K + 11ᵀ/4)⁻¹ − 11ᵀ/4` for this `K`, whose kernel
/// is exactly `span{(1,1,1,1)}`. The two cross ranks differ, which is what withholds the neck
/// identification. Every entry below is a rational; no float is formed.
pub fn neck_cross_block_counterexample(
) -> Result<(usize, usize, Vec<Vec<Rat>>), StaticResponseError> {
    let k = ExactRatMatrix::new(vec![
        vec![integer(1), integer(-1), integer(0), integer(0)],
        vec![integer(-1), integer(2), integer(-1), integer(0)],
        vec![integer(0), integer(-1), integer(2), integer(-1)],
        vec![integer(0), integer(0), integer(-1), integer(1)],
    ])?;
    let quarter = Rat::new(BigInt::from(1), BigInt::from(4));
    let ones = ExactRatMatrix::new(vec![vec![quarter.clone(); 4]; 4])?;
    let pseudo = k.add(&ones)?.inverse()?.subtract(&ones)?;

    // Penrose, checked rather than trusted.
    if k.multiply(&pseudo)?.multiply(&k)? != k {
        return Err(StaticResponseError::PenroseConditionFails);
    }
    if pseudo.multiply(&k)?.multiply(&pseudo)? != pseudo {
        return Err(StaticResponseError::PenroseConditionFails);
    }
    let kp = k.multiply(&pseudo)?;
    if kp != kp.transpose()? {
        return Err(StaticResponseError::PenroseConditionFails);
    }
    let pk = pseudo.multiply(&k)?;
    if pk != pk.transpose()? {
        return Err(StaticResponseError::PenroseConditionFails);
    }

    let cross = |matrix: &ExactRatMatrix| -> Result<(usize, Vec<Vec<Rat>>), StaticResponseError> {
        let rows: Vec<Vec<Rat>> = (2..4)
            .map(|row| {
                (0..2)
                    .map(|column| matrix.get(row, column).cloned())
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<_, _>>()?;
        let block = ExactRatMatrix::shaped(2, 2, rows.clone())?;
        Ok((block.rank()?, rows))
    };
    let (stiffness_rank, _) = cross(&k)?;
    let (pseudo_rank, block) = cross(&pseudo)?;
    Ok((stiffness_rank, pseudo_rank, block))
}

// -------------------------------------------------------------------------------------------
// refusals
// -------------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum StaticResponseError {
    #[error("the exact linear carrier refused: {0}")]
    Linear(#[from] ExactLinearError),
    #[error("the rigidity receiver refused: {0}")]
    Rigidity(#[from] Box<RigidityError>),
    #[error(
        "constraint {constraint} carries a negative spring constant; W must be positive semidefinite"
    )]
    NegativeStiffness { constraint: usize },
    #[error(
        "the declaration carries {declared} spring constants for {constraints} constraints; a stiffness is declared per constraint and never broadcast"
    )]
    StiffnessPopulationDisagrees { declared: usize, constraints: usize },
    #[error(
        "constraint {constraint} is coincident, so l^2 = 0 and gamma/(4 l^2) does not exist; a loaded zero-length spring is a modelling question and not a division"
    )]
    CoincidentConstraintIsLoaded { constraint: usize },
    #[error("K is not self-adjoint at ({row}, {column}); the declared pairing does not hold")]
    StiffnessIsNotSelfAdjoint { row: usize, column: usize },
    #[error("a trivial motion of the configuration is outside ker K")]
    TrivialMotionOutsideStiffnessKernel,
    #[error("the declared metric is not square")]
    MetricIsNotSquare,
    #[error("the declared metric is not symmetric at ({row}, {column})")]
    MetricIsNotSymmetric { row: usize, column: usize },
    #[error("a forcing family with no generator declares no force")]
    EmptyForcingFamily,
    #[error("a pinch between block {block} and itself is not a pair")]
    PinchIsNotAPair { block: usize },
    #[error(
        "blocks {lower} and {upper} are coincident, so the pinch has no direction; a contact site does not supply one"
    )]
    PinchIsCoincident { lower: usize, upper: usize },
    #[error("block {block} is outside the declared configuration")]
    BlockOutsideConfiguration { block: usize },
    #[error("B carries {columns} columns for {generators} declared generators")]
    ForcingPopulationDisagrees { columns: usize, generators: usize },
    #[error("the declared force family carries {declared} magnitudes for {generators} generators")]
    ForceFamilyDisagrees { declared: usize, generators: usize },
    #[error(
        "Z* f vanishes but K dq = f has no preimage; the stiffness kernel and its image disagree and the reading is refused rather than repaired"
    )]
    CompatibleForcingHasNoPreimage,
    #[error(
        "the measured null fibre has dimension {measured} and the solve returned {returned}; the kernel is not the same kernel"
    )]
    NullFibreDisagrees { measured: usize, returned: usize },
    #[error("the returned displacement does not satisfy K dq = f exactly")]
    EquilibriumResidualIsNotZero,
    #[error("the returned displacement does not satisfy the declared gauge exactly")]
    GaugeResidualIsNotZero,
    #[error("the null fibre basis is linearly dependent; its Gram matrix is singular")]
    NullFibreBasisIsDependent,
    #[error(
        "the declared null-fibre dimension {declared} disagrees with its basis length {basis}"
    )]
    NullFibreDimensionFieldDisagrees { declared: usize, basis: usize },
    #[error("a declared null-fibre basis vector is not in the stiffness kernel")]
    NullFibreBasisVectorNotInKernel,
    #[error("Z* G Z is singular, so the declared gauge does not select a representative")]
    GaugeIsDegenerate,
    #[error("the block correspondence is not injective over the declared source chart")]
    CorrespondenceIsNotInjective,
    #[error(
        "the four-site witness failed a Penrose condition; the counterexample is not what it claims"
    )]
    PenroseConditionFails,
}

impl From<RigidityError> for StaticResponseError {
    fn from(error: RigidityError) -> Self {
        Self::Rigidity(Box::new(error))
    }
}

#[cfg(test)]
mod tests;
