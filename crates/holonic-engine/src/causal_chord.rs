//! **The causal chord: the exact transfer object of a linearization, and its resolvent.**
//!
//! [definition] This is receiver **R1** of
//! `docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md`. For a local linearization
//!
//! ```text
//! x' = A x + B u,    y = C x
//! ```
//!
//! the receiver-relative transfer object is `H(s) = C (sI − A)^{-1} B`. This module owns it as an
//! **exact matrix of rational functions over `Q`** — never a float, never a sampled frequency
//! response — together with everything the plan says a returned component must carry: its source
//! lineage, its excitation (which column of `B`), its transport path (which row of `C`), its
//! approximation error (exactly zero, or a stated isolating interval used only as a readout) and
//! its residual (exactly zero, certified **coefficientwise**: `(sI−A)·adj(sI−A) = det(sI−A)·I` and
//! `num_{ij}(s) = (C adj(sI−A) B)_{ij}` are verified as polynomial identities, one matrix equation
//! per power of `s`, not sampled at a point).
//!
//! The paired Lean owner is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/CausalChord.lean`
//! (`Soma.Holonics.Foundation.CausalChord`). Each theorem there appears here as a test or an
//! invariant; each definition here is the executable equivalent of the Lean object.
//!
//! # The governing correction: no object has one intrinsic chord
//!
//! [definition] The plan's first clause is that **isospectral objects exist**, so one global
//! spectrum cannot identify an arbitrary source. That is not a caveat attached to this module, it
//! is the reason the module returns what it returns. [`separate_under_probe`] takes two
//! linearizations with *identical characteristic polynomials* and returns the probe/readout pair at
//! which their responses differ; the test
//! `cospectral_graphs_are_separated_by_the_response_atlas` runs it on a genuine pair of
//! Laplacian-cospectral non-isomorphic graphs on six vertices. The Lean counterpart is
//! `spectrum_does_not_determine_response`, and its positive half is
//! `full_atlas_determines_the_operator_fin_two`: the *complete* probe atlas does determine the
//! operator, while the spectrum does not. Identity lives in the response atlas under active
//! probing.
//!
//! # How the transfer object is built, exactly
//!
//! [proved-standard; implemented-exact] One exact Faddeev–LeVerrier recurrence returns both halves
//! of `C adj(sI−A) B / det(sI−A)` at once. With `M_0 = 0` and, for `k = 1..n`,
//!
//! ```text
//! M_k = A M_{k-1} + c_{n-k+1} I,      c_{n-k} = − tr(A M_k) / k
//! ```
//!
//! the characteristic polynomial is `det(sI−A) = Σ_k c_k s^k` and the adjugate is
//! `adj(sI−A) = Σ_{k=1}^{n} M_k s^{n−k}`. [`ResolventExpansion`] carries both. The scalar half is
//! already owned by [`holonics::exact_linear::ExactRatMatrix::characteristic_polynomial`]
//! (`exact_linear.rs:336`), which discards the intermediate `M_k`; this module recomputes the
//! recurrence because it needs them, and
//! `the_expansion_agrees_with_the_existing_characteristic_owner` holds the two to exact agreement
//! at every reading. Nothing here reimplements rank, kernel, inverse or spectrum: those are
//! `exact_linear.rs:761/770/543` and [`crate::lattice_gauge::exact_spectrum`]
//! (`lattice_gauge.rs:1039`).
//!
//! # Cancellation is reported, never lost
//!
//! [definition] `C_i adj(sI−A) B_j / det(sI−A)` is not in lowest terms. The common factor is
//! exactly the modes that source `j` cannot excite or receiver `i` cannot observe — the
//! uncontrollable and unobservable directions — and the plan requires them **visible as
//! cancellations and reported**. [`TransferEntry`] therefore carries the raw numerator and
//! denominator, the exact polynomial `cancelled` gcd, and the reduced pair. [`TransferFunction`]
//! additionally carries `atlas_cancellation`: `det(sI−A)` divided by the least common multiple of
//! the reduced entry denominators, which is the population of modes invisible to the **whole**
//! declared atlas. [`ModeSupport`] names them structurally at each rational eigenvalue, by
//! exhibiting the right and left eigenvectors and the sources and receivers that pair nontrivially
//! with them.
//!
//! # Poles: the polynomial factor is the exact object, an interval is only a readout
//!
//! [definition] [`pole_atlas`] squarefree-factors the reduced denominator with
//! [`holonics::rational_polynomial::RationalPolynomial::squarefree_decomposition`], so each pole
//! carries its **multiplicity as an index, not a guess**. Rational poles are returned as exact
//! rationals. Every other pole is named by the exact squarefree factor it is a root of. Under
//! [`PoleReading::Certified`] each factor additionally reports Sturm-certified isolating boxes for
//! its real roots — obtained from the existing owner
//! [`holonics::rational_polynomial::rational_root_census`] (`rational_polynomial.rs:1110`), whose
//! isolation is for the monic companion `c^{n−1}A(z/c)` and is rescaled here by the leading
//! coefficient — and a sign-certified half-plane count. **The interval is a readout. The factor is
//! the pole's name.**
//!
//! [proved-derived; implemented-exact] The half-plane count was the one piece of polynomial
//! machinery this module had to write, because the repository had no owner for it. **It is no
//! longer this module's**: the signed remainder sequence a Cauchy index reads is the Sturm chain
//! read at `±∞` instead of at a point, so the routine lives in
//! [`crate::rational_polynomial`] beside [`holonics::exact_value::SturmChain`] and the root census,
//! and [`half_plane_count`] here is re-entry into it at the same signature. The three steps are
//! unchanged and are stated at the owner; in outline:
//!
//! 1. **Axis roots, with multiplicity.** Write `p(iω) = P(ω) + i Q(ω)` with `P, Q ∈ Q[ω]`. If `p`
//!    has a root `iω_0` of order `m` then `p(iω)` has a zero of order `m` at the real point `ω_0`,
//!    so `(ω−ω_0)^m` divides both `P` and `Q`, and at least one of the two order-`m` coefficients is
//!    nonzero — hence **the multiplicity of `iω_0` in `p` is exactly the multiplicity of `ω_0` as a
//!    real root of `gcd(P,Q)`**. That count is taken by squarefree decomposition plus the existing
//!    Sturm owner.
//! 2. **Left and right, by the Cauchy index.** For `p` of degree `n` with no axis roots, the
//!    argument principle on the half-plane contour gives `Δ arg p(iω) = π(n − 2k)` for `k` the
//!    right-half-plane count. Writing the continuous argument against `arctan` and counting the
//!    jumps of the ratio at the zeros of the denominator gives
//!    `k = (n + I(Q/P))/2` for `n` even and `k = (n − I(P/Q))/2` for `n` odd, where `I` is the
//!    Cauchy index over `(−∞, +∞)`, computed as `V(−∞) − V(+∞)` on the signed remainder sequence
//!    `f_0, f_1, f_{i+1} = −rem(f_{i−1}, f_i)`. This is Routh–Hurwitz in its Sturm form, and it is
//!    exact rational arithmetic throughout.
//! 3. **The shift, with a self-certifying stop.** `p` itself may have axis roots, so the left and
//!    right counts are read at a rational shift `σ > 0`: `#{Re λ < −σ}` from `p(s−σ)` and
//!    `#{Re λ > σ}` from `p(s+σ)`. The loop halves `σ` until `left + axis + right = n`, which is
//!    exactly the certificate that no non-axis root has `|Re λ| ≤ σ`. It terminates because there
//!    are finitely many distinct real parts, and it carries a declared refinement ceiling so a
//!    hostile polynomial returns a named refusal rather than running forever.
//!
//! [definition] When `A` is symmetric the whole question is already owned: the spectrum is real and
//! the half-plane count **is** Sylvester's signature. [`half_plane_from_symmetric`] routes to
//! [`holonics::inertia::inertia`] (`inertia.rs:375`), and [`rate_form_congruence`] routes a chart
//! change to [`holonics::inertia::congruence`] (`inertia.rs:597`), which refuses a singular chart by
//! name. This is the connection
//! `research/records/2026-09-15_INTEGRATING_AND_DIFFERENTIATING_ROLES_SHARE_ONE_CURRENT.md` asks
//! for — "the intention is to connect that owner to the rate reading, not to build a second one."
//!
//! # Non-normal operators: the resolvent, not the spectrum, governs response
//!
//! [proved-derived; implemented-exact] The plan is explicit that for a non-normal `A` the
//! eigenvalues omit the transient amplification, so the receiver must read the resolvent.
//! [`resolvent_probe`] builds `(sI − A)^{-1}` **exactly at a Gaussian-rational probe point**
//! `s = σ + iω`, by realifying `sI − A` over `Q` as the `2n × 2n` block matrix
//! `[[σI − A, −ωI], [ωI, σI − A]]` and inverting it with the existing exact inverse. No float and
//! no complex floating type appears; the returned real and imaginary parts are exact rational
//! matrices and the identity `(sI−A)(sI−A)^{-1} = I` is re-checked to exact zero residual.
//!
//! [`jordan_realification`] and [`semisimple_realification`] are the worked case. Both are `4 × 4`
//! rational matrices, both have characteristic polynomial `(s²+1)²`, and both have their entire
//! spectrum on the imaginary axis. They are the realifications of `[[i,1],[0,i]]` and
//! `diag(i,i)`. Their **minimal** polynomials differ — `(s²+1)²` against `s²+1` — and so do their
//! resolvents: probed at `s = i + δ` the Jordan resolvent grows like `δ^{-2}` and the semisimple
//! one like `δ^{-1}`, which the test
//! `the_jordan_resolvent_grows_two_orders_faster_than_the_semisimple_one_at_the_same_spectrum`
//! asserts by exact rational comparison at declared `δ`. The Lean counterparts are
//! `jordan_eigenvalue_eq_I` and `jordan_has_no_conserving_receiver`.
//!
//! # The rate form and the seam
//!
//! [proved-derived] With a constant symmetric metric `G` and `x' = A x`, the source-free change of
//! `E_G = xᵀGx/2` is governed by `Σ_G = AᵀG + GA` ([`rate_form`]). Putting `A = L − I/2` gives
//! `Σ_G = LᵀG + GL − G` ([`seam_form`]). If `G` is positive definite, then
//!
//! ```text
//! L*G + GL = G   ⟺   L − I/2 is G-skew   ⟹   every eigenvalue of L has Re = 1/2.
//! ```
//!
//! Positive definiteness is required for the spectral implication: an indefinite conserving
//! form can carry real eigenvalues. For example `G = diag(1,-1)` and
//! `A = [[0,1],[1,0]]` have `AᵀG + GA = 0` but eigenvalues `1,-1`.
//! **The converse is false as usually stated**: it needs
//! semisimplicity, and [`jordan_realification`] is the counterexample — purely imaginary spectrum,
//! non-squarefree minimal polynomial, and no positive definite `G` making it `G`-skew.
//! [`is_semisimple`] decides that exactly, as "the minimal polynomial equals its own squarefree
//! part", through [`holonics::exact_linear::ExactRatMatrix::minimal_polynomial`]
//! (`exact_linear.rs:367`). A defective generator can sit on the seam spectrally and still have no
//! conserving receiver.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use holonics::geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use holonics::exact_linear::{ExactLinearError, ExactRatMatrix};
use holonics::exact_value::{ExactInterval, ExactValueError};
use holonics::inertia::{Inertia, InertiaError, SymmetricForm, congruence, inertia};
use holonics::rational_polynomial::{
    ExactPolynomialError, RationalPolynomial, rational_root_census, rational_roots_by_lifting,
};

/// Serialized schema name for a returned chord.
pub const CAUSAL_CHORD_SCHEMA: &str = "holonics.causal-chord.v1";

// -------------------------------------------------------------------------------------------------
// the linearization

/// **A local linearization `(A, B, C)` in exact rationals, with named ports.**
///
/// The names are not decoration: the plan requires every returned component to carry its source and
/// its transport path, so a column of `B` and a row of `C` each carry the name the caller declared
/// for it, and [`ChordComponent`] repeats both.
///
/// A remounted linearization passes through [`Linearization::declared`]: the wire carries the same
/// fields, and one whose excitation, readout or port-name counts do not agree with the state it
/// carries is refused at the boundary rather than reconstructed past the constructor. The declared
/// schema label is carried through unchanged, so a remounted chart is the chart it was.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "LinearizationWire")]
pub struct Linearization {
    pub schema: String,
    pub lineage: String,
    /// `A`, `n × n`.
    pub state: ExactRatMatrix,
    /// `B`, `n × m`. Column `j` is source port `j`.
    pub excitation: ExactRatMatrix,
    /// `C`, `p × n`. Row `i` is receiver port `i`.
    pub readout: ExactRatMatrix,
    /// One name per column of `B`.
    pub sources: Vec<String>,
    /// One name per row of `C`.
    pub receivers: Vec<String>,
}

#[derive(Deserialize)]
struct LinearizationWire {
    schema: String,
    lineage: String,
    state: ExactRatMatrix,
    excitation: ExactRatMatrix,
    readout: ExactRatMatrix,
    sources: Vec<String>,
    receivers: Vec<String>,
}

impl TryFrom<LinearizationWire> for Linearization {
    type Error = ChordRefusal;

    fn try_from(wire: LinearizationWire) -> Result<Self, Self::Error> {
        let mut remounted = Self::declared(
            wire.lineage,
            wire.state,
            wire.excitation,
            wire.readout,
            wire.sources,
            wire.receivers,
        )?;
        // `declared` stamps this module's current schema constant. The wire's own label is what
        // the chart declared itself to be, so it is carried through rather than overwritten; every
        // shape the constructor checks has been re-checked above it.
        remounted.schema = wire.schema;
        Ok(remounted)
    }
}

impl Linearization {
    /// A declared linearization, with every shape checked against every other.
    ///
    /// The port-name vectors are exterior declarations and are checked against the matrix shapes
    /// rather than trusted: a caller who declares three sources for a two-column `B` is refused by
    /// name, and nothing is allocated from the declared counts.
    pub fn declared(
        lineage: impl Into<String>,
        state: ExactRatMatrix,
        excitation: ExactRatMatrix,
        readout: ExactRatMatrix,
        sources: Vec<String>,
        receivers: Vec<String>,
    ) -> Result<Self, ChordRefusal> {
        if !state.is_square() {
            return Err(ChordRefusal::StateNotSquare {
                rows: state.rows(),
                columns: state.columns(),
            });
        }
        let extent = state.rows();
        if extent == 0 {
            return Err(ChordRefusal::EmptyState);
        }
        if excitation.rows() != extent {
            return Err(ChordRefusal::ExcitationShape {
                extent,
                rows: excitation.rows(),
            });
        }
        if readout.columns() != extent {
            return Err(ChordRefusal::ReadoutShape {
                extent,
                columns: readout.columns(),
            });
        }
        if sources.len() != excitation.columns() {
            return Err(ChordRefusal::SourceNameCount {
                declared: sources.len(),
                columns: excitation.columns(),
            });
        }
        if receivers.len() != readout.rows() {
            return Err(ChordRefusal::ReceiverNameCount {
                declared: receivers.len(),
                rows: readout.rows(),
            });
        }
        Ok(Self {
            schema: CAUSAL_CHORD_SCHEMA.to_owned(),
            lineage: lineage.into(),
            state,
            excitation,
            readout,
            sources,
            receivers,
        })
    }

    /// A single-input single-output probe of a square operator: excite state coordinate `probe`,
    /// read state coordinate `readout`.
    pub fn single_probe(
        lineage: impl Into<String>,
        state: ExactRatMatrix,
        probe: usize,
        readout_site: usize,
    ) -> Result<Self, ChordRefusal> {
        if !state.is_square() {
            return Err(ChordRefusal::StateNotSquare {
                rows: state.rows(),
                columns: state.columns(),
            });
        }
        let extent = state.rows();
        if probe >= extent || readout_site >= extent {
            return Err(ChordRefusal::PortOutsideState {
                extent,
                port: probe.max(readout_site),
            });
        }
        let column = (0..extent)
            .map(|index| {
                vec![if index == probe {
                    Rat::one()
                } else {
                    Rat::zero()
                }]
            })
            .collect::<Vec<_>>();
        let row = vec![
            (0..extent)
                .map(|index| {
                    if index == readout_site {
                        Rat::one()
                    } else {
                        Rat::zero()
                    }
                })
                .collect::<Vec<_>>(),
        ];
        Self::declared(
            lineage,
            state,
            ExactRatMatrix::shaped(extent, 1, column)?,
            ExactRatMatrix::shaped(1, extent, row)?,
            vec![format!("probe@{probe}")],
            vec![format!("readout@{readout_site}")],
        )
    }

    pub fn extent(&self) -> usize {
        self.state.rows()
    }

    pub fn source_count(&self) -> usize {
        self.excitation.columns()
    }

    pub fn receiver_count(&self) -> usize {
        self.readout.rows()
    }

    /// **The chart change.** `(A, B, C) ↦ (T A T^{-1}, T B, C T^{-1})`.
    ///
    /// The Lean owner's `rebase_numerator` / `rebase_denominator` / `rebase_transfer` prove that the
    /// transfer object is invariant under this, which is exactly why it is a *chart* change and not
    /// a different object. A singular `T` is refused by name, for the same reason
    /// [`holonics::inertia::congruence`] refuses one.
    pub fn rebased(&self, chart: &ExactRatMatrix) -> Result<Self, ChordRefusal> {
        if !chart.is_square() || chart.rows() != self.extent() {
            return Err(ChordRefusal::ChartShape {
                extent: self.extent(),
                rows: chart.rows(),
                columns: chart.columns(),
            });
        }
        let inverse = chart
            .inverse()
            .map_err(|_| ChordRefusal::SingularChart)?;
        Ok(Self {
            schema: self.schema.clone(),
            lineage: format!("{}|rebased", self.lineage),
            state: chart.multiply(&self.state)?.multiply(&inverse)?,
            excitation: chart.multiply(&self.excitation)?,
            readout: self.readout.multiply(&inverse)?,
            sources: self.sources.clone(),
            receivers: self.receivers.clone(),
        })
    }
}

// -------------------------------------------------------------------------------------------------
// the resolvent expansion

/// **`det(sI−A)` and `adj(sI−A)` from one exact Faddeev–LeVerrier recurrence.**
///
/// `adjugate[j]` is the matrix multiplying `s^{extent − 1 − j}`, so
/// `adj(sI−A) = Σ_j adjugate[j] · s^{extent−1−j}`.
///
/// **A remounted expansion re-runs its own certificate.** The expansion does not carry `A`, but it
/// determines it: the coefficient identities force `M_1 = I` and `M_2 − A M_1 = c_{n−1} I`, so
/// `A = adjugate[1] − c_{n−1} I` (and `A = −c_0 I` at extent one). That recovered operator is fed
/// back through [`certify_adjugate`], which re-derives all `extent + 1` matrix coefficient
/// identities of `(sI−A)·adj(sI−A) = det(sI−A)·I` — the same work the constructor did, so the
/// remount costs what the construction cost. A forged adjugate coefficient, a characteristic that
/// is not monic of the declared degree, a certified-coefficient count that is not `extent + 1` and
/// a residual that is not exactly zero are each refused by name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ResolventExpansionWire")]
pub struct ResolventExpansion {
    pub extent: usize,
    /// `det(sI − A)`, monic of degree `extent`, ascending coefficients.
    pub characteristic: RationalPolynomial,
    pub adjugate: Vec<ExactRatMatrix>,
    /// How many coefficient identities of `(sI−A)·adj(sI−A) = det(sI−A)·I` were checked. Both
    /// sides are matrix polynomials of degree `extent`, so this is `extent + 1`: **the whole
    /// identity**, not a sample of it.
    pub certified_coefficients: usize,
    /// Exactly zero. The largest absolute entry over every coefficient identity's difference.
    pub residual: Rat,
}

#[derive(Deserialize)]
struct ResolventExpansionWire {
    extent: usize,
    characteristic: RationalPolynomial,
    adjugate: Vec<ExactRatMatrix>,
    certified_coefficients: usize,
    residual: Rat,
}

impl TryFrom<ResolventExpansionWire> for ResolventExpansion {
    type Error = ChordRefusal;

    fn try_from(wire: ResolventExpansionWire) -> Result<Self, Self::Error> {
        if wire.extent == 0 {
            return Err(ChordRefusal::EmptyState);
        }
        if wire.adjugate.len() != wire.extent {
            return Err(ChordRefusal::ExpansionWireDisagrees {
                relation: "the number of adjugate coefficients against the declared extent",
                declared: wire.extent.to_string(),
                derived: wire.adjugate.len().to_string(),
            });
        }
        for block in &wire.adjugate {
            if block.rows() != wire.extent || block.columns() != wire.extent {
                return Err(ChordRefusal::ExpansionWireDisagrees {
                    relation: "an adjugate coefficient's shape against the declared extent",
                    declared: format!("{extent}x{extent}", extent = wire.extent),
                    derived: format!("{}x{}", block.rows(), block.columns()),
                });
            }
        }
        if wire.characteristic.degree() != Some(wire.extent) || !wire.characteristic.is_monic() {
            return Err(ChordRefusal::ExpansionWireDisagrees {
                relation: "the characteristic polynomial as a monic of the declared extent",
                declared: format!("monic of degree {}", wire.extent),
                derived: format!(
                    "degree {:?}, monic {}",
                    wire.characteristic.degree(),
                    wire.characteristic.is_monic()
                ),
            });
        }
        if wire.certified_coefficients != wire.extent + 1 {
            return Err(ChordRefusal::ExpansionWireDisagrees {
                relation: "the certified coefficient count against the declared extent",
                declared: wire.certified_coefficients.to_string(),
                derived: (wire.extent + 1).to_string(),
            });
        }
        if !wire.residual.is_zero() {
            return Err(ChordRefusal::ExpansionWireDisagrees {
                relation: "the certificate residual, which is exactly zero or there is no expansion",
                declared: wire.residual.to_string(),
                derived: "0".to_owned(),
            });
        }
        // `A` is not carried, but the identities determine it: `M_1 = I` and
        // `M_2 − A M_1 = c_{n−1} I`, so `A = M_2 − c_{n−1} I`; at extent one the only identity
        // left is `−A M_1 = c_0 I`.
        let identity = ExactRatMatrix::identity(wire.extent)?;
        let state = if wire.extent == 1 {
            identity.scaled(&-wire.characteristic.coefficient(0))
        } else {
            wire.adjugate[1]
                .subtract(&identity.scaled(&wire.characteristic.coefficient(wire.extent - 1)))?
        };
        let residual = certify_adjugate(&state, &wire.characteristic, &wire.adjugate)?;
        Ok(Self {
            extent: wire.extent,
            characteristic: wire.characteristic,
            adjugate: wire.adjugate,
            certified_coefficients: wire.certified_coefficients,
            residual,
        })
    }
}

impl ResolventExpansion {
    /// `adj(s₀ I − A)` at a rational point, by exact Horner over the stored matrix coefficients.
    pub fn adjugate_at(&self, point: &Rat) -> Result<ExactRatMatrix, ChordRefusal> {
        let mut accumulated = ExactRatMatrix::zero(self.extent, self.extent)?;
        for block in &self.adjugate {
            accumulated = accumulated.scaled(point).add(block)?;
        }
        Ok(accumulated)
    }
}

/// The exact Faddeev–LeVerrier recurrence, keeping the intermediate matrices.
pub fn resolvent_expansion(state: &ExactRatMatrix) -> Result<ResolventExpansion, ChordRefusal> {
    if !state.is_square() {
        return Err(ChordRefusal::StateNotSquare {
            rows: state.rows(),
            columns: state.columns(),
        });
    }
    let extent = state.rows();
    if extent == 0 {
        return Err(ChordRefusal::EmptyState);
    }
    let identity = ExactRatMatrix::identity(extent)?;
    let mut descending = vec![Rat::one()];
    let mut standing = ExactRatMatrix::zero(extent, extent)?;
    let mut adjugate = Vec::with_capacity(extent);
    for step in 1..=extent {
        let last = descending
            .last()
            .cloned()
            .expect("the recurrence always holds its leading coefficient");
        standing = state.multiply(&standing)?.add(&identity.scaled(&last))?;
        adjugate.push(standing.clone());
        let product = state.multiply(&standing)?;
        let trace = (0..extent).try_fold(Rat::zero(), |sum, index| {
            product.get(index, index).map(|entry| sum + entry)
        })?;
        descending.push(-trace / Rat::from_integer(BigInt::from(step as i64)));
    }
    let mut ascending = descending;
    ascending.reverse();
    let characteristic = RationalPolynomial::new(ascending);

    let residual = certify_adjugate(state, &characteristic, &adjugate)?;
    Ok(ResolventExpansion {
        extent,
        characteristic,
        adjugate,
        certified_coefficients: extent + 1,
        residual,
    })
}

/// **The coefficientwise certificate of `(sI−A)·adj(sI−A) = det(sI−A)·I`.**
///
/// [proved-standard; implemented-exact] Both sides are matrix polynomials of degree `n = extent`
/// in `s`, so the identity **is** the `n + 1` matrix equations between their coefficients, and
/// checking all of them is a certificate in the literal sense: the identity is verified, finitely
/// and exactly, not sampled. With `adj(sI−A) = Σ_{k=1}^{n} M_k s^{n−k}` and
/// `det(sI−A) = Σ_{j=0}^{n} c_j s^{n−j}` the coefficient of `s^{n−j}` reads
///
/// ```text
/// j = 0:           M_1              = c_0 I   (= I)
/// 1 ≤ j ≤ n−1:     M_{j+1} − A M_j  = c_j I
/// j = n:                  − A M_n   = c_n I   (Cayley–Hamilton)
/// ```
///
/// which are exactly the Faddeev–LeVerrier recurrences the loop above ran, plus the closing one.
/// **Checking the identity at a single rational point would not be a certificate**: a matrix
/// polynomial identity of degree `n` is implied by its values only at `n + 1` distinct points,
/// and the closing identity — Cayley–Hamilton — is the one the recurrence does not give for free.
fn certify_adjugate(
    state: &ExactRatMatrix,
    characteristic: &RationalPolynomial,
    adjugate: &[ExactRatMatrix],
) -> Result<Rat, ChordRefusal> {
    let extent = adjugate.len();
    let identity = ExactRatMatrix::identity(extent)?;
    let zero = ExactRatMatrix::zero(extent, extent)?;
    let mut residual = Rat::zero();
    for step in 0..=extent {
        // `M_{step+1}`, absent past the top coefficient.
        let leading = match adjugate.get(step) {
            Some(block) => block.clone(),
            None => zero.clone(),
        };
        // `A M_step`, absent below the first.
        let trailing = match step.checked_sub(1).and_then(|at| adjugate.get(at)) {
            Some(block) => state.multiply(block)?,
            None => zero.clone(),
        };
        let left = leading.subtract(&trailing)?;
        let right = identity.scaled(&characteristic.coefficient(extent - step));
        let difference = left.subtract(&right)?;
        let worst = difference
            .entries()
            .iter()
            .map(num_traits::Signed::abs)
            .max()
            .unwrap_or_else(Rat::zero);
        if worst > residual {
            residual = worst;
        }
    }
    if !residual.is_zero() {
        return Err(ChordRefusal::AdjugateCertificateFailure);
    }
    Ok(residual)
}

// -------------------------------------------------------------------------------------------------
// the transfer function

/// One `(receiver, source)` entry of `H(s)`, before and after exact cancellation.
///
/// **A remounted entry re-derives its own cancellation.** The gcd is recomputed from the numerator
/// and denominator the same wire carries and compared to the declared `cancelled` — a proper
/// divisor of the true gcd would still multiply back correctly, so the product relations alone are
/// not enough — and the two factorizations `numerator = reduced_numerator · cancelled` and
/// `denominator = reduced_denominator · cancelled` are then re-derived by exact polynomial
/// multiplication. `certified_coefficients` is the extent, which the shared denominator's degree
/// names, and `residual` is exactly zero.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "TransferEntryWire")]
pub struct TransferEntry {
    /// Row of `C`: the transport path.
    pub transport_path: usize,
    pub receiver_name: String,
    /// Column of `B`: the excitation.
    pub excitation: usize,
    pub source_name: String,
    /// `C_i adj(sI−A) B_j`.
    pub numerator: RationalPolynomial,
    /// `det(sI−A)`, shared by every entry.
    pub denominator: RationalPolynomial,
    /// The monic gcd. **Nonconstant exactly when a mode is uncontrollable from this source or
    /// unobservable at this receiver**, and it is returned rather than divided away silently.
    pub cancelled: RationalPolynomial,
    pub reduced_numerator: RationalPolynomial,
    pub reduced_denominator: RationalPolynomial,
    /// How many coefficient identities of `num_{ij}(s) = (C adj(sI−A) B)_{ij}` were checked. The
    /// numerator has degree at most `extent − 1`, so this is `extent`: **the whole identity**.
    pub certified_coefficients: usize,
    /// Exactly zero. The largest absolute difference over every one of those coefficients.
    pub residual: Rat,
}

#[derive(Deserialize)]
struct TransferEntryWire {
    transport_path: usize,
    receiver_name: String,
    excitation: usize,
    source_name: String,
    numerator: RationalPolynomial,
    denominator: RationalPolynomial,
    cancelled: RationalPolynomial,
    reduced_numerator: RationalPolynomial,
    reduced_denominator: RationalPolynomial,
    certified_coefficients: usize,
    residual: Rat,
}

impl TryFrom<TransferEntryWire> for TransferEntry {
    type Error = ChordRefusal;

    fn try_from(wire: TransferEntryWire) -> Result<Self, Self::Error> {
        let Some(extent) = wire.denominator.degree().filter(|degree| *degree > 0) else {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the shared denominator, which is `det(sI−A)` of the state's extent",
                declared: format!("degree {:?}", wire.denominator.degree()),
                derived: "a positive degree".to_owned(),
            });
        };
        // The gcd, re-derived from the pair the wire carries rather than read off it.
        let cancelled = if wire.numerator.is_zero() {
            wire.denominator.made_monic()
        } else {
            wire.numerator.monic_gcd(&wire.denominator)?
        };
        if cancelled != wire.cancelled {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the cancelled gcd of the numerator and the denominator",
                declared: format!("{:?}", wire.cancelled.coefficients()),
                derived: format!("{:?}", cancelled.coefficients()),
            });
        }
        let numerator = wire.reduced_numerator.times(&wire.cancelled);
        if numerator != wire.numerator {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the numerator against its reduced factor times the cancellation",
                declared: format!("{:?}", wire.numerator.coefficients()),
                derived: format!("{:?}", numerator.coefficients()),
            });
        }
        let denominator = wire.reduced_denominator.times(&wire.cancelled);
        if denominator != wire.denominator {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the denominator against its reduced factor times the cancellation",
                declared: format!("{:?}", wire.denominator.coefficients()),
                derived: format!("{:?}", denominator.coefficients()),
            });
        }
        if !wire.reduced_denominator.is_monic() {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the reduced denominator, which the entry returns monic",
                declared: format!("{:?}", wire.reduced_denominator.leading()),
                derived: "1".to_owned(),
            });
        }
        if wire.numerator.degree().is_some_and(|degree| degree >= extent) {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the numerator's degree, which `C adj(sI−A) B` holds below the extent",
                declared: format!("{:?}", wire.numerator.degree()),
                derived: format!("below {extent}"),
            });
        }
        if wire.certified_coefficients != extent {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the certified coefficient count against the denominator's degree",
                declared: wire.certified_coefficients.to_string(),
                derived: extent.to_string(),
            });
        }
        if !wire.residual.is_zero() {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the entry's certificate residual, which is exactly zero",
                declared: wire.residual.to_string(),
                derived: "0".to_owned(),
            });
        }
        Ok(Self {
            transport_path: wire.transport_path,
            receiver_name: wire.receiver_name,
            excitation: wire.excitation,
            source_name: wire.source_name,
            numerator: wire.numerator,
            denominator: wire.denominator,
            cancelled: wire.cancelled,
            reduced_numerator: wire.reduced_numerator,
            reduced_denominator: wire.reduced_denominator,
            certified_coefficients: wire.certified_coefficients,
            residual: wire.residual,
        })
    }
}

impl TransferEntry {
    /// Whether this source/receiver pair sees a cancellation at all.
    pub fn cancels(&self) -> bool {
        self.cancelled.degree().is_some_and(|degree| degree > 0)
    }
}

/// **The exact transfer matrix of a linearization.**
///
/// **A remounted transfer matrix re-derives its atlas.** `atlas_denominator` is recomputed as the
/// monic least common multiple of the entries' reduced denominators — the same computation the
/// constructor ran — and `atlas_cancellation` is then pinned by the exact product
/// `atlas_denominator · atlas_cancellation = det(sI−A)`. The entry population is checked to be the
/// complete rectangular grid it claims, in the row-major order the constructor emits, with one
/// name per index and the shared denominator on every entry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "TransferFunctionWire")]
pub struct TransferFunction {
    pub schema: String,
    pub lineage: String,
    pub extent: usize,
    pub expansion: ResolventExpansion,
    pub entries: Vec<TransferEntry>,
    /// The least common multiple of every reduced entry denominator: the characteristic polynomial
    /// of the part of `A` this atlas can reach and see.
    pub atlas_denominator: RationalPolynomial,
    /// `det(sI−A) / atlas_denominator` — the modes **no** declared source excites or **no** declared
    /// receiver observes. Constant exactly when the declared atlas is complete for this operator.
    pub atlas_cancellation: RationalPolynomial,
}

#[derive(Deserialize)]
struct TransferFunctionWire {
    schema: String,
    lineage: String,
    extent: usize,
    expansion: ResolventExpansion,
    entries: Vec<TransferEntry>,
    atlas_denominator: RationalPolynomial,
    atlas_cancellation: RationalPolynomial,
}

impl TryFrom<TransferFunctionWire> for TransferFunction {
    type Error = ChordRefusal;

    fn try_from(wire: TransferFunctionWire) -> Result<Self, Self::Error> {
        if wire.extent != wire.expansion.extent {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the declared extent against the expansion's own",
                declared: wire.extent.to_string(),
                derived: wire.expansion.extent.to_string(),
            });
        }
        check_entry_grid(&wire.entries)?;
        for entry in &wire.entries {
            if entry.denominator != wire.expansion.characteristic {
                return Err(ChordRefusal::TransferWireDisagrees {
                    relation: "an entry's denominator against the shared characteristic polynomial",
                    declared: format!("{:?}", entry.denominator.coefficients()),
                    derived: format!("{:?}", wire.expansion.characteristic.coefficients()),
                });
            }
        }
        // The atlas denominator is the least common multiple of the reduced entry denominators,
        // re-derived here rather than read off the wire.
        let mut atlas_denominator = RationalPolynomial::one();
        for entry in &wire.entries {
            atlas_denominator = polynomial_lcm(&atlas_denominator, &entry.reduced_denominator)?;
        }
        if atlas_denominator != wire.atlas_denominator {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the atlas denominator against the lcm of the reduced entry denominators",
                declared: format!("{:?}", wire.atlas_denominator.coefficients()),
                derived: format!("{:?}", atlas_denominator.coefficients()),
            });
        }
        let reassembled = wire.atlas_denominator.times(&wire.atlas_cancellation);
        if reassembled != wire.expansion.characteristic {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the atlas denominator times the atlas cancellation against `det(sI−A)`",
                declared: format!("{:?}", wire.expansion.characteristic.coefficients()),
                derived: format!("{:?}", reassembled.coefficients()),
            });
        }
        Ok(Self {
            schema: wire.schema,
            lineage: wire.lineage,
            extent: wire.extent,
            expansion: wire.expansion,
            entries: wire.entries,
            atlas_denominator: wire.atlas_denominator,
            atlas_cancellation: wire.atlas_cancellation,
        })
    }
}

/// The entry population of a transfer matrix is the complete `receivers × sources` grid in
/// row-major order, with one receiver name per row and one source name per column.
///
/// [`TransferFunction::entry`] is a linear search over these, so a wire that repeats an index, omits
/// one, or names the same port two ways is a chart whose readings depend on which copy is found
/// first. That is checkable from the entries alone and is checked.
fn check_entry_grid(entries: &[TransferEntry]) -> Result<(), ChordRefusal> {
    if entries.is_empty() {
        return Ok(());
    }
    let receivers = entries
        .iter()
        .map(|entry| entry.transport_path)
        .max()
        .map_or(0, |top| top + 1);
    let sources = entries
        .iter()
        .map(|entry| entry.excitation)
        .max()
        .map_or(0, |top| top + 1);
    let expected = receivers
        .checked_mul(sources)
        .ok_or_else(|| ChordRefusal::StateExtentOverflows {
            extent: receivers.max(sources),
        })?;
    if entries.len() != expected {
        return Err(ChordRefusal::TransferWireDisagrees {
            relation: "the entry count against the port grid the indices declare",
            declared: entries.len().to_string(),
            derived: format!("{receivers}x{sources}"),
        });
    }
    for (at, entry) in entries.iter().enumerate() {
        let (row, column) = (at / sources, at % sources);
        if entry.transport_path != row || entry.excitation != column {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "an entry's port indices against its row-major position",
                declared: format!("({}, {})", entry.transport_path, entry.excitation),
                derived: format!("({row}, {column})"),
            });
        }
        let named = &entries[row * sources];
        if entry.receiver_name != named.receiver_name {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the receiver name of one transport path, named two ways",
                declared: entry.receiver_name.clone(),
                derived: named.receiver_name.clone(),
            });
        }
        let named = &entries[column];
        if entry.source_name != named.source_name {
            return Err(ChordRefusal::TransferWireDisagrees {
                relation: "the source name of one excitation, named two ways",
                declared: entry.source_name.clone(),
                derived: named.source_name.clone(),
            });
        }
    }
    Ok(())
}

impl TransferFunction {
    pub fn characteristic(&self) -> &RationalPolynomial {
        &self.expansion.characteristic
    }

    pub fn entry(&self, transport_path: usize, excitation: usize) -> Option<&TransferEntry> {
        self.entries
            .iter()
            .find(|entry| entry.transport_path == transport_path && entry.excitation == excitation)
    }

    /// Whether the declared atlas reaches and sees every mode.
    pub fn atlas_is_complete(&self) -> bool {
        self.atlas_cancellation
            .degree()
            .is_none_or(|degree| degree == 0)
    }
}

/// `H(s) = C adj(sI−A) B / det(sI−A)`, entry by entry, with the cancellations named.
pub fn transfer_function(linearization: &Linearization) -> Result<TransferFunction, ChordRefusal> {
    let expansion = resolvent_expansion(&linearization.state)?;
    let extent = expansion.extent;
    let denominator = expansion.characteristic.clone();

    // `C M_k B` for every coefficient matrix, once, associated `(C M_k) B`.
    let mut blocks = Vec::with_capacity(extent);
    for block in &expansion.adjugate {
        blocks.push(
            linearization
                .readout
                .multiply(block)?
                .multiply(&linearization.excitation)?,
        );
    }

    // The same coefficients associated the other way, `C (M_k B)`. `num_{ij}(s) = (C adj(sI−A) B)_{ij}`
    // is an identity between polynomials of degree at most `extent − 1`, so the certificate is the
    // `extent` equations between their coefficients — every one of them, checked below against an
    // independently associated product. A single rational evaluation certifies nothing here: a
    // degree-`(extent−1)` identity needs `extent` distinct points before one value implies it.
    let mut certificate_blocks = Vec::with_capacity(extent);
    for block in &expansion.adjugate {
        certificate_blocks.push(
            linearization
                .readout
                .multiply(&block.multiply(&linearization.excitation)?)?,
        );
    }

    let mut entries = Vec::new();
    let mut atlas_denominator = RationalPolynomial::one();
    for row in 0..linearization.receiver_count() {
        for column in 0..linearization.source_count() {
            // `blocks[j]` multiplies `s^{extent−1−j}`, so the ascending coefficient vector is the
            // reversed sequence of entries.
            let mut ascending = vec![Rat::zero(); extent];
            for (index, block) in blocks.iter().enumerate() {
                ascending[extent - 1 - index] = block.get(row, column)?.clone();
            }
            let numerator = RationalPolynomial::new(ascending);
            let cancelled = if numerator.is_zero() {
                denominator.made_monic()
            } else {
                numerator.monic_gcd(&denominator)?
            };
            let reduced_numerator = numerator.divided_exactly_by(&cancelled)?;
            let reduced_denominator = denominator.divided_exactly_by(&cancelled)?.made_monic();
            let mut residual = Rat::zero();
            for (index, block) in certificate_blocks.iter().enumerate() {
                let difference =
                    numerator.coefficient(extent - 1 - index) - block.get(row, column)?;
                let worst = num_traits::Signed::abs(&difference);
                if worst > residual {
                    residual = worst;
                }
            }
            if !residual.is_zero() {
                return Err(ChordRefusal::TransferCertificateFailure {
                    transport_path: row,
                    excitation: column,
                });
            }
            atlas_denominator = polynomial_lcm(&atlas_denominator, &reduced_denominator)?;
            entries.push(TransferEntry {
                transport_path: row,
                receiver_name: linearization.receivers[row].clone(),
                excitation: column,
                source_name: linearization.sources[column].clone(),
                numerator,
                denominator: denominator.clone(),
                cancelled,
                reduced_numerator,
                reduced_denominator,
                certified_coefficients: extent,
                residual,
            });
        }
    }
    let atlas_cancellation = denominator
        .made_monic()
        .divided_exactly_by(&atlas_denominator)?;
    Ok(TransferFunction {
        schema: CAUSAL_CHORD_SCHEMA.to_owned(),
        lineage: linearization.lineage.clone(),
        extent,
        expansion,
        entries,
        atlas_denominator,
        atlas_cancellation,
    })
}

/// The monic least common multiple of two nonzero polynomials.
fn polynomial_lcm(
    left: &RationalPolynomial,
    right: &RationalPolynomial,
) -> Result<RationalPolynomial, ChordRefusal> {
    if left.is_zero() || right.is_zero() {
        return Err(ChordRefusal::Polynomial(
            ExactPolynomialError::ZeroPolynomial,
        ));
    }
    let gcd = left.monic_gcd(right)?;
    Ok(left.times(right).divided_exactly_by(&gcd)?.made_monic())
}

// -------------------------------------------------------------------------------------------------
// half-plane counting

/// **The half-plane counter now lives beside the root-counting owner.**
///
/// [definition] `causal_chord` founded this routine because the repository had no owner for it.
/// It is now `crate::rational_polynomial`'s, beside the Sturm chain the Cauchy index is built from
/// and beside `rational_root_census`, because those are the same machinery: the signed remainder
/// sequence over `Z` with tracked signs is [`holonics::exact_value::SturmChain`], and reading it at
/// `±∞` rather than at a point is the only difference between a Sturm count and a Cauchy index.
/// The chart adapters below map refusals into [`ChordRefusal`]'s own species so a caller matching on
/// [`ChordRefusal::HalfPlaneParityFailure`] or
/// [`ChordRefusal::HalfPlaneRefinementExhausted`] still sees them.
use holonics::rational_polynomial::HalfPlaneCount;

/// The number of roots of `p` on the imaginary axis, with multiplicity.
///
/// Re-entry into [`holonics::rational_polynomial::axis_root_count`].
pub fn axis_root_count(polynomial: &RationalPolynomial) -> Result<usize, ChordRefusal> {
    holonics::rational_polynomial::axis_root_count(polynomial).map_err(chord_refusal)
}

/// **The exact half-plane population of a real polynomial's roots, with multiplicity.**
///
/// Re-entry into [`holonics::rational_polynomial::half_plane_count`], which is the owner.
pub fn half_plane_count(polynomial: &RationalPolynomial) -> Result<HalfPlaneCount, ChordRefusal> {
    holonics::rational_polynomial::half_plane_count(polynomial).map_err(chord_refusal)
}

/// Map the two refusals this module named before the owner moved back onto its own species, so the
/// public error surface is the one it always was.
fn chord_refusal(error: ExactPolynomialError) -> ChordRefusal {
    match error {
        ExactPolynomialError::HalfPlaneRefinementExhausted { ceiling } => {
            ChordRefusal::HalfPlaneRefinementExhausted { ceiling }
        }
        ExactPolynomialError::HalfPlaneParityFailure { degree, index } => {
            ChordRefusal::HalfPlaneParityFailure { degree, index }
        }
        other => ChordRefusal::Polynomial(other),
    }
}

/// **The half-plane count of a symmetric operator, from Sylvester's signature.**
///
/// A symmetric rational `A` has real spectrum, so `Re λ > 0`, `= 0` and `< 0` are exactly the
/// positive, null and negative indices of the form. This routes to [`holonics::inertia::inertia`]
/// (`inertia.rs:375`) rather than running the Routh–Hurwitz machinery, which is both cheaper and
/// the connection the September 15 record asks for.
pub fn half_plane_from_symmetric(state: &ExactRatMatrix) -> Result<HalfPlaneCount, ChordRefusal> {
    let form = SymmetricForm::from_rows(state.to_rows())?;
    let reading: Inertia = inertia(&form);
    Ok(HalfPlaneCount {
        degree: state.rows(),
        left: reading.negative,
        axis: reading.zero,
        right: reading.positive,
        shift_witness: None,
        refinements: 0,
    })
}

// -------------------------------------------------------------------------------------------------
// poles

/// How much of the pole reading a caller is asking for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PoleReading {
    /// Exact squarefree factors, multiplicities and rational poles. No isolation, no half-plane
    /// count. This is the reading a large exact operator can afford; the factor is still the pole's
    /// exact name, which is the object the plan asks for.
    Named,
    /// Adds Sturm-certified isolating boxes for every real root and the sign-certified half-plane
    /// count.
    Certified,
}

/// One squarefree factor of the denominator, at one multiplicity.
///
/// **A remounted factor is tested against its own poles.** Every declared rational pole is
/// evaluated on the factor and refused unless it vanishes exactly — one exact evaluation each, and
/// a genuine re-derivation rather than a restatement — the factor is re-checked to be monic,
/// squarefree and of the declared degree, and every isolating readout is refused unless the factor
/// changes sign across it, which for a squarefree factor is exactly the statement that a real root
/// lies inside. The half-plane count, when present, must place the factor's whole degree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "PoleFactorWire")]
pub struct PoleFactor {
    /// **The pole's exact name.** Monic, squarefree, and the product of exactly those irreducible
    /// factors occurring with this multiplicity.
    pub factor: RationalPolynomial,
    pub multiplicity: u32,
    pub degree: usize,
    /// Poles of this factor that are rational, exactly.
    pub rational_poles: Vec<Rat>,
    /// Sturm-certified isolating boxes for the real roots, present only under
    /// [`PoleReading::Certified`]. **A readout, never the object.**
    pub real_isolations: Vec<ExactInterval>,
    /// Present only under [`PoleReading::Certified`].
    pub half_plane: Option<HalfPlaneCount>,
}

#[derive(Deserialize)]
struct PoleFactorWire {
    factor: RationalPolynomial,
    multiplicity: u32,
    degree: usize,
    rational_poles: Vec<Rat>,
    real_isolations: Vec<ExactInterval>,
    half_plane: Option<HalfPlaneCount>,
}

impl TryFrom<PoleFactorWire> for PoleFactor {
    type Error = ChordRefusal;

    fn try_from(wire: PoleFactorWire) -> Result<Self, Self::Error> {
        if wire.multiplicity == 0 {
            return Err(ChordRefusal::PoleWireDisagrees {
                relation: "the multiplicity of a factor, which is an index and starts at one",
                declared: "0".to_owned(),
                derived: "at least 1".to_owned(),
            });
        }
        if wire.factor.degree() != Some(wire.degree) || !wire.factor.is_monic() {
            return Err(ChordRefusal::PoleWireDisagrees {
                relation: "the factor as a monic of the declared degree",
                declared: format!("monic of degree {}", wire.degree),
                derived: format!(
                    "degree {:?}, monic {}",
                    wire.factor.degree(),
                    wire.factor.is_monic()
                ),
            });
        }
        if wire.degree > 0 && wire.factor.squarefree_part()? != wire.factor {
            return Err(ChordRefusal::PoleWireDisagrees {
                relation: "the factor, which a squarefree decomposition returns squarefree",
                declared: format!("{:?}", wire.factor.coefficients()),
                derived: format!("{:?}", wire.factor.squarefree_part()?.coefficients()),
            });
        }
        if wire.rational_poles.len() > wire.degree {
            return Err(ChordRefusal::PoleWireDisagrees {
                relation: "the rational pole count against the factor's degree",
                declared: wire.rational_poles.len().to_string(),
                derived: format!("at most {}", wire.degree),
            });
        }
        for (at, pole) in wire.rational_poles.iter().enumerate() {
            if wire.rational_poles[..at].contains(pole) {
                return Err(ChordRefusal::PoleWireDisagrees {
                    relation: "a rational pole listed twice on one squarefree factor",
                    declared: pole.to_string(),
                    derived: "listed once".to_owned(),
                });
            }
            // The real re-derivation: the declared pole is a root of the factor, or it is not a
            // pole of it.
            if !wire.factor.evaluate(pole).is_zero() {
                return Err(ChordRefusal::PoleWireDisagrees {
                    relation: "a declared rational pole evaluated on the factor it names",
                    declared: pole.to_string(),
                    derived: wire.factor.evaluate(pole).to_string(),
                });
            }
        }
        for pair in wire.real_isolations.windows(2) {
            if pair[0].upper > pair[1].lower {
                return Err(ChordRefusal::PoleWireDisagrees {
                    relation: "the isolating readouts, which are ascending and pairwise disjoint",
                    declared: format!("[{}, {}] then [{}, {}]",
                        pair[0].lower, pair[0].upper, pair[1].lower, pair[1].upper),
                    derived: "ascending, disjoint".to_owned(),
                });
            }
        }
        if wire.real_isolations.len() > wire.degree {
            return Err(ChordRefusal::PoleWireDisagrees {
                relation: "the isolating readout count against the factor's degree",
                declared: wire.real_isolations.len().to_string(),
                derived: format!("at most {}", wire.degree),
            });
        }
        for interval in &wire.real_isolations {
            let low = wire.factor.evaluate(&interval.lower);
            let high = wire.factor.evaluate(&interval.upper);
            if low.is_zero() || high.is_zero() || low.is_negative() == high.is_negative() {
                return Err(ChordRefusal::PoleWireDisagrees {
                    relation: "an isolating readout, across which a squarefree factor changes sign",
                    declared: format!("[{}, {}]", interval.lower, interval.upper),
                    derived: format!("f = {low} and {high} at the endpoints"),
                });
            }
        }
        if let Some(count) = &wire.half_plane
            && (count.degree != wire.degree || count.total() != wire.degree)
        {
            return Err(ChordRefusal::PoleWireDisagrees {
                relation: "the factor's half-plane population against its degree",
                declared: format!("degree {}, left+axis+right {}", count.degree, count.total()),
                derived: wire.degree.to_string(),
            });
        }
        Ok(Self {
            factor: wire.factor,
            multiplicity: wire.multiplicity,
            degree: wire.degree,
            rational_poles: wire.rational_poles,
            real_isolations: wire.real_isolations,
            half_plane: wire.half_plane,
        })
    }
}

/// The complete pole population of one denominator.
///
/// **A remounted atlas re-multiplies its own factorization.** `∏ factor^multiplicity` is formed
/// exactly and refused unless it is the denominator the atlas carries — which subsumes
/// [`PoleAtlas::accounted`] and is the statement the squarefree decomposition makes. The declared
/// reading decides exactly which readouts may be present, and under
/// [`PoleReading::Certified`] the whole denominator's half-plane population must be the factors'
/// own, summed with multiplicity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "PoleAtlasWire")]
pub struct PoleAtlas {
    pub denominator: RationalPolynomial,
    pub reading: PoleReading,
    pub factors: Vec<PoleFactor>,
    /// For the whole denominator, with multiplicity. Present only under [`PoleReading::Certified`].
    pub half_plane: Option<HalfPlaneCount>,
}

#[derive(Deserialize)]
struct PoleAtlasWire {
    denominator: RationalPolynomial,
    reading: PoleReading,
    factors: Vec<PoleFactor>,
    half_plane: Option<HalfPlaneCount>,
}

impl TryFrom<PoleAtlasWire> for PoleAtlas {
    type Error = ChordRefusal;

    fn try_from(wire: PoleAtlasWire) -> Result<Self, Self::Error> {
        let Some(degree) = wire.denominator.degree() else {
            return Err(ChordRefusal::Polynomial(
                ExactPolynomialError::ZeroPolynomial,
            ));
        };
        if !wire.denominator.is_monic() {
            return Err(ChordRefusal::PoleWireDisagrees {
                relation: "the denominator, which the atlas returns monic",
                declared: format!("{:?}", wire.denominator.leading()),
                derived: "1".to_owned(),
            });
        }
        for pair in wire.factors.windows(2) {
            if pair[0].multiplicity >= pair[1].multiplicity {
                return Err(ChordRefusal::PoleWireDisagrees {
                    relation: "the factors, keyed by strictly ascending multiplicity",
                    declared: format!("{} then {}", pair[0].multiplicity, pair[1].multiplicity),
                    derived: "strictly ascending".to_owned(),
                });
            }
        }
        // A multiplicity sizes the re-multiplication below, so it is bounded against the degree it
        // has to account for **before** anything is formed from it: `i · deg V_i ≤ n` with
        // `deg V_i ≥ 1` gives `i ≤ n`, and a hostile `u32` is refused here rather than run.
        for factor in &wire.factors {
            if factor.multiplicity as usize > degree {
                return Err(ChordRefusal::PoleWireDisagrees {
                    relation: "a factor's multiplicity against the degree it has to account for",
                    declared: factor.multiplicity.to_string(),
                    derived: format!("at most {degree}"),
                });
            }
        }
        let accounted: usize = wire
            .factors
            .iter()
            .map(|factor| factor.degree * factor.multiplicity as usize)
            .sum();
        if accounted != degree {
            return Err(ChordRefusal::PoleWireDisagrees {
                relation: "the degree the factors account for against the denominator's own",
                declared: accounted.to_string(),
                derived: degree.to_string(),
            });
        }
        let mut product = RationalPolynomial::one();
        for factor in &wire.factors {
            for _ in 0..factor.multiplicity {
                product = product.times(&factor.factor);
            }
        }
        if product != wire.denominator {
            return Err(ChordRefusal::PoleWireDisagrees {
                relation: "the product of the factors at their multiplicities against the denominator",
                declared: format!("{:?}", wire.denominator.coefficients()),
                derived: format!("{:?}", product.coefficients()),
            });
        }
        let certified = matches!(wire.reading, PoleReading::Certified);
        if wire.half_plane.is_some() != certified {
            return Err(ChordRefusal::PoleWireDisagrees {
                relation: "the half-plane count, present exactly under the certified reading",
                declared: format!("present {}", wire.half_plane.is_some()),
                derived: format!("present {certified}"),
            });
        }
        for factor in &wire.factors {
            let expected = certified && factor.degree > 0;
            if factor.half_plane.is_some() != expected {
                return Err(ChordRefusal::PoleWireDisagrees {
                    relation: "a factor's half-plane count against the atlas's declared reading",
                    declared: format!("present {}", factor.half_plane.is_some()),
                    derived: format!("present {expected}"),
                });
            }
            if !certified && !factor.real_isolations.is_empty() {
                return Err(ChordRefusal::PoleWireDisagrees {
                    relation: "a factor's isolating readouts, which the named reading does not take",
                    declared: factor.real_isolations.len().to_string(),
                    derived: "0".to_owned(),
                });
            }
        }
        if let Some(count) = &wire.half_plane {
            let mut summed = HalfPlaneCount {
                degree,
                ..HalfPlaneCount::default()
            };
            for factor in &wire.factors {
                let Some(part) = &factor.half_plane else {
                    continue;
                };
                let times = factor.multiplicity as usize;
                summed.left += part.left * times;
                summed.axis += part.axis * times;
                summed.right += part.right * times;
            }
            if (count.degree, count.left, count.axis, count.right)
                != (degree, summed.left, summed.axis, summed.right)
            {
                return Err(ChordRefusal::PoleWireDisagrees {
                    relation: "the denominator's half-plane population against its factors', summed with multiplicity",
                    declared: format!(
                        "degree {}, left {}, axis {}, right {}",
                        count.degree, count.left, count.axis, count.right
                    ),
                    derived: format!(
                        "degree {degree}, left {}, axis {}, right {}",
                        summed.left, summed.axis, summed.right
                    ),
                });
            }
        }
        Ok(Self {
            denominator: wire.denominator,
            reading: wire.reading,
            factors: wire.factors,
            half_plane: wire.half_plane,
        })
    }
}

impl PoleAtlas {
    /// The rational poles with their multiplicities, ascending.
    pub fn rational_poles(&self) -> Vec<(Rat, u32)> {
        let mut population: Vec<(Rat, u32)> = self
            .factors
            .iter()
            .flat_map(|factor| {
                factor
                    .rational_poles
                    .iter()
                    .map(move |pole| (pole.clone(), factor.multiplicity))
            })
            .collect();
        population.sort_by(|left, right| left.0.cmp(&right.0));
        population
    }

    /// The degree the factors account for, which must equal the denominator's degree.
    pub fn accounted(&self) -> usize {
        self.factors
            .iter()
            .map(|factor| factor.degree * factor.multiplicity as usize)
            .sum()
    }
}


/// Every rational root of a polynomial, by the prime-lifting route rather than the Sturm census.
///
/// [`rational_root_census`] (`rational_polynomial.rs:1110`) is complete and certified, but its
/// descent runs from an absolute Cauchy bound that, on a characteristic polynomial built from a
/// physical network operator, is astronomically wider than the roots themselves — the same
/// pathology `lattice_gauge.rs:955` records and rebases away. [`rational_roots_by_lifting`]
/// (`rational_polynomial.rs:906`) answers the same question through one prime receiver and
/// verifies every returned candidate by exact evaluation, so it is a certificate and not a
/// heuristic. When no prime leaves every residue root simple it refuses by name, and the census is
/// the declared fallback.
fn rational_poles_by_lifting(
    polynomial: &RationalPolynomial,
) -> Result<Vec<Rat>, ChordRefusal> {
    if polynomial.degree().unwrap_or(0) == 0 {
        return Ok(Vec::new());
    }
    match rational_roots_by_lifting(polynomial) {
        Ok(roots) => Ok(roots),
        Err(ExactPolynomialError::LiftingPrimesExhausted) => {
            Ok(rational_root_census(polynomial)?.rational_roots)
        }
        Err(error) => Err(ChordRefusal::Polynomial(error)),
    }
}

/// Squarefree-factor a denominator and read each factor's poles.
pub fn pole_atlas(
    denominator: &RationalPolynomial,
    reading: PoleReading,
) -> Result<PoleAtlas, ChordRefusal> {
    let Some(degree) = denominator.degree() else {
        return Err(ChordRefusal::Polynomial(
            ExactPolynomialError::ZeroPolynomial,
        ));
    };
    let mut factors = Vec::new();
    if degree > 0 {
        for (multiplicity, factor) in denominator.squarefree_decomposition()? {
            let factor_degree = factor.degree().unwrap_or(0);
            let (rational_poles, real_isolations) = if factor_degree == 0 {
                (Vec::new(), Vec::new())
            } else {
                match reading {
                    PoleReading::Named => (rational_poles_by_lifting(&factor)?, Vec::new()),
                    PoleReading::Certified => {
                        let census = rational_root_census(&factor)?;
                        // The census isolates the **monic companion** `c^{n−1}·f(z/c)`, whose real
                        // roots are `c` times `f`'s. `c` is positive by the primitive
                        // normalization, so dividing the endpoints preserves their order.
                        let scale = Rat::from_integer(census.leading_coefficient.clone());
                        let mut isolations = Vec::new();
                        for root in &census.roots {
                            let interval = &root.isolating.isolating_interval;
                            isolations.push(ExactInterval::new(
                                &interval.lower / &scale,
                                &interval.upper / &scale,
                            )?);
                        }
                        (census.rational_roots.clone(), isolations)
                    }
                }
            };
            let half_plane = match reading {
                PoleReading::Named => None,
                PoleReading::Certified if factor_degree == 0 => None,
                PoleReading::Certified => Some(half_plane_count(&factor)?),
            };
            factors.push(PoleFactor {
                factor,
                multiplicity,
                degree: factor_degree,
                rational_poles,
                real_isolations,
                half_plane,
            });
        }
    }
    let half_plane = match reading {
        PoleReading::Named => None,
        PoleReading::Certified => Some(half_plane_count(denominator)?),
    };
    Ok(PoleAtlas {
        denominator: denominator.made_monic(),
        reading,
        factors,
        half_plane,
    })
}

// -------------------------------------------------------------------------------------------------
// residues

/// The residue of one transfer entry at one pole.
///
/// **A remounted residue carries its order in two places and they must agree.** The Laurent tail
/// runs `c_{−order} … c_{−1}`, so its length is the order; an algebraic residue's coefficients are
/// elements of `Q[x]/(factor)` and must be reduced there, which is one degree comparison each. The
/// numerator and denominator the coefficients came from are not carried, so the values themselves
/// are testimony about a transfer entry; what is checkable without it is checked.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case", try_from = "ChordResidueWire")]
pub enum ChordResidue {
    /// A rational pole. The Laurent coefficients `c_{−order} … c_{−1}`, so the last entry is the
    /// residue proper and the earlier ones are the higher-order parts of the pole.
    Rational {
        pole: Rat,
        order: u32,
        laurent: Vec<Rat>,
    },
    /// A pole named only by its squarefree factor. The Laurent coefficients as elements of
    /// `Q[x]/(factor)`, each of which specializes to the corresponding coefficient at every root of
    /// the factor. The last entry is the residue.
    Algebraic {
        factor: RationalPolynomial,
        order: u32,
        laurent: Vec<RationalPolynomial>,
    },
}

#[derive(Deserialize)]
#[serde(rename_all = "kebab-case")]
enum ChordResidueWire {
    Rational {
        pole: Rat,
        order: u32,
        laurent: Vec<Rat>,
    },
    Algebraic {
        factor: RationalPolynomial,
        order: u32,
        laurent: Vec<RationalPolynomial>,
    },
}

impl TryFrom<ChordResidueWire> for ChordResidue {
    type Error = ChordRefusal;

    fn try_from(wire: ChordResidueWire) -> Result<Self, Self::Error> {
        match wire {
            ChordResidueWire::Rational {
                pole,
                order,
                laurent,
            } => {
                if order == 0 || laurent.len() != order as usize {
                    return Err(ChordRefusal::PoleOrderDisagrees { order });
                }
                Ok(Self::Rational {
                    pole,
                    order,
                    laurent,
                })
            }
            ChordResidueWire::Algebraic {
                factor,
                order,
                laurent,
            } => {
                if order == 0 || laurent.len() != order as usize {
                    return Err(ChordRefusal::PoleOrderDisagrees { order });
                }
                let Some(modulus) = factor.degree().filter(|degree| *degree > 0) else {
                    return Err(ChordRefusal::ChordWireDisagrees {
                        object: "an algebraic residue",
                        relation: "the factor naming the pole, which is nonconstant",
                        declared: format!("degree {:?}", factor.degree()),
                        derived: "a positive degree".to_owned(),
                    });
                };
                if !factor.is_monic() {
                    return Err(ChordRefusal::ChordWireDisagrees {
                        object: "an algebraic residue",
                        relation: "the factor naming the pole, which is monic",
                        declared: format!("{:?}", factor.leading()),
                        derived: "1".to_owned(),
                    });
                }
                for coefficient in &laurent {
                    if coefficient.degree().is_some_and(|degree| degree >= modulus) {
                        return Err(ChordRefusal::ChordWireDisagrees {
                            object: "an algebraic residue",
                            relation: "a Laurent coefficient reduced in `Q[x]/(factor)`",
                            declared: format!("degree {:?}", coefficient.degree()),
                            derived: format!("below {modulus}"),
                        });
                    }
                }
                Ok(Self::Algebraic {
                    factor,
                    order,
                    laurent,
                })
            }
        }
    }
}

impl ChordResidue {
    /// The residue proper — the coefficient of `1/(s − pole)`.
    pub fn residue(&self) -> Option<RationalPolynomial> {
        match self {
            Self::Rational { laurent, .. } => laurent
                .last()
                .map(|value| RationalPolynomial::constant(value.clone())),
            Self::Algebraic { laurent, .. } => laurent.last().cloned(),
        }
    }

    pub fn order(&self) -> u32 {
        match self {
            Self::Rational { order, .. } | Self::Algebraic { order, .. } => *order,
        }
    }
}

/// `p mod modulus`, monic modulus assumed nonconstant.
fn modular_reduce(
    polynomial: &RationalPolynomial,
    modulus: &RationalPolynomial,
) -> Result<RationalPolynomial, ChordRefusal> {
    Ok(polynomial.divided_by(modulus)?.1)
}

fn modular_multiply(
    left: &RationalPolynomial,
    right: &RationalPolynomial,
    modulus: &RationalPolynomial,
) -> Result<RationalPolynomial, ChordRefusal> {
    modular_reduce(&left.times(right), modulus)
}

/// The inverse of `value` in `Q[x]/(modulus)`, or a named refusal when it is not a unit.
fn modular_inverse(
    value: &RationalPolynomial,
    modulus: &RationalPolynomial,
) -> Result<RationalPolynomial, ChordRefusal> {
    let reduced = modular_reduce(value, modulus)?;
    if reduced.is_zero() {
        return Err(ChordRefusal::ResidueDenominatorNotInvertible);
    }
    let (gcd, cofactor, _) = reduced.extended_monic_gcd(modulus)?;
    if gcd.degree() != Some(0) {
        return Err(ChordRefusal::ResidueDenominatorNotInvertible);
    }
    modular_reduce(&cofactor, modulus)
}

/// The Laurent coefficients of `numerator/denominator` at a rational pole of the given order.
///
/// `denominator = (s − pole)^order · E` with `E(pole) ≠ 0`; the coefficients are the Taylor
/// coefficients of `N(pole + u)/E(pole + u)` in `u`, computed by exact power-series division.
fn rational_laurent(
    numerator: &RationalPolynomial,
    denominator: &RationalPolynomial,
    pole: &Rat,
    order: u32,
) -> Result<Vec<Rat>, ChordRefusal> {
    let linear = RationalPolynomial::new(vec![-pole.clone(), Rat::one()]);
    let mut remaining = denominator.clone();
    for _ in 0..order {
        remaining = remaining.divided_exactly_by(&linear)?;
    }
    if remaining.evaluate(pole).is_zero() {
        return Err(ChordRefusal::PoleOrderDisagrees {
            order,
        });
    }
    let shift = RationalPolynomial::new(vec![pole.clone(), Rat::one()]);
    let shifted_numerator = numerator.composed_with(&shift);
    let shifted_denominator = remaining.composed_with(&shift);
    let series = power_series_quotient(
        shifted_numerator.coefficients(),
        shifted_denominator.coefficients(),
        order as usize,
    )?;
    Ok(series)
}

/// `numerator/denominator` as a power series to `terms` coefficients, with rational coefficients.
fn power_series_quotient(
    numerator: &[Rat],
    denominator: &[Rat],
    terms: usize,
) -> Result<Vec<Rat>, ChordRefusal> {
    let constant = denominator.first().cloned().unwrap_or_else(Rat::zero);
    if constant.is_zero() {
        return Err(ChordRefusal::ResidueDenominatorNotInvertible);
    }
    let mut quotient = Vec::with_capacity(terms);
    for index in 0..terms {
        let mut value = numerator.get(index).cloned().unwrap_or_else(Rat::zero);
        for (back, coefficient) in quotient.iter().enumerate() {
            let step = index - back;
            if let Some(entry) = denominator.get(step) {
                value -= coefficient * entry;
            }
        }
        quotient.push(value / &constant);
    }
    Ok(quotient)
}

/// The Laurent coefficients at a pole named only by a squarefree factor, as elements of
/// `Q[x]/(factor)`.
///
/// **The local uniformizer is `s − x_0`, not the factor.** For a squarefree `f` dividing `D`
/// exactly `m` times, every root `x_0` of `f` is a simple root of `f` and an order-`m` root of `D`,
/// so `D^{(k)}(x_0) = 0` for `k < m`, and — `f` being squarefree — `f` divides each `D^{(k)}` for
/// `k < m`. Writing the shift `D(x + u) = Σ_k (D^{(k)}(x)/k!) u^k` over `Q[x]/(f)`, the first `m`
/// coefficients therefore vanish identically and
///
/// ```text
/// W(x + u) = Σ_{j ≥ 0} (D^{(m+j)}(x)/(m+j)!) u^j
/// ```
///
/// is the local cofactor `D/(s−x_0)^m`, whose constant term is a unit exactly because the order is
/// *exactly* `m`. The Laurent coefficients are the power-series coefficients of
/// `N(x+u)/W(x+u)`. At `m = 1` this reduces to the familiar `N/D'`, and the vanishing of the first
/// `m` shift coefficients is checked rather than assumed.
fn algebraic_laurent(
    numerator: &RationalPolynomial,
    denominator: &RationalPolynomial,
    factor: &RationalPolynomial,
    order: u32,
) -> Result<Vec<RationalPolynomial>, ChordRefusal> {
    let terms = order as usize;
    if terms == 0 {
        return Err(ChordRefusal::PoleOrderDisagrees { order });
    }
    let shifted = taylor_series_modulo(denominator, factor, 2 * terms)?;
    for coefficient in shifted.iter().take(terms) {
        if !coefficient.is_zero() {
            return Err(ChordRefusal::PoleOrderDisagrees { order });
        }
    }
    let cofactor = &shifted[terms..];
    let numerator_series = taylor_series_modulo(numerator, factor, terms)?;
    let inverse = modular_inverse(&cofactor[0], factor)?;
    let mut quotient: Vec<RationalPolynomial> = Vec::with_capacity(terms);
    for index in 0..terms {
        let mut value = numerator_series
            .get(index)
            .cloned()
            .unwrap_or_else(RationalPolynomial::zero);
        for (back, coefficient) in quotient.iter().enumerate() {
            let step = index - back;
            if let Some(entry) = cofactor.get(step) {
                value = value.minus(&modular_multiply(coefficient, entry, factor)?);
            }
        }
        quotient.push(modular_multiply(&value, &inverse, factor)?);
    }
    Ok(quotient)
}

/// `[p(x), p'(x)/1!, p''(x)/2!, …]` reduced modulo the factor.
fn taylor_series_modulo(
    polynomial: &RationalPolynomial,
    factor: &RationalPolynomial,
    terms: usize,
) -> Result<Vec<RationalPolynomial>, ChordRefusal> {
    let mut derivative = polynomial.clone();
    let mut factorial = Rat::one();
    let mut series = Vec::with_capacity(terms);
    for index in 0..terms {
        if index > 0 {
            derivative = derivative.derivative();
            factorial *= Rat::from_integer(BigInt::from(index as i64));
        }
        let scaled = derivative.scaled(&(Rat::one() / &factorial));
        series.push(modular_reduce(&scaled, factor)?);
    }
    Ok(series)
}

// -------------------------------------------------------------------------------------------------
// eigenvector support

/// Which state coordinates participate in one rational eigenvalue's modes, and which ports reach
/// them.
///
/// **A remounted support re-derives its own support.** `support` is documented as the state
/// coordinates carrying a nonzero entry in some right eigenvector, which the eigenvectors the
/// struct already carries determine completely, so it is recomputed and refused on disagreement.
/// The geometric multiplicity is the eigenvector count, it cannot pass the algebraic one, and every
/// eigenvector and covector is nonzero and of one common width. Which ports pair nontrivially is a
/// statement about `B` and `C`, which this struct does not carry, so those two index lists are
/// testimony; that they are ascending and repeat nothing is checkable and is checked.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ModeSupportWire")]
pub struct ModeSupport {
    pub eigenvalue: Rat,
    pub algebraic_multiplicity: usize,
    pub geometric_multiplicity: usize,
    /// A basis of `ker(A − λI)`, exactly.
    pub eigenvectors: Vec<Vec<Rat>>,
    /// A basis of `ker(A − λI)ᵀ`, exactly. These are the covectors that decide excitability.
    pub left_eigenvectors: Vec<Vec<Rat>>,
    /// The state coordinates carrying a nonzero entry in some right eigenvector.
    pub support: Vec<usize>,
    /// Columns of `B` that pair nontrivially with some left eigenvector: the sources that can
    /// excite this mode.
    pub excited_sources: Vec<usize>,
    /// Rows of `C` that pair nontrivially with some right eigenvector: the receivers that observe
    /// it.
    pub observed_receivers: Vec<usize>,
}

#[derive(Deserialize)]
struct ModeSupportWire {
    eigenvalue: Rat,
    algebraic_multiplicity: usize,
    geometric_multiplicity: usize,
    eigenvectors: Vec<Vec<Rat>>,
    left_eigenvectors: Vec<Vec<Rat>>,
    support: Vec<usize>,
    excited_sources: Vec<usize>,
    observed_receivers: Vec<usize>,
}

impl TryFrom<ModeSupportWire> for ModeSupport {
    type Error = ChordRefusal;

    fn try_from(wire: ModeSupportWire) -> Result<Self, Self::Error> {
        if wire.algebraic_multiplicity == 0 {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a mode support",
                relation: "the algebraic multiplicity of a listed eigenvalue",
                declared: "0".to_owned(),
                derived: "at least 1".to_owned(),
            });
        }
        if wire.geometric_multiplicity != wire.eigenvectors.len() {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a mode support",
                relation: "the geometric multiplicity against the exhibited eigenvector count",
                declared: wire.geometric_multiplicity.to_string(),
                derived: wire.eigenvectors.len().to_string(),
            });
        }
        if wire.geometric_multiplicity > wire.algebraic_multiplicity {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a mode support",
                relation: "the geometric multiplicity, which cannot pass the algebraic one",
                declared: wire.geometric_multiplicity.to_string(),
                derived: format!("at most {}", wire.algebraic_multiplicity),
            });
        }
        let extent = wire
            .eigenvectors
            .iter()
            .chain(&wire.left_eigenvectors)
            .map(Vec::len)
            .max()
            .unwrap_or(0);
        for vector in wire.eigenvectors.iter().chain(&wire.left_eigenvectors) {
            if vector.len() != extent {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a mode support",
                    relation: "an eigenvector's width against the state's extent",
                    declared: vector.len().to_string(),
                    derived: extent.to_string(),
                });
            }
            if vector.iter().all(Zero::is_zero) {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a mode support",
                    relation: "an exhibited eigenvector, which is never the zero vector",
                    declared: "0".to_owned(),
                    derived: "a nonzero vector".to_owned(),
                });
            }
        }
        // The support is a property of the exhibited eigenvectors, so it is re-derived from them.
        let support: Vec<usize> = (0..extent)
            .filter(|at| {
                wire.eigenvectors
                    .iter()
                    .any(|vector| !vector[*at].is_zero())
            })
            .collect();
        if support != wire.support {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a mode support",
                relation: "the carried support against the exhibited eigenvectors' own",
                declared: format!("{:?}", wire.support),
                derived: format!("{support:?}"),
            });
        }
        for (name, indices) in [
            ("the excited sources", &wire.excited_sources),
            ("the observed receivers", &wire.observed_receivers),
        ] {
            if indices.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a mode support",
                    relation: name,
                    declared: format!("{indices:?}"),
                    derived: "strictly ascending port indices".to_owned(),
                });
            }
        }
        Ok(Self {
            eigenvalue: wire.eigenvalue,
            algebraic_multiplicity: wire.algebraic_multiplicity,
            geometric_multiplicity: wire.geometric_multiplicity,
            eigenvectors: wire.eigenvectors,
            left_eigenvectors: wire.left_eigenvectors,
            support: wire.support,
            excited_sources: wire.excited_sources,
            observed_receivers: wire.observed_receivers,
        })
    }
}

impl ModeSupport {
    /// Defective exactly when the geometric multiplicity falls short of the algebraic one.
    pub fn is_defective(&self) -> bool {
        self.geometric_multiplicity < self.algebraic_multiplicity
    }

    /// A mode no declared source reaches or no declared receiver sees cancels out of every entry of
    /// `H`. This is the structural reading of [`TransferFunction::atlas_cancellation`].
    pub fn is_hidden(&self) -> bool {
        self.excited_sources.is_empty() || self.observed_receivers.is_empty()
    }
}

/// The rational eigenvalues of `A` with their modes, their supports and their port reachability.
///
/// The eigenvalue population comes from [`rational_poles_by_lifting`] and the kernels from
/// `exact_linear.rs:770`; the multiplicities are read by exact division, exactly as
/// [`crate::lattice_gauge::exact_spectrum`] (`lattice_gauge.rs:1039`) reads them after its own
/// census. `the_mode_population_agrees_with_the_existing_spectrum_owner` holds the two to
/// agreement. Nothing here recomputes a kernel, a rank or a root.
pub fn rational_mode_supports(
    linearization: &Linearization,
) -> Result<Vec<ModeSupport>, ChordRefusal> {
    let characteristic = linearization.state.characteristic_polynomial()?;
    let mut population: Vec<(Rat, usize)> = Vec::new();
    let mut remaining = characteristic.clone();
    for root in rational_poles_by_lifting(&characteristic)? {
        let divisor = RationalPolynomial::new(vec![-root.clone(), Rat::one()]);
        let mut multiplicity = 0usize;
        while let Ok(quotient) = remaining.divided_exactly_by(&divisor) {
            remaining = quotient;
            multiplicity += 1;
        }
        if multiplicity > 0 {
            population.push((root, multiplicity));
        }
    }
    population.sort_by(|left, right| left.0.cmp(&right.0));
    let extent = linearization.extent();
    let identity = ExactRatMatrix::identity(extent)?;
    let mut supports = Vec::new();
    for (eigenvalue, multiplicity) in &population {
        let shifted = linearization
            .state
            .subtract(&identity.scaled(eigenvalue))?;
        let eigenvectors = shifted.kernel_basis()?;
        let left_eigenvectors = shifted.transpose()?.kernel_basis()?;
        let mut support = BTreeSet::new();
        for vector in &eigenvectors {
            for (index, entry) in vector.iter().enumerate() {
                if !entry.is_zero() {
                    support.insert(index);
                }
            }
        }
        let mut excited_sources = Vec::new();
        for column in 0..linearization.source_count() {
            let reaches = left_eigenvectors.iter().any(|covector| {
                !(0..extent)
                    .try_fold(Rat::zero(), |sum, row| {
                        linearization
                            .excitation
                            .get(row, column)
                            .map(|entry| sum + &covector[row] * entry)
                    })
                    .unwrap_or_else(|_| Rat::zero())
                    .is_zero()
            });
            if reaches {
                excited_sources.push(column);
            }
        }
        let mut observed_receivers = Vec::new();
        for row in 0..linearization.receiver_count() {
            let sees = eigenvectors.iter().any(|vector| {
                !(0..extent)
                    .try_fold(Rat::zero(), |sum, column| {
                        linearization
                            .readout
                            .get(row, column)
                            .map(|entry| sum + entry * &vector[column])
                    })
                    .unwrap_or_else(|_| Rat::zero())
                    .is_zero()
            });
            if sees {
                observed_receivers.push(row);
            }
        }
        supports.push(ModeSupport {
            eigenvalue: eigenvalue.clone(),
            algebraic_multiplicity: *multiplicity,
            geometric_multiplicity: eigenvectors.len(),
            eigenvectors,
            left_eigenvectors,
            support: support.into_iter().collect(),
            excited_sources,
            observed_receivers,
        });
    }
    Ok(supports)
}

// -------------------------------------------------------------------------------------------------
// the resolvent at a Gaussian-rational probe point

/// A Gaussian-rational probe point `σ + iω`. Exact; there is no float anywhere near it.
///
/// **This carries no certificate and no invariant, so its wire adds nothing.** Every pair of
/// rationals is a lawful Gaussian rational; there is no relation between the two fields to check
/// and no third field to check them against. Whether the point is a pole of a particular resolvent
/// is [`resolvent_probe`]'s refusal and not the point's.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProbePoint {
    pub real: Rat,
    pub imaginary: Rat,
}

impl ProbePoint {
    pub fn new(real: Rat, imaginary: Rat) -> Self {
        Self { real, imaginary }
    }

    pub fn is_real(&self) -> bool {
        self.imaginary.is_zero()
    }
}

/// `(sI − A)^{-1}` and `C (sI − A)^{-1} B` at one exact probe point.
///
/// **A remounted probe re-derives its own norm.** `resolvent_frobenius_squared` is the exact sum of
/// the squared entries of the two resolvent parts the probe already carries, so it is recomputed
/// and refused on disagreement — and it is the reading the module head says governs a non-normal
/// response, so a forged one is the forgery that matters. The inverse certificate is a statement
/// about `A`, which the probe does not carry, so the probe is testimony about that operator; that
/// the residual is exactly zero and the two parts share one square shape is checkable and is
/// checked.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ResolventProbeWire")]
pub struct ResolventProbe {
    pub lineage: String,
    pub point: ProbePoint,
    pub resolvent_real: ExactRatMatrix,
    pub resolvent_imaginary: ExactRatMatrix,
    pub response_real: ExactRatMatrix,
    pub response_imaginary: ExactRatMatrix,
    /// `Σ |Re|² + |Im|²` over the resolvent entries: the exact squared Frobenius norm. **This is the
    /// reading that governs a non-normal response and the spectrum does not.**
    pub resolvent_frobenius_squared: Rat,
    /// Exactly zero: `(sI−A)(sI−A)^{-1} − I`, largest absolute entry over both parts.
    pub residual: Rat,
}

#[derive(Deserialize)]
struct ResolventProbeWire {
    lineage: String,
    point: ProbePoint,
    resolvent_real: ExactRatMatrix,
    resolvent_imaginary: ExactRatMatrix,
    response_real: ExactRatMatrix,
    response_imaginary: ExactRatMatrix,
    resolvent_frobenius_squared: Rat,
    residual: Rat,
}

impl TryFrom<ResolventProbeWire> for ResolventProbe {
    type Error = ChordRefusal;

    fn try_from(wire: ResolventProbeWire) -> Result<Self, Self::Error> {
        if !wire.resolvent_real.is_square()
            || wire.resolvent_real.rows() != wire.resolvent_imaginary.rows()
            || wire.resolvent_real.columns() != wire.resolvent_imaginary.columns()
        {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a resolvent probe",
                relation: "the two resolvent parts, one square operator read in two charts",
                declared: format!(
                    "{}x{} and {}x{}",
                    wire.resolvent_real.rows(),
                    wire.resolvent_real.columns(),
                    wire.resolvent_imaginary.rows(),
                    wire.resolvent_imaginary.columns()
                ),
                derived: "one common square shape".to_owned(),
            });
        }
        if wire.response_real.rows() != wire.response_imaginary.rows()
            || wire.response_real.columns() != wire.response_imaginary.columns()
        {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a resolvent probe",
                relation: "the two response parts, one matrix read in two charts",
                declared: format!(
                    "{}x{} and {}x{}",
                    wire.response_real.rows(),
                    wire.response_real.columns(),
                    wire.response_imaginary.rows(),
                    wire.response_imaginary.columns()
                ),
                derived: "one common shape".to_owned(),
            });
        }
        if !wire.residual.is_zero() {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a resolvent probe",
                relation: "the inverse certificate's residual, which is exactly zero",
                declared: wire.residual.to_string(),
                derived: "0".to_owned(),
            });
        }
        let frobenius = wire
            .resolvent_real
            .entries()
            .iter()
            .chain(wire.resolvent_imaginary.entries())
            .fold(Rat::zero(), |sum, entry| sum + entry * entry);
        if frobenius != wire.resolvent_frobenius_squared {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a resolvent probe",
                relation: "the squared Frobenius norm against the resolvent entries it sums",
                declared: wire.resolvent_frobenius_squared.to_string(),
                derived: frobenius.to_string(),
            });
        }
        Ok(Self {
            lineage: wire.lineage,
            point: wire.point,
            resolvent_real: wire.resolvent_real,
            resolvent_imaginary: wire.resolvent_imaginary,
            response_real: wire.response_real,
            response_imaginary: wire.response_imaginary,
            resolvent_frobenius_squared: wire.resolvent_frobenius_squared,
            residual: wire.residual,
        })
    }
}

/// The exact resolvent at a Gaussian-rational point, by realification over `Q`.
///
/// `sI − A` with `s = σ + iω` realifies to `[[σI − A, −ωI], [ωI, σI − A]]`, whose exact rational
/// inverse is `[[X, −Y], [Y, X]]` for `(sI−A)^{-1} = X + iY`.
pub fn resolvent_probe(
    linearization: &Linearization,
    point: &ProbePoint,
) -> Result<ResolventProbe, ChordRefusal> {
    let extent = linearization.extent();
    let identity = ExactRatMatrix::identity(extent)?;
    let real_block = identity
        .scaled(&point.real)
        .subtract(&linearization.state)?;
    let imaginary_block = identity.scaled(&point.imaginary);
    let doubled = 2 * extent;
    let mut rows = vec![vec![Rat::zero(); doubled]; doubled];
    for row in 0..extent {
        for column in 0..extent {
            let re = real_block.get(row, column)?.clone();
            let im = imaginary_block.get(row, column)?.clone();
            rows[row][column] = re.clone();
            rows[row][extent + column] = -&im;
            rows[extent + row][column] = im;
            rows[extent + row][extent + column] = re;
        }
    }
    let realified = ExactRatMatrix::shaped(doubled, doubled, rows)?;
    let inverse = realified
        .inverse()
        .map_err(|_| ChordRefusal::ProbePointIsAPole)?;
    let mut real_rows = vec![vec![Rat::zero(); extent]; extent];
    let mut imaginary_rows = vec![vec![Rat::zero(); extent]; extent];
    for row in 0..extent {
        for column in 0..extent {
            real_rows[row][column] = inverse.get(row, column)?.clone();
            imaginary_rows[row][column] = inverse.get(extent + row, column)?.clone();
        }
    }
    let resolvent_real = ExactRatMatrix::shaped(extent, extent, real_rows)?;
    let resolvent_imaginary = ExactRatMatrix::shaped(extent, extent, imaginary_rows)?;

    // `C (X + iY) B` splits into its two exact rational parts.
    let response_real = linearization
        .readout
        .multiply(&resolvent_real)?
        .multiply(&linearization.excitation)?;
    let response_imaginary = linearization
        .readout
        .multiply(&resolvent_imaginary)?
        .multiply(&linearization.excitation)?;

    // The certificate, in the realified chart where it is one exact product.
    let certificate = realified
        .multiply(&inverse)?
        .subtract(&ExactRatMatrix::identity(doubled)?)?;
    let residual = certificate
        .entries()
        .iter()
        .map(num_traits::Signed::abs)
        .max()
        .unwrap_or_else(Rat::zero);
    if !residual.is_zero() {
        return Err(ChordRefusal::ResolventCertificateFailure);
    }
    let resolvent_frobenius_squared = resolvent_real
        .entries()
        .iter()
        .chain(resolvent_imaginary.entries())
        .fold(Rat::zero(), |sum, entry| sum + entry * entry);
    Ok(ResolventProbe {
        lineage: linearization.lineage.clone(),
        point: point.clone(),
        resolvent_real,
        resolvent_imaginary,
        response_real,
        response_imaginary,
        resolvent_frobenius_squared,
        residual,
    })
}

// -------------------------------------------------------------------------------------------------
// the rate form and the seam

/// A symmetric form as an exact matrix. [`SymmetricForm`] keeps its own rows private, so this
/// rebuilds them through its public `at`/`extent` accessors rather than widening that owner.
fn form_matrix(form: &SymmetricForm) -> Result<ExactRatMatrix, ChordRefusal> {
    let extent = form.extent();
    let rows = (0..extent)
        .map(|row| {
            (0..extent)
                .map(|column| form.at(row, column).clone())
                .collect()
        })
        .collect();
    Ok(ExactRatMatrix::shaped(extent, extent, rows)?)
}

/// `Σ_G = AᵀG + GA`, the source-free rate form of the reading `E_G = xᵀGx/2`.
pub fn rate_form(
    state: &ExactRatMatrix,
    metric: &SymmetricForm,
) -> Result<SymmetricForm, ChordRefusal> {
    let matrix = form_matrix(metric)?;
    if !state.is_square() || state.rows() != matrix.rows() {
        return Err(ChordRefusal::MetricShape {
            extent: state.rows(),
            metric: matrix.rows(),
        });
    }
    let form = state
        .transpose()?
        .multiply(&matrix)?
        .add(&matrix.multiply(state)?)?;
    Ok(SymmetricForm::from_rows(form.to_rows())?)
}

/// `LᵀG + GL − G`, which is `rate_form(L − I/2, G)`.
///
/// The Lean owner's `seam_iff_gSkew` is the statement that these two are the same object;
/// `the_seam_form_is_the_rate_form_of_the_centred_generator` is the executable equivalent.
pub fn seam_form(
    generator: &ExactRatMatrix,
    metric: &SymmetricForm,
) -> Result<SymmetricForm, ChordRefusal> {
    let matrix = form_matrix(metric)?;
    if !generator.is_square() || generator.rows() != matrix.rows() {
        return Err(ChordRefusal::MetricShape {
            extent: generator.rows(),
            metric: matrix.rows(),
        });
    }
    let form = generator
        .transpose()?
        .multiply(&matrix)?
        .add(&matrix.multiply(generator)?)?
        .subtract(&matrix)?;
    Ok(SymmetricForm::from_rows(form.to_rows())?)
}

/// The rate form under a chart change, through the existing congruence owner.
///
/// `Σ_{G'} = P^T Σ_G P` for `G' = P^T G P` and `A' = P^{-1} A P`. The singular case is
/// [`holonics::inertia::congruence`]'s refusal, by name, and is not re-implemented here.
pub fn rate_form_congruence(
    state: &ExactRatMatrix,
    metric: &SymmetricForm,
    chart: &ExactRatMatrix,
) -> Result<(SymmetricForm, SymmetricForm), ChordRefusal> {
    let transported_metric = congruence(metric, chart)?;
    let inverse = chart.inverse().map_err(|_| ChordRefusal::SingularChart)?;
    let transported_state = inverse.multiply(state)?.multiply(chart)?;
    let direct = rate_form(&transported_state, &transported_metric)?;
    let transported = congruence(&rate_form(state, metric)?, chart)?;
    Ok((direct, transported))
}

/// **Semisimplicity, exactly: the minimal polynomial is its own squarefree part.**
///
/// This is the hypothesis the seam slogan drops. A defective generator can sit on the imaginary
/// axis spectrally and still admit no conserving receiver — see [`jordan_realification`].
pub fn is_semisimple(state: &ExactRatMatrix) -> Result<bool, ChordRefusal> {
    let minimal = state.minimal_polynomial()?;
    let squarefree = minimal.squarefree_part()?;
    Ok(minimal.made_monic() == squarefree)
}

/// **The space of metrics that make a generator `G`-skew, with the refutation exhibited.**
///
/// `{G symmetric : AᵀG + GA = 0}` is a linear subspace of the symmetric forms, and it is solved
/// here exactly through `exact_linear.rs:770`. The plan's biconditional says a positive definite
/// member exists exactly when `A` is semisimple with purely imaginary spectrum. Both halves are
/// answered concretely:
///
/// - **Refutation.** A positive definite form has every diagonal entry strictly positive, so a
///   diagonal coordinate that vanishes on the *whole* subspace refutes the existence of any
///   positive definite member — completely, not for a sampled candidate. This is the executable
///   form of the Lean theorem `jordan_has_no_conserving_receiver`, and
///   [`jordan_realification`] is exactly the case it refutes.
/// - **Exhibition.** The declared candidate set is the solved basis, its sum, and the Euclidean
///   metric when that is admissible. A positive definite member found among them is returned, and
///   [`holonics::inertia::inertia`] certifies it.
///
/// When neither happens the answer is `None`. Deciding whether a linear subspace of symmetric
/// forms meets the positive definite cone is a feasibility question this receiver does not claim
/// to answer, and it says so rather than defaulting.
///
/// **A remounted space re-derives both of its answers.** A vanishing diagonal is a diagonal
/// coordinate on which the *whole* subspace vanishes, which the exhibited basis decides completely,
/// so the list is recomputed from the basis and refused on disagreement. An exhibited witness is
/// re-certified through [`holonics::inertia::inertia`] and re-solved for membership in the span of the
/// basis, because a positive definite form that is not in the subspace is not a conserving
/// receiver. The subspace is a statement about a generator the struct does not carry, so which
/// forms are in it at all is testimony; everything the exhibited basis decides is decided.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ConservingReceiverSpaceWire")]
pub struct ConservingReceiverSpace {
    pub extent: usize,
    pub basis: Vec<SymmetricForm>,
    /// Diagonal coordinates vanishing on the whole subspace.
    pub vanishing_diagonals: Vec<usize>,
    /// An exhibited positive definite member.
    pub witness: Option<SymmetricForm>,
}

#[derive(Deserialize)]
struct ConservingReceiverSpaceWire {
    extent: usize,
    basis: Vec<SymmetricForm>,
    vanishing_diagonals: Vec<usize>,
    witness: Option<SymmetricForm>,
}

impl TryFrom<ConservingReceiverSpaceWire> for ConservingReceiverSpace {
    type Error = ChordRefusal;

    fn try_from(wire: ConservingReceiverSpaceWire) -> Result<Self, Self::Error> {
        for form in wire.basis.iter().chain(wire.witness.as_ref()) {
            if form.extent() != wire.extent {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a conserving receiver space",
                    relation: "an exhibited form's extent against the declared one",
                    declared: form.extent().to_string(),
                    derived: wire.extent.to_string(),
                });
            }
        }
        // The refutation is read straight off the basis: only the `index`-th diagonal unit
        // contributes to the `(index, index)` entry, so a coordinate vanishes on the subspace
        // exactly when every basis form's diagonal entry there is zero.
        let vanishing_diagonals: Vec<usize> = (0..wire.extent)
            .filter(|index| {
                wire.basis
                    .iter()
                    .all(|form| form.at(*index, *index).is_zero())
            })
            .collect();
        if vanishing_diagonals != wire.vanishing_diagonals {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a conserving receiver space",
                relation: "the vanishing diagonals against the exhibited basis's own",
                declared: format!("{:?}", wire.vanishing_diagonals),
                derived: format!("{vanishing_diagonals:?}"),
            });
        }
        if let Some(witness) = &wire.witness {
            if !inertia(witness).is_positive_definite() {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a conserving receiver space",
                    relation: "the exhibited witness, which Sylvester's signature must certify",
                    declared: format!("{:?}", inertia(witness).signature()),
                    derived: format!("({}, 0)", wire.extent),
                });
            }
            if !form_is_spanned(witness, &wire.basis)? {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a conserving receiver space",
                    relation: "the exhibited witness, which lies in the span of the solved basis",
                    declared: "outside the subspace".to_owned(),
                    derived: "a member of it".to_owned(),
                });
            }
        }
        Ok(Self {
            extent: wire.extent,
            basis: wire.basis,
            vanishing_diagonals: wire.vanishing_diagonals,
            witness: wire.witness,
        })
    }
}

/// Whether a symmetric form is a rational combination of the given ones, decided exactly.
///
/// The forms are flattened to their `extent²` coordinates and the membership question is one
/// preimage solve through `exact_linear.rs:823`. An empty basis spans only the zero form.
fn form_is_spanned(form: &SymmetricForm, basis: &[SymmetricForm]) -> Result<bool, ChordRefusal> {
    let extent = form.extent();
    let coordinates = conserving_equation_count(extent)?;
    let target: Vec<Rat> = (0..extent)
        .flat_map(|row| (0..extent).map(move |column| (row, column)))
        .map(|(row, column)| form.at(row, column).clone())
        .collect();
    if basis.is_empty() {
        return Ok(target.iter().all(Zero::is_zero));
    }
    let rows: Vec<Vec<Rat>> = (0..coordinates)
        .map(|at| {
            let (row, column) = (at / extent, at % extent);
            basis
                .iter()
                .map(|member| member.at(row, column).clone())
                .collect()
        })
        .collect();
    let operator = ExactRatMatrix::shaped(coordinates, basis.len(), rows)?;
    Ok(operator.preimage_fibre(&target)?.is_some())
}

impl ConservingReceiverSpace {
    /// `Some(true)` with a witness, `Some(false)` with a vanishing diagonal, `None` when neither.
    pub fn admits_positive_definite_metric(&self) -> Option<bool> {
        if self.witness.is_some() {
            return Some(true);
        }
        if !self.vanishing_diagonals.is_empty() {
            return Some(false);
        }
        None
    }
}

/// The `extent²` equations `AᵀG + GA = 0` poses, formed with checked arithmetic.
///
/// The extent comes from a declared operator, so the product that sizes the solve is checked
/// rather than wrapped: an extent whose square does not fit a machine integer is refused by name
/// with [`ChordRefusal::StateExtentOverflows`] before anything is allocated from it.
fn conserving_equation_count(extent: usize) -> Result<usize, ChordRefusal> {
    extent
        .checked_mul(extent)
        .ok_or(ChordRefusal::StateExtentOverflows { extent })
}

/// Solve `AᵀG + GA = 0` over the symmetric forms, exactly.
pub fn conserving_receiver_space(
    state: &ExactRatMatrix,
) -> Result<ConservingReceiverSpace, ChordRefusal> {
    if !state.is_square() {
        return Err(ChordRefusal::StateNotSquare {
            rows: state.rows(),
            columns: state.columns(),
        });
    }
    let extent = state.rows();
    if extent == 0 {
        return Err(ChordRefusal::EmptyState);
    }
    // The solve is over `extent²` equations, so that product is formed with checked arithmetic
    // before anything is sized by it.
    let equations = conserving_equation_count(extent)?;
    // The symmetric basis: the `extent` diagonal units first, so a diagonal coordinate is a
    // coordinate of the solution vector and the refutation can be read straight off it.
    let mut basis_forms: Vec<Vec<Vec<Rat>>> = Vec::new();
    for index in 0..extent {
        let mut rows = vec![vec![Rat::zero(); extent]; extent];
        rows[index][index] = Rat::one();
        basis_forms.push(rows);
    }
    for row in 0..extent {
        for column in (row + 1)..extent {
            let mut rows = vec![vec![Rat::zero(); extent]; extent];
            rows[row][column] = Rat::one();
            rows[column][row] = Rat::one();
            basis_forms.push(rows);
        }
    }
    let transposed = state.transpose()?;
    let mut columns: Vec<Vec<Rat>> = Vec::with_capacity(basis_forms.len());
    for form in &basis_forms {
        let matrix = ExactRatMatrix::shaped(extent, extent, form.clone())?;
        let image = transposed
            .multiply(&matrix)?
            .add(&matrix.multiply(state)?)?;
        columns.push(image.entries().to_vec());
    }
    let rows = (0..equations)
        .map(|row| {
            columns
                .iter()
                .map(|column| column[row].clone())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let operator = ExactRatMatrix::shaped(equations, basis_forms.len(), rows)?;
    let kernel = operator.kernel_basis()?;

    let mut basis = Vec::new();
    for coefficients in &kernel {
        let mut accumulated = vec![vec![Rat::zero(); extent]; extent];
        for (index, coefficient) in coefficients.iter().enumerate() {
            if coefficient.is_zero() {
                continue;
            }
            for row in 0..extent {
                for column in 0..extent {
                    accumulated[row][column] = &accumulated[row][column]
                        + coefficient * &basis_forms[index][row][column];
                }
            }
        }
        basis.push(SymmetricForm::from_rows(accumulated)?);
    }
    let vanishing_diagonals = (0..extent)
        .filter(|index| kernel.iter().all(|vector| vector[*index].is_zero()))
        .collect::<Vec<_>>();

    let mut witness = None;
    if !basis.is_empty() {
        let mut candidates = basis.clone();
        let mut sum = vec![vec![Rat::zero(); extent]; extent];
        for form in &basis {
            for (row, line) in sum.iter_mut().enumerate() {
                for (column, entry) in line.iter_mut().enumerate() {
                    *entry = &*entry + form.at(row, column);
                }
            }
        }
        candidates.push(SymmetricForm::from_rows(sum)?);
        // The Euclidean receiver, admissible exactly when `A` is skew-symmetric. It is in the
        // declared candidate set because it is the metric a caller means by default, not because
        // it is the only one that could work.
        let euclidean = SymmetricForm::from_rows(ExactRatMatrix::identity(extent)?.to_rows())?;
        if rate_form(state, &euclidean)? == SymmetricForm::zeros(extent) {
            candidates.push(euclidean);
        }
        witness = candidates
            .into_iter()
            .find(|form| inertia(form).is_positive_definite());
    }
    Ok(ConservingReceiverSpace {
        extent,
        basis,
        vanishing_diagonals,
        witness,
    })
}

/// The realification over `Q` of the complex Jordan block `[[i, 1], [0, i]]`.
///
/// `Z = X + iY` acts on `(x, y)` as `[[X, −Y], [Y, X]]`. Here `X = [[0,1],[0,0]]` and `Y = I`.
/// Characteristic polynomial `(s²+1)²`, spectrum `{i, i, −i, −i}` — entirely on the imaginary axis
/// — and minimal polynomial `(s²+1)²`, so **not semisimple**.
pub fn jordan_realification() -> ExactRatMatrix {
    integer_matrix(&[
        &[0, 1, -1, 0],
        &[0, 0, 0, -1],
        &[1, 0, 0, 1],
        &[0, 1, 0, 0],
    ])
}

/// The realification over `Q` of `diag(i, i)` — the same spectrum, semisimple.
///
/// Characteristic polynomial `(s²+1)²`, minimal polynomial `s²+1`.
pub fn semisimple_realification() -> ExactRatMatrix {
    integer_matrix(&[
        &[0, 0, -1, 0],
        &[0, 0, 0, -1],
        &[1, 0, 0, 0],
        &[0, 1, 0, 0],
    ])
}

fn integer_matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| {
                row.iter()
                    .map(|value| Rat::from_integer(BigInt::from(*value)))
                    .collect()
            })
            .collect(),
    )
    .expect("a declared integer matrix is rectangular")
}

// -------------------------------------------------------------------------------------------------
// the chord

/// One audible or visible component of the chord.
///
/// Every field the plan requires is here: the source and its lineage, the excitation (the column of
/// `B`), the transport path (the row of `C`), the pole's exact name, its residue, the participating
/// state coordinates, the approximation error and the residual.
///
/// **A remounted component is held to the one statement it makes twice.** The pole is named in the
/// factor, in `rational_pole` and again inside the residue, so a rational component must carry
/// `x − pole` as its factor and a `Rational` residue at that pole, an algebraic one must carry an
/// `Algebraic` residue at the same factor, the residue's order is the multiplicity, and
/// `ApproximationError::Exact` is present exactly on the rational case. The isolating interval a
/// component may carry is the *squarefree factor's* first real readout and not necessarily a
/// readout of this component's own factor — the rational roots have been divided out of it — so it
/// is not tested against the factor here; that would refuse lawful components.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ChordComponentWire")]
pub struct ChordComponent {
    pub lineage: String,
    pub source_name: String,
    /// Column of `B`.
    pub excitation: usize,
    pub receiver_name: String,
    /// Row of `C`.
    pub transport_path: usize,
    /// The pole's exact name: a monic squarefree factor of the reduced denominator.
    pub pole_factor: RationalPolynomial,
    pub multiplicity: u32,
    /// Present exactly when the pole is rational.
    pub rational_pole: Option<Rat>,
    pub residue: ChordResidue,
    /// State coordinates that participate, when the pole is a rational eigenvalue with a computed
    /// mode. Empty for an algebraically named pole.
    pub support: Vec<usize>,
    /// **Exactly zero**, or the stated isolating interval used as a readout.
    pub approximation_error: ApproximationError,
    /// Exactly zero. The transfer entry's own certificate residual.
    pub residual: Rat,
}

#[derive(Deserialize)]
struct ChordComponentWire {
    lineage: String,
    source_name: String,
    excitation: usize,
    receiver_name: String,
    transport_path: usize,
    pole_factor: RationalPolynomial,
    multiplicity: u32,
    rational_pole: Option<Rat>,
    residue: ChordResidue,
    support: Vec<usize>,
    approximation_error: ApproximationError,
    residual: Rat,
}

impl TryFrom<ChordComponentWire> for ChordComponent {
    type Error = ChordRefusal;

    fn try_from(wire: ChordComponentWire) -> Result<Self, Self::Error> {
        if wire.multiplicity == 0 {
            return Err(ChordRefusal::PoleOrderDisagrees { order: 0 });
        }
        if wire.pole_factor.degree().is_none_or(|degree| degree == 0) || !wire.pole_factor.is_monic()
        {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a chord component",
                relation: "the pole's exact name, a monic nonconstant factor",
                declared: format!(
                    "degree {:?}, monic {}",
                    wire.pole_factor.degree(),
                    wire.pole_factor.is_monic()
                ),
                derived: "monic of positive degree".to_owned(),
            });
        }
        match (&wire.rational_pole, &wire.residue) {
            (Some(pole), ChordResidue::Rational { pole: named, order, .. }) => {
                if named != pole {
                    return Err(ChordRefusal::ChordWireDisagrees {
                        object: "a chord component",
                        relation: "the rational pole, named once beside the residue and once inside it",
                        declared: pole.to_string(),
                        derived: named.to_string(),
                    });
                }
                let linear = RationalPolynomial::new(vec![-pole.clone(), Rat::one()]);
                if wire.pole_factor != linear {
                    return Err(ChordRefusal::ChordWireDisagrees {
                        object: "a chord component",
                        relation: "the factor naming a rational pole, which is `x − pole`",
                        declared: format!("{:?}", wire.pole_factor.coefficients()),
                        derived: format!("{:?}", linear.coefficients()),
                    });
                }
                if *order != wire.multiplicity {
                    return Err(ChordRefusal::PoleOrderDisagrees { order: *order });
                }
            }
            (None, ChordResidue::Algebraic { factor, order, .. }) => {
                if factor != &wire.pole_factor {
                    return Err(ChordRefusal::ChordWireDisagrees {
                        object: "a chord component",
                        relation: "the pole's factor, named once beside the residue and once inside it",
                        declared: format!("{:?}", wire.pole_factor.coefficients()),
                        derived: format!("{:?}", factor.coefficients()),
                    });
                }
                if *order != wire.multiplicity {
                    return Err(ChordRefusal::PoleOrderDisagrees { order: *order });
                }
            }
            _ => {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a chord component",
                    relation: "the residue's species against whether the pole is rational",
                    declared: format!("rational pole {}", wire.rational_pole.is_some()),
                    derived: format!(
                        "rational residue {}",
                        matches!(wire.residue, ChordResidue::Rational { .. })
                    ),
                });
            }
        }
        let exact = matches!(wire.approximation_error, ApproximationError::Exact);
        if exact != wire.rational_pole.is_some() {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a chord component",
                relation: "the approximation error, which is exact on exactly the rational poles",
                declared: format!("exact {exact}"),
                derived: format!("exact {}", wire.rational_pole.is_some()),
            });
        }
        if wire.support.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a chord component",
                relation: "the participating state coordinates",
                declared: format!("{:?}", wire.support),
                derived: "strictly ascending coordinates".to_owned(),
            });
        }
        if !wire.residual.is_zero() {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a chord component",
                relation: "the transfer entry's certificate residual, which is exactly zero",
                declared: wire.residual.to_string(),
                derived: "0".to_owned(),
            });
        }
        Ok(Self {
            lineage: wire.lineage,
            source_name: wire.source_name,
            excitation: wire.excitation,
            receiver_name: wire.receiver_name,
            transport_path: wire.transport_path,
            pole_factor: wire.pole_factor,
            multiplicity: wire.multiplicity,
            rational_pole: wire.rational_pole,
            residue: wire.residue,
            support: wire.support,
            approximation_error: wire.approximation_error,
            residual: wire.residual,
        })
    }
}

/// What a component's numbers cost in exactness. There is no third case.
///
/// **Its wire adds nothing of its own.** Two variants carry no data, and the third carries an
/// [`ExactInterval`], which is already closed at its own wire. *Which* variant a component may
/// carry is the relation that matters, and that is one field's agreement with another, so it is
/// enforced at [`ChordComponent`] where both fields are in hand.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ApproximationError {
    /// The component is exact: a rational pole, an exact residue, an exact support.
    Exact,
    /// The pole is named by its exact factor; the interval is a Sturm-certified readout of one of
    /// its real roots and is not the object.
    IsolatingInterval(ExactInterval),
    /// The pole is named by its exact factor and no real isolation was requested or exists.
    FactorOnly,
}

/// **The causal chord of a linearization.**
///
/// **A remounted chord is held to the agreements between its parts.** The pole atlas is the atlas
/// of the transfer matrix's own atlas denominator, the hidden modes are the transfer matrix's own
/// atlas cancellation, and every component names a transfer entry that is present and carries that
/// entry's names and residual. Each component's pole factor is divided into that entry's reduced
/// denominator exactly, which refuses a component invented at a pole the entry does not have.
/// Semisimplicity is a statement about the generator, which the chord does not carry, so it is
/// testimony.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "CausalChordWire")]
pub struct CausalChord {
    pub schema: String,
    pub lineage: String,
    pub extent: usize,
    pub transfer: TransferFunction,
    pub poles: PoleAtlas,
    pub components: Vec<ChordComponent>,
    pub modes: Vec<ModeSupport>,
    /// Modes no declared source excites or no declared receiver observes: the cancellation, named.
    pub hidden_modes: RationalPolynomial,
    pub semisimple: bool,
}

#[derive(Deserialize)]
struct CausalChordWire {
    schema: String,
    lineage: String,
    extent: usize,
    transfer: TransferFunction,
    poles: PoleAtlas,
    components: Vec<ChordComponent>,
    modes: Vec<ModeSupport>,
    hidden_modes: RationalPolynomial,
    semisimple: bool,
}

impl TryFrom<CausalChordWire> for CausalChord {
    type Error = ChordRefusal;

    fn try_from(wire: CausalChordWire) -> Result<Self, Self::Error> {
        if wire.extent != wire.transfer.extent {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a causal chord",
                relation: "the declared extent against the transfer matrix's own",
                declared: wire.extent.to_string(),
                derived: wire.transfer.extent.to_string(),
            });
        }
        if wire.poles.denominator != wire.transfer.atlas_denominator {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a causal chord",
                relation: "the pole atlas's denominator against the transfer atlas denominator",
                declared: format!("{:?}", wire.poles.denominator.coefficients()),
                derived: format!("{:?}", wire.transfer.atlas_denominator.coefficients()),
            });
        }
        if wire.hidden_modes != wire.transfer.atlas_cancellation {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "a causal chord",
                relation: "the hidden modes against the transfer matrix's atlas cancellation",
                declared: format!("{:?}", wire.hidden_modes.coefficients()),
                derived: format!("{:?}", wire.transfer.atlas_cancellation.coefficients()),
            });
        }
        for component in &wire.components {
            let Some(entry) = wire
                .transfer
                .entry(component.transport_path, component.excitation)
            else {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a causal chord",
                    relation: "a component's port pair against the transfer matrix's entries",
                    declared: format!(
                        "({}, {})",
                        component.transport_path, component.excitation
                    ),
                    derived: "a port pair the atlas carries".to_owned(),
                });
            };
            if component.source_name != entry.source_name
                || component.receiver_name != entry.receiver_name
            {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a causal chord",
                    relation: "a component's port names against its own transfer entry's",
                    declared: format!("{} / {}", component.source_name, component.receiver_name),
                    derived: format!("{} / {}", entry.source_name, entry.receiver_name),
                });
            }
            if component.residual != entry.residual {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a causal chord",
                    relation: "a component's residual against its own transfer entry's",
                    declared: component.residual.to_string(),
                    derived: entry.residual.to_string(),
                });
            }
            if component.lineage != wire.lineage {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a causal chord",
                    relation: "a component's lineage against the chord's own",
                    declared: component.lineage.clone(),
                    derived: wire.lineage.clone(),
                });
            }
            // The component's pole is a pole of the entry it came from, or it is not its pole.
            entry
                .reduced_denominator
                .divided_exactly_by(&component.pole_factor)?;
        }
        for pair in wire.modes.windows(2) {
            if pair[0].eigenvalue >= pair[1].eigenvalue {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "a causal chord",
                    relation: "the rational mode population, ascending with each eigenvalue once",
                    declared: format!("{} then {}", pair[0].eigenvalue, pair[1].eigenvalue),
                    derived: "strictly ascending".to_owned(),
                });
            }
        }
        Ok(Self {
            schema: wire.schema,
            lineage: wire.lineage,
            extent: wire.extent,
            transfer: wire.transfer,
            poles: wire.poles,
            components: wire.components,
            modes: wire.modes,
            hidden_modes: wire.hidden_modes,
            semisimple: wire.semisimple,
        })
    }
}

impl CausalChord {
    pub fn characteristic(&self) -> &RationalPolynomial {
        self.transfer.characteristic()
    }

    /// Components carrying this transport path.
    pub fn through(&self, transport_path: usize) -> Vec<&ChordComponent> {
        self.components
            .iter()
            .filter(|component| component.transport_path == transport_path)
            .collect()
    }
}

/// The chord at the certified reading.
pub fn causal_chord(linearization: &Linearization) -> Result<CausalChord, ChordRefusal> {
    causal_chord_read(linearization, PoleReading::Certified)
}

/// The chord at a declared reading.
pub fn causal_chord_read(
    linearization: &Linearization,
    reading: PoleReading,
) -> Result<CausalChord, ChordRefusal> {
    let transfer = transfer_function(linearization)?;
    let poles = pole_atlas(&transfer.atlas_denominator, reading)?;
    let modes = rational_mode_supports(linearization)?;
    let semisimple = is_semisimple(&linearization.state)?;

    let mut components = Vec::new();
    for entry in &transfer.entries {
        let entry_atlas = pole_atlas(&entry.reduced_denominator, reading)?;
        for factor in &entry_atlas.factors {
            if factor.degree == 0 {
                continue;
            }
            // A rational pole gets its own component with exact Laurent coefficients; the rest of
            // the factor is one component named by the factor.
            for pole in &factor.rational_poles {
                let laurent = rational_laurent(
                    &entry.reduced_numerator,
                    &entry.reduced_denominator,
                    pole,
                    factor.multiplicity,
                )?;
                let support = modes
                    .iter()
                    .find(|mode| mode.eigenvalue == *pole)
                    .map(|mode| mode.support.clone())
                    .unwrap_or_default();
                components.push(ChordComponent {
                    lineage: linearization.lineage.clone(),
                    source_name: entry.source_name.clone(),
                    excitation: entry.excitation,
                    receiver_name: entry.receiver_name.clone(),
                    transport_path: entry.transport_path,
                    pole_factor: RationalPolynomial::new(vec![-pole.clone(), Rat::one()]),
                    multiplicity: factor.multiplicity,
                    rational_pole: Some(pole.clone()),
                    residue: ChordResidue::Rational {
                        pole: pole.clone(),
                        order: factor.multiplicity,
                        laurent,
                    },
                    support,
                    approximation_error: ApproximationError::Exact,
                    residual: entry.residual.clone(),
                });
            }
            // Whatever the rational roots do not account for.
            let mut algebraic = factor.factor.clone();
            for pole in &factor.rational_poles {
                algebraic = algebraic
                    .divided_exactly_by(&RationalPolynomial::new(vec![
                        -pole.clone(),
                        Rat::one(),
                    ]))?;
            }
            if algebraic.degree().unwrap_or(0) == 0 {
                continue;
            }
            let algebraic = algebraic.made_monic();
            let laurent = algebraic_laurent(
                &entry.reduced_numerator,
                &entry.reduced_denominator,
                &algebraic,
                factor.multiplicity,
            )?;
            let approximation_error = factor
                .real_isolations
                .first()
                .cloned()
                .map_or(ApproximationError::FactorOnly, |interval| {
                    ApproximationError::IsolatingInterval(interval)
                });
            components.push(ChordComponent {
                lineage: linearization.lineage.clone(),
                source_name: entry.source_name.clone(),
                excitation: entry.excitation,
                receiver_name: entry.receiver_name.clone(),
                transport_path: entry.transport_path,
                pole_factor: algebraic.clone(),
                multiplicity: factor.multiplicity,
                rational_pole: None,
                residue: ChordResidue::Algebraic {
                    factor: algebraic,
                    order: factor.multiplicity,
                    laurent,
                },
                support: Vec::new(),
                approximation_error,
                residual: entry.residual.clone(),
            });
        }
    }
    let hidden_modes = transfer.atlas_cancellation.clone();
    Ok(CausalChord {
        schema: CAUSAL_CHORD_SCHEMA.to_owned(),
        lineage: linearization.lineage.clone(),
        extent: transfer.extent,
        transfer,
        poles,
        components,
        modes,
        hidden_modes,
        semisimple,
    })
}

// -------------------------------------------------------------------------------------------------
// the separating atlas

/// The probe at which two isospectral systems part company.
///
/// **A remounted separation must still separate.** The two numerators at the named probe are
/// refused unless they actually differ — a separation whose two readings agree is not one — the
/// named probe is the first of the declared probe list, as the constructor takes it, no probe is
/// listed twice, and the shared characteristic polynomial is monic, which is what makes the claim
/// that the spectrum cannot tell the two apart a claim about one polynomial.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "AtlasSeparationWire")]
pub struct AtlasSeparation {
    pub left_lineage: String,
    pub right_lineage: String,
    /// The characteristic polynomial the two share. **The spectrum cannot tell them apart.**
    pub shared_characteristic: RationalPolynomial,
    /// Row of `C` at which they differ.
    pub transport_path: usize,
    /// Column of `B` at which they differ.
    pub excitation: usize,
    pub left_numerator: RationalPolynomial,
    pub right_numerator: RationalPolynomial,
    /// Every probe/readout pair at which the two differ, not only the first.
    pub separating_probes: Vec<(usize, usize)>,
}

#[derive(Deserialize)]
struct AtlasSeparationWire {
    left_lineage: String,
    right_lineage: String,
    shared_characteristic: RationalPolynomial,
    transport_path: usize,
    excitation: usize,
    left_numerator: RationalPolynomial,
    right_numerator: RationalPolynomial,
    separating_probes: Vec<(usize, usize)>,
}

impl TryFrom<AtlasSeparationWire> for AtlasSeparation {
    type Error = ChordRefusal;

    fn try_from(wire: AtlasSeparationWire) -> Result<Self, Self::Error> {
        if wire.left_numerator == wire.right_numerator {
            return Err(ChordRefusal::NoSeparatingProbe);
        }
        if wire.separating_probes.first() != Some(&(wire.transport_path, wire.excitation)) {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "an atlas separation",
                relation: "the named probe against the first of the declared separating probes",
                declared: format!("({}, {})", wire.transport_path, wire.excitation),
                derived: format!("{:?}", wire.separating_probes.first()),
            });
        }
        for (at, probe) in wire.separating_probes.iter().enumerate() {
            if wire.separating_probes[..at].contains(probe) {
                return Err(ChordRefusal::ChordWireDisagrees {
                    object: "an atlas separation",
                    relation: "a separating probe listed twice",
                    declared: format!("({}, {})", probe.0, probe.1),
                    derived: "listed once".to_owned(),
                });
            }
        }
        if wire.shared_characteristic.degree().is_none() || !wire.shared_characteristic.is_monic() {
            return Err(ChordRefusal::ChordWireDisagrees {
                object: "an atlas separation",
                relation: "the shared characteristic polynomial, which is monic and nonzero",
                declared: format!(
                    "degree {:?}, monic {}",
                    wire.shared_characteristic.degree(),
                    wire.shared_characteristic.is_monic()
                ),
                derived: "monic and nonzero".to_owned(),
            });
        }
        Ok(Self {
            left_lineage: wire.left_lineage,
            right_lineage: wire.right_lineage,
            shared_characteristic: wire.shared_characteristic,
            transport_path: wire.transport_path,
            excitation: wire.excitation,
            left_numerator: wire.left_numerator,
            right_numerator: wire.right_numerator,
            separating_probes: wire.separating_probes,
        })
    }
}

/// **Two isospectral systems, separated by the response atlas under a declared probe.**
///
/// Refuses when the characteristic polynomials differ — then the spectrum already separates them
/// and the atlas has nothing to prove — and refuses when no probe separates them.
pub fn separate_under_probe(
    left: &Linearization,
    right: &Linearization,
) -> Result<AtlasSeparation, ChordRefusal> {
    let left_transfer = transfer_function(left)?;
    let right_transfer = transfer_function(right)?;
    if left_transfer.characteristic() != right_transfer.characteristic() {
        return Err(ChordRefusal::NotIsospectral);
    }
    if left.receiver_count() != right.receiver_count()
        || left.source_count() != right.source_count()
    {
        return Err(ChordRefusal::AtlasShapesDiffer);
    }
    let mut separating_probes = Vec::new();
    for entry in &left_transfer.entries {
        let Some(other) = right_transfer.entry(entry.transport_path, entry.excitation) else {
            return Err(ChordRefusal::AtlasShapesDiffer);
        };
        if entry.numerator != other.numerator {
            separating_probes.push((entry.transport_path, entry.excitation));
        }
    }
    let Some((transport_path, excitation)) = separating_probes.first().copied() else {
        return Err(ChordRefusal::NoSeparatingProbe);
    };
    let left_numerator = left_transfer
        .entry(transport_path, excitation)
        .expect("the separating probe was found in this atlas")
        .numerator
        .clone();
    let right_numerator = right_transfer
        .entry(transport_path, excitation)
        .expect("the separating probe was found in the other atlas")
        .numerator
        .clone();
    Ok(AtlasSeparation {
        left_lineage: left.lineage.clone(),
        right_lineage: right.lineage.clone(),
        shared_characteristic: left_transfer.characteristic().clone(),
        transport_path,
        excitation,
        left_numerator,
        right_numerator,
        separating_probes,
    })
}

// -------------------------------------------------------------------------------------------------
// the elastic network of a rigidity Jacobian

/// Which linearized network response is being built from a constraint Jacobian.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NetworkForm {
    /// `A = −JᵀJ`: the overdamped relaxation of the quadratic constraint energy `|J v|²/2` at unit
    /// mobility. Symmetric negative semidefinite, so the spectrum is real and
    /// [`half_plane_from_symmetric`] reads it through [`holonics::inertia::inertia`]. Its kernel is
    /// exactly the infinitesimal motion space `ker J` the rigidity receiver already returns.
    OverdampedRelaxation,
}

/// **The linearized network response of a constraint Jacobian, as a probed linearization.**
///
/// The Jacobian is the exact rational matrix `rigidity_receiver.rs` returns; nothing is recomputed
/// here. `probe` and `readout_site` are *coordinate* indices into the flattened `d·n` configuration
/// space, so a caller declares an occurrence and an axis by their flattened address.
pub fn elastic_network(
    lineage: impl Into<String>,
    jacobian: &ExactRatMatrix,
    form: NetworkForm,
    probe: usize,
    readout_site: usize,
) -> Result<Linearization, ChordRefusal> {
    match form {
        NetworkForm::OverdampedRelaxation => {}
    }
    let state = jacobian
        .transpose()?
        .multiply(jacobian)?
        .scaled(&(-Rat::one()));
    Linearization::single_probe(lineage, state, probe, readout_site)
}

// -------------------------------------------------------------------------------------------------
// refusals

#[derive(Debug, Error)]
pub enum ChordRefusal {
    #[error("a linearization's state operator must be square, not {rows}×{columns}")]
    StateNotSquare { rows: usize, columns: usize },
    #[error("a linearization on no state has no transfer object")]
    EmptyState,
    #[error(
        "a state of extent {extent} overflows the machine integer counting the {extent}² equations its conserving-form solve poses"
    )]
    StateExtentOverflows { extent: usize },
    #[error("the excitation has {rows} rows against a state of extent {extent}")]
    ExcitationShape { extent: usize, rows: usize },
    #[error("the readout has {columns} columns against a state of extent {extent}")]
    ReadoutShape { extent: usize, columns: usize },
    #[error("{declared} source names were declared for {columns} excitation columns")]
    SourceNameCount { declared: usize, columns: usize },
    #[error("{declared} receiver names were declared for {rows} readout rows")]
    ReceiverNameCount { declared: usize, rows: usize },
    #[error("port {port} lies outside a state of extent {extent}")]
    PortOutsideState { extent: usize, port: usize },
    #[error("a chart for extent {extent} cannot be {rows}×{columns}")]
    ChartShape {
        extent: usize,
        rows: usize,
        columns: usize,
    },
    #[error("a singular chart is not a change of basis")]
    SingularChart,
    #[error("a metric of extent {metric} does not pair with a state of extent {extent}")]
    MetricShape { extent: usize, metric: usize },
    #[error("the Faddeev--LeVerrier adjugate failed its exact certificate")]
    AdjugateCertificateFailure,
    #[error(
        "the transfer numerator for transport path {transport_path} and excitation {excitation} \
         failed its exact certificate"
    )]
    TransferCertificateFailure {
        transport_path: usize,
        excitation: usize,
    },
    #[error("the exact resolvent failed its inverse certificate")]
    ResolventCertificateFailure,
    #[error("the declared probe point is a pole of the resolvent")]
    ProbePointIsAPole,
    #[error(
        "the half-plane count did not close after {ceiling} shift refinements; the polynomial is \
         refused rather than reported from an unclosed count"
    )]
    HalfPlaneRefinementExhausted { ceiling: u32 },
    #[error("the Cauchy index {index} has the wrong parity against degree {degree}")]
    HalfPlaneParityFailure { degree: usize, index: i64 },
    #[error("the declared pole order {order} does not divide the denominator that many times")]
    PoleOrderDisagrees { order: u32 },
    #[error("the residue's denominator is not invertible modulo the pole's factor")]
    ResidueDenominatorNotInvertible,
    #[error("the two linearizations are not isospectral, so the spectrum already separates them")]
    NotIsospectral,
    #[error("the two response atlases do not have the same shape and cannot be compared")]
    AtlasShapesDiffer,
    #[error("no declared probe separates the two isospectral systems")]
    NoSeparatingProbe,
    #[error(
        "a remounted resolvent expansion declares {declared} for {relation}, where the expansion it \
         carries gives {derived}"
    )]
    ExpansionWireDisagrees {
        relation: &'static str,
        declared: String,
        derived: String,
    },
    #[error(
        "a remounted transfer chart declares {declared} for {relation}, where the polynomials it \
         carries give {derived}"
    )]
    TransferWireDisagrees {
        relation: &'static str,
        declared: String,
        derived: String,
    },
    #[error(
        "a remounted pole chart declares {declared} for {relation}, where the factors it carries \
         give {derived}"
    )]
    PoleWireDisagrees {
        relation: &'static str,
        declared: String,
        derived: String,
    },
    #[error(
        "{object} declares {declared} for {relation}, where the chart it carries gives {derived}"
    )]
    ChordWireDisagrees {
        object: &'static str,
        relation: &'static str,
        declared: String,
        derived: String,
    },
    #[error("the exact spectrum refused: {0}")]
    Spectrum(String),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Polynomial(#[from] ExactPolynomialError),
    #[error(transparent)]
    Value(#[from] ExactValueError),
    #[error(transparent)]
    Inertia(#[from] InertiaError),
}

impl PartialEq for ChordRefusal {
    fn eq(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }
}

/// A convenience for callers that want the components grouped by transport path.
pub fn components_by_path(chord: &CausalChord) -> BTreeMap<usize, Vec<&ChordComponent>> {
    let mut grouped: BTreeMap<usize, Vec<&ChordComponent>> = BTreeMap::new();
    for component in &chord.components {
        grouped
            .entry(component.transport_path)
            .or_default()
            .push(component);
    }
    grouped
}

#[cfg(test)]
#[path = "causal_chord/tests.rs"]
mod tests;
