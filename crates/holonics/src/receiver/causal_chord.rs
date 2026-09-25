//! **The causal chord: the exact transfer object of a linearization, and its resolvent.**
//!
//! [definition] For a local linearization
//!
//! ```text
//! x' = A x + B u,    y = C x
//! ```
//!
//! the receiver-relative transfer object is `H(s) = C (sI − A)^{-1} B`. This module owns it as an
//! **exact matrix of rational functions over `Q`** — never a float, never a sampled frequency
//! response — together with everything a returned component must carry: its source
//! lineage, its excitation (which column of `B`), its transport path (which row of `C`), its
//! approximation error (exactly zero, or a stated isolating interval used only as a readout) and
//! its residual (exactly zero, certified **coefficientwise**: `(sI−A)·adj(sI−A) = det(sI−A)·I` and
//! `num_{ij}(s) = (C adj(sI−A) B)_{ij}` are verified as polynomial identities, one matrix equation
//! per power of `s`, not sampled at a point).
//!
//! The paired Lean owner is
//! `Foundation/CausalChord`
//!. Each theorem there appears here as a test or an
//! invariant; each definition here is the executable equivalent of the Lean object.
//!
//! # The governing correction: no object has one intrinsic chord
//!
//! [definition] **Isospectral objects exist**, so one global
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
//! already owned by [`crate::ratio::linear::ExactRatMatrix::characteristic_polynomial`]
//!, which discards the intermediate `M_k`; this module recomputes the
//! recurrence because it needs them, and
//! `the_expansion_agrees_with_the_existing_characteristic_owner` holds the two to exact agreement
//! at every reading. Nothing here reimplements rank, kernel, inverse or spectrum: those are
//! the exact linear carrier's.
//!
//! # Cancellation is reported, never lost
//!
//! [definition] `C_i adj(sI−A) B_j / det(sI−A)` is not in lowest terms. The common factor is
//! exactly the modes that source `j` cannot excite or receiver `i` cannot observe — the
//! uncontrollable and unobservable directions — and they must stay **visible as
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
//! [`crate::ratio::polynomial::RationalPolynomial::squarefree_decomposition`], so each pole
//! carries its **multiplicity as an index, not a guess**. Rational poles are returned as exact
//! rationals. Every other pole is named by the exact squarefree factor it is a root of. Under
//! [`PoleReading::Certified`] each factor additionally reports Sturm-certified isolating boxes for
//! its real roots — obtained from the existing owner
//! [`crate::ratio::polynomial::rational_root_census`], whose
//! isolation is for the monic companion `c^{n−1}A(z/c)` and is rescaled here by the leading
//! coefficient — and a sign-certified half-plane count. **The interval is a readout. The factor is
//! the pole's name.**
//!
//! [proved-derived; implemented-exact] The half-plane count was the one piece of polynomial
//! machinery this module had to write, because the repository had no owner for it. **It is no
//! longer this module's**: the signed remainder sequence a Cauchy index reads is the Sturm chain
//! read at `±∞` instead of at a point, so the routine lives in
//! [`crate::ratio::polynomial`] beside [`crate::ratio::algebraic::SturmChain`] and the root census,
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
//! [`crate::ratio::linear::inertia::inertia`], and [`rate_form_congruence`] routes a chart
//! change to [`crate::ratio::linear::inertia::congruence`], which refuses a singular chart by
//! name. The rate reading
//! is read through that owner rather than a second one.
//!
//! # Non-normal operators: the resolvent, not the spectrum, governs response
//!
//! [proved-derived; implemented-exact] For a non-normal `A` the
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
//! part", through [`crate::ratio::linear::ExactRatMatrix::minimal_polynomial`]
//!. A defective generator can sit on the seam spectrally and still have no
//! conserving receiver.

use std::collections::BTreeSet;

use crate::ratio::{GaussianRat, Rat};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use thiserror::Error;

use crate::ratio::algebraic::{ExactInterval, ExactValueError};
use crate::ratio::linear::inertia::{Inertia, InertiaError, SymmetricForm, congruence, inertia};
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};
use crate::ratio::polynomial::{
    ExactPolynomialError, RationalPolynomial, rational_root_census, rational_roots_by_lifting,
};

// -------------------------------------------------------------------------------------------------
// the linearization

/// **A local linearization `(A, B, C)` in exact rationals, with named ports.**
///
/// Every returned component carries its source and
/// its transport path, so a column of `B` and a row of `C` each carry the name the caller declared
/// for it, and [`ChordComponent`] repeats both.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Linearization {
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

    pub(crate) fn receiver_count(&self) -> usize {
        self.readout.rows()
    }

    /// **The chart change.** `(A, B, C) ↦ (T A T^{-1}, T B, C T^{-1})`.
    ///
    /// The Lean owner's `rebase_numerator` / `rebase_denominator` / `rebase_transfer` prove that the
    /// transfer object is invariant under this, which is exactly why it is a *chart* change and not
    /// a different object. A singular `T` is refused by name, for the same reason
    /// [`crate::ratio::linear::inertia::congruence`] refuses one.
    pub fn rebased(&self, chart: &ExactRatMatrix) -> Result<Self, ChordRefusal> {
        if !chart.is_square() || chart.rows() != self.extent() {
            return Err(ChordRefusal::ChartShape {
                extent: self.extent(),
                rows: chart.rows(),
                columns: chart.columns(),
            });
        }
        let inverse = chart.inverse().map_err(|_| ChordRefusal::SingularChart)?;
        Ok(Self {
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
pub(crate) fn resolvent_expansion(
    state: &ExactRatMatrix,
) -> Result<ResolventExpansion, ChordRefusal> {
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
#[derive(Clone, Debug, PartialEq, Eq)]
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

impl TransferEntry {
    /// Whether this source/receiver pair sees a cancellation at all.
    pub fn cancels(&self) -> bool {
        self.cancelled.degree().is_some_and(|degree| degree > 0)
    }
}

/// **The exact transfer matrix of a linearization.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransferFunction {
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
pub(crate) fn transfer_function(
    linearization: &Linearization,
) -> Result<TransferFunction, ChordRefusal> {
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
/// [definition] The shared half-plane counter is owned by `crate::ratio::polynomial`, beside the Sturm chain the Cauchy index is built from
/// and beside `rational_root_census`, because those are the same machinery: the signed remainder
/// sequence over `Z` with tracked signs is [`crate::ratio::algebraic::SturmChain`], and reading it at
/// `±∞` rather than at a point is the only difference between a Sturm count and a Cauchy index.
/// The chart adapters below map refusals into [`ChordRefusal`]'s own species so a caller matching on
/// [`ChordRefusal::HalfPlaneParityFailure`] or
/// [`ChordRefusal::HalfPlaneRefinementExhausted`] still sees them.
use crate::ratio::polynomial::HalfPlaneCount;

/// The number of roots of `p` on the imaginary axis, with multiplicity.
///
/// Re-entry into [`crate::ratio::polynomial::axis_root_count`].
pub fn axis_root_count(polynomial: &RationalPolynomial) -> Result<usize, ChordRefusal> {
    crate::ratio::polynomial::axis_root_count(polynomial).map_err(chord_refusal)
}

/// **The exact half-plane population of a real polynomial's roots, with multiplicity.**
///
/// Re-entry into [`crate::ratio::polynomial::half_plane_count`], which is the owner.
pub fn half_plane_count(polynomial: &RationalPolynomial) -> Result<HalfPlaneCount, ChordRefusal> {
    crate::ratio::polynomial::half_plane_count(polynomial).map_err(chord_refusal)
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
/// positive, null and negative indices of the form. This routes to [`crate::ratio::linear::inertia::inertia`]
/// rather than running the Routh–Hurwitz machinery, which is both cheaper and
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
#[derive(Clone, Debug, PartialEq, Eq)]
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

/// The complete pole population of one denominator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoleAtlas {
    pub denominator: RationalPolynomial,
    pub reading: PoleReading,
    pub factors: Vec<PoleFactor>,
    /// For the whole denominator, with multiplicity. Present only under [`PoleReading::Certified`].
    pub half_plane: Option<HalfPlaneCount>,
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
/// [`rational_root_census`] is complete and certified, but its
/// descent runs from an absolute Cauchy bound that, on a characteristic polynomial built from a
/// physical network operator, is astronomically wider than the roots themselves — the same
/// pathology the former lattice-gauge receiver records and rebases away. [`rational_roots_by_lifting`]
/// answers the same question through one prime receiver and
/// verifies every returned candidate by exact evaluation, so it is a certificate and not a
/// heuristic. When no prime leaves every residue root simple it refuses by name, and the census is
/// the declared fallback.
fn rational_poles_by_lifting(polynomial: &RationalPolynomial) -> Result<Vec<Rat>, ChordRefusal> {
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
        return Err(ChordRefusal::PoleOrderDisagrees { order });
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
/// the exact linear carrier; the multiplicities are read by exact division. Nothing here
/// recomputes a kernel, a rank or a root.
pub(crate) fn rational_mode_supports(
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
        let shifted = linearization.state.subtract(&identity.scaled(eigenvalue))?;
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

/// `(sI − A)^{-1}` and `C (sI − A)^{-1} B` at one exact probe point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolventProbe {
    pub lineage: String,
    /// The probe point `s = σ + iω`, a Gaussian rational ([`GaussianRat`]): exact, with no float
    /// anywhere near it.
    pub point: GaussianRat,
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

/// The exact resolvent at a Gaussian-rational point, by realification over `Q`.
///
/// `sI − A` with `s = σ + iω` realifies to `[[σI − A, −ωI], [ωI, σI − A]]`, whose exact rational
/// inverse is `[[X, −Y], [Y, X]]` for `(sI−A)^{-1} = X + iY`.
pub fn resolvent_probe(
    linearization: &Linearization,
    point: &GaussianRat,
) -> Result<ResolventProbe, ChordRefusal> {
    let extent = linearization.extent();
    let identity = ExactRatMatrix::identity(extent)?;
    let real_block = identity.scaled(&point.re).subtract(&linearization.state)?;
    let imaginary_block = identity.scaled(&point.im);
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
/// [`crate::ratio::linear::inertia::congruence`]'s refusal, by name, and is not re-implemented here.
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
/// here exactly through the exact linear carrier. The biconditional says a positive definite
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
///   [`crate::ratio::linear::inertia::inertia`] certifies it.
///
/// When neither happens the answer is `None`. Deciding whether a linear subspace of symmetric
/// forms meets the positive definite cone is a feasibility question this receiver does not claim
/// to answer, and it says so rather than defaulting.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConservingReceiverSpace {
    pub extent: usize,
    pub basis: Vec<SymmetricForm>,
    /// Diagonal coordinates vanishing on the whole subspace.
    pub vanishing_diagonals: Vec<usize>,
    /// An exhibited positive definite member.
    pub witness: Option<SymmetricForm>,
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
                    accumulated[row][column] =
                        &accumulated[row][column] + coefficient * &basis_forms[index][row][column];
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
    integer_matrix(&[&[0, 1, -1, 0], &[0, 0, 0, -1], &[1, 0, 0, 1], &[0, 1, 0, 0]])
}

/// The realification over `Q` of `diag(i, i)` — the same spectrum, semisimple.
///
/// Characteristic polynomial `(s²+1)²`, minimal polynomial `s²+1`.
pub fn semisimple_realification() -> ExactRatMatrix {
    integer_matrix(&[&[0, 0, -1, 0], &[0, 0, 0, -1], &[1, 0, 0, 0], &[0, 1, 0, 0]])
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
#[derive(Clone, Debug, PartialEq, Eq)]
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

/// What a component's numbers cost in exactness. There is no third case.
#[derive(Clone, Debug, PartialEq, Eq)]
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CausalChord {
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
pub(crate) fn causal_chord_read(
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
                algebraic = algebraic.divided_exactly_by(&RationalPolynomial::new(vec![
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
#[derive(Clone, Debug, PartialEq, Eq)]
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

#[cfg(test)]
mod tests;
