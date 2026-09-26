//! **The local tick: the junction Swing, the ring element and the contact's midpoint two-port.**
//!
//! [definition] One tick is one contact hop (design (a), "The law of one passage", `tick`). Every
//! operand is fixed at the cut ([`Operands::at_cut`]): the pair quadrance and so each contact's
//! conductance from the rings' phases, the admittances from the declaration, the element's `K_r`
//! from the sheet classes of the standing contrast. Within a word each tick is therefore one fixed
//! map of the change: the medium's Green's function.
//!
//! ```text
//! junction  G_a = κ_a Y_a,  κ_a = 2^(s_a),  s_a = −β_a Q_a / 2 = n_a + φ_a/L          one exponent per contact
//!           v_r = (Y_r s_r + Σ_a G_a a_(r←a)) / (Y_r + Σ_a G_a)                       participation is the anchor
//!           o_(r→a) = 2 v_r − a_(r←a),  b_r = 2 v_r − s_r,  c_r = v_r − s_r            the junction Swing
//! element   (I − ½K_r) s_r′ = (I + ½K_r) b_r + W_c,r c_r,   K_r = W_s,r + Σ_ρ σ_ρ,r A_ρ,r
//!           s_r′ = (I − ½K_r)⁻¹ (2b_r + W_c,r c_r) − b_r                               one solve
//! transit   m_a ζ_a = h(α_g − α_h) + 2C_a w_a − h K_a u_a,
//!           m_a = 1 + (G_a/2h)(2C_a + h D_a + (h²/2) K_a),   ω_a = (G_a/2h) ζ_a           one solve
//!           w ← 2ω − w,  u ← u + hω,  a_(g←a) = o_(g→a) − ι_g ζ_a/h,  a_(h←a) = o_(h→a) + ι_h ζ_a/h
//! power     P = (h/4)[Σ_r Y_r |s_r|² + Σ_(r,a) G_a |a_(r←a)|²] + Σ_a (½ w*C w + ½ u*K u)
//!           P(t+1) = P(t) − h Σ_a ω*D ω + (h/2) Σ_r Y_r ⟨x̄_r, W_s x̄_r⟩ + Π_c,
//!           Π_c = (h/2) Σ_r Y_r ⟨x̄_r, W_c c_r⟩,   x̄_r = ½(b_r + s_r′)
//! ```
//!
//! The contact's solve is `M_a ω_a = h(α_g − α_h) + 2C_a w_a − h K_a u_a` with
//! `M_a = 2C_a + (2h/G_a)I + hD_a + (h²/2)K_a = (2h/G_a) m_a`, written through the normalized
//! `m_a ⪰ 1`, whose inverse has `‖m_a⁻¹‖₂ ≤ 1` whatever the conductance: the exchange `(2/G_a)ω_a`
//! is `ζ_a/h`, and a shielded contact (`G_a` far below one) carries its small rate `ω_a` exactly as
//! the product `(G_a/2h)ζ_a`, never as a chart of `M_a⁻¹` below the lattice.
//!
//! [definition] **The Swing is local** (guard 14): every solve here is a junction's own admittance
//! sum, a ring's own `I − ½K_r` (bijective for passive `K_r`, `Holon/Cayley.cayley_bijective`), or a
//! contact's own `k_a × k_a` `m_a` (positive definite for PSD squared carriers and `G_a > 0`). No
//! global solve over the contact graph exists; the cone test checks the support exactly.
//!
//! [definition; agent-inferred] **The executed tick on declared lattices** (Decision 24;
//! [`crate::hnn::chart`]). A field's word carries each inverse as a certified lattice chart and each
//! transient on `2^(−L_w)ℤ` with error feedback:
//! - the junction's inverse `(Y_r + Σ G_a)⁻¹` is its weights' chart ([`junction_weights`]):
//!   `ŵ_a` at the nearest point of `2^(−L_c)ℤ` to `G_a/(Y_r + Σ G)`, and `ŵ_s = 1 − Σ ŵ_a`, so the
//!   weights sum to one exactly and the executed Swing is an exact involution about the executed
//!   anchor; its certificate is `‖ŵ − w‖₁`;
//! - the element's and the contact's solves are the charts of `(I − ½K_r)⁻¹` and `m_a⁻¹`
//!   ([`crate::hnn::chart::refine`]), each certified `‖1 − A X̂‖∞ ≤ δ`;
//! - the word carries the anchor `v_r`, the storage `s_r′`, the contact's solved `ζ_a` and every
//!   state (`a`, `u`, `w`) on the transients' lattice ([`crate::hnn::word`]).
//!
//! The tick's power balance then holds up to its residual, which [`TickBalance`] reports with a
//! bound read from the certificates and the transients' cells ([`TickBalance::closes`]):
//!
//! ```text
//! residual = Σ_r h W_r ⟨v_r, v_r − v_r*⟩                      the executed anchor against the participation mean
//!          + Σ_r (h/2) Y_r ⟨x̄_r, e_r⟩,  e_r = −R_r(2b_r + W_c c_r)      the element's chart
//!          + Σ_r (h/4) Y_r (|s_r′|² − |ŝ_r′|²)                  the storage's split
//!          + Σ_a ⟨ω_a, m_a ζ_a − right_a⟩                       the contact's chart and split
//!          + Σ_a [E_a(u′, w′) − E_a(û′, ŵ′) + (hG_a/4)(|a′|² − |â′|²)]   the contact's states' split
//! ```
//!
//! each term an exact identity of the executed tick (the hat marks an image before its split), and
//! zero for the exact law. The element's term is Lean `HNN/LatticeWord.cayley_chart_energy` read on
//! the full element (its skew part is the Cayley element's; the passive part and the contrast port
//! enter through `W_s` and `W_c`, the full element's balance at an executed chart being owed in #62).
//!
//! [definition; agent-inferred] **The tick realizes the midpoint scheme directly** (design (a),
//! "Reception is composed", item 1). The element step is exactly `ReferenceHolon`'s
//! implicit-midpoint advance (`holon::law`, `Holon/Law.advance_law`) of the medium
//! `ẋ = (Ω − R)x + W_c c` with `Q = I`, `h = 1`, `Ω = Σ σ_ρ A_ρ`, `R = −W_s`; the transit is exactly
//! its advance on `(u, p = C_a w)` with storage `(K_a, C_a⁻¹)`, resistance `D_a + (2/G_a)I` and the
//! channel waves as sources, whenever `C_a ≻ 0`. Two tests equate them at the same operands under
//! the exact law (`tests/propagation.rs`, `the_element_step_is_the_reference_holons_midpoint_advance`,
//! `a_stored_transit_is_the_reference_holons_midpoint_advance`). The tick does not call the owner:
//! (i) `C_a = c_a c_aᵀ` may be singular (campaign 1 admits `c_a = 0`, pure transmission), where the
//! transit is a descriptor midpoint step with mass `C_a` that the owner's unit-mass step
//! `q⁺ − q = h((J − R)Q q̄ + B u)` does not state; (ii) a word's operands are fixed at its cut, so
//! each solve is charted once and applied every tick, and the return reads the executed charts'
//! transposes, while the owner solves its whole Dirac system (`3σ + μ` unknowns) at every step.
//!
//! [definition; agent-inferred] **The exponent's carry and phase.** `s_a = n_a + φ_a/L` is read by
//! floor into its carry `n_a` (an exact shift `2^(n_a)`) and its phase class `φ_a ∈ ℤ/L`
//! ([`ExponentReading`]); nothing is rounded. Campaign 1 declares `L = 1`, so `φ_a = 0` and
//! `κ_a = 2^(n_a)` is rational; a nonzero phase class would carry the current in `ℚ(θ)`,
//! `θ^L = 2`, which campaign 1 does not, so it is refused with its class (the `CarriedPower`
//! owner, addition 4, is the ratio module's).
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Propagation.anchor_is_participation`, `junctionSwing_involutive`, `junctionSwing_isometry`; `Geometry/AffineSwing.swing` | [`junction_swing`], [`participation`], [`swing_about`] |
//! | `HNN/Word.reaction_stage_isometry`, `reaction_stage_balance`, `contrastPort_active`; `Holon/Cayley.drive_balance`; `HNN/LatticeWord.cayley_chart_energy` | [`element_step`] |
//! | `HNN/Propagation.partialIsometry_transit`, `transit_balance`, `tick_well_defined` | [`transit`], [`transit_solve`], [`transit_update`], [`ContactOperands`] |
//! | `HNN/Word.word_tick_balance`; `HNN/LatticeWord.{chart_energy_identity, feedback_tick}` | [`global_power`], [`TickBalance`] |
//! | `Holon/Law.advance_law` (the midpoint scheme the element and a stored transit realize) | [`element_step`], [`transit`] (equated with `holon::law::ReferenceHolon` in the tests) |
//!
//! [definition; agent-inferred] **The path attenuation** ([`path_attenuation`], review C2) reads, at
//! a cut, the least `Σ_a β_a Q_a / 2` over the source-to-receiver walks within the receiver's last
//! epoch, and calls the path open when `2^(−x)` is at least the receiver's grain `1/L_R`. The refine
//! receipt reports it, so a shielded receiver is a located cause, not a silent uniform face.

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::geometry::swing::swing;
use crate::hnn::HnnError;
use crate::hnn::chart::{ChartKey, ChartReading, ChartWords, Charts, WordLattice, refine};
use crate::hnn::constitution::Lattice;
use crate::hnn::field::{ConstitutionRead, Current, End, Field};
use crate::hnn::realization::{entries, indexed};
use crate::ratio::exponentiated::power_of_two;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, integer_dot, integral, lcm, scale, sub};
use crate::ratio::{Rat, integer, rat};

// -------------------------------------------------------------------------------------------
// the exponent

/// [definition] **A contact's exponent at the cut**: its pair quadrance `Q_a`, `s_a = −β_a Q_a / 2`,
/// and that exponent's carry `n_a = ⌊s_a⌋` and phase class `φ_a = L(s_a − n_a) ∈ ℤ/L`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExponentReading {
    pub quadrance: Rat,
    pub exponent: Rat,
    pub carry: BigInt,
    pub phase: u64,
}

/// The exponent of one contact at a lift point, read from the two rings' screws.
pub fn contact_exponent(
    field: &Field,
    contact: usize,
    lift: &[BigInt],
) -> Result<ExponentReading, HnnError> {
    let declared = field.contact(contact);
    let quadrance = declared.pair(field, lift).quadrance().clone();
    let exponent = -(declared.exponent() * &quadrance) / integer(2);
    let carry = exponent.floor().to_integer();
    let grain = BigInt::from(field.exponent_grain());
    let class = (&exponent - Rat::from_integer(carry.clone())) * Rat::from_integer(grain.clone());
    if !class.is_integer() {
        // The declared lattice makes `s_a ∈ (1/L)ℤ`; a reading off it is a declaration defect.
        return Err(HnnError::ExponentLattice {
            contact,
            exponent: Box::new(declared.exponent().clone()),
            lattice: Box::new(
                Rat::from_integer(BigInt::from(2) * field.quadrance_denominator())
                    / Rat::from_integer(grain),
            ),
        });
    }
    let phase = class
        .to_integer()
        .to_u64()
        .expect("a phase class lies in ℤ/L");
    Ok(ExponentReading {
        quadrance,
        exponent,
        carry,
        phase,
    })
}

/// [definition] **The source-to-receiver path attenuation at a lift point** (review C2): the least
/// `x = Σ_a β_a Q_a / 2 = −Σ_a s_a` over the walks of at most `hops` contacts from a source ring
/// to the receiving ring, in bits (the walk's product of participation factors is `2^(−x)`), and
/// whether the path is **open**: `2^(−x) ≥ 1/L_R`, the receiver's grain, so that a unit change at
/// the source still moves the receiver's logits by at least one grain cell. A reading of the
/// medium at the cut; it enters no law.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathAttenuation {
    pub exponent: Rat,
    pub open: bool,
}

/// **The least path attenuation** from the source rings to `ring` within `hops` contacts, read at
/// the lift point against the receiver's grain `L_R` (open when `2^x ≤ L_R`, compared exactly as
/// `2^(p) ≤ L_R^q` for `x = p/q`). Refused when no walk of that length reaches the ring.
pub fn path_attenuation(
    field: &Field,
    lift: &[BigInt],
    ring: usize,
    hops: usize,
    grain: u64,
) -> Result<PathAttenuation, HnnError> {
    if ring >= field.rings().len() {
        return Err(HnnError::RingOutside {
            ring,
            rings: field.rings().len(),
        });
    }
    let costs = (0..field.contacts().len())
        .map(|contact| contact_exponent(field, contact, lift).map(|reading| -reading.exponent))
        .collect::<Result<Vec<Rat>, HnnError>>()?;
    let mut least: Vec<Option<Rat>> = vec![None; field.rings().len()];
    for &source in field.sources() {
        least[source] = Some(Rat::zero());
    }
    for _ in 0..hops {
        let mut next = least.clone();
        for (contact, cost) in field.contacts().iter().zip(&costs) {
            let (g, h) = contact.ends();
            for (here, there) in [(g, h), (h, g)] {
                if let Some(reached) = &least[here] {
                    let through = reached + cost;
                    if next[there].as_ref().is_none_or(|known| &through < known) {
                        next[there] = Some(through);
                    }
                }
            }
        }
        least = next;
    }
    let exponent = least[ring].clone().ok_or(HnnError::Unreached { ring })?;
    let open = if exponent.is_positive() {
        let power = BigInt::one() << exponent.numer().to_usize().ok_or(HnnError::CountOverflow)?;
        let bound = num_traits::pow(
            BigInt::from(grain),
            exponent.denom().to_usize().ok_or(HnnError::CountOverflow)?,
        );
        power <= bound
    } else {
        true
    };
    Ok(PathAttenuation { exponent, open })
}

// -------------------------------------------------------------------------------------------
// the executed solve

/// [definition] **An executed solve**: the exact inverse (the law), or a certified lattice chart
/// (Decision 24). The word applies it forward and its return applies its transpose, so the paired
/// adjoint keeps the operands the forward executed (Lean `HNN/LatticeWord.executed_adjoint_unique`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Solve {
    Exact { rows: Rows, transposed: Rows },
    Chart(ChartWords),
}

impl Solve {
    fn exact(inverse: &ExactRatMatrix) -> Result<Self, HnnError> {
        Ok(Self::Exact {
            rows: Rows::of(inverse),
            transposed: Rows::of(&inverse.transpose()?),
        })
    }

    /// `X̂ y`.
    pub(crate) fn apply(&self, vector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        match self {
            Self::Exact { rows, .. } => Ok(rows.apply(vector)),
            Self::Chart(chart) => chart.apply(vector),
        }
    }

    /// `X̂ᵀ λ`: the executed adjoint.
    pub(crate) fn apply_transpose(&self, vector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        match self {
            Self::Exact { transposed, .. } => Ok(transposed.apply(vector)),
            Self::Chart(chart) => chart.apply_transpose(vector),
        }
    }

    /// The executed map, as an exact matrix.
    pub(crate) fn matrix(&self) -> Result<ExactRatMatrix, HnnError> {
        match self {
            Self::Exact { rows, .. } => rows.matrix(),
            Self::Chart(chart) => chart.to_matrix(),
        }
    }
}

/// **The executed solve of an operator**: the chart refined from the start (lattice), or the exact
/// inverse (the law).
fn solve_of(
    operator: &ExactRatMatrix,
    lattice: Option<(&WordLattice, ChartKey, Option<&ChartWords>)>,
) -> Result<(Solve, Option<ChartReading>), HnnError> {
    match lattice {
        Some((lattice, key, start)) => {
            let (chart, reading) = refine(key, operator, start, lattice)?;
            Ok((Solve::Chart(chart), Some(reading)))
        }
        None => Ok((Solve::exact(&operator.inverse()?)?, None)),
    }
}

// -------------------------------------------------------------------------------------------
// the operands at the cut

/// [definition] **A ring's operands at the cut**: its admittance, the sheet classes of its standing
/// contrast, its element `K_r = W_s + Σ σ_ρ A_ρ`, the contrast port `W_c`, and the executed solve of
/// `I − ½K_r` (the exact inverse, or its certified chart with its reading).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingOperands {
    admittance: Rat,
    sheets: Vec<bool>,
    element: ExactRatMatrix,
    passive: ExactRatMatrix,
    contrast: ExactRatMatrix,
    solve: Solve,
    chart: Option<ChartReading>,
    element_rows: Rows,
    passive_rows: Option<Rows>,
    contrast_rows: Option<Rows>,
    contrast_transposed: Option<Rows>,
}

/// **The element material read from the constitution**: the sheet classes, `W_s = −ffᵀ` and
/// `K = W_s + Σ σ_ρ A_ρ`. Public for a realization that forms the ring's operator
/// ([`ring_operator`]) and its balance's operands off the host (`holonics-cuda::hnn::port`).
pub fn element_material(
    contrast_reading: &[Rat],
    passive_factor: &ExactRatMatrix,
    contrast_port: &ExactRatMatrix,
    slices: &[(Vec<Rat>, Vec<Rat>)],
) -> Result<(Vec<bool>, ExactRatMatrix, ExactRatMatrix), HnnError> {
    let n = contrast_reading.len();
    if slices.len() != n || slices.iter().any(|(u, v)| u.len() != n || v.len() != n) {
        return Err(HnnError::Shape {
            what: "skew slices (one per realified coordinate)",
            expected: n,
            found: slices.len(),
        });
    }
    if passive_factor.rows() != n || contrast_port.rows() != n || contrast_port.columns() != n {
        return Err(HnnError::Shape {
            what: "ring element material",
            expected: n,
            found: passive_factor.rows(),
        });
    }
    let sheets: Vec<bool> = contrast_reading.iter().map(|x| !x.is_negative()).collect();
    let passive = gram(passive_factor)?.scaled(&-Rat::one());
    // Σ_ρ σ_ρ (u_ρ v_ρᵀ − v_ρ u_ρᵀ), accumulated as integers over one common denominator.
    let charted: Vec<(Vec<BigInt>, BigInt, Vec<BigInt>, BigInt)> = slices
        .iter()
        .map(|(u, v)| {
            let (u, du) = integral(u);
            let (v, dv) = integral(v);
            (u, du, v, dv)
        })
        .collect();
    let denominator = charted
        .iter()
        .fold(BigInt::one(), |d, (_, du, _, dv)| lcm(&d, &(du * dv)));
    let mut skew = vec![vec![BigInt::zero(); n]; n];
    for ((u, du, v, dv), sheet) in charted.iter().zip(&sheets) {
        let mut weight = &denominator / (du * dv);
        if !*sheet {
            weight = -weight;
        }
        for i in 0..n {
            if u[i].is_zero() && v[i].is_zero() {
                continue;
            }
            for j in 0..n {
                let term = &u[i] * &v[j] - &v[i] * &u[j];
                if !term.is_zero() {
                    skew[i][j] += &weight * term;
                }
            }
        }
    }
    let element = ExactRatMatrix::shaped(
        n,
        n,
        (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| {
                        passive.get(i, j).expect("in range")
                            + Rat::new(skew[i][j].clone(), denominator.clone())
                    })
                    .collect()
            })
            .collect(),
    )?;
    Ok((sheets, passive, element))
}

/// **The ring element's operator** `I − ½K_r`, whose inverse (exact, or its certified chart) is the
/// element's solve. Public for a realization that charts it off the host.
pub fn ring_operator(element: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
    Ok(ExactRatMatrix::identity(element.rows())?.subtract(&element.scaled(&rat(1, 2)))?)
}

/// **The contact's normalized operator** `m_a = 1 + (G_a/2h)(2C_a + hD_a + (h²/2)K_a)` from its
/// squared forms, conductance and hop (`M_a = (2h/G_a) m_a`), whose inverse is the transit's solve.
/// Public for a realization that charts it off the host.
pub fn contact_operator(
    storage: &ExactRatMatrix,
    stiffness: &ExactRatMatrix,
    dissipation: &ExactRatMatrix,
    conductance: &Rat,
    step: &Rat,
) -> Result<ExactRatMatrix, HnnError> {
    let h = step;
    // m = 1 + (G/2h)(2C + hD + (h²/2)K) = (G/2h) M.
    let gain = conductance / (integer(2) * h);
    Ok(ExactRatMatrix::identity(storage.rows())?.add(
        &storage
            .scaled(&integer(2))
            .add(&dissipation.scaled(h))?
            .add(&stiffness.scaled(&(h * h / integer(2))))?
            .scaled(&gain),
    )?)
}

impl RingOperands {
    /// **A ring's operands under the exact law**, from its declared admittance and its element
    /// material, at the sheet classes of the standing contrast `Δ_r` (`σ_ρ = sign Δ_r[ρ]`,
    /// `sign 0 = +1`, the half-open sheet): the solve is the exact `(I − ½K_r)⁻¹`.
    pub fn new(
        admittance: Rat,
        contrast_reading: &[Rat],
        passive_factor: &ExactRatMatrix,
        contrast_port: &ExactRatMatrix,
        slices: &[(Vec<Rat>, Vec<Rat>)],
    ) -> Result<Self, HnnError> {
        Self::build(
            admittance,
            contrast_reading,
            passive_factor,
            contrast_port,
            slices,
            None,
        )
    }

    /// **A ring's operands on the word's lattices**: the solve is the chart of `(I − ½K_r)⁻¹`
    /// refined from `start` ([`crate::hnn::chart::refine`]), with its reading.
    #[allow(clippy::too_many_arguments)]
    pub fn charted(
        admittance: Rat,
        contrast_reading: &[Rat],
        passive_factor: &ExactRatMatrix,
        contrast_port: &ExactRatMatrix,
        slices: &[(Vec<Rat>, Vec<Rat>)],
        key: ChartKey,
        lattice: &WordLattice,
        start: Option<&ChartWords>,
    ) -> Result<Self, HnnError> {
        Self::build(
            admittance,
            contrast_reading,
            passive_factor,
            contrast_port,
            slices,
            Some((lattice, key, start)),
        )
    }

    fn build(
        admittance: Rat,
        contrast_reading: &[Rat],
        passive_factor: &ExactRatMatrix,
        contrast_port: &ExactRatMatrix,
        slices: &[(Vec<Rat>, Vec<Rat>)],
        lattice: Option<(&WordLattice, ChartKey, Option<&ChartWords>)>,
    ) -> Result<Self, HnnError> {
        let (sheets, passive, element) =
            element_material(contrast_reading, passive_factor, contrast_port, slices)?;
        let left = ring_operator(&element)?;
        let (solve, chart) = solve_of(&left, lattice)?;
        let contrast = !is_zero_matrix(contrast_port);
        Ok(Self {
            admittance,
            sheets,
            solve,
            chart,
            element_rows: Rows::of(&element),
            passive_rows: (!is_zero_matrix(&passive)).then(|| Rows::of(&passive)),
            contrast_rows: contrast.then(|| Rows::of(contrast_port)),
            contrast_transposed: contrast
                .then(|| contrast_port.transpose().map(|t| Rows::of(&t)))
                .transpose()?,
            element,
            passive,
            contrast: contrast_port.clone(),
        })
    }

    pub fn admittance(&self) -> &Rat {
        &self.admittance
    }

    /// The sheet classes `σ_ρ` (`true` for `+1`).
    pub fn sheets(&self) -> &[bool] {
        &self.sheets
    }

    /// `K_r`.
    pub fn element(&self) -> &ExactRatMatrix {
        &self.element
    }

    /// `W_s,r = −f fᵀ`.
    pub fn passive(&self) -> &ExactRatMatrix {
        &self.passive
    }

    /// `W_c,r`.
    pub fn contrast(&self) -> &ExactRatMatrix {
        &self.contrast
    }

    pub fn width(&self) -> usize {
        self.element.rows()
    }

    /// The executed solve of `I − ½K_r`, as an exact matrix (the exact inverse, or the chart).
    pub fn solve(&self) -> Result<ExactRatMatrix, HnnError> {
        self.solve.matrix()
    }

    /// The chart's reading (certificate, steps, seed); `None` under the exact law.
    pub fn chart(&self) -> Option<&ChartReading> {
        self.chart.as_ref()
    }

    /// The executed solve's chart, when the word is on its lattices.
    pub(crate) fn chart_words(&self) -> Option<&ChartWords> {
        match &self.solve {
            Solve::Chart(chart) => Some(chart),
            Solve::Exact { .. } => None,
        }
    }

    /// `X̂ᵀ s̄`: the element's executed adjoint.
    pub(crate) fn solve_transpose(&self, covector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        self.solve.apply_transpose(covector)
    }

    /// `W_cᵀ u`, or zero for an absent port.
    pub(crate) fn contrast_transpose(&self, covector: &[Rat]) -> Vec<Rat> {
        match &self.contrast_transposed {
            Some(rows) => rows.apply(covector),
            None => vec![Rat::zero(); covector.len()],
        }
    }
}

/// [definition] **A contact's operands at the cut**: its ends and channel selections, its exponent
/// reading and conductance `G_a = 2^(n_a) Y_a`, its squared forms `C_a`, `K_a`, `D_a`, its normalized
/// operator `m_a = 1 + (G_a/2h)(2C_a + hD_a + (h²/2)K_a)` and that operator's executed solve (the
/// exact inverse, or its certified chart with its reading).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactOperands {
    ends: (usize, usize),
    selection: (Vec<usize>, Vec<usize>),
    exponent: ExponentReading,
    conductance: Rat,
    storage: ExactRatMatrix,
    stiffness: ExactRatMatrix,
    dissipation: ExactRatMatrix,
    storage_rows: Option<Rows>,
    stiffness_rows: Option<Rows>,
    dissipation_rows: Option<Rows>,
    operator: ExactRatMatrix,
    operator_rows: Rows,
    operator_norm: Rat,
    solve: Solve,
    chart: Option<ChartReading>,
}

impl ContactOperands {
    /// **A contact's operands under the exact law**, from its geometry reading, its conductance,
    /// the hop `h` and its three square factors (`C = c cᵀ`, `K = b bᵀ`, `D = F Fᵀ`, each `k_a × m`).
    /// `m_a ⪰ 1` for `G_a > 0`, so its inverse exists (`tick_well_defined`).
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        ends: (usize, usize),
        selection: (Vec<usize>, Vec<usize>),
        exponent: ExponentReading,
        conductance: Rat,
        step: &Rat,
        storage_factor: &ExactRatMatrix,
        stiffness_factor: &ExactRatMatrix,
        dissipation_factor: &ExactRatMatrix,
    ) -> Result<Self, HnnError> {
        Self::build(
            ends,
            selection,
            exponent,
            conductance,
            step,
            [storage_factor, stiffness_factor, dissipation_factor],
            None,
        )
    }

    /// **A contact's operands on the word's lattices**: the solve is the chart of `m_a⁻¹` refined
    /// from `start`, with its reading.
    #[allow(clippy::too_many_arguments)]
    pub fn charted(
        ends: (usize, usize),
        selection: (Vec<usize>, Vec<usize>),
        exponent: ExponentReading,
        conductance: Rat,
        step: &Rat,
        factors: [&ExactRatMatrix; 3],
        key: ChartKey,
        lattice: &WordLattice,
        start: Option<&ChartWords>,
    ) -> Result<Self, HnnError> {
        Self::build(
            ends,
            selection,
            exponent,
            conductance,
            step,
            factors,
            Some((lattice, key, start)),
        )
    }

    fn build(
        ends: (usize, usize),
        selection: (Vec<usize>, Vec<usize>),
        exponent: ExponentReading,
        conductance: Rat,
        step: &Rat,
        [storage_factor, stiffness_factor, dissipation_factor]: [&ExactRatMatrix; 3],
        lattice: Option<(&WordLattice, ChartKey, Option<&ChartWords>)>,
    ) -> Result<Self, HnnError> {
        let k = selection.0.len();
        let square = |factor: &ExactRatMatrix| -> Result<ExactRatMatrix, HnnError> {
            if factor.rows() != k {
                return Err(HnnError::Shape {
                    what: "contact factor rows (the channel width)",
                    expected: k,
                    found: factor.rows(),
                });
            }
            gram(factor)
        };
        let storage = square(storage_factor)?;
        let stiffness = square(stiffness_factor)?;
        let dissipation = square(dissipation_factor)?;
        if !conductance.is_positive() || !step.is_positive() {
            return Err(HnnError::NonpositiveDeclaration);
        }
        let operator = contact_operator(&storage, &stiffness, &dissipation, &conductance, step)?;
        let operator_norm = (0..k)
            .map(|i| {
                operator
                    .row(i)
                    .expect("in range")
                    .iter()
                    .map(|x| x.abs())
                    .sum::<Rat>()
            })
            .max()
            .unwrap_or_else(Rat::zero);
        let (solve, chart) = solve_of(&operator, lattice)?;
        let rows = |form: &ExactRatMatrix| (!is_zero_matrix(form)).then(|| Rows::of(form));
        Ok(Self {
            ends,
            selection,
            exponent,
            conductance,
            storage_rows: rows(&storage),
            stiffness_rows: rows(&stiffness),
            dissipation_rows: rows(&dissipation),
            storage,
            stiffness,
            dissipation,
            operator_rows: Rows::of(&operator),
            operator,
            operator_norm,
            solve,
            chart,
        })
    }

    pub fn ends(&self) -> (usize, usize) {
        self.ends
    }

    /// `G_a`, the port conductance at both ends.
    pub fn conductance(&self) -> &Rat {
        &self.conductance
    }

    pub fn exponent(&self) -> &ExponentReading {
        &self.exponent
    }

    /// `C_a`, `K_a`, `D_a`.
    pub fn forms(&self) -> (&ExactRatMatrix, &ExactRatMatrix, &ExactRatMatrix) {
        (&self.storage, &self.stiffness, &self.dissipation)
    }

    /// `m_a = 1 + (G_a/2h)(2C_a + hD_a + (h²/2)K_a)`.
    pub fn operator(&self) -> &ExactRatMatrix {
        &self.operator
    }

    /// The executed solve of `m_a`, as an exact matrix (the exact inverse, or the chart).
    pub fn solve(&self) -> Result<ExactRatMatrix, HnnError> {
        self.solve.matrix()
    }

    /// The chart's reading; `None` under the exact law.
    pub fn chart(&self) -> Option<&ChartReading> {
        self.chart.as_ref()
    }

    /// The executed solve's chart, when the word is on its lattices.
    pub(crate) fn chart_words(&self) -> Option<&ChartWords> {
        match &self.solve {
            Solve::Chart(chart) => Some(chart),
            Solve::Exact { .. } => None,
        }
    }

    /// `m̂ᵀ ζ̄`: the transit's executed adjoint.
    pub(crate) fn solve_transpose(&self, covector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        self.solve.apply_transpose(covector)
    }

    pub fn width(&self) -> usize {
        self.selection.0.len()
    }

    /// The channel's selections at the two ends.
    pub(crate) fn selection(&self) -> (&[usize], &[usize]) {
        (&self.selection.0, &self.selection.1)
    }

    /// `E_a = ½ w*C w + ½ u*K u`.
    pub fn energy(&self, displacement: &[Rat], rate: &[Rat]) -> Result<Rat, HnnError> {
        Ok(
            (quadratic(&self.storage_rows, rate) + quadratic(&self.stiffness_rows, displacement))
                / integer(2),
        )
    }

    /// `C w` and `K u` (zero for an absent form).
    fn forms_applied(&self, displacement: &[Rat], rate: &[Rat]) -> (Vec<Rat>, Vec<Rat>) {
        let apply = |form: &Option<Rows>, vector: &[Rat]| match form {
            Some(rows) => rows.apply(vector),
            None => vec![Rat::zero(); vector.len()],
        };
        (
            apply(&self.storage_rows, rate),
            apply(&self.stiffness_rows, displacement),
        )
    }
}

/// [definition] **Every operand of a word, fixed at the cut**, with the junctions' executed weights
/// (and their exact ones, which the balance's residual reads), the word's declared precisions
/// (`None` under the exact law) and every chart's reading.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operands {
    step: Rat,
    rings: Vec<RingOperands>,
    contacts: Vec<ContactOperands>,
    incident: Vec<Vec<usize>>,
    weights: Vec<Vec<Rat>>,
    exact_weights: Vec<Vec<Rat>>,
    junction_certificates: Vec<Rat>,
    lattice: Option<WordLattice>,
}

/// **One ring's operands from the constitution**: its admittance and element material at the sheet
/// classes of its standing contrast `Δ_r = Σ_(a∋r) U_(r←a) q_(other end) − q_r`
/// ([`Field::standing_contrast`], read from the connection incidence's blocks), under the exact law.
/// They read no lift point; the contacts' conductances do.
pub fn ring_operands(
    field: &Field,
    constitution: &impl ConstitutionRead,
    index: usize,
) -> Result<RingOperands, HnnError> {
    ring_operands_on(field, constitution, index, None)
}

fn ring_operands_on(
    field: &Field,
    constitution: &impl ConstitutionRead,
    index: usize,
    lattice: Option<(&WordLattice, Option<&ChartWords>)>,
) -> Result<RingOperands, HnnError> {
    let ring = field.rings().get(index).ok_or(HnnError::RingOutside {
        ring: index,
        rings: field.rings().len(),
    })?;
    let contrast = field.standing_contrast(constitution, index)?;
    RingOperands::build(
        ring.admittance().clone(),
        &contrast,
        constitution.passive_factor(index),
        constitution.contrast_port(index),
        constitution.slices(index),
        lattice.map(|(lattice, start)| (lattice, ChartKey::Ring(index), start)),
    )
}

/// **The junction's weights**: the exact participation weights `w_p = W_p/(Y_r + Σ G_a)` (storage
/// port first, then the incident contacts in order) and, on the word's lattices, their chart:
/// `ŵ_a` at the nearest point of `2^(−L_c)ℤ` to `w_a`, ties upward, and `ŵ_s = 1 − Σ ŵ_a`, so the
/// executed weights sum to one exactly. Returns the executed weights, the exact ones and the
/// chart's certificate `‖ŵ − w‖₁` (zero under the exact law).
pub fn junction_weights(
    admittance: &Rat,
    conductances: &[&Rat],
    lattice: Option<&Lattice>,
) -> Result<(Vec<Rat>, Vec<Rat>, Rat), HnnError> {
    let total = conductances
        .iter()
        .fold(admittance.clone(), |sum, g| sum + *g);
    if !total.is_positive() {
        return Err(HnnError::NonpositiveDeclaration);
    }
    let exact: Vec<Rat> = std::iter::once(admittance)
        .chain(conductances.iter().copied())
        .map(|w| w / &total)
        .collect();
    let Some(lattice) = lattice else {
        return Ok((exact.clone(), exact, Rat::zero()));
    };
    let unit = lattice.unit();
    let contacts: Vec<Rat> = exact[1..]
        .iter()
        .map(|w| Rat::from_integer(lattice.div_rem(w).0) * &unit)
        .collect();
    let own = Rat::one() - contacts.iter().sum::<Rat>();
    let executed: Vec<Rat> = std::iter::once(own).chain(contacts).collect();
    let certificate = executed
        .iter()
        .zip(&exact)
        .map(|(a, b)| (a - b).abs())
        .sum();
    Ok((executed, exact, certificate))
}

impl Operands {
    /// **The operands at the cut** `(Θ, λ)` on the field's declared word: each contact's exponent
    /// from the pair quadrance of its rings' screws at `λ`, each ring's sheet classes from the
    /// standing contrast `Δ_r = Σ_(a∋r) U_(r←a) q_(other end) − q_r`, the constitution's factors,
    /// and every solve seeded afresh ([`crate::hnn::chart::refine`] from no start); under the exact
    /// law, every solve exact.
    pub fn at_cut(
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
    ) -> Result<Self, HnnError> {
        Self::at_cut_charted(field, constitution, current, &mut Charts::new())
    }

    /// **The operands at the cut, warm-started from a resident's charts**: each solve refines the
    /// chart its key last left, and the refined charts replace them.
    pub fn at_cut_charted(
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        charts: &mut Charts,
    ) -> Result<Self, HnnError> {
        let operands = Self::build(
            field,
            constitution,
            current,
            field.word_lattice().copied(),
            charts,
        )?;
        for ring in &operands.rings {
            if let (Some(reading), Some(chart)) = (&ring.chart, ring.chart_words()) {
                charts.insert(reading.key.clone(), chart.clone());
            }
        }
        for contact in &operands.contacts {
            if let (Some(reading), Some(chart)) = (&contact.chart, contact.chart_words()) {
                charts.insert(reading.key.clone(), chart.clone());
            }
        }
        Ok(operands)
    }

    /// **The operands at the cut under the exact law**: every solve the exact inverse and every
    /// junction weight exact (the observability rank's map, and the law the certificates are read
    /// against).
    pub fn exact_at_cut(
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
    ) -> Result<Self, HnnError> {
        Self::build(field, constitution, current, None, &Charts::new())
    }

    fn build(
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        lattice: Option<WordLattice>,
        charts: &Charts,
    ) -> Result<Self, HnnError> {
        // Each ring's operands read only its own material, the standings and its own chart; each
        // contact's only its own factors, its two rings' screws and its own chart: the rings, then
        // the contacts, run together.
        let rings = indexed(field.rings().len(), |index| {
            ring_operands_on(
                field,
                constitution,
                index,
                lattice
                    .as_ref()
                    .map(|lattice| (lattice, charts.get(&ChartKey::Ring(index)))),
            )
        })?;
        let contacts = indexed(field.contacts().len(), |index| {
            let contact = field.contact(index);
            let exponent = contact_exponent(field, index, current.lift())?;
            if exponent.phase != 0 {
                return Err(HnnError::ExponentPhase {
                    contact: index,
                    phase: exponent.phase,
                    grain: field.exponent_grain(),
                });
            }
            let conductance = power_of_two(&exponent.carry)? * contact.admittance();
            let key = ChartKey::Contact {
                contact: index,
                carry: exponent.carry.clone(),
            };
            let start = charts.get(&key);
            ContactOperands::build(
                contact.ends(),
                (contact.selection(End::From), contact.selection(End::To)),
                exponent,
                conductance,
                field.step(),
                [
                    constitution.contact_storage(index),
                    constitution.contact_stiffness(index),
                    constitution.contact_dissipation(index),
                ],
                lattice.as_ref().map(|lattice| (lattice, key, start)),
            )
        })?;
        let incident: Vec<Vec<usize>> = (0..field.rings().len())
            .map(|ring| field.incident(ring).to_vec())
            .collect();
        let chart_lattice = lattice.as_ref().map(WordLattice::chart);
        let mut weights = Vec::with_capacity(rings.len());
        let mut exact_weights = Vec::with_capacity(rings.len());
        let mut junction_certificates = Vec::with_capacity(rings.len());
        for (ring, operands) in rings.iter().enumerate() {
            let conductances: Vec<&Rat> = incident[ring]
                .iter()
                .map(|&a| contacts[a].conductance())
                .collect();
            let (executed, exact, certificate) =
                junction_weights(operands.admittance(), &conductances, chart_lattice.as_ref())?;
            weights.push(executed);
            exact_weights.push(exact);
            junction_certificates.push(certificate);
        }
        Ok(Self {
            step: field.step().clone(),
            rings,
            contacts,
            incident,
            weights,
            exact_weights,
            junction_certificates,
            lattice,
        })
    }

    /// `h`.
    pub fn step(&self) -> &Rat {
        &self.step
    }

    pub fn rings(&self) -> &[RingOperands] {
        &self.rings
    }

    pub fn contacts(&self) -> &[ContactOperands] {
        &self.contacts
    }

    /// The contacts meeting a ring.
    pub fn incident(&self, ring: usize) -> &[usize] {
        &self.incident[ring]
    }

    /// The wave slot of contact `a` at ring `r`: `0` at its `from` end, `1` at its `to` end.
    pub fn end_slot(&self, contact: usize, ring: usize) -> usize {
        usize::from(self.contacts[contact].ends.0 != ring)
    }

    /// Ring `r`'s executed junction weights: its storage port's, then its incident contacts' in
    /// order.
    pub fn weights(&self, ring: usize) -> &[Rat] {
        &self.weights[ring]
    }

    /// Ring `r`'s exact participation weights.
    pub fn exact_weights(&self, ring: usize) -> &[Rat] {
        &self.exact_weights[ring]
    }

    /// The certificate `‖ŵ − w‖₁` of ring `r`'s junction weights.
    pub fn junction_certificate(&self, ring: usize) -> &Rat {
        &self.junction_certificates[ring]
    }

    /// The word's declared precisions; `None` under the exact law.
    pub fn lattice(&self) -> Option<&WordLattice> {
        self.lattice.as_ref()
    }

    /// **The executed charts with no transient split**: every solve the executed chart's exact
    /// values and every junction weight the executed one, the word unsplit. The executed word's
    /// linear map, on which its return pairs exactly (Lean `HNN/LatticeWord.executed_adjoint_unique`,
    /// the law's own tests).
    #[cfg(test)]
    pub(crate) fn unsplit(mut self) -> Result<Self, HnnError> {
        let exact = |solve: &Solve| -> Result<Solve, HnnError> { Solve::exact(&solve.matrix()?) };
        for ring in &mut self.rings {
            ring.solve = exact(&ring.solve)?;
        }
        for contact in &mut self.contacts {
            contact.solve = exact(&contact.solve)?;
        }
        self.lattice = None;
        Ok(self)
    }

    /// Every chart's reading, the rings' then the contacts'.
    pub fn charts(&self) -> Vec<ChartReading> {
        self.rings
            .iter()
            .filter_map(|ring| ring.chart.clone())
            .chain(
                self.contacts
                    .iter()
                    .filter_map(|contact| contact.chart.clone()),
            )
            .collect()
    }
}

// -------------------------------------------------------------------------------------------
// the junction Swing

/// [definition] **What the junction Swing returns**: the anchor `v_r` (the `G`-weighted mean of
/// the arrivals, the ring's own storage port included), the storage wave `b = 2v − s`, the
/// contrast `c = v − s`, and one outgoing wave `o = 2v − a` per arrival.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Junction {
    pub anchor: Vec<Rat>,
    pub storage_wave: Vec<Rat>,
    pub contrast: Vec<Rat>,
    pub outgoing: Vec<Vec<Rat>>,
}

/// **The participation anchor** `v = ŵ_s s + Σ_a ŵ_a a_a` at declared weights (the storage port's
/// first).
pub fn participation(
    weights: &[Rat],
    storage: &[Rat],
    arrivals: &[&[Rat]],
) -> Result<Vec<Rat>, HnnError> {
    let width = storage.len();
    if weights.len() != arrivals.len() + 1 {
        return Err(HnnError::Shape {
            what: "junction weights (the storage port and each arrival)",
            expected: arrivals.len() + 1,
            found: weights.len(),
        });
    }
    let mut anchor = scale(&weights[0], storage);
    for (weight, wave) in weights[1..].iter().zip(arrivals) {
        if wave.len() != width {
            return Err(HnnError::Shape {
                what: "arriving wave",
                expected: width,
                found: wave.len(),
            });
        }
        anchor = add(&anchor, &scale(weight, wave));
    }
    Ok(anchor)
}

/// **The junction Swing about an anchor**: each wave leaves as the owner's point Swing about it
/// ([`crate::geometry::swing::swing`] on `ℚ^(2d_r)`, Lean `Geometry/AffineSwing.swing`).
pub fn swing_about(anchor: Vec<Rat>, storage: &[Rat], arrivals: &[&[Rat]]) -> Junction {
    Junction {
        storage_wave: swing(&anchor, &storage.to_vec()),
        contrast: sub(&anchor, storage),
        outgoing: arrivals
            .iter()
            .map(|wave| swing(&anchor, &wave.to_vec()))
            .collect(),
        anchor,
    }
}

/// **The junction Swing** about the participation anchor (Lean
/// `HNN/Propagation.{anchor_is_participation, junctionSwing_involutive, junctionSwing_isometry}`):
/// the reflection `2P_D − I` onto the common-potential subspace, `W = diag(Y_r, G_a)`, under the
/// exact law. It divides by its own positive admittance sum only.
pub fn junction_swing(
    admittance: &Rat,
    storage: &[Rat],
    arrivals: &[(&Rat, &[Rat])],
) -> Result<Junction, HnnError> {
    let conductances: Vec<&Rat> = arrivals.iter().map(|(g, _)| *g).collect();
    let (weights, _, _) = junction_weights(admittance, &conductances, None)?;
    let waves: Vec<&[Rat]> = arrivals.iter().map(|(_, wave)| *wave).collect();
    let anchor = participation(&weights, storage, &waves)?;
    Ok(swing_about(anchor, storage, &waves))
}

// -------------------------------------------------------------------------------------------
// the ring element

/// [definition] **One element step**: the next storage's image `s′ = X̂(2b + W_c c) − b` (before the
/// word splits it), the midpoint `x̄ = ½(b + s′)`, the two unscaled balance terms `⟨x̄, W_s x̄⟩ ≤ 0`
/// and `⟨x̄, W_c c⟩` (no sign), and on a chart the unscaled chart term `⟨x̄, e⟩` of the equation
/// residual `e = (I − ½K)s′ − (I + ½K)b − W_c c = −R(2b + W_c c)` with its certified bound
/// `‖x̄‖₁ δ ‖2b + W_c c‖∞` (both zero under the exact law).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElementStep {
    pub next: Vec<Rat>,
    pub midpoint: Vec<Rat>,
    pub resist: Rat,
    pub drive: Rat,
    pub defect: Rat,
    pub bound: Rat,
}

fn l1(vector: &[Rat]) -> Rat {
    vector.iter().map(|x| x.abs()).sum()
}

fn sup(vector: &[Rat]) -> Rat {
    vector
        .iter()
        .map(|x| x.abs())
        .max()
        .unwrap_or_else(Rat::zero)
}

/// **The ring element's Cayley step with the contrast port inside the midpoint**:
/// `(I − ½K)s′ = (I + ½K)b + W_c c`, solved as `s′ = (I − ½K)⁻¹(2b + W_c c) − b` through the
/// executed solve, so `½|s′|² − ½|b|² = ⟨x̄, W_s x̄⟩ + ⟨x̄, W_c c⟩ + ⟨x̄, e⟩` exactly (Lean
/// `HNN/Word.reaction_stage_balance` over `Holon/Cayley.drive_balance`, with `e = 0` for the exact
/// law); with `W_s = W_c = 0` the exact law is an isometry (`reaction_stage_isometry`) and a chart
/// moves the energy by at most its certificate's bound (`HNN/LatticeWord.cayley_chart_energy`).
pub fn element_step(
    ring: &RingOperands,
    wave: &[Rat],
    contrast: &[Rat],
) -> Result<ElementStep, HnnError> {
    if wave.len() != ring.width() || contrast.len() != ring.width() {
        return Err(HnnError::Shape {
            what: "element waves",
            expected: ring.width(),
            found: wave.len().min(contrast.len()),
        });
    }
    let driven = ring.contrast_rows.as_ref().map(|port| port.apply(contrast));
    let operand = match &driven {
        Some(drive) => add(&scale(&integer(2), wave), drive),
        None => scale(&integer(2), wave),
    };
    let next = sub(&ring.solve.apply(&operand)?, wave);
    let midpoint = scale(&rat(1, 2), &add(wave, &next));
    let resist = quadratic(&ring.passive_rows, &midpoint);
    let drive = match &driven {
        Some(drive) => dot(&midpoint, drive),
        None => Rat::zero(),
    };
    let (defect, bound) = match &ring.chart {
        Some(chart) => {
            // e = s′ − b − K x̄ − W_c c.
            let mut residual = sub(&sub(&next, wave), &ring.element_rows.apply(&midpoint));
            if let Some(drive) = &driven {
                residual = sub(&residual, drive);
            }
            (
                dot(&midpoint, &residual),
                l1(&midpoint) * &chart.certificate * sup(&operand),
            )
        }
        None => (Rat::zero(), Rat::zero()),
    };
    Ok(ElementStep {
        next,
        midpoint,
        resist,
        drive,
        defect,
        bound,
    })
}

// -------------------------------------------------------------------------------------------
// the contact transit

/// [definition] **One transit**: the waves arriving back at the two ends, the next contact state
/// (each an image before the word splits it), the midpoint rate `ω = (G/2h)ζ`, the dissipation
/// `h ω*D ω`, and the channel waves in and out.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transit {
    pub arrive_from: Vec<Rat>,
    pub arrive_to: Vec<Rat>,
    pub displacement: Vec<Rat>,
    pub rate: Vec<Rat>,
    pub midpoint: Vec<Rat>,
    pub dissipation: Rat,
    pub channel_in: (Vec<Rat>, Vec<Rat>),
    pub channel_out: (Vec<Rat>, Vec<Rat>),
}

/// The channel's waves `α_g = ι_gᵀ o_(g→a)`, `α_h = ι_hᵀ o_(h→a)`.
fn channel_waves(
    contact: &ContactOperands,
    outgoing_from: &[Rat],
    outgoing_to: &[Rat],
) -> (Vec<Rat>, Vec<Rat>) {
    let (select_from, select_to) = &contact.selection;
    (
        select_from
            .iter()
            .map(|i| outgoing_from[*i].clone())
            .collect(),
        select_to.iter().map(|i| outgoing_to[*i].clone()).collect(),
    )
}

/// **The transit's solve** from its two ends' outgoing waves and its state: the right side
/// `h(α_g − α_h) + 2C w − h K u` and the executed solve's image `ζ = m̂⁻¹(…)` before the word splits
/// it.
pub fn transit_solve(
    contact: &ContactOperands,
    step: &Rat,
    outgoing_from: &[Rat],
    outgoing_to: &[Rat],
    displacement: &[Rat],
    rate: &[Rat],
) -> Result<(Vec<Rat>, Vec<Rat>), HnnError> {
    let (alpha_from, alpha_to) = channel_waves(contact, outgoing_from, outgoing_to);
    let h = step;
    let mut right = scale(h, &sub(&alpha_from, &alpha_to));
    let (stored, stiffened) = contact.forms_applied(displacement, rate);
    if contact.storage_rows.is_some() {
        right = add(&right, &scale(&integer(2), &stored));
    }
    if contact.stiffness_rows.is_some() {
        right = sub(&right, &scale(h, &stiffened));
    }
    let image = contact.solve.apply(&right)?;
    Ok((right, image))
}

/// **The transit's update at a solved `ζ`**: `ω = (G/2h)ζ`, `w′ = 2ω − w`, `u′ = u + hω`, and the
/// channel's outgoing waves `α_g − ζ/h`, `α_h + ζ/h`; off the channel each wave reflects straight
/// back to its own ring (Lean `HNN/Propagation.{partialIsometry_transit, transit_balance}`):
/// `E_a′ − E_a + h ω*D ω = (hG_a/4)(|α|² − |α_out|²) + ⟨ω, M_a ω − right⟩`.
pub fn transit_update(
    contact: &ContactOperands,
    step: &Rat,
    solved: &[Rat],
    outgoing_from: &[Rat],
    outgoing_to: &[Rat],
    displacement: &[Rat],
    rate: &[Rat],
) -> Transit {
    let (alpha_from, alpha_to) = channel_waves(contact, outgoing_from, outgoing_to);
    let (select_from, select_to) = &contact.selection;
    let h = step;
    let midpoint = scale(&(&contact.conductance / (integer(2) * h)), solved);
    let next_rate = sub(&scale(&integer(2), &midpoint), rate);
    let next_displacement = add(displacement, &scale(h, &midpoint));
    let exchange = scale(&h.recip(), solved);
    let out_from = sub(&alpha_from, &exchange);
    let out_to = add(&alpha_to, &exchange);
    let mut arrive_from = outgoing_from.to_vec();
    for (index, coordinate) in select_from.iter().enumerate() {
        arrive_from[*coordinate] = out_from[index].clone();
    }
    let mut arrive_to = outgoing_to.to_vec();
    for (index, coordinate) in select_to.iter().enumerate() {
        arrive_to[*coordinate] = out_to[index].clone();
    }
    let dissipation = h * quadratic(&contact.dissipation_rows, &midpoint);
    Transit {
        arrive_from,
        arrive_to,
        displacement: next_displacement,
        rate: next_rate,
        midpoint,
        dissipation,
        channel_in: (alpha_from, alpha_to),
        channel_out: (out_from, out_to),
    }
}

/// **The transit's chart term** `⟨ω, m ζ − right⟩` at the solved `ζ` the word carried (the chart's
/// residual `−R·right` and the split's `m(ζ − ζ̂)`), with its certified bound
/// `‖ω‖₁(δ‖right‖∞ + ‖m‖∞ u)`, `u` the unit of the split; both zero under the exact law.
pub fn transit_defect(
    contact: &ContactOperands,
    solved: &[Rat],
    midpoint: &[Rat],
    right: &[Rat],
    unit: &Rat,
) -> (Rat, Rat) {
    match &contact.chart {
        Some(chart) => {
            let residual = sub(&contact.operator_rows.apply(solved), right);
            (
                dot(midpoint, &residual),
                l1(midpoint) * (&chart.certificate * sup(right) + &contact.operator_norm * unit),
            )
        }
        None => (Rat::zero(), Rat::zero()),
    }
}

/// **The contact's midpoint two-port** under one solve and no split (Lean
/// `HNN/Propagation.{partialIsometry_transit, transit_balance}`): [`transit_solve`], then
/// [`transit_update`] at the solve's image. Under the exact law it is the law's transit; on a chart
/// it is the executed map before the word's splits.
pub fn transit(
    contact: &ContactOperands,
    step: &Rat,
    outgoing_from: &[Rat],
    outgoing_to: &[Rat],
    displacement: &[Rat],
    rate: &[Rat],
) -> Result<Transit, HnnError> {
    let (_, solved) = transit_solve(
        contact,
        step,
        outgoing_from,
        outgoing_to,
        displacement,
        rate,
    )?;
    Ok(transit_update(
        contact,
        step,
        &solved,
        outgoing_from,
        outgoing_to,
        displacement,
        rate,
    ))
}

// -------------------------------------------------------------------------------------------
// the global power

/// **The global power** `P = (h/4)[Σ_r Y_r|s_r|² + Σ_(r,a) G_a|a_(r←a)|²] + Σ_a E_a` of a change:
/// the storage waves per ring, the arriving waves per contact (`[at from, at to]`) and the contact
/// states `[u, w]`.
pub fn global_power(
    operands: &Operands,
    storage: &[Vec<Rat>],
    arrivals: &[[Vec<Rat>; 2]],
    states: &[[Vec<Rat>; 2]],
) -> Result<Rat, HnnError> {
    // Each ring's and each contact's term reads only its own waves and state: they are formed
    // together and summed afterwards in ring, then contact, order.
    let rings = operands.rings.len().min(storage.len());
    let contacts = operands
        .contacts
        .len()
        .min(arrivals.len())
        .min(states.len());
    let ring_terms = indexed(rings, |r| {
        Ok::<_, HnnError>(&operands.rings[r].admittance * dot(&storage[r], &storage[r]))
    })?;
    let contact_terms = indexed(contacts, |a| {
        let (contact, pair, state) = (&operands.contacts[a], &arrivals[a], &states[a]);
        Ok::<_, HnnError>((
            &contact.conductance * (dot(&pair[0], &pair[0]) + dot(&pair[1], &pair[1])),
            contact.energy(&state[0], &state[1])?,
        ))
    })?;
    let mut waves = Rat::zero();
    for term in ring_terms {
        waves += term;
    }
    let mut stored = Rat::zero();
    for (wave, energy) in contact_terms {
        waves += wave;
        stored += energy;
    }
    Ok(&operands.step / integer(4) * waves + stored)
}

/// [definition] **One tick's balance** (Lean `HNN/Word.word_tick_balance`): the power before and
/// after, the contacts' dissipation `h Σ ω*D ω ≥ 0`, the element's passive term
/// `(h/2) Σ Y_r ⟨x̄, W_s x̄⟩ ≤ 0`, the contrast ports' power `Π_c` (no sign), and the executed
/// word's residual (module header: the executed anchors, charts and splits, each term an exact
/// identity) with its bound from the certificates and the transients' cells. Under the exact law
/// the residual and its bound are zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TickBalance {
    pub before: Rat,
    pub after: Rat,
    pub dissipation: Rat,
    pub resist: Rat,
    pub contrast: Rat,
    pub residual: Rat,
    pub bound: Rat,
}

impl TickBalance {
    /// `P(t+1) = P(t) − dissipation + resist + Π_c + residual`, exactly, with the residual within
    /// its certified bound (Lean `HNN/LatticeWord.{chart_energy_identity, cayley_chart_energy,
    /// feedback_tick}`).
    pub fn closes(&self) -> bool {
        self.after
            == &self.before - &self.dissipation + &self.resist + &self.contrast + &self.residual
            && self.residual.abs() <= self.bound
    }
}

// -------------------------------------------------------------------------------------------
// the exact chart of a fixed operand

/// [definition; agent-inferred] **A fixed operand as integer rows over one denominator per row**:
/// the same exact map, applied with one normalization per output entry rather than one per term.
/// A word's operands are fixed at the cut, so each is charted once and applied every tick.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Rows {
    numerators: Vec<Vec<BigInt>>,
    denominators: Vec<BigInt>,
}

impl Rows {
    pub(crate) fn of(matrix: &ExactRatMatrix) -> Self {
        let (numerators, denominators) = (0..matrix.rows())
            .map(|row| integral(matrix.row(row).expect("in range")))
            .unzip();
        Self {
            numerators,
            denominators,
        }
    }

    /// `M v`, exactly.
    pub(crate) fn apply(&self, vector: &[Rat]) -> Vec<Rat> {
        let (values, denominator) = integral(vector);
        // Each row reads only itself and the shared vector: the rows run together.
        let rows = self.numerators.len().min(self.denominators.len());
        entries(rows, |row| {
            Rat::new(
                integer_dot(&self.numerators[row], &values),
                &self.denominators[row] * &denominator,
            )
        })
    }

    /// The rows as an exact matrix.
    fn matrix(&self) -> Result<ExactRatMatrix, HnnError> {
        let columns = self.numerators.first().map_or(0, Vec::len);
        Ok(ExactRatMatrix::shaped(
            self.numerators.len(),
            columns,
            self.numerators
                .iter()
                .zip(&self.denominators)
                .map(|(row, d)| row.iter().map(|n| Rat::new(n.clone(), d.clone())).collect())
                .collect(),
        )?)
    }
}

/// `⟨v, M v⟩`, or zero for an absent (zero) form.
fn quadratic(form: &Option<Rows>, vector: &[Rat]) -> Rat {
    match form {
        Some(rows) => dot(vector, &rows.apply(vector)),
        None => Rat::zero(),
    }
}

fn is_zero_matrix(matrix: &ExactRatMatrix) -> bool {
    matrix.entries().iter().all(Zero::is_zero)
}

/// `F Fᵀ`, entry by entry over each row's common denominator. Public for a realization that forms
/// the contact's squared forms off the host.
pub fn gram(factor: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
    let rows = Rows::of(factor);
    let n = factor.rows();
    // Each row of the upper triangle reads only the shared factor: the rows run together.
    let upper = entries(n, |i| {
        (i..n)
            .map(|j| {
                Rat::new(
                    integer_dot(&rows.numerators[i], &rows.numerators[j]),
                    &rows.denominators[i] * &rows.denominators[j],
                )
            })
            .collect::<Vec<Rat>>()
    });
    let mut values = vec![vec![Rat::zero(); n]; n];
    for (i, row) in upper.into_iter().enumerate() {
        for (offset, value) in row.into_iter().enumerate() {
            let j = i + offset;
            values[j][i] = value.clone();
            values[i][j] = value;
        }
    }
    Ok(ExactRatMatrix::shaped(n, n, values)?)
}
