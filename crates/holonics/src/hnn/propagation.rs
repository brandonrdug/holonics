//! **The local tick: the junction Swing, the ring element and the contact's midpoint two-port.**
//!
//! [definition] One tick is one contact hop (design (a), "The law of one passage", `tick`). Every
//! operand is fixed at the cut ([`Operands::at_cut`]): the pair quadrance and so each contact's
//! conductance from the rings' phases, the admittances from the declaration, the element's `K_r`
//! from the sheet classes of the standing contrast. Within a word each tick is therefore one exact
//! linear map of the change: the medium's Green's function.
//!
//! ```text
//! junction  G_a = κ_a Y_a,  κ_a = 2^(s_a),  s_a = −β_a Q_a / 2 = n_a + φ_a/L          one exponent per contact
//!           v_r = (Y_r s_r + Σ_a G_a a_(r←a)) / (Y_r + Σ_a G_a)                       participation is the anchor
//!           o_(r→a) = 2 v_r − a_(r←a),  b_r = 2 v_r − s_r,  c_r = v_r − s_r            the junction Swing
//! element   (I − ½K_r) s_r′ = (I + ½K_r) b_r + W_c,r c_r,   K_r = W_s,r + Σ_ρ σ_ρ,r A_ρ,r
//! transit   M_a ω_a = 2C_a w_a + h(α_g − α_h) − h K_a u_a,
//!           M_a = 2C_a + (2h/G_a) I + h D_a + (h²/2) K_a;   w ← 2ω − w,  u ← u + hω
//!           a_(g←a) = o_(g→a) − ι_g (2/G_a) ω_a,   a_(h←a) = o_(h→a) + ι_h (2/G_a) ω_a
//! power     P = (h/4)[Σ_r Y_r |s_r|² + Σ_(r,a) G_a |a_(r←a)|²] + Σ_a (½ w*C w + ½ u*K u)
//!           P(t+1) = P(t) − h Σ_a ω*D ω + (h/2) Σ_r Y_r ⟨x̄_r, W_s x̄_r⟩ + Π_c,
//!           Π_c = (h/2) Σ_r Y_r ⟨x̄_r, W_c c_r⟩,   x̄_r = ½(b_r + s_r′)
//! ```
//!
//! [definition] **The Swing is local** (guard 14): every solve here is a junction's own admittance
//! sum, a ring's own `I − ½K_r` (bijective for passive `K_r`, `Holon/Cayley.cayley_bijective`), or a
//! contact's own `k_a × k_a` `M_a` (positive definite for PSD squared carriers and `G_a > 0`). No
//! global solve over the contact graph exists; the cone test checks the support exactly.
//!
//! [definition; agent-inferred] **The tick realizes the midpoint scheme directly** (design (a),
//! "Reception is composed", item 1). The element step is exactly `ReferenceHolon`'s
//! implicit-midpoint advance (`holon::law`, `Holon/Law.advance_law`) of the medium
//! `ẋ = (Ω − R)x + W_c c` with `Q = I`, `h = 1`, `Ω = Σ σ_ρ A_ρ`, `R = −W_s`; the transit is exactly
//! its advance on `(u, p = C_a w)` with storage `(K_a, C_a⁻¹)`, resistance `D_a + (2/G_a)I` and the
//! channel waves as sources, whenever `C_a ≻ 0`. Two tests equate them at the same operands
//! (`tests/propagation.rs`, `the_element_step_is_the_reference_holons_midpoint_advance`,
//! `a_stored_transit_is_the_reference_holons_midpoint_advance`). The tick does not call the owner:
//! (i) `C_a = c_a c_aᵀ` may be singular (campaign 1 admits `c_a = 0`, pure transmission), where the
//! transit is a descriptor midpoint step with mass `C_a` that the owner's unit-mass step
//! `q⁺ − q = h((J − R)Q q̄ + B u)` does not state; (ii) a word's operands are fixed at its cut, so
//! each solved map (`Cay_r`, `(I − ½K_r)⁻¹W_c`, `M_a⁻¹`) is charted once and applied every tick,
//! and the return reads their transposes, while the owner solves its whole Dirac system
//! (`3σ + μ` unknowns) at every step.
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
//! | `HNN/Propagation.anchor_is_participation`, `junctionSwing_involutive`, `junctionSwing_isometry`; `Geometry/AffineSwing.swing` | [`junction_swing`] |
//! | `HNN/Word.reaction_stage_isometry`, `reaction_stage_balance`, `contrastPort_active`; `Holon/Cayley.drive_balance` | [`element_step`] |
//! | `HNN/Propagation.partialIsometry_transit`, `transit_balance`, `tick_well_defined` | [`transit`], [`ContactOperands`] |
//! | `HNN/Word.word_tick_balance` | [`global_power`], [`TickBalance`] |
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
use crate::hnn::field::{ConstitutionRead, Current, End, Field};
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
// the operands at the cut

/// [definition] **A ring's operands at the cut**: its admittance, the sheet classes of its standing
/// contrast, its element `K_r = W_s + Σ σ_ρ A_ρ`, and the element's two exact solved maps
/// `Cay_r = (I − ½K_r)⁻¹(I + ½K_r)` and `(I − ½K_r)⁻¹ W_c,r`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingOperands {
    admittance: Rat,
    sheets: Vec<bool>,
    element: ExactRatMatrix,
    passive: ExactRatMatrix,
    contrast: ExactRatMatrix,
    cayley: Rows,
    drive: Option<Rows>,
    passive_rows: Option<Rows>,
    contrast_rows: Option<Rows>,
}

impl RingOperands {
    /// Build a ring's operands from its declared admittance and its element material, at the sheet
    /// classes of the standing contrast `Δ_r` (`σ_ρ = sign Δ_r[ρ]`, `sign 0 = +1`, the half-open
    /// sheet). `Cay_r = 2(I − ½K_r)⁻¹ − I`, since `(I + ½K) = 2I − (I − ½K)`.
    pub fn new(
        admittance: Rat,
        contrast_reading: &[Rat],
        passive_factor: &ExactRatMatrix,
        contrast_port: &ExactRatMatrix,
        slices: &[(Vec<Rat>, Vec<Rat>)],
    ) -> Result<Self, HnnError> {
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
        let left = ExactRatMatrix::identity(n)?.subtract(&element.scaled(&rat(1, 2)))?;
        let solved = left.inverse()?;
        let cayley = solved
            .scaled(&integer(2))
            .subtract(&ExactRatMatrix::identity(n)?)?;
        let solved_rows = Rows::of(&solved);
        let drive = (!is_zero_matrix(contrast_port))
            .then(|| solved_rows.product(contrast_port))
            .transpose()?
            .map(|product| Rows::of(&product));
        Ok(Self {
            admittance,
            sheets,
            cayley: Rows::of(&cayley),
            drive,
            passive_rows: (!is_zero_matrix(&passive)).then(|| Rows::of(&passive)),
            contrast_rows: (!is_zero_matrix(contrast_port)).then(|| Rows::of(contrast_port)),
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
}

/// [definition] **A contact's operands at the cut**: its ends and channel selections, its exponent
/// reading and conductance `G_a = 2^(n_a) Y_a`, its squared forms `C_a`, `K_a`, `D_a`, and the solved
/// `M_a⁻¹` of its midpoint two-port.
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
    solve: Rows,
}

impl ContactOperands {
    /// Build a contact's operands from its geometry reading, its conductance, the hop `h` and its
    /// three square factors (`C = c cᵀ`, `K = b bᵀ`, `D = F Fᵀ`, each `k_a × m`). `M_a` is positive
    /// definite for `G_a > 0`, so its inverse exists (`tick_well_defined`).
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
        if !conductance.is_positive() {
            return Err(HnnError::NonpositiveDeclaration);
        }
        let h = step;
        let m = storage
            .scaled(&integer(2))
            .add(&ExactRatMatrix::identity(k)?.scaled(&(integer(2) * h / &conductance)))?
            .add(&dissipation.scaled(h))?
            .add(&stiffness.scaled(&(h * h / integer(2))))?;
        let solve = Rows::of(&m.inverse()?);
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
            solve,
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

    pub fn width(&self) -> usize {
        self.selection.0.len()
    }

    /// `E_a = ½ w*C w + ½ u*K u`.
    pub fn energy(&self, displacement: &[Rat], rate: &[Rat]) -> Result<Rat, HnnError> {
        Ok(
            (quadratic(&self.storage_rows, rate) + quadratic(&self.stiffness_rows, displacement))
                / integer(2),
        )
    }
}

/// [definition] **Every operand of a word, fixed at the cut.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operands {
    step: Rat,
    rings: Vec<RingOperands>,
    contacts: Vec<ContactOperands>,
    incident: Vec<Vec<usize>>,
}

/// **One ring's operands from the constitution**: its admittance and element material at the sheet
/// classes of its standing contrast `Δ_r = Σ_(a∋r) U_(r←a) q_(other end) − q_r`
/// ([`Field::standing_contrast`], read from the connection incidence's blocks). They read no lift
/// point; the contacts' conductances do.
pub fn ring_operands(
    field: &Field,
    constitution: &impl ConstitutionRead,
    index: usize,
) -> Result<RingOperands, HnnError> {
    let ring = field.rings().get(index).ok_or(HnnError::RingOutside {
        ring: index,
        rings: field.rings().len(),
    })?;
    let contrast = field.standing_contrast(constitution, index)?;
    RingOperands::new(
        ring.admittance().clone(),
        &contrast,
        constitution.passive_factor(index),
        constitution.contrast_port(index),
        constitution.slices(index),
    )
}

impl Operands {
    /// **The operands at the cut** `(Θ, λ)`: each contact's exponent from the pair quadrance of its
    /// rings' screws at `λ`, each ring's sheet classes from the standing contrast
    /// `Δ_r = Σ_(a∋r) U_(r←a) q_(other end) − q_r`, and the constitution's factors.
    pub fn at_cut(
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
    ) -> Result<Self, HnnError> {
        let rings = (0..field.rings().len())
            .map(|index| ring_operands(field, constitution, index))
            .collect::<Result<Vec<_>, _>>()?;
        let contacts = field
            .contacts()
            .iter()
            .enumerate()
            .map(|(index, contact)| {
                let exponent = contact_exponent(field, index, current.lift())?;
                if exponent.phase != 0 {
                    return Err(HnnError::ExponentPhase {
                        contact: index,
                        phase: exponent.phase,
                        grain: field.exponent_grain(),
                    });
                }
                let conductance = power_of_two(&exponent.carry)? * contact.admittance();
                ContactOperands::new(
                    contact.ends(),
                    (contact.selection(End::From), contact.selection(End::To)),
                    exponent,
                    conductance,
                    field.step(),
                    constitution.contact_storage(index),
                    constitution.contact_stiffness(index),
                    constitution.contact_dissipation(index),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            step: field.step().clone(),
            rings,
            contacts,
            incident: (0..field.rings().len())
                .map(|ring| field.incident(ring).to_vec())
                .collect(),
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

/// **The junction Swing** about the participation anchor (Lean
/// `HNN/Propagation.{anchor_is_participation, junctionSwing_involutive, junctionSwing_isometry}`):
/// the reflection `2P_D − I` onto the common-potential subspace, `W = diag(Y_r, G_a)`. Each wave
/// leaves as the owner's point Swing about the anchor ([`crate::geometry::swing::swing`] on
/// `ℚ^(2d_r)`, Lean `Geometry/AffineSwing.swing`); it divides by its own positive admittance sum
/// only.
pub fn junction_swing(
    admittance: &Rat,
    storage: &[Rat],
    arrivals: &[(&Rat, &[Rat])],
) -> Result<Junction, HnnError> {
    let width = storage.len();
    let mut total = admittance.clone();
    let mut weighted = scale(admittance, storage);
    for (conductance, wave) in arrivals {
        if wave.len() != width {
            return Err(HnnError::Shape {
                what: "arriving wave",
                expected: width,
                found: wave.len(),
            });
        }
        total += *conductance;
        weighted = add(&weighted, &scale(conductance, wave));
    }
    if !total.is_positive() {
        return Err(HnnError::NonpositiveDeclaration);
    }
    let anchor = scale(&total.recip(), &weighted);
    // Every wave leaves as the point Swing about the anchor (`geometry::swing` on `ℚ^(2d_r)`).
    Ok(Junction {
        storage_wave: swing(&anchor, &storage.to_vec()),
        contrast: sub(&anchor, storage),
        outgoing: arrivals
            .iter()
            .map(|(_, wave)| swing(&anchor, &wave.to_vec()))
            .collect(),
        anchor,
    })
}

// -------------------------------------------------------------------------------------------
// the ring element

/// [definition] **One element step**: the next storage `s′`, the midpoint `x̄ = ½(b + s′)`, and the
/// two unscaled balance terms `⟨x̄, W_s x̄⟩ ≤ 0` and `⟨x̄, W_c c⟩` (no sign).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElementStep {
    pub next: Vec<Rat>,
    pub midpoint: Vec<Rat>,
    pub resist: Rat,
    pub drive: Rat,
}

/// **The ring element's Cayley step with the contrast port inside the midpoint**:
/// `(I − ½K)s′ = (I + ½K)b + W_c c`, so `½|s′|² − ½|b|² = ⟨x̄, W_s x̄⟩ + ⟨x̄, W_c c⟩` exactly
/// (Lean `HNN/Word.reaction_stage_balance` over `Holon/Cayley.drive_balance`); with `W_s = W_c = 0`
/// it is an isometry (`reaction_stage_isometry`).
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
    let mut next = ring.cayley.apply(wave);
    if let Some(drive) = &ring.drive {
        next = add(&next, &drive.apply(contrast));
    }
    let midpoint = scale(&rat(1, 2), &add(wave, &next));
    let resist = quadratic(&ring.passive_rows, &midpoint);
    let drive = match &ring.contrast_rows {
        Some(port) => dot(&midpoint, &port.apply(contrast)),
        None => Rat::zero(),
    };
    Ok(ElementStep {
        next,
        midpoint,
        resist,
        drive,
    })
}

// -------------------------------------------------------------------------------------------
// the contact transit

/// [definition] **One transit**: the waves arriving back at the two ends, the next contact state,
/// the midpoint rate `ω`, the dissipation `h ω*D ω`, and the channel waves in and out.
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

/// **The contact's midpoint two-port** on its partial-isometry channel (Lean
/// `HNN/Propagation.{partialIsometry_transit, transit_balance}`): off the channel each wave
/// reflects straight back to its own ring; on it,
/// `E_a′ − E_a + h ω*D ω = (hG_a/4)(|α|² − |α_out|²)`. One `k_a × k_a` solve, already inverted at
/// the cut.
pub fn transit(
    contact: &ContactOperands,
    step: &Rat,
    outgoing_from: &[Rat],
    outgoing_to: &[Rat],
    displacement: &[Rat],
    rate: &[Rat],
) -> Result<Transit, HnnError> {
    let (select_from, select_to) = &contact.selection;
    let alpha_from: Vec<Rat> = select_from
        .iter()
        .map(|i| outgoing_from[*i].clone())
        .collect();
    let alpha_to: Vec<Rat> = select_to.iter().map(|i| outgoing_to[*i].clone()).collect();
    let h = step;
    let mut right = scale(h, &sub(&alpha_from, &alpha_to));
    if let Some(storage) = &contact.storage_rows {
        right = add(&right, &scale(&integer(2), &storage.apply(rate)));
    }
    if let Some(stiffness) = &contact.stiffness_rows {
        right = sub(&right, &scale(h, &stiffness.apply(displacement)));
    }
    let midpoint = contact.solve.apply(&right);
    let next_rate = sub(&scale(&integer(2), &midpoint), rate);
    let next_displacement = add(displacement, &scale(h, &midpoint));
    let exchange = scale(&(integer(2) / &contact.conductance), &midpoint);
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
    Ok(Transit {
        arrive_from,
        arrive_to,
        displacement: next_displacement,
        rate: next_rate,
        midpoint,
        dissipation,
        channel_in: (alpha_from, alpha_to),
        channel_out: (out_from, out_to),
    })
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
    let mut waves = Rat::zero();
    for (ring, wave) in operands.rings.iter().zip(storage) {
        waves += &ring.admittance * dot(wave, wave);
    }
    let mut stored = Rat::zero();
    for ((contact, pair), state) in operands.contacts.iter().zip(arrivals).zip(states) {
        waves += &contact.conductance * (dot(&pair[0], &pair[0]) + dot(&pair[1], &pair[1]));
        stored += contact.energy(&state[0], &state[1])?;
    }
    Ok(&operands.step / integer(4) * waves + stored)
}

/// [definition] **One tick's exact balance** (Lean `HNN/Word.word_tick_balance`): the power before
/// and after, the contacts' dissipation `h Σ ω*D ω ≥ 0`, the element's passive term
/// `(h/2) Σ Y_r ⟨x̄, W_s x̄⟩ ≤ 0` and the contrast ports' power `Π_c` (no sign).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TickBalance {
    pub before: Rat,
    pub after: Rat,
    pub dissipation: Rat,
    pub resist: Rat,
    pub contrast: Rat,
}

impl TickBalance {
    /// `P(t+1) = P(t) − dissipation + resist + Π_c`, exactly.
    pub fn closes(&self) -> bool {
        self.after == &self.before - &self.dissipation + &self.resist + &self.contrast
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
        self.numerators
            .iter()
            .zip(&self.denominators)
            .map(|(row, row_denominator)| {
                Rat::new(integer_dot(row, &values), row_denominator * &denominator)
            })
            .collect()
    }

    /// `M B` for a matrix `B`, column by column.
    fn product(&self, right: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
        let columns: Vec<Vec<Rat>> = (0..right.columns())
            .map(|column| {
                let values: Vec<Rat> = (0..right.rows())
                    .map(|row| right.get(row, column).expect("in range").clone())
                    .collect();
                self.apply(&values)
            })
            .collect();
        let rows = self.numerators.len();
        Ok(ExactRatMatrix::shaped(
            rows,
            columns.len(),
            (0..rows)
                .map(|row| columns.iter().map(|column| column[row].clone()).collect())
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

/// `F Fᵀ`, entry by entry over each row's common denominator.
pub(crate) fn gram(factor: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
    let rows = Rows::of(factor);
    let n = factor.rows();
    let mut entries = vec![vec![Rat::zero(); n]; n];
    for i in 0..n {
        for j in i..n {
            let value = Rat::new(
                integer_dot(&rows.numerators[i], &rows.numerators[j]),
                &rows.denominators[i] * &rows.denominators[j],
            );
            entries[j][i] = value.clone();
            entries[i][j] = value;
        }
    }
    Ok(ExactRatMatrix::shaped(n, n, entries)?)
}
