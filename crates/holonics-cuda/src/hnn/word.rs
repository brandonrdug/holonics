//! **The inverse charts' entries and the loaded resonators' plan on the card** (the lattice word;
//! kernels `hnn_inverse_residual`, `hnn_inverse_refine` and `hnn_inverse_certificate` in
//! `kernels/hnn.cu`, launched by `store`; the resonators run inside `kernels/hnn_word.cuh`'s
//! forward and reverse word, launched by `execute`).
//!
//! [definition] **The contract** (Lean `HNN/LatticeWord`, `HNN/LatticeDeposit.quot`/`rem`), shared
//! with the host owner in `holonics::hnn::chart`. Every quantity is an integer coordinate on a
//! declared lattice, and the only rounding is the nearest-point split, ties upward, whose remainder
//! is bounded:
//!
//! ```text
//! split_L(s) = (q, r) ,  s = q·2^L + r ,  −2^(L−1) ≤ r < 2^(L−1)     (L = 0: q = s, r = 0)
//!
//! inverse      A = a·2^(−L_A), X̂ = ξ·2^(−L_c), S = L_A + L_c ≤ 126
//! residual     ρ = 2^S·1 − aξ               (R = 1 − AX̂ on 2^(−S)ℤ)
//! refinement   ξ'' = split_S(ξ(2^(S+1)·1 − aξ)).q = ξ + split_S(ξρ).q     (nsStep, right form)
//!              the discarded remainder |e| ≤ 2^(S−1): |Δ| ≤ 2^(−L_c)/2
//! certificate  ‖1 − AX̂‖∞ = max_i Σ_j |ρ_ij| / 2^S       (exact; rounded_refinement_certificate)
//! ```
//!
//! [definition] **Refusals, never rounding**, per entry, in this order:
//! - [`Refusal::Operand`]: the entry reads a coordinate refused upstream (a residual entry `(i, j)`
//!   reads column `j` of the chart; a refinement entry reads row `i` of the chart and column `j` of
//!   the residual; a certificate reads its whole residual);
//! - [`Refusal::Carrier`]: its l1 certificate reaches `2^127` (`kernels/exact_integer.cuh`): for a
//!   residual `2^S δ_ij + Σ_k |a_ik ξ_kj|`, for a refinement `Σ_k |ξ_ik| |ρ_kj|` (a word times a
//!   carrier word), for a certificate the row sum itself;
//! - [`Refusal::Word`]: the new chart coordinate lies outside the signed 64-bit word.
//!
//! [definition] **The ceiling is derived, not authored.** An inverse's `2^S` is a carrier word
//! exactly when `S ≤ 126` ([`INVERSE_EXPONENT_CEILING`]).
//!
//! The carried tick and its adjoint as separate launches (`hnn_word_tick`, `hnn_word_adjoint_tick`),
//! their resident chaining and captured graphs, and the standalone resident inverse charts were
//! retired on September 28: the word runs whole in `hnn_word_forward`/`hnn_word_reverse`, and the
//! charts live in `store`. They are at
//! [`2d34b819`](https://github.com/brandonrdug/holonics/tree/2d34b819/crates/holonics-cuda/src/hnn/word.rs).

use holonics::ratio::Rat;
use num_bigint::BigInt;
use num_traits::{One, Signed};

use crate::hnn::DeviceError;

/// The inverse charts' entries' names in the image.
pub const RESIDUAL_ENTRY: &str = "hnn_inverse_residual";
pub const REFINE_ENTRY: &str = "hnn_inverse_refine";
pub const CERTIFICATE_ENTRY: &str = "hnn_inverse_certificate";

/// The largest `S = L_A + L_c` of an inverse pair: `2^S` lies in the carrier `(−2^127, 2^127)`
/// exactly when `S ≤ 126`.
pub const INVERSE_EXPONENT_CEILING: u32 = i128::BITS - 2;

// The status words (`kernels/exact_integer.cuh`).
const EXACT: u32 = 0;
const REFUSED_CARRIER: u32 = 1;
const REFUSED_WORD: u32 = 4;
const REFUSED_OPERAND: u32 = 8;

// -------------------------------------------------------------------------------------------
// refusals

/// [definition] **Why an entry was refused** (see the module header). Nothing is rounded instead.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Refusal {
    /// The entry's l1 certificate reached `2^127`.
    Carrier,
    /// The new coordinate lies outside the signed 64-bit word.
    Word,
    /// The entry reads a coordinate refused upstream.
    Operand,
}

impl Refusal {
    /// The refusal a status word carries, `None` when exact.
    pub fn of_status(status: u32) -> Result<Option<Self>, DeviceError> {
        match status {
            EXACT => Ok(None),
            REFUSED_CARRIER => Ok(Some(Self::Carrier)),
            REFUSED_WORD => Ok(Some(Self::Word)),
            REFUSED_OPERAND => Ok(Some(Self::Operand)),
            other => Err(DeviceError::Status { status: other }),
        }
    }
}

// -------------------------------------------------------------------------------------------
// the ring's resonator (campaign 2)

/// [definition] **The loaded resonators' plan** (campaign 2, `holonics::hnn::ring`; the loaded resonator):
/// every declared resonator's storage, dissipation and pumped stiffnesses as dyadic words at one
/// exponent `L_m`, the optional symmetric quartic coefficient `beta` at `L_beta`, each phase's
/// operator at `L_operator`, its executed charts (the host's certified lattice charts, at `L_c`),
/// and the hop `h = 2^(e_h)`. It refuses what the card's dyadic words
/// cannot carry: a hop that is not a nonnegative power of two, material off the dyadics, a word
/// under the exact law (no chart), or charts of different exponents. The resident word embeds these
/// operands in `execute::WordPlan` and runs them inside its forward and reverse kernels
/// (`hnn_word_forward`, `hnn_word_reverse`), the resonator's only realization on the card.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorPlan {
    rings: Vec<usize>,
    widths: Vec<usize>,
    capacity: Vec<i64>,
    capacity_base: Vec<u64>,
    dissipation: Vec<i64>,
    dissipation_base: Vec<u64>,
    stiffness: Vec<i64>,
    operators: Vec<i64>,
    operator_base: Vec<u64>,
    charts: Vec<i64>,
    phase_base: Vec<u64>,
    e_h: u32,
    l_m: u32,
    l_operator: u32,
    l_c: u32,
    l_w: u32,
    /// Effective beta, its exponent, and L_f=max(L_m,L_beta+2L_w), per declared ring.
    /// None keeps the quadratic midpoint law. The cubic effort and its Hessian return use
    /// this same scale, with no intermediate split.
    saturation: Vec<Option<(i64, u32, u32)>>,
}

fn hop_exponent(hop: &Rat) -> Option<u32> {
    if !hop.denom().is_one() || !hop.numer().is_positive() {
        return None;
    }
    let bits = hop.numer().bits();
    (hop.numer() == &(BigInt::one() << (bits - 1) as usize)).then(|| (bits - 1) as u32)
}

impl ResonatorPlan {
    /// **The plan of a word's resonators** from the host's operands at the cut (the lattice word's:
    /// each phase's chart is the one the host executes) and the transients' exponent `L_w`.
    pub fn form(
        resonators: &[&holonics::hnn::ring::ResonatorOperands],
        transient: u32,
    ) -> Result<Self, holonics::hnn::HnnError> {
        use crate::hnn::dyadic::{DyadicMatrix, common_exponent, refused};
        if resonators.is_empty() {
            return Err(refused("a resonator word carries at least one resonator"));
        }
        let hop = resonators[0].hop();
        let e_h = hop_exponent(hop).ok_or(refused("a resonator's hop that is 2^e, e ≥ 0"))?;
        let mut forms: Vec<&holonics::ratio::linear::ExactRatMatrix> = Vec::new();
        let mut stiffnesses = Vec::new();
        let mut operators = Vec::new();
        for resonator in resonators {
            if resonator.hop() != hop {
                return Err(refused("one hop for every resonator of a word"));
            }
            forms.push(resonator.material().forms().0);
            forms.push(resonator.material().forms().2);
            for phase in 0..resonator.phases() {
                stiffnesses.push(resonator.stiffness(phase).clone());
                operators.push(resonator.operator(phase).clone());
            }
        }
        let l_m = common_exponent(
            forms
                .iter()
                .flat_map(|form| form.entries())
                .chain(stiffnesses.iter().flat_map(|form| form.entries())),
            "a resonator's storage and stiffness on the dyadics",
        )?;
        let l_operator = common_exponent(
            operators.iter().flat_map(|form| form.entries()),
            "a loaded resonator's operator on the dyadics",
        )?;
        let mut plan = Self {
            rings: Vec::new(),
            widths: Vec::new(),
            capacity: Vec::new(),
            capacity_base: Vec::new(),
            dissipation: Vec::new(),
            dissipation_base: Vec::new(),
            stiffness: Vec::new(),
            operators: Vec::new(),
            operator_base: Vec::new(),
            charts: Vec::new(),
            phase_base: Vec::new(),
            e_h,
            l_m,
            l_operator,
            l_c: 0,
            l_w: transient,
            saturation: Vec::new(),
        };
        let mut chart_exponent: Option<u32> = None;
        for resonator in resonators {
            let n = resonator.width();
            let saturation = resonator
                .material()
                .saturation()
                .map(|law| {
                    use crate::hnn::dyadic::{exponent_of, word};
                    if n == 0 || !n.is_multiple_of(2) {
                        return Err(refused("a saturation's nonempty realified node width"));
                    }
                    let exponent = exponent_of(law.coefficient())
                        .ok_or_else(|| refused("a resonator's saturation on the dyadics"))?;
                    let beta = word(law.coefficient(), exponent, "a resonator's saturation word")?;
                    let force_exponent = transient
                        .checked_mul(2)
                        .and_then(|grain| exponent.checked_add(grain))
                        .map(|nonlinear| l_m.max(nonlinear))
                        .ok_or_else(|| refused("a resonator's force exponent"))?;
                    Ok::<_, holonics::hnn::HnnError>((beta, exponent, force_exponent))
                })
                .transpose()?;
            plan.saturation.push(saturation);
            plan.rings.push(resonator.ring());
            plan.widths.push(n);
            plan.capacity_base.push(plan.capacity.len() as u64);
            plan.capacity.extend(
                DyadicMatrix::at(resonator.material().forms().0, l_m, "a resonator's storage")?
                    .words,
            );
            plan.dissipation_base.push(plan.dissipation.len() as u64);
            plan.dissipation.extend(
                DyadicMatrix::at(
                    resonator.material().forms().2,
                    l_m,
                    "a resonator's dissipation",
                )?
                .words,
            );
            plan.phase_base.push(plan.stiffness.len() as u64);
            plan.operator_base.push(plan.operators.len() as u64);
            for phase in 0..resonator.phases() {
                plan.stiffness.extend(
                    DyadicMatrix::at(resonator.stiffness(phase), l_m, "a resonator's stiffness")?
                        .words,
                );
                plan.operators.extend(
                    DyadicMatrix::at(
                        resonator.operator(phase),
                        l_operator,
                        "a loaded resonator's operator",
                    )?
                    .words,
                );
                let chart = resonator.chart_words(phase).ok_or(refused(
                    "a resonator's chart: the word runs on its lattices",
                ))?;
                match chart_exponent {
                    None => chart_exponent = Some(chart.exponent()),
                    Some(exponent) if exponent != chart.exponent() => {
                        return Err(refused("one chart exponent for every resonator of a word"));
                    }
                    Some(_) => {}
                }
                plan.charts.extend_from_slice(chart.words());
            }
        }
        plan.l_c = chart_exponent.unwrap_or(0);
        // The existing nearest-point splitter carries shifts through i128::BITS-1. A finer
        // nonlinear image needs another exact carrier; it must not acquire an extra split.
        for (_, _, force_exponent) in plan.saturation.iter().flatten() {
            if force_exponent
                .checked_add(plan.l_c)
                .is_none_or(|shift| shift >= i128::BITS)
            {
                return Err(refused(
                    "a saturation's rate split beyond the integer carrier",
                ));
            }
        }
        Ok(plan)
    }

    /// The rings whose resonators the plan carries, in order.
    pub fn rings(&self) -> &[usize] {
        &self.rings
    }

    /// CUDA word-plan operands, in each resonator's declaration order. The loaded word embeds
    /// these beside its junction/contact charts so the coupled tick can stay in one resident
    /// forward/reverse launch.
    pub(crate) fn execution_operands(
        &self,
    ) -> (
        &[i64],
        &[u64],
        &[i64],
        &[u64],
        &[i64],
        &[u64],
        &[i64],
        &[u64],
        &[i64],
    ) {
        (
            &self.capacity,
            &self.capacity_base,
            &self.dissipation,
            &self.dissipation_base,
            &self.stiffness,
            &self.phase_base,
            &self.operators,
            &self.operator_base,
            &self.charts,
        )
    }

    /// Each ring's effective saturation coefficient and force scale, in declaration order.
    pub(crate) fn execution_saturation(&self) -> &[Option<(i64, u32, u32)>] {
        &self.saturation
    }

    /// Per-resonator declaration tables for the coupled word kernel: the rings, their widths, and
    /// `(e_h, L_m, L_operator, L_c)`.
    pub(crate) fn execution_shape(&self) -> (&[usize], &[usize], (u32, u32, u32, u32)) {
        (
            &self.rings,
            &self.widths,
            (self.e_h, self.l_m, self.l_operator, self.l_c),
        )
    }
}
