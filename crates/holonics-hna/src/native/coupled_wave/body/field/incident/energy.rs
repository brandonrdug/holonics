//! The exterior energy balance of one committed power-neutral incident word.
//!
//! [definition; agent-inferred] Read host-side from the word's returned balls at their exact
//! centres, never an operand of the word or its return. With `E(x) = ½|x|²` (the current's unit
//! storage pairing), each refinement step is the chain
//!
//! ```text
//! q ─participation→ p ─Cayley reaction→ y ─projection→ a ─S_D reflection→ r ─relaxation→ q⁺
//! ```
//!
//! and its stored change telescopes exactly into the stage terms. The reaction stage is the core
//! Holon balance (`holonic_core::law::EnergyBalance`, `Holon/Cayley.lean::midpoint_reaction_balance`):
//! with `x̄ = (p + y)/2` and the exact residual `ρ = (I + K/2)p + W_c c − (I − K/2)y` of the returned
//! centre, `½|y|² − ½|p|² = −⟨x̄, R x̄⟩ + Re⟨x̄, W_c c⟩ + Re⟨x̄, J(c) x̄⟩ − Re⟨x̄, ρ⟩`, `R = −herm W_s`:
//! `dissipated`, `port`, `reaction` (the skew interconnection's work, exactly `0` for exactly
//! skew-Hermitian slices at every point of every ball, `Holon/Reaction.lean::skewReaction_workless`)
//! and the solve's `discretization_defect`; the core balance's residual is computed and must be
//! `0`. The per-row balance is the chart's facet (`ResidentHolonChart::reaction_step_balance`,
//! plan phase 12a), not a parallel reading of the certificate. The participation is an exterior drive (an active receiver's delivered power, plan phase 7),
//! the projection onto the real-coded image is orthogonal (`≤ 0`), and `S_D` joins the contact
//! dissipation and the source injection `b` in one reflection, which this host reading does not
//! separate. Deposition work is `0`: a reaction deposit leaves the unit storage pairing unchanged
//! (`ReactionDepositRecord::storage_epsilon`).
use super::holon_chart::{ResidentHolonChart, RingReaction};
use super::*;
use holonic_engine::ExactComplexWaveCurrent;
use num_traits::{ToPrimitive, Zero};
use relational_geometry::Rat;

/// One committed word's balance. Exact terms are kept as rationals; `f64` fields are readings.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct IncidentEnergyBalance {
    /// The body generation this word was committed at.
    pub generation: u64,
    pub steps: usize,
    /// `E(q_final) − E(q_anchor)` over the joint current (before the commit's rebase).
    pub stored_change: f64,
    /// `Σ E(p) − E(q_boundary)`: the participation drive's delivered power (exterior drive).
    pub participation: f64,
    /// `Σ ⟨x̄, R x̄⟩ ≥ 0` of the reaction stage.
    pub reaction_dissipated: f64,
    /// `Σ Re⟨x̄, W_c c⟩`: the contrast port of the reaction stage.
    pub reaction_port: f64,
    /// `Σ Re⟨x̄, J(c) x̄⟩`, exact: must be `0`.
    pub reaction: Rat,
    /// `Σ −Re⟨x̄, ρ⟩`: the certified solve's centre residual.
    pub reaction_solve_defect: f64,
    /// Whether every row's core `EnergyBalance` closed with residual exactly `0`.
    pub reaction_balance_exact: bool,
    /// `Σ E(a) − E(y)` (`≤ 0`).
    pub projection: f64,
    /// `Σ E(S_D(a)) − E(a)`: contact dissipation and source injection, joined.
    pub reflection: f64,
    /// `Σ E(q⁺) − E(S_D(a))`: the held relaxation toward the anchor.
    pub relaxation: f64,
    /// `½⟨x, (Q' − Q)x⟩ = 0` (unit pairing).
    pub deposition_work: Rat,
    /// `stored_change − Σ terms`, computed exactly: `0`.
    pub residual: Rat,
    /// `½|q_final|²` per site (ring).
    pub rings: Vec<f64>,
}

fn f(value: &Rat) -> f64 {
    value.to_f64().unwrap_or(f64::NAN)
}
fn half() -> Rat {
    Rat::new(1.into(), 2.into())
}
fn energy(center: &[ExactComplexWaveCurrent]) -> Rat {
    center
        .iter()
        .map(|z| &z.real * &z.real + &z.imaginary * &z.imaginary)
        .sum::<Rat>()
        * half()
}
/// The interleaved real chart `[re₀, im₀, re₁, im₁, …]` of a complex centre.
fn realified(center: &[ExactComplexWaveCurrent]) -> Vec<Rat> {
    center
        .iter()
        .flat_map(|z| [z.real.clone(), z.imaginary.clone()])
        .collect()
}

impl<'c> IncidentFieldModel<'c> {
    /// The balance of a committed word (see the module header). Power-neutral words only.
    pub(super) fn read_energy_balance(
        &self,
        word: &IncidentWord<'c>,
    ) -> Result<IncidentEnergyBalance, NativeSessionError> {
        let boundary = word.source.boundary_components() / 2;
        let joint = |e: &ResidentNormalEnclosure<'c>| -> Result<Vec<ExactComplexWaveCurrent>, NativeSessionError> {
            Ok(e.view().inspect()?.center)
        };
        let anchor = joint(&word.anchor)?;
        let output = joint(&word.output)?;
        let mut balance = IncidentEnergyBalance {
            generation: self.generations,
            steps: word.steps.len(),
            stored_change: f(&(energy(&output) - energy(&anchor))),
            participation: 0.0,
            reaction_dissipated: 0.0,
            reaction_port: 0.0,
            reaction: Rat::zero(),
            reaction_solve_defect: 0.0,
            reaction_balance_exact: true,
            projection: 0.0,
            reflection: 0.0,
            relaxation: 0.0,
            deposition_work: Rat::zero(),
            residual: Rat::zero(),
            rings: output[..boundary]
                .chunks(self.layout.width / 2)
                .map(|ring| f(&energy(ring)))
                .collect(),
        };
        let (mut participation, mut dissipated, mut port, mut defect) =
            (Rat::zero(), Rat::zero(), Rat::zero(), Rat::zero());
        let (mut projection, mut reflection, mut relaxation) =
            (Rat::zero(), Rat::zero(), Rat::zero());
        for (index, step) in word.steps.iter().enumerate() {
            let before = joint(&step.before)?;
            let input = joint(&step.input)?;
            let reflected = joint(&step.reflected)?;
            let after = match word.steps.get(index + 1) {
                Some(next) => joint(&next.before)?,
                None => output.clone(),
            };
            let (mut drive_energy, mut step_energy) = (Rat::zero(), Rat::zero());
            for stage in &step.sites {
                let cayley = stage
                    .cayley
                    .as_ref()
                    .ok_or_else(|| invalid("energy balance of a legacy reaction stage"))?;
                let drives = stage.phase.output().inspect_rows()?;
                let steps = cayley.step.inspect_rows()?;
                let contrasts = match &stage.condition {
                    Some(c) => c.inspect_rows()?,
                    None => vec![],
                };
                for (row, (p, y)) in drives.iter().zip(&steps).enumerate() {
                    let c: Vec<Rat> = contrasts
                        .get(row)
                        .map(|ball| {
                            ball.center
                                .iter()
                                .flat_map(|z| [z.real.clone(), z.imaginary.clone()])
                                .collect()
                        })
                        .unwrap_or_default();
                    // The ring Holon's step balance (the chart's advance facet), read at the
                    // returned centres.
                    let row_balance = ResidentHolonChart::reaction_step_balance(
                        &RingReaction::certified(&cayley.certificate, &c),
                        &realified(&p.center),
                        &realified(&y.center),
                    )?;
                    balance.reaction_balance_exact &= row_balance.is_exact();
                    balance.reaction += &row_balance.active;
                    dissipated += &row_balance.dissipated;
                    port += &row_balance.port;
                    defect += &row_balance.discretization_defect;
                    drive_energy += energy(&p.center);
                    step_energy += energy(&y.center);
                }
            }
            participation += &drive_energy - energy(&before[..boundary]);
            projection += energy(&input[..boundary]) - &step_energy;
            reflection += energy(&reflected) - energy(&input);
            relaxation += energy(&after) - energy(&reflected);
        }
        let stored = energy(&output) - energy(&anchor);
        let reaction_stored = -&dissipated + &port + &balance.reaction + &defect;
        balance.residual =
            &stored - (&participation + reaction_stored + &projection + &reflection + &relaxation);
        balance.participation = f(&participation);
        balance.reaction_dissipated = f(&dissipated);
        balance.reaction_port = f(&port);
        balance.reaction_solve_defect = f(&defect);
        balance.projection = f(&projection);
        balance.reflection = f(&reflection);
        balance.relaxation = f(&relaxation);
        Ok(balance)
    }
}
