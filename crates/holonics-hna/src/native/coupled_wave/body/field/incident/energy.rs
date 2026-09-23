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
//! `0`. The participation is an exterior drive (an active receiver's delivered power, plan phase 7),
//! the projection onto the real-coded image is orthogonal (`≤ 0`), and `S_D` joins the contact
//! dissipation and the source injection `b` in one reflection, which this host reading does not
//! separate. Deposition work is `0`: a reaction deposit leaves the unit storage pairing unchanged
//! (`ReactionDepositRecord::storage_epsilon`).
use super::*;
use holonic_core::law::EnergyBalance;
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
type C = (Rat, Rat);
fn cmul(a: &C, b: &C) -> C {
    (&a.0 * &b.0 - &a.1 * &b.1, &a.0 * &b.1 + &a.1 * &b.0)
}
fn cadd(a: &C, b: &C) -> C {
    (&a.0 + &b.0, &a.1 + &b.1)
}
/// `Re⟨x, v⟩ = Σ Re(conj(x_i) v_i)`.
fn re_inner(x: &[C], v: &[C]) -> Rat {
    x.iter()
        .zip(v)
        .map(|(a, b)| &a.0 * &b.0 + &a.1 * &b.1)
        .sum()
}
fn apply(m: &[Vec<C>], v: &[C]) -> Vec<C> {
    m.iter()
        .map(|row| {
            row.iter()
                .zip(v)
                .fold((Rat::zero(), Rat::zero()), |acc, (a, b)| {
                    cadd(&acc, &cmul(a, b))
                })
        })
        .collect()
}

/// The exact reaction-stage balance of one row at the returned centres (see the module header):
/// `(stored, dissipated, port, reaction, defect)` and the core balance.
pub(crate) fn reaction_row_balance(
    certificate: &holonic_engine::native_ecology::constitutive_fibre::PowerNeutralCertificate<'_>,
    drive: &[ExactComplexWaveCurrent],
    step: &[ExactComplexWaveCurrent],
    contrast: &[Rat],
) -> Result<EnergyBalance, NativeSessionError> {
    let (n, k) = (certificate.n, certificate.k);
    if drive.len() != n || step.len() != n || contrast.len() != k {
        return Err(invalid("reaction balance extent"));
    }
    let unit = Rat::from_integer(num_bigint::BigInt::from(1) << certificate.grain);
    let coefficient = |a: usize, j: usize| -> C {
        let (re, im) = &certificate.coefficients[a][j];
        (
            Rat::from_integer(re.clone()) / &unit,
            Rat::from_integer(im.clone()) / &unit,
        )
    };
    let ws: Vec<Vec<C>> = (0..n)
        .map(|a| (0..n).map(|b| coefficient(a, b)).collect())
        .collect();
    let j: Vec<Vec<C>> = (0..n)
        .map(|a| {
            (0..n)
                .map(|b| {
                    (0..k).fold((Rat::zero(), Rat::zero()), |acc, r| {
                        let s = coefficient(a, n + k / 2 + r * n + b);
                        (&acc.0 + &contrast[r] * &s.0, &acc.1 + &contrast[r] * &s.1)
                    })
                })
                .collect()
        })
        .collect();
    let wc: Vec<C> = (0..n)
        .map(|a| {
            (0..k / 2).fold((Rat::zero(), Rat::zero()), |acc, m| {
                cadd(
                    &acc,
                    &cmul(
                        &coefficient(a, n + m),
                        &(contrast[2 * m].clone(), contrast[2 * m + 1].clone()),
                    ),
                )
            })
        })
        .collect();
    let p: Vec<C> = drive
        .iter()
        .map(|z| (z.real.clone(), z.imaginary.clone()))
        .collect();
    let y: Vec<C> = step
        .iter()
        .map(|z| (z.real.clone(), z.imaginary.clone()))
        .collect();
    let xbar: Vec<C> = p
        .iter()
        .zip(&y)
        .map(|(a, b)| ((&a.0 + &b.0) * half(), (&a.1 + &b.1) * half()))
        .collect();
    // ρ = (I + K/2)p + W_c c − (I − K/2)y = p − y + K x̄ + W_c c.
    let (wsx, jx) = (apply(&ws, &xbar), apply(&j, &xbar));
    let rho: Vec<C> = (0..n)
        .map(|a| {
            (
                &p[a].0 - &y[a].0 + &wsx[a].0 + &jx[a].0 + &wc[a].0,
                &p[a].1 - &y[a].1 + &wsx[a].1 + &jx[a].1 + &wc[a].1,
            )
        })
        .collect();
    let stored = (re_inner(&y, &y) - re_inner(&p, &p)) * half();
    let dissipated = -re_inner(&xbar, &wsx);
    let port = re_inner(&xbar, &wc);
    let reaction = re_inner(&xbar, &jx);
    let defect = -re_inner(&xbar, &rho);
    Ok(EnergyBalance::closed(
        stored,
        dissipated,
        port,
        reaction,
        Rat::zero(),
        defect,
    ))
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
                    let row_balance =
                        reaction_row_balance(&cayley.certificate, &p.center, &y.center, &c)?;
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
