//! Private consumer of the reflected contact law (Refs #62 #73).
//!
//! [definition; agent-inferred] Read the existing full-tick cut, never a replay history. The
//! helical pair's interior is z=(u,w), its boundary the selected junction return x=(α_g,α_h).
//! This touches pair, helix, faces and tube; cell holonomy and tower restrictions stay attached.
//! The October 2 contact record §10 supplies the law. The lessons' missing consumer, omitted
//! storage work and retained-tape failures are avoided by reading the live Word and its operands.
//! The contact instantiation and storage split remain formal obligations in #62.

use num_bigint::BigUint;
use num_traits::{One, Zero};

use crate::hnn::HnnError;
use crate::hnn::chart::carry;
use crate::hnn::constitution::{Constitution, DepositReading, FactorGradient, Locus};
use crate::hnn::field::{ConstitutionRead, Current, End, Field};
use crate::hnn::port::Deposit;
use crate::hnn::propagation::{ContactOperands, Operands};
use crate::hnn::word::{EndChange, PowerForm, Word};
use crate::ratio::linear::vector::{add, dot, matrix, scale, sub};
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};
use crate::ratio::{Rat, integer};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CutKind {
    BeforeJunction,
    AfterJunction,
}

// The refusals' payloads are read through `Debug` in the tests' failure messages.
#[allow(dead_code)]
#[derive(Debug)]
pub(super) enum Refusal {
    Hnn(HnnError),
    Linear(ExactLinearError),
    Cut(CutKind),
    Clock,
    Phase,
    Producer,
    Step,
}

impl From<HnnError> for Refusal {
    fn from(e: HnnError) -> Self {
        Self::Hnn(e)
    }
}
impl From<ExactLinearError> for Refusal {
    fn from(e: ExactLinearError) -> Self {
        Self::Linear(e)
    }
}

/// The declared constitution is kept whole for later return checks. `read` establishes only its
/// equality with the word's executed propagation operands: a Word does not store or prove which
/// source/receiving maps or receiving population opened it. Those unread entries are declarations,
/// not inferred provenance. This private instrumentation does not repair Word::continuing.
#[derive(Clone, Debug)]
pub(super) struct ContactCut {
    pub kind: CutKind,
    pub change: EndChange,
    field: Field,
    current: Current,
    producing: Constitution,
    operands: Operands,
    next_tick: usize,
}

impl ContactCut {
    pub fn read(
        word: &Word<'_>,
        producing: &Constitution,
        current: &Current,
    ) -> Result<Self, Refusal> {
        if word.is_ended() {
            return Err(Refusal::Cut(CutKind::AfterJunction));
        }
        if word.field_balances().len() != word.ticks() || word.balances().len() != word.ticks() {
            return Err(Refusal::Step); // A failed partial tick is not a full-tick cut.
        }
        let expected = if word.operands().lattice().is_some() {
            Operands::at_cut(word.field(), producing, current)?
        } else {
            Operands::exact_at_cut(word.field(), producing, current)?
        };
        // This private first consumer admits exact or cold-charted words. A warm chart is a
        // different declared operand; do not silently substitute it for the producing solve.
        if &expected != word.operands() {
            return Err(Refusal::Producer);
        }
        let next_tick = word
            .opened_at()
            .checked_add(word.ticks())
            .ok_or(Refusal::Clock)?;
        if word.clock().ticks() != BigUint::from(next_tick) {
            return Err(Refusal::Clock);
        }
        let change = word.change()?;
        for (ring, resonator) in word.operands().resonators().iter().enumerate() {
            if let Some(r) = resonator {
                let phase = r.phase_at(next_tick.saturating_sub(1));
                if change.resonator_phases[ring] != Some(phase) {
                    return Err(Refusal::Phase);
                }
            }
        }
        Ok(Self {
            kind: CutKind::BeforeJunction,
            change,
            field: word.field().clone(),
            current: current.clone(),
            producing: producing.clone(),
            operands: word.operands().clone(),
            next_tick,
        })
    }

    pub fn continuing<'a>(
        &self,
        field: &'a Field,
        producing: &Constitution,
        current: &Current,
        injection: &[Vec<Rat>],
        opened_at: usize,
    ) -> Result<Word<'a>, Refusal> {
        if self.kind != CutKind::BeforeJunction {
            return Err(Refusal::Cut(self.kind));
        }
        if opened_at != self.next_tick {
            return Err(Refusal::Clock);
        }
        if field != &self.field || current != &self.current {
            return Err(Refusal::Producer);
        }
        let operands = if self.operands.lattice().is_some() {
            Operands::at_cut(field, producing, current)?
        } else {
            Operands::exact_at_cut(field, producing, current)?
        };
        // A contact commit keeps the declared ring constitution, pump and junction ports.
        if operands.rings() != self.operands.rings()
            || operands.resonators() != self.operands.resonators()
        {
            return Err(Refusal::Producer);
        }
        for (ring, resonator) in operands.resonators().iter().enumerate() {
            if let Some(r) = resonator {
                if self.change.resonator_phases[ring]
                    != Some(r.phase_at(opened_at.saturating_sub(1)))
                {
                    return Err(Refusal::Phase);
                }
            }
        }
        for (old, new) in self.operands.contacts().iter().zip(operands.contacts()) {
            if old.ends() != new.ends()
                || old.exponent() != new.exponent()
                || old.conductance() != new.conductance()
            {
                return Err(Refusal::Producer);
            }
        }
        Word::continuing(field, operands, &self.change, injection, opened_at).map_err(Into::into)
    }

    /// One first full tick of a continued word. Its contact carry streams reopen at zero.
    /// Reconstruct α from the existing anchor and this cut's arrival; do not add a wave tape.
    pub fn first_step(
        &self,
        word: &Word<'_>,
        producing: &Constitution,
        current: &Current,
        a: usize,
    ) -> Result<StepRead, Refusal> {
        let after = Self::read(word, producing, current)?;
        if word.opened_at() != self.next_tick
            || !matches!(word.ticks(), 1 | 2)
            || producing != &self.producing
            || after.current != self.current
            || word.field() != &self.field
        {
            return Err(Refusal::Step);
        }
        let passage = &word.recorded()[0];
        // The actual first Passage, not a reconstructed anchor alone, binds every incoming field
        // storage wave, contact arrival and contact state. It is the existing word's live record.
        if passage.storage != self.change.storage
            || passage.arrivals != self.change.arrivals
            || passage.states != self.change.states
        {
            return Err(Refusal::Step);
        }
        for (ring, resonance) in word.resonances().iter().enumerate() {
            match (resonance, &self.change.resonators[ring]) {
                (Some(r), Some(input)) if r.steps[0].input == *input => {
                    let declared = word.operands().resonators()[ring].as_ref().unwrap();
                    if self.change.resonator_phases[ring]
                        != Some(declared.phase_at(self.next_tick.saturating_sub(1)))
                    {
                        return Err(Refusal::Phase);
                    }
                }
                (None, None) => {}
                _ => return Err(Refusal::Step),
            }
        }
        let next_passage = word.recorded().get(1);
        let (next_states, next_arrivals) = next_passage
            .map_or((&after.change.states, &after.change.arrivals), |p| {
                (&p.states, &p.arrivals)
            });
        let declared = self.field.contact(a);
        let (from, to) = declared.ends();
        let x = [(from, End::From), (to, End::To)].map(|(ring, end)| {
            let anchor = word.anchor(0, ring).expect("one full tick has its anchor");
            let slot = self.operands.end_slot(a, ring);
            declared
                .selection(end)
                .into_iter()
                .map(|i| integer(2) * &anchor[i] - &self.change.arrivals[a][slot][i])
                .collect::<Vec<_>>()
        });
        let contact = &word.operands().contacts()[a];
        let h = word.operands().step();
        let z = &self.change.states[a];
        let (c, k, _) = contact.forms();
        let right = sub(
            &add(
                &scale(h, &sub(&x[0], &x[1])),
                &scale(&integer(2), &c.apply(&z[1])?),
            ),
            &scale(h, &k.apply(&z[0])?),
        );
        let image = contact.solve()?.apply(&right)?;
        let split = |image: &[Rat]| {
            let mut remainder = vec![Rat::zero(); image.len()];
            match word.operands().lattice() {
                Some(lattice) => carry(&lattice.transient(), image, &mut remainder),
                None => image.to_vec(),
            }
        };
        let solved = split(&image);
        let omega = scale(&(contact.conductance() / (integer(2) * h)), &solved);
        if omega != passage.rates[a] {
            return Err(Refusal::Step);
        }
        let arrivals = [(from, End::From), (to, End::To)].map(|(ring, end)| {
            let slot = self.operands.end_slot(a, ring);
            let anchor = word.anchor(0, ring).expect("one full tick has its anchor");
            let mut outgoing = sub(&scale(&integer(2), anchor), &self.change.arrivals[a][slot]);
            for (j, i) in declared.selection(end).into_iter().enumerate() {
                let exchange = &solved[j] / h;
                if end == End::From {
                    outgoing[i] -= exchange;
                } else {
                    outgoing[i] += exchange;
                }
            }
            split(&outgoing)
        });
        if arrivals != next_arrivals[a] {
            return Err(Refusal::Step);
        }
        let images = [
            add(&z[0], &scale(h, &omega)),
            sub(&scale(&integer(2), &omega), &z[1]),
        ];
        let carried = images.each_ref().map(|image| split(image));
        if carried != next_states[a] {
            return Err(Refusal::Step);
        }
        let solve_split = sub(&solved, &image);
        let state_split = [sub(&carried[0], &images[0]), sub(&carried[1], &images[1])];
        // With one tick the local boundary is held. With two, x_next is the actual next junction
        // return, read against the first tick's state from that next Passage before it moves.
        let next_x = next_passage.map_or_else(
            || x.clone(),
            |p| {
                [(from, End::From), (to, End::To)].map(|(ring, end)| {
                    let slot = self.operands.end_slot(a, ring);
                    declared
                        .selection(end)
                        .into_iter()
                        .map(|i| integer(2) * &p.anchors[ring][i] - &p.arrivals[a][slot][i])
                        .collect()
                })
            },
        );
        let before = read(contact, h, &x, z)?;
        let next = read(contact, h, &next_x, &carried)?;
        let remainder = match (&before, &next) {
            (Read::Unique(_), Read::Unique(_)) => Some(recurrence(
                contact,
                h,
                &before,
                &next,
                &solve_split,
                &state_split,
            )?),
            _ => None, // Motion remains checked above; a plural/obstructed stationary chart stays attached.
        };
        Ok(StepRead {
            before,
            next,
            solve_split,
            state_split,
            remainder,
            boundary_advanced: next_passage.is_some(),
        })
    }

    /// Manual material replacement control, not an accepted Constitution::deposited successor.
    pub fn control_deposit(
        &self,
        after: &Constitution,
        a: usize,
        x: &[Vec<Rat>; 2],
    ) -> Result<DepositRead, Refusal> {
        let mut changed = 0;
        for b in 0..self.field.contacts().len() {
            for (old, new) in [
                (self.producing.contact_storage(b), after.contact_storage(b)),
                (
                    self.producing.contact_stiffness(b),
                    after.contact_stiffness(b),
                ),
                (
                    self.producing.contact_dissipation(b),
                    after.contact_dissipation(b),
                ),
            ] {
                if old != new {
                    if b != a {
                        return Err(Refusal::Producer);
                    }
                    changed += 1;
                }
            }
        }
        if changed != 1 {
            return Err(Refusal::Producer);
        }
        // This first consumer admits precisely one material factor changed by with_channel;
        // source/receiving maps, rings, signatures and every other constitution entry stay bound.
        let expected = self.producing.clone().with_channel(
            a,
            after.contact_storage(a).clone(),
            after.contact_stiffness(a).clone(),
            after.contact_dissipation(a).clone(),
        )?;
        if &expected != after {
            return Err(Refusal::Producer);
        }
        self.material_work(after, a, x, None)
    }

    /// Join a genuine returned successor to its native staged return and publication. Exactly one
    /// contact factor is admitted. Re-evaluating the existing immutable deposited law checks the
    /// *whole* successor and publication, including commits, clocks, statistics and carries; no
    /// list of metadata differences is silently ignored. This control does not certify that the
    /// staged covector was produced by a comparison: its declared provenance is the native return.
    pub fn deposited_return(
        &self,
        deposit: &Deposit,
        successor: &Constitution,
        publication: &DepositReading,
        a: usize,
        x: &[Vec<Rat>; 2],
    ) -> Result<DepositRead, Refusal> {
        if !deposit.linear().is_empty()
            || !deposit.landmarks().is_empty()
            || !deposit.receiving().is_empty()
            || deposit.factors().len() != 1
            || deposit.commit() != self.producing.commit()
            || deposit.loci().iter().any(|l| *l != Locus::Channel(a))
        {
            return Err(Refusal::Producer);
        }
        let contact = match &deposit.factors()[0].gradient {
            FactorGradient::Storage { contact, .. }
            | FactorGradient::Stiffness { contact, .. }
            | FactorGradient::Dissipation { contact, .. } => *contact,
            _ => return Err(Refusal::Producer),
        };
        if contact != a {
            return Err(Refusal::Producer);
        }
        let (checked, reading) = self.producing.deposited(deposit)?;
        if &checked != successor || &reading != publication {
            return Err(Refusal::Producer);
        }
        self.material_work(successor, a, x, Some(reading))
    }

    fn material_work(
        &self,
        after: &Constitution,
        a: usize,
        x: &[Vec<Rat>; 2],
        publication: Option<DepositReading>,
    ) -> Result<DepositRead, Refusal> {
        let operands = if self.operands.lattice().is_some() {
            Operands::at_cut(&self.field, after, &self.current)?
        } else {
            Operands::exact_at_cut(&self.field, after, &self.current)?
        };
        let before = read(
            &self.operands.contacts()[a],
            self.operands.step(),
            x,
            &self.change.states[a],
        )?;
        let next = read(
            &operands.contacts()[a],
            operands.step(),
            x,
            &self.change.states[a],
        )?;
        let old = PowerForm::read(&self.field, &self.producing, &self.current)?;
        let new = PowerForm::read(&self.field, after, &self.current)?;
        let work = old.deposition_work(&new, &self.change)?;
        let power_difference = new.power(&self.change)? - old.power(&self.change)?;
        Ok(DepositRead {
            before,
            next,
            work,
            power_difference,
            publication,
        })
    }
}

#[allow(dead_code)]
#[derive(Debug)]
pub(super) struct StorageRead {
    pub boundary: Vec<Rat>,
    pub interior: Vec<Rat>,
    pub chart: ExactRatMatrix,
    pub operator: ExactRatMatrix,
    pub drive: ExactRatMatrix,
    pub residual: Vec<Rat>,
    pub charted: Vec<Rat>,
    pub energy: Rat,
    pub residual_energy: Rat,
    pub cross: Rat,
    pub charted_energy: Rat,
}

impl StorageRead {
    pub fn closes(&self) -> bool {
        self.energy == &self.residual_energy + &self.cross + &self.charted_energy
    }
}

#[derive(Debug)]
pub(super) enum Read {
    Unique(StorageRead),
    Fibre {
        interior: Vec<Rat>,
        boundary: Vec<Rat>,
        particular: Vec<Rat>,
        kernel: Vec<Vec<Rat>>,
    },
    Obstructed {
        interior: Vec<Rat>,
        boundary: Vec<Rat>,
        covector: Vec<Rat>,
        pairing: Rat,
    },
}

/// Solve (I-𝒟)z_eq=𝒞x with the existing affine-fibre owner. Never assume stiffness invertible.
pub(super) fn read(
    contact: &ContactOperands,
    h: &Rat,
    x: &[Vec<Rat>; 2],
    z: &[Vec<Rat>; 2],
) -> Result<Read, Refusal> {
    let n = contact.width();
    if x.iter().chain(z).any(|v| v.len() != n) {
        return Err(Refusal::Step);
    }
    let (c, k, _) = contact.forms();
    let s = contact.solve()?;
    let (sc, sk) = (s.multiply(c)?, s.multiply(k)?);
    let g = contact.conductance();
    let operator = matrix(2 * n, 2 * n, |i, j| {
        let delta = if i % n == j % n {
            Rat::one()
        } else {
            Rat::zero()
        };
        let (i0, j0) = (i % n, j % n);
        match (i < n, j < n) {
            (true, true) => g * h / integer(2) * sk.get(i0, j0).unwrap(),
            (true, false) => -g * sc.get(i0, j0).unwrap(),
            (false, true) => g * sk.get(i0, j0).unwrap(),
            (false, false) => integer(2) * delta - integer(2) * g / h * sc.get(i0, j0).unwrap(),
        }
    })?;
    let drive = matrix(2 * n, 2 * n, |i, j| {
        let sign = if j < n { Rat::one() } else { -Rat::one() };
        let weight = if i < n { g * h / integer(2) } else { g.clone() };
        weight * sign * s.get(i % n, j % n).unwrap()
    })?;
    let boundary: Vec<Rat> = x.iter().flatten().cloned().collect();
    let interior: Vec<Rat> = z.iter().flatten().cloned().collect();
    let target = drive.apply(&boundary)?;
    match operator.preimage_fibre(&target)? {
        Some((particular, kernel)) if !kernel.is_empty() => Ok(Read::Fibre {
            interior,
            boundary,
            particular,
            kernel,
        }),
        None => {
            let covector = operator
                .preimage_obstruction(&target)?
                .expect("inconsistent fibre has an obstruction");
            let pairing = dot(&covector, &target);
            Ok(Read::Obstructed {
                interior,
                boundary,
                covector,
                pairing,
            })
        }
        Some(_) => {
            let chart = operator.inverse()?.multiply(&drive)?;
            let charted = chart.apply(&boundary)?;
            let residual = sub(&interior, &charted);
            let energy = |v: &[Rat]| -> Result<Rat, Refusal> {
                Ok(
                    (dot(&v[..n], &k.apply(&v[..n])?) + dot(&v[n..], &c.apply(&v[n..])?))
                        / integer(2),
                )
            };
            let cross = dot(&residual[..n], &k.apply(&charted[..n])?)
                + dot(&residual[n..], &c.apply(&charted[n..])?);
            Ok(Read::Unique(StorageRead {
                energy: energy(&interior)?,
                residual_energy: energy(&residual)?,
                charted_energy: energy(&charted)?,
                cross,
                boundary,
                interior,
                chart,
                operator,
                drive,
                residual,
                charted,
            }))
        }
    }
}

pub(super) fn recurrence(
    contact: &ContactOperands,
    h: &Rat,
    before: &Read,
    next: &Read,
    solve_split: &[Rat],
    state_split: &[Vec<Rat>; 2],
) -> Result<Vec<Rat>, Refusal> {
    let (Read::Unique(before), Read::Unique(next)) = (before, next) else {
        return Err(Refusal::Step);
    };
    let n = contact.width();
    if solve_split.len() != n || state_split.iter().any(|v| v.len() != n) {
        return Err(Refusal::Step);
    }
    let d = ExactRatMatrix::identity(2 * n)?.subtract(&before.operator)?;
    let forcing = before
        .drive
        .add(&d.multiply(&before.chart)?)?
        .apply(&before.boundary)?;
    let split: Vec<Rat> = [
        add(
            &scale(&(contact.conductance() / integer(2)), solve_split),
            &state_split[0],
        ),
        add(
            &scale(&(contact.conductance() / h), solve_split),
            &state_split[1],
        ),
    ]
    .into_iter()
    .flatten()
    .collect();
    Ok(sub(
        &add(
            &sub(&add(&d.apply(&before.residual)?, &forcing), &next.charted),
            &split,
        ),
        &next.residual,
    ))
}

#[derive(Debug)]
#[allow(dead_code)]
pub(super) struct StepRead {
    pub before: Read,
    pub next: Read,
    pub solve_split: Vec<Rat>,
    pub state_split: [Vec<Rat>; 2],
    pub remainder: Option<Vec<Rat>>,
    pub boundary_advanced: bool,
}

#[cfg(test)]
mod laws {
    use super::*;
    use crate::hnn::constitution::Lattice;
    use crate::hnn::propagation::{ExponentReading, transit_solve, transit_update};
    use crate::ratio::rat;

    fn contact(stiffness_factor: Rat) -> ContactOperands {
        let one = ExactRatMatrix::identity(1).unwrap();
        ContactOperands::new(
            (0, 1),
            (vec![0], vec![0]),
            ExponentReading {
                quadrance: Rat::zero(),
                exponent: Rat::zero(),
                carry: 0.into(),
                phase: 0,
            },
            Rat::one(),
            &Rat::one(),
            &one,
            &one.scaled(&stiffness_factor),
            &one,
        )
        .unwrap()
    }

    #[test]
    fn changing_chart_recurrence_keeps_each_executed_split() {
        let (old, new) = (contact(Rat::one()), contact(integer(2)));
        let x = [vec![rat(1, 2)], vec![rat(-1, 2)]];
        let next_x = [vec![Rat::one()], vec![rat(-1, 2)]];
        let z = [vec![rat(1, 2)], vec![rat(1, 3)]];
        let (_, image) = transit_solve(&old, &Rat::one(), &x[0], &x[1], &z[0], &z[1]).unwrap();
        let lattice = Lattice::new(2);
        let solved = carry(&lattice, &image, &mut [Rat::zero()]);
        let transit = transit_update(&old, &Rat::one(), &solved, &x[0], &x[1], &z[0], &z[1]);
        let images = [transit.displacement, transit.rate];
        let carried = images
            .each_ref()
            .map(|v| carry(&lattice, v, &mut [Rat::zero()]));
        let state_split = [sub(&carried[0], &images[0]), sub(&carried[1], &images[1])];
        let solve_split = sub(&solved, &image);
        let before = read(&old, &Rat::one(), &x, &z).unwrap();
        let after = read(&new, &Rat::one(), &next_x, &carried).unwrap();
        assert!(!solve_split[0].is_zero());
        assert!(state_split.iter().flatten().any(|x| !x.is_zero()));
        assert!(
            recurrence(
                &old,
                &Rat::one(),
                &before,
                &after,
                &solve_split,
                &state_split
            )
            .unwrap()
            .iter()
            .all(Zero::is_zero)
        );
        assert!(
            recurrence(
                &old,
                &Rat::one(),
                &before,
                &after,
                &[Rat::zero()],
                &state_split
            )
            .unwrap()
            .iter()
            .any(|x| !x.is_zero())
        );
        assert!(
            recurrence(
                &old,
                &Rat::one(),
                &before,
                &after,
                &solve_split,
                &[vec![Rat::zero()], vec![Rat::zero()]]
            )
            .unwrap()
            .iter()
            .any(|x| !x.is_zero())
        );
    }

    #[test]
    fn deposit_transport_keeps_the_metric_and_storage_cross_term() {
        let (old, new) = (contact(Rat::one()), contact(integer(2)));
        let x = [vec![rat(1, 2)], vec![rat(-1, 2)]];
        let z = [vec![rat(1, 2)], vec![rat(1, 3)]];
        let before = read(&old, &Rat::one(), &x, &z).unwrap();
        let next = read(&new, &Rat::one(), &x, &z).unwrap();
        let Read::Unique(a) = &before else {
            panic!("declared positive stiffness")
        };
        let Read::Unique(b) = &next else {
            panic!("declared positive stiffness")
        };
        assert!(a.closes() && b.closes());
        assert!(!a.residual_energy.is_zero() && !a.cross.is_zero() && !a.charted_energy.is_zero());
        let work = rat(3, 8); // ½ u² ΔK = ½ (½)² (2² − 1²).
        let receipt = DepositRead {
            before,
            next,
            work: work.clone(),
            power_difference: work,
            publication: None,
        };
        assert!(receipt.closes());
    }

    #[test]
    fn singular_stiffness_retains_the_complete_stationary_fibre() {
        let contact = contact(Rat::zero());
        let x = [vec![Rat::one()], vec![Rat::one()]];
        let z = [vec![integer(3)], vec![rat(1, 3)]];
        let Read::Fibre {
            interior,
            boundary,
            particular,
            kernel,
        } = read(&contact, &Rat::one(), &x, &z).unwrap()
        else {
            panic!("zero stiffness has a free displacement")
        };
        assert_eq!(interior, vec![integer(3), rat(1, 3)]);
        assert_eq!(boundary, vec![Rat::one(), Rat::one()]);
        assert_eq!(particular, vec![Rat::zero(), Rat::zero()]);
        assert_eq!(kernel, vec![vec![Rat::one(), Rat::zero()]]);
    }

    #[test]
    fn singular_stiffness_returns_the_boundary_obstruction() {
        let contact = contact(Rat::zero());
        let x = [vec![Rat::one()], vec![Rat::zero()]];
        let z = [vec![integer(3)], vec![rat(1, 3)]];
        let Read::Obstructed {
            interior,
            boundary,
            covector,
            pairing,
        } = read(&contact, &Rat::one(), &x, &z).unwrap()
        else {
            panic!("constant nonzero slip has no stationary state")
        };
        assert_eq!(interior, vec![integer(3), rat(1, 3)]);
        assert_eq!(boundary, vec![Rat::one(), Rat::zero()]);
        assert!(!pairing.is_zero());
        assert_eq!(covector.len(), 2);
    }
}

#[derive(Debug)]
pub(super) struct DepositRead {
    pub before: Read,
    pub next: Read,
    pub work: Rat,
    pub power_difference: Rat,
    pub publication: Option<DepositReading>,
}

impl DepositRead {
    pub fn closes(&self) -> bool {
        let (Read::Unique(before), Read::Unique(next)) = (&self.before, &self.next) else {
            return false;
        };
        before.closes()
            && next.closes()
            && self.work == self.power_difference
            && next.energy.clone() - &before.energy == self.work
            && next.residual_energy.clone() - &before.residual_energy + &next.cross - &before.cross
                + &next.charted_energy
                - &before.charted_energy
                == self.work
            && sub(&next.residual, &before.residual)
                == scale(
                    &-Rat::one(),
                    &next
                        .chart
                        .subtract(&before.chart)
                        .unwrap()
                        .apply(&before.boundary)
                        .unwrap(),
                )
    }
}
