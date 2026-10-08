//! The contact material's first variation through a bounded continuing current (Refs #73 #62).
//!
//! [agent-inferred] Recover the local tangent equations in `hnn/tests/port`, using the existing
//! junction, element, loaded solve and contact variation owners. The retained columns are
//! `EndChange`, not Words or source occurrences. For a later observed ratio the ordinary native
//! contact consumer reads `g = g_this_word + J_open^* mu_open`. This is a differential at one
//! material point. The continuing consumer binds the reached sum to the source-owned ContactCut
//! and rebases under its explicitly declared realized-factor-translation action. It claims no
//! learner-policy derivative or finite decrease of the historical comparison.

use super::continuation::ContactCut;
use super::*;
use crate::hnn::constitution::{Constitution, FactorGradient, FactorStep, Family, Locus, Reach};
use crate::hnn::field::ConstitutionRead;
use crate::hnn::port::{ChangeCovector, Deposit, WordReturn};
use crate::hnn::propagation::transit_variation;
use crate::hnn::ratio::{HolonRatio, target_phases};
use crate::hnn::retention::Diamond;

mod rebase;

/// The parameter family whose first variation the current carries. A realized translation
/// holds the actually applied factor increments as exterior controls: P = I. It differentiates
/// neither observation selection nor the learner's dyadic/quotient/rounding decisions. The
/// contemporary normalization and unresolved factor material stay in Constitution as values;
/// no derivative of that policy or of a never-rounded learner is asserted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContactVariationAction {
    FixedMaterial,
    RealizedFactorTranslation,
}

/// The exact metric operands of one reached family. The opening columns use the native wave
/// coordinates (s,a,u/(hG),w/G,u_R/(hY),w_R/Y); their dual uses the reciprocal units. These are
/// current first-variation readings, not reconstructed energies of a previous passage or a
/// Gauss--Newton Hessian of the historical score. The native factor statistic adds the current
/// feature energy and this declared opening-column squared norm. Its covector ceiling covers
/// the current solved transit RHS and the opening dual's l1 norm in that same chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReachedContactMetric {
    pub contact: usize,
    pub family: Family,
    pub within_word_energy: Rat,
    pub within_word_covector: Rat,
    pub opening_column_power: Rat,
    pub opening_dual_bound: Rat,
}

/// Exact resource admission, supplied before the first passage. Counts concern ratios and
/// column-ticks; the external admission queue also measures CPU, wall and resident memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VariationBudget {
    pub ratios: usize,
    pub bits: u64,
    pub column_ticks: usize,
}

/// A raw producing Gram-factor coordinate. Families 0/1/2 are C/K/D, respectively.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactCoordinate {
    pub contact: usize,
    pub family: usize,
    pub row: usize,
    pub column: usize,
}

/// The actual work/storage read, separate from the unchanged physical energy receipts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariationReading {
    pub parameters: usize,
    pub state_coordinates: usize,
    pub retained_ratios: usize,
    pub retained_bits: u64,
    pub column_ticks: usize,
    pub words: usize,
    pub next_tick: usize,
}

/// One contemporary material identity and its forward differential, with no past Word.
/// The equality operand is solely an identity check, never used to replay a prior trajectory.
/// Its duplicate exact bits are counted. Zero initial columns mean a fixed prospective initial
/// configuration even when the actual current is nonzero; no earlier derivative is asserted.
#[derive(Clone, Debug)]
pub struct HeldContactVariation {
    producing: Constitution,
    references: Vec<Rat>,
    coordinates: Vec<ContactCoordinate>,
    columns: Vec<EndChange>,
    budget: VariationBudget,
    reading: VariationReading,
    action: ContactVariationAction,
}

/// The transient comparison through the held material and actual carried current. Both terms
/// have the ratio-gradient sign; the negative is the descent direction. Only its producing
/// Word can bind the combined covector to a ContactCut. The native proposal/storage gates do
/// not certify finite decrease of the historical comparison that reached this differential.
#[derive(Debug)]
pub struct HeldContactComparison {
    pub producing_commit: u64,
    pub coordinates: Vec<ContactCoordinate>,
    pub ratio: HolonRatio,
    pub pullback: WordReturn,
    pub opening: ChangeCovector,
    pub within_word: Vec<Rat>,
    pub carried: Vec<Rat>,
    pub total: Vec<Rat>,
    pub reading: VariationReading,
    pub metric: Vec<ReachedContactMetric>,
    pub action: ContactVariationAction,
    pub(crate) reaction: Option<(ContactCut, Deposit)>,
}

fn refuse<T>(reason: &'static str) -> Result<T, HnnError> {
    Err(HnnError::Unadmitted { reason })
}

fn values(change: &EndChange) -> impl Iterator<Item = &Rat> {
    change
        .storage
        .iter()
        .chain(change.arrivals.iter().flatten())
        .chain(change.states.iter().flatten())
        .chain(change.resonators.iter().flatten().flatten())
        .flatten()
}

fn factors(theta: &Constitution, a: usize) -> [&ExactRatMatrix; 3] {
    [
        theta.contact_storage(a),
        theta.contact_stiffness(a),
        theta.contact_dissipation(a),
    ]
}

fn admit(ops: &Operands) -> Result<(), HnnError> {
    if ops.lattice().is_some()
        || ops.rings().iter().any(|r| r.chart().is_some())
        || ops.contacts().iter().any(|a| a.chart().is_some())
        || ops
            .resonators()
            .iter()
            .flatten()
            .any(|r| !r.charts().is_empty() || r.material().saturation().is_some())
    {
        return refuse(
            "the held contact variation requires exact unsplit quadratic producing solves",
        );
    }
    Ok(())
}

/// Validate the whole dual topology before pairing; the legacy zip-based pairing alone does
/// not reject truncated storage/arrival/state/loaded arrays.
fn same_shape(dual: &ChangeCovector, column: &EndChange) -> bool {
    let vectors = |a: &[Vec<Rat>], b: &[Vec<Rat>]| {
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.len() == y.len())
    };
    let pairs = |a: &[[Vec<Rat>; 2]], b: &[[Vec<Rat>; 2]]| {
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| vectors(x, y))
    };
    vectors(&dual.storage, &column.storage)
        && pairs(&dual.arrivals, &column.arrivals)
        && pairs(&dual.states, &column.states)
        && dual.resonators.len() == column.resonators.len()
        && dual
            .resonators
            .iter()
            .zip(&column.resonators)
            .all(|(x, y)| match (x, y) {
                (Some(x), Some(y)) => vectors(x, y),
                (None, None) => true,
                _ => false,
            })
}

/// Positive coordinate norm and its dual in the same wave chart used by the native loaded
/// certificate. The discrete pump tags carry the frame; they are not squared state entries.
fn opening_power(ops: &Operands, column: &EndChange) -> Result<Rat, HnnError> {
    let mut power: Rat = column
        .storage
        .iter()
        .flatten()
        .chain(column.arrivals.iter().flatten().flatten())
        .map(|x| x * x)
        .sum();
    for (state, contact) in column.states.iter().zip(ops.contacts()) {
        let scales = [
            ops.step() * contact.conductance(),
            contact.conductance().clone(),
        ];
        for (xs, scale) in state.iter().zip(scales) {
            power += xs.iter().map(|x| (x / &scale) * (x / &scale)).sum::<Rat>();
        }
    }
    for (state, law) in column.resonators.iter().zip(ops.resonators()) {
        if let (Some(state), Some(law)) = (state, law) {
            let scales = [ops.step() * law.admittance(), law.admittance().clone()];
            for (xs, scale) in state.iter().zip(scales) {
                power += xs.iter().map(|x| (x / &scale) * (x / &scale)).sum::<Rat>();
            }
        }
    }
    Ok(power)
}

fn opening_dual_bound(ops: &Operands, dual: &ChangeCovector) -> Rat {
    let mut bound: Rat = dual
        .storage
        .iter()
        .flatten()
        .chain(dual.arrivals.iter().flatten().flatten())
        .map(Signed::abs)
        .sum();
    for (state, contact) in dual.states.iter().zip(ops.contacts()) {
        let scales = [
            ops.step() * contact.conductance(),
            contact.conductance().clone(),
        ];
        for (xs, scale) in state.iter().zip(scales) {
            bound += xs.iter().map(|x| (x * &scale).abs()).sum::<Rat>();
        }
    }
    for (state, law) in dual.resonators.iter().zip(ops.resonators()) {
        if let (Some(state), Some(law)) = (state, law) {
            let scales = [ops.step() * law.admittance(), law.admittance().clone()];
            for (xs, scale) in state.iter().zip(scales) {
                bound += xs.iter().map(|x| (x * &scale).abs()).sum::<Rat>();
            }
        }
    }
    bound
}

impl HeldContactVariation {
    pub(crate) fn begin(
        field: &Field,
        theta: &Constitution,
        current: &Current,
        carry: Option<&ReceptionCarry>,
        budget: VariationBudget,
    ) -> Result<Self, HnnError> {
        let ops = Operands::exact_at_cut(field, theta, current)?;
        admit(&ops)?;
        if (0..field.contacts().len()).any(|a| {
            theta.contact_stiffness_signature(a).is_some()
                || theta.contact_surface_storage(a).is_some()
        }) {
            return refuse("the first held contact variation admits unsigned Gram contacts only");
        }
        let mut coordinates = Vec::new();
        for a in 0..field.contacts().len() {
            if theta.released().contains(&Locus::Channel(a)) {
                continue;
            }
            for (family, factor) in factors(theta, a).into_iter().enumerate() {
                for row in 0..factor.rows() {
                    for column in 0..factor.columns() {
                        coordinates.push(ContactCoordinate {
                            contact: a,
                            family,
                            row,
                            column,
                        });
                    }
                }
            }
        }
        if coordinates.is_empty() {
            return refuse("a held variation has an unreleased contact coordinate");
        }
        let mut zero = EndChange::rest(field, &ops);
        let next_tick = carry.map_or(0, |c| c.ticks);
        if let Some(carry) = carry {
            if !carry.fits(field) {
                return refuse("the held variation begins at the actual full carried shape");
            }
            for (a, contact) in ops.contacts().iter().enumerate() {
                if contact.forms().0.apply(&carry.change.states[a][1])? != carry.momenta[a] {
                    return refuse(
                        "the held variation begins with Cw equal to its actual canonical momentum",
                    );
                }
            }
            for (g, resonator) in ops.resonators().iter().enumerate() {
                match (
                    resonator,
                    &carry.change.resonators[g],
                    &carry.resonator_momenta[g],
                ) {
                    (Some(r), Some([_, w]), Some(pi))
                        if r.material().forms().0.apply(w)? == *pi
                            && carry.change.resonator_phases[g]
                                == Some(r.phase_at(next_tick.saturating_sub(1))) => {}
                    (None, None, None) => {}
                    _ => {
                        return refuse(
                            "the held variation begins with the full matched loaded momentum",
                        );
                    }
                }
            }
            zero.resonator_phases = carry.change.resonator_phases.clone();
        }
        let state_coordinates = values(&zero).count();
        let retained_ratios = state_coordinates
            .checked_mul(coordinates.len())
            .ok_or(HnnError::CountOverflow)?;
        if retained_ratios > budget.ratios {
            return refuse("the held contact variation exceeds its predeclared ratio allocation");
        }
        let references: Vec<_> = ops
            .contacts()
            .iter()
            .map(|a| a.conductance().clone())
            .collect();
        if carry.is_some_and(|c| c.conductances != references) {
            return refuse("the held variation begins in the actual unchanged contact reference");
        }
        let parameters = coordinates.len();
        let mut retained = Self {
            producing: theta.clone(),
            references,
            coordinates,
            columns: vec![zero; parameters],
            budget,
            reading: VariationReading {
                parameters,
                state_coordinates,
                retained_ratios,
                retained_bits: 0,
                column_ticks: 0,
                words: 0,
                next_tick,
            },
            action: ContactVariationAction::FixedMaterial,
        };
        retained.read_bits()?;
        Ok(retained)
    }

    pub fn reading(&self) -> &VariationReading {
        &self.reading
    }
    pub fn coordinates(&self) -> &[ContactCoordinate] {
        &self.coordinates
    }
    pub fn action(&self) -> ContactVariationAction {
        self.action
    }
    pub(crate) fn with_realized_translations(mut self) -> Result<Self, HnnError> {
        self.action = ContactVariationAction::RealizedFactorTranslation;
        self.read_bits()?;
        Ok(self)
    }
    /// Current full-state columns, not a history. Discrete phase tags are the primal tags.
    pub fn columns(&self) -> &[EndChange] {
        &self.columns
    }

    pub(crate) fn matches(&self, theta: &Constitution, carry: &ReceptionCarry) -> bool {
        theta == &self.producing
            && carry.ticks == self.reading.next_tick
            && carry.conductances == self.references
            && self
                .columns
                .iter()
                .all(|chi| chi.resonator_phases == carry.change.resonator_phases)
    }

    pub(crate) fn admit_ticks(&self, ticks: usize) -> Result<(), HnnError> {
        let count = ticks
            .checked_mul(self.coordinates.len())
            .and_then(|n| n.checked_add(self.reading.column_ticks))
            .ok_or(HnnError::CountOverflow)?;
        if count > self.budget.column_ticks {
            return refuse("the held variation exceeds its predeclared column-tick domain");
        }
        Ok(())
    }

    fn read_bits(&mut self) -> Result<(), HnnError> {
        let mut bits = self.producing.exact_bits();
        for value in self.columns.iter().flat_map(values).chain(&self.references) {
            bits = bits
                .checked_add(value.numer().bits())
                .and_then(|n| n.checked_add(value.denom().bits()))
                .ok_or(HnnError::CountOverflow)?;
        }
        // Numerical metadata as exact integer readings; heap capacity/allocations remain
        // a separate measured peak resident set, not inferred from this bit count.
        for value in self
            .columns
            .iter()
            .flat_map(|chi| chi.resonator_phases.iter().flatten())
            .copied()
            .chain(
                self.coordinates
                    .iter()
                    .flat_map(|c| [c.contact, c.family, c.row, c.column]),
            )
            .chain([
                self.reading.parameters,
                self.reading.state_coordinates,
                self.reading.retained_ratios,
                self.reading.column_ticks,
                self.reading.words,
                self.reading.next_tick,
                match self.action {
                    ContactVariationAction::FixedMaterial => 0,
                    ContactVariationAction::RealizedFactorTranslation => 1,
                },
            ])
        {
            bits = bits
                .checked_add(u64::from(usize::BITS - value.leading_zeros()))
                .ok_or(HnnError::CountOverflow)?;
        }
        self.reading.retained_bits = bits;
        if bits > self.budget.bits {
            return refuse("the held contact variation exceeded its fixed exact-bit budget");
        }
        Ok(())
    }

    /// At the same material/reference the momentum identity dπ=dC w+C dw makes crossing
    /// identity on dw, including a compatible singular C. Then the source clamp replaces
    /// source storage: Pi_int chi, with dI_source=0 for these contact-only coordinates.
    pub(crate) fn opened(&self, word: &Word<'_>) -> Result<Vec<EndChange>, HnnError> {
        let (theta, _, _, _) = word.native_source.as_ref().ok_or(HnnError::Unadmitted {
            reason: "a held material differential consumes the actual native source producer",
        })?;
        admit(word.operands())?;
        if theta != &self.producing
            || word.opened_at() != self.reading.next_tick
            || word
                .operands()
                .contacts()
                .iter()
                .map(|a| a.conductance())
                .ne(self.references.iter())
            || word.is_ended()
            || word.fields.len() != word.ticks()
        {
            return refuse(
                "the continuing variation keeps its exact material, reference, clock and complete-tick domain",
            );
        }
        let mut columns: Vec<_> = self
            .columns
            .iter()
            .cloned()
            .map(|chi| interior_of(word.field, chi))
            .collect();
        for chi in &mut columns {
            for (g, resonator) in word.operands.resonators().iter().enumerate() {
                if let Some(resonator) = resonator {
                    let phase = resonator.phase_at(word.opened_at.saturating_sub(1));
                    if chi.resonator_phases[g] != Some(phase) {
                        return refuse(
                            "the carried first variation keeps the actual previous pump phase",
                        );
                    }
                }
            }
        }
        Ok(columns)
    }

    /// Advance columns through this Word's recorded producing ticks. All primal states and
    /// midpoints come from this Word; this is no second simulation of the physical passage.
    pub(crate) fn advanced(&self, word: &Word<'_>, opened: &[EndChange]) -> Result<Self, HnnError> {
        let count = word
            .ticks()
            .checked_mul(self.coordinates.len())
            .ok_or(HnnError::CountOverflow)?;
        let column_ticks = self
            .reading
            .column_ticks
            .checked_add(count)
            .ok_or(HnnError::CountOverflow)?;
        if column_ticks > self.budget.column_ticks {
            return refuse("the held contact variation exceeds its fixed column-tick budget");
        }
        let mut next = self.clone();
        next.columns = opened.to_vec();
        next.reading.column_ticks = column_ticks;
        next.reading.words = next
            .reading
            .words
            .checked_add(1)
            .ok_or(HnnError::CountOverflow)?;
        next.reading.next_tick = word
            .opened_at()
            .checked_add(word.ticks())
            .ok_or(HnnError::CountOverflow)?;
        for t in 0..word.ticks() {
            for (coordinate, chi) in next.coordinates.iter().zip(&mut next.columns) {
                *chi = word.contact_first_variation(t, chi, coordinate, &next.producing)?;
            }
            next.read_bits()?;
        }
        next.read_bits()?;
        Ok(next)
    }
}

impl Word<'_> {
    fn contact_first_variation(
        &self,
        t: usize,
        chi: &EndChange,
        coordinate: &ContactCoordinate,
        theta: &Constitution,
    ) -> Result<EndChange, HnnError> {
        let ops = &self.operands;
        let record = &self.passage[t];
        // Reuse the existing full signed tick used by physical completion; no second
        // homogeneous state engine. The reached material forcing has only this contact's
        // u/w and arrival slots at this tick; later signed ticks carry it to every ring.
        let mut next = crate::hnn::prediction::physical_signed_tick(ops, chi, self.opened_at + t)?;
        let a = coordinate.contact;
        let contact = &ops.contacts()[a];
        let (from, to) = contact.ends();
        let width = contact.width();
        let factor = factors(theta, a)[coordinate.family];
        let mut direction = vec![vec![Rat::zero(); factor.columns()]; factor.rows()];
        direction[coordinate.row][coordinate.column] = integer(1);
        let direction = ExactRatMatrix::shaped(factor.rows(), factor.columns(), direction)?;
        let mut forms = [
            ExactRatMatrix::zero(width, width)?,
            ExactRatMatrix::zero(width, width)?,
            ExactRatMatrix::zero(width, width)?,
        ];
        forms[coordinate.family] = direction
            .multiply(&factor.transpose()?)?
            .add(&factor.multiply(&direction.transpose()?)?)?;
        let zero_from = vec![Rat::zero(); ops.rings()[from].width()];
        let zero_to = vec![Rat::zero(); ops.rings()[to].width()];
        let zero_state = vec![Rat::zero(); width];
        let forced = transit_variation(
            contact,
            ops.step(),
            &zero_from,
            &zero_to,
            &zero_state,
            &zero_state,
            &record.states[a][0],
            &record.states[a][1],
            &record.rates[a],
            &forms,
        )?;
        next.arrivals[a] = [
            add(&next.arrivals[a][0], &forced.arrive_from),
            add(&next.arrivals[a][1], &forced.arrive_to),
        ];
        next.states[a] = [
            add(&next.states[a][0], &forced.displacement),
            add(&next.states[a][1], &forced.rate),
        ];
        Ok(next)
    }

    pub(crate) fn compare_contacts_held(
        self,
        receiver: usize,
        targets: &crate::hnn::encoding::Encoded,
        compared: &[bool],
        held: &HeldContactVariation,
        opened: &[EndChange],
        reading: VariationReading,
    ) -> Result<HeldContactComparison, HnnError> {
        let (theta, current, source, support) = self
            .native_source
            .as_ref()
            .ok_or(HnnError::Unadmitted {
                reason: "a held comparison consumes its actual source-bound Word",
            })?
            .clone();
        if theta != held.producing || opened.len() != held.coordinates.len() {
            return refuse(
                "the held comparison and every column keep their producing material identity",
            );
        }
        let field = self.field;
        let cut = self.contact_cut()?;
        let ops = self.operands.clone();
        let (phases, faces) = self.contact_receiving(receiver)?;
        let ratio = HolonRatio::compare_partition(
            faces,
            &targets.classes_read().collect::<Vec<_>>(),
            &target_phases(field, current.lift(), phases.ring(), targets)?,
            compared,
        )?;
        let (back, opening) = self.pull_back_full(
            &ratio.covector()?,
            theta
                .receiving_map(phases.ring())
                .ok_or(HnnError::Unadmitted {
                    reason: "the held comparison has its producing receiving map",
                })?,
            &current.lift()[phases.ring()],
            &phases,
        )?;
        if opened.iter().any(|chi| !same_shape(&opening, chi)) {
            return refuse(
                "the complete held opening covector and tangent have equal topology and shape",
            );
        }
        let diamond = Diamond::opened(field, &phases, &support);
        let contact_returns = (0..field.contacts().len())
            .map(|a| {
                crate::hnn::reference::compose_contact(
                    field,
                    &theta,
                    &back,
                    &diamond,
                    &|locus| diamond.retains(field, locus),
                    current.lift(),
                    field.step(),
                    a,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let within_word = held
            .coordinates
            .iter()
            .map(|coordinate| {
                let pull = &contact_returns[coordinate.contact].1;
                let form = [&pull.storage, &pull.stiffness, &pull.dissipation][coordinate.family];
                Ok(form.get(coordinate.row, coordinate.column)?.clone())
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let carried: Vec<_> = opened.iter().map(|chi| opening.pairing(chi)).collect();
        let total: Vec<Rat> = within_word
            .iter()
            .zip(&carried)
            .map(|(a, b)| a + b)
            .collect();
        let dual_bound = opening_dual_bound(&ops, &opening);
        let mut metric = Vec::new();
        let mut steps = Vec::new();
        let mut loci = diamond.retained(field);
        for (a, (current_steps, _)) in contact_returns.iter().enumerate() {
            if theta.released().contains(&Locus::Channel(a)) {
                continue;
            }
            for (family, factor) in factors(&theta, a).into_iter().enumerate() {
                let family_tag = crate::hnn::constitution::Family::Factor(family);
                let now = current_steps
                    .iter()
                    .find(|s| s.gradient.family() == family_tag);
                let mut descent = vec![vec![Rat::zero(); factor.columns()]; factor.rows()];
                let mut column_power = Rat::zero();
                for (i, coordinate) in held.coordinates.iter().enumerate() {
                    if coordinate.contact == a && coordinate.family == family {
                        descent[coordinate.row][coordinate.column] = -total[i].clone();
                        column_power += opening_power(&ops, &opened[i])?;
                    }
                }
                let energy = now.map_or_else(Rat::zero, |s| s.energy.clone());
                let covector = now.map_or_else(Rat::zero, |s| s.covector.clone());
                let reading = ReachedContactMetric {
                    contact: a,
                    family: family_tag,
                    within_word_energy: energy.clone(),
                    within_word_covector: covector.clone(),
                    opening_column_power: column_power.clone(),
                    opening_dual_bound: dual_bound.clone(),
                };
                // This declared positive material metric normalizes the reached combined
                // covector. It is not an estimate of missing historical feature energies.
                if descent.iter().flatten().any(|x| !x.is_zero()) && !ratio.stations().is_empty() {
                    let gradient =
                        ExactRatMatrix::shaped(factor.rows(), factor.columns(), descent)?;
                    let gradient = match family {
                        0 => FactorGradient::Storage {
                            contact: a,
                            gradient,
                        },
                        1 => FactorGradient::Stiffness {
                            contact: a,
                            gradient,
                        },
                        _ => FactorGradient::Dissipation {
                            contact: a,
                            gradient,
                        },
                    };
                    steps.push(FactorStep {
                        gradient,
                        energy: energy + column_power,
                        covector: covector + &dual_bound,
                    });
                    loci.insert(Locus::Channel(a));
                }
                metric.push(reading);
            }
        }
        let reaction = if held.action == ContactVariationAction::RealizedFactorTranslation
            && !steps.is_empty()
        {
            let occupied = field
                .sources()
                .iter()
                .map(|&g| {
                    let mut n = 0u64;
                    for class in 0..field.ring(g).placements().len() {
                        if source.phase_counts(g, class)?.iter().any(|x| *x != 0) {
                            n = n.checked_add(1).ok_or(HnnError::CountOverflow)?;
                        }
                    }
                    Ok(n)
                })
                .collect::<Result<Vec<_>, HnnError>>()?
                .into_iter()
                .max()
                .unwrap_or(0);
            let reached = steps.iter().map(|s| s.gradient.locus()).collect();
            let deposit = Deposit::new(theta.commit(), vec![], steps, reached).with_reach(Reach {
                receiver: phases.ring(),
                stations: ratio
                    .stations()
                    .iter()
                    .map(|&j| (phases.first_epoch() + j) as u64)
                    .collect(),
                entries: vec![0],
                phases: occupied,
                loci,
            });
            Some((cut.bind_comparison(deposit.clone()), deposit))
        } else {
            None
        };
        Ok(HeldContactComparison {
            producing_commit: theta.commit(),
            coordinates: held.coordinates.clone(),
            ratio,
            pullback: back,
            opening,
            within_word,
            carried,
            total,
            reading,
            metric,
            action: held.action,
            reaction,
        })
    }
}
