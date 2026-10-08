//! The held contact material's first variation through two continuing full Words (Refs #73 #62).
//!
//! [agent-inferred] Recover the local tangent equations in `hnn/tests/port`, using the existing
//! junction, element, loaded solve and contact variation owners. The retained columns are
//! `EndChange`, not Words or source occurrences. For a later observed ratio the ordinary native
//! contact consumer reads `g = g_this_word + J_open^* mu_open`. This is a differential at one
//! material point, not a Deposit: updating that point requires its held-state/update/rebase jet.

use super::*;
use crate::hnn::constitution::{Constitution, Locus};
use crate::hnn::field::ConstitutionRead;
use crate::hnn::port::{ChangeCovector, WordReturn};
use crate::hnn::propagation::transit_variation;
use crate::hnn::ratio::{HolonRatio, target_phases};
use crate::hnn::retention::Diamond;

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
}

/// The transient comparison through the held material and actual carried current. Both terms
/// have the ratio-gradient sign; the negative is the descent direction. This type deliberately
/// has no Deposit conversion or certified finite-step field.
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
        if self.reading.words >= 2 || count > self.budget.column_ticks {
            return refuse(
                "the held variation exceeds its two-Word or predeclared column-tick domain",
            );
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
            || self.reading.words >= 2
        {
            return refuse(
                "the two-Word variation keeps its exact material, reference, clock and complete-tick domain",
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
        next.reading.words += 1;
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
        let mut direction = ExactRatMatrix::zero(factor.rows(), factor.columns())?;
        direction.set(coordinate.row, coordinate.column, integer(1))?;
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
        let (theta, current, _, support) = self
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
        let pulls = (0..field.contacts().len())
            .map(|a| {
                crate::hnn::reference::compose_contact(
                    field,
                    &theta,
                    &back,
                    &diamond,
                    &|_| false,
                    current.lift(),
                    field.step(),
                    a,
                )
                .map(|(_, pull)| pull)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let within_word = held
            .coordinates
            .iter()
            .map(|coordinate| {
                let pull = &pulls[coordinate.contact];
                let form = [&pull.storage, &pull.stiffness, &pull.dissipation][coordinate.family];
                Ok(form.get(coordinate.row, coordinate.column)?.clone())
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let carried: Vec<_> = opened.iter().map(|chi| opening.pairing(chi)).collect();
        let total = within_word
            .iter()
            .zip(&carried)
            .map(|(a, b)| a + b)
            .collect();
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
        })
    }
}
