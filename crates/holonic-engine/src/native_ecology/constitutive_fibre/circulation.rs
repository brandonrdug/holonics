//! Actual two-port phase circulation joined to the developing local constitutive relation.
//! The caller supplies an incoming current and, when one exists, an owned prior emission handle.
//! The carried source is produced by native incidence and retained on-device; no caller supplies
//! a training source/target pair. A handle proves the native source occurrence and its exact
//! carrying section, not arbitrary assertions about an exterior's constitutive law.

use super::*;

mod rechart;
pub(super) mod rest;
use crate::dimensional_wave::ExactComplexWaveCurrent;
pub(super) use rechart::HeldCurrentFrame;
pub use rechart::{NativeCurrentFrame, NativeIncidenceChange, NativeRechartReceipt};
pub use rest::NativeEcologyRest;
use serde::Deserialize;
use std::rc::Rc;

/// One exact local phase pair. The denominator is positive; this is an apparatus chart, not an ID.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "PhaseRestWire")]
pub struct NativePhaseCurrent {
    real: i64,
    imaginary: i64,
    denominator: i64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PhaseRestWire {
    real: i64,
    imaginary: i64,
    denominator: i64,
}
impl TryFrom<PhaseRestWire> for NativePhaseCurrent {
    type Error = ConstitutiveFibreError;
    fn try_from(wire: PhaseRestWire) -> Result<Self, Self::Error> {
        Self::new(wire.real, wire.imaginary, wire.denominator)
    }
}

impl NativePhaseCurrent {
    /// Exact apparatus-mouth conversion. No midpoint or floating-point approximation is used.
    pub fn from_current(current: &ExactComplexWaveCurrent) -> Result<Self, ConstitutiveFibreError> {
        use num_traits::{ToPrimitive, Zero};
        let mut a = current.real.denom().clone();
        let mut b = current.imaginary.denom().clone();
        while !b.is_zero() {
            let r = &a % &b;
            a = b;
            b = r;
        }
        let denominator = current.real.denom() / a * current.imaginary.denom();
        let real = (current.real.numer() * (&denominator / current.real.denom()))
            .to_i64()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let imaginary = (current.imaginary.numer() * (&denominator / current.imaginary.denom()))
            .to_i64()
            .ok_or(ConstitutiveFibreError::Shape)?;
        Self::new(
            real,
            imaginary,
            denominator.to_i64().ok_or(ConstitutiveFibreError::Shape)?,
        )
    }
    pub fn new(
        real: i64,
        imaginary: i64,
        denominator: i64,
    ) -> Result<Self, ConstitutiveFibreError> {
        if denominator <= 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        fn gcd(mut a: u64, mut b: u64) -> u64 {
            while b != 0 {
                let r = a % b;
                a = b;
                b = r;
            }
            a
        }
        let divisor = gcd(
            gcd(real.unsigned_abs(), imaginary.unsigned_abs()),
            denominator as u64,
        ) as i128;
        Ok(Self {
            real: (real as i128 / divisor) as i64,
            imaginary: (imaginary as i128 / divisor) as i64,
            denominator: (denominator as i128 / divisor) as i64,
        })
    }

    pub fn zero() -> Self {
        Self {
            real: 0,
            imaginary: 0,
            denominator: 1,
        }
    }
    pub fn unit() -> Self {
        Self {
            real: 1,
            imaginary: 0,
            denominator: 1,
        }
    }
    pub fn current(self) -> ExactComplexWaveCurrent {
        ExactComplexWaveCurrent::new(
            Rat::new(self.real.into(), self.denominator.into()),
            Rat::new(self.imaginary.into(), self.denominator.into()),
        )
    }
    pub(in crate::native_ecology::constitutive_fibre) fn words(self) -> [i64; 3] {
        [self.real, self.imaginary, self.denominator]
    }
    pub(in crate::native_ecology::constitutive_fibre) fn is_unit(self) -> bool {
        (self.real as i128 * self.real as i128)
            .checked_add(self.imaginary as i128 * self.imaginary as i128)
            == Some(self.denominator as i128 * self.denominator as i128)
    }
}

/// Declared constitutive seed, not learned task coefficients. Every node has an incoming and a
/// retained-wave port; the incoming edge carries this exact unit-phase change of local chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeJunctionSeed {
    pub incoming_admittance: i64,
    pub held_admittance: i64,
    pub incoming_transport: NativePhaseCurrent,
    pub initial_held: NativePhaseCurrent,
}

impl NativeJunctionSeed {
    pub fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        if self.incoming_admittance <= 0
            || self.held_admittance <= 0
            || !self.incoming_transport.is_unit()
        {
            Err(ConstitutiveFibreError::Shape)
        } else {
            Ok(())
        }
    }
}

/// A linear handle to one actual emitted source section. It cannot be constructed from an event
/// number, copied for multiple returns, or used against another ecology with equal coordinate data.
#[derive(Debug)]
pub struct NativeEmissionHandle {
    owner: Rc<()>,
    occurrence: usize,
}

#[derive(Debug)]
pub struct NativeCurrentOccurrence {
    current: NativePhaseCurrent,
    source: Option<NativeEmissionHandle>,
}

impl NativeCurrentOccurrence {
    /// Recover an unconsumed source after refusal. Successful reception has already consumed it.
    pub fn take_source(&mut self) -> Option<NativeEmissionHandle> {
        self.source.take()
    }
    pub fn entering(current: NativePhaseCurrent) -> Self {
        Self {
            current,
            source: None,
        }
    }
    pub fn through(source: NativeEmissionHandle, current: NativePhaseCurrent) -> Self {
        Self {
            current,
            source: Some(source),
        }
    }
    pub fn current(&self) -> NativePhaseCurrent {
        self.current
    }
}

/// Boundary maps for the actual incoming/held incidence population in an operation. Each node's
/// two incidences read this incoming occurrence and the named prior native state, respectively.
/// The optional receiving edge joins the exact carried emission, not the immediately prior text.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCurrentLineage {
    pub occurrence: usize,
    /// A position in this body's chart history, not a source identity or a global frame key.
    pub frame: u64,
    pub predecessor_state: Option<usize>,
    pub received_from: Option<usize>,
    pub incoming: NativePhaseCurrent,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeCurrentCarrier {
    Incoming { occurrence: usize },
    Held { after: Option<usize>, node: usize },
    Emitted { occurrence: usize, node: usize },
}

/// An actual boundary in this owning ecology. Equal coordinate positions in two independently
/// founded bodies do not compare equal: the occurrence scope remains part of both boundary maps.
#[derive(Clone, Debug)]
pub struct NativeCurrentBoundary {
    owner: Rc<()>,
    pub position: NativeCurrentCarrier,
    frame: Option<Rc<NativeCurrentFrame>>,
}

impl PartialEq for NativeCurrentBoundary {
    fn eq(&self, other: &Self) -> bool {
        self.same_carrier(other)
            && match (&self.frame, &other.frame) {
                (None, None) => true,
                (Some(a), Some(b)) => Rc::ptr_eq(a, b),
                _ => false,
            }
    }
}
impl Eq for NativeCurrentBoundary {}

impl NativeCurrentBoundary {
    fn same_carrier(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.owner, &other.owner) && self.position == other.position
    }
    pub fn frame(&self) -> Option<&NativeCurrentFrame> {
        self.frame.as_deref()
    }
    fn transport_into(&self, other: &Self) -> ExactComplexWaveCurrent {
        let node = match self.position {
            NativeCurrentCarrier::Held { node, .. }
            | NativeCurrentCarrier::Emitted { node, .. } => node,
            NativeCurrentCarrier::Incoming { .. } => return NativePhaseCurrent::unit().current(),
        };
        let unit = NativePhaseCurrent::unit();
        let first = self
            .frame
            .as_ref()
            .map_or(unit, |f| f.root_to_local[node])
            .current();
        let second = other
            .frame
            .as_ref()
            .map_or(unit, |f| f.root_to_local[node])
            .current();
        second.multiply(&first.conjugate())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeCurrentIncidence {
    pub occurrence: usize,
    pub node: usize,
    pub source: NativeCurrentBoundary,
    pub target: NativeCurrentBoundary,
    /// Exact complex linear transport in the declared seed chart. A zero transported current
    /// does not erase the carrying occurrence from this population.
    pub transport: ExactComplexWaveCurrent,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeJoinedCurrentIncidence {
    pub first: NativeCurrentIncidence,
    pub second: NativeCurrentIncidence,
    /// The admitted middle-frame passage, not an equality of raw coordinate faces.
    pub middle_transport: ExactComplexWaveCurrent,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct NativeReceivedCurrentDifference {
    pub source_occurrence: usize,
    pub former_receiver_fibre: ConstitutiveReading,
    pub arrived: ExactComplexWaveCurrent,
}

#[derive(Debug)]
pub struct NativeCurrentStep {
    pub source: NativeEmissionHandle,
    pub lineage: NativeCurrentLineage,
    pub frame: Rc<NativeCurrentFrame>,
    /// Ordered in this return's local node frame, not a later value of `material()`. These coordinates are
    /// not interchangeable with another body's or a later recharted field without its transport.
    pub source_currents: Vec<ExactComplexWaveCurrent>,
    pub receiver: ConstitutiveReading,
    pub received_difference: Option<NativeReceivedCurrentDifference>,
    pub formed_pivot: Option<usize>,
    pub successor_rank: usize,
}

impl NativeCurrentStep {
    /// Exterior codec projection to the stable boundary chart. It does not execute or alter the
    /// learner; the device has already enacted its complete current and successor.
    pub fn root_source_currents(&self) -> Vec<ExactComplexWaveCurrent> {
        self.source_currents
            .iter()
            .zip(&self.frame.root_to_local)
            .map(|(current, gauge)| gauge.current().conjugate().multiply(current))
            .collect()
    }
}

struct HeldEmission<'chart> {
    section: ResidentSection<'chart>,
    lineage: NativeCurrentLineage,
    returned: bool,
    frame: Rc<HeldCurrentFrame<'chart>>,
    material: Rc<[NativeJunctionSeed]>,
}

/// One continuing ecology: versioned incidence/constitution, held phase, developing relation,
/// and its occurrence-bearing emitted sources. Neither the ecology nor its device state is Clone.
/// The held source sections serve only actual receiving edges, never answer lookup for a query.
pub struct NativeConstitutiveEcology<'chart> {
    seed: ResidentSection<'chart>,
    memory: ResidentSection<'chart>,
    relation: ResidentConstitutiveFibre<'chart>,
    material: Rc<[NativeJunctionSeed]>,
    frame: Rc<HeldCurrentFrame<'chart>>,
    recharts: Vec<NativeRechartReceipt>,
    incidence_changes: Vec<NativeIncidenceChange>,
    owner: Rc<()>,
    history: Vec<HeldEmission<'chart>>,
    pending: Option<HeldEmission<'chart>>,
}

impl<'chart> NativeConstitutiveEcology<'chart> {
    pub fn found(
        surface: &'chart ResidentSurface<'chart>,
        material: Vec<NativeJunctionSeed>,
    ) -> Result<Self, ConstitutiveFibreError> {
        let nodes = material.len();
        let scratch = nodes
            .checked_mul(12)
            .and_then(|n| n.checked_add(6))
            .and_then(|n| n.checked_mul(16))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let available = surface.declaration().max_sectiond_bytes;
        if nodes == 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        for seed in &material {
            seed.validate()?;
        }
        if scratch > available as usize {
            return Err(ConstitutiveFibreError::ScratchAperture {
                required: scratch,
                available,
            });
        }
        let relation = ResidentConstitutiveFibre::found(surface, 2 * nodes, 2)?;
        let mut seed_words = Vec::with_capacity(nodes * 5);
        let mut memory_words = Vec::with_capacity(nodes * 3);
        for node in &material {
            seed_words.extend([
                node.incoming_admittance,
                node.held_admittance,
                node.incoming_transport.real,
                node.incoming_transport.imaginary,
                node.incoming_transport.denominator,
            ]);
            memory_words.extend(node.initial_held.words());
        }
        let mount = |width, words: Vec<i64>| -> Result<_, ConstitutiveFibreError> {
            let rest = ResidentSectionRest::found(
                nodes,
                width,
                ResidentGrain(0),
                64,
                words.into_iter().map(|v| (v, v)).collect(),
            )
            .map_err(|_| ConstitutiveFibreError::Shape)?;
            Ok(surface.mount_section_rest(&rest)?)
        };
        Ok(Self {
            seed: mount(5, seed_words)?,
            memory: mount(3, memory_words)?,
            relation,
            material: material.into(),
            frame: Rc::new(HeldCurrentFrame {
                native: mount(3, (0..nodes).flat_map(|_| [1, 0, 1]).collect())?,
                view: Rc::new(NativeCurrentFrame {
                    ordinal: 0,
                    root_to_local: vec![NativePhaseCurrent::unit(); nodes],
                }),
            }),
            recharts: Vec::new(),
            incidence_changes: Vec::new(),
            owner: Rc::new(()),
            history: Vec::new(),
            pending: None,
        })
    }

    pub fn material(&self) -> &[NativeJunctionSeed] {
        &self.material
    }
    pub fn occurrence_count(&self) -> usize {
        self.history.len()
    }
    pub fn material_at(&self, occurrence: usize) -> Option<&[NativeJunctionSeed]> {
        self.history.get(occurrence).map(|h| h.material.as_ref())
    }
    pub fn current_frame(&self) -> &NativeCurrentFrame {
        &self.frame.view
    }
    pub fn lineage(&self) -> impl Iterator<Item = &NativeCurrentLineage> {
        self.history.iter().map(|e| &e.lineage)
    }

    /// Read the four actual incidence terms of each executed two-port junction. This is a
    /// reconstruction view of the seeded law, never a CPU step in native current or formation.
    pub fn incidence(
        &self,
        occurrence: usize,
    ) -> Result<Vec<NativeCurrentIncidence>, ConstitutiveFibreError> {
        let history = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let boundary = |position| NativeCurrentBoundary {
            owner: Rc::clone(&self.owner),
            frame: if matches!(position, NativeCurrentCarrier::Incoming { .. }) {
                None
            } else {
                Some(Rc::clone(&history.frame.view))
            },
            position,
        };
        let mut result = Vec::with_capacity(4 * self.material.len());
        for (node, seed) in history.material.iter().enumerate() {
            let a = Rat::from_integer(seed.incoming_admittance.into());
            let b = Rat::from_integer(seed.held_admittance.into());
            let sum = &a + &b;
            let two = Rat::from_integer(2.into());
            let incoming = boundary(NativeCurrentCarrier::Incoming { occurrence });
            let held = boundary(NativeCurrentCarrier::Held {
                after: history.lineage.predecessor_state,
                node,
            });
            let emitted = boundary(NativeCurrentCarrier::Emitted { occurrence, node });
            let successor = boundary(NativeCurrentCarrier::Held {
                after: Some(occurrence),
                node,
            });
            let rotation = seed.incoming_transport.current();
            let unit = NativePhaseCurrent::unit().current();
            for (source, target, transport) in [
                (
                    incoming.clone(),
                    emitted.clone(),
                    rotation.scaled(&((&a - &b) / &sum)),
                ),
                (held.clone(), emitted, unit.scaled(&(&two * &b / &sum))),
                (
                    incoming,
                    successor.clone(),
                    rotation.scaled(&(&two * &a / &sum)),
                ),
                (held, successor, unit.scaled(&((&b - &a) / &sum))),
            ] {
                result.push(NativeCurrentIncidence {
                    occurrence,
                    node,
                    source,
                    target,
                    transport,
                });
            }
        }
        Ok(result)
    }

    /// The full joining occurrence population, not merely the endpoint relation. The same
    /// held-state carrier and node are joined through their explicit middle-frame transport;
    /// different coordinate presentations are not asserted equal.
    pub fn joined_incidence(
        &self,
        first: usize,
        second: usize,
    ) -> Result<Vec<NativeJoinedCurrentIncidence>, ConstitutiveFibreError> {
        let left = self.incidence(first)?;
        let right = self.incidence(second)?;
        Ok(left
            .into_iter()
            .flat_map(|a| {
                right.iter().filter_map(move |b| {
                    a.target
                        .same_carrier(&b.source)
                        .then(|| NativeJoinedCurrentIncidence {
                            middle_transport: a.target.transport_into(&b.source),
                            first: a.clone(),
                            second: b.clone(),
                        })
                })
            })
            .collect())
    }
    pub fn pending_lineage(&self) -> Option<&NativeCurrentLineage> {
        self.pending.as_ref().map(|e| &e.lineage)
    }
    pub fn census(&self) -> TransferCensus {
        self.relation.census()
    }
    pub fn inspect_relation(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        self.relation.inspect_relation()
    }
    pub fn inspect_held(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        Ok(self.relation.surface.detach_section(&self.memory, 64)?)
    }

    /// One incoming occurrence enacts phase current, actual receiving comparison, local formation,
    /// receiver reading and successor together. The source handle is consumed only on success;
    /// arithmetic refusal leaves it with the caller. Driver uncertainty preserves the pending
    /// occurrence and prevents a silent retry against possibly changed device state.
    pub fn advance(
        &mut self,
        occurrence: &mut NativeCurrentOccurrence,
    ) -> Result<NativeCurrentStep, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let source_at = if let Some(source) = &occurrence.source {
            if !Rc::ptr_eq(&source.owner, &self.owner)
                || self
                    .history
                    .get(source.occurrence)
                    .is_none_or(|h| h.returned)
            {
                return Err(ConstitutiveFibreError::ForeignOccurrence);
            }
            Some(source.occurrence)
        } else {
            None
        };
        let at = self.history.len();
        let next = self
            .relation
            .occurrences
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        self.history
            .try_reserve(1)
            .map_err(|_| ConstitutiveFibreError::Shape)?;
        let lineage = NativeCurrentLineage {
            occurrence: at,
            frame: self.frame.view.ordinal,
            predecessor_state: at.checked_sub(1),
            received_from: source_at,
            incoming: occurrence.current,
        };
        let surface = self.relation.surface;
        let input = surface.mount_section_rest(
            &ResidentSectionRest::found(
                1,
                3,
                ResidentGrain(0),
                64,
                occurrence
                    .current
                    .words()
                    .into_iter()
                    .map(|v| (v, v))
                    .collect(),
            )
            .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let output = surface.fresh_section(1, 6 * self.material.len() + 13, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_constitutive_circulation(
                &lane,
                &self.seed,
                &mut self.memory,
                &mut self.relation.basis,
                &input,
                source_at.map(|i| &self.history[i].section),
                &self.frame.native,
                source_at.map(|i| &self.history[i].frame.native),
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let passage = passage.finish()?;
        self.pending = Some(HeldEmission {
            section: output,
            lineage: lineage.clone(),
            returned: false,
            frame: Rc::clone(&self.frame),
            material: Rc::clone(&self.material),
        });
        self.relation.usable = false;
        let reading = passage.launch()?;
        if !reading.obstruction.is_empty() {
            self.pending = None;
            self.relation.usable = true;
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "{:?}",
                reading.obstruction
            )));
        }
        let words = surface.read_out(&self.pending.as_ref().expect("pending operation").section)?;
        let source_width = self.relation.source_width;
        let width = source_width + 2;
        if words.iter().any(|(l, h)| l != h) || words[source_width].0 <= 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let current_at = source_width + 1;
        let former_at = current_at + width + 4;
        let formed_pivot = match words[current_at + width + 2].0 {
            -1 => None,
            p if p >= 0 && (p as usize) < width => Some(p as usize),
            _ => return Err(ConstitutiveFibreError::Uncertain),
        };
        let rank = usize::try_from(words[current_at + width + 3].0)
            .map_err(|_| ConstitutiveFibreError::Uncertain)?;
        if rank > width {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let receiver = self.relation.decode_reading(&words, current_at, None)?;
        let received_difference = source_at
            .map(|source_occurrence| -> Result<_, ConstitutiveFibreError> {
                Ok(NativeReceivedCurrentDifference {
                    source_occurrence,
                    former_receiver_fibre: self.relation.decode_reading(
                        &words,
                        former_at,
                        formed_pivot,
                    )?,
                    arrived: occurrence.current.current(),
                })
            })
            .transpose()?;
        let denominator = words[source_width].0;
        let source_currents = (0..self.material.len())
            .map(|i| {
                ExactComplexWaveCurrent::new(
                    Rat::new(words[2 * i].0.into(), denominator.into()),
                    Rat::new(words[2 * i + 1].0.into(), denominator.into()),
                )
            })
            .collect();
        if let Some(i) = source_at {
            self.history[i].returned = true;
        }
        occurrence.source = None;
        self.history
            .push(self.pending.take().expect("completed operation"));
        self.relation.occurrences = next;
        self.relation.usable = true;
        Ok(NativeCurrentStep {
            source: NativeEmissionHandle {
                owner: Rc::clone(&self.owner),
                occurrence: at,
            },
            lineage,
            frame: Rc::clone(&self.frame.view),
            source_currents,
            receiver,
            received_difference,
            formed_pivot,
            successor_rank: rank,
        })
    }
}

#[cfg(test)]
mod tests;
