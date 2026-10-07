//! Charted physical reception with a source, state and comparison error consumer (Refs #73 #62).
//!
//! [agent-inferred] The exact comparison is the *same* sparse source/chart and declared initial
//! carry on the contemporary linear physical constitution. The source's population chart is an
//! operand of that law. It is not an unrounded historic constitution or an erasure completion.
//! Each native chart has ||X-Xhat||_inf <= ||Xhat||_inf delta/(1-delta). The native signed tick
//! supplies its center; the exact weights, material relations and inverse bounds supply its
//! coordinate radius. The actual Word supplies every measured split difference. Thus
//! e_(t+1) <= |Phi| e_t + error(Phi) + |xhat_(t+1)-Phihat(xhat_t)| at opened_at+t.
//! Energy residuals are never substituted for these state or covector bounds.
//!
//! Only R is published. Its actual move is checked against both operands' errors and the local
//! receiving curvature, after the existing normal law proposes it. Rounded E/pair publication
//! is still unsupported. Erasures remain Held: this numerical sparse-source certificate is not
//! the missing-source completion certificate. No source, Word or response columns survive the
//! immediate comparison; the resident retains Theta, frame, charts, carry and its current box.

use super::*;
use crate::hnn::chart::{ChartReading, Charts, Remainders};
use crate::hnn::constitution::{Constitution, LinearLocus, Locus, Reach};
use crate::hnn::field::ReceiverDeclaration;
use crate::hnn::port::{Deposit, WordReturn};
use crate::hnn::propagation::{Junction, Operands};
use crate::hnn::ratio::{Faces, HolonRatio, RatioCovector, target_phases};
use crate::hnn::receiving::{DeclaringFace, ReceivingRead};
use crate::hnn::retention::Diamond;
use crate::hnn::word::{Absorption, ChartedSourceOpeningReceipt, EndChange};
use crate::holon::deposition::JointReading;
use crate::ratio::exponentiated::CarriedPower;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, scale, sub};

mod linear_radius;
use linear_radius::ContactRadiusMaps;

/// Component tolerances in the declared receiving/source charts. None is an iteration budget.
#[derive(Clone, Debug)]
pub struct ChartedTolerance {
    pub logits: Rat,
    pub receiving_covector: Rat,
    pub source_covector: Rat,
}

impl ChartedTolerance {
    fn admit(&self) -> Result<(), HnnError> {
        if [&self.logits, &self.receiving_covector, &self.source_covector].iter()
            .any(|x| **x < Rat::zero()) {
            return Err(HnnError::Unadmitted { reason: "a charted comparison tolerance is negative" });
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct ChartedStationError {
    pub station: usize,
    pub tick: usize,
    pub anchor: Vec<Rat>,
    pub logits: Vec<Rat>,
}

/// Error against the exact sparse source reception, on its same declared entered motion.
#[derive(Clone, Debug)]
pub struct ChartedErrorReceipt {
    pub opening: ChartedSourceOpeningReceipt,
    /// Producing chart selection/refinement readings; these are not retained response columns.
    pub charts: Vec<ChartReading>,
    pub initial: EndChange,
    pub end: EndChange,
    pub stations: Vec<ChartedStationError>,
}

#[derive(Clone, Debug)]
pub struct ChartedPhysicalRepair {
    /// Whole actual output and physical carry. Its source work closes with `error.opening.split`.
    pub physical: PhysicalRepair,
    pub error: ChartedErrorReceipt,
}

impl ChartedPhysicalRepair {
    /// Close the actual source opening, Word and every executed tick with their stated work.
    /// `after - before + split = imposed - absorbed`: projecting onto `physical.opening`
    /// alone omits the signed opening split and is the exact-only law when `split = 0`.
    /// The two copies of the producing source receipt and the Word's opening must agree;
    /// coordinate error radii never stand in for any of these power identities (Refs #73 #62).
    pub fn closes(&self) -> bool {
        self.error.opening.source == self.physical.opening
            && self.error.opening.closes()
            && self.physical.opening.after
                == &self.physical.word.open + &self.physical.word.resonator_open
            && self.physical.word.closes()
            && self.physical.balances.iter().all(|balance| balance.closes())
    }
}

/// Both covector operands and the actual applied receiving move, independently of normal proposals.
#[derive(Debug)]
pub struct ChartedComparisonReceipt {
    pub logit_covectors: Vec<Vec<Rat>>,
    pub receiving_covector: ExactRatMatrix,
    /// The actual producing opening return; `source_covectors` encloses declared source rings.
    pub source_opening: Vec<Vec<Rat>>,
    pub source_covectors: Vec<Vec<Rat>>,
    pub source_rounding: Vec<Vec<Rat>>,
    pub return_remainders: Remainders,
    pub applied: JointReading,
    pub alignment_error: Rat,
    pub tolerance: ChartedTolerance,
}

#[derive(Debug)]
pub struct ChartedPhysicalPublication {
    pub teaching: PhysicalTeaching,
    pub error: ChartedComparisonReceipt,
}

#[derive(Debug)]
pub struct ChartedPhysicalReception {
    pub prediction: ChartedPhysicalRepair,
    pub comparison: Result<Option<ChartedPhysicalPublication>, HnnError>,
    /// Equal declaring inputs reused their face; actual point/error/comparison reads are fresh.
    pub declaring_face_reused: bool,
}

/// The one actual blind Word, borrowed material and error box awaiting an immediate comparison.
pub struct ChartedPhysicalPrediction<'f, 'm> {
    pending: PhysicalPrediction<'f, 'm>,
    error: ChartedErrorReceipt,
}

impl ChartedPhysicalPrediction<'_, '_> {
    pub fn prediction(&self) -> &PhysicalRepair { self.pending.prediction() }
    pub fn error(&self) -> &ChartedErrorReceipt { &self.error }

    pub fn finish(self) -> ChartedPhysicalRepair {
        ChartedPhysicalRepair { physical: self.pending.finish(), error: self.error }
    }

    /// The target enters only here, after the actual blind source/clock/phase reception.
    pub fn observe(
        self,
        contemporary: &Constitution,
        observed: &Encoded,
        compared: &[bool],
        tolerance: &ChartedTolerance,
    ) -> Result<ChartedPhysicalPublication, (ChartedPhysicalRepair, HnnError)> {
        let Self { pending, error } = self;
        let PhysicalPrediction { field, material, current, phases, chart, opening_support,
            source, word, prediction } = pending;
        let joined = (|| -> Result<_, HnnError> {
            tolerance.admit()?;
            if material.commit() != contemporary.commit() || material != contemporary {
                return Err(HnnError::Unadmitted { reason: "the charted return's producing material changed" });
            }
            if observed.part(0..0)? != chart || observed.len() != phases.aperture()
                || compared.len() != phases.aperture() || prediction.reads.len() != phases.aperture()
                || !compared.iter().any(|x| *x) || !field.is_source(phases.ring()) || phases.first_epoch() != 0 {
                return Err(HnnError::Unadmitted { reason: "the charted observation has a foreign chart, partition or station clock" });
            }
            let reads: Vec<_> = prediction.reads.iter().map(|x| x.read.clone()).collect();
            let targets: Vec<_> = observed.classes_read().collect();
            let ratio = HolonRatio::compare_partition(Faces::of_reads(&reads, phases.grain())?,
                &targets, &target_phases(field, current.lift(), phases.ring(), observed)?, compared)?;
            let covector = ratio.covector()?;
            let g_error = comparison_error(&reads, &error.stations, &targets, compared, phases.grain())?;
            let operands = word.operands().clone();
            let opened_at = word.opened_at();
            let map = material.receiving_map(phases.ring()).ok_or(HnnError::MissingReceivingMap { ring: phases.ring() })?;
            let back = word.pull_back(&covector, map, &current.lift()[phases.ring()], &phases)?;
            let (source_error, source_rounding) = source_return_error(field, material, &current,
                &phases, &operands, opened_at, &covector, &g_error, &back)?;
            let gradient_error = receiving_error(field, &current, &phases, &back,
                &error.stations, &covector, &g_error, compared)?;
            if error.stations.iter().zip(compared).any(|(e, crossed)| *crossed && sup(&e.logits) > tolerance.logits)
                || gradient_error.entries().iter().any(|e| *e > tolerance.receiving_covector)
                || source_error.iter().flatten().any(|e| *e > tolerance.source_covector) {
                return Err(HnnError::Unadmitted { reason: "the source or receiving covector exceeds its declared charted tolerance" });
            }
            let diamond = Diamond::opened(field, &phases, &opening_support);
            let composed = crate::hnn::reference::compose_return(field, material, &diamond,
                current.lift(), &current, &source, &back)?;
            let mut linear: Vec<_> = composed.linear.into_iter()
                .filter(|step| step.locus == LinearLocus::Receiving(phases.ring())).collect();
            for step in &mut linear {
                if step.samples.len() != compared.len() {
                    return Err(HnnError::Unadmitted { reason: "the charted receiving samples have another comparison partition" });
                }
                step.samples = std::mem::take(&mut step.samples).into_iter().zip(compared)
                    .filter_map(|(sample, crossed)| crossed.then_some(sample)).collect();
            }
            if linear.is_empty() { return Err(HnnError::Unadmitted { reason: "the charted comparison reaches no receiving relation" }); }
            let reached = vec![Locus::ReceivingMap(phases.ring())];
            let deposit = Deposit::new(material.commit(), linear, Vec::new(), reached.clone()).with_reach(Reach {
                receiver: phases.ring(), stations: phases.epochs().zip(compared)
                    .filter_map(|(tick, crossed)| crossed.then_some(tick as u64)).collect(),
                entries: vec![0], phases: composed.phases, loci: reached.into_iter().collect(),
            });
            let feature_energy = deposit.linear().iter().map(|step| (step.locus.locus(),
                step.samples.iter().map(|s| &s.weight * dot(&s.feature, &s.feature)).sum())).collect();
            let (constitution, publication) = contemporary.deposited(&deposit)?;
            if !same_interior(field, material, &constitution) {
                return Err(HnnError::Unadmitted { reason: "a charted receiving successor changes the carried physical law" });
            }
            let delta = constitution.receiving_map(phases.ring())
                .ok_or(HnnError::MissingReceivingMap { ring: phases.ring() })?.subtract(map)?;
            let alignment_error = matrix_pairing_radius(&gradient_error, &delta)?;
            let (mut alignment, mut moves) = (Rat::zero(), Rat::zero());
            for (j, crossed) in compared.iter().enumerate().filter(|(_, x)| **x) {
                let _ = crossed;
                let feature = &back.reads[j].0;
                let moved = delta.apply(feature)?;
                alignment -= dot(&covector.logits()[j], &moved);
                let radius = matrix_radius(&delta, &transport_radius(field, &current, phases.ring(), &error.stations[j].anchor))?;
                moves += moved.iter().zip(radius).map(|(x, r)| (x.abs()+r).pow(2)).sum::<Rat>();
            }
            let applied = JointReading { curvature: &moves / crate::ratio::integer(2), decrease: alignment - &alignment_error };
            if applied.decrease <= Rat::zero() || !applied.holds() {
                return Err(HnnError::Unadmitted { reason: "the actual receiving move fails after source and covector error are charged" });
            }
            Ok((ratio, composed.pullback, constitution, publication, feature_energy,
                ChartedComparisonReceipt { logit_covectors: g_error, receiving_covector: gradient_error,
                    source_opening: back.opening,
                    source_covectors: source_error, source_rounding, return_remainders: back.released,
                    applied, alignment_error, tolerance: tolerance.clone() }))
        })();
        match joined {
            Ok((ratio, pullback, constitution, publication, feature_energy, comparison)) => Ok(ChartedPhysicalPublication {
                teaching: PhysicalTeaching { prediction, ratio, pullback, constitution, publication,
                    feature_energy, source_certificate: None, source_pairing: None }, error: comparison }),
            Err(reason) => Err((ChartedPhysicalRepair { physical: prediction, error }, reason)),
        }
    }
}

/// A resident of the actual physical field and its present error box. R-only publication keeps
/// every carry-crossing material/reference fixed, so this box crosses by the identity; imposed
/// source storage is replaced. A caller-supplied first opening is a declared exact initial state.
pub struct ChartedPhysicalResident<'f> {
    field: &'f Field,
    constitution: Constitution,
    current: Current,
    opening: WordOpening,
    bound: Option<EndChange>,
    charts: Charts,
    chart: Option<Encoded>,
    tolerance: ChartedTolerance,
    declaring: DeclaringFace<'f>,
}

impl<'f> ChartedPhysicalResident<'f> {
    pub fn new(field: &'f Field, constitution: Constitution, current: Current,
        opening: WordOpening, tolerance: ChartedTolerance) -> Result<Self, HnnError> {
        tolerance.admit()?;
        if field.word_lattice().is_none() {
            return Err(HnnError::Unadmitted { reason: "the charted physical resident has no declared Word lattice" });
        }
        Ok(Self { field, constitution, current, opening, bound: None,
            charts: Charts::new(), chart: None, tolerance, declaring: DeclaringFace::new(field) })
    }
    pub fn constitution(&self) -> &Constitution { &self.constitution }
    pub fn opening(&self) -> &WordOpening { &self.opening }
    pub fn carry_error(&self) -> Option<&EndChange> { self.bound.as_ref() }
    pub fn charts(&self) -> &Charts { &self.charts }

    pub fn receive(&mut self, section: &DamagedSection, receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalRepair) -> Option<(Encoded, Vec<bool>)>,
    ) -> Result<ChartedPhysicalReception, HnnError> {
        if self.chart.as_ref().is_some_and(|chart| chart != section.chart()) {
            return Err(HnnError::Unadmitted { reason: "the charted resident's producing source chart changed" });
        }
        let (phases, declaring_face_reused) = self.declaring.declare(&self.constitution, &self.current, receiver)?;
        let mut charts = self.charts.clone();
        let pending = predict(self.field, &self.constitution, &self.current, section,
            &self.opening, self.bound.as_ref(), &phases, &mut charts)?;
        let forward_error = pending.error.clone();
        let (prediction, comparison, successor) = match observation(pending.prediction()) {
            None => (pending.finish(), Ok(None), None),
            Some((observed, compared)) => match pending.observe(&self.constitution, &observed, &compared, &self.tolerance) {
                Ok(publication) => {
                    let successor = publication.teaching.constitution.clone();
                    let prediction = ChartedPhysicalRepair { physical: publication.teaching.prediction.clone(), error: forward_error };
                    (prediction, Ok(Some(publication)), Some(successor))
                }
                Err((prediction, error)) => (prediction, Err(error), None),
            },
        };
        if let Some(successor) = successor { self.constitution = successor; }
        self.opening = WordOpening::Received { carry: prediction.physical.carry.clone(), absorption: Absorption::Nothing };
        self.bound = Some(prediction.error.end.clone());
        self.chart = Some(section.chart().clone());
        self.charts = charts;
        Ok(ChartedPhysicalReception { prediction, comparison, declaring_face_reused })
    }
}

fn predict<'f, 'm>(field: &'f Field, material: &'m Constitution, current: &Current,
    section: &DamagedSection, opening: &WordOpening, carried: Option<&EndChange>,
    phases: &ReceivingPhases, charts: &mut Charts,
) -> Result<ChartedPhysicalPrediction<'f, 'm>, HnnError> {
    section.admit(field, material, phases)?;
    let placed = section.placed();
    let mut source = SourceMoment::open_with(field, current, material)?;
    for &g in field.sources() { source = source.station_section(field, current, g, &placed)?; }
    let (mut word, receipt) = Word::open_charted_received(field, material, current, &source, charts, opening)?;
    let operands = word.operands().clone();
    let mut radius_maps = ContactRadiusMaps::new(&operands);
    if operands.resonators().iter().flatten().any(|r| r.material().saturation().is_some()) {
        return Err(HnnError::Unadmitted { reason: "a charted physical comparison needs its nonlinear Word-Hessian error join" });
    }
    let mut radius = receipt.error.clone();
    if matches!(opening, WordOpening::Received { absorption: Absorption::Nothing, .. }) {
        if let Some(carried) = carried {
            let mut interior = carried.clone();
            for &g in field.sources() { interior.storage[g].fill(Rat::zero()); }
            join_change(&mut radius, &interior, |a,b| a+b);
        }
    }
    let initial = radius.clone();
    let opened_at = word.opened_at();
    let mut errors = Vec::new();
    let mut carried_point = None;
    for crossing in 0..phases.junction_steps() {
        let point = word.change()?;
        let centers = physical_signed_junctions(&operands, &point)?;
        let junctions = junction_error(&operands, &point, &radius)?;
        if crossing+1 == phases.junction_steps() {
            // reception_end restores this pre-scatter crossing; emitted coordinates belong
            // to released().end. Bind the retained radius to its actual consuming state.
            carried_point = Some(point);
            word.last_junction()?;
        }
        else {
            let signed = physical_signed_tick(&operands, &point, opened_at+crossing)?;
            let mut next = tick_error_cached(&mut radius_maps, &point, &radius, opened_at+crossing)?;
            word.tick()?;
            let actual = word.change()?;
            let mut split = actual;
            join_change(&mut split, &signed, |a,b| (a-b).abs());
            join_change(&mut next, &split, |a,b| a+b);
            radius = next;
        }
        if phases.epochs().contains(&crossing) {
            let ring = phases.ring();
            let actual = word.anchor(crossing, ring).ok_or(HnnError::WordEnded { ticks: word.ticks() })?;
            let anchor = junctions[ring].anchor.iter().zip(actual.iter().zip(&centers[ring].anchor))
                .map(|(e,(a,c))| e+(a-c).abs()).collect::<Vec<_>>();
            let logits = matrix_radius(material.receiving_map(ring).ok_or(HnnError::MissingReceivingMap { ring })?,
                &transport_radius(field, current, ring, &anchor))?;
            errors.push(ChartedStationError { station: errors.len(), tick: opened_at+crossing, anchor, logits });
        }
    }
    let reads = phases.epochs().enumerate().map(|(station, crossing)| Ok(StationRead {
        station, crossing, tick: opened_at+crossing,
        read: phases.read(field, material, current, word.anchor(crossing, phases.ring())
            .ok_or(HnnError::WordEnded { ticks: word.ticks() })?)?,
    })).collect::<Result<Vec<_>, HnnError>>()?;
    let carry = word.reception_end()?;
    if carried_point.as_ref() != Some(&carry.change) {
        return Err(HnnError::Unadmitted { reason: "the charted carry and its error box have different producing crossings" });
    }
    if carry.ticks != opened_at+phases.last_epoch() || errors.len() != phases.aperture()
        || word.clock().ticks() != num_bigint::BigUint::from(carry.ticks+1) {
        return Err(HnnError::Unadmitted { reason: "the charted physical receiving clock did not execute its declared crossings" });
    }
    let cells = placed.iter().map(|x| match x {
        Some(c) => RepairedCell::Intact(*c),
        None => RepairedCell::Held { fibre: domain_classes(section), unresolved: Unresolved::UncertifiedDomain },
    }).collect();
    let prediction = PhysicalRepair { cells, reads, domains: vec![None; phases.aperture()],
        opening: receipt.source.clone(), balances: word.field_balances().to_vec(),
        word: WordBalance::of(&word.released()?), carry };
    Ok(ChartedPhysicalPrediction { pending: PhysicalPrediction { field, material, current: current.clone(),
        phases: phases.clone(), chart: section.chart().clone(), opening_support: opening.support(field),
        source, word, prediction }, error: ChartedErrorReceipt { opening: receipt, charts: operands.charts(), initial, end: radius, stations: errors } })
}

fn sup(x: &[Rat]) -> Rat { x.iter().map(|x| x.abs()).max().unwrap_or_else(Rat::zero) }
fn matrix_radius(m: &ExactRatMatrix, e: &[Rat]) -> Result<Vec<Rat>, HnnError> { physical_matrix_radius(m,e) }
fn transport_radius(field: &Field, current: &Current, ring: usize, e: &[Rat]) -> Vec<Rat> {
    field.ring(ring).rotate(e, &current.lift()[ring]).into_iter().map(|e| e.abs()).collect()
}

/// A radius and a point share their native shape, phase and field identity, from this producer.
fn join_change(a: &mut EndChange, b: &EndChange, op: impl Fn(&Rat,&Rat)->Rat) {
    let join = |a: &mut Vec<Rat>, b: &Vec<Rat>| {
        for (a,b) in a.iter_mut().zip(b) { *a=op(a,b); }
    };
    for (a,b) in a.storage.iter_mut().zip(&b.storage) { join(a,b); }
    for (a,b) in a.arrivals.iter_mut().zip(&b.arrivals) { for k in 0..2 { join(&mut a[k], &b[k]); } }
    for (a,b) in a.states.iter_mut().zip(&b.states) { for k in 0..2 { join(&mut a[k], &b[k]); } }
    for (a,b) in a.resonators.iter_mut().zip(&b.resonators) {
        if let (Some(a),Some(b))=(a,b) { for k in 0..2 { join(&mut a[k], &b[k]); } }
    }
}

fn row_norm(m: &ExactRatMatrix) -> Rat {
    (0..m.rows()).map(|i| m.row(i).expect("a native row").iter()
        .map(|x| x.abs()).sum()).max().unwrap_or_else(Rat::zero)
}

/// Existing inverse-chart deviation, with no exact inverse or unrounded counterfactual solve.
fn solve_error(x: &ExactRatMatrix, delta: Rat, point: &[Rat], error: &[Rat]) -> Result<Vec<Rat>,HnnError> {
    if delta < Rat::zero() || delta >= Rat::one() {
        return Err(HnnError::Unadmitted { reason: "a producing inverse chart has no deviation regime" });
    }
    let defect = row_norm(x) * &delta / (Rat::one()-delta) * (sup(point)+sup(error));
    Ok(matrix_radius(x,error)?.into_iter().map(|e| e+&defect).collect())
}

fn junction_error(o: &Operands, point: &EndChange, error: &EndChange) -> Result<Vec<Junction>,HnnError> {
    (0..o.rings().len()).map(|g| {
        let points: Vec<_> = std::iter::once(point.storage[g].as_slice()).chain(o.incident(g).iter()
            .map(|&a| point.arrivals[a][o.end_slot(a,g)].as_slice())).collect();
        let errors: Vec<_> = std::iter::once(error.storage[g].as_slice()).chain(o.incident(g).iter()
            .map(|&a| error.arrivals[a][o.end_slot(a,g)].as_slice())).collect();
        let radius = |multiplier: Rat, port: Option<usize>| {
            (0..o.rings()[g].width()).map(|i| {
                o.exact_weights(g).iter().zip(o.weights(g)).enumerate().map(|(p,(exact,charted))| {
                    let coefficient = &multiplier*exact - if port==Some(p) { Rat::one() } else { Rat::zero() };
                    coefficient.abs()*&errors[p][i] + (&multiplier*(exact-charted)).abs()*points[p][i].abs()
                }).sum()
            }).collect::<Vec<Rat>>()
        };
        Ok(Junction { anchor: radius(Rat::one(),None), storage_wave: radius(crate::ratio::integer(2),Some(0)),
            contrast: radius(Rat::one(),Some(0)), outgoing: (1..points.len())
                .map(|p| radius(crate::ratio::integer(2),Some(p))).collect() })
    }).collect()
}

#[cfg(test)]
fn tick_error(o: &Operands, point: &EndChange, error: &EndChange, tick: usize) -> Result<EndChange,HnnError> {
    tick_error_cached(&mut ContactRadiusMaps::new(o), point, error, tick)
}

fn tick_error_cached(maps: &mut ContactRadiusMaps<'_>, point: &EndChange, error: &EndChange, tick: usize) -> Result<EndChange,HnnError> {
    let o = maps.operands;
    let centers = physical_signed_junctions(o,point)?;
    let bounds = junction_error(o,point,error)?;
    let mut next = error.clone();
    let h=o.step();
    for (g,ring) in o.rings().iter().enumerate() {
        let c=&centers[g]; let e=&bounds[g];
        let right=add(&scale(&crate::ratio::integer(2),&c.storage_wave), &ring.contrast().apply(&c.contrast)?);
        let right_error=add(&scale(&crate::ratio::integer(2),&e.storage_wave), &matrix_radius(ring.contrast(),&e.contrast)?);
        let drive_error=add(&solve_error(&ring.solve()?,ring.chart().map_or_else(Rat::zero,|c|c.certificate.clone()),
            &right,&right_error)?, &e.storage_wave);
        let Some(r)=&o.resonators()[g] else { next.storage[g]=drive_error; continue };
        let drive=crate::hnn::propagation::element_step(ring,&c.storage_wave,&c.contrast)?.next;
        let state=point.resonators[g].as_ref().ok_or(HnnError::Unadmitted { reason: "the error tube lost its producing resonator state" })?;
        let re=error.resonators[g].as_ref().ok_or(HnnError::Unadmitted { reason: "the error tube lost its resonator radius" })?;
        let phase=r.phase_at(tick); let (capacity,_,_)=r.material().forms();
        let right=sub(&add(&scale(&crate::ratio::integer(2),&capacity.apply(&state[1])?), &scale(h,&drive)),
            &scale(h,&r.stiffness(phase).apply(&state[0])?));
        let right_error=add(&add(&scale(&crate::ratio::integer(2),&matrix_radius(capacity,&re[1])?), &scale(&h.abs(),&drive_error)),
            &scale(&h.abs(),&matrix_radius(r.stiffness(phase),&re[0])?));
        let n=r.width();
        let columns=(0..n).map(|i| { let mut basis=vec![Rat::zero();n]; basis[i]=Rat::one();r.solve(phase,&basis) })
            .collect::<Result<Vec<_>,_>>()?;
        let solve=ExactRatMatrix::shaped(n,n,(0..n).map(|i|columns.iter().map(|c|c[i].clone()).collect()).collect())?;
        let rate=solve_error(&solve,r.certificate(phase),&right,&right_error)?;
        next.storage[g]=add(&drive_error,&scale(&(crate::ratio::integer(2)/r.admittance()),&rate));
        next.resonators[g]=Some([add(&re[0],&scale(&h.abs(),&rate)),
            add(&scale(&crate::ratio::integer(2),&rate),&re[1])]);
        next.resonator_phases[g]=Some(phase);
    }
    for (a,c) in o.contacts().iter().enumerate() {
        let (from,to)=c.ends();
        let point_inputs=[outgoing(o,&centers,from,a),outgoing(o,&centers,to,a),point.states[a][0].as_slice(),point.states[a][1].as_slice()];
        let inputs=[outgoing(o,&bounds,from,a),outgoing(o,&bounds,to,a),error.states[a][0].as_slice(),error.states[a][1].as_slice()];
        let right=crate::hnn::propagation::transit_solve(c,h,point_inputs[0],point_inputs[1],point_inputs[2],point_inputs[3])?.0;
        let re=maps.right(a,&inputs)?;
        let solved=solve_error(&c.solve()?,c.chart().map_or_else(Rat::zero,|c|c.certificate.clone()),&right,&re)?;
        let n0=inputs[0].len();let n1=inputs[1].len();let n=c.width();
        let inputs=[solved.as_slice(),inputs[0],inputs[1],inputs[2],inputs[3]];
        let image=maps.update(a,&inputs)?;
        next.arrivals[a]=[image[..n0].to_vec(),image[n0..n0+n1].to_vec()];
        next.states[a]=[image[n0+n1..n0+n1+n].to_vec(),image[n0+n1+n..].to_vec()];
    }
    Ok(next)
}

fn outgoing<'a>(o:&Operands,j:&'a [Junction],g:usize,a:usize)->&'a [Rat] {
    &j[g].outgoing[o.incident(g).iter().position(|&i|i==a).expect("an incident native contact")]
}

fn comparison_error(reads: &[ReceivingRead], errors: &[ChartedStationError], targets: &[usize], compared: &[bool], grain: u64)
    -> Result<Vec<Vec<Rat>>,HnnError> {
    reads.iter().zip(errors).enumerate().map(|(j,(read,e))| {
        let mut radius=vec![Rat::zero();read.logits.len()];
        if !compared[j] { return Ok(radius) }
        let classes=read.cells.len();
        let lower: Vec<_>=(0..classes).map(|c|crate::receiver::face::GrainCell::of(&(&read.logits[2*c]-&e.logits[2*c]),grain)).collect();
        let upper: Vec<_>=(0..classes).map(|c|crate::receiver::face::GrainCell::of(&(&read.logits[2*c]+&e.logits[2*c]),grain)).collect();
        if lower.iter().zip(&upper).any(|(l,u)|(l.carry.clone(),l.phase)!=(u.carry.clone(),u.phase)) {
            let top=upper.iter().map(|c|c.carry.clone()).max().unwrap();
            let weight=|c:&crate::receiver::face::GrainCell|->Result<Rat,HnnError> {
                Ok(CarriedPower::new(&c.carry-&top,c.phase,grain)?.odometer()?)
            };
            let lo=lower.iter().map(&weight).collect::<Result<Vec<_>,_>>()?;
            let hi=upper.iter().map(&weight).collect::<Result<Vec<_>,_>>()?;
            let masses=crate::hnn::ratio::Face::of_read(read,grain)?.odometer_masses()?;
            for c in 0..classes {
                let lower=&lo[c]/(&lo[c]+hi.iter().enumerate().filter(|(d,_)|*d!=c).map(|(_,w)|w).sum::<Rat>());
                let upper=&hi[c]/(&hi[c]+lo.iter().enumerate().filter(|(d,_)|*d!=c).map(|(_,w)|w).sum::<Rat>());
                radius[2*c]=(&masses[c]-lower).abs().max((upper-&masses[c]).abs());
            }
        }
        radius[2*targets[j]+1]=&e.logits[2*targets[j]+1]/crate::ratio::integer(4);
        Ok(radius)
    }).collect()
}

// The actual paired return supplies R's phase-rotated normal features. No receiving inverse or
// authored feature is substituted, and the transient back is dropped after composition.
fn receiving_error(field:&Field,current:&Current,phases:&ReceivingPhases,back:&WordReturn,
    errors:&[ChartedStationError],g:&RatioCovector,ge:&[Vec<Rat>],compared:&[bool])->Result<ExactRatMatrix,HnnError> {
    let n=field.ring(phases.ring()).width();let rows=2*field.alphabet();
    let mut bound=vec![vec![Rat::zero();n];rows];
    for j in (0..compared.len()).filter(|&j|compared[j]) {
        let feature=&back.reads[j].0;
        let fe=transport_radius(field,current,phases.ring(),&errors[j].anchor);
        for r in 0..rows {for c in 0..n {
            bound[r][c]+=g.logits()[j][r].abs()*&fe[c]+&ge[j][r]*feature[c].abs()+&ge[j][r]*&fe[c];
        }}
    }
    Ok(ExactRatMatrix::shaped(rows,n,bound)?)
}

fn source_return_error(field:&Field,material:&Constitution,current:&Current,phases:&ReceivingPhases,
    operands:&Operands,opened_at:usize,g:&RatioCovector,ge:&[Vec<Rat>],back:&WordReturn)
    ->Result<(Vec<Vec<Rat>>,Vec<Vec<Rat>>),HnnError> {
    // [agent-inferred] These columns are the unsplit linear response of the producing
    // charts, not transient hardware Words. Re-represent the SAME Xhat and weights as exact
    // integer rows before their rational coordinates outgrow the i64 input carrier. No inverse,
    // refinement, certificate, tolerance or actual forward/adjoint operand is replaced.
    let linear = operands.clone().unsplit()?;
    source_return_error_on(field,material,current,phases,&linear,opened_at,g,ge,back)
}

fn source_return_error_on(field:&Field,material:&Constitution,current:&Current,phases:&ReceivingPhases,
    operands:&Operands,opened_at:usize,g:&RatioCovector,ge:&[Vec<Rat>],back:&WordReturn)
    ->Result<(Vec<Vec<Rat>>,Vec<Vec<Rat>>),HnnError> {
    let mut error:Vec<_>=field.rings().iter().map(|r|vec![Rat::zero();r.width()]).collect();
    let mut rounding=error.clone();
    let mut radius_maps = ContactRadiusMaps::new(operands);
    for &ring in field.sources() {for coordinate in 0..field.ring(ring).width() {
        let mut point=EndChange::rest(field,operands);point.storage[ring][coordinate]=Rat::one();
        let mut radius=EndChange::rest(field,operands);
        let (mut paired,mut bound)=(Rat::zero(),Rat::zero());
        for crossing in 0..phases.junction_steps() {
            let centers=physical_signed_junctions(operands,&point)?;
            let errors=junction_error(operands,&point,&radius)?;
            if crossing>=phases.first_epoch() && crossing<=phases.last_epoch() {
                let j=crossing-phases.first_epoch();
                let logits=phases.read(field,material,current,&centers[phases.ring()].anchor)?.logits;
                let le=matrix_radius(material.receiving_map(phases.ring()).ok_or(HnnError::MissingReceivingMap {ring:phases.ring()})?,
                    &transport_radius(field,current,phases.ring(),&errors[phases.ring()].anchor))?;
                paired+=dot(&g.logits()[j],&logits);
                bound+=logits.iter().zip(le).zip(g.logits()[j].iter().zip(&ge[j]))
                    .map(|((l,e),(g,ge))|&e*g.abs()+(l.abs()+e)*ge).sum::<Rat>();
            }
            if crossing+1<phases.junction_steps() {
                radius=tick_error_cached(&mut radius_maps,&point,&radius,opened_at+crossing)?;
                point=physical_signed_tick(operands,&point,opened_at+crossing)?;
            }
        }
        rounding[ring][coordinate]=(&back.opening[ring][coordinate]-paired).abs();
        error[ring][coordinate]=bound+&rounding[ring][coordinate];
    }}
    Ok((error,rounding))
}

fn matrix_pairing_radius(error:&ExactRatMatrix,delta:&ExactRatMatrix)->Result<Rat,HnnError> {
    Ok(error.entries().iter().zip(delta.entries()).map(|(e,d)|e*d.abs()).sum())
}

fn same_interior(field:&Field,a:&Constitution,b:&Constitution)->bool {
    field.rings().iter().enumerate().all(|(g,_)| {
        a.standing(g)==b.standing(g) && a.passive_factor(g)==b.passive_factor(g)
        && a.contrast_port(g)==b.contrast_port(g) && a.slices(g)==b.slices(g)
        && a.source_port(g)==b.source_port(g) && a.ring_resonator(g)==b.ring_resonator(g)
        && a.transport(g)==b.transport(g) && field.offsets().iter().all(|&d|a.pair_port(g,d)==b.pair_port(g,d))
    }) && field.contacts().iter().enumerate().all(|(a_index,_)| {
        a.contact_storage(a_index)==b.contact_storage(a_index) && a.contact_stiffness(a_index)==b.contact_stiffness(a_index)
        && a.contact_dissipation(a_index)==b.contact_dissipation(a_index)
        && a.contact_stiffness_signature(a_index)==b.contact_stiffness_signature(a_index)
        && a.contact_surface_storage(a_index)==b.contact_surface_storage(a_index)
    })
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::compression::landmark::context::{BaseMeasure, StopPrior};
    use crate::geometry::RatVec3;
    use crate::geometry::screw::ScrewGenerator;
    use crate::hnn::chart::ChartStart;
    use crate::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    use crate::hnn::field::{ContactDeclaration, CribDeclaration, FieldDeclaration, RingDeclaration};
    use crate::holarchy::terrain::{CyclicLaw, KnownTruth};
    use crate::ratio::linear::vector::integral;
    use crate::ratio::{integer, rat};
    use num_traits::ToPrimitive;

    // Exact operands of the refused matched first comparison, not a new source family.
    fn matched_field() -> Field {
        let ring = |lock| RingDeclaration {
            period: 4,
            screw: ScrewGenerator::new(RatVec3::from_i64(0,0,1), RatVec3::zero()),
            placements: (0..4).map(|node| FieldDeclaration::quarter_turn(node,4)).collect(),
            lock, reflector: vec![0,3,2,1], admittance: integer(2), initial: 0,
        };
        let contact = |from,to| ContactDeclaration {
            from, to, channel: (0..4).map(|node|(node,node)).collect(),
            admittance: integer(2), exponent: Rat::zero(),
        };
        Field::declare(FieldDeclaration {
            rings: vec![ring((0..4).collect()),ring(Vec::new()),ring(Vec::new())],
            contacts: vec![contact(0,1),contact(1,2)], loops: Vec::new(), sources: vec![0],
            offsets: vec![1,2,3], alphabet: 4, step: integer(1), exponent_grain: 1,
            receivers: vec![ReceiverDeclaration { ring:0, aperture:3, tolerance:rat(1,16),
                depth:1, prior:StopPrior::half(), mass:1, base:BaseMeasure::Even, receiving_prior:0 }],
            crib: CribDeclaration { window:16, offset:1 }, population:1<<16, lattice:Default::default(),
        }.by_lattice_rule()).unwrap()
    }

    // Trace the first refused transit of the SAME response-column loop. The right side is read
    // through the producing chart's exact values, so its numerator/denominator survives refusal.
    fn refused_response_operand(field:&Field, phases:&ReceivingPhases, operands:&Operands, opened_at:usize) {
        let linear=operands.clone().unsplit().unwrap();
        for &source in field.sources() { for coordinate in 0..field.ring(source).width() {
            let mut point=EndChange::rest(field,operands);point.storage[source][coordinate]=Rat::one();
            let mut radius=EndChange::rest(field,operands);
            for crossing in 0..phases.junction_steps()-1 {
                let (error,stage)=match tick_error(operands,&point,&radius,opened_at+crossing) {
                    Ok(next)=> {
                        radius=next;
                        match physical_signed_tick(operands,&point,opened_at+crossing) {
                            Ok(next)=>{point=next;continue},
                            Err(error)=>(error,"signed response tick"),
                        }
                    }
                    Err(error)=>(error,"response radius"),
                };
                assert!(matches!(error,HnnError::Carrier { what:"an operand's coordinate beyond the 64-bit word" }));
                let centers=physical_signed_junctions(operands,&point).unwrap();
                if stage=="signed response tick" {
                    for (r,ring) in operands.rings().iter().enumerate() {
                        let c=&centers[r];
                        let right=add(&scale(&integer(2),&c.storage_wave),&ring.contrast().apply(&c.contrast).unwrap());
                        let (numerators,denominator)=integral(&right);
                        if numerators.iter().any(|n|n.to_i64().is_none()) {
                            let refused=crate::hnn::propagation::element_step(ring,&c.storage_wave,&c.contrast);
                            assert!(matches!(refused,Err(HnnError::Carrier { what:"an operand's coordinate beyond the 64-bit word" })));
                            println!("old response refused: stage={stage}; source_ring={source}; coordinate={coordinate}; absolute_tick={}; ring={r}; exact_right={right:?}; integral_numerators={numerators:?}; positive_denominator={denominator}; magnitude_bits={:?}",
                                opened_at+crossing,numerators.iter().map(|n|n.bits()).collect::<Vec<_>>());
                            return;
                        }
                    }
                }
                for (a,contact) in operands.contacts().iter().enumerate() {
                    let (from,to)=contact.ends();
                    let args=[outgoing(operands,&centers,from,a),outgoing(operands,&centers,to,a),
                        point.states[a][0].as_slice(),point.states[a][1].as_slice()];
                    let (right,image)=crate::hnn::propagation::transit_solve(&linear.contacts()[a],
                        linear.step(),args[0],args[1],args[2],args[3]).unwrap();
                    let (numerators,denominator)=integral(&right);
                    if numerators.iter().any(|n|n.to_i64().is_none()) {
                        let refused=crate::hnn::propagation::transit_solve(contact,operands.step(),
                            args[0],args[1],args[2],args[3]);
                        assert!(matches!(refused,Err(HnnError::Carrier { what:"an operand's coordinate beyond the 64-bit word" })));
                        assert_eq!(image,contact.solve().unwrap().apply(&right).unwrap());
                        println!("old response refused: stage={stage}; source_ring={source}; coordinate={coordinate}; absolute_tick={}; contact={a}; exact_right={right:?}; integral_numerators={numerators:?}; positive_denominator={denominator}; magnitude_bits={:?}; same_Xhat_image={image:?}",
                            opened_at+crossing,numerators.iter().map(|n|n.bits()).collect::<Vec<_>>());
                        return;
                    }
                }
                panic!("the diagnosed matched refusal must expose its producing operand");
            }
        }}
        panic!("the actual refused response operand must be reproduced");
    }

    #[test]
    fn contact_radius_faces_reuse_the_same_native_images_under_one_producing_word() {
        let field=matched_field();
        let theta=Constitution::initial(&field,CAMPAIGN_ONE_BUDGET).unwrap();
        let current=Current::at_rest(&field);
        let source=SourceMoment::open_with(&field,&current,&theta).unwrap();
        let mut charts=Charts::new();
        let (word,_)=Word::open_charted_received(&field,&theta,&current,&source,&mut charts,&WordOpening::Rest).unwrap();
        let linear=word.operands().clone().unsplit().unwrap();
        let mut faces=ContactRadiusMaps::new(&linear);
        let mut total=0;
        for (a,c) in linear.contacts().iter().enumerate() {
            let (from,to)=c.ends();
            let n0=linear.rings()[from].width();let n1=linear.rings()[to].width();let n=c.width();
            let shape=[n0,n1,n,n];
            let values:Vec<_>=shape.iter().map(|&width|vec![Rat::one();width]).collect();
            let inputs:Vec<_>=values.iter().map(Vec::as_slice).collect();
            let raw=|b:&[Vec<Rat>]|Ok(crate::hnn::propagation::transit_solve(c,linear.step(),&b[0],&b[1],&b[2],&b[3])?.0);
            let expected=physical_linear_radius(&inputs,n,&raw).unwrap();
            assert_eq!(faces.right(a,&inputs).unwrap(),expected);
            total+=shape.iter().sum::<usize>();
            assert_eq!(faces.located_columns(),total);
            let changed:Vec<_>=values.iter().map(|row|scale(&integer(3),row)).collect();
            let inputs:Vec<_>=changed.iter().map(Vec::as_slice).collect();
            assert_eq!(faces.right(a,&inputs).unwrap(),physical_linear_radius(&inputs,n,&raw).unwrap());
            assert_eq!(faces.located_columns(),total,"fresh radius uses already located coefficient columns");
            let shape=[n,n0,n1,n,n];
            let values:Vec<_>=shape.iter().map(|&width|vec![Rat::one();width]).collect();
            let inputs:Vec<_>=values.iter().map(Vec::as_slice).collect();
            let raw=|b:&[Vec<Rat>]| {
                let p=crate::hnn::propagation::transit_update(c,linear.step(),&b[0],&b[1],&b[2],&b[3],&b[4]);
                Ok([p.arrive_from,p.arrive_to,p.displacement,p.rate].concat())
            };
            assert_eq!(faces.update(a,&inputs).unwrap(),physical_linear_radius(&inputs,n0+n1+2*n,&raw).unwrap());
            total+=shape.iter().sum::<usize>();
            assert_eq!(faces.located_columns(),total);
            assert_eq!(faces.update(a,&inputs).unwrap(),physical_linear_radius(&inputs,n0+n1+2*n,&raw).unwrap());
            assert_eq!(faces.located_columns(),total);
        }
        let fresh=ContactRadiusMaps::new(&linear);
        assert_eq!(fresh.located_columns(),0,"a new producing face never inherits a previous word's coefficients");
        println!("exact contact radius columns located={total}; repeated applications locate no further columns; no forward tick removed");
        drop(word);
    }

    #[test]
    fn source_response_re_represents_the_producing_chart() {
        let started=std::time::Instant::now();
        let field=matched_field();let theta=Constitution::initial(&field,CAMPAIGN_ONE_BUDGET).unwrap();
        let current=Current::at_rest(&field);
        let receiver=ReceiverDeclaration {aperture:4,..field.receivers()[0].clone()};
        let phases=ReceivingPhases::declare(&field,&theta,&current,&receiver).unwrap();
        let truth=KnownTruth::cyclic_class_orbit(CyclicLaw::OrderTwo {opening:2},4,20261006001,4).unwrap();
        let observed=Encoded::identity(&truth,&field).unwrap().remove(0);
        let damaged=DamagedSection::damage(&observed,&[2]).unwrap();
        assert_eq!(damaged.placed(),vec![Some(2),Some(2),None,Some(3)]);
        let mut charts=Charts::new();
        let pending=predict(&field,&theta,&current,&damaged,&WordOpening::Rest,None,&phases,&mut charts).unwrap();
        println!("same matched blind cells={:?}; actual ticks={}; producing charts={:?}",
            pending.prediction().cells,pending.prediction().carry.ticks,pending.error().charts);
        assert!(matches!(pending.prediction().cells[2],RepairedCell::Held {..}));
        let compared=[false,false,true,false];
        let reads:Vec<_>=pending.prediction().reads.iter().map(|r|r.read.clone()).collect();
        let targets:Vec<_>=observed.classes_read().collect();
        let ratio=HolonRatio::compare_partition(Faces::of_reads(&reads,phases.grain()).unwrap(),&targets,
            &target_phases(&field,current.lift(),0,&observed).unwrap(),&compared).unwrap();
        let g=ratio.covector().unwrap();
        let ge=comparison_error(&reads,&pending.error.stations,&targets,&compared,phases.grain()).unwrap();
        let word=&pending.pending.word;
        // pull_back consumes its Word. This explicit native return control opens from the
        // SAME blind source and cold charts; the original Word remains for observe below.
        // Its construction, passage and return cost belong to this falsifier, not a speed read.
        let control_started=std::time::Instant::now();
        let mut control_charts=Charts::new();
        let (mut control,control_opening)=crate::hnn::word::Word::open_charted_received(
            &field,&theta,&current,&pending.pending.source,&mut control_charts,&WordOpening::Rest).unwrap();
        for _ in 1..phases.junction_steps() {control.tick().unwrap();}
        // The terminal junction emits another exchange. change() reads the continuing motion
        // only before that junction; afterward its legitimate receipt is reception_end().
        assert!(!control.is_ended());
        let control_before_terminal=control.change().unwrap();
        control.last_junction().unwrap();
        assert!(control.is_ended() && word.is_ended());
        assert_eq!(control_opening,pending.error.opening);
        assert!(control_opening.closes());
        assert_eq!(control.operands(),word.operands());
        assert_eq!(control.opened_at(),word.opened_at());
        assert_eq!(control.clock().ticks(),word.clock().ticks());
        assert_eq!(control.recorded(),word.recorded());
        let control_carry=control.reception_end().unwrap();
        assert_eq!(control_before_terminal,pending.prediction().carry.change);
        assert_eq!(control_carry.change,control_before_terminal);
        assert_eq!(control_carry,pending.prediction().carry);
        assert_eq!(control_carry,word.reception_end().unwrap());
        assert_eq!(control.released().unwrap(),word.released().unwrap());
        let back=control.pull_back(&g,theta.receiving_map(0).unwrap(),&current.lift()[0],&phases).unwrap();
        println!("explicit identical native return control: opening_operands_clock_passage_change_carry_release_equal=true; control_setup_forward_identity_and_return_ns={}",
            control_started.elapsed().as_nanos());
        let operands=word.operands();let opened_at=word.opened_at();
        let old=source_return_error_on(&field,&theta,&current,&phases,operands,opened_at,&g,&ge,&back);
        assert!(matches!(old,Err(HnnError::Carrier { what:"an operand's coordinate beyond the 64-bit word" })));
        refused_response_operand(&field,&phases,operands,opened_at);
        let linear=operands.clone().unsplit().unwrap();
        assert_eq!(linear.charts(),operands.charts());
        for (r,l) in operands.rings().iter().zip(linear.rings()) {assert_eq!(r.solve().unwrap(),l.solve().unwrap());}
        for (r,l) in operands.contacts().iter().zip(linear.contacts()) {assert_eq!(r.solve().unwrap(),l.solve().unwrap());}
        for ring in 0..field.rings().len() {assert_eq!(operands.weights(ring),linear.weights(ring));}
        let changed=source_return_error(&field,&theta,&current,&phases,operands,opened_at,&g,&ge,&back).unwrap();
        assert_eq!(changed,source_return_error_on(&field,&theta,&current,&phases,&linear,opened_at,&g,&ge,&back).unwrap());
        // The same bounded carrier still refuses the original right side above. Only the
        // certificate's unsplit response calculus changes representation; no target enters it.
        let tolerance=ChartedTolerance {logits:rat(1,16),receiving_covector:rat(1,16),source_covector:rat(1,16)};
        let publication=pending.observe(&theta,&observed,&compared,&tolerance)
            .unwrap_or_else(|(_,e)|panic!("same first observed comparison refused: {e:?}"));
        assert_eq!(publication.error.source_opening,back.opening);
        assert_eq!(publication.error.return_remainders,back.released);
        assert!(publication.error.applied.holds());
        assert!(publication.error.applied.decrease>Rat::zero());
        assert_eq!(publication.error.tolerance.source_covector,tolerance.source_covector);
        assert!(publication.teaching.publication.stepped>0);
        assert!(publication.teaching.prediction.word.closes());
        assert!(publication.teaching.prediction.balances.iter().all(|b|b.closes()));
        println!("changed matched comparison: commit={}; source_error={:?}; source_rounding={:?}; applied={:?}; chart_starts={:?}; elapsed_ns={}",
            publication.teaching.publication.commit,publication.error.source_covectors,publication.error.source_rounding,
            publication.error.applied,linear.charts().iter().map(|r|(r.start,r.steps)).collect::<Vec<(ChartStart,u32)>>(),
            started.elapsed().as_nanos());
    }
}
