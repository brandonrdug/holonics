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
use crate::hnn::reference::{Reference, Resident};
use crate::hnn::retention::Diamond;
use crate::hnn::word::{Absorption, ChartedSourceOpeningReceipt, EndChange};
use crate::holon::HolonState;
use crate::holon::deposition::JointReading;
use crate::ratio::exponentiated::CarriedPower;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, scale, sub};

mod linear_radius;
use linear_radius::ContactRadiusMaps;

/// Coordinate radius for a same-cut response column, against the unsplit physical law.
/// This shares the existing native error owner. Each advance charges one unsplit surrogate
/// tick, whose difference from the executed column includes every signed-feedback split.
pub struct ResponseTube<'a> {
    maps: std::rc::Rc<std::cell::RefCell<ContactRadiusMaps<'a>>>,
    radius: EndChange,
}

impl<'a> ResponseTube<'a> {
    /// Immutable domain admission; requesting no unsplit report never skips this.
    pub fn admit_operands(o: &Operands) -> Result<(), HnnError> {
        let valid=|d:Rat| d>=Rat::zero() && d<Rat::one();
        if o.rings().iter().any(|r| !valid(r.chart().map_or_else(Rat::zero,|c|c.certificate.clone())))
            || o.contacts().iter().any(|c| !valid(c.chart().map_or_else(Rat::zero,|c|c.certificate.clone())))
            || o.resonators().iter().flatten().any(|r| r.material().saturation().is_some() || (0..r.phases()).any(|p|!valid(r.certificate(p)))) {
            return Err(HnnError::Unadmitted {reason:"paired response operands retain linear resonators and admitted inverse-chart deviations"});
        }
        Ok(())
    }

    fn admit_shape(o: &Operands, point: &EndChange, missing_rest: bool) -> Result<(), HnnError> {
        let widths: Vec<_> = o.rings().iter().map(|r| r.width()).collect();
        let valid = point.storage.len() == widths.len()
            && point
                .storage
                .iter()
                .zip(&widths)
                .all(|(v, n)| v.len() == *n)
            && point.arrivals.len() == o.contacts().len()
            && point.states.len() == o.contacts().len()
            && point.arrivals.iter().zip(o.contacts()).all(|(v, c)| {
                let (a, b) = c.ends();
                v[0].len() == widths[a] && v[1].len() == widths[b]
            })
            && point
                .states
                .iter()
                .zip(o.contacts())
                .all(|(v, c)| v.iter().all(|v| v.len() == c.width()))
            && point.resonators.len() == widths.len()
            && point.resonator_phases.len() == widths.len()
            && point.resonators.iter().zip(o.resonators()).enumerate().all(
                |(r, (state, op))| match (state, op) {
                    (Some(state), Some(_)) => state.iter().all(|v| v.len() == widths[r]),
                    (None, None) => true,
                    (None, Some(_)) => missing_rest,
                    _ => false,
                },
            );
        if !valid {
            return Err(HnnError::Unadmitted {
                reason: "a coordinate error tube keeps its producing complete state shape",
            });
        }
        Ok(())
    }

    pub fn open(
        o: &'a Operands,
        exact: &EndChange,
        executed: &EndChange,
    ) -> Result<Self, HnnError> {
        Self::admit_operands(o)?;
        Self::admit_shape(o, exact, true)?;
        Self::admit_shape(o, executed, false)?;
        if o.resonators()
            .iter()
            .flatten()
            .any(|r| r.material().saturation().is_some())
        {
            return Err(HnnError::Unadmitted {
                reason: "a paired response column requires a linear resonator or its declared nonlinear variation",
            });
        }
        let mut exact = exact.clone();
        for (r, state) in exact.resonators.iter_mut().enumerate() {
            if state.is_none() && o.resonators()[r].is_some() {
                *state = Some([
                    vec![Rat::zero(); o.rings()[r].width()],
                    vec![Rat::zero(); o.rings()[r].width()],
                ]);
            }
        }
        let mut radius = executed.clone();
        join_change(&mut radius, &exact, |a, b| (a - b).abs());
        Ok(Self {
            maps: std::rc::Rc::new(std::cell::RefCell::new(ContactRadiusMaps::new(o))),
            radius,
        })
    }

    /// New independent radius/point state; only authentic immutable coefficient columns are shared.
    pub fn new_track(&self,exact:&EndChange,executed:&EndChange)->Result<Self,HnnError>{
        let mut track=Self::open(self.maps.borrow().operands,exact,executed)?;
        track.maps=std::rc::Rc::clone(&self.maps); Ok(track)
    }
    pub fn radius(&self) -> &EndChange {
        &self.radius
    }

    /// Direction-independent contact readings at the original executed intermediate.
    /// The actual anchor split is included before selecting channel coordinates. These are
    /// state/midpoint operands for a later tangent certificate, never a material-ray proof.
    pub(crate) fn material_contact_stages(&self,point:&EndChange,anchors:&[Vec<Rat>],midpoints:&[Vec<Rat>])
        ->Result<Vec<crate::hnn::word::material_ray::OriginalContactStage>,HnnError>{
        let o=self.maps.borrow().operands;
        Self::admit_shape(o,point,false)?;
        let centers=crate::hnn::word::linear::junctions(o,point)?;
        let bounds=junction_error(o,point,&self.radius)?;
        if anchors.len()!=centers.len() || midpoints.len()!=o.contacts().len() || anchors.iter().zip(&centers).any(|(a,c)|a.len()!=c.anchor.len()) {
            return Err(HnnError::Unadmitted{reason:"material stage readings keep every original anchor/midpoint"});
        }
        o.contacts().iter().enumerate().map(|(a,c)|{
            let (from,to)=c.ends();let (sf,st)=c.selection();
            let actual_outgoing=|r:usize|->Vec<Rat>{let incoming=&point.arrivals[a][o.end_slot(a,r)];anchors[r].iter().zip(incoming).map(|(v,x)|crate::ratio::integer(2)*v-x).collect()};
            let out_error=|r:usize|->Vec<Rat>{outgoing(o,&bounds,r,a).iter().zip(anchors[r].iter().zip(&centers[r].anchor)).map(|(e,(v,c))|e+crate::ratio::integer(2)*(v-c).abs()).collect()};
            let af=actual_outgoing(from);let at=actual_outgoing(to);let ef=out_error(from);let et=out_error(to);
            let h=o.step();let g=c.conductance();
            let selected=sf.iter().map(|&i|af[i].clone()).chain(st.iter().map(|&i|at[i].clone()))
                .chain(point.states[a][0].iter().map(|x|x/(h*g))).chain(point.states[a][1].iter().map(|x|x/g)).collect::<Vec<_>>();
            let errors=sf.iter().map(|&i|ef[i].clone()).chain(st.iter().map(|&i|et[i].clone()))
                .chain(self.radius.states[a][0].iter().map(|x|x/(h*g))).chain(self.radius.states[a][1].iter().map(|x|x/g)).collect::<Vec<_>>();
            if midpoints[a].len()!=c.width(){return Err(HnnError::Unadmitted{reason:"material stage has its actual complete midpoint"});}
            let (_,image)=crate::hnn::propagation::transit_solve(c,h,&af,&at,&point.states[a][0],&point.states[a][1])?;
            let residual=midpoints[a].iter().zip(image).map(|(w,z)|crate::ratio::integer(2)*h/g*w-z).collect::<Vec<_>>();
            Ok(crate::hnn::word::material_ray::OriginalContactStage{
                input_norm:crate::hnn::word::material_ray::vector_norm(&selected),
                input_error:crate::hnn::word::material_ray::vector_norm(&errors),
                solve_residual:crate::hnn::word::material_ray::vector_norm(&residual)})
        }).collect()
    }

    /// A whole physical tick norm from the existing nonnegative radius action. A Euclidean
    /// unit ball lies in this normalized component box. Shared inputs/copies are all counted.
    /// This is one coefficient-bound computation, not a basis Word or physical tick.
    pub(crate) fn physical_tick_norms(o:&Operands,tick:usize)->Result<(Rat,Rat),HnnError>{
        let point=EndChange{
            storage:o.rings().iter().map(|r|vec![Rat::zero();r.width()]).collect(),
            arrivals:o.contacts().iter().map(|c|{let(a,b)=c.ends();[vec![Rat::zero();o.rings()[a].width()],vec![Rat::zero();o.rings()[b].width()]]}).collect(),
            states:o.contacts().iter().map(|c|[vec![Rat::zero();c.width()],vec![Rat::zero();c.width()]]).collect(),
            resonators:o.resonators().iter().map(|r|r.as_ref().map(|r|[vec![Rat::zero();r.width()],vec![Rat::zero();r.width()]])).collect(),
            resonator_phases:o.resonators().iter().map(|r|r.as_ref().map(|r|r.phase_at(tick.saturating_sub(1)))).collect()};
        let mut radius=point.clone();
        for v in radius.storage.iter_mut().chain(radius.arrivals.iter_mut().flatten()){v.fill(Rat::one());}
        for (s,c) in radius.states.iter_mut().zip(o.contacts()){s[0].fill(o.step()*c.conductance());s[1].fill(c.conductance().clone());}
        for (s,r) in radius.resonators.iter_mut().zip(o.resonators()){if let(Some(s),Some(r))=(s,r){s[0].fill(o.step()*r.admittance());s[1].fill(r.admittance().clone());}}
        // Keep the declared phases; zero values are a coefficient origin, not an exterior event.
        let mut bound=tick_error_cached(&mut ContactRadiusMaps::new(o),&point,&radius,tick)?;
        let full=crate::hnn::word::material_ray::state_norm(o,&bound)?;
        // The intermediate cut is AFTER the fixed junction/element/load stage and
        // BEFORE contact transits: carry every outgoing wave and unchanged contact state.
        // Shared storage/outgoing inputs are counted together in this full vector norm.
        let junction=junction_error(o,&point,&radius)?;
        for(a,c)in o.contacts().iter().enumerate(){let(f,t)=c.ends();
            bound.arrivals[a]=[outgoing(o,&junction,f,a).to_vec(),outgoing(o,&junction,t,a).to_vec()];
            bound.states[a]=radius.states[a].clone();
        }
        Ok((full,crate::hnn::word::material_ray::state_norm(o,&bound)?))
    }

    pub fn held_overwrite(&mut self, ring: usize) -> Result<(), HnnError> {
        let rings = self.radius.storage.len();
        self.radius
            .storage
            .get_mut(ring)
            .ok_or(HnnError::RingOutside { ring, rings })?
            .fill(Rat::zero());
        Ok(())
    }

    pub fn anchors(
        &self,
        point: &EndChange,
        actual: &[Vec<Rat>],
    ) -> Result<Vec<Vec<Rat>>, HnnError> {
        Self::admit_shape(self.maps.borrow().operands, point, false)?;
        if actual.len() != self.maps.borrow().operands.rings().len()
            || actual
                .iter()
                .zip(self.maps.borrow().operands.rings())
                .any(|(v, r)| v.len() != r.width())
        {
            return Err(HnnError::Unadmitted {
                reason: "the anchor error certificate reads every producing ring coordinate",
            });
        }
        let centers = physical_signed_junctions(self.maps.borrow().operands, point)?;
        let bounds = junction_error(self.maps.borrow().operands, point, &self.radius)?;
        Ok(bounds
            .iter()
            .zip(centers)
            .zip(actual)
            .map(|((e, c), a)| {
                e.anchor
                    .iter()
                    .zip(a.iter().zip(c.anchor))
                    .map(|(e, (a, c))| e + (a - c).abs())
                    .collect()
            })
            .collect())
    }

    /// One requested crossing: reuse identical signed junctions and radius junctions for
    /// anchor observation and the following tick. Point and radius remain independent.
    pub fn crossing(&mut self,point:&EndChange,anchors:&[Vec<Rat>],next:Option<&EndChange>,tick:usize)->Result<Vec<Vec<Rat>>,HnnError>{
        let o=self.maps.borrow().operands;
        Self::admit_shape(o,point,false)?;
        if anchors.len()!=o.rings().len() || anchors.iter().zip(o.rings()).any(|(a,r)|a.len()!=r.width()) {return Err(HnnError::Unadmitted {reason:"requested crossing retains actual anchor shape"});}
        let centers=physical_signed_junctions(o,point)?;
        let bounds=junction_error(o,point,&self.radius)?;
        let error=bounds.iter().zip(&centers).zip(anchors).map(|((e,c),a)|e.anchor.iter().zip(a.iter().zip(&c.anchor)).map(|(e,(a,c))|e+(a-c).abs()).collect()).collect();
        if let Some(actual)=next {
            Self::admit_shape(o,actual,false)?;
            let signed=crate::hnn::word::linear::tick_at_junctions(o,point,tick,&centers)?;
            let mut radius=tick_error_at_junctions(&mut self.maps.borrow_mut(),point,&self.radius,tick,&centers,&bounds)?;
            let mut split=actual.clone();join_change(&mut split,&signed,|a,b|(a-b).abs());join_change(&mut radius,&split,|a,b|a+b);self.radius=radius;
        }
        Ok(error)
    }
    pub fn advance(
        &mut self,
        point: &EndChange,
        actual: &EndChange,
        tick: usize,
    ) -> Result<(), HnnError> {
        Self::admit_shape(self.maps.borrow().operands, point, false)?;
        Self::admit_shape(self.maps.borrow().operands, actual, false)?;
        let signed = physical_signed_tick(self.maps.borrow().operands, point, tick)?;
        let mut next = tick_error_cached(&mut self.maps.borrow_mut(), point, &self.radius, tick)?;
        let mut split = actual.clone();
        join_change(&mut split, &signed, |a, b| (a - b).abs());
        join_change(&mut next, &split, |a, b| a + b);
        self.radius = next;
        Ok(())
    }
}

/// Component tolerances in the declared receiving/source charts. None is an iteration budget.
#[derive(Clone, Debug)]
pub struct ChartedTolerance {
    pub logits: Rat,
    pub receiving_covector: Rat,
    pub source_covector: Rat,
}

impl ChartedTolerance {
    fn admit(&self) -> Result<(), HnnError> {
        if [
            &self.logits,
            &self.receiving_covector,
            &self.source_covector,
        ]
        .iter()
        .any(|x| **x < Rat::zero())
        {
            return Err(HnnError::Unadmitted {
                reason: "a charted comparison tolerance is negative",
            });
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
            && self
                .physical
                .balances
                .iter()
                .all(|balance| balance.closes())
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
    /// The actual same-return cotangent lattice; forward Word precision is unchanged.
    pub return_precision: crate::hnn::chart::ReturnPrecision,
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
    pub fn prediction(&self) -> &PhysicalRepair {
        self.pending.prediction()
    }
    pub fn error(&self) -> &ChartedErrorReceipt {
        &self.error
    }

    pub fn finish(self) -> ChartedPhysicalRepair {
        ChartedPhysicalRepair {
            physical: self.pending.finish(),
            error: self.error,
        }
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
        let PhysicalPrediction {
            field,
            material,
            current,
            phases,
            chart,
            opening_support,
            source,
            word,
            prediction,
        } = pending;
        let joined = (|| -> Result<_, HnnError> {
            tolerance.admit()?;
            if material.commit() != contemporary.commit() || material != contemporary {
                return Err(HnnError::Unadmitted {
                    reason: "the charted return's producing material changed",
                });
            }
            if observed.part(0..0)? != chart
                || observed.len() != phases.aperture()
                || compared.len() != phases.aperture()
                || prediction.reads.len() != phases.aperture()
                || !compared.iter().any(|x| *x)
                || !field.is_source(phases.ring())
                || phases.first_epoch() != 0
            {
                return Err(HnnError::Unadmitted {
                    reason: "the charted observation has a foreign chart, partition or station clock",
                });
            }
            let reads: Vec<_> = prediction.reads.iter().map(|x| x.read.clone()).collect();
            let targets: Vec<_> = observed.classes_read().collect();
            let ratio = HolonRatio::compare_partition(
                Faces::of_reads(&reads, phases.grain())?,
                &targets,
                &target_phases(field, current.lift(), phases.ring(), observed)?,
                compared,
            )?;
            let covector = ratio.covector()?;
            let g_error =
                comparison_error(&reads, &error.stations, &targets, compared, phases.grain())?;
            let operands = word.operands().clone();
            let opened_at = word.opened_at();
            let map =
                material
                    .receiving_map(phases.ring())
                    .ok_or(HnnError::MissingReceivingMap {
                        ring: phases.ring(),
                    })?;
            let back = word.pull_back(&covector, map, &phases)?;
            let (source_error, source_rounding) = source_return_error(
                field, material, &phases, &operands, opened_at, &covector, &g_error, &back,
            )?;
            let gradient_error = receiving_error(
                field,
                &phases,
                &back,
                &error.stations,
                &covector,
                &g_error,
                compared,
            )?;
            if error
                .stations
                .iter()
                .zip(compared)
                .any(|(e, crossed)| *crossed && sup(&e.logits) > tolerance.logits)
                || gradient_error
                    .entries()
                    .iter()
                    .any(|e| *e > tolerance.receiving_covector)
                || source_error
                    .iter()
                    .flatten()
                    .any(|e| *e > tolerance.source_covector)
            {
                return Err(HnnError::Unadmitted {
                    reason: "the source or receiving covector exceeds its declared charted tolerance",
                });
            }
            let diamond = Diamond::opened(field, &phases, &opening_support);
            let composed = crate::hnn::reference::compose_return(
                field,
                material,
                &diamond,
                current.lift(),
                &current,
                &source,
                &back,
            )?;
            let mut linear: Vec<_> = composed
                .linear
                .into_iter()
                .filter(|step| step.locus == LinearLocus::Receiving(phases.ring()))
                .collect();
            for step in &mut linear {
                if step.samples.len() != compared.len() {
                    return Err(HnnError::Unadmitted {
                        reason: "the charted receiving samples have another comparison partition",
                    });
                }
                step.samples = std::mem::take(&mut step.samples)
                    .into_iter()
                    .zip(compared)
                    .filter_map(|(sample, crossed)| crossed.then_some(sample))
                    .collect();
            }
            if linear.is_empty() {
                return Err(HnnError::Unadmitted {
                    reason: "the charted comparison reaches no receiving relation",
                });
            }
            let reached = vec![Locus::ReceivingMap(phases.ring())];
            let deposit = Deposit::new(material.commit(), linear, Vec::new(), reached.clone())
                .with_reach(Reach {
                    receiver: phases.ring(),
                    stations: phases
                        .epochs()
                        .zip(compared)
                        .filter_map(|(tick, crossed)| crossed.then_some(tick as u64))
                        .collect(),
                    entries: vec![0],
                    phases: composed.phases,
                    loci: reached.into_iter().collect(),
                    passages: Vec::new(),
                });
            let feature_energy = deposit
                .linear()
                .iter()
                .map(|step| {
                    (
                        step.locus.locus(),
                        step.samples
                            .iter()
                            .map(|s| &s.weight * dot(&s.feature, &s.feature))
                            .sum(),
                    )
                })
                .collect();
            let (constitution, publication) = contemporary.deposited(&deposit)?;
            if !same_interior(field, material, &constitution) {
                return Err(HnnError::Unadmitted {
                    reason: "a charted receiving successor changes the carried physical law",
                });
            }
            let delta = constitution
                .receiving_map(phases.ring())
                .ok_or(HnnError::MissingReceivingMap {
                    ring: phases.ring(),
                })?
                .subtract(map)?;
            let alignment_error = matrix_pairing_radius(&gradient_error, &delta)?;
            let (mut alignment, mut moves) = (Rat::zero(), Rat::zero());
            for (j, crossed) in compared.iter().enumerate().filter(|(_, x)| **x) {
                let _ = crossed;
                let feature = &back.reads[j].0;
                let moved = delta.apply(feature)?;
                alignment -= dot(&covector.logits()[j], &moved);
                let radius = matrix_radius(&delta, &transport_radius(&error.stations[j].anchor))?;
                moves += moved
                    .iter()
                    .zip(radius)
                    .map(|(x, r)| (x.abs() + r).pow(2))
                    .sum::<Rat>();
            }
            let applied = JointReading {
                curvature: &moves / crate::ratio::integer(2),
                decrease: alignment - &alignment_error,
            };
            if applied.decrease <= Rat::zero() || !applied.holds() {
                return Err(HnnError::Unadmitted {
                    reason: "the actual receiving move fails after source and covector error are charged",
                });
            }
            Ok((
                ratio,
                composed.pullback,
                constitution,
                publication,
                feature_energy,
                ChartedComparisonReceipt {
                    logit_covectors: g_error,
                    receiving_covector: gradient_error,
                    source_opening: back.opening,
                    source_covectors: source_error,
                    source_rounding,
                    return_precision: back.precision.clone(),
                    return_remainders: back.released,
                    applied,
                    alignment_error,
                    tolerance: tolerance.clone(),
                },
            ))
        })();
        match joined {
            Ok((ratio, pullback, constitution, publication, feature_energy, comparison)) => {
                Ok(ChartedPhysicalPublication {
                    teaching: PhysicalTeaching {
                        prediction,
                        ratio,
                        pullback,
                        constitution,
                        publication,
                        feature_energy,
                        receiving_diagnostic: None,
                        source_certificate: None,
                        source_pairing: None,
                    },
                    error: comparison,
                })
            }
            Err(reason) => Err((
                ChartedPhysicalRepair {
                    physical: prediction,
                    error,
                },
                reason,
            )),
        }
    }
}

/// A resident of the actual physical field and its present error box. R-only publication keeps
/// every carry-crossing material/reference fixed, so this box crosses by the identity; imposed
/// source storage is replaced. A caller-supplied first opening is a declared exact initial state.
pub struct ChartedPhysicalReceiver<'f> {
    field: &'f Field,
    resident: Resident,
    tolerance: ChartedTolerance,
    declaring: DeclaringFace<'f>,
}

impl<'f> ChartedPhysicalReceiver<'f> {
    pub fn new(
        field: &'f Field,
        constitution: Constitution,
        current: Current,
        opening: WordOpening,
        tolerance: ChartedTolerance,
    ) -> Result<Self, HnnError> {
        Self::from_resident(
            field,
            Reference::mount_receiving(field, &current, constitution, opening)?,
            tolerance,
        )
    }
    pub fn from_resident(
        field: &'f Field,
        resident: Resident,
        tolerance: ChartedTolerance,
    ) -> Result<Self, HnnError> {
        resident.admit_receiving_view(field)?;
        tolerance.admit()?;
        if field.word_lattice().is_none() {
            return Err(HnnError::Unadmitted {
                reason: "the charted receiving view has no declared Word lattice",
            });
        }
        Ok(Self {
            field,
            resident,
            tolerance,
            declaring: DeclaringFace::new(field),
        })
    }
    pub fn constitution(&self) -> &Constitution {
        self.resident.constitution()
    }
    pub fn opening(&self) -> WordOpening {
        self.resident.reception_opening()
    }
    pub fn carry_error(&self) -> Option<&EndChange> {
        self.resident.carry_error()
    }
    pub fn charts(&self) -> &Charts {
        self.resident.charts()
    }
    pub fn into_resident(self) -> Resident {
        self.resident
    }

    pub fn receive(
        &mut self,
        section: &DamagedSection,
        receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalRepair) -> Option<(Encoded, Vec<bool>)>,
    ) -> Result<ChartedPhysicalReception, HnnError> {
        self.resident.admit_receiving_chart(section.chart())?;
        let opening = self.resident.reception_opening();
        let (phases, declaring_face_reused) = self.declaring.declare(
            self.resident.constitution(),
            self.resident.current(),
            receiver,
        )?;
        let mut charts = self.resident.reception_charts();
        let pending = predict(
            self.field,
            self.resident.constitution(),
            self.resident.current(),
            section,
            &opening,
            self.resident.carry_error(),
            &phases,
            &mut charts,
        )?;
        let forward_error = pending.error.clone();
        let (prediction, mut comparison, successor) = match observation(pending.prediction()) {
            None => (pending.finish(), Ok(None), None),
            Some((observed, compared)) => match pending.observe(
                self.resident.constitution(),
                &observed,
                &compared,
                &self.tolerance,
            ) {
                Ok(publication) => {
                    let successor = publication.teaching.constitution.clone();
                    let prediction = ChartedPhysicalRepair {
                        physical: publication.teaching.prediction.clone(),
                        error: forward_error,
                    };
                    (prediction, Ok(Some(publication)), Some(successor))
                }
                Err((prediction, error)) => (prediction, Err(error), None),
            },
        };
        let commit = successor
            .as_ref()
            .unwrap_or_else(|| self.resident.constitution())
            .commit();
        if let Err(error) = self.resident.publish_reception(
            successor,
            HolonState::at(prediction.physical.carry.clone(), commit),
            Some(charts.clone()),
            Some(prediction.error.end.clone()),
            section.chart(),
        ) {
            comparison = Err(error);
            let commit = self.resident.constitution().commit();
            self.resident.publish_reception(
                None,
                HolonState::at(prediction.physical.carry.clone(), commit),
                Some(charts),
                Some(prediction.error.end.clone()),
                section.chart(),
            )?;
        }
        Ok(ChartedPhysicalReception {
            prediction,
            comparison,
            declaring_face_reused,
        })
    }
}

fn predict<'f, 'm>(
    field: &'f Field,
    material: &'m Constitution,
    current: &Current,
    section: &DamagedSection,
    opening: &WordOpening,
    carried: Option<&EndChange>,
    phases: &ReceivingPhases,
    charts: &mut Charts,
) -> Result<ChartedPhysicalPrediction<'f, 'm>, HnnError> {
    section.admit(field, material, phases)?;
    let placed = section.placed();
    let mut source = SourceMoment::open_with(field, current, material)?;
    for &g in field.sources() {
        source = source.station_section(field, current, g, &placed)?;
    }
    let (mut word, receipt) =
        Word::open_charted_received(field, material, current, &source, charts, opening)?;
    let operands = word.operands().clone();
    let mut radius_maps = ContactRadiusMaps::new(&operands);
    if operands
        .resonators()
        .iter()
        .flatten()
        .any(|r| r.material().saturation().is_some())
    {
        return Err(HnnError::Unadmitted {
            reason: "a charted physical comparison needs its nonlinear Word-Hessian error join",
        });
    }
    let mut radius = receipt.error.clone();
    if matches!(
        opening,
        WordOpening::Received {
            absorption: Absorption::Nothing,
            ..
        }
    ) {
        if let Some(carried) = carried {
            let mut interior = carried.clone();
            for &g in field.sources() {
                interior.storage[g].fill(Rat::zero());
            }
            join_change(&mut radius, &interior, |a, b| a + b);
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
        if crossing + 1 == phases.junction_steps() {
            // reception_end restores this pre-scatter crossing; emitted coordinates belong
            // to released().end. Bind the retained radius to its actual consuming state.
            carried_point = Some(point);
            word.last_junction()?;
        } else {
            let signed = physical_signed_tick(&operands, &point, opened_at + crossing)?;
            let mut next =
                tick_error_cached(&mut radius_maps, &point, &radius, opened_at + crossing)?;
            word.tick()?;
            let actual = word.change()?;
            let mut split = actual;
            join_change(&mut split, &signed, |a, b| (a - b).abs());
            join_change(&mut next, &split, |a, b| a + b);
            radius = next;
        }
        if phases.epochs().contains(&crossing) {
            let ring = phases.ring();
            let actual = word.anchor(crossing, ring).ok_or(HnnError::WordEnded {
                ticks: word.ticks(),
            })?;
            let anchor = junctions[ring]
                .anchor
                .iter()
                .zip(actual.iter().zip(&centers[ring].anchor))
                .map(|(e, (a, c))| e + (a - c).abs())
                .collect::<Vec<_>>();
            let logits = matrix_radius(
                material
                    .receiving_map(ring)
                    .ok_or(HnnError::MissingReceivingMap { ring })?,
                &transport_radius(&anchor),
            )?;
            errors.push(ChartedStationError {
                station: errors.len(),
                tick: opened_at + crossing,
                anchor,
                logits,
            });
        }
    }
    let reads = phases
        .epochs()
        .enumerate()
        .map(|(station, crossing)| {
            Ok(StationRead {
                station,
                crossing,
                tick: opened_at + crossing,
                read: phases.read(
                    field,
                    material,
                    word.anchor(crossing, phases.ring())
                        .ok_or(HnnError::WordEnded {
                            ticks: word.ticks(),
                        })?,
                )?,
            })
        })
        .collect::<Result<Vec<_>, HnnError>>()?;
    let carry = word.reception_end()?;
    if carried_point.as_ref() != Some(&carry.change) {
        return Err(HnnError::Unadmitted {
            reason: "the charted carry and its error box have different producing crossings",
        });
    }
    if carry.ticks != opened_at + phases.last_epoch()
        || errors.len() != phases.aperture()
        || word.clock().ticks() != num_bigint::BigUint::from(carry.ticks + 1)
    {
        return Err(HnnError::Unadmitted {
            reason: "the charted physical receiving clock did not execute its declared crossings",
        });
    }
    let cells = placed
        .iter()
        .map(|x| match x {
            Some(c) => RepairedCell::Intact(*c),
            None => RepairedCell::Held {
                fibre: domain_classes(section),
                unresolved: Unresolved::UncertifiedDomain,
            },
        })
        .collect();
    let prediction = PhysicalRepair {
        cells,
        reads,
        domains: vec![None; phases.aperture()],
        opening: receipt.source.clone(),
        balances: word.field_balances().to_vec(),
        word: WordBalance::of(&word.released()?),
        carry,
    };
    Ok(ChartedPhysicalPrediction {
        pending: PhysicalPrediction {
            field,
            material,
            current: current.clone(),
            phases: phases.clone(),
            chart: section.chart().clone(),
            opening_support: opening.support(field),
            source,
            word,
            prediction,
        },
        error: ChartedErrorReceipt {
            opening: receipt,
            charts: operands.charts(),
            initial,
            end: radius,
            stations: errors,
        },
    })
}

fn sup(x: &[Rat]) -> Rat {
    x.iter().map(|x| x.abs()).max().unwrap_or_else(Rat::zero)
}
fn matrix_radius(m: &ExactRatMatrix, e: &[Rat]) -> Result<Vec<Rat>, HnnError> {
    physical_matrix_radius(m, e)
}
/// The radius `R` meets: in the passage frame, the anchor's radius as it stands.
fn transport_radius(e: &[Rat]) -> Vec<Rat> {
    e.iter().map(|e| e.abs()).collect()
}

/// A radius and a point share their native shape, phase and field identity, from this producer.
fn join_change(a: &mut EndChange, b: &EndChange, op: impl Fn(&Rat, &Rat) -> Rat) {
    let join = |a: &mut Vec<Rat>, b: &Vec<Rat>| {
        for (a, b) in a.iter_mut().zip(b) {
            *a = op(a, b);
        }
    };
    for (a, b) in a.storage.iter_mut().zip(&b.storage) {
        join(a, b);
    }
    for (a, b) in a.arrivals.iter_mut().zip(&b.arrivals) {
        for k in 0..2 {
            join(&mut a[k], &b[k]);
        }
    }
    for (a, b) in a.states.iter_mut().zip(&b.states) {
        for k in 0..2 {
            join(&mut a[k], &b[k]);
        }
    }
    for (a, b) in a.resonators.iter_mut().zip(&b.resonators) {
        if let (Some(a), Some(b)) = (a, b) {
            for k in 0..2 {
                join(&mut a[k], &b[k]);
            }
        }
    }
}

fn row_norm(m: &ExactRatMatrix) -> Rat {
    (0..m.rows())
        .map(|i| {
            m.row(i)
                .expect("a native row")
                .iter()
                .map(|x| x.abs())
                .sum()
        })
        .max()
        .unwrap_or_else(Rat::zero)
}

/// Existing inverse-chart deviation, with no exact inverse or unrounded counterfactual solve.
fn solve_error(
    x: &ExactRatMatrix,
    delta: Rat,
    point: &[Rat],
    error: &[Rat],
) -> Result<Vec<Rat>, HnnError> {
    if delta < Rat::zero() || delta >= Rat::one() {
        return Err(HnnError::Unadmitted {
            reason: "a producing inverse chart has no deviation regime",
        });
    }
    let defect = row_norm(x) * &delta / (Rat::one() - delta) * (sup(point) + sup(error));
    Ok(matrix_radius(x, error)?
        .into_iter()
        .map(|e| e + &defect)
        .collect())
}

fn junction_error(
    o: &Operands,
    point: &EndChange,
    error: &EndChange,
) -> Result<Vec<Junction>, HnnError> {
    (0..o.rings().len())
        .map(|g| {
            let points: Vec<_> = std::iter::once(point.storage[g].as_slice())
                .chain(
                    o.incident(g)
                        .iter()
                        .map(|&a| point.arrivals[a][o.end_slot(a, g)].as_slice()),
                )
                .collect();
            let errors: Vec<_> = std::iter::once(error.storage[g].as_slice())
                .chain(
                    o.incident(g)
                        .iter()
                        .map(|&a| error.arrivals[a][o.end_slot(a, g)].as_slice()),
                )
                .collect();
            let radius = |multiplier: Rat, port: Option<usize>| {
                (0..o.rings()[g].width())
                    .map(|i| {
                        o.exact_weights(g)
                            .iter()
                            .zip(o.weights(g))
                            .enumerate()
                            .map(|(p, (exact, charted))| {
                                let coefficient = &multiplier * exact
                                    - if port == Some(p) {
                                        Rat::one()
                                    } else {
                                        Rat::zero()
                                    };
                                coefficient.abs() * &errors[p][i]
                                    + (&multiplier * (exact - charted)).abs() * points[p][i].abs()
                            })
                            .sum()
                    })
                    .collect::<Vec<Rat>>()
            };
            Ok(Junction {
                anchor: radius(Rat::one(), None),
                storage_wave: radius(crate::ratio::integer(2), Some(0)),
                contrast: radius(Rat::one(), Some(0)),
                outgoing: (1..points.len())
                    .map(|p| radius(crate::ratio::integer(2), Some(p)))
                    .collect(),
            })
        })
        .collect()
}

fn tick_error_cached(
    maps: &mut ContactRadiusMaps<'_>,
    point: &EndChange,
    error: &EndChange,
    tick: usize,
) -> Result<EndChange, HnnError> {
    let o = maps.operands;
    let centers = physical_signed_junctions(o, point)?;
    let bounds = junction_error(o, point, error)?;
    tick_error_at_junctions(maps,point,error,tick,&centers,&bounds)
}
fn tick_error_at_junctions(maps:&mut ContactRadiusMaps<'_>,point:&EndChange,error:&EndChange,tick:usize,centers:&[Junction],bounds:&[Junction])->Result<EndChange,HnnError>{
    let o=maps.operands;
    let mut next = error.clone();
    let h = o.step();
    for (g, ring) in o.rings().iter().enumerate() {
        let c = &centers[g];
        let e = &bounds[g];
        let right = add(
            &scale(&crate::ratio::integer(2), &c.storage_wave),
            &ring.contrast().apply(&c.contrast)?,
        );
        let right_error = add(
            &scale(&crate::ratio::integer(2), &e.storage_wave),
            &matrix_radius(ring.contrast(), &e.contrast)?,
        );
        let drive_error = add(
            &solve_error(
                &ring.solve()?,
                ring.chart()
                    .map_or_else(Rat::zero, |c| c.certificate.clone()),
                &right,
                &right_error,
            )?,
            &e.storage_wave,
        );
        let Some(r) = &o.resonators()[g] else {
            next.storage[g] = drive_error;
            continue;
        };
        let drive = crate::hnn::propagation::element_step(ring, &c.storage_wave, &c.contrast)?.next;
        let state = point.resonators[g].as_ref().ok_or(HnnError::Unadmitted {
            reason: "the error tube lost its producing resonator state",
        })?;
        let re = error.resonators[g].as_ref().ok_or(HnnError::Unadmitted {
            reason: "the error tube lost its resonator radius",
        })?;
        let phase = r.phase_at(tick);
        let (capacity, _, _) = r.material().forms();
        let right = sub(
            &add(
                &scale(&crate::ratio::integer(2), &capacity.apply(&state[1])?),
                &scale(h, &drive),
            ),
            &scale(h, &r.stiffness(phase).apply(&state[0])?),
        );
        let right_error = add(
            &add(
                &scale(&crate::ratio::integer(2), &matrix_radius(capacity, &re[1])?),
                &scale(&h.abs(), &drive_error),
            ),
            &scale(&h.abs(), &matrix_radius(r.stiffness(phase), &re[0])?),
        );
        let n = r.width();
        let columns = (0..n)
            .map(|i| {
                let mut basis = vec![Rat::zero(); n];
                basis[i] = Rat::one();
                r.solve(phase, &basis)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let solve = ExactRatMatrix::shaped(
            n,
            n,
            (0..n)
                .map(|i| columns.iter().map(|c| c[i].clone()).collect())
                .collect(),
        )?;
        let rate = solve_error(&solve, r.certificate(phase), &right, &right_error)?;
        next.storage[g] = add(
            &drive_error,
            &scale(&(crate::ratio::integer(2) / r.admittance()), &rate),
        );
        next.resonators[g] = Some([
            add(&re[0], &scale(&h.abs(), &rate)),
            add(&scale(&crate::ratio::integer(2), &rate), &re[1]),
        ]);
        next.resonator_phases[g] = Some(phase);
    }
    for (a, c) in o.contacts().iter().enumerate() {
        let (from, to) = c.ends();
        let point_inputs = [
            outgoing(o, &centers, from, a),
            outgoing(o, &centers, to, a),
            point.states[a][0].as_slice(),
            point.states[a][1].as_slice(),
        ];
        let inputs = [
            outgoing(o, &bounds, from, a),
            outgoing(o, &bounds, to, a),
            error.states[a][0].as_slice(),
            error.states[a][1].as_slice(),
        ];
        let right = crate::hnn::propagation::transit_solve(
            c,
            h,
            point_inputs[0],
            point_inputs[1],
            point_inputs[2],
            point_inputs[3],
        )?
        .0;
        let re = maps.right(a, &inputs)?;
        let solved = solve_error(
            &c.solve()?,
            c.chart().map_or_else(Rat::zero, |c| c.certificate.clone()),
            &right,
            &re,
        )?;
        let n0 = inputs[0].len();
        let n1 = inputs[1].len();
        let n = c.width();
        let inputs = [
            solved.as_slice(),
            inputs[0],
            inputs[1],
            inputs[2],
            inputs[3],
        ];
        let image = maps.update(a, &inputs)?;
        next.arrivals[a] = [image[..n0].to_vec(), image[n0..n0 + n1].to_vec()];
        next.states[a] = [
            image[n0 + n1..n0 + n1 + n].to_vec(),
            image[n0 + n1 + n..].to_vec(),
        ];
    }
    Ok(next)
}

fn outgoing<'a>(o: &Operands, j: &'a [Junction], g: usize, a: usize) -> &'a [Rat] {
    &j[g].outgoing[o
        .incident(g)
        .iter()
        .position(|&i| i == a)
        .expect("an incident native contact")]
}

fn comparison_error(
    reads: &[ReceivingRead],
    errors: &[ChartedStationError],
    targets: &[usize],
    compared: &[bool],
    grain: u64,
) -> Result<Vec<Vec<Rat>>, HnnError> {
    reads
        .iter()
        .zip(errors)
        .enumerate()
        .map(|(j, (read, e))| {
            let mut radius = vec![Rat::zero(); read.logits.len()];
            if !compared[j] {
                return Ok(radius);
            }
            let classes = read.cells.len();
            let lower: Vec<_> = (0..classes)
                .map(|c| {
                    crate::receiver::face::GrainCell::of(
                        &(&read.logits[2 * c] - &e.logits[2 * c]),
                        grain,
                    )
                })
                .collect();
            let upper: Vec<_> = (0..classes)
                .map(|c| {
                    crate::receiver::face::GrainCell::of(
                        &(&read.logits[2 * c] + &e.logits[2 * c]),
                        grain,
                    )
                })
                .collect();
            if lower
                .iter()
                .zip(&upper)
                .any(|(l, u)| (l.carry.clone(), l.phase) != (u.carry.clone(), u.phase))
            {
                let top = upper.iter().map(|c| c.carry.clone()).max().unwrap();
                let weight = |c: &crate::receiver::face::GrainCell| -> Result<Rat, HnnError> {
                    Ok(CarriedPower::new(&c.carry - &top, c.phase, grain)?.odometer()?)
                };
                let lo = lower.iter().map(&weight).collect::<Result<Vec<_>, _>>()?;
                let hi = upper.iter().map(&weight).collect::<Result<Vec<_>, _>>()?;
                let masses = crate::hnn::ratio::Face::of_read(read, grain)?.odometer_masses()?;
                for c in 0..classes {
                    let lower = &lo[c]
                        / (&lo[c]
                            + hi.iter()
                                .enumerate()
                                .filter(|(d, _)| *d != c)
                                .map(|(_, w)| w)
                                .sum::<Rat>());
                    let upper = &hi[c]
                        / (&hi[c]
                            + lo.iter()
                                .enumerate()
                                .filter(|(d, _)| *d != c)
                                .map(|(_, w)| w)
                                .sum::<Rat>());
                    radius[2 * c] = (&masses[c] - lower).abs().max((upper - &masses[c]).abs());
                }
            }
            radius[2 * targets[j] + 1] = &e.logits[2 * targets[j] + 1] / crate::ratio::integer(4);
            Ok(radius)
        })
        .collect()
}

// The actual paired return supplies R's features in the passage frame. No receiving inverse or
// authored feature is substituted, and the transient back is dropped after composition.
fn receiving_error(
    field: &Field,
    phases: &ReceivingPhases,
    back: &WordReturn,
    errors: &[ChartedStationError],
    g: &RatioCovector,
    ge: &[Vec<Rat>],
    compared: &[bool],
) -> Result<ExactRatMatrix, HnnError> {
    let n = field.ring(phases.ring()).width();
    let rows = 2 * field.alphabet();
    let mut bound = vec![vec![Rat::zero(); n]; rows];
    for j in (0..compared.len()).filter(|&j| compared[j]) {
        let feature = &back.reads[j].0;
        let fe = transport_radius(&errors[j].anchor);
        for r in 0..rows {
            for c in 0..n {
                bound[r][c] += g.logits()[j][r].abs() * &fe[c]
                    + &ge[j][r] * feature[c].abs()
                    + &ge[j][r] * &fe[c];
            }
        }
    }
    Ok(ExactRatMatrix::shaped(rows, n, bound)?)
}

fn source_return_error(
    field: &Field,
    material: &Constitution,
    phases: &ReceivingPhases,
    operands: &Operands,
    opened_at: usize,
    g: &RatioCovector,
    ge: &[Vec<Rat>],
    back: &WordReturn,
) -> Result<(Vec<Vec<Rat>>, Vec<Vec<Rat>>), HnnError> {
    // [agent-inferred] These columns are the unsplit linear response of the producing
    // charts, not transient hardware Words. Re-represent the SAME Xhat and weights as exact
    // integer rows before their rational coordinates outgrow the i64 input carrier. No inverse,
    // refinement, certificate, tolerance or actual forward/adjoint operand is replaced.
    let linear = operands.clone().unsplit()?;
    source_return_error_on(field, material, phases, &linear, opened_at, g, ge, back)
}

fn source_return_error_on(
    field: &Field,
    material: &Constitution,
    phases: &ReceivingPhases,
    operands: &Operands,
    opened_at: usize,
    g: &RatioCovector,
    ge: &[Vec<Rat>],
    back: &WordReturn,
) -> Result<(Vec<Vec<Rat>>, Vec<Vec<Rat>>), HnnError> {
    let mut error: Vec<_> = field
        .rings()
        .iter()
        .map(|r| vec![Rat::zero(); r.width()])
        .collect();
    let mut rounding = error.clone();
    let mut radius_maps = ContactRadiusMaps::new(operands);
    for &ring in field.sources() {
        for coordinate in 0..field.ring(ring).width() {
            let mut point = EndChange::rest(field, operands);
            point.storage[ring][coordinate] = Rat::one();
            let mut radius = EndChange::rest(field, operands);
            let (mut paired, mut bound) = (Rat::zero(), Rat::zero());
            for crossing in 0..phases.junction_steps() {
                let centers = physical_signed_junctions(operands, &point)?;
                let errors = junction_error(operands, &point, &radius)?;
                if crossing >= phases.first_epoch() && crossing <= phases.last_epoch() {
                    let j = crossing - phases.first_epoch();
                    let logits = phases
                        .read(field, material, &centers[phases.ring()].anchor)?
                        .logits;
                    let le = matrix_radius(
                        material.receiving_map(phases.ring()).ok_or(
                            HnnError::MissingReceivingMap {
                                ring: phases.ring(),
                            },
                        )?,
                        &transport_radius(&errors[phases.ring()].anchor),
                    )?;
                    paired += dot(&g.logits()[j], &logits);
                    bound += logits
                        .iter()
                        .zip(le)
                        .zip(g.logits()[j].iter().zip(&ge[j]))
                        .map(|((l, e), (g, ge))| &e * g.abs() + (l.abs() + e) * ge)
                        .sum::<Rat>();
                }
                if crossing + 1 < phases.junction_steps() {
                    radius =
                        tick_error_cached(&mut radius_maps, &point, &radius, opened_at + crossing)?;
                    point = physical_signed_tick(operands, &point, opened_at + crossing)?;
                }
            }
            rounding[ring][coordinate] = (&back.opening[ring][coordinate] - paired).abs();
            error[ring][coordinate] = bound + &rounding[ring][coordinate];
        }
    }
    Ok((error, rounding))
}

fn matrix_pairing_radius(error: &ExactRatMatrix, delta: &ExactRatMatrix) -> Result<Rat, HnnError> {
    Ok(error
        .entries()
        .iter()
        .zip(delta.entries())
        .map(|(e, d)| e * d.abs())
        .sum())
}

fn same_interior(field: &Field, a: &Constitution, b: &Constitution) -> bool {
    field.rings().iter().enumerate().all(|(g, _)| {
        a.standing(g) == b.standing(g)
            && a.passive_factor(g) == b.passive_factor(g)
            && a.contrast_port(g) == b.contrast_port(g)
            && a.slices(g) == b.slices(g)
            && a.source_port(g) == b.source_port(g)
            && a.ring_resonator(g) == b.ring_resonator(g)
            && a.transport(g) == b.transport(g)
            && field
                .offsets()
                .iter()
                .all(|&d| a.pair_port(g, d) == b.pair_port(g, d))
    }) && field.contacts().iter().enumerate().all(|(a_index, _)| {
        a.contact_storage(a_index) == b.contact_storage(a_index)
            && a.contact_stiffness(a_index) == b.contact_stiffness(a_index)
            && a.contact_dissipation(a_index) == b.contact_dissipation(a_index)
            && a.contact_stiffness_signature(a_index) == b.contact_stiffness_signature(a_index)
            && a.contact_surface_storage(a_index) == b.contact_surface_storage(a_index)
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
    use crate::hnn::field::{
        ContactDeclaration, CribDeclaration, FieldDeclaration, RingDeclaration,
    };
    use crate::holarchy::terrain::{CyclicLaw, KnownTruth};
    use crate::ratio::{integer, rat};

    // Exact operands of the formerly refused matched first comparison, not a new source family.
    fn matched_field() -> Field {
        let ring = |lock| RingDeclaration {
            period: 4,
            screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
            placements: (0..4)
                .map(|node| FieldDeclaration::quarter_turn(node, 4))
                .collect(),
            lock,
            reflector: vec![0, 3, 2, 1],
            admittance: integer(2),
            initial: 0,
        };
        let contact = |from, to| ContactDeclaration {
            from,
            to,
            channel: (0..4).map(|node| (node, node)).collect(),
            admittance: integer(2),
            exponent: Rat::zero(),
        };
        Field::declare(
            FieldDeclaration {
                founded: Vec::new(),
                founding: false,
                rings: vec![ring((0..4).collect()), ring(Vec::new()), ring(Vec::new())],
                contacts: vec![contact(0, 1), contact(1, 2)],
                loops: Vec::new(),
                sources: vec![0],
                offsets: vec![1, 2, 3],
                alphabet: 4,
                step: integer(1),
                exponent_grain: 1,
                receivers: vec![ReceiverDeclaration {
                    ring: 0,
                    aperture: 3,
                    tolerance: rat(1, 16),
                    depth: 1,
                    prior: StopPrior::half(),
                    mass: 1,
                    base: BaseMeasure::Even,
                    receiving_prior: 0,
                }],
                crib: CribDeclaration {
                    window: 16,
                    offset: 1,
                },
                population: 1 << 16,
                lattice: Default::default(),
            }
            .by_lattice_rule(),
        )
        .unwrap()
    }

    #[test]
    fn contact_radius_faces_reuse_the_same_native_images_under_one_producing_word() {
        let field = matched_field();
        let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        let source = SourceMoment::open_with(&field, &current, &theta).unwrap();
        let mut charts = Charts::new();
        let (word, _) = Word::open_charted_received(
            &field,
            &theta,
            &current,
            &source,
            &mut charts,
            &WordOpening::Rest,
        )
        .unwrap();
        let linear = word.operands().clone().unsplit().unwrap();
        let mut faces = ContactRadiusMaps::new(&linear);
        let mut total = 0;
        for (a, c) in linear.contacts().iter().enumerate() {
            let (from, to) = c.ends();
            let n0 = linear.rings()[from].width();
            let n1 = linear.rings()[to].width();
            let n = c.width();
            let shape = [n0, n1, n, n];
            let values: Vec<_> = shape.iter().map(|&width| vec![Rat::one(); width]).collect();
            let inputs: Vec<_> = values.iter().map(Vec::as_slice).collect();
            let raw = |b: &[Vec<Rat>]| {
                Ok(crate::hnn::propagation::transit_solve(
                    c,
                    linear.step(),
                    &b[0],
                    &b[1],
                    &b[2],
                    &b[3],
                )?
                .0)
            };
            let expected = physical_linear_radius(&inputs, n, &raw).unwrap();
            assert_eq!(faces.right(a, &inputs).unwrap(), expected);
            total += shape.iter().sum::<usize>();
            assert_eq!(faces.located_columns(), total);
            let changed: Vec<_> = values.iter().map(|row| scale(&integer(3), row)).collect();
            let inputs: Vec<_> = changed.iter().map(Vec::as_slice).collect();
            assert_eq!(
                faces.right(a, &inputs).unwrap(),
                physical_linear_radius(&inputs, n, &raw).unwrap()
            );
            assert_eq!(
                faces.located_columns(),
                total,
                "fresh radius uses already located coefficient columns"
            );
            let shape = [n, n0, n1, n, n];
            let values: Vec<_> = shape.iter().map(|&width| vec![Rat::one(); width]).collect();
            let inputs: Vec<_> = values.iter().map(Vec::as_slice).collect();
            let raw = |b: &[Vec<Rat>]| {
                let p = crate::hnn::propagation::transit_update(
                    c,
                    linear.step(),
                    &b[0],
                    &b[1],
                    &b[2],
                    &b[3],
                    &b[4],
                );
                Ok([p.arrive_from, p.arrive_to, p.displacement, p.rate].concat())
            };
            assert_eq!(
                faces.update(a, &inputs).unwrap(),
                physical_linear_radius(&inputs, n0 + n1 + 2 * n, &raw).unwrap()
            );
            total += shape.iter().sum::<usize>();
            assert_eq!(faces.located_columns(), total);
            assert_eq!(
                faces.update(a, &inputs).unwrap(),
                physical_linear_radius(&inputs, n0 + n1 + 2 * n, &raw).unwrap()
            );
            assert_eq!(faces.located_columns(), total);
        }
        let fresh = ContactRadiusMaps::new(&linear);
        assert_eq!(
            fresh.located_columns(),
            0,
            "a new producing face never inherits a previous word's coefficients"
        );
        println!(
            "exact contact radius columns located={total}; repeated applications locate no further columns; no forward tick removed"
        );
        drop(word);
    }

    #[test]
    fn source_response_re_represents_the_producing_chart() {
        let started = std::time::Instant::now();
        let field = matched_field();
        let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        let receiver = ReceiverDeclaration {
            aperture: 4,
            ..field.receivers()[0].clone()
        };
        let phases = ReceivingPhases::declare(&field, &theta, &current, &receiver).unwrap();
        let truth =
            KnownTruth::cyclic_class_orbit(CyclicLaw::OrderTwo { opening: 2 }, 4, 20261006001, 4)
                .unwrap();
        let observed = Encoded::identity(&truth, &field).unwrap().remove(0);
        let damaged = DamagedSection::damage(&observed, &[2]).unwrap();
        assert_eq!(damaged.placed(), vec![Some(2), Some(2), None, Some(3)]);
        let mut charts = Charts::new();
        let pending = predict(
            &field,
            &theta,
            &current,
            &damaged,
            &WordOpening::Rest,
            None,
            &phases,
            &mut charts,
        )
        .unwrap();
        println!(
            "same matched blind cells={:?}; actual ticks={}; producing charts={:?}",
            pending.prediction().cells,
            pending.prediction().carry.ticks,
            pending.error().charts
        );
        assert!(matches!(
            pending.prediction().cells[2],
            RepairedCell::Held { .. }
        ));
        let compared = [false, false, true, false];
        let reads: Vec<_> = pending
            .prediction()
            .reads
            .iter()
            .map(|r| r.read.clone())
            .collect();
        let targets: Vec<_> = observed.classes_read().collect();
        let ratio = HolonRatio::compare_partition(
            Faces::of_reads(&reads, phases.grain()).unwrap(),
            &targets,
            &target_phases(&field, current.lift(), 0, &observed).unwrap(),
            &compared,
        )
        .unwrap();
        let g = ratio.covector().unwrap();
        let ge = comparison_error(
            &reads,
            &pending.error.stations,
            &targets,
            &compared,
            phases.grain(),
        )
        .unwrap();
        let word = &pending.pending.word;
        // pull_back consumes its Word. This explicit native return control opens from the
        // SAME blind source and cold charts; the original Word remains for observe below.
        // Its construction, passage and return cost belong to this falsifier, not a speed read.
        let control_started = std::time::Instant::now();
        let mut control_charts = Charts::new();
        let (mut control, control_opening) = crate::hnn::word::Word::open_charted_received(
            &field,
            &theta,
            &current,
            &pending.pending.source,
            &mut control_charts,
            &WordOpening::Rest,
        )
        .unwrap();
        for _ in 1..phases.junction_steps() {
            control.tick().unwrap();
        }
        // The terminal junction emits another exchange. change() reads the continuing motion
        // only before that junction; afterward its legitimate receipt is reception_end().
        assert!(!control.is_ended());
        let control_before_terminal = control.change().unwrap();
        control.last_junction().unwrap();
        assert!(control.is_ended() && word.is_ended());
        assert_eq!(control_opening, pending.error.opening);
        assert!(control_opening.closes());
        assert_eq!(control.operands(), word.operands());
        assert_eq!(control.opened_at(), word.opened_at());
        assert_eq!(control.clock().ticks(), word.clock().ticks());
        assert_eq!(control.recorded(), word.recorded());
        let control_carry = control.reception_end().unwrap();
        assert_eq!(control_before_terminal, pending.prediction().carry.change);
        assert_eq!(control_carry.change, control_before_terminal);
        assert_eq!(control_carry, pending.prediction().carry);
        assert_eq!(control_carry, word.reception_end().unwrap());
        assert_eq!(control.released().unwrap(), word.released().unwrap());
        let back = control
            .pull_back(&g, theta.receiving_map(0).unwrap(), &phases)
            .unwrap();
        println!(
            "explicit identical native return control: opening_operands_clock_passage_change_carry_release_equal=true; control_setup_forward_identity_and_return_ns={}",
            control_started.elapsed().as_nanos()
        );
        let operands = word.operands();
        let opened_at = word.opened_at();
        // The per-limb operand representation now admits the response that exceeded
        // the former i64 numerator carrier. Certify its complete error/rounding result
        // against the existing exact unsplit oracle below, rather than expecting refusal.
        let widened =
            source_return_error_on(&field, &theta, &phases, operands, opened_at, &g, &ge, &back)
                .unwrap();
        let linear = operands.clone().unsplit().unwrap();
        assert_eq!(linear.charts(), operands.charts());
        for (r, l) in operands.rings().iter().zip(linear.rings()) {
            assert_eq!(r.solve().unwrap(), l.solve().unwrap());
        }
        for (r, l) in operands.contacts().iter().zip(linear.contacts()) {
            assert_eq!(r.solve().unwrap(), l.solve().unwrap());
        }
        for ring in 0..field.rings().len() {
            assert_eq!(operands.weights(ring), linear.weights(ring));
        }
        let changed =
            source_return_error(&field, &theta, &phases, operands, opened_at, &g, &ge, &back)
                .unwrap();
        assert_eq!(
            changed,
            source_return_error_on(&field, &theta, &phases, &linear, opened_at, &g, &ge, &back)
                .unwrap()
        );
        assert_eq!(widened, changed);
        // Both representations execute the same producing chart; no target enters the
        // response calculus. Primitive single-word refusal is tested in chart.rs.
        let tolerance = ChartedTolerance {
            logits: rat(1, 16),
            receiving_covector: rat(1, 16),
            source_covector: rat(1, 16),
        };
        let publication = pending
            .observe(&theta, &observed, &compared, &tolerance)
            .unwrap_or_else(|(_, e)| panic!("same first observed comparison refused: {e:?}"));
        assert_eq!(publication.error.source_opening, back.opening);
        assert_eq!(publication.error.return_remainders, back.released);
        assert!(publication.error.applied.holds());
        assert!(publication.error.applied.decrease > Rat::zero());
        assert_eq!(
            publication.error.tolerance.source_covector,
            tolerance.source_covector
        );
        assert!(publication.teaching.publication.stepped > 0);
        assert!(publication.teaching.prediction.word.closes());
        assert!(
            publication
                .teaching
                .prediction
                .balances
                .iter()
                .all(|b| b.closes())
        );
        println!(
            "changed matched comparison: commit={}; source_error={:?}; source_rounding={:?}; applied={:?}; chart_starts={:?}; elapsed_ns={}",
            publication.teaching.publication.commit,
            publication.error.source_covectors,
            publication.error.source_rounding,
            publication.error.applied,
            linear
                .charts()
                .iter()
                .map(|r| (r.start, r.steps))
                .collect::<Vec<(ChartStart, u32)>>(),
            started.elapsed().as_nanos()
        );
    }
}
