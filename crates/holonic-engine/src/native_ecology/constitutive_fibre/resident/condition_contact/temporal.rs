//! The existing unit-admittance contact on the structured temporal graph
//! F_y = {(h,e): R_S X_x h + e = y_S}. The free response directions and their
//! correlated unexplained return remain explicit; the graph is never made dense in S.

use super::ConditionContactMetric;
use crate::{
    native_ecology::constitutive_fibre::{ConstitutiveFibreError, ResidentConstitutiveCurrent},
    phase_current::{
        PhaseCurrentLineageId, PhaseCurrentReceiverId,
        resident::{
            PhaseComparisonSupport, ResidentEnclosedPhaseConvolution,
            ResidentEnclosedPhaseDifference, ResidentPhaseCurrentError, ResidentPhaseCurrentView,
            ResidentPhaseEnclosureView, compare_enclosed_resident, convolve_enclosed_resident,
            enclose_resident,
        },
    },
    resident_section::{ResidentGrain, ResidentSection, ResidentSurface},
};
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use std::{ops::Range, rc::Rc};

/// A caller-declared temporal response aperture and receiver chart, not semantic grains.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TemporalResponseChart {
    pub receiver: PhaseCurrentReceiverId,
    pub origin: Rat,
    pub sample_step: Rat,
    pub phase_extent: u32,
    pub raw_extent: usize,
}

impl TemporalResponseChart {
    fn view<'a, 'c>(
        &self,
        section: &'a ResidentSection<'c>,
        at: usize,
        grain: u32,
        lineage: PhaseCurrentLineageId,
    ) -> Result<ResidentPhaseEnclosureView<'a, 'c>, ResidentPhaseCurrentError> {
        ResidentPhaseEnclosureView::new(
            section,
            at,
            grain,
            self.receiver,
            lineage,
            self.origin.clone(),
            self.sample_step.clone(),
            self.phase_extent,
            self.raw_extent,
        )
    }
}

/// Immutable standing shares only its completed carrier and exact construction. The retained
/// Gram/adjoint coordinates suffice to reconstruct the response current; raw recording archives
/// are not a prerequisite of this decoder. Full recording-relative fibres belong to contacts.
struct TemporalStanding<'c> {
    section: ResidentSection<'c>,
    at: usize,
    cut: u64,
    lineage: PhaseCurrentLineageId,
    construction: TemporalConstruction<'c>,
}

enum TemporalConstruction<'c> {
    Initial(ResidentSection<'c>),
    Contact(Rc<TemporalStanding<'c>>),
}

/// An immutable producing cut, shareable while the single move owner receives later contacts.
#[derive(Clone)]
pub struct ResidentTemporalConditionSnapshot<'c> {
    standing: Rc<TemporalStanding<'c>>,
    owner: Rc<()>,
    chart: TemporalResponseChart,
    grain: u32,
}

impl<'c> ResidentTemporalConditionSnapshot<'c> {
    pub fn view(&self) -> ResidentPhaseEnclosureView<'_, 'c> {
        self.chart
            .view(
                &self.standing.section,
                self.standing.at,
                self.grain,
                self.standing.lineage,
            )
            .expect("completed temporal standing")
    }
    pub fn cut(&self) -> u64 {
        self.standing.cut
    }
    pub fn chart(&self) -> &TemporalResponseChart {
        &self.chart
    }
}

/// One move owner. Every contact stages the complete two-port return before publishing h'.
pub struct ResidentTemporalConditionCurrent<'c> {
    surface: &'c ResidentSurface<'c>,
    current: ResidentTemporalConditionSnapshot<'c>,
    metric: ConditionContactMetric,
}

/// The full implicit affine fibre, with the operation and comparison that actually produced it.
/// Every response h is paired with e=y-R_S Xh; no unexplained direction is asserted zero.
pub struct ResidentTemporalConditionPreimage<'a, 'c> {
    producing: &'a ResidentTemporalConditionSnapshot<'c>,
    forward: &'a ResidentEnclosedPhaseConvolution<'a, 'a, 'c>,
    difference: &'a ResidentEnclosedPhaseDifference<'a, 'a, 'c>,
}

fn same_carrier(
    a: &ResidentPhaseEnclosureView<'_, '_>,
    b: &ResidentPhaseEnclosureView<'_, '_>,
) -> bool {
    std::ptr::eq(a.section, b.section)
        && a.wide_offset == b.wide_offset
        && a.grain == b.grain
        && a.receiver == b.receiver
        && a.lineage == b.lineage
        && a.origin == b.origin
        && a.sample_step == b.sample_step
        && a.phase_extent == b.phase_extent
        && a.raw_extent == b.raw_extent
}

fn point_view<'a, 'c>(
    v: &ResidentPhaseCurrentView<'a, 'c>,
) -> Result<ResidentPhaseCurrentView<'a, 'c>, ResidentPhaseCurrentError> {
    ResidentPhaseCurrentView::new(
        v.current(),
        v.receiver(),
        v.lineage(),
        v.origin().clone(),
        v.sample_step().clone(),
        v.phase_extent(),
        v.raw_extent(),
    )
}

impl<'a, 'c> ResidentTemporalConditionPreimage<'a, 'c> {
    pub fn from_return(
        producing: &'a ResidentTemporalConditionSnapshot<'c>,
        forward: &'a ResidentEnclosedPhaseConvolution<'a, 'a, 'c>,
        difference: &'a ResidentEnclosedPhaseDifference<'a, 'a, 'c>,
    ) -> Result<Self, ResidentPhaseCurrentError> {
        if !same_carrier(&producing.view(), forward.response())
            || !same_carrier(&forward.view(), difference.predicted())
        {
            return Err(ResidentPhaseCurrentError::PredictionMismatch);
        }
        Ok(Self {
            producing,
            forward,
            difference,
        })
    }
    pub fn producing_cut(&self) -> u64 {
        self.producing.cut()
    }
    pub fn forward(&self) -> &ResidentEnclosedPhaseConvolution<'a, 'a, 'c> {
        self.forward
    }
    pub fn difference(&self) -> &ResidentEnclosedPhaseDifference<'a, 'a, 'c> {
        self.difference
    }
    pub fn support(&self) -> &PhaseComparisonSupport {
        self.difference.support()
    }

    /// Evaluate the correlated e leg for any supplied h in the declared chart. This executable
    /// graph presents all compatible pairs without enumerating or choosing a cause.
    pub fn unexplained_for(
        &self,
        surface: &'c ResidentSurface<'c>,
        candidate: ResidentPhaseEnclosureView<'_, 'c>,
        lineage: PhaseCurrentLineageId,
    ) -> Result<ResidentTemporalWaveReturn<'c>, ResidentPhaseCurrentError> {
        let c = self.producing.chart();
        if candidate.receiver() != c.receiver
            || candidate.origin() != &c.origin
            || candidate.sample_step() != &c.sample_step
            || candidate.phase_extent() != c.phase_extent
            || candidate.raw_extent() != c.raw_extent
        {
            return Err(ConstitutiveFibreError::Shape.into());
        }
        unexplained(surface, self, candidate, lineage)
    }
}

/// An owned completed enclosed waveform; no point-current conversion of its centre exists.
pub struct ResidentTemporalWaveReturn<'c> {
    section: ResidentSection<'c>,
    chart: TemporalResponseChart,
    grain: u32,
    lineage: PhaseCurrentLineageId,
}

impl<'c> ResidentTemporalWaveReturn<'c> {
    pub fn view(&self) -> ResidentPhaseEnclosureView<'_, 'c> {
        self.chart
            .view(&self.section, 0, self.grain, self.lineage)
            .expect("completed waveform")
    }
}

fn waveform_chart(view: &ResidentPhaseEnclosureView<'_, '_>) -> TemporalResponseChart {
    TemporalResponseChart {
        receiver: view.receiver(),
        origin: view.origin().clone(),
        sample_step: view.sample_step().clone(),
        phase_extent: view.phase_extent(),
        raw_extent: view.raw_extent(),
    }
}

fn unexplained<'c>(
    surface: &'c ResidentSurface<'c>,
    family: &ResidentTemporalConditionPreimage<'_, 'c>,
    h: ResidentPhaseEnclosureView<'_, 'c>,
    lineage: PhaseCurrentLineageId,
) -> Result<ResidentTemporalWaveReturn<'c>, ResidentPhaseCurrentError> {
    let prediction = convolve_enclosed_resident(
        surface,
        point_view(family.forward.source())?,
        h,
        family.forward.view().receiver(),
        lineage,
    )?;
    let result = compare_enclosed_resident(
        surface,
        prediction.view(),
        point_view(family.difference.observed())?,
        lineage,
    )?;
    let view = result.view();
    let chart = waveform_chart(&view);
    let grain = view.grain;
    Ok(ResidentTemporalWaveReturn {
        section: result.into_section(),
        chart,
        grain,
        lineage,
    })
}

/// Restriction of a complete resident waveform. The retained full radius bounds the restricted
/// Euclidean error too. Outside-S coordinates are retained operands, not normal-current entries.
pub struct ResidentTemporalRestrictedEnclosure<'a, 'c> {
    pub full: ResidentPhaseEnclosureView<'a, 'c>,
    pub range: Range<usize>,
}

/// Complete staged two-port return. The exact affine graph preserves the correlations among
/// h/e and the normal legs; the balls separately certify numerical representation error.
pub struct ResidentTemporalConditionContact<'a, 'c> {
    successor: ResidentTemporalConditionSnapshot<'c>,
    family: ResidentTemporalConditionPreimage<'a, 'c>,
    incoming_e: ResidentTemporalWaveReturn<'c>,
    returned_e_full: ResidentTemporalWaveReturn<'c>,
    successor_e: ResidentTemporalWaveReturn<'c>,
    metric: ConditionContactMetric,
}

impl<'c> ResidentTemporalConditionCurrent<'c> {
    /// Transfer an explicit initial rational section into the sole continuing owner. Its exact
    /// coordinates remain the initial construction, including a non-dyadic numerical enclosure.
    pub fn retain(
        surface: &'c ResidentSurface<'c>,
        initial: ResidentSection<'c>,
        chart: TemporalResponseChart,
        lineage: PhaseCurrentLineageId,
        grain: u32,
        metric: ConditionContactMetric,
    ) -> Result<Self, ResidentPhaseCurrentError> {
        let point = ResidentPhaseCurrentView::new(
            ResidentConstitutiveCurrent::rational(&initial)?,
            chart.receiver,
            lineage,
            chart.origin.clone(),
            chart.sample_step.clone(),
            chart.phase_extent,
            chart.raw_extent,
        )?;
        let enclosed = enclose_resident(surface, point, grain)?.into_section();
        let standing = Rc::new(TemporalStanding {
            section: enclosed,
            at: 0,
            cut: 0,
            lineage,
            construction: TemporalConstruction::Initial(initial),
        });
        Ok(Self {
            surface,
            current: ResidentTemporalConditionSnapshot {
                standing,
                owner: Rc::new(()),
                chart,
                grain,
            },
            metric,
        })
    }
    pub fn snapshot(&self) -> ResidentTemporalConditionSnapshot<'c> {
        self.current.clone()
    }
    pub fn contacts(&self) -> u64 {
        self.current.cut()
    }
    pub fn metric(&self) -> ConditionContactMetric {
        self.metric
    }

    /// Apply (z,Qa) -> (Pz+Qa,Qz) for z=(current h,0), a=(0,y),
    /// V=ker[R_S X,I]. An older producing cut is allowed, but its operation is not rewritten.
    pub fn contact<'a>(
        &mut self,
        family: ResidentTemporalConditionPreimage<'a, 'c>,
        lineage: PhaseCurrentLineageId,
    ) -> Result<ResidentTemporalConditionContact<'a, 'c>, ResidentPhaseCurrentError> {
        if !Rc::ptr_eq(&self.current.owner, &family.producing.owner)
            || self.current.chart != family.producing.chart
            || self.current.grain != family.producing.grain
        {
            return Err(ConstitutiveFibreError::Shape.into());
        }
        let next = self
            .contacts()
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let k = self.current.chart.raw_extent;
        let d = k.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let gram = d.checked_mul(d).ok_or(ConstitutiveFibreError::Shape)?;
        let workspace_values = gram
            .checked_mul(2)
            .and_then(|n| {
                d.checked_mul(6)
                    .and_then(|six_d| six_d.checked_add(5).and_then(|tail| n.checked_add(tail)))
            })
            .ok_or(ConstitutiveFibreError::Shape)?;
        let workspace_words = ResidentSurface::constitutive_wide_workspace_words(workspace_values)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let report_segment = d.checked_add(1).ok_or(ConstitutiveFibreError::Shape)?;
        let report_values = report_segment
            .checked_mul(8)
            .and_then(|n| n.checked_add(gram))
            .and_then(|n| d.checked_add(3).and_then(|tail| n.checked_add(tail)))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let report_words = report_values
            .checked_mul(2)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let workspace = self
            .surface
            .fresh_section(1, workspace_words, ResidentGrain(0))?;
        let report = self
            .surface
            .fresh_section(1, report_words, ResidentGrain(0))?;
        let support = family.support();
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_temporal_condition_contact(
                &lane,
                family.forward.source().current(),
                family.difference.observed().current(),
                family.forward.source().raw_extent(),
                k,
                support.predicted.start,
                support.observed.start,
                support.predicted.len(),
                family.difference.observed().raw_extent(),
                &self.current.standing.section,
                self.current.standing.at,
                self.current.grain,
                &workspace,
                &report,
            )?;
        }
        passage.close(0, &report, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "temporal condition contact: {:?}",
                receipt.obstruction
            ))
            .into());
        }
        let chart = &self.current.chart;
        let grain = self.current.grain;
        let block = |i| chart.view(&report, i * report_segment, grain, lineage);
        let incoming_e = unexplained(self.surface, &family, block(2)?, lineage)?;
        // Q(h0,0)=(h0-V,XV); the returned normal is not a point of the affine graph.
        let v_prediction = convolve_enclosed_resident(
            self.surface,
            point_view(family.forward.source())?,
            block(1)?,
            family.forward.view().receiver(),
            lineage,
        )?;
        let v_chart = waveform_chart(&v_prediction.view());
        let returned_e_full = ResidentTemporalWaveReturn {
            section: v_prediction.into_section(),
            chart: v_chart,
            grain,
            lineage,
        };
        let successor_e = unexplained(self.surface, &family, block(3)?, lineage)?;
        let standing = Rc::new(TemporalStanding {
            section: report,
            at: 3 * report_segment,
            cut: next,
            lineage,
            construction: TemporalConstruction::Contact(Rc::clone(&self.current.standing)),
        });
        let successor = ResidentTemporalConditionSnapshot {
            standing,
            owner: Rc::clone(&self.current.owner),
            chart: chart.clone(),
            grain,
        };
        let result = ResidentTemporalConditionContact {
            successor,
            family,
            incoming_e,
            returned_e_full,
            successor_e,
            metric: self.metric,
        };
        // No fallible stage follows publication. The complete contact, not just its coefficient
        // solve, must have returned before a later operation can see the new current.
        self.current = result.successor.clone();
        Ok(result)
    }
}

impl<'a, 'c> ResidentTemporalConditionContact<'a, 'c> {
    fn block(&self, index: usize) -> ResidentPhaseEnclosureView<'_, 'c> {
        let d = 2 * self.successor.chart.raw_extent;
        self.successor
            .chart
            .view(
                &self.successor.standing.section,
                index * (d + 1),
                self.successor.grain,
                self.successor.standing.lineage,
            )
            .expect("completed contact block")
    }
    pub fn family(&self) -> &ResidentTemporalConditionPreimage<'a, 'c> {
        &self.family
    }
    pub fn metric(&self) -> ConditionContactMetric {
        self.metric
    }
    pub fn current_cut(&self) -> u64 {
        self.successor.cut() - 1
    }
    pub fn successor_cut(&self) -> u64 {
        self.successor.cut()
    }
    pub fn predecessor(&self) -> ResidentPhaseEnclosureView<'_, 'c> {
        self.block(0)
    }
    pub fn successor(&self) -> ResidentPhaseEnclosureView<'_, 'c> {
        self.block(3)
    }
    pub fn incoming_normal_h(&self) -> ResidentPhaseEnclosureView<'_, 'c> {
        self.block(2)
    }
    pub fn returned_normal_h(&self) -> ResidentPhaseEnclosureView<'_, 'c> {
        self.block(4)
    }
    pub fn difference_h(&self) -> ResidentPhaseEnclosureView<'_, 'c> {
        self.block(5)
    }
    pub fn incoming_normal_e(&self) -> ResidentPhaseEnclosureView<'_, 'c> {
        self.incoming_e.view()
    }
    pub fn returned_normal_e(&self) -> ResidentTemporalRestrictedEnclosure<'_, 'c> {
        ResidentTemporalRestrictedEnclosure {
            full: self.returned_e_full.view(),
            range: self.family.support().predicted.clone(),
        }
    }
    pub fn unexplained(&self) -> ResidentPhaseEnclosureView<'_, 'c> {
        self.successor_e.view()
    }
}

mod inspect;
pub use inspect::ResidentTemporalConditionReading;
#[cfg(test)]
mod tests;
