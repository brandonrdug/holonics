//! A receiving chart of the existing analytic geometry, compiled into native incidence.
//! Supports, shared junctions, phase arcs and their source events are validated by
//! ExactAnalyticFieldWaveLaw; this adapter supplies no alternative torus/contact definition.
mod placement;
pub mod machine;
pub mod machine_factor;
use super::NativeSessionError;
use holonic_engine::{
    AnalyticFieldJunctionId, CausalFieldStanding, DimensionalWaveModeId, ExactAnalyticFieldArc,
    ExactAnalyticFieldJunction, ExactAnalyticFieldMode, ExactAnalyticFieldWaveLaw,
    ExactWavePhaseTransport,
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

/// Supplied geometry and receiving chart. The model infers its reaction material; geometry,
/// phase transport, beta and the finite refinement aperture remain declared operands here.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeometricFieldSpec {
    pub field: CausalFieldStanding,
    pub junctions: Vec<ExactAnalyticFieldJunction>,
    pub arcs: Vec<ExactAnalyticFieldArc>,
    pub modes: Vec<ExactAnalyticFieldMode>,
    pub mode: DimensionalWaveModeId,
    /// The exterior source/receiving chart's ordered slots, not a native identity of words.
    pub slot_junctions: Vec<AnalyticFieldJunctionId>,
    /// A local retained-current comparison in addition to the admitted incoming arcs.
    pub self_comparison: bool,
    pub beta_significand: i64,
    pub beta_exponent: i32,
    pub series_terms: u32,
    pub refinement_steps: usize,
    /// mu=2^-relaxation_bits, x_next=H seed+(I-H)((1-mu)seed+mu reaction).
    pub relaxation_bits: u32,
}
#[derive(Clone, Debug)]
pub(crate) struct GeometricRowGroup {
    pub receivers: Vec<usize>,
    pub sources: Vec<usize>,
    pub phases: Vec<ExactWavePhaseTransport>,
    pub neighbors: usize,
}
#[derive(Clone, Debug)]
pub(crate) struct CompiledFieldGeometry {
    placement: std::cell::OnceCell<(
        usize,
        usize,
        holonic_engine::hardware_cover::ModeIdentity,
        serde_json::Value,
    )>,
    pub groups: Vec<GeometricRowGroup>,
    pub rows: usize,
    pub condition_complex: usize,
    pub slot_rows: Vec<usize>,
    pub beta_significand: i64,
    pub beta_exponent: i32,
    pub series_terms: u32,
    pub steps: usize,
    pub relaxation_bits: u32,
}
impl GeometricFieldSpec {
    pub(crate) fn compile(&self) -> Result<CompiledFieldGeometry, NativeSessionError> {
        let invalid = |s: &str| NativeSessionError::Application(s.into());
        if self.refinement_steps == 0
            || self.relaxation_bits > 120
            || self.series_terms == 0
            || self.series_terms == u32::MAX
        {
            return Err(invalid("geometric refinement/series aperture"));
        }
        let law = ExactAnalyticFieldWaveLaw::new(
            self.field.clone(),
            self.junctions.clone(),
            self.arcs.clone(),
            self.modes.clone(),
        )
        .map_err(|e| NativeSessionError::Application(e.to_string()))?;
        if !law.modes().contains_key(&self.mode) {
            return Err(invalid("geometric field mode is outside its source law"));
        }
        let indices: BTreeMap<_, _> = law
            .junctions()
            .keys()
            .enumerate()
            .map(|(i, id)| (*id, i))
            .collect();
        let rows = indices.len();
        let mut incoming = vec![Vec::new(); rows];
        if self.self_comparison {
            for row in 0..rows {
                incoming[row].push((row, ExactWavePhaseTransport::identity()));
            }
        }
        for arc in law.arcs().values() {
            let phase = arc
                .modal_phase_step
                .get(&self.mode)
                .ok_or_else(|| invalid("arc does not carry the selected mode"))?
                .pow(arc.delay);
            incoming[indices[&arc.to]].push((indices[&arc.from], phase));
        }
        if incoming.iter().any(Vec::is_empty) {
            return Err(invalid("geometric receiving site has no admitted current"));
        }
        let condition_complex = incoming.iter().map(Vec::len).max().unwrap();
        let mut groups: BTreeMap<usize, GeometricRowGroup> = BTreeMap::new();
        for (receiver, ports) in incoming.into_iter().enumerate() {
            let degree = ports.len();
            let group = groups.entry(degree).or_insert_with(|| GeometricRowGroup {
                receivers: vec![],
                sources: vec![],
                phases: vec![],
                neighbors: degree,
            });
            group.receivers.push(receiver);
            for (source, phase) in ports {
                group.sources.push(source);
                group.phases.push(phase);
            }
        }
        let mut seen = BTreeSet::new();
        let slot_rows = self
            .slot_junctions
            .iter()
            .map(|id| {
                let row = *indices
                    .get(id)
                    .ok_or_else(|| invalid("receiving slot is not a geometric junction"))?;
                if !seen.insert(row) {
                    return Err(invalid("geometric source slots must be injective"));
                }
                Ok(row)
            })
            .collect::<Result<Vec<_>, _>>()?;
        if slot_rows.is_empty() {
            return Err(invalid("geometric receiving chart is empty"));
        }
        Ok(CompiledFieldGeometry {
            placement: std::cell::OnceCell::new(),
            groups: groups.into_values().collect(),
            rows,
            condition_complex,
            slot_rows,
            beta_significand: self.beta_significand,
            beta_exponent: self.beta_exponent,
            series_terms: self.series_terms,
            steps: self.refinement_steps,
            relaxation_bits: self.relaxation_bits,
        })
    }
}
