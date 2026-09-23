//! **The one passage receipt of the normal wave Holon** (plan phase 9, motion facet).
//!
//! [definition; agent-inferred] Every motion of the wave that is not the free word `advance`
//! — a source actuation, a material development, the reception of an actual next current, the
//! read-only normal-reference continuation, the one-cut pullback of a pending prediction and a
//! change of operator-family transport — returns this one receipt, as every motion of a core
//! `HolonLaw` returns one `Advance`. It carries the predecessor and successor points of the
//! Holon (their generating fibres) and, by kind, the operands the passage read: the joint it read
//! and produced, the borrowed source section, the received current, the observed comparand and
//! the resident normal report. The former per-operation receipts (`NormalSourceActuation`,
//! `NormalWaveDevelopment`, `NormalWaveReception`, `NormalWaveReference`,
//! `NormalWaveComparison`, `NormalWaveTransportChange`) are this type; their readings are
//! [`NormalWavePassageReading`].
use super::*;

/// The one passage receipt (see the module header).
pub struct NormalWavePassage<'a, 'c> {
    pub kind: NormalPassageKind,
    pub predecessor_fibre: NormalWaveFibre<'c>,
    pub successor_fibre: NormalWaveFibre<'c>,
    /// Develop and pullback: whether the held word was rebased onto its joint enclosure.
    pub rebased_joint_enclosure: bool,
    /// Pullback: the pending prediction consumed.
    pub prediction: Option<u64>,
    pub(super) source_joint: Option<Rc<ResidentSection<'c>>>,
    pub(super) produced_joint: Option<Rc<ResidentSection<'c>>>,
    pub(super) source_state: Option<NormalWaveState<'c>>,
    pub(super) current: Option<NormalWaveCurrent<'c>>,
    pub(super) report: Option<ResidentSection<'c>>,
    pub(super) section: Option<ResidentConstitutiveSection<'a, 'c>>,
    pub(super) comparison: Option<ResidentNormalSectionReturn<'a, 'c>>,
    pub(super) observed: Option<ResidentConstitutiveCurrent<'a, 'c>>,
}

impl<'a, 'c> NormalWavePassage<'a, 'c> {
    pub(super) fn new(
        kind: NormalPassageKind,
        predecessor_fibre: NormalWaveFibre<'c>,
        successor_fibre: NormalWaveFibre<'c>,
    ) -> Self {
        Self {
            kind,
            predecessor_fibre,
            successor_fibre,
            rebased_joint_enclosure: false,
            prediction: None,
            source_joint: None,
            produced_joint: None,
            source_state: None,
            current: None,
            report: None,
            section: None,
            comparison: None,
            observed: None,
        }
    }
    pub fn predecessor_fibre(&self) -> &NormalWaveFibre<'c> {
        &self.predecessor_fibre
    }
    pub fn successor_fibre(&self) -> &NormalWaveFibre<'c> {
        &self.successor_fibre
    }
    fn joint_view<'r>(
        &'r self,
        section: &'r ResidentSection<'c>,
    ) -> ResidentNormalEnclosureView<'r, 'c> {
        let f = &self.successor_fibre;
        ResidentNormalEnclosureView {
            surface: f.surface,
            section,
            offset: 0,
            width: 4 * f.roots,
            grain: f.grain,
        }
    }
    /// The joint `(p, c)` the passage read (actuation: before; reception, reference and
    /// pullback: the source joint).
    pub fn source_joint(&self) -> Option<ResidentNormalEnclosureView<'_, 'c>> {
        self.source_joint.as_deref().map(|s| self.joint_view(s))
    }
    /// The joint the passage produced (actuation: after; reference: the reference next joint).
    pub fn produced_joint(&self) -> Option<ResidentNormalEnclosureView<'_, 'c>> {
        self.produced_joint.as_deref().map(|s| self.joint_view(s))
    }
    /// Actuation: the joint before the source word.
    pub fn before(&self) -> Option<ResidentNormalEnclosureView<'_, 'c>> {
        self.source_joint()
    }
    /// Actuation: the joint after the source word.
    pub fn after(&self) -> Option<ResidentNormalEnclosureView<'_, 'c>> {
        self.produced_joint()
    }
    /// Reception: the state whose joint was read.
    pub fn source_state(&self) -> Option<&NormalWaveState<'c>> {
        self.source_state.as_ref()
    }
    /// Reception: the received current occurrence.
    pub fn current(&self) -> Option<&NormalWaveCurrent<'c>> {
        self.current.as_ref()
    }
    /// Actuation: the borrowed source section.
    pub fn source_section(&self) -> Option<ResidentConstitutiveSection<'a, 'c>> {
        self.section
    }
    /// Development: the material comparison of the measured section.
    pub fn comparison(&self) -> Option<&ResidentNormalSectionReturn<'a, 'c>> {
        self.comparison.as_ref()
    }
    /// Pullback: the observed comparand.
    pub fn observed(&self) -> Option<ResidentConstitutiveCurrent<'_, 'c>> {
        self.observed
    }
    pub fn inspect(&self) -> Result<NormalWavePassageReading, ConstitutiveFibreError> {
        let f = &self.successor_fibre;
        let comparison = self
            .report
            .as_ref()
            .map(|report| {
                decode_report(
                    &f.surface.detach_section(report, i64::BITS)?,
                    f.roots,
                    f.roots,
                    f.grain.0,
                    true,
                )
            })
            .transpose()?;
        let producing_epoch = match (self.kind, self.prediction) {
            (NormalPassageKind::Pullback, Some(id)) => id - 1,
            _ => self.predecessor_fibre.epoch,
        };
        Ok(NormalWavePassageReading {
            kind: self.kind,
            prediction_id: self.prediction,
            producing_epoch,
            producing_transport: self.predecessor_fibre.transport,
            epoch: f.epoch,
            successor_transport: f.transport,
            source_joint: self.source_joint().map(|v| v.inspect()).transpose()?,
            produced_joint: self.produced_joint().map(|v| v.inspect()).transpose()?,
            comparison,
        })
    }
}
