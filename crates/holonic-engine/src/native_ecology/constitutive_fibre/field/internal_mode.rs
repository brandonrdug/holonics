//! A descended generator for two distinct internal currents with the same complete root drive.
//! The shared present prefix cancels before numerical evaluation. One amplitude/fibre remains.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_section, read_blob,
};
use std::io::{Read, Write};

#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct ModeOrigin {
    root_nodes: usize,
    source_occurrences: [usize; 2],
    receiving_occurrences: [usize; 2],
    captured_at: usize,
}
struct ModeData<'c> {
    surface: &'c ResidentSurface<'c>,
    owner: Option<Rc<()>>,
    origin: ModeOrigin,
    contact: ResidentSection<'c>,
    amplitude: ResidentSection<'c>,
}

/// Source-independent model of the declared receiver q=b_left-b_right. This is neither a copy
/// of the ecology nor a claim that the two contacts or their histories are the same holon.
pub struct NativeSharedDriveMode<'c> {
    inner: Rc<ModeData<'c>>,
}
pub struct NativeSharedDriveModeReturn<'c> {
    origin: Rc<ModeData<'c>>,
    report: ResidentSection<'c>,
    steps: u64,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct NativeSharedDriveModeReading {
    pub source_occurrences: [usize; 2],
    pub receiving_occurrences: [usize; 2],
    pub captured_at: usize,
    pub steps: u64,
    pub root_contact: Vec<ExactComplexWaveCurrent>,
    pub current: NativeFieldCurrentBall,
    pub point_availability: NativeInternalPointAvailability,
}

/// A cold generator chart, not another continuing ecology. It carries its amplitude once.
pub struct NativeSharedDriveModeRest {
    origin: ModeOrigin,
    contact: ResidentSectionRest,
    amplitude: ResidentSectionRest,
}
impl NativeSharedDriveModeRest {
    fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        let o = &self.origin;
        let width = o
            .root_nodes
            .checked_mul(6)
            .and_then(|n| n.checked_add(1))
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if o.root_nodes == 0
            || o.receiving_occurrences[0] == o.receiving_occurrences[1]
            || (0..2).any(|i| {
                o.source_occurrences[i] >= o.receiving_occurrences[i]
                    || o.receiving_occurrences[i] > o.captured_at
            })
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        point_section(&self.contact, 1, width)?;
        point_section(&self.amplitude, 1, 12)?;
        let contact = material_transport::wides(&self.contact.intervals)?;
        let v = material_transport::wides(&self.amplitude.intervals[..8])?;
        if *contact.last().ok_or(ConstitutiveFibreError::Shape)? <= 0 || v[2] < 0 || v[3] <= 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let fits = |x: i128| i64::try_from(x).is_ok();
        let point = if v[2] != 0 {
            vec![0, 0, 1, 1]
        } else if fits(v[0]) && fits(v[1]) && fits(v[3]) {
            vec![v[0] as i64, v[1] as i64, v[3] as i64, 0]
        } else {
            vec![0, 0, 1, 2]
        };
        if self.amplitude.intervals[8..].iter().map(|p| p.0).ne(point) {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        self.validate()?;
        out.write_all(b"HNA-SHARED-DRIVE-MODE\x01")
            .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?;
        blob(
            out,
            &serde_json::to_vec(&self.origin)
                .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?,
        )?;
        blob(out, &rest::point_bytes(&self.contact)?)?;
        blob(out, &rest::point_bytes(&self.amplitude)?)?;
        Ok(())
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, b"HNA-SHARED-DRIVE-MODE\x01")?;
        let origin = serde_json::from_slice(&read_blob(&mut input)?)
            .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?;
        let contact = rest::read_point(&read_blob(&mut input)?)?;
        let amplitude = rest::read_point(&read_blob(&mut input)?)?;
        if input.limit() != 0 {
            return Err(ConstitutiveFibreError::Rest(
                "trailing shared-drive mode data".into(),
            ));
        }
        let value = Self {
            origin,
            contact,
            amplitude,
        };
        value.validate()?;
        Ok(value)
    }
}

impl<'c> NativeSharedDriveMode<'c> {
    pub(super) fn material_origin(&self, owner: &Rc<()>) -> Option<([usize; 2], usize)> {
        self.inner
            .owner
            .as_ref()
            .filter(|o| Rc::ptr_eq(o, owner))
            .map(|_| {
                (
                    self.inner.origin.receiving_occurrences,
                    self.inner.origin.captured_at,
                )
            })
    }
    pub(super) fn share_origin(&self) -> Self {
        Self {
            inner: Rc::clone(&self.inner),
        }
    }
    pub(super) fn native_parts(&self) -> (&ResidentSection<'c>, &ResidentSection<'c>) {
        (&self.inner.contact, &self.inner.amplitude)
    }
    /// Predict after this many ordinary field occurrences, under the certified shared-drive
    /// family. The forcing and any added contacts may vary; the two old root drives stay fixed.
    /// This predicts a continuation, not a claim that a physical field has executed those steps.
    pub fn unfold(
        &self,
        steps: u64,
    ) -> Result<NativeSharedDriveModeReturn<'c>, ConstitutiveFibreError> {
        let s = self.inner.surface;
        let report = s.fresh_section(1, 12, ResidentGrain(0))?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_internal_mode_unfold(&lane, &self.inner.amplitude, steps, &report)?;
        }
        passage.close(0, &report, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "shared-drive unfolding: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeSharedDriveModeReturn {
            origin: Rc::clone(&self.inner),
            report,
            steps,
        })
    }
    pub fn rest(&self) -> Result<NativeSharedDriveModeRest, ConstitutiveFibreError> {
        let o = &self.inner.origin;
        let r = NativeSharedDriveModeRest {
            origin: ModeOrigin {
                root_nodes: o.root_nodes,
                source_occurrences: o.source_occurrences,
                receiving_occurrences: o.receiving_occurrences,
                captured_at: o.captured_at,
            },
            contact: self.inner.surface.detach_section(&self.inner.contact, 64)?,
            amplitude: self
                .inner
                .surface
                .detach_section(&self.inner.amplitude, 64)?,
        };
        r.validate()?;
        Ok(r)
    }
    pub fn remount(
        surface: &'c ResidentSurface<'c>,
        rest: NativeSharedDriveModeRest,
    ) -> Result<Self, ConstitutiveFibreError> {
        rest.validate()?;
        Ok(Self {
            inner: Rc::new(ModeData {
                surface,
                owner: None,
                origin: rest.origin,
                contact: surface.mount_section_rest(&rest.contact)?,
                amplitude: surface.mount_section_rest(&rest.amplitude)?,
            }),
        })
    }
}
impl<'c> NativeSharedDriveModeReturn<'c> {
    pub fn current(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        ResidentConstitutiveCurrent {
            section: &self.report,
            offset: 8,
            width: 2,
            denominator: Some(10),
            disposition: Some(11),
        }
    }
    pub fn inspect(&self) -> Result<NativeSharedDriveModeReading, ConstitutiveFibreError> {
        let (root_contact, current, point_availability) = internal_current::inspect_sections(
            self.origin.surface,
            &self.origin.contact,
            &self.report,
        )?;
        let o = &self.origin.origin;
        Ok(NativeSharedDriveModeReading {
            source_occurrences: o.source_occurrences,
            receiving_occurrences: o.receiving_occurrences,
            captured_at: o.captured_at,
            steps: self.steps,
            root_contact,
            current,
            point_availability,
        })
    }
}

impl<'c> NativeConstitutiveField<'c> {
    /// Derive q=b_left-b_right only after native equality of their full root coupling vectors.
    /// q's Preimage Fibre leaves their common component and all other internal currents free.
    /// No source identity is inferred from equal couplings; both actual birth histories survive.
    pub fn condense_shared_drive_mode(
        &mut self,
        left: usize,
        right: usize,
    ) -> Result<NativeSharedDriveMode<'c>, ConstitutiveFibreError> {
        if self.junction.as_ref().and_then(|j|j.operative.as_ref()).is_some_and(|o|!o.is_fixed()) {
            return Err(ConstitutiveFibreError::Rest("the fixed-drive quotient does not cover changed operative contacts".into()));
        }
        if left == right {
            return Err(ConstitutiveFibreError::Shape);
        }
        let right_prefix = right
            .checked_sub(1)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        if right >= self.history.len() || self.history[right].lineage.observed_source().is_none() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        // Cancel the shared CURRENT prefix symbolically. Only the two birth prefixes remain.
        let (ls, contact, amplitude) = self.internal_current_section(left, right_prefix)?;
        let (rs, right_contact, _) = self.internal_current_section(right, right_prefix)?;
        let s = self.relation.surface;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_internal_shared_drive(&lane, &contact, &right_contact)?;
        }
        passage.close(0, &amplitude, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "mode requires equal complete root drives: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeSharedDriveMode {
            inner: Rc::new(ModeData {
                surface: s,
                owner: Some(Rc::clone(&self.owner)),
                origin: ModeOrigin {
                    root_nodes: self.nodes(),
                    source_occurrences: [ls, rs],
                    receiving_occurrences: [left, right],
                    captured_at: self.history.len() - 1,
                },
                contact,
                amplitude,
            }),
        })
    }
}

#[cfg(test)]
mod tests;
