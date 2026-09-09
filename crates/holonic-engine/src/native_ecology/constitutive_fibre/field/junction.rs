//! Paired passive junction on the field's root current chart.
//!
//! Each actual joined source/arrival adds the Hermitian moment d d*, with d=(source,-arrival).
//! The native junction acts through that moment and retained internal current. This is a declared
//! unit-admittance junction, not selection of one value from the separate constitutive fibre.

use super::*;

mod enclosure;
mod producer;
pub(super) mod operative;
pub use operative::{NativeOperativeCurrentFactorCondensation,NativeOperativeReturnStorage,NativeOperativeReflectionReading,NativeOperativeContactBirth, NativeOperativeContactReading, NativeOperativeContactStaging,
    NativeMaterialContactResponse, NativeMaterialContactResponseReading, NativeRetainedMaterialRelation, NativeMaterialContactStepComparison, NativeFiniteMaterialResponse, NativeContactRealization, NativeContactDepositReading};
pub use producer::{CausalContactPropagation, CausalContactPropagationCotangent, CausalContactPropagationEnclosure, PairedContactCotangent, PairedJunctionCotangent, PairedJunctionLinearization, PairedJunctionTangent,JointMaterialContactResponse,joint_material_contact};
pub use operative::{NativeCausalContactPropagation,NativeCausalContactPropagationReading,NativeCausalContactJoinReading};
#[cfg(test)]
mod solver_tests;
pub use enclosure::{
    NativeFieldCurrentBall, NativeFieldEnclosedJunctionReading, NativeFieldInternalCurrentBall,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(tag = "representation", rename_all = "kebab-case")]
pub enum NativeFieldJunctionRepresentation {
    RationalWords,
    EnclosedDyadic { fractional_bits: u32 },
}

/// Numerical factorization policy. Both policies certify the same complete root-current law.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeFieldJunctionSolver {
    Full,
    BalancedPairs,
}

impl NativeFieldJunctionRepresentation {
    pub(super) fn kernel(self) -> (u32, u32) {
        match self {
            Self::RationalWords => (1, 0),
            Self::EnclosedDyadic { fractional_bits } => (2, fractional_bits),
        }
    }
    fn report_words(self, width: usize) -> usize {
        match self {
            Self::RationalWords => 4 * (width + 1),
            Self::EnclosedDyadic { .. } => 12 * (width + 1),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", content = "reading", rename_all = "kebab-case")]
pub enum NativeFieldJunctionReading {
    Exact(NativeFieldExactJunctionReading),
    Enclosed(NativeFieldEnclosedJunctionReading),
    Operative(operative::NativeOperativeReflectionReading),
}

impl NativeFieldJunctionReading {
    pub fn exact(&self) -> Option<&NativeFieldExactJunctionReading> {
        match self {
            Self::Exact(value) => Some(value),
            _ => None,
        }
    }
    pub fn enclosed(&self) -> Option<&NativeFieldEnclosedJunctionReading> {
        match self {
            Self::Enclosed(value) => Some(value),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldExactJunctionReading {
    /// All three complex port blocks: two source branches per node, then the arriving-field port.
    pub potential: Vec<ExactComplexWaveCurrent>,
    pub outgoing: Vec<ExactComplexWaveCurrent>,
    /// R* b of the internal currents, sufficient for this junction's next boundary operation.
    pub held_current: Vec<ExactComplexWaveCurrent>,
    /// Alternating prefix of actual junction potentials. Together with each contact's birth
    /// prefix and source it decodes its actual internal current without choosing an inverse.
    pub potential_prefix: Vec<ExactComplexWaveCurrent>,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldInternalCurrent {
    pub source_occurrence: usize,
    pub receiving_occurrence: usize,
    /// Actual root contact vector, retaining all source and receiving coordinates.
    pub contact: Vec<ExactComplexWaveCurrent>,
    pub current: ExactComplexWaveCurrent,
}

pub(super) struct PairedJunction<'chart> {
    pub(super) representation: NativeFieldJunctionRepresentation,
    pub(super) solver: NativeFieldJunctionSolver,
    pub(super) covariance: ResidentSection<'chart>,
    pub(super) current: Rc<ResidentSection<'chart>>,
    pub(super) operative: Option<operative::OperativeState<'chart>>,
}

impl PairedJunction<'_> {
    pub(super) fn kernel(&self) -> (u32, u32) {
        let (mode, grain) = self.representation.kernel();
        (
            if mode == 2 && self.solver == NativeFieldJunctionSolver::BalancedPairs {
                3
            } else {
                mode
            },
            grain,
        )
    }
}

pub(super) struct PendingJunction<'chart> {
    pub(super) covariance: ResidentSection<'chart>,
    pub(super) report: Rc<ResidentSection<'chart>>,
    pub(super) operative: Option<operative::PendingOperative<'chart>>,
}

impl<'chart> NativeConstitutiveField<'chart> {
    /// Found the same field with a coupled passive junction. The initial paired moment and
    /// internal currents are zero. Unit port admittances specify this first junction chart;
    /// arbitrary unit-phase incidence and exact initial held currents remain admitted.
    pub fn found_with_paired_junction(
        surface: &'chart ResidentSurface<'chart>,
        material: Vec<NativeJunctionSeed>,
    ) -> Result<Self, ConstitutiveFibreError> {
        Self::found_with_junction_representation(
            surface,
            material,
            NativeFieldJunctionRepresentation::RationalWords,
        )
    }

    /// Represent the same unique junction current by a certified dyadic ball and its retained
    /// oriented residual trace. The numerical center is never reported as that exact current.
    pub fn found_with_enclosed_junction(
        surface: &'chart ResidentSurface<'chart>,
        material: Vec<NativeJunctionSeed>,
        grain: ResidentGrain,
    ) -> Result<Self, ConstitutiveFibreError> {
        if !(1..=120).contains(&grain.0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        Self::found_with_junction_representation(
            surface,
            material,
            NativeFieldJunctionRepresentation::EnclosedDyadic {
                fractional_bits: grain.0,
            },
        )
    }

    fn found_with_junction_representation(
        surface: &'chart ResidentSurface<'chart>,
        material: Vec<NativeJunctionSeed>,
        representation: NativeFieldJunctionRepresentation,
    ) -> Result<Self, ConstitutiveFibreError> {
        if material
            .iter()
            .any(|seed| seed.incoming_admittance != 1 || seed.held_admittance != 1)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut body = Self::found(surface, material)?;
        let width = body.relation.source_width + body.relation.target_width;
        let count = width
            .checked_mul(width)
            .and_then(|n| n.checked_add(1))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let mut covariance = vec![(0, 0); count];
        covariance[count - 1] = (1, 1);
        let mut report = vec![(0, 0); representation.report_words(width)];
        match representation {
            NativeFieldJunctionRepresentation::RationalWords => {
                for part in 0..4 {
                    report[part * (width + 1) + width] = (1, 1);
                }
            }
            NativeFieldJunctionRepresentation::EnclosedDyadic { .. } => {
                // The packed signed-wide C denominator is the report's final two wire words.
                let low = report.len() - 2;
                report[low] = (1, 1);
            }
        }
        let mount = |words: Vec<(i64, i64)>| -> Result<_, ConstitutiveFibreError> {
            Ok(surface.mount_section_rest(
                &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words)
                    .map_err(|_| ConstitutiveFibreError::Shape)?,
            )?)
        };
        body.junction = Some(PairedJunction {
            representation,
            solver: NativeFieldJunctionSolver::Full,
            covariance: mount(covariance)?,
            current: Rc::new(mount(report)?),
            operative: None,
        });
        Ok(body)
    }

    pub fn has_paired_junction(&self) -> bool {
        self.junction.is_some()
    }

    pub fn junction_representation(&self) -> Option<NativeFieldJunctionRepresentation> {
        self.junction
            .as_ref()
            .map(|junction| junction.representation)
    }

    pub fn junction_solver(&self) -> Option<NativeFieldJunctionSolver> {
        self.junction.as_ref().map(|junction| junction.solver)
    }

    /// Select a numerical factorization, without changing the exact current, morphology,
    /// history or receiving capabilities. The balanced policy uses the full solver when its
    /// exact covariance/RHS conditions do not hold. Arithmetic failures remain explicit.
    pub fn set_junction_solver(
        &mut self,
        solver: NativeFieldJunctionSolver,
    ) -> Result<(), ConstitutiveFibreError> {
        if self.has_operative_contacts() && solver!=NativeFieldJunctionSolver::Full {
            return Err(ConstitutiveFibreError::Rest("operative reflection currently uses the full numerical factorization".into()));
        }
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let junction = self
            .junction
            .as_mut()
            .ok_or(ConstitutiveFibreError::Shape)?;
        if !matches!(
            junction.representation,
            NativeFieldJunctionRepresentation::EnclosedDyadic { .. }
        ) {
            return Err(ConstitutiveFibreError::Shape);
        }
        junction.solver = solver;
        Ok(())
    }

    /// Explicit observers; these create no source or reaction capability.
    pub fn inspect_junction_covariance(
        &self,
    ) -> Result<Option<ResidentSectionRest>, ConstitutiveFibreError> {
        if self.has_operative_contacts() {return Err(ConstitutiveFibreError::Rest("operative covariance uses its complex enclosure receiver".into()));}
        self.junction
            .as_ref()
            .map(|junction| {
                self.relation
                    .surface
                    .detach_section(&junction.covariance, 64)
                    .map_err(Into::into)
            })
            .transpose()
    }

    pub fn inspect_junction(
        &self,
        occurrence: usize,
    ) -> Result<Option<ResidentSectionRest>, ConstitutiveFibreError> {
        let held = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        held.junction_rest(self.relation.surface)
    }

    /// Executable reconstruction of every actual internal current. This is an explicitly
    /// requested cold receiver over immutable native source/prefix sections, never the productive
    /// update. It does not select a vector from the kernel of the moment map or replay cultivation.
    pub fn inspect_internal_currents(
        &self,
    ) -> Result<Option<Vec<NativeFieldInternalCurrent>>, ConstitutiveFibreError> {
        if self.has_operative_contacts() {return Err(ConstitutiveFibreError::Rest("operative internal currents require their enclosed current receiver and chronological decoder".into()));}
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let Some(junction) = self.junction.as_ref() else {
            return Ok(None);
        };
        if matches!(
            junction.representation,
            NativeFieldJunctionRepresentation::EnclosedDyadic { .. }
        ) {
            return self.decode_enclosed_internal_currents().map(Some);
        }
        let width = self.relation.source_width + self.relation.target_width;
        let prefix =
            |words: &[(i64, i64)]| -> Result<Vec<ExactComplexWaveCurrent>, ConstitutiveFibreError> {
                let at = 3 * (width + 1);
                let den = words[at + width].0;
                if den <= 0 || words.iter().any(|(a, b)| a != b) {
                    return Err(ConstitutiveFibreError::Uncertain);
                }
                Ok((0..width / 2)
                    .map(|j| {
                        ExactComplexWaveCurrent::new(
                            Rat::new(words[at + 2 * j].0.into(), den.into()),
                            Rat::new(words[at + 2 * j + 1].0.into(), den.into()),
                        )
                    })
                    .collect())
            };
        let current_prefix = prefix(&self.relation.surface.read_out(&junction.current)?)?;
        let sign = Rat::from_integer(if self.history.len() % 2 == 1 { 1 } else { -1 }.into());
        let mut internal = Vec::new();
        for (receiving, event) in self.history.iter().enumerate() {
            let Some(source_at) = event.lineage.observed_source() else {
                continue;
            };
            let source = &self.history[source_at];
            let source_words = source.source_rest(self.relation.surface)?.intervals;
            let denominator = source_words[self.relation.source_width].0;
            if denominator <= 0 || source_words.iter().any(|(a, b)| a != b) {
                return Err(ConstitutiveFibreError::Uncertain);
            }
            let mut contact = Vec::with_capacity(width / 2);
            for (node, frame) in source.frame.view.root_to_local().iter().enumerate() {
                for branch in 0..2 {
                    let at = 4 * node + 2 * branch;
                    let local = ExactComplexWaveCurrent::new(
                        Rat::new(source_words[at].0.into(), denominator.into()),
                        Rat::new(source_words[at + 1].0.into(), denominator.into()),
                    );
                    contact.push(frame.current().conjugate().multiply(&local));
                }
            }
            let minus_one = Rat::from_integer((-1).into());
            contact.extend(
                self.inspect_incoming(receiving)?
                    .iter()
                    .map(|a| a.current().scaled(&minus_one)),
            );
            let before = if receiving == 0 {
                vec![ExactComplexWaveCurrent::zero(); width / 2]
            } else {
                prefix(
                    &self
                        .inspect_junction(receiving - 1)?
                        .ok_or(ConstitutiveFibreError::Uncertain)?
                        .intervals,
                )?
            };
            let current = contact
                .iter()
                .zip(current_prefix.iter().zip(&before))
                .fold(
                    ExactComplexWaveCurrent::zero(),
                    |total, (d, (now, birth))| {
                        total.add(&d.conjugate().multiply(&now.subtract(birth)))
                    },
                )
                .scaled(&sign);
            internal.push(NativeFieldInternalCurrent {
                source_occurrence: source_at,
                receiving_occurrence: receiving,
                contact,
                current,
            });
        }
        Ok(Some(internal))
    }

    pub(super) fn prepare_junction(
        &self, linked: bool,
    ) -> Result<Option<(PendingJunction<'chart>, ResidentSection<'chart>)>, ConstitutiveFibreError>
    {
        let Some(junction) = self.junction.as_ref() else {
            return Ok(None);
        };
        let width = self.relation.source_width + self.relation.target_width;
        let surface = self.relation.surface;
        // The scratch section is apparatus storage for signed wide words. Its low allocation is
        // interpreted as i128 only by the private native kernel; no interval readout is made.
        let extra = match junction.representation {
            NativeFieldJunctionRepresentation::RationalWords => 7,
            NativeFieldJunctionRepresentation::EnclosedDyadic { .. } => 8,
        };
        let scratch_words = width
            .checked_mul(width)
            .and_then(|n| n.checked_add(extra * width))
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        Ok(Some((
            PendingJunction {
                operative: junction.operative.as_ref().map(|o|o.prepare(surface,self.nodes(),linked)).transpose()?,
                covariance: surface.fresh_section(1, width * width + 1, ResidentGrain(0))?,
                report: Rc::new(surface.fresh_section(
                    1,
                    junction.representation.report_words(width),
                    ResidentGrain(0),
                )?),
            },
            surface.fresh_section(1, scratch_words, ResidentGrain(0))?,
        )))
    }

    pub(super) fn read_pending_junction(
        &self,
    ) -> Result<Option<NativeFieldJunctionReading>, ConstitutiveFibreError> {
        let Some(pending) = self.pending_junction.as_ref() else {
            return Ok(None);
        };
        if let Some(op)=&pending.operative {
            return operative::decode_reflection(self.relation.surface,&pending.report,&op.history(),self.nodes(),self.transport_grain()?)
                .map(|r|Some(NativeFieldJunctionReading::Operative(r)));
        }
        let words = self.relation.surface.read_out(&pending.report)?;
        let width = self.relation.source_width + self.relation.target_width;
        let representation = self
            .junction
            .as_ref()
            .ok_or(ConstitutiveFibreError::Uncertain)?
            .representation;
        if let NativeFieldJunctionRepresentation::EnclosedDyadic { fractional_bits } =
            representation
        {
            return enclosure::decode_report(&words, width, fractional_bits)
                .map(|reading| Some(NativeFieldJunctionReading::Enclosed(reading)));
        }
        let stride = width + 1;
        if words.len() != 4 * stride
            || words.iter().any(|(lo, hi)| lo != hi)
            || (0..4).any(|part| words[part * stride + width].0 <= 0)
        {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let decode = |part: usize| -> Vec<ExactComplexWaveCurrent> {
            let at = part * stride;
            let denominator = words[at + width].0;
            (0..width / 2)
                .map(|i| {
                    ExactComplexWaveCurrent::new(
                        Rat::new(words[at + 2 * i].0.into(), denominator.into()),
                        Rat::new(words[at + 2 * i + 1].0.into(), denominator.into()),
                    )
                })
                .collect()
        };
        Ok(Some(NativeFieldJunctionReading::Exact(
            NativeFieldExactJunctionReading {
                potential: decode(0),
                outgoing: decode(1),
                held_current: decode(2),
                potential_prefix: decode(3),
            },
        )))
    }
}

#[cfg(test)]
mod tests;
