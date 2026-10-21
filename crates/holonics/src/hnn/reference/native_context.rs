//! Native model prediction from the common Resident's actual prepared opening.
use super::*;
use std::sync::Arc;

/// Explicit execution scope; neither branch is a fallback on execution/admission failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeExecutionChart {
    Declared,
    ExactUnsplit,
}

impl Reference {
    /// One complete native Word, without q/tree/population reads or a second source ingress.
    /// The resident is borrowed until its score/draw/actual return consumes this producer.
    pub fn prepare_native_current_prediction<'a>(
        &self,
        resident: &'a Resident,
        chart: NativeExecutionChart,
        bits: u32,
    ) -> Result<crate::hnn::word::native_prediction::NativePredictionWord<'a>, HnnError> {
        resident.admit_no_participating_world()?;
        if !resident.pending.is_empty() || !resident.staged.is_empty() || resident.arrived.is_some()
        {
            return Err(HnnError::Unadmitted {
                reason: "native model contact prediction needs its ordinary committed cut with no open return handles",
            });
        }
        if let Some(lag) = resident
            .prepared_input
            .as_ref()
            .and_then(|p| p.lagged.as_ref())
        {
            if resident.carried.as_ref().map(|c| c.ticks) != Some(lag.reached_tick()) {
                return Err(HnnError::Unadmitted {
                    reason: "lagged native context belongs to the actual complete carried crossing",
                });
            }
        }
        let (moment, _) = resident.continuing().ok_or(HnnError::Unadmitted {
            reason: "one native model source moment",
        })?;
        let phases = resident.admitted.first().ok_or(HnnError::Unadmitted {
            reason: "one native model receiver",
        })?;
        let field = &resident.field;
        let theta = &resident.constitution;
        let (ratio, opening, _) = self.prepare_refine(
            resident,
            &moment,
            phases,
            &crate::hnn::ring::modes::ModeView::whole(),
            field,
            theta,
        )?;
        let mut charts = resident.reception_charts();
        let mut word = match chart {
            NativeExecutionChart::Declared => ratio.open_on(field, theta, &mut charts, &opening)?,
            NativeExecutionChart::ExactUnsplit => Word::open_received_view_exact(
                field,
                theta,
                &resident.current,
                ratio.moment(),
                &opening,
                ratio.view(),
            )?,
        };
        if let Some(cut) = ratio.prepared_input() {
            word = cut.apply(field, theta, &ratio, word)?;
        } else {
            word.bind_source_producer(theta, &resident.current, Arc::new(ratio.moment().clone()))?;
        }
        word.run(phases.junction_steps())?;
        let receiver = field
            .receivers()
            .iter()
            .position(|r| r.ring == phases.ring())
            .ok_or(HnnError::MissingReceivingMap {
                ring: phases.ring(),
            })?;
        Ok(word
            .native_current_prediction(receiver, bits)?
            .with_prepared_cut(ratio.prepared_input().cloned()))
    }
}

/// Inspection of one actual event. Contact-only is explicit; this does not claim an R-only
/// epoch consumer, CUDA execution or a native-language command has been joined.
pub struct NativeContextEvent {
    pub prediction: crate::hnn::word::native_prediction::NativePredictionReading,
    pub scores: Vec<crate::ratio::algebraic::ExactInterval>,
    pub forward: WordBalance,
    pub preparation: Option<crate::hnn::word::action::PortPreparationReceipt>,
    pub contact: Option<crate::hnn::word::native_prediction::NativeContactPublication>,
    pub input: observed::IngestClassReceipt,
}
impl Resident {
    pub(crate) fn native_context_chart(&self) -> Result<Option<Encoded>, HnnError> {
        let Some(p) = self.prepared_input.as_ref().filter(|p| {
            p.context_chart() == prepared_input::ContextChart::LaggedReceiverBoundaryV1
        }) else {
            return Ok(None);
        };
        let pairing = crate::hnn::paired::PairingDeclaration::Family {
            table: p.pairs.clone(),
        };
        let chart = crate::hnn::encoding::observed::PairedObservation::admit(
            &self.field,
            &self.constitution,
            &pairing,
        )?
        .encode(&[])?;
        Ok(Some(chart))
    }
}
impl Reference {
    /// A declared contact-only actual event at a closed native cut. It consumes ONE new
    /// exterior class after its prediction. It cannot certify an aggregate of older openings.
    pub fn observe_native_current_contact(
        &self,
        resident: &mut Resident,
        crib: &mut observed::ObservedCrib,
        pairing: &crate::hnn::paired::PairingDeclaration,
        class: usize,
        bits: u32,
    ) -> Result<NativeContextEvent, HnnError> {
        self.native_current_event(resident, crib, pairing, class, bits, true)
    }
    /// Same F/prefix computation on a frozen forecast fork. The chosen class is a hypothesis,
    /// not a material-forming observation. Contact, receiving and M moments remain fixed.
    pub fn continue_native_current_forecast(
        &self,
        resident: &mut Resident,
        crib: &mut observed::ObservedCrib,
        pairing: &crate::hnn::paired::PairingDeclaration,
        class: usize,
        bits: u32,
    ) -> Result<NativeContextEvent, HnnError> {
        self.native_current_event(resident, crib, pairing, class, bits, false)
    }
    fn native_current_event(
        &self,
        resident: &mut Resident,
        crib: &mut observed::ObservedCrib,
        pairing: &crate::hnn::paired::PairingDeclaration,
        class: usize,
        bits: u32,
        actual: bool,
    ) -> Result<NativeContextEvent, HnnError> {
        let mut next = resident.clone();
        let mut next_crib = crib.clone();
        let input = next.prepared_input.as_ref().ok_or(HnnError::Unadmitted {
            reason: "native prediction needs its explicit fresh context owner",
        })?;
        if input.context_chart() != prepared_input::ContextChart::LaggedReceiverBoundaryV1
            || actual != (input.mode() == prepared_input::PrefixMode::Training)
        {
            return Err(HnnError::Unadmitted {
                reason: "native event keeps explicit observed versus frozen hypothetical lineage",
            });
        }
        let (_, source_cells) = next.continuing().ok_or(HnnError::Unadmitted {
            reason: "one actual native source",
        })?;
        let boundary = crate::hnn::encoding::observed::PairedObservation::admit(
            &next.field,
            &next.constitution,
            pairing,
        )?;
        if boundary.immutable_identity_text() != input.boundary_identity {
            return Err(HnnError::Unadmitted {
                reason: "native event uses its unchanged original input chart",
            });
        }
        let target = boundary.encode(&[class])?;
        let chart = boundary.encode(&[])?;
        let predictor = self.prepare_native_current_prediction(
            &next,
            NativeExecutionChart::ExactUnsplit,
            bits,
        )?;
        let prepared = predictor
            .prepared_cut()
            .cloned()
            .ok_or(HnnError::Unadmitted {
                reason: "one kept original native preparation cut",
            })?;
        let prediction = predictor.reading();
        let role = if actual {
            prepared_input::PrefixRole::Observed
        } else {
            input.forecast_role
        };
        let lag = predictor.lagged_boundary(role)?;
        let (carry, forward, preparation) = predictor.forward_receipt()?;
        let (scores, contact, material, carry, charts) = if actual {
            let returned = predictor.observe(&target)?;
            let scores = returned.scores().to_vec();
            let mut charts = next.reception_charts();
            let published = returned.publish_contact_carry(&mut charts)?;
            (scores, Some(published), None, None, charts)
        } else {
            let scores = predictor.score(&target)?;
            drop(predictor);
            (
                scores,
                None,
                Some(next.constitution.clone()),
                Some(carry),
                next.reception_charts(),
            )
        };
        let (material, carry) = match &contact {
            Some(p) => (p.constitution.clone(), p.carry.clone()),
            None => (
                material.expect("frozen material"),
                carry.expect("executed carry"),
            ),
        };
        let point = crate::holon::HolonState {
            commit: material.commit(),
            configuration: carry,
        };
        next.publish_reception(Some(material), point, Some(charts), None, &chart)?;
        let ingested =
            self.ingest_class_continuing(&mut next, &mut next_crib, pairing, class, None)?;
        if ingested.cells != source_cells.checked_add(1).ok_or(HnnError::CountOverflow)? {
            return Err(HnnError::Unadmitted {
                reason: "native event ingests its actual class exactly once",
            });
        }
        let input = next.prepared_input.as_mut().expect("same material owner");
        if actual {
            input.after_actual(prepared, class)?;
        } else {
            input.after_forecast(class)?;
        }
        input.install_reached_lag(lag)?;
        *resident = next;
        *crib = next_crib;
        Ok(NativeContextEvent {
            prediction,
            scores,
            forward,
            preparation,
            contact,
            input: ingested,
        })
    }
}
