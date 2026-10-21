//! One source-bound native predictive receiver. Scoring, draw and return borrow ONE face.
//! The legacy tree/mixture is neither a constructor operand nor a selected fallback here.
use super::*;
use crate::hnn::receiving::RetainedStationReturn;
use crate::hnn::receiving::native_current::NativeCurrentFace;
use crate::ratio::algebraic::ExactInterval;
use crate::receiver::release::ReleaseReturn;

pub const LAW: &str = "native-current-prediction-v1";

/// Consumes the actual Word; callers cannot construct a face, change the predictor or rebind y.
pub struct NativePredictionWord<'a> {
    word: Word<'a>,
    prepared: Option<crate::hnn::reference::prepared_input::PreparedInputCut>,
    phases: ReceivingPhases,
    map: ExactRatMatrix,
    faces: Vec<NativeCurrentFace>,
    features: Vec<Vec<Rat>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativePredictionReading {
    pub law: &'static str,
    pub producing_commit: u64,
    pub opened_at: usize,
    pub source_cells: u64,
    pub receiver: usize,
    pub features: Vec<Vec<Rat>>,
    pub waves: Vec<Vec<Rat>>,
    pub masses: Vec<Vec<ExactInterval>>,
}
pub struct NativePredictionReturn {
    reading: NativePredictionReading,
    scores: Vec<ExactInterval>,
    stations: Vec<RetainedStationReturn>,
    back: crate::hnn::port::WordReturn,
    pub(crate) cut: continuation::ContactCut,
    pub(crate) covector: crate::hnn::ratio::RatioCovector,
    phases: ReceivingPhases,
}
impl NativePredictionReturn {
    pub fn reading(&self) -> &NativePredictionReading {
        &self.reading
    }
    pub fn scores(&self) -> &[ExactInterval] {
        &self.scores
    }
    pub fn stations(&self) -> &[RetainedStationReturn] {
        &self.stations
    }
    /// Actual factor publication only. Unsupported paired/split input is refused, not rerouted.
    pub fn publish_contact_carry(
        self,
        charts: &mut Charts,
    ) -> Result<NativeContactPublication, HnnError> {
        self.cut.publish_native_comparison(
            self.reading,
            &self.stations,
            &self.back,
            &self.phases,
            &self.covector,
            charts,
        )
    }
}
/// No Word tape is retained. The complete actual contact successor carries forward once.
pub struct NativeContactPublication {
    pub prediction: NativePredictionReading,
    pub constitution: crate::hnn::constitution::Constitution,
    pub carry: ReceptionCarry,
    pub publication: crate::hnn::constitution::DepositReading,
    pub continuation: continuation::ContinuationReceipt,
    pub actual_alignment: Rat,
    pub actual_error_charge: Rat,
    pub paired_readout_norm: Rat,
}

/// Private admitting input, issued only by the actual native Word comparison consumer.
#[derive(Clone, Debug)]
pub(crate) struct NativeContactWitness {
    pub(super) field: Field,
    pub(super) current: Current,
    pub(super) source: std::sync::Arc<crate::hnn::moment::SourceMoment>,
    pub(super) geometry: crate::hnn::port::PairedReturnGeometry,
    pub(super) phases: ReceivingPhases,
    pub(super) opened_at: usize,
    pub(super) reads: Vec<(Vec<Rat>, Vec<Rat>)>,
    pub(super) producing: crate::hnn::constitution::Constitution,
    pub(super) deposit: crate::hnn::port::Deposit,
    pub(super) readout_norm: Rat,
    pub(super) error_l1: Rat,
}
impl NativeContactWitness {
    pub(crate) fn admit_cut(
        &self,
        field: &Field,
        current: &Current,
        source: &std::sync::Arc<crate::hnn::moment::SourceMoment>,
    ) -> Result<(), HnnError> {
        if field != &self.field
            || current != &self.current
            || !std::sync::Arc::ptr_eq(source, &self.source)
        {
            return Err(HnnError::Unadmitted {
                reason: "native contact proof keeps the actual original source/field/frame/clock owner",
            });
        }
        Ok(())
    }
    pub(crate) fn admit_span(
        &self,
        operands: &crate::hnn::propagation::Operands,
        opened_at: usize,
        reach: &crate::hnn::constitution::Reach,
    ) -> Result<(), HnnError> {
        if opened_at != self.opened_at
            || reach.receiver != self.phases.ring()
            || reach.stations != self.phases.epochs().map(|j| j as u64).collect::<Vec<_>>()
        {
            return Err(HnnError::Unadmitted {
                reason: "native paired propagation gain keeps the actual opening and complete original receiving cut",
            });
        }
        self.geometry.admit_native_contact(
            &self.field,
            &self.reads,
            operands,
            &self.phases,
            opened_at,
        )
    }
    pub(crate) fn admit(
        &self,
        theta: &crate::hnn::constitution::Constitution,
        deposit: &crate::hnn::port::Deposit,
    ) -> Result<(), HnnError> {
        if theta != &self.producing || deposit != &self.deposit {
            return Err(HnnError::Unadmitted {
                reason: "native paired contact witness binds complete producing material and exact reached return",
            });
        }
        Ok(())
    }
    pub(crate) fn readout_norm(&self) -> &Rat {
        &self.readout_norm
    }
    pub(crate) fn error_charge(&self, squared_response: &Rat) -> Rat {
        &self.error_l1 * crate::holon::deposition::sqrt_ceiling(squared_response, 64)
    }
}
impl<'a> Word<'a> {
    /// Read only already-executed stations; never runs or reinjects the source.
    pub fn native_current_prediction(
        mut self,
        receiver: usize,
        bits: u32,
    ) -> Result<NativePredictionWord<'a>, HnnError> {
        let (theta, current, _, _) = self.native_source.as_ref().ok_or(HnnError::Unadmitted {
            reason: "native prediction requires the actual source-producing Word",
        })?;
        let decl = self
            .field
            .receivers()
            .get(receiver)
            .ok_or(HnnError::Unadmitted {
                reason: "native prediction names an admitted receiver",
            })?;
        let phases = ReceivingPhases::declare(self.field, theta, current, decl)?;
        let map = theta
            .receiving_map(phases.ring())
            .ok_or(HnnError::MissingReceivingMap {
                ring: phases.ring(),
            })?
            .clone();
        if theta.receiving_layout(phases.ring())
            != Some(crate::hnn::constitution::ReceivingLayout::ArrivalContext {
                source_width: self.field.ring(phases.ring()).width(),
            })
        {
            return Err(HnnError::Unadmitted {
                reason: "native contextual predictor requires declared paired source/context layout",
            });
        }
        self.prepare_response()?;
        let response = self.response().expect("native response prepared");
        let mut faces = Vec::new();
        let mut features = Vec::new();
        for tick in phases.epochs() {
            let actual = self
                .anchor(tick, phases.ring())
                .ok_or(HnnError::WordEnded {
                    ticks: self.ticks(),
                })?;
            let fresh = &response
                .records
                .get(tick)
                .ok_or(HnnError::WordEnded {
                    ticks: self.ticks(),
                })?
                .anchors[phases.ring()];
            let mut feature = fresh.clone();
            feature.extend(actual.iter().zip(fresh).map(|(a, s)| a - s));
            let wave = map.apply(&feature)?;
            faces.push(NativeCurrentFace::at(wave, bits)?);
            features.push(feature);
        }
        Ok(NativePredictionWord {
            word: self,
            prepared: None,
            phases,
            map,
            faces,
            features,
        })
    }
}
impl NativePredictionWord<'_> {
    pub(crate) fn with_prepared_cut(
        mut self,
        cut: Option<crate::hnn::reference::prepared_input::PreparedInputCut>,
    ) -> Self {
        self.prepared = cut;
        self
    }
    pub(crate) fn prepared_cut(
        &self,
    ) -> Option<&crate::hnn::reference::prepared_input::PreparedInputCut> {
        self.prepared.as_ref()
    }
    pub fn reading(&self) -> NativePredictionReading {
        let (theta, _, source, _) = self
            .word
            .native_source
            .as_ref()
            .expect("issued native producer");
        NativePredictionReading {
            law: LAW,
            producing_commit: theta.commit(),
            opened_at: self.word.opened_at(),
            source_cells: source.cells(),
            receiver: self.phases.ring(),
            features: self.features.clone(),
            waves: self.faces.iter().map(|f| f.wave().to_vec()).collect(),
            masses: self.faces.iter().map(|f| f.masses().to_vec()).collect(),
        }
    }
    /// The pre-target reached contrast. It can prepare only a later input, never this Word.
    pub(crate) fn lagged_boundary(
        &self,
        role: crate::hnn::reference::prepared_input::PrefixRole,
    ) -> Result<crate::hnn::reference::prepared_input::LaggedReceiverBoundary, HnnError> {
        let (theta, current, source, _) =
            self.word.native_source.as_ref().expect("native producer");
        if self.features.len() != 1 {
            return Err(HnnError::Unadmitted {
                reason: "one reached native context boundary in this causal chart",
            });
        }
        crate::hnn::reference::prepared_input::LaggedReceiverBoundary::issued(
            self.word.field,
            self.phases.ring(),
            source.cells(),
            theta.commit(),
            self.word
                .opened_at()
                .checked_add(self.word.ticks())
                .ok_or(HnnError::CountOverflow)?,
            current.lift(),
            &self.features[0],
            role,
        )
    }
    pub(crate) fn forward_receipt(
        &self,
    ) -> Result<
        (
            ReceptionCarry,
            WordBalance,
            Option<action::PortPreparationReceipt>,
        ),
        HnnError,
    > {
        let released = self.word.released()?;
        let balance = WordBalance::of(&released);
        if !balance.closes() {
            return Err(HnnError::Unadmitted {
                reason: "native full-tick forward retains its exact executed balance",
            });
        }
        let prep = self.word.source_preparation().cloned();
        if prep.as_ref().is_some_and(|p| !p.closes()) {
            return Err(HnnError::Unadmitted {
                reason: "native preparation work closes once before the first executed tick",
            });
        }
        Ok((self.word.reception_end()?, balance, prep))
    }
    pub fn draw(&self, station: usize, key: &Rat) -> Result<ReleaseReturn, HnnError> {
        let face = self.faces.get(station).ok_or(HnnError::Unadmitted {
            reason: "native release at an original produced station",
        })?;
        crate::receiver::release::draw(face.masses(), key).map_err(|_| HnnError::Unadmitted {
            reason: "native receiver draw reads its produced CDF",
        })
    }
    pub fn score(
        &self,
        targets: &crate::hnn::encoding::Encoded,
    ) -> Result<Vec<ExactInterval>, HnnError> {
        self.word.field.admit(targets)?;
        if targets.len() != self.faces.len() {
            return Err(HnnError::Unadmitted {
                reason: "one actual target for each native prediction",
            });
        }
        self.faces
            .iter()
            .zip(targets.classes_read())
            .map(|(f, t)| f.score(t))
            .collect()
    }
    pub fn observe(
        self,
        targets: &crate::hnn::encoding::Encoded,
    ) -> Result<NativePredictionReturn, HnnError> {
        let scores = self.score(targets)?;
        let reading = self.reading();
        let stations = self
            .faces
            .iter()
            .zip(targets.classes_read())
            .map(|(f, t)| f.returned(t))
            .collect::<Result<Vec<_>, _>>()?;
        let (_, current, _, _) = self
            .word
            .native_source
            .as_ref()
            .expect("native source owner");
        let phases = crate::hnn::ratio::target_phases(
            self.word.field,
            current.lift(),
            self.phases.ring(),
            targets,
        )?;
        let covector =
            crate::hnn::ratio::RatioCovector::native_current(&reading.waves, &phases, &stations)?;
        let returned = self
            .word
            .return_contact(&covector, &self.map, &self.phases)?;
        let cut = returned
            .forward
            .into_present()
            .ok_or(HnnError::Unadmitted {
                reason: "actual native contact cut",
            })?;
        let back = returned
            .pullback
            .into_present()
            .ok_or(HnnError::Unadmitted {
                reason: "actual native same-Word return",
            })?;
        if back.reads.iter().map(|(f, _)| f).ne(self.features.iter()) {
            return Err(HnnError::Unadmitted {
                reason: "native return preserves complete actual/fresh producing feature",
            });
        }
        Ok(NativePredictionReturn {
            reading,
            scores,
            stations,
            back,
            cut,
            covector,
            phases: self.phases,
        })
    }
}
