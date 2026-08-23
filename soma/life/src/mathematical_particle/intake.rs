//! The addressed material-to-operation boundary returned by rich intake.
//!
//! This is the narrow relation R0 found absent.  It owns neither a parser nor a semantic router:
//! A1 record occurrences are paired with M0 carriers only when situated record incidence and exact
//! payload identity agree; M0 presentations remain distinct branches of one [`TypedPassage`]; and
//! the M1 typing population binds only actual ports, laws, source occurrences, and receiver
//! occurrences.  A later receiver may identify branches only through the retained fibres.

use std::collections::BTreeSet;

use holonic_engine::causal::EventId;
use holonic_engine::evolution::EvolutionLawId;
use holonic_engine::ported_operation::PortedOperationComplex;

use crate::exchange_world_tube::ExchangeWorldTube;
use crate::mathematical_source::{CoTestimonyFiber, PresentationComparison, SourceLayoutTestimony};

use super::validation::typing::{
    require_sources, require_subset, require_unique, source_addresses, validate_operation_typing,
    validate_ports,
};
use super::{
    BinderScope, BranchId, CarrierOccurrence, HypothesisLicense, MathematicalParticleError,
    PassageBranchId, TypedOperation, TypedPassage, TypedPort,
};

/// One exact A1-record/M0-carrier boundary square.  Source and target remain different occurrence
/// identities; equality is asserted only for the carried payload face.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordFacePassage {
    pub record: u64,
    pub record_occurrence_sha256: String,
    pub carrier_address: String,
    pub carried_payload_sha256: String,
}

/// The complete boundary is consumed once into the world-tube. Keeping these populations in one
/// input owner avoids restating and reallocating the continuing ecology inside its wrapper.
#[derive(Debug)]
pub struct MaterialOperationWorldTubeInput {
    pub occurrence: String,
    pub exchange: ExchangeWorldTube,
    pub source_testimonies: Vec<SourceLayoutTestimony>,
    pub record_face_passages: Vec<RecordFacePassage>,
    pub operation: PortedOperationComplex,
    pub passage: TypedPassage,
    pub carriers: Vec<CarrierOccurrence>,
    pub binders: Vec<BinderScope>,
    pub ports: Vec<TypedPort>,
    pub operations: Vec<TypedOperation>,
    pub hypotheses: Vec<HypothesisLicense>,
    pub branches: BTreeSet<BranchId>,
    pub receiver_record_occurrences: BTreeSet<String>,
    pub cross_codec_fibres: Vec<CoTestimonyFiber>,
    pub presentation_controls: Vec<PresentationComparison>,
    pub open_fibres: Vec<String>,
}

/// One continuing rich-intake body.  It intentionally has no `Clone`: the exchange occurrence,
/// M0 presentations, and M1 operation passage have one owner.
#[derive(Debug)]
pub struct MaterialOperationWorldTube {
    boundary: MaterialOperationWorldTubeInput,
}

impl MaterialOperationWorldTube {
    pub fn found(
        boundary: MaterialOperationWorldTubeInput,
    ) -> Result<Self, MathematicalParticleError> {
        if boundary.occurrence.is_empty()
            || boundary.source_testimonies.len() < 2
            || boundary.receiver_record_occurrences.is_empty()
            || boundary.cross_codec_fibres.is_empty()
            || boundary.presentation_controls.is_empty()
            || boundary.open_fibres.is_empty()
            || boundary.open_fibres.iter().any(String::is_empty)
        {
            return Err(MathematicalParticleError::MaterialOperationBoundaryIncomplete);
        }

        let source_addresses = source_addresses(&boundary.source_testimonies);
        if boundary.passage.source_occurrences() != &source_addresses {
            return Err(MathematicalParticleError::EmptySourceLineage);
        }
        let rebuilt = TypedPassage::found(
            boundary.passage.occurrence().to_owned(),
            boundary.passage.staging_sources().clone(),
            boundary.passage.staging().clone(),
            boundary.passage.branches().clone(),
            &boundary.operation,
            &source_addresses,
        )?;
        if rebuilt.addressed() != boundary.passage.addressed()
            || rebuilt.source_occurrences() != boundary.passage.source_occurrences()
        {
            return Err(MathematicalParticleError::AddressedOccurrenceKeyDisagrees);
        }
        boundary
            .operation
            .shape
            .validate()
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
        let closure = boundary
            .operation
            .closure()
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
        if !closure.open_questions.is_empty()
            || !closure.operations_without_deciding_testimony.is_empty()
        {
            return Err(MathematicalParticleError::OperationShapeOpen);
        }

        require_unique(
            boundary.carriers.iter().map(|carrier| carrier.id),
            MathematicalParticleError::DuplicateCarrier,
        )?;
        require_unique(
            boundary.binders.iter().map(|binder| binder.id),
            MathematicalParticleError::DuplicateBinder,
        )?;
        require_unique(
            boundary.hypotheses.iter().map(|hypothesis| hypothesis.id),
            MathematicalParticleError::DuplicateHypothesis,
        )?;
        if boundary.branches.is_empty() {
            return Err(MathematicalParticleError::MaterialOperationBoundaryIncomplete);
        }
        let all_ports = boundary
            .operation
            .shape
            .boundaries
            .objects
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let all_laws = boundary
            .operation
            .shape
            .laws
            .keys()
            .copied()
            .collect::<BTreeSet<EvolutionLawId>>();
        for carrier in &boundary.carriers {
            require_sources(&carrier.source_occurrences, &source_addresses)?;
            if carrier.owner_carrier.is_empty() || carrier.equality_law_lineage.is_empty() {
                return Err(MathematicalParticleError::EmptyCarrierLaw(carrier.id));
            }
        }
        for binder in &boundary.binders {
            require_sources(&binder.source_occurrences, &source_addresses)?;
            require_subset(
                &binder.ports,
                &all_ports,
                MathematicalParticleError::UnknownPort,
            )?;
            require_subset(
                &binder.laws,
                &all_laws,
                MathematicalParticleError::UnknownLaw,
            )?;
        }
        validate_ports(
            &boundary.ports,
            &all_ports,
            &boundary.carriers,
            &boundary.binders,
            &boundary.operation,
        )?;
        for hypothesis in &boundary.hypotheses {
            require_sources(&hypothesis.source_occurrences, &source_addresses)?;
            require_subset(
                &hypothesis.licenses,
                &all_laws,
                MathematicalParticleError::UnknownLaw,
            )?;
            require_subset(
                &hypothesis.branches,
                &boundary.branches,
                MathematicalParticleError::UnknownBranch,
            )?;
        }
        validate_operation_typing(
            &boundary.operations,
            &boundary.operation,
            &boundary
                .hypotheses
                .iter()
                .map(|hypothesis| hypothesis.id)
                .collect(),
            &boundary.branches,
        )?;

        validate_record_faces(
            &boundary.exchange,
            &boundary.source_testimonies,
            &boundary.record_face_passages,
        )?;
        let available_records = boundary
            .record_face_passages
            .iter()
            .map(|passage| passage.record_occurrence_sha256.clone())
            .collect::<BTreeSet<_>>();
        if let Some(unknown) = boundary
            .receiver_record_occurrences
            .iter()
            .find(|occurrence| !available_records.contains(*occurrence))
        {
            return Err(MathematicalParticleError::ReceiverOccurrenceUnknown(
                unknown.clone(),
            ));
        }

        let artifacts = boundary
            .source_testimonies
            .iter()
            .map(|testimony| testimony.artifact.occurrence.clone())
            .collect::<BTreeSet<_>>();
        if boundary.cross_codec_fibres.iter().any(|fibre| {
            !artifacts.contains(&fibre.left_artifact.occurrence)
                || !artifacts.contains(&fibre.right_artifact.occurrence)
        }) {
            return Err(MathematicalParticleError::MaterialOperationBoundaryIncomplete);
        }

        Ok(Self { boundary })
    }

    pub fn occurrence(&self) -> &str {
        &self.boundary.occurrence
    }

    pub fn exchange(&self) -> &ExchangeWorldTube {
        &self.boundary.exchange
    }

    pub fn source_testimonies(&self) -> &[SourceLayoutTestimony] {
        &self.boundary.source_testimonies
    }

    pub fn record_face_passages(&self) -> &[RecordFacePassage] {
        &self.boundary.record_face_passages
    }

    pub fn operation(&self) -> &PortedOperationComplex {
        &self.boundary.operation
    }

    pub fn passage(&self) -> &TypedPassage {
        &self.boundary.passage
    }

    pub fn carriers(&self) -> &[CarrierOccurrence] {
        &self.boundary.carriers
    }

    pub fn binders(&self) -> &[BinderScope] {
        &self.boundary.binders
    }

    pub fn ports(&self) -> &[TypedPort] {
        &self.boundary.ports
    }

    pub fn operations(&self) -> &[TypedOperation] {
        &self.boundary.operations
    }

    pub fn hypotheses(&self) -> &[HypothesisLicense] {
        &self.boundary.hypotheses
    }

    pub fn branches(&self) -> &BTreeSet<BranchId> {
        &self.boundary.branches
    }

    pub fn receiver_record_occurrences(&self) -> &BTreeSet<String> {
        &self.boundary.receiver_record_occurrences
    }

    pub fn cross_codec_fibres(&self) -> &[CoTestimonyFiber] {
        &self.boundary.cross_codec_fibres
    }

    pub fn presentation_controls(&self) -> &[PresentationComparison] {
        &self.boundary.presentation_controls
    }

    pub fn open_fibres(&self) -> &[String] {
        &self.boundary.open_fibres
    }

    pub fn branch_entry_events(
        &self,
    ) -> impl Iterator<Item = (PassageBranchId, EventId, EventId)> + '_ {
        self.boundary
            .passage
            .staging()
            .iter()
            .filter_map(|(branch, staging)| {
                self.boundary
                    .passage
                    .terminal_events()
                    .get(branch)
                    .copied()
                    .map(|terminal| (*branch, staging.event, terminal))
            })
    }
}

fn validate_record_faces(
    exchange: &ExchangeWorldTube,
    testimonies: &[SourceLayoutTestimony],
    passages: &[RecordFacePassage],
) -> Result<(), MathematicalParticleError> {
    if passages.len() != exchange.records.len() {
        return Err(MathematicalParticleError::RecordFacePopulationDisagrees);
    }
    require_unique(
        passages.iter().map(|passage| passage.record),
        MathematicalParticleError::RecordFacePopulationDisagrees,
    )?;
    for passage in passages {
        let Some(record) = exchange.records.get(passage.record as usize) else {
            return Err(MathematicalParticleError::RecordFacePopulationDisagrees);
        };
        if exchange.record_occurrence(passage.record).render() != passage.record_occurrence_sha256 {
            return Err(MathematicalParticleError::RecordFaceOccurrenceDisagrees);
        }
        let Some(carrier) = testimonies
            .iter()
            .flat_map(|testimony| &testimony.occurrences)
            .find(|carrier| carrier.address == passage.carrier_address)
        else {
            return Err(MathematicalParticleError::RecordFaceCarrierAbsent);
        };
        if record.raw_sha256.render() != passage.carried_payload_sha256
            || carrier.payload_sha256 != passage.carried_payload_sha256
        {
            return Err(MathematicalParticleError::RecordFaceContentDisagrees);
        }
    }
    Ok(())
}
