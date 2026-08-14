//! The world-read boundary for one returned conditioned-production contact.
//!
//! `RTCF` is the wide, validation-only seal. It binds addressed predecessor and first-production
//! occurrences to one separately deposited returned-reading occurrence and the complete typed
//! passage/cell movement population. This owner rereads all four addressed forms, proves their
//! content addresses, reconstructs the two circuits and returned reading, asks the engine to
//! validate the whole population, and requires CUDA to group the resulting dense atlas.
//!
//! `CRST` is the narrow continuing rest. It carries the base `CDER` rest and only the minimal
//! passage sites and exact local causes accepted by the engine. It carries form occurrence/content
//! lineage as exterior testimony, but no path, first-production passage, bridge, query, or returned
//! contact sheet. None of that lineage is consulted when the remounted body produces again.

use std::path::{Path, PathBuf};

#[cfg(test)]
use std::sync::atomic::{AtomicU64, Ordering};

use holonic_engine::{
    algebraic::ComparativeMultiplicity,
    conditioned_derivation::{
        found_conditioned_circuit, Bridge, ConditionedBody, ConditionedCircuit, DerivationQuery,
        DerivedPassage,
    },
    derivation_atlas::{
        CircuitAperture, DerivationIdentity, ReachOrientation, RecruitmentCoefficient,
        StatementIncidence,
    },
    derivation_integral::AccumulationRule,
    rebase_invariants::PivotRule,
    returned_conduct::{
        BoundaryMemberAddress, CellAddress, FirstPassageAddress, FirstProductionIdentity,
        FoundedRouteAddress, PassageSite, ReturnOccurrenceId, ReturnReadingIdentity,
        ReturnSourceLineage, ReturnedCause, ReturnedContactMorphology, ReturnedContactRecord,
        ReturnedIncidence, ReturnedProduction, ReturnedTargetGroup as EngineReturnedTargetGroup,
        ValidatedReturnedAtlas,
    },
    returned_reading::{read_production, ReturnedReading},
};
use holonic_structure::{LocalSequence, LocalSet};
use num_bigint::BigUint;
use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::{
    conditioned_rest::{decode_derived_passages, ConditionedRest},
    returned_contact_cuda::{
        CudaReturnedContactExecutor, ReturnedContactCudaFront, ReturnedContactCudaReceipt,
        ReturnedContactGroups, ReturnedContactRelation,
    },
};

#[cfg(test)]
use crate::conditioned_rest::{CONDITIONED_REST_PREFIX, DERIVED_PASSAGE_RENDERING_PREFIX};

/// Exact wire identity for the validation-only returned-contact form.
pub const RETURNED_CONTACT_FORM_PREFIX: [u8; 8] = *b"RTCF\0\0\0\x01";

/// Exact wire identity for the source-free continuing composite rest.
pub const RETURNED_COMPOSITE_REST_PREFIX: [u8; 8] = *b"CRST\0\0\0\x01";

/// A form schema is distinct from its occurrence, content address, and apparatus path.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum NativeFormSchema {
    ConditionedRest,
    DerivedProduction,
    ReturnedReading,
    ReturnedContact,
    ReturnedCompositeRest,
}

impl NativeFormSchema {
    pub const fn name(self) -> &'static str {
        match self {
            Self::ConditionedRest => "CDER/v1",
            Self::DerivedProduction => "CDPS/v2",
            Self::ReturnedReading => "holonic-engine.returned-reading.v1",
            Self::ReturnedContact => "RTCF/v1",
            Self::ReturnedCompositeRest => "CRST/v1",
        }
    }
}

/// One immutable SHA-256 content address. It is never an occurrence identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContentAddress([u8; 32]);

impl ContentAddress {
    pub fn parse(hex: &str) -> Result<Self, ReturnedConductBoundaryRefusal> {
        if hex.len() != 64 {
            return Err(
                ReturnedConductBoundaryRefusal::ContentAddressIsNotCanonical {
                    address: hex.to_owned(),
                },
            );
        }
        let bytes = hex.as_bytes();
        let mut opened = [0u8; 32];
        for at in 0..32 {
            let Some(high) = lower_hex_digit(bytes[at * 2]) else {
                return Err(
                    ReturnedConductBoundaryRefusal::ContentAddressIsNotCanonical {
                        address: hex.to_owned(),
                    },
                );
            };
            let Some(low) = lower_hex_digit(bytes[at * 2 + 1]) else {
                return Err(
                    ReturnedConductBoundaryRefusal::ContentAddressIsNotCanonical {
                        address: hex.to_owned(),
                    },
                );
            };
            opened[at] = (high << 4) | low;
        }
        Ok(Self(opened))
    }

    pub fn of(octets: &[u8]) -> Self {
        let digest = Sha256::digest(octets);
        let mut address = [0u8; 32];
        address.copy_from_slice(&digest);
        Self(address)
    }

    pub fn render(self) -> String {
        let mut rendered = String::with_capacity(64);
        const HEX: &[u8; 16] = b"0123456789abcdef";
        for octet in self.0 {
            rendered.push(HEX[(octet >> 4) as usize] as char);
            rendered.push(HEX[(octet & 0x0f) as usize] as char);
        }
        rendered
    }

    pub const fn octets(self) -> [u8; 32] {
        self.0
    }
}

fn lower_hex_digit(octet: u8) -> Option<u8> {
    match octet {
        b'0'..=b'9' => Some(octet - b'0'),
        b'a'..=b'f' => Some(octet - b'a' + 10),
        _ => None,
    }
}

/// A causal form occurrence, distinct even when two occurrences carry equal content.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct FormOccurrenceIdentity(String);

impl FormOccurrenceIdentity {
    pub fn new(identity: String) -> Result<Self, ReturnedConductBoundaryRefusal> {
        if identity.is_empty() {
            return Err(ReturnedConductBoundaryRefusal::FormOccurrenceIsEmpty);
        }
        Ok(Self(identity))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Occurrence plus immutable content address, with no filesystem coordinate.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FormLineage {
    occurrence: FormOccurrenceIdentity,
    content: ContentAddress,
}

impl FormLineage {
    pub fn new(occurrence: FormOccurrenceIdentity, content: ContentAddress) -> Self {
        Self {
            occurrence,
            content,
        }
    }

    pub fn occurrence(&self) -> &FormOccurrenceIdentity {
        &self.occurrence
    }

    pub const fn content(&self) -> ContentAddress {
        self.content
    }
}

/// Canonical causal identity of the addressed returned-reading occurrence.
pub fn return_reading_identity(lineage: &FormLineage) -> ReturnReadingIdentity {
    ReturnReadingIdentity {
        form: lineage.occurrence.as_str().to_owned(),
    }
}

/// Canonical exterior source testimony: occurrence and immutable reading content together.
pub fn return_source_lineage(lineage: &FormLineage) -> ReturnSourceLineage {
    ReturnSourceLineage {
        source: format!(
            "{}@sha256:{}",
            lineage.occurrence.as_str(),
            lineage.content.render()
        ),
    }
}

/// Exterior world-read descriptor. Path, expected content, schema, and occurrence are four fields.
#[derive(Debug, PartialEq, Eq)]
pub struct AddressedForm {
    path: PathBuf,
    expected_content: ContentAddress,
    schema: NativeFormSchema,
    occurrence: FormOccurrenceIdentity,
}

impl AddressedForm {
    pub fn new(
        path: PathBuf,
        expected_content: &str,
        schema: NativeFormSchema,
        occurrence: String,
    ) -> Result<Self, ReturnedConductBoundaryRefusal> {
        Ok(Self {
            path,
            expected_content: ContentAddress::parse(expected_content)?,
            schema,
            occurrence: FormOccurrenceIdentity::new(occurrence)?,
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub const fn schema(&self) -> NativeFormSchema {
        self.schema
    }

    pub fn occurrence(&self) -> &FormOccurrenceIdentity {
        &self.occurrence
    }

    pub const fn expected_content(&self) -> ContentAddress {
        self.expected_content
    }

    pub fn lineage(&self) -> FormLineage {
        FormLineage::new(self.occurrence.to_owned(), self.expected_content)
    }
}

/// The wide typed contact sheet. It exists only until exact engine validation and CUDA grouping.
#[derive(Debug, PartialEq, Eq)]
pub struct ReturnedContactForm {
    predecessor: FormLineage,
    first_production: FormLineage,
    returned_reading: FormLineage,
    accumulation_rule: AccumulationRule,
    pivot_rule: PivotRule,
    query: DerivationQuery,
    aperture: CircuitAperture,
    incidences: LocalSequence<ReturnedIncidence>,
}

impl ReturnedContactForm {
    pub fn seal(
        predecessor: FormLineage,
        first_production: FormLineage,
        returned_reading: FormLineage,
        accumulation_rule: AccumulationRule,
        pivot_rule: PivotRule,
        query: DerivationQuery,
        aperture: CircuitAperture,
        incidences: LocalSequence<ReturnedIncidence>,
    ) -> Result<Self, ReturnedConductBoundaryRefusal> {
        let form = Self {
            predecessor,
            first_production,
            returned_reading,
            accumulation_rule,
            pivot_rule,
            query,
            aperture,
            incidences,
        };
        form.validate_shape()?;
        Ok(form)
    }

    pub fn predecessor(&self) -> &FormLineage {
        &self.predecessor
    }

    pub fn first_production(&self) -> &FormLineage {
        &self.first_production
    }

    pub fn returned_reading(&self) -> &FormLineage {
        &self.returned_reading
    }

    pub const fn accumulation_rule(&self) -> AccumulationRule {
        self.accumulation_rule
    }

    pub const fn pivot_rule(&self) -> PivotRule {
        self.pivot_rule
    }

    pub fn query(&self) -> &DerivationQuery {
        &self.query
    }

    pub const fn aperture(&self) -> CircuitAperture {
        self.aperture
    }

    pub fn incidences(&self) -> &[ReturnedIncidence] {
        &self.incidences
    }

    fn validate_shape(&self) -> Result<(), ReturnedConductBoundaryRefusal> {
        let reading = return_reading_identity(&self.returned_reading);
        let source_lineage = return_source_lineage(&self.returned_reading);
        if self.predecessor.occurrence == self.first_production.occurrence
            || self.predecessor.occurrence == self.returned_reading.occurrence
            || self.first_production.occurrence == self.returned_reading.occurrence
        {
            return Err(ReturnedConductBoundaryRefusal::FormOccurrencesAreNotDistinct);
        }
        if self.query.statement.is_empty() {
            return Err(ReturnedConductBoundaryRefusal::QueryIsEmpty);
        }
        for (at, incidence) in self.incidences.iter().enumerate() {
            if incidence.occurrence.reading != reading
                || incidence.occurrence.ordinal != at as u64
                || incidence.source_lineage != source_lineage
                || incidence.passage.first_production.form
                    != self.first_production.occurrence.as_str()
            {
                return Err(ReturnedConductBoundaryRefusal::IncidenceIdentityDisagrees { at });
            }
            if incidence.stood_before == incidence.stands_after {
                return Err(ReturnedConductBoundaryRefusal::IncidenceIsNotMovement { at });
            }
            if incidence.founded_route.is_some()
                != (!incidence.stood_before && incidence.stands_after)
            {
                return Err(
                    ReturnedConductBoundaryRefusal::IncidenceRouteDirectionDisagrees { at },
                );
            }
            if at > 0 && self.incidences[at - 1] >= *incidence {
                return Err(ReturnedConductBoundaryRefusal::IncidencesAreNotCanonical { at });
            }
        }
        Ok(())
    }

    pub fn encode_native_bytes(&self) -> Result<LocalSequence<u8>, ReturnedConductBoundaryRefusal> {
        self.validate_shape()?;
        let mut octets = LocalSequence::new();
        octets.extend_from_slice(&RETURNED_CONTACT_FORM_PREFIX);
        put_lineage(&mut octets, &self.predecessor)?;
        put_lineage(&mut octets, &self.first_production)?;
        put_lineage(&mut octets, &self.returned_reading)?;
        put_accumulation_rule(&mut octets, self.accumulation_rule);
        put_pivot_rule(&mut octets, self.pivot_rule);
        put_text(&mut octets, &self.query.statement, "query statement")?;
        put_aperture(&mut octets, self.aperture);
        put_extent(&mut octets, self.incidences.len(), "returned incidences")?;
        for incidence in &self.incidences {
            put_incidence(&mut octets, incidence)?;
        }
        Ok(octets)
    }

    pub fn decode_native_bytes(octets: &[u8]) -> Result<Self, ReturnedConductBoundaryRefusal> {
        let mut cursor = Cursor::new(octets);
        cursor.prefix(&RETURNED_CONTACT_FORM_PREFIX, "RTCF")?;
        let predecessor = cursor.lineage()?;
        let first_production = cursor.lineage()?;
        let returned_reading = cursor.lineage()?;
        let accumulation_rule = cursor.accumulation_rule()?;
        let pivot_rule = cursor.pivot_rule()?;
        let query = DerivationQuery {
            statement: cursor.text("query statement")?,
        };
        let aperture = cursor.aperture()?;
        let extent = cursor.extent("returned incidences")?;
        let mut incidences = LocalSequence::with_capacity(extent.min(1 << 16));
        for _ in 0..extent {
            incidences.push(cursor.incidence()?);
        }
        cursor.finish()?;
        Self::seal(
            predecessor,
            first_production,
            returned_reading,
            accumulation_rule,
            pivot_rule,
            query,
            aperture,
            incidences,
        )
    }
}

/// Exterior lineage retained by the narrow rest but never consulted by production.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnedRestLineage {
    predecessor: FormLineage,
    first_production: FormLineage,
    returned_reading: FormLineage,
    returned_contact: FormLineage,
}

impl ReturnedRestLineage {
    fn new(
        predecessor: FormLineage,
        first_production: FormLineage,
        returned_reading: FormLineage,
        returned_contact: FormLineage,
    ) -> Result<Self, ReturnedConductBoundaryRefusal> {
        let mut occurrences = LocalSet::new();
        for lineage in [
            &predecessor,
            &first_production,
            &returned_reading,
            &returned_contact,
        ] {
            if !occurrences.insert(lineage.occurrence.to_owned()) {
                return Err(ReturnedConductBoundaryRefusal::FormOccurrencesAreNotDistinct);
            }
        }
        Ok(Self {
            predecessor,
            first_production,
            returned_reading,
            returned_contact,
        })
    }

    pub fn predecessor(&self) -> &FormLineage {
        &self.predecessor
    }

    pub fn first_production(&self) -> &FormLineage {
        &self.first_production
    }

    pub fn returned_contact(&self) -> &FormLineage {
        &self.returned_contact
    }

    pub fn returned_reading(&self) -> &FormLineage {
        &self.returned_reading
    }
}

/// Source-free native rest: one base rest plus minimal returned-contact morphology.
#[derive(Debug, PartialEq, Eq)]
pub struct ReturnedCompositeRest {
    base: ConditionedRest,
    lineage: ReturnedRestLineage,
    morphology: ReturnedContactMorphology,
}

impl ReturnedCompositeRest {
    fn from_parts(
        base: ConditionedRest,
        lineage: ReturnedRestLineage,
        morphology: ReturnedContactMorphology,
    ) -> Result<Self, ReturnedConductBoundaryRefusal> {
        let base_octets = base.encode_native_bytes().map_err(|refusal| {
            ReturnedConductBoundaryRefusal::BaseRest {
                detail: refusal.to_string(),
            }
        })?;
        if ContentAddress::of(&base_octets) != lineage.predecessor.content {
            return Err(ReturnedConductBoundaryRefusal::RestPredecessorContentDisagrees);
        }
        if morphology.first_production_lineage().form
            != lineage.first_production.occurrence.as_str()
        {
            return Err(ReturnedConductBoundaryRefusal::RestFirstProductionDisagrees);
        }
        for record in morphology.records() {
            for cause in &record.causes {
                if cause.occurrence.reading.form != lineage.returned_reading.occurrence.as_str() {
                    return Err(ReturnedConductBoundaryRefusal::RestReadingIdentityDisagrees);
                }
                if cause.source_lineage != return_source_lineage(&lineage.returned_reading) {
                    return Err(ReturnedConductBoundaryRefusal::RestSourceLineageDisagrees);
                }
            }
        }
        Ok(Self {
            base,
            lineage,
            morphology,
        })
    }

    pub fn lineage(&self) -> &ReturnedRestLineage {
        &self.lineage
    }

    pub fn records(&self) -> &[ReturnedContactRecord] {
        self.morphology.records()
    }

    pub fn encode_native_bytes(&self) -> Result<LocalSequence<u8>, ReturnedConductBoundaryRefusal> {
        let base = self.base.encode_native_bytes().map_err(|refusal| {
            ReturnedConductBoundaryRefusal::BaseRest {
                detail: refusal.to_string(),
            }
        })?;
        let mut octets = LocalSequence::new();
        octets.extend_from_slice(&RETURNED_COMPOSITE_REST_PREFIX);
        put_lineage(&mut octets, &self.lineage.predecessor)?;
        put_lineage(&mut octets, &self.lineage.first_production)?;
        put_lineage(&mut octets, &self.lineage.returned_reading)?;
        put_lineage(&mut octets, &self.lineage.returned_contact)?;
        put_bytes(&mut octets, &base, "base CDER rest")?;
        put_extent(
            &mut octets,
            self.morphology.records().len(),
            "returned contact records",
        )?;
        for record in self.morphology.records() {
            put_site(&mut octets, &record.site)?;
            put_extent(&mut octets, record.causes.len(), "returned causes")?;
            for cause in &record.causes {
                put_cause(&mut octets, cause)?;
            }
        }
        Ok(octets)
    }

    pub fn decode_native_bytes(octets: &[u8]) -> Result<Self, ReturnedConductBoundaryRefusal> {
        let mut cursor = Cursor::new(octets);
        cursor.prefix(&RETURNED_COMPOSITE_REST_PREFIX, "CRST")?;
        let predecessor = cursor.lineage()?;
        let first_production = cursor.lineage()?;
        let returned_reading = cursor.lineage()?;
        let returned_contact = cursor.lineage()?;
        let lineage = ReturnedRestLineage::new(
            predecessor,
            first_production,
            returned_reading,
            returned_contact,
        )?;
        let base_octets = cursor.bytes("base CDER rest")?;
        let base = ConditionedRest::decode_native_bytes(base_octets).map_err(|refusal| {
            ReturnedConductBoundaryRefusal::BaseRest {
                detail: refusal.to_string(),
            }
        })?;
        let extent = cursor.extent("returned contact records")?;
        let mut records = LocalSequence::with_capacity(extent.min(1 << 16));
        for _ in 0..extent {
            let site = cursor.site()?;
            let cause_extent = cursor.extent("returned causes")?;
            let mut causes = LocalSequence::with_capacity(cause_extent.min(1 << 16));
            for _ in 0..cause_extent {
                causes.push(cursor.cause()?);
            }
            records.push(ReturnedContactRecord { site, causes });
        }
        cursor.finish()?;
        let morphology = ReturnedContactMorphology::resume(
            FirstProductionIdentity {
                form: lineage.first_production.occurrence.as_str().to_owned(),
            },
            records,
        )
        .map_err(|refusal| ReturnedConductBoundaryRefusal::Engine {
            detail: refusal.to_string(),
        })?;
        Self::from_parts(base, lineage, morphology)
    }

    /// Consume the rest into one live owner. The source forms and rest owner do not survive mount.
    pub fn mount(self) -> Result<ReturnedConditionedBody, ReturnedConductBoundaryRefusal> {
        let Self {
            base,
            lineage,
            morphology,
        } = self;
        let body = base
            .mount()
            .map_err(|refusal| ReturnedConductBoundaryRefusal::BaseRest {
                detail: refusal.to_string(),
            })?;
        Ok(ReturnedConditionedBody {
            body,
            lineage,
            morphology,
        })
    }
}

/// The one live body after CRST remount. It owns base morphology and returned morphology together.
#[derive(Debug)]
pub struct ReturnedConditionedBody {
    body: ConditionedBody,
    lineage: ReturnedRestLineage,
    morphology: ReturnedContactMorphology,
}

impl ReturnedConditionedBody {
    pub fn produce(
        &self,
        query: &DerivationQuery,
    ) -> Result<ReturnedProduction, ReturnedConductBoundaryRefusal> {
        self.morphology
            .materialize(&self.body, query)
            .map_err(|refusal| ReturnedConductBoundaryRefusal::Engine {
                detail: refusal.to_string(),
            })
    }

    pub fn returned_records(&self) -> &[ReturnedContactRecord] {
        self.morphology.records()
    }

    /// Found the exact circuit of a returned production against this owner's private base body.
    pub fn found_circuit(
        &self,
        production: &ReturnedProduction,
        query: &DerivationQuery,
        aperture: CircuitAperture,
    ) -> Result<ConditionedCircuit, ReturnedConductBoundaryRefusal> {
        production
            .found_circuit(&self.body, query, aperture)
            .map_err(|refusal| ReturnedConductBoundaryRefusal::Engine {
                detail: refusal.to_string(),
            })
    }

    /// The fresh base production's circuit, without any returned companion.
    pub fn base_circuit(
        &self,
        query: &DerivationQuery,
        aperture: CircuitAperture,
    ) -> Result<ConditionedCircuit, ReturnedConductBoundaryRefusal> {
        self.body.circuit(query, aperture).map_err(|refusal| {
            ReturnedConductBoundaryRefusal::Engine {
                detail: refusal.to_string(),
            }
        })
    }

    pub fn ablate_site(
        self,
        site: &PassageSite,
    ) -> Result<TargetedReturnedAblation, ReturnedConductBoundaryRefusal> {
        let Self {
            body,
            lineage,
            morphology,
        } = self;
        let ablation = morphology.ablate_site(site).map_err(|refusal| {
            ReturnedConductBoundaryRefusal::Engine {
                detail: refusal.to_string(),
            }
        })?;
        Ok(TargetedReturnedAblation {
            body: Self {
                body,
                lineage,
                morphology: ablation.morphology,
            },
            removed: ablation.removed,
        })
    }

    /// Remove the complete returned-contact fiber while preserving the same private base body.
    pub fn ablate_all(self) -> Result<AllReturnedAblation, ReturnedConductBoundaryRefusal> {
        let Self {
            body,
            lineage,
            morphology,
        } = self;
        let ablation = morphology.ablate_all();
        Ok(AllReturnedAblation {
            body: Self {
                body,
                lineage,
                morphology: ablation.morphology,
            },
            removed: ablation.removed,
        })
    }

    pub fn settle(self) -> Result<ReturnedCompositeRest, ReturnedConductBoundaryRefusal> {
        let Self {
            body,
            lineage,
            morphology,
        } = self;
        let base = ConditionedRest::seal(&body).map_err(|refusal| {
            ReturnedConductBoundaryRefusal::BaseRest {
                detail: refusal.to_string(),
            }
        })?;
        ReturnedCompositeRest::from_parts(base, lineage, morphology)
    }
}

/// Exact result of removing one site from one branch of a shared predecessor rest.
#[derive(Debug)]
pub struct TargetedReturnedAblation {
    pub body: ReturnedConditionedBody,
    pub removed: ReturnedContactRecord,
}

/// Exact result of removing every returned site from one branch of a shared predecessor rest.
#[derive(Debug)]
pub struct AllReturnedAblation {
    pub body: ReturnedConditionedBody,
    pub removed: LocalSequence<ReturnedContactRecord>,
}

/// One addressed read in the exterior receipt. Paths remain here and never enter CRST.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AddressedReadReceipt {
    pub path: PathBuf,
    pub schema: NativeFormSchema,
    pub occurrence: FormOccurrenceIdentity,
    pub content_address: String,
}

impl AddressedReadReceipt {
    fn of(form: &AddressedForm) -> Self {
        Self {
            path: form.path.to_owned(),
            schema: form.schema,
            occurrence: form.occurrence.to_owned(),
            content_address: form.expected_content.render(),
        }
    }
}

/// Deterministic addressed-world testimony, separate from physical CUDA testimony.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReturnedConductBoundaryReceipt {
    pub schema: String,
    pub predecessor: AddressedReadReceipt,
    pub first_production: AddressedReadReceipt,
    pub returned_reading: AddressedReadReceipt,
    pub returned_contact: AddressedReadReceipt,
    pub accumulation_rule: AccumulationRule,
    pub pivot_rule: PivotRule,
    pub exact_targets: usize,
    pub exact_occurrences: usize,
    pub exact_relations: usize,
}

/// The source-free rest and the two disjoint species of receipt returned by the deed.
pub struct ReturnedConductOutput {
    pub rest: ReturnedCompositeRest,
    pub semantic: ReturnedConductBoundaryReceipt,
    pub apparatus: ReturnedContactCudaReceipt,
}

/// Reread all addressed forms, prove the complete typed seal, group it on CUDA, and condense it.
pub fn conduct_returned_contact(
    predecessor: &AddressedForm,
    first_production: &AddressedForm,
    returned_reading: &AddressedForm,
    returned_contact: &AddressedForm,
    executor: &mut CudaReturnedContactExecutor,
) -> Result<ReturnedConductOutput, ReturnedConductBoundaryRefusal> {
    let predecessor_octets = read_addressed(predecessor, NativeFormSchema::ConditionedRest)?;
    let first_octets = read_addressed(first_production, NativeFormSchema::DerivedProduction)?;
    let reading_octets = read_addressed(returned_reading, NativeFormSchema::ReturnedReading)?;
    let contact_octets = read_addressed(returned_contact, NativeFormSchema::ReturnedContact)?;

    let base = ConditionedRest::decode_native_bytes(&predecessor_octets).map_err(|refusal| {
        ReturnedConductBoundaryRefusal::BaseRest {
            detail: refusal.to_string(),
        }
    })?;
    let first = decode_derived_passages(&first_octets).map_err(|refusal| {
        ReturnedConductBoundaryRefusal::FirstProduction {
            detail: refusal.to_string(),
        }
    })?;
    let sealed_reading = ReturnedReading::unseal(&reading_octets).map_err(|refusal| {
        ReturnedConductBoundaryRefusal::ReturnedReading {
            detail: refusal.to_string(),
        }
    })?;
    let contact = ReturnedContactForm::decode_native_bytes(&contact_octets)?;

    if &contact.predecessor != &predecessor.lineage() {
        return Err(ReturnedConductBoundaryRefusal::PredecessorLineageDisagrees);
    }
    if &contact.first_production != &first_production.lineage() {
        return Err(ReturnedConductBoundaryRefusal::FirstProductionLineageDisagrees);
    }
    if &contact.returned_reading != &returned_reading.lineage() {
        return Err(ReturnedConductBoundaryRefusal::ReturnedReadingLineageDisagrees);
    }
    let rest_lineage = ReturnedRestLineage::new(
        predecessor.lineage(),
        first_production.lineage(),
        returned_reading.lineage(),
        returned_contact.lineage(),
    )?;

    let ReturnedContactForm {
        predecessor: _,
        first_production: _,
        returned_reading: reading_lineage,
        accumulation_rule,
        pivot_rule,
        query,
        aperture,
        incidences,
    } = contact;
    let body = base
        .mount()
        .map_err(|refusal| ReturnedConductBoundaryRefusal::BaseRest {
            detail: refusal.to_string(),
        })?;
    let before =
        found_conditioned_circuit(body.standing().to_owned(), aperture).map_err(|refusal| {
            ReturnedConductBoundaryRefusal::Engine {
                detail: refusal.to_string(),
            }
        })?;
    let after = body
        .circuit_from_production(&query, first.to_owned(), aperture)
        .map_err(|refusal| ReturnedConductBoundaryRefusal::FirstProduction {
            detail: refusal.to_string(),
        })?;
    let production_reading = read_production(
        &before,
        &after,
        accumulation_rule,
        pivot_rule,
        &query.statement,
    )
    .map_err(|refusal| ReturnedConductBoundaryRefusal::ReturnedReading {
        detail: refusal.to_string(),
    })?;
    if production_reading.returned != sealed_reading {
        return Err(ReturnedConductBoundaryRefusal::ReturnedReadingSealDisagrees);
    }
    let reading = return_reading_identity(&reading_lineage);
    let source_lineage = return_source_lineage(&reading_lineage);
    let first_identity = FirstProductionIdentity {
        form: first_production.occurrence.as_str().to_owned(),
    };
    let atlas = ValidatedReturnedAtlas::validate(
        &body,
        &query,
        &before,
        &after,
        &first_identity,
        &first,
        &production_reading.routes,
        &reading,
        &source_lineage,
        incidences,
    )
    .map_err(|refusal| ReturnedConductBoundaryRefusal::Engine {
        detail: refusal.to_string(),
    })?;

    let exact_targets = atlas.targets().len();
    let exact_occurrences = atlas.occurrences().len();
    let exact_relations = atlas.relations().len();
    let front = cuda_front(&atlas)?;
    let cuda = executor
        .enact(&front)
        .map_err(|refusal| ReturnedConductBoundaryRefusal::Cuda {
            detail: refusal.to_string(),
        })?;
    let groups = groups_from_cuda(&atlas, &cuda.semantic)?;
    let morphology =
        ReturnedContactMorphology::found_from_groups(atlas, groups).map_err(|refusal| {
            ReturnedConductBoundaryRefusal::Engine {
                detail: refusal.to_string(),
            }
        })?;
    let rest = ReturnedCompositeRest::from_parts(base, rest_lineage, morphology)?;
    Ok(ReturnedConductOutput {
        rest,
        semantic: ReturnedConductBoundaryReceipt {
            schema: "soma-life.returned-conduct-boundary-receipt.v1".to_owned(),
            predecessor: AddressedReadReceipt::of(predecessor),
            first_production: AddressedReadReceipt::of(first_production),
            returned_reading: AddressedReadReceipt::of(returned_reading),
            returned_contact: AddressedReadReceipt::of(returned_contact),
            accumulation_rule,
            pivot_rule,
            exact_targets,
            exact_occurrences,
            exact_relations,
        },
        apparatus: cuda.apparatus,
    })
}

fn read_addressed(
    form: &AddressedForm,
    expected_schema: NativeFormSchema,
) -> Result<Box<[u8]>, ReturnedConductBoundaryRefusal> {
    if form.schema != expected_schema {
        return Err(ReturnedConductBoundaryRefusal::AddressedSchemaDisagrees {
            expected: expected_schema,
            declared: form.schema,
        });
    }
    let octets = std::fs::read(&form.path).map_err(|error| {
        ReturnedConductBoundaryRefusal::AddressedReadFailed {
            path: form.path.to_owned(),
            detail: error.to_string(),
        }
    })?;
    let opened = ContentAddress::of(&octets);
    if opened != form.expected_content {
        return Err(ReturnedConductBoundaryRefusal::AddressedContentDisagrees {
            path: form.path.to_owned(),
            expected: form.expected_content.render(),
            opened: opened.render(),
        });
    }
    Ok(octets.into_boxed_slice())
}

fn cuda_front(
    atlas: &ValidatedReturnedAtlas,
) -> Result<ReturnedContactCudaFront, ReturnedConductBoundaryRefusal> {
    let mut rows = LocalSequence::with_capacity(atlas.relations().len());
    for relation in atlas.relations() {
        let Some(occurrence) = atlas.occurrences().iter().position(|candidate| {
            candidate.occurrence == relation.cause.occurrence
                && candidate.source_lineage == relation.cause.source_lineage
        }) else {
            return Err(ReturnedConductBoundaryRefusal::CudaAtlasDisagrees);
        };
        let target = u32::try_from(relation.target).map_err(|_| {
            ReturnedConductBoundaryRefusal::ExtentExceedsCarrier {
                field: "CUDA target",
            }
        })?;
        let occurrence = u32::try_from(occurrence).map_err(|_| {
            ReturnedConductBoundaryRefusal::ExtentExceedsCarrier {
                field: "CUDA occurrence",
            }
        })?;
        let Some(row) = ReturnedContactRelation::new(
            target,
            occurrence,
            relation.cause.stood_before,
            relation.cause.stands_after,
        ) else {
            return Err(ReturnedConductBoundaryRefusal::CudaAtlasDisagrees);
        };
        rows.push(row);
    }
    ReturnedContactCudaFront::new(atlas.targets().len(), atlas.occurrences().len(), rows).map_err(
        |refusal| ReturnedConductBoundaryRefusal::Cuda {
            detail: refusal.to_string(),
        },
    )
}

fn groups_from_cuda(
    atlas: &ValidatedReturnedAtlas,
    returned: &ReturnedContactGroups,
) -> Result<LocalSequence<EngineReturnedTargetGroup>, ReturnedConductBoundaryRefusal> {
    if returned.targets.len() != atlas.targets().len()
        || returned.occurrences.len() != atlas.occurrences().len()
    {
        return Err(ReturnedConductBoundaryRefusal::CudaAtlasDisagrees);
    }
    for (at, occurrence) in returned.occurrences.iter().enumerate() {
        let Some(relation) = atlas.relations().iter().find(|relation| {
            relation.cause.occurrence == atlas.occurrences()[at].occurrence
                && relation.cause.source_lineage == atlas.occurrences()[at].source_lineage
        }) else {
            return Err(ReturnedConductBoundaryRefusal::CudaAtlasDisagrees);
        };
        let expected_withdrawn = u32::from(relation.cause.stood_before);
        let expected_founded = u32::from(relation.cause.stands_after);
        if occurrence.occurrence as usize != at
            || occurrence.is_uncontacted()
            || occurrence.withdrawn_targets != expected_withdrawn
            || occurrence.founded_targets != expected_founded
        {
            return Err(ReturnedConductBoundaryRefusal::CudaAtlasDisagrees);
        }
    }

    let mut groups = LocalSequence::new();
    for (target_at, target) in returned.targets.iter().enumerate() {
        if target.target as usize != target_at {
            return Err(ReturnedConductBoundaryRefusal::CudaAtlasDisagrees);
        }
        let mut causes = LocalSequence::new();
        for occurrence_at in 0..atlas.occurrences().len() {
            let ordinal = u32::try_from(occurrence_at).map_err(|_| {
                ReturnedConductBoundaryRefusal::ExtentExceedsCarrier {
                    field: "CUDA returned occurrence",
                }
            })?;
            let withdrawn = target.withdrawn_causes.contains(&ordinal);
            let founded = target.founded_causes.contains(&ordinal);
            if withdrawn && founded {
                return Err(ReturnedConductBoundaryRefusal::CudaAtlasDisagrees);
            }
            if !withdrawn && !founded {
                continue;
            }
            let declared = &atlas.occurrences()[occurrence_at];
            let Some(relation) = atlas.relations().iter().find(|relation| {
                relation.cause.occurrence == declared.occurrence
                    && relation.cause.source_lineage == declared.source_lineage
            }) else {
                return Err(ReturnedConductBoundaryRefusal::CudaAtlasDisagrees);
            };
            if relation.target as usize != target_at
                || withdrawn != relation.cause.stood_before
                || founded != relation.cause.stands_after
            {
                return Err(ReturnedConductBoundaryRefusal::CudaAtlasDisagrees);
            }
            causes.push(relation.cause.to_owned());
        }
        if !causes.is_empty() {
            groups.push(EngineReturnedTargetGroup {
                target: target.target as u64,
                causes,
            });
        }
    }
    Ok(groups)
}

fn put_lineage(
    octets: &mut LocalSequence<u8>,
    lineage: &FormLineage,
) -> Result<(), ReturnedConductBoundaryRefusal> {
    put_text(octets, lineage.occurrence.as_str(), "form occurrence")?;
    octets.extend_from_slice(&lineage.content.octets());
    Ok(())
}

fn put_incidence(
    octets: &mut LocalSequence<u8>,
    incidence: &ReturnedIncidence,
) -> Result<(), ReturnedConductBoundaryRefusal> {
    put_text(
        octets,
        &incidence.occurrence.reading.form,
        "incidence reading",
    )?;
    put_u64(octets, incidence.occurrence.ordinal);
    put_text(
        octets,
        &incidence.source_lineage.source,
        "incidence source lineage",
    )?;
    put_founded_route(octets, incidence.founded_route.as_ref())?;
    put_text(
        octets,
        &incidence.passage.first_production.form,
        "first-production occurrence",
    )?;
    put_u64(octets, incidence.passage.ordinal);
    put_passage(octets, &incidence.passage.passage)?;
    put_cell(octets, &incidence.cell)?;
    put_bool(octets, incidence.stood_before);
    put_bool(octets, incidence.stands_after);
    Ok(())
}

fn put_cause(
    octets: &mut LocalSequence<u8>,
    cause: &ReturnedCause,
) -> Result<(), ReturnedConductBoundaryRefusal> {
    put_text(octets, &cause.occurrence.reading.form, "cause reading")?;
    put_u64(octets, cause.occurrence.ordinal);
    put_text(octets, &cause.source_lineage.source, "cause source lineage")?;
    put_founded_route(octets, cause.founded_route.as_ref())?;
    put_cell(octets, &cause.cell)?;
    put_bool(octets, cause.stood_before);
    put_bool(octets, cause.stands_after);
    Ok(())
}

fn put_founded_route(
    octets: &mut LocalSequence<u8>,
    route: Option<&FoundedRouteAddress>,
) -> Result<(), ReturnedConductBoundaryRefusal> {
    match route {
        None => octets.push(0),
        Some(route) => {
            octets.push(1);
            put_text(octets, &route.statement, "founded-route statement")?;
            put_text(octets, &route.passage, "founded-route passage")?;
        }
    }
    Ok(())
}

fn put_site(
    octets: &mut LocalSequence<u8>,
    site: &PassageSite,
) -> Result<(), ReturnedConductBoundaryRefusal> {
    put_text(octets, &site.statement, "passage-site statement")?;
    put_text(octets, &site.reaches, "passage-site reach")?;
    put_text(octets, &site.stem, "passage-site stem")?;
    put_text(octets, &site.brought, "passage-site brought identifier")?;
    Ok(())
}

fn put_passage(
    octets: &mut LocalSequence<u8>,
    passage: &DerivedPassage,
) -> Result<(), ReturnedConductBoundaryRefusal> {
    for (run, field) in [
        (&passage.name, "passage name"),
        (&passage.statement, "passage statement"),
        (&passage.reaches, "passage reach"),
        (&passage.brought, "passage brought identifier"),
        (&passage.stem, "passage stem"),
        (&passage.text, "passage text"),
    ] {
        put_text(octets, run, field)?;
    }
    put_extent(octets, passage.bridges.len(), "passage bridges")?;
    for bridge in &passage.bridges {
        for (run, field) in [
            (&bridge.stem, "bridge stem"),
            (&bridge.held, "bridge held identifier"),
            (&bridge.brought, "bridge brought identifier"),
            (&bridge.route, "bridge route"),
        ] {
            put_text(octets, run, field)?;
        }
        put_extent(octets, bridge.held_at, "bridge held offset")?;
        put_extent(octets, bridge.brought_at, "bridge brought offset")?;
        for (members, field) in [
            (&bridge.held_face, "bridge held face"),
            (&bridge.brought_face, "bridge brought face"),
            (&bridge.held_crossings, "bridge held crossings"),
            (&bridge.brought_crossings, "bridge brought crossings"),
        ] {
            put_extent(octets, members.len(), field)?;
            for member in members {
                put_text(octets, member, field)?;
            }
        }
    }
    Ok(())
}

fn put_cell(
    octets: &mut LocalSequence<u8>,
    cell: &CellAddress,
) -> Result<(), ReturnedConductBoundaryRefusal> {
    put_u32(octets, cell.grade);
    put_text(octets, &cell.name, "cell name")?;
    put_extent(octets, cell.boundary.len(), "cell boundary")?;
    for member in &cell.boundary {
        put_u32(octets, member.grade);
        put_text(octets, &member.name, "boundary member name")?;
        put_biguint(octets, member.coefficient.positive_count())?;
        put_biguint(octets, member.coefficient.negative_count())?;
    }
    Ok(())
}

fn put_biguint(
    octets: &mut LocalSequence<u8>,
    value: &BigUint,
) -> Result<(), ReturnedConductBoundaryRefusal> {
    if value.bits() == 0 {
        return put_extent(octets, 0, "multiplicity magnitude");
    }
    let magnitude = value.to_bytes_le();
    put_bytes(octets, &magnitude, "multiplicity magnitude")
}

fn put_aperture(octets: &mut LocalSequence<u8>, aperture: CircuitAperture) {
    octets.push(match aperture.identity {
        DerivationIdentity::ByDeclaration => 0,
        DerivationIdentity::ByRoute => 1,
    });
    octets.push(match aperture.coefficient {
        RecruitmentCoefficient::Incidence => 0,
        RecruitmentCoefficient::Multiplicity => 1,
    });
    octets.push(match aperture.statements {
        StatementIncidence::Withheld => 0,
        StatementIncidence::Founded => 1,
    });
    // The reach orientation is on the wire, not defaulted on decode. A default would silently
    // collapse `OutOfDerivation` into the inherited convention on every round trip — the axis
    // would be carried by the type and lost by the boundary, which is the same shape as a
    // magnitude crossing a horizon.
    octets.push(match aperture.reach {
        ReachOrientation::IntoDerivation => 0,
        ReachOrientation::OutOfDerivation => 1,
    });
}

fn put_accumulation_rule(octets: &mut LocalSequence<u8>, rule: AccumulationRule) {
    octets.push(match rule {
        AccumulationRule::RouteLoad => 0,
        AccumulationRule::RecruitmentLoad => 1,
    });
}

fn put_pivot_rule(octets: &mut LocalSequence<u8>, rule: PivotRule) {
    octets.push(match rule {
        PivotRule::FirstNonzero => 0,
        PivotRule::SmallestMagnitude => 1,
        PivotRule::LargestMagnitude => 2,
    });
}

fn put_bool(octets: &mut LocalSequence<u8>, value: bool) {
    octets.push(u8::from(value));
}

fn put_u32(octets: &mut LocalSequence<u8>, value: u32) {
    octets.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(octets: &mut LocalSequence<u8>, value: u64) {
    octets.extend_from_slice(&value.to_le_bytes());
}

fn put_extent(
    octets: &mut LocalSequence<u8>,
    extent: usize,
    field: &'static str,
) -> Result<(), ReturnedConductBoundaryRefusal> {
    let extent = u64::try_from(extent)
        .map_err(|_| ReturnedConductBoundaryRefusal::ExtentExceedsCarrier { field })?;
    put_u64(octets, extent);
    Ok(())
}

fn put_text(
    octets: &mut LocalSequence<u8>,
    text: &str,
    field: &'static str,
) -> Result<(), ReturnedConductBoundaryRefusal> {
    put_bytes(octets, text.as_bytes(), field)
}

fn put_bytes(
    octets: &mut LocalSequence<u8>,
    run: &[u8],
    field: &'static str,
) -> Result<(), ReturnedConductBoundaryRefusal> {
    put_extent(octets, run.len(), field)?;
    octets.extend_from_slice(run);
    Ok(())
}

struct Cursor<'a> {
    octets: &'a [u8],
    at: usize,
}

impl<'a> Cursor<'a> {
    const fn new(octets: &'a [u8]) -> Self {
        Self { octets, at: 0 }
    }

    fn prefix(
        &mut self,
        expected: &[u8],
        schema: &'static str,
    ) -> Result<(), ReturnedConductBoundaryRefusal> {
        let opened = self.take(expected.len(), "wire prefix")?;
        if opened != expected {
            return Err(ReturnedConductBoundaryRefusal::NotThisForm { schema });
        }
        Ok(())
    }

    fn take(
        &mut self,
        extent: usize,
        field: &'static str,
    ) -> Result<&'a [u8], ReturnedConductBoundaryRefusal> {
        let Some(end) = self
            .at
            .checked_add(extent)
            .filter(|end| *end <= self.octets.len())
        else {
            return Err(ReturnedConductBoundaryRefusal::EndedInsideAField {
                field,
                declared: extent,
                remaining: self.octets.len().saturating_sub(self.at),
            });
        };
        let taken = &self.octets[self.at..end];
        self.at = end;
        Ok(taken)
    }

    fn byte(&mut self, field: &'static str) -> Result<u8, ReturnedConductBoundaryRefusal> {
        Ok(self.take(1, field)?[0])
    }

    fn u32(&mut self, field: &'static str) -> Result<u32, ReturnedConductBoundaryRefusal> {
        let mut bytes = [0u8; 4];
        bytes.copy_from_slice(self.take(4, field)?);
        Ok(u32::from_le_bytes(bytes))
    }

    fn u64(&mut self, field: &'static str) -> Result<u64, ReturnedConductBoundaryRefusal> {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(self.take(8, field)?);
        Ok(u64::from_le_bytes(bytes))
    }

    fn extent(&mut self, field: &'static str) -> Result<usize, ReturnedConductBoundaryRefusal> {
        usize::try_from(self.u64(field)?)
            .map_err(|_| ReturnedConductBoundaryRefusal::ExtentExceedsCarrier { field })
    }

    fn bytes(&mut self, field: &'static str) -> Result<&'a [u8], ReturnedConductBoundaryRefusal> {
        let extent = self.extent(field)?;
        self.take(extent, field)
    }

    fn text(&mut self, field: &'static str) -> Result<String, ReturnedConductBoundaryRefusal> {
        std::str::from_utf8(self.bytes(field)?)
            .map(str::to_owned)
            .map_err(|_| ReturnedConductBoundaryRefusal::NotUtf8 { field })
    }

    fn lineage(&mut self) -> Result<FormLineage, ReturnedConductBoundaryRefusal> {
        let occurrence = FormOccurrenceIdentity::new(self.text("form occurrence")?)?;
        let mut content = [0u8; 32];
        content.copy_from_slice(self.take(32, "form content address")?);
        Ok(FormLineage::new(occurrence, ContentAddress(content)))
    }

    fn aperture(&mut self) -> Result<CircuitAperture, ReturnedConductBoundaryRefusal> {
        let identity = match self.byte("derivation identity")? {
            0 => DerivationIdentity::ByDeclaration,
            1 => DerivationIdentity::ByRoute,
            tag => {
                return Err(ReturnedConductBoundaryRefusal::UnknownWireTag {
                    field: "derivation identity",
                    tag,
                })
            }
        };
        let coefficient = match self.byte("recruitment coefficient")? {
            0 => RecruitmentCoefficient::Incidence,
            1 => RecruitmentCoefficient::Multiplicity,
            tag => {
                return Err(ReturnedConductBoundaryRefusal::UnknownWireTag {
                    field: "recruitment coefficient",
                    tag,
                })
            }
        };
        let statements = match self.byte("statement incidence")? {
            0 => StatementIncidence::Withheld,
            1 => StatementIncidence::Founded,
            tag => {
                return Err(ReturnedConductBoundaryRefusal::UnknownWireTag {
                    field: "statement incidence",
                    tag,
                })
            }
        };
        let reach = match self.byte("reach orientation")? {
            0 => ReachOrientation::IntoDerivation,
            1 => ReachOrientation::OutOfDerivation,
            tag => {
                return Err(ReturnedConductBoundaryRefusal::UnknownWireTag {
                    field: "reach orientation",
                    tag,
                })
            }
        };
        Ok(CircuitAperture {
            identity,
            coefficient,
            statements,
            reach,
        })
    }

    fn accumulation_rule(&mut self) -> Result<AccumulationRule, ReturnedConductBoundaryRefusal> {
        match self.byte("accumulation rule")? {
            0 => Ok(AccumulationRule::RouteLoad),
            1 => Ok(AccumulationRule::RecruitmentLoad),
            tag => Err(ReturnedConductBoundaryRefusal::UnknownWireTag {
                field: "accumulation rule",
                tag,
            }),
        }
    }

    fn pivot_rule(&mut self) -> Result<PivotRule, ReturnedConductBoundaryRefusal> {
        match self.byte("pivot rule")? {
            0 => Ok(PivotRule::FirstNonzero),
            1 => Ok(PivotRule::SmallestMagnitude),
            2 => Ok(PivotRule::LargestMagnitude),
            tag => Err(ReturnedConductBoundaryRefusal::UnknownWireTag {
                field: "pivot rule",
                tag,
            }),
        }
    }

    fn incidence(&mut self) -> Result<ReturnedIncidence, ReturnedConductBoundaryRefusal> {
        let occurrence = ReturnOccurrenceId {
            reading: ReturnReadingIdentity {
                form: self.text("incidence reading")?,
            },
            ordinal: self.u64("incidence ordinal")?,
        };
        let source_lineage = ReturnSourceLineage {
            source: self.text("incidence source lineage")?,
        };
        let founded_route = self.founded_route()?;
        let passage = FirstPassageAddress {
            first_production: FirstProductionIdentity {
                form: self.text("first-production occurrence")?,
            },
            ordinal: self.u64("first-passage ordinal")?,
            passage: self.passage()?,
        };
        let cell = self.cell()?;
        let stood_before = self.boolean("stood-before state")?;
        let stands_after = self.boolean("stands-after state")?;
        Ok(ReturnedIncidence {
            occurrence,
            source_lineage,
            founded_route,
            passage,
            cell,
            stood_before,
            stands_after,
        })
    }

    fn cause(&mut self) -> Result<ReturnedCause, ReturnedConductBoundaryRefusal> {
        let occurrence = ReturnOccurrenceId {
            reading: ReturnReadingIdentity {
                form: self.text("cause reading")?,
            },
            ordinal: self.u64("cause ordinal")?,
        };
        let source_lineage = ReturnSourceLineage {
            source: self.text("cause source lineage")?,
        };
        let founded_route = self.founded_route()?;
        let cell = self.cell()?;
        let stood_before = self.boolean("cause stood-before state")?;
        let stands_after = self.boolean("cause stands-after state")?;
        Ok(ReturnedCause {
            occurrence,
            source_lineage,
            founded_route,
            cell,
            stood_before,
            stands_after,
        })
    }

    fn founded_route(
        &mut self,
    ) -> Result<Option<FoundedRouteAddress>, ReturnedConductBoundaryRefusal> {
        match self.byte("founded-route tag")? {
            0 => Ok(None),
            1 => Ok(Some(FoundedRouteAddress {
                statement: self.text("founded-route statement")?,
                passage: self.text("founded-route passage")?,
            })),
            tag => Err(ReturnedConductBoundaryRefusal::UnknownWireTag {
                field: "founded-route tag",
                tag,
            }),
        }
    }

    fn site(&mut self) -> Result<PassageSite, ReturnedConductBoundaryRefusal> {
        Ok(PassageSite {
            statement: self.text("passage-site statement")?,
            reaches: self.text("passage-site reach")?,
            stem: self.text("passage-site stem")?,
            brought: self.text("passage-site brought identifier")?,
        })
    }

    fn passage(&mut self) -> Result<DerivedPassage, ReturnedConductBoundaryRefusal> {
        let name = self.text("passage name")?;
        let statement = self.text("passage statement")?;
        let reaches = self.text("passage reach")?;
        let brought = self.text("passage brought identifier")?;
        let stem = self.text("passage stem")?;
        let text = self.text("passage text")?;
        let extent = self.extent("passage bridges")?;
        let mut bridges = LocalSequence::with_capacity(extent.min(1 << 16));
        for _ in 0..extent {
            bridges.push(Bridge {
                stem: self.text("bridge stem")?,
                held: self.text("bridge held identifier")?,
                brought: self.text("bridge brought identifier")?,
                route: self.text("bridge route")?,
                held_at: self.extent("bridge held offset")?,
                brought_at: self.extent("bridge brought offset")?,
                held_face: self.text_population("bridge held face")?.into_inner(),
                brought_face: self.text_population("bridge brought face")?.into_inner(),
                held_crossings: self.text_population("bridge held crossings")?.into_inner(),
                brought_crossings: self
                    .text_population("bridge brought crossings")?
                    .into_inner(),
            });
        }
        Ok(DerivedPassage {
            name,
            statement,
            reaches,
            brought,
            stem,
            bridges: bridges.into_inner(),
            text,
        })
    }

    fn text_population(
        &mut self,
        field: &'static str,
    ) -> Result<LocalSequence<String>, ReturnedConductBoundaryRefusal> {
        let extent = self.extent(field)?;
        let mut population = LocalSequence::with_capacity(extent.min(1 << 16));
        for _ in 0..extent {
            population.push(self.text(field)?);
        }
        Ok(population)
    }

    fn cell(&mut self) -> Result<CellAddress, ReturnedConductBoundaryRefusal> {
        let grade = self.u32("cell grade")?;
        let name = self.text("cell name")?;
        let extent = self.extent("cell boundary")?;
        let mut boundary = LocalSequence::with_capacity(extent.min(1 << 16));
        for _ in 0..extent {
            boundary.push(BoundaryMemberAddress {
                grade: self.u32("boundary member grade")?,
                name: self.text("boundary member name")?,
                coefficient: ComparativeMultiplicity::new(
                    self.biguint("positive multiplicity")?,
                    self.biguint("negative multiplicity")?,
                ),
            });
        }
        Ok(CellAddress {
            grade,
            name,
            boundary,
        })
    }

    fn biguint(&mut self, field: &'static str) -> Result<BigUint, ReturnedConductBoundaryRefusal> {
        let magnitude = self.bytes(field)?;
        if magnitude.last() == Some(&0) {
            return Err(ReturnedConductBoundaryRefusal::NonCanonicalMagnitude { field });
        }
        Ok(BigUint::from_bytes_le(magnitude))
    }

    fn boolean(&mut self, field: &'static str) -> Result<bool, ReturnedConductBoundaryRefusal> {
        match self.byte(field)? {
            0 => Ok(false),
            1 => Ok(true),
            tag => Err(ReturnedConductBoundaryRefusal::UnknownWireTag { field, tag }),
        }
    }

    fn finish(self) -> Result<(), ReturnedConductBoundaryRefusal> {
        let remaining = self.octets.len().saturating_sub(self.at);
        if remaining != 0 {
            return Err(ReturnedConductBoundaryRefusal::TrailingOctets { remaining });
        }
        Ok(())
    }
}

/// Every refusal names the exact boundary that failed; no decoder guesses or repairs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReturnedConductBoundaryRefusal {
    ContentAddressIsNotCanonical {
        address: String,
    },
    FormOccurrenceIsEmpty,
    FormOccurrencesAreNotDistinct,
    QueryIsEmpty,
    IncidenceIdentityDisagrees {
        at: usize,
    },
    IncidenceIsNotMovement {
        at: usize,
    },
    IncidenceRouteDirectionDisagrees {
        at: usize,
    },
    IncidencesAreNotCanonical {
        at: usize,
    },
    AddressedSchemaDisagrees {
        expected: NativeFormSchema,
        declared: NativeFormSchema,
    },
    AddressedReadFailed {
        path: PathBuf,
        detail: String,
    },
    AddressedContentDisagrees {
        path: PathBuf,
        expected: String,
        opened: String,
    },
    PredecessorLineageDisagrees,
    FirstProductionLineageDisagrees,
    ReturnedReadingLineageDisagrees,
    ReturnedReadingSealDisagrees,
    RestFirstProductionDisagrees,
    RestPredecessorContentDisagrees,
    RestReadingIdentityDisagrees,
    RestSourceLineageDisagrees,
    CudaAtlasDisagrees,
    NotThisForm {
        schema: &'static str,
    },
    EndedInsideAField {
        field: &'static str,
        declared: usize,
        remaining: usize,
    },
    ExtentExceedsCarrier {
        field: &'static str,
    },
    NotUtf8 {
        field: &'static str,
    },
    UnknownWireTag {
        field: &'static str,
        tag: u8,
    },
    NonCanonicalMagnitude {
        field: &'static str,
    },
    TrailingOctets {
        remaining: usize,
    },
    BaseRest {
        detail: String,
    },
    FirstProduction {
        detail: String,
    },
    ReturnedReading {
        detail: String,
    },
    Engine {
        detail: String,
    },
    Cuda {
        detail: String,
    },
}

impl std::fmt::Display for ReturnedConductBoundaryRefusal {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(out, "returned-conduct boundary refused: {self:?}")
    }
}

impl std::error::Error for ReturnedConductBoundaryRefusal {}

// Kept here rather than in a test helper module so concurrent owner-local tests can mint unique
// apparatus paths without a global collection or an inferred repository coordinate.
#[cfg(test)]
static TEST_WORLD_ORDINAL: AtomicU64 = AtomicU64::new(0);

#[cfg(test)]
mod tests {
    use super::*;
    use holonic_engine::{
        conditioned_derivation::{expose, ConditionedBody},
        returned_conduct::canonical_incidences,
    };

    const STATEMENT: &str = "(h : P) : exactCarrier P";

    struct TestWorld {
        root: PathBuf,
    }

    impl TestWorld {
        fn new(label: &str) -> Self {
            let ordinal = TEST_WORLD_ORDINAL.fetch_add(1, Ordering::Relaxed);
            let root = std::env::temp_dir().join(format!(
                "holonics-returned-conduct-{}-{label}-{ordinal}",
                std::process::id()
            ));
            std::fs::create_dir_all(&root).expect("create exact test world");
            Self { root }
        }

        fn addressed(
            &self,
            name: &str,
            schema: NativeFormSchema,
            occurrence: &str,
            octets: &[u8],
        ) -> AddressedForm {
            let path = self.root.join(name);
            std::fs::write(&path, octets).expect("write addressed form");
            AddressedForm::new(
                path,
                &ContentAddress::of(octets).render(),
                schema,
                occurrence.to_owned(),
            )
            .expect("declare addressed form")
        }

        fn detach(&self) {
            if self.root.exists() {
                std::fs::remove_dir_all(&self.root).expect("detach exact test world");
            }
        }
    }

    impl Drop for TestWorld {
        fn drop(&mut self) {
            if self.root.exists() {
                std::fs::remove_dir_all(&self.root).expect("remove exact test world");
            }
        }
    }

    fn standing() -> LocalSequence<(String, String)> {
        LocalSequence::from([
            (
                "alpha.lean".to_owned(),
                "namespace Soma\ntheorem carrier_alpha (h : P) : exactCarrier P := by\n  have bridged := exactCarry h\nend Soma\n".to_owned(),
            ),
            (
                "beta.lean".to_owned(),
                "namespace Soma\ntheorem carrier_beta (h : P) : exactCarrier P := by\n  have bridged := formalKernel h\nend Soma\n".to_owned(),
            ),
            (
                "gamma.lean".to_owned(),
                "namespace Soma\ntheorem transport_gamma (a b : Nat) : a = b := by\n  have bridged := exactTransport a\nend Soma\n".to_owned(),
            ),
        ])
    }

    fn conditioned_body() -> ConditionedBody {
        let mut body = ConditionedBody::mount(standing()).expect("mount standing");
        body.condition(&[
            expose(
                "corpus/one",
                "exact carrier formal kernel transport exactCarry formalKernel",
            ),
            expose(
                "corpus/two",
                "formal carrier exact kernel transport exactCarry formalKernel",
            ),
        ]);
        body
    }

    fn lineage(identity: &str, fill: u8) -> FormLineage {
        FormLineage::new(
            FormOccurrenceIdentity::new(identity.to_owned()).expect("occurrence"),
            ContentAddress([fill; 32]),
        )
    }

    fn simple_passage() -> DerivedPassage {
        DerivedPassage {
            name: "returned_fixture".to_owned(),
            statement: STATEMENT.to_owned(),
            reaches: "carrier_alpha".to_owned(),
            brought: "formalKernel".to_owned(),
            stem: "formal".to_owned(),
            bridges: LocalSequence::new().into_inner(),
            text: "theorem returned_fixture (h : P) : exactCarrier P := by exact h".to_owned(),
        }
    }

    fn simple_cell() -> CellAddress {
        CellAddress {
            grade: 0,
            name: "returned_fixture".to_owned(),
            boundary: LocalSequence::new(),
        }
    }

    fn sample_contact() -> ReturnedContactForm {
        let reading_lineage = lineage("reading/occurrence", 3);
        let reading = return_reading_identity(&reading_lineage);
        let source_lineage = return_source_lineage(&reading_lineage);
        let incidences = LocalSequence::from([ReturnedIncidence {
            occurrence: ReturnOccurrenceId {
                reading: reading.to_owned(),
                ordinal: 0,
            },
            source_lineage: source_lineage.to_owned(),
            founded_route: Some(FoundedRouteAddress {
                statement: STATEMENT.to_owned(),
                passage: "returned_fixture".to_owned(),
            }),
            passage: FirstPassageAddress {
                first_production: FirstProductionIdentity {
                    form: "first/occurrence".to_owned(),
                },
                ordinal: 0,
                passage: simple_passage(),
            },
            cell: simple_cell(),
            stood_before: false,
            stands_after: true,
        }]);
        ReturnedContactForm::seal(
            lineage("predecessor/occurrence", 1),
            lineage("first/occurrence", 2),
            reading_lineage,
            AccumulationRule::RecruitmentLoad,
            PivotRule::SmallestMagnitude,
            DerivationQuery::reaching(STATEMENT),
            CircuitAperture::STATEMENT_INCIDENT,
            incidences,
        )
        .expect("sample contact")
    }

    fn sample_composite_rest() -> ReturnedCompositeRest {
        let body = ConditionedBody::mount(LocalSequence::from([(
            "base.lean".to_owned(),
            "theorem base (h : P) : exactCarrier P := by exact h".to_owned(),
        )]))
        .expect("sample base");
        let base = ConditionedRest::seal(&body).expect("sample base rest");
        let base_content = ContentAddress::of(
            &base
                .encode_native_bytes()
                .expect("encode sample base for address"),
        );
        let reading_lineage = lineage("reading/occurrence", 3);
        let reading = return_reading_identity(&reading_lineage);
        let source_lineage = return_source_lineage(&reading_lineage);
        let records = LocalSequence::from([ReturnedContactRecord {
            site: PassageSite {
                statement: STATEMENT.to_owned(),
                reaches: "carrier_alpha".to_owned(),
                stem: "formal".to_owned(),
                brought: "formalKernel".to_owned(),
            },
            causes: LocalSequence::from([ReturnedCause {
                occurrence: ReturnOccurrenceId {
                    reading,
                    ordinal: 0,
                },
                source_lineage,
                founded_route: Some(FoundedRouteAddress {
                    statement: STATEMENT.to_owned(),
                    passage: "returned_fixture".to_owned(),
                }),
                cell: simple_cell(),
                stood_before: false,
                stands_after: true,
            }]),
        }]);
        let morphology = ReturnedContactMorphology::resume(
            FirstProductionIdentity {
                form: "first/occurrence".to_owned(),
            },
            records,
        )
        .expect("sample returned morphology");
        ReturnedCompositeRest::from_parts(
            base,
            ReturnedRestLineage::new(
                FormLineage::new(
                    FormOccurrenceIdentity::new("predecessor/occurrence".to_owned())
                        .expect("predecessor occurrence"),
                    base_content,
                ),
                lineage("first/occurrence", 2),
                reading_lineage,
                lineage("contact/occurrence", 4),
            )
            .expect("sample lineage"),
            morphology,
        )
        .expect("sample composite rest")
    }

    fn contains_run(haystack: &[u8], needle: &[u8]) -> bool {
        !needle.is_empty()
            && haystack
                .windows(needle.len())
                .any(|window| window == needle)
    }

    fn validated_atlas() -> ValidatedReturnedAtlas {
        let body = conditioned_body();
        let query = DerivationQuery::reaching(STATEMENT);
        let first = body.derive(&query).expect("atlas first production");
        let before = found_conditioned_circuit(
            body.standing().to_owned(),
            CircuitAperture::STATEMENT_INCIDENT,
        )
        .expect("atlas standing circuit");
        let after = body
            .circuit_from_production(
                &query,
                first.to_owned(),
                CircuitAperture::STATEMENT_INCIDENT,
            )
            .expect("atlas first circuit");
        let first_identity = FirstProductionIdentity {
            form: "first/atlas".to_owned(),
        };
        let reading_lineage = lineage("reading/atlas", 7);
        let reading = return_reading_identity(&reading_lineage);
        let source = return_source_lineage(&reading_lineage);
        let production_reading = read_production(
            &before,
            &after,
            AccumulationRule::RecruitmentLoad,
            PivotRule::SmallestMagnitude,
            &query.statement,
        )
        .expect("atlas returned reading");
        let rows = canonical_incidences(
            &before,
            &after,
            &first_identity,
            &first,
            &production_reading.routes,
            &reading,
            &source,
        )
        .expect("atlas rows");
        ValidatedReturnedAtlas::validate(
            &body,
            &query,
            &before,
            &after,
            &first_identity,
            &first,
            &production_reading.routes,
            &reading,
            &source,
            rows,
        )
        .expect("validated atlas")
    }

    #[test]
    fn addressed_form_keeps_occurrence_content_schema_and_path_distinct() {
        let world = TestWorld::new("address-kinds");
        let octets = b"equal form content";
        let left = world.addressed(
            "left.form",
            NativeFormSchema::ReturnedContact,
            "occurrence/left",
            octets,
        );
        let right = world.addressed(
            "right.form",
            NativeFormSchema::ReturnedContact,
            "occurrence/right",
            octets,
        );
        assert_eq!(left.expected_content(), right.expected_content());
        assert_ne!(left.occurrence(), right.occurrence());
        assert_ne!(left.path(), right.path());
        assert_eq!(left.schema(), right.schema());
        assert_eq!(
            read_addressed(&left, NativeFormSchema::ReturnedContact)
                .unwrap()
                .as_ref(),
            octets
        );

        let missing = AddressedForm::new(
            world.root.join("missing.form"),
            &ContentAddress::of(octets).render(),
            NativeFormSchema::ReturnedContact,
            "occurrence/missing".to_owned(),
        )
        .expect("missing descriptor");
        assert!(matches!(
            read_addressed(&missing, NativeFormSchema::ReturnedContact),
            Err(ReturnedConductBoundaryRefusal::AddressedReadFailed { .. })
        ));

        std::fs::write(left.path(), b"changed").expect("corrupt addressed form");
        assert!(matches!(
            read_addressed(&left, NativeFormSchema::ReturnedContact),
            Err(ReturnedConductBoundaryRefusal::AddressedContentDisagrees { .. })
        ));
        assert!(matches!(
            read_addressed(&right, NativeFormSchema::ConditionedRest),
            Err(ReturnedConductBoundaryRefusal::AddressedSchemaDisagrees { .. })
        ));
    }

    #[test]
    fn rtcf_is_fixed_strict_and_refuses_identity_redistribution() {
        let form = sample_contact();
        let encoded = form.encode_native_bytes().expect("encode RTCF");
        let decoded = ReturnedContactForm::decode_native_bytes(&encoded).expect("decode RTCF");
        assert_eq!(decoded, form);
        assert_eq!(
            decoded.encode_native_bytes().expect("re-encode RTCF"),
            encoded
        );

        for cut in 0..encoded.len() {
            assert!(ReturnedContactForm::decode_native_bytes(&encoded[..cut]).is_err());
        }
        let mut trailing = encoded.to_owned();
        trailing.push(0);
        assert!(matches!(
            ReturnedContactForm::decode_native_bytes(&trailing),
            Err(ReturnedConductBoundaryRefusal::TrailingOctets { remaining: 1 })
        ));
        let mut version = encoded.to_owned();
        version[7] = 2;
        assert!(matches!(
            ReturnedContactForm::decode_native_bytes(&version),
            Err(ReturnedConductBoundaryRefusal::NotThisForm { schema: "RTCF" })
        ));
        let mut bad_direction = encoded.to_owned();
        let last = bad_direction.len() - 1;
        bad_direction[last] = 0;
        assert!(matches!(
            ReturnedContactForm::decode_native_bytes(&bad_direction),
            Err(ReturnedConductBoundaryRefusal::IncidenceIsNotMovement { at: 0 })
        ));

        let ReturnedContactForm {
            predecessor,
            first_production,
            returned_reading,
            accumulation_rule,
            pivot_rule,
            query,
            aperture,
            incidences,
        } = sample_contact();
        let mut duplicate = incidences.to_owned();
        duplicate.push(incidences[0].to_owned());
        assert!(matches!(
            ReturnedContactForm::seal(
                predecessor,
                first_production,
                returned_reading,
                accumulation_rule,
                pivot_rule,
                query,
                aperture,
                duplicate,
            ),
            Err(ReturnedConductBoundaryRefusal::IncidenceIdentityDisagrees { at: 1 })
        ));
    }

    #[test]
    fn crst_is_fixed_strict_and_delegates_semantic_corruption_to_the_engine() {
        let rest = sample_composite_rest();
        let encoded = rest.encode_native_bytes().expect("encode CRST");
        let decoded = ReturnedCompositeRest::decode_native_bytes(&encoded).expect("decode CRST");
        assert_eq!(decoded, rest);
        assert_eq!(
            decoded.encode_native_bytes().expect("re-encode CRST"),
            encoded
        );

        for cut in 0..encoded.len() {
            assert!(ReturnedCompositeRest::decode_native_bytes(&encoded[..cut]).is_err());
        }
        let mut trailing = encoded.to_owned();
        trailing.push(0);
        assert!(matches!(
            ReturnedCompositeRest::decode_native_bytes(&trailing),
            Err(ReturnedConductBoundaryRefusal::TrailingOctets { remaining: 1 })
        ));
        let mut version = encoded.to_owned();
        version[7] = 2;
        assert!(matches!(
            ReturnedCompositeRest::decode_native_bytes(&version),
            Err(ReturnedConductBoundaryRefusal::NotThisForm { schema: "CRST" })
        ));
        let mut bad_direction = encoded.to_owned();
        let last = bad_direction.len() - 1;
        bad_direction[last] = 0;
        assert!(matches!(
            ReturnedCompositeRest::decode_native_bytes(&bad_direction),
            Err(ReturnedConductBoundaryRefusal::Engine { .. })
        ));

        let mut false_predecessor = encoded.to_owned();
        let digest_at =
            RETURNED_COMPOSITE_REST_PREFIX.len() + 8 + "predecessor/occurrence".as_bytes().len();
        false_predecessor[digest_at] ^= 1;
        assert!(matches!(
            ReturnedCompositeRest::decode_native_bytes(&false_predecessor),
            Err(ReturnedConductBoundaryRefusal::RestPredecessorContentDisagrees)
        ));

        let noncanonical_magnitude = [2, 0, 0, 0, 0, 0, 0, 0, 1, 0];
        let mut cursor = Cursor::new(&noncanonical_magnitude);
        assert!(matches!(
            cursor.biguint("test multiplicity"),
            Err(ReturnedConductBoundaryRefusal::NonCanonicalMagnitude {
                field: "test multiplicity"
            })
        ));
    }

    #[test]
    fn cuda_occurrence_face_must_match_the_exact_target_direction() {
        let atlas = validated_atlas();
        let mut targets = LocalSequence::new();
        for target_at in 0..atlas.targets().len() {
            let mut withdrawn_causes = LocalSequence::new();
            let mut founded_causes = LocalSequence::new();
            for (occurrence_at, occurrence) in atlas.occurrences().iter().enumerate() {
                let relation = atlas
                    .relations()
                    .iter()
                    .find(|relation| {
                        relation.cause.occurrence == occurrence.occurrence
                            && relation.cause.source_lineage == occurrence.source_lineage
                    })
                    .expect("one relation per occurrence");
                if relation.target as usize == target_at {
                    if relation.cause.stood_before {
                        withdrawn_causes.push(occurrence_at as u32);
                    } else {
                        founded_causes.push(occurrence_at as u32);
                    }
                }
            }
            targets.push(crate::returned_contact_cuda::ReturnedTargetGroup {
                target: target_at as u32,
                withdrawn_causes,
                founded_causes,
            });
        }
        let mut occurrences = LocalSequence::new();
        for (at, declared) in atlas.occurrences().iter().enumerate() {
            let relation = atlas
                .relations()
                .iter()
                .find(|relation| {
                    relation.cause.occurrence == declared.occurrence
                        && relation.cause.source_lineage == declared.source_lineage
                })
                .expect("one relation per occurrence");
            let (withdrawn_targets, founded_targets) = if at == 0 {
                (
                    u32::from(relation.cause.stands_after),
                    u32::from(relation.cause.stood_before),
                )
            } else {
                (
                    u32::from(relation.cause.stood_before),
                    u32::from(relation.cause.stands_after),
                )
            };
            occurrences.push(
                crate::returned_contact_cuda::ReturnedOccurrenceDisposition {
                    occurrence: at as u32,
                    withdrawn_targets,
                    founded_targets,
                },
            );
        }
        let forged = ReturnedContactGroups {
            schema: "soma-life.returned-contact-groups.v1".to_owned(),
            targets,
            occurrences,
        };
        assert!(matches!(
            groups_from_cuda(&atlas, &forged),
            Err(ReturnedConductBoundaryRefusal::CudaAtlasDisagrees)
        ));
    }

    struct WorldFixture {
        world: TestWorld,
        predecessor: AddressedForm,
        first: AddressedForm,
        reading: AddressedForm,
        contact: AddressedForm,
        query: DerivationQuery,
        first_octets: LocalSequence<u8>,
        reading_octets: LocalSequence<u8>,
        contact_octets: LocalSequence<u8>,
        first_text: String,
    }

    fn world_fixture() -> WorldFixture {
        let world = TestWorld::new("whole-deed");
        let body = conditioned_body();
        let query = DerivationQuery::reaching(STATEMENT);
        let base = ConditionedRest::seal(&body).expect("seal predecessor");
        let base_octets = base.encode_native_bytes().expect("encode predecessor");
        let predecessor = world.addressed(
            "predecessor.form",
            NativeFormSchema::ConditionedRest,
            "predecessor/turn-zero",
            &base_octets,
        );

        let first = body.derive(&query).expect("first production");
        assert!(first.len() > 1);
        let first_text = first[0].text.to_owned();
        let first_octets =
            LocalSequence::from_slice(&crate::conditioned_rest::render_derived_passages(&first));
        let first_form = world.addressed(
            "first.form",
            NativeFormSchema::DerivedProduction,
            "first/turn-one",
            &first_octets,
        );
        let before = found_conditioned_circuit(
            body.standing().to_owned(),
            CircuitAperture::STATEMENT_INCIDENT,
        )
        .expect("standing circuit");
        let after = body
            .circuit_from_production(
                &query,
                first.to_owned(),
                CircuitAperture::STATEMENT_INCIDENT,
            )
            .expect("first-production circuit");
        let production_reading = read_production(
            &before,
            &after,
            AccumulationRule::RecruitmentLoad,
            PivotRule::SmallestMagnitude,
            &query.statement,
        )
        .expect("read deposited first production");
        let reading_octets = LocalSequence::from_slice(&production_reading.returned.seal());
        let reading_form = world.addressed(
            "reading.form",
            NativeFormSchema::ReturnedReading,
            "reading/turn-one",
            &reading_octets,
        );
        let reading = return_reading_identity(&reading_form.lineage());
        let source_lineage = return_source_lineage(&reading_form.lineage());
        let incidences = canonical_incidences(
            &before,
            &after,
            &FirstProductionIdentity {
                form: first_form.occurrence().as_str().to_owned(),
            },
            &first,
            &production_reading.routes,
            &reading,
            &source_lineage,
        )
        .expect("canonical returned incidences");
        assert!(!incidences.is_empty());
        let contact = ReturnedContactForm::seal(
            predecessor.lineage(),
            first_form.lineage(),
            reading_form.lineage(),
            AccumulationRule::RecruitmentLoad,
            PivotRule::SmallestMagnitude,
            query.to_owned(),
            CircuitAperture::STATEMENT_INCIDENT,
            incidences,
        )
        .expect("typed contact form");
        let contact_octets = contact.encode_native_bytes().expect("encode typed contact");
        let contact_form = world.addressed(
            "contact.form",
            NativeFormSchema::ReturnedContact,
            "contact/turn-one-projection",
            &contact_octets,
        );
        WorldFixture {
            world,
            predecessor,
            first: first_form,
            reading: reading_form,
            contact: contact_form,
            query,
            first_octets,
            reading_octets,
            contact_octets,
            first_text,
        }
    }

    #[test]
    fn cuda_conduct_is_world_read_source_free_idempotent_and_exactly_ablatable() {
        let fixture = world_fixture();
        let mut executor = CudaReturnedContactExecutor::new(0).expect("mount CUDA executor");

        let full = conduct_returned_contact(
            &fixture.predecessor,
            &fixture.first,
            &fixture.reading,
            &fixture.contact,
            &mut executor,
        )
        .expect("full world-read conduct");
        let targeted = conduct_returned_contact(
            &fixture.predecessor,
            &fixture.first,
            &fixture.reading,
            &fixture.contact,
            &mut executor,
        )
        .expect("target branch world-read conduct");
        let all = conduct_returned_contact(
            &fixture.predecessor,
            &fixture.first,
            &fixture.reading,
            &fixture.contact,
            &mut executor,
        )
        .expect("all-ablated branch world-read conduct");
        assert_eq!(executor.launches(), 3);
        assert_eq!(full.apparatus.kernel_launches, 1);
        assert_eq!(targeted.apparatus.kernel_launches, 1);
        assert_eq!(all.apparatus.kernel_launches, 1);
        assert!(full.semantic.exact_relations > 0);

        let full_rest = full.rest.encode_native_bytes().expect("encode full CRST");
        let targeted_rest = targeted
            .rest
            .encode_native_bytes()
            .expect("encode target CRST");
        let all_rest = all.rest.encode_native_bytes().expect("encode all CRST");
        assert_eq!(full_rest, targeted_rest);
        assert_eq!(full_rest, all_rest);
        assert!(!contains_run(&full_rest, &fixture.first_octets));
        assert!(!contains_run(&full_rest, &fixture.reading_octets));
        assert!(!contains_run(&full_rest, &fixture.contact_octets));
        assert!(!contains_run(&full_rest, &DERIVED_PASSAGE_RENDERING_PREFIX));
        assert!(!contains_run(&full_rest, &RETURNED_CONTACT_FORM_PREFIX));
        assert!(!contains_run(&full_rest, fixture.first_text.as_bytes()));
        assert!(contains_run(&full_rest, &CONDITIONED_REST_PREFIX));

        let reading_path = fixture.reading.path().to_owned();
        std::fs::remove_file(&reading_path).expect("delete only returned-reading seal");
        match conduct_returned_contact(
            &fixture.predecessor,
            &fixture.first,
            &fixture.reading,
            &fixture.contact,
            &mut executor,
        ) {
            Err(ReturnedConductBoundaryRefusal::AddressedReadFailed { path, .. }) => {
                assert_eq!(path, reading_path);
            }
            _ => panic!("deleted returned-reading seal did not refuse at its exact path"),
        }
        assert_eq!(executor.launches(), 3);
        fixture.world.detach();

        let full_owner = ReturnedCompositeRest::decode_native_bytes(&full_rest)
            .expect("source-free full decode")
            .mount()
            .expect("source-free full mount");
        let target_owner = ReturnedCompositeRest::decode_native_bytes(&targeted_rest)
            .expect("source-free target decode")
            .mount()
            .expect("source-free target mount");
        let all_owner = ReturnedCompositeRest::decode_native_bytes(&all_rest)
            .expect("source-free all decode")
            .mount()
            .expect("source-free all mount");

        assert!(full_owner.returned_records().len() > 1);
        let removed_site = full_owner.returned_records()[0].site.to_owned();
        let full_production = full_owner.produce(&fixture.query).expect("full production");
        let full_circuit = full_owner
            .found_circuit(
                &full_production,
                &fixture.query,
                CircuitAperture::STATEMENT_INCIDENT,
            )
            .expect("full circuit");
        let base_circuit = full_owner
            .base_circuit(&fixture.query, CircuitAperture::STATEMENT_INCIDENT)
            .expect("base circuit");
        assert_ne!(
            full_circuit.circuit.complex().cells().len(),
            base_circuit.circuit.complex().cells().len()
        );

        let targeted = target_owner
            .ablate_site(&removed_site)
            .expect("targeted ablation");
        assert_eq!(targeted.removed.site, removed_site);
        let targeted_production = targeted
            .body
            .produce(&fixture.query)
            .expect("targeted production");
        assert_eq!(
            targeted_production.returned().len() + 1,
            full_production.returned().len()
        );
        assert!(targeted_production
            .returned()
            .iter()
            .all(|route| route.site != removed_site));
        for route in targeted_production.returned() {
            assert!(full_production.returned().contains(route));
        }

        let all = all_owner.ablate_all().expect("complete ablation");
        assert_eq!(all.removed.len(), full_owner.returned_records().len());
        let all_production = all
            .body
            .produce(&fixture.query)
            .expect("base-only production");
        assert!(all_production.returned().is_empty());
        assert_eq!(all_production.base(), full_production.base());

        let settled = full_owner.settle().expect("settle full owner");
        assert_eq!(
            settled
                .encode_native_bytes()
                .expect("re-encode settled CRST"),
            full_rest
        );
    }
}
