const REST_SCHEMA: &str = "soma-life.affine-laboratory-cultivated-rest.v1";
const ADMITTED_REST_WITNESS_SCHEMA: &str = "soma-life.affine-laboratory-admitted-rest-witness.v1";
const RETURNED_REST_SCHEMA: &str = "soma-life.returned-affine-laboratory-cultivated-rest.v1";
const RECURRENT_RETURNED_REST_SCHEMA: &str =
    "soma-life.recurrent-returned-affine-laboratory-cultivated-rest.v1";
const ADMITTED_RETURNED_REST_WITNESS_SCHEMA: &str =
    "soma-life.returned-affine-laboratory-admitted-rest-witness.v1";
const FACTOR_ADDRESS_DOMAIN: &[u8] = b"soma-life.affine-laboratory-factor.v1";

/// One of the four exact L2 fibres over an addressed receiver-history landmark.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryCycleFibreAddress {
    pub coordinate: usize,
    pub thread_address: String,
    pub exact_fibre_address: String,
}

/// Exact correspondence from one affine base landmark to its four local period-lattice fibres.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryFactorCycleCorrespondence {
    pub factor: u32,
    pub factor_address: String,
    pub native: NativeStateId,
    pub cycle_fibres: Vec<LaboratoryCycleFibreAddress>,
}

/// Derived affine coordinates of one native relational cell.
///
/// `occurrence_multiplicities` are the complete integer population.  `barycentric_weights` are
/// their normalized receiver chart and never replace that population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryCellAffineSection {
    pub cell_address: String,
    pub landmark_factors: Vec<u32>,
    pub occurrence_multiplicities: Vec<u64>,
    pub barycentric_weights: Vec<Rat>,
    pub source_occurrence_identities_sha256: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryCultivationReceipt {
    pub predecessor_rest_identity_sha256: String,
    pub cultivated_rest_identity_sha256: String,
    pub addressed_factor_population: usize,
    pub cycle_coordinate_population_per_factor: usize,
    pub exact_cycle_fibre_population: usize,
    pub delivered_occurrence_population: u64,
    pub relational_clause_population: u64,
    pub native_face_population: usize,
    pub native_cell_population: usize,
    pub affine_cell_population: usize,
    pub factor_world_line_join_population: usize,
    pub aggregate_count_coordinate_population: usize,
    pub additional_winding_thread_population: usize,
    pub complete_source_occurrence_lineage_retained: bool,
    pub barycentric_reconstruction_population_retained: bool,
}

/// A later receiver occurrence addressed to the one dialogue participant port. The proper name
/// and deictic chart are exterior projection coordinates and never select cultivated morphology.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryParticipantIngress {
    pub occurrence: String,
    pub participant: EmanationParticipant,
    pub deed: EmanationDeed,
    pub perspective: PerspectiveChart,
}

impl LaboratoryParticipantIngress {
    pub fn found(
        occurrence: impl Into<String>,
        participant: EmanationParticipant,
        deed: EmanationDeed,
        perspective: PerspectiveChart,
    ) -> Result<Self, LaboratoryCultivationError> {
        let ingress = Self {
            occurrence: occurrence.into(),
            participant,
            deed,
            perspective,
        };
        if ingress.occurrence.is_empty()
            || ingress.participant.occurrence.is_empty()
            || ingress.participant.identity.is_empty()
            || ingress.participant.proper_name.is_empty()
            || ingress.perspective.occurrence.is_empty()
            || ingress
                .perspective
                .speaker
                .as_ref()
                .is_some_and(String::is_empty)
            || ingress
                .perspective
                .addressee
                .as_ref()
                .is_some_and(String::is_empty)
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the participant receiver chart is incomplete".to_owned(),
            ));
        }
        Ok(ingress)
    }
}

/// One complete participant receiver return. Cell selection is the GPU return; English is a
/// later boundary projection of exactly those native sections.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryParticipantEmanation {
    pub ingress_occurrence: String,
    pub rest_identity_sha256: String,
    pub deed: EmanationDeed,
    pub perspective_surface: String,
    pub native_successor_identity_sha256: String,
    pub selected_cell_addresses: Vec<String>,
    pub selected_affine_sections: Vec<LaboratoryCellAffineSection>,
    pub hidden_participant_cell_fibre: Vec<String>,
    pub text: String,
    pub text_sha256: String,
    pub apparatus: ResidentParticipantCausalFrontReturn,
}

/// The repaired L5 type-state successor.  It owns the sole L2 body and one relational organ over
/// its addressed affine base.  There is no independently conductible predecessor beside it.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AffineLaboratoryCultivatedRest {
    schema: String,
    predecessor_rest_identity_sha256: String,
    body: SituatedCultivatedEcologyRest,
    potential: NativeRelationalPotentialComplex,
    codec: NativeRelationalCodec,
    correspondences: Vec<LaboratoryFactorCycleCorrespondence>,
    affine_cells: Vec<LaboratoryCellAffineSection>,
    identity_sha256: String,
}

/// The affine Athena body after one genuinely returned situated difference has cultivated its
/// native ecology.  The relational organ is retained around the moved successor ecology; the
/// predecessor does not remain independently conductible beside it.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnedAffineLaboratoryRest {
    schema: String,
    predecessor_rest_identity_sha256: String,
    predecessor_body_identity_sha256: String,
    body: LaboratoryCultivatedRest,
    potential: NativeRelationalPotentialComplex,
    codec: NativeRelationalCodec,
    correspondences: Vec<LaboratoryFactorCycleCorrespondence>,
    affine_cells: Vec<LaboratoryCellAffineSection>,
    identity_sha256: String,
}

/// The same affine organ around a native body carrying two or more genuinely returned
/// differences. The return population lives in the moved body; these fields retain only the
/// exact affine-organ lineage required to invert the newest return.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecurrentReturnedAffineLaboratoryRest {
    schema: String,
    rest_identity_history: Vec<String>,
    origin_predecessor_rest_identity_sha256: String,
    origin_predecessor_body_identity_sha256: String,
    body: RecurrentLaboratoryCultivatedRest,
    potential: NativeRelationalPotentialComplex,
    codec: NativeRelationalCodec,
    correspondences: Vec<LaboratoryFactorCycleCorrespondence>,
    affine_cells: Vec<LaboratoryCellAffineSection>,
    identity_sha256: String,
}

#[derive(Debug, PartialEq, Eq)]
pub enum RecurrentReturnedAffinePredecessor {
    First(ReturnedAffineLaboratoryRest),
    Recurrent(RecurrentReturnedAffineLaboratoryRest),
}

impl RecurrentReturnedAffinePredecessor {
    pub fn identity(&self) -> &str {
        match self {
            Self::First(rest) => rest.identity(),
            Self::Recurrent(rest) => rest.identity(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct RecurrentReturnedAffineDifferenceWithdrawal {
    original_rest_identity_sha256: String,
    predecessor_rest_identity_sha256: String,
    situated: RecurrentSituatedDifferenceWithdrawal,
}

/// Move-owned inverse of the returned situated passage while the affine organ remains on the
/// continuing body.  Restoration consumes this token and the exact predecessor.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnedAffineLaboratoryDifferenceWithdrawal {
    original_rest_identity_sha256: String,
    predecessor_rest_identity_sha256: String,
    predecessor_body_identity_sha256: String,
    situated: SituatedReturnedDifferenceWithdrawal,
}

impl ReturnedAffineLaboratoryDifferenceWithdrawal {
    /// Persist the move-owned inverse across an apparatus cut.  No predecessor or successor body
    /// is copied into this fibre; restoration still checks every held identity and native deposit.
    pub fn canonical_bytes(&self) -> Result<Vec<u8>, LaboratoryCultivationError> {
        serde_json::to_vec(self)
            .map_err(|error| LaboratoryCultivationError::Wire(error.to_string()))
    }

    pub fn read(bytes: &[u8]) -> Result<Self, LaboratoryCultivationError> {
        serde_json::from_slice(bytes)
            .map_err(|error| LaboratoryCultivationError::Wire(error.to_string()))
    }
}

/// Cold testimony that a particular returned-rest wire already passed complete validation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AdmittedReturnedAffineLaboratoryRestWitness {
    pub schema: String,
    pub truth_status: String,
    pub rest_wire_sha256: String,
    pub rest_identity_sha256: String,
    pub complete_validation_receipt_sha256: String,
    pub complete_validation_was_replayed_for_this_wire: bool,
}

impl AdmittedReturnedAffineLaboratoryRestWitness {
    pub fn found(
        rest_wire_sha256: impl Into<String>,
        rest_identity_sha256: impl Into<String>,
        complete_validation_receipt_sha256: impl Into<String>,
    ) -> Result<Self, LaboratoryCultivationError> {
        let witness = Self {
            schema: ADMITTED_RETURNED_REST_WITNESS_SCHEMA.to_owned(),
            truth_status: "implemented-exact".to_owned(),
            rest_wire_sha256: rest_wire_sha256.into(),
            rest_identity_sha256: rest_identity_sha256.into(),
            complete_validation_receipt_sha256: complete_validation_receipt_sha256.into(),
            complete_validation_was_replayed_for_this_wire: true,
        };
        witness.validate()?;
        Ok(witness)
    }

    pub fn validate(&self) -> Result<(), LaboratoryCultivationError> {
        if self.schema != ADMITTED_RETURNED_REST_WITNESS_SCHEMA
            || self.truth_status != "implemented-exact"
            || !is_digest(&self.rest_wire_sha256)
            || !is_digest(&self.rest_identity_sha256)
            || !is_digest(&self.complete_validation_receipt_sha256)
            || !self.complete_validation_was_replayed_for_this_wire
        {
            return Err(LaboratoryCultivationError::Wire(
                "the admitted returned affine-rest witness is malformed".to_owned(),
            ));
        }
        Ok(())
    }
}

/// Cold proof-carrying remount testimony for a rest which already passed complete construction
/// validation.  It permits an immutable admitted wire to be remounted without replaying every
/// local proof on every inference occurrence.  The witness is not a validator for a new body: its
/// exact wire digest, native identity, and retained construction receipt must all agree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AdmittedAffineLaboratoryRestWitness {
    pub schema: String,
    pub truth_status: String,
    pub rest_wire_sha256: String,
    pub rest_identity_sha256: String,
    pub complete_validation_receipt_sha256: String,
    pub complete_validation_was_replayed_for_this_wire: bool,
}

impl AdmittedAffineLaboratoryRestWitness {
    pub fn found(
        rest_wire_sha256: impl Into<String>,
        rest_identity_sha256: impl Into<String>,
        complete_validation_receipt_sha256: impl Into<String>,
    ) -> Result<Self, LaboratoryCultivationError> {
        let witness = Self {
            schema: ADMITTED_REST_WITNESS_SCHEMA.to_owned(),
            truth_status: "implemented-exact".to_owned(),
            rest_wire_sha256: rest_wire_sha256.into(),
            rest_identity_sha256: rest_identity_sha256.into(),
            complete_validation_receipt_sha256: complete_validation_receipt_sha256.into(),
            complete_validation_was_replayed_for_this_wire: true,
        };
        witness.validate()?;
        Ok(witness)
    }

    pub fn validate(&self) -> Result<(), LaboratoryCultivationError> {
        if self.schema != ADMITTED_REST_WITNESS_SCHEMA
            || self.truth_status != "implemented-exact"
            || !is_digest(&self.rest_wire_sha256)
            || !is_digest(&self.rest_identity_sha256)
            || !is_digest(&self.complete_validation_receipt_sha256)
            || !self.complete_validation_was_replayed_for_this_wire
        {
            return Err(LaboratoryCultivationError::Wire(
                "the admitted affine-rest witness is malformed".to_owned(),
            ));
        }
        Ok(())
    }
}

/// The one mounted affine Athena body and its resident participant causal atlas.
pub struct ResidentAffineLaboratoryEcology {
    schema: String,
    predecessor_rest_identity_sha256: String,
    body: SituatedCultivatedEcologyRest,
    factors: Vec<(String, Vec<String>)>,
    expected: Vec<holonic_engine::ExactComplexWaveCurrent>,
    potential: NativeRelationalPotentialComplex,
    codec: NativeRelationalCodec,
    correspondences: Vec<LaboratoryFactorCycleCorrespondence>,
    affine_cells: Vec<LaboratoryCellAffineSection>,
    identity_sha256: String,
    participant_faces: BTreeSet<u32>,
    resident: ResidentIntegratedFront,
}

/// The same card-owned affine/material front mounted over the recurrent returned body.
///
/// Returned differences enlarge the resident coupled-current population, but they do not found a
/// second affine organ or another inference apparatus.  This owner retains the one recurrent rest
/// while its original four-dimensional material section crosses the standing affine cells.
pub struct ResidentRecurrentAffineLaboratoryEcology {
    rest: RecurrentReturnedAffineLaboratoryRest,
    factors: Vec<(String, Vec<String>)>,
    expected: Vec<holonic_engine::ExactComplexWaveCurrent>,
    resident: ResidentIntegratedFront,
}

/// Recoverable move-owned relational organ.  Restoration consumes it and the exact L2 body.
#[derive(Debug, PartialEq, Eq)]
pub struct AffineLaboratoryCultivationWithdrawal {
    original_rest_identity_sha256: String,
    predecessor_rest_identity_sha256: String,
    potential: NativeRelationalPotentialComplex,
    codec: NativeRelationalCodec,
    correspondences: Vec<LaboratoryFactorCycleCorrespondence>,
    affine_cells: Vec<LaboratoryCellAffineSection>,
}

/// Recoverable removal of one addressed relational 2-cell from the cultivated affine base.
///
/// The moved cell remains the complete reconstruction fibre.  Its faces, codec chart, L2 body,
/// rank-four cycle fibres, and every nonincident relational cell remain in the continuing rest.
/// This is therefore a local structural ablation rather than a mask or caller-authored score.
#[derive(Debug, PartialEq, Eq)]
pub struct AffineLaboratoryCellWithdrawal {
    original_rest_identity_sha256: String,
    ablated_rest_identity_sha256: String,
    original_position: usize,
    cell: super::native_relational_potential::NativeRelationalCell,
}

/// Native control population for local cultivation ablation.  The partition is induced only by
/// incidence with the addressed participant port; no proper name, question, or surface token is
/// consulted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AffineLaboratoryAblationAtlas {
    pub participant_incident_cells: Vec<String>,
    pub participant_disjoint_cells: Vec<String>,
}

#[derive(Debug, Error)]
pub enum LaboratoryCultivationError {
    #[error("the L2 situated body refused laboratory cultivation: {0}")]
    Situated(String),
    #[error("the L1 exchange product does not correspond to the L2 body: {0}")]
    Product(String),
    #[error("the exchange world-tube projection is malformed: {0}")]
    Exchange(String),
    #[error("the affine factor/fibre correspondence is incomplete: {0}")]
    Correspondence(String),
    #[error("the relational cultivation organ refused the passage: {0}")]
    Relational(String),
    #[error("the affine laboratory rest wire is malformed: {0}")]
    Wire(String),
}
