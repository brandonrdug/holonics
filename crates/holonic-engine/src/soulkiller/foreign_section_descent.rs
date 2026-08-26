//! Exact descent of foreign local maps on a cultivated reachable section.
//!
//! Let the columns of `A_a : Q^H -> V_a` be the addressed states returned by `H` cultivated
//! histories at one foreign boundary, and let `A_(a+1)` present their returned states at the next
//! boundary. A map on the reachable section `S_a = image(A_a)` is well-defined precisely when
//!
//! ```text
//!     kernel(A_a) is a subset of kernel(A_(a+1)).
//! ```
//!
//! Under that obligation, `Wbar_a(A_a c) = A_(a+1) c` is independent of the coefficient
//! representative. The complete reconstruction fibre of an entering state is the affine fibre
//! returned by `A_a`; no pseudoinverse or preferred coefficient is hidden. Current outside
//! `image(A_a)` returns an obstruction and never opens the foreign tower.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    cuda_refine::{
        CudaRefineExecutor, ResidentComplexIncidence, ResidentComplexIncidenceReturn,
        ResidentNativeWord, ResidentNativeWordReturn,
    },
    dimensional_wave::ExactComplexWaveCurrent,
    exact_linear::{ExactLinearError, ExactRatMatrix},
};

const SCHEMA: &str = "holonic-engine.soulkiller.foreign-reachable-section-rest.v1";

/// One compact exact point section in a common resident grain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CarrierSectionRest {
    pub address: String,
    pub rows: usize,
    pub columns: usize,
    pub grain: u32,
    /// Row-major exact carrier integers. Physical values are `entry * 2^(-grain)`.
    pub entries: Vec<i64>,
}

impl CarrierSectionRest {
    pub fn from_columns(
        address: impl Into<String>,
        grain: u32,
        columns: &[Vec<(i64, i64)>],
    ) -> Result<Self, ForeignSectionDescentRefusal> {
        let rows = columns.first().map(Vec::len).unwrap_or(0);
        if columns.is_empty()
            || rows == 0
            || columns.iter().any(|column| {
                column.len() != rows || column.iter().any(|(lower, upper)| lower != upper)
            })
        {
            return Err(ForeignSectionDescentRefusal::CarrierSection);
        }
        let mut entries = Vec::with_capacity(rows * columns.len());
        for row in 0..rows {
            for column in columns {
                entries.push(column[row].0);
            }
        }
        Ok(Self {
            address: address.into(),
            rows,
            columns: columns.len(),
            grain,
            entries,
        })
    }

    fn matrix(&self) -> Result<ExactRatMatrix, ForeignSectionDescentRefusal> {
        if self.address.is_empty()
            || self.rows == 0
            || self.columns == 0
            || self.entries.len() != self.rows * self.columns
        {
            return Err(ForeignSectionDescentRefusal::CarrierSection);
        }
        ExactRatMatrix::new(
            self.entries
                .chunks_exact(self.columns)
                .map(|row| {
                    row.iter()
                        .map(|entry| Rat::from_integer(BigInt::from(*entry)))
                        .collect()
                })
                .collect(),
        )
        .map_err(Into::into)
    }

    pub fn column(&self, column: usize) -> Result<Vec<Rat>, ForeignSectionDescentRefusal> {
        if column >= self.columns {
            return Err(ForeignSectionDescentRefusal::HistoryAddress);
        }
        Ok((0..self.rows)
            .map(|row| Rat::from_integer(BigInt::from(self.entries[row * self.columns + column])))
            .collect())
    }
}

/// Canonical source-detached standing: compact point sections, addressed history lineage, and no
/// foreign tensor population.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ForeignReachableSectionRest {
    pub schema: String,
    pub history_addresses: Vec<String>,
    pub native_history_states: Vec<u64>,
    pub sections: Vec<CarrierSectionRest>,
    pub identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HistorySeparator {
    pub left_history: usize,
    pub right_history: usize,
    pub target_coordinate: usize,
    pub left: i64,
    pub right: i64,
}

/// One receiver-equivalence class of addressed coefficient occurrences. Equal carrier columns
/// do not identify their source occurrences; every member remains in this reconstruction fibre.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForeignCoefficientReceiverClass {
    pub class: usize,
    pub representative_history: usize,
    pub histories: Vec<usize>,
    pub history_addresses: Vec<String>,
}

/// The first section/coordinate which separates two coefficient occurrences for the complete
/// captured receiver word.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForeignCoefficientWordSeparator {
    pub left_history: usize,
    pub right_history: usize,
    pub section: usize,
    pub section_address: String,
    pub coordinate: usize,
    pub left: i64,
    pub right: i64,
}

/// Exact quotient of addressed history occurrences by the complete captured foreign carrier
/// word. This is a receiver quotient only: lineage remains in `classes[*].histories`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForeignCoefficientReceiverQuotient {
    pub history_to_class: Vec<usize>,
    pub classes: Vec<ForeignCoefficientReceiverClass>,
    pub shortest_separators: Vec<ForeignCoefficientWordSeparator>,
}

/// Exact adjacent-section descent certified entirely in coefficient space. For the explicitly
/// declared identity carrier receiver, the pulled storage is `G = B^T B`; positivity over `Q`
/// gives `kernel(B) = kernel(G)` and `rank(B) = rank(G)`. The certificate therefore never performs
/// rational elimination across the usually much larger carrier-row population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoefficientNaturalityCertificate {
    pub from_address: String,
    pub to_address: String,
    pub coefficient_population: usize,
    pub carrier_population: usize,
    pub entering_rank: usize,
    pub returned_rank: usize,
    pub complete_coefficient_kernel: Vec<Vec<String>>,
    pub returned_coefficient_kernel: Vec<Vec<String>>,
    pub shortest_history_separators: Vec<HistorySeparator>,
    pub naturality_commutes: bool,
    pub carrier_elimination_performed: bool,
}

/// One exact descended foreign map. Deliberately derived from the rest rather than serialized:
/// elimination is construction work, while the compact sections are the continuing standing.
#[derive(Debug, PartialEq, Eq)]
pub struct DescendedForeignSection {
    pub from_address: String,
    pub to_address: String,
    pub entering: ExactRatMatrix,
    pub returned: ExactRatMatrix,
    pub entering_rank: usize,
    pub complete_coefficient_kernel: Vec<Vec<Rat>>,
    pub returned_coefficient_kernel: Vec<Vec<Rat>>,
    pub shortest_history_separators: Vec<HistorySeparator>,
    pub naturality_commutes: bool,
}

/// The Complex Parametron face of one captured foreign section. The captured matrix is the
/// oriented incidence `B` from addressed coefficient nodes into carrier branches. The
/// constitutive form is an explicitly declared receiver metric, never an inferred physical
/// capacitance or inverse inductance. Its pullback `B^T M B` and complete radical are the exact
/// storage/receiver testimony retained beside the section.
#[derive(Debug, PartialEq, Eq)]
pub struct ForeignParametronSection {
    pub address: String,
    pub grain: u32,
    pub incidence: ExactRatMatrix,
    pub receiver_constitutive_form: ForeignReceiverConstitutiveForm,
    pub pulled_storage: ExactRatMatrix,
    pub complete_incidence_kernel: Vec<Vec<Rat>>,
    pub complete_radical: Vec<Vec<Rat>>,
    pub incidence_rank: usize,
}

/// A receiver constitutive face with its storage geometry preserved. Diagonal branch storage stays
/// linear in the branch population; a dense mutual table exists only when the receiver actually
/// declares off-diagonal coupling.
#[derive(Debug, PartialEq, Eq)]
pub enum ForeignReceiverConstitutiveForm {
    Diagonal(Vec<Rat>),
    Mutual(ExactRatMatrix),
}

/// One inspected current through the pre-quotient Parametron section.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ForeignParametronReceipt {
    pub address: String,
    pub branch_population: usize,
    pub coefficient_node_population: usize,
    pub incidence_rank: usize,
    pub incidence_kernel_dimension: usize,
    pub radical_dimension: usize,
    pub realized_current: Vec<ExactComplexWaveCurrent>,
    pub pulled_storage: String,
    pub realized_storage: String,
    pub storage_pullback_exact: bool,
    pub selected_reoriented_branches: Vec<usize>,
    pub orientation_covariant: bool,
    pub half_turn_negates_complete_current: bool,
    pub binary_receiver_taken: bool,
}

/// The complete captured section family in its pre-quotient Parametron reading. This is a view of
/// the same continuing standing, not another semantic subsystem.
#[derive(Debug, PartialEq, Eq)]
pub struct ForeignParametronAtlas {
    pub sections: Vec<ForeignParametronSection>,
}

/// The final captured incidence mounted once on the resident card. Earlier sections remain exact
/// naturality/reconstruction testimony; later conduct crosses only coefficient current and reads
/// the resulting physical section.
pub struct ResidentForeignParametronSection {
    exact: ForeignParametronSection,
    resident: ResidentComplexIncidence,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResidentForeignParametronReturn {
    pub exact_sections: Vec<Vec<ExactComplexWaveCurrent>>,
    pub storage_pullback_exact: Vec<bool>,
    pub apparatus: ResidentComplexIncidenceReturn,
}

impl ForeignReceiverConstitutiveForm {
    fn extent(&self) -> Result<usize, ForeignSectionDescentRefusal> {
        match self {
            Self::Diagonal(weights) if !weights.is_empty() => Ok(weights.len()),
            Self::Mutual(matrix)
                if matrix.rows() > 0
                    && matrix.rows() == matrix.columns()
                    && matrix.transpose()? == *matrix =>
            {
                Ok(matrix.rows())
            }
            _ => Err(ForeignSectionDescentRefusal::ReceiverConstitutiveForm),
        }
    }

    fn apply(&self, current: &[Rat]) -> Result<Vec<Rat>, ForeignSectionDescentRefusal> {
        if self.extent()? != current.len() {
            return Err(ForeignSectionDescentRefusal::ComplexCurrentShape);
        }
        match self {
            Self::Diagonal(weights) => Ok(weights
                .iter()
                .zip(current)
                .map(|(weight, value)| weight * value)
                .collect()),
            Self::Mutual(matrix) => matrix.apply(current).map_err(Into::into),
        }
    }

    fn pullback(
        &self,
        incidence: &ExactRatMatrix,
    ) -> Result<ExactRatMatrix, ForeignSectionDescentRefusal> {
        if self.extent()? != incidence.rows() {
            return Err(ForeignSectionDescentRefusal::ReceiverConstitutiveForm);
        }
        let responded = match self {
            Self::Diagonal(weights) => ExactRatMatrix::new(
                incidence
                    .to_rows()
                    .into_iter()
                    .zip(weights)
                    .map(|(row, weight)| row.into_iter().map(|entry| weight * entry).collect())
                    .collect(),
            )?,
            Self::Mutual(matrix) => matrix.multiply(incidence)?,
        };
        incidence
            .transpose()?
            .multiply(&responded)
            .map_err(Into::into)
    }

    fn reorient(&self, signs: &[Rat]) -> Result<Self, ForeignSectionDescentRefusal> {
        if self.extent()? != signs.len() {
            return Err(ForeignSectionDescentRefusal::ReceiverConstitutiveForm);
        }
        match self {
            Self::Diagonal(weights) => Ok(Self::Diagonal(weights.clone())),
            Self::Mutual(matrix) => Ok(Self::Mutual(ExactRatMatrix::new(
                matrix
                    .to_rows()
                    .into_iter()
                    .enumerate()
                    .map(|(first, row)| {
                        row.into_iter()
                            .enumerate()
                            .map(|(second, entry)| &signs[first] * entry * &signs[second])
                            .collect()
                    })
                    .collect(),
            )?)),
        }
    }
}

/// One mounted word. It is not cloneable continuing ecology.
pub struct MountedForeignSectionWord {
    rest: ForeignReachableSectionRest,
    pub maps: Vec<DescendedForeignSection>,
}

/// One complete future-equivalence class of cultivated history occurrences. Two histories share
/// this class only when every captured section receiver reads the same exact carrier column.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ForeignHistoryClass {
    pub native_class: u32,
    pub history_indices: Vec<usize>,
    pub history_addresses: Vec<String>,
    pub native_history_states: Vec<u64>,
}

/// The locked finite receiver of the exact descended word. It is a lawful control only after the
/// complete future receiver identifies a history class; it is not the pre-quotient productive
/// carrier because it discards complex coefficient amplitude and phase. Continuing ownership is
/// singular: this type is deliberately not `Clone`.
pub struct ResidentForeignSectionWord {
    exact: MountedForeignSectionWord,
    history_class: Vec<u32>,
    classes: Vec<ForeignHistoryClass>,
    action: ResidentNativeWord,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResidentForeignHistoryReturn {
    pub history_index: usize,
    pub history_address: String,
    pub native_history_state: u64,
    pub native_class: u32,
    pub entering_native_state: u32,
    pub returned_native_state: u32,
    pub complete_history_fibre: Vec<usize>,
    pub final_section: Vec<i64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResidentForeignSectionReturn {
    pub histories: Vec<ResidentForeignHistoryReturn>,
    pub apparatus: ResidentForeignSectionApparatus,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResidentForeignSectionApparatus {
    pub device: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub mount_host_ingress_octets: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeHistoryOutOfSection {
    pub native_history_state: u64,
    pub admitted_native_history_states: Vec<u64>,
    pub foreign_fallback_permitted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ResidentForeignSectionRefusal {
    #[error(transparent)]
    Exact(#[from] ForeignSectionDescentRefusal),
    #[error("resident foreign-section apparatus refused: {0}")]
    Apparatus(String),
    #[error("the card returned a state outside the compiled receiver-history word")]
    DeviceReturn,
    #[error("native history {0:?} leaves the cultivated reachable section")]
    OutOfSection(NativeHistoryOutOfSection),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ForeignSectionReturn {
    pub from_address: String,
    pub to_address: String,
    pub entering: Vec<String>,
    pub returned: Vec<String>,
    pub particular_coefficients: Vec<String>,
    pub complete_coefficient_fibre: Vec<Vec<String>>,
    pub exact_reconstruction: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OutOfReachableSection {
    pub from_address: String,
    pub entering: Vec<String>,
    pub reachable_rank: usize,
    pub ambient_dimension: usize,
    pub foreign_fallback_permitted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ForeignSectionDescentRefusal {
    #[error("the compact carrier section is empty, non-point, ragged, or malformed")]
    CarrierSection,
    #[error("history addresses are empty, repeated, or disagree with the section columns")]
    HistoryAddress,
    #[error("adjacent reachable sections disagree in ambient carrier or grain")]
    AdjacentSection,
    #[error("the declared receiver constitutive form does not match its carrier section")]
    ReceiverConstitutiveForm,
    #[error("the exact complex coefficient current does not match the section's addressed nodes")]
    ComplexCurrentShape,
    #[error(
        "the foreign map does not descend because an entering-kernel direction returns visibly"
    )]
    Naturality,
    #[error("the reachable-section rest identity does not reconstruct")]
    Identity,
    #[error("reachable-section wire refused: {0}")]
    Wire(String),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
}

impl ForeignReachableSectionRest {
    pub fn seal(
        history_addresses: Vec<String>,
        native_history_states: Vec<u64>,
        sections: Vec<CarrierSectionRest>,
    ) -> Result<Self, ForeignSectionDescentRefusal> {
        let mut rest = Self {
            schema: SCHEMA.to_owned(),
            history_addresses,
            native_history_states,
            sections,
            identity_sha256: String::new(),
        };
        rest.validate_shape()?;
        rest.identity_sha256 = rest.derived_identity()?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, ForeignSectionDescentRefusal> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| ForeignSectionDescentRefusal::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, ForeignSectionDescentRefusal> {
        self.validate()?;
        serde_json::to_vec(self)
            .map_err(|error| ForeignSectionDescentRefusal::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), ForeignSectionDescentRefusal> {
        self.validate_shape()?;
        if self.schema != SCHEMA || self.identity_sha256 != self.derived_identity()? {
            return Err(ForeignSectionDescentRefusal::Identity);
        }
        Ok(())
    }

    fn validate_shape(&self) -> Result<(), ForeignSectionDescentRefusal> {
        let unique_histories = self
            .history_addresses
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let unique_native = self
            .native_history_states
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        if self.history_addresses.is_empty()
            || unique_histories.len() != self.history_addresses.len()
            || self.native_history_states.len() != self.history_addresses.len()
            || unique_native.len() != self.native_history_states.len()
            || self.sections.len() < 2
        {
            return Err(ForeignSectionDescentRefusal::HistoryAddress);
        }
        let first = &self.sections[0];
        if first.columns != self.history_addresses.len()
            || first.rows == 0
            || first.entries.len() != first.rows * first.columns
        {
            return Err(ForeignSectionDescentRefusal::CarrierSection);
        }
        let mut addresses = BTreeSet::new();
        if self.sections.iter().any(|section| {
            section.address.is_empty()
                || !addresses.insert(section.address.as_str())
                || section.rows != first.rows
                || section.columns != first.columns
                || section.grain != first.grain
                || section.entries.len() != section.rows * section.columns
        }) {
            return Err(ForeignSectionDescentRefusal::AdjacentSection);
        }
        Ok(())
    }

    fn derived_identity(&self) -> Result<String, ForeignSectionDescentRefusal> {
        let bytes = serde_json::to_vec(&(
            SCHEMA,
            &self.history_addresses,
            &self.native_history_states,
            &self.sections,
        ))
        .map_err(|error| ForeignSectionDescentRefusal::Wire(error.to_string()))?;
        Ok(format!("{:x}", Sha256::digest(bytes)))
    }

    pub fn mount(self) -> Result<MountedForeignSectionWord, ForeignSectionDescentRefusal> {
        self.validate()?;
        let mut maps = Vec::with_capacity(self.sections.len() - 1);
        for pair in self.sections.windows(2) {
            maps.push(descend(&pair[0], &pair[1])?);
        }
        Ok(MountedForeignSectionWord { rest: self, maps })
    }

    /// Quotient addressed coefficient occurrences only when every captured carrier section has
    /// the same column. The comparison covers the complete section word, not a terminal answer or
    /// a hash label; every unequal pair returns its first separating section and coordinate.
    pub fn coefficient_receiver_quotient(
        &self,
    ) -> Result<ForeignCoefficientReceiverQuotient, ForeignSectionDescentRefusal> {
        self.validate()?;
        let histories = self.history_addresses.len();
        let same_word = |left: usize, right: usize| {
            self.sections.iter().all(|section| {
                (0..section.rows).all(|row| {
                    section.entries[row * histories + left]
                        == section.entries[row * histories + right]
                })
            })
        };

        let mut representatives = Vec::<usize>::new();
        let mut history_to_class = Vec::with_capacity(histories);
        let mut members = Vec::<Vec<usize>>::new();
        for history in 0..histories {
            let class = representatives
                .iter()
                .position(|representative| same_word(*representative, history))
                .unwrap_or_else(|| {
                    representatives.push(history);
                    members.push(Vec::new());
                    representatives.len() - 1
                });
            history_to_class.push(class);
            members[class].push(history);
        }
        let classes = representatives
            .iter()
            .enumerate()
            .map(|(class, representative)| ForeignCoefficientReceiverClass {
                class,
                representative_history: *representative,
                histories: members[class].clone(),
                history_addresses: members[class]
                    .iter()
                    .map(|history| self.history_addresses[*history].clone())
                    .collect(),
            })
            .collect();

        let mut shortest_separators = Vec::new();
        for left in 0..histories {
            for right in left + 1..histories {
                if history_to_class[left] == history_to_class[right] {
                    continue;
                }
                let separator = self
                    .sections
                    .iter()
                    .enumerate()
                    .find_map(|(section_index, section)| {
                        (0..section.rows).find_map(|coordinate| {
                            let left_value = section.entries[coordinate * histories + left];
                            let right_value = section.entries[coordinate * histories + right];
                            (left_value != right_value).then(|| ForeignCoefficientWordSeparator {
                                left_history: left,
                                right_history: right,
                                section: section_index,
                                section_address: section.address.clone(),
                                coordinate,
                                left: left_value,
                                right: right_value,
                            })
                        })
                    })
                    .ok_or(ForeignSectionDescentRefusal::CarrierSection)?;
                shortest_separators.push(separator);
            }
        }
        Ok(ForeignCoefficientReceiverQuotient {
            history_to_class,
            classes,
            shortest_separators,
        })
    }

    /// Certify the complete captured word through the Complex Parametron storage pullback. This is
    /// exact for the declared identity receiver: a coefficient direction is carrier-invisible iff
    /// its quadratic storage vanishes. Naturality is the inclusion of the entering radical in the
    /// returned radical. No ambient carrier map or preferred inverse is constructed.
    pub fn coefficient_naturality_certificates(
        &self,
    ) -> Result<Vec<CoefficientNaturalityCertificate>, ForeignSectionDescentRefusal> {
        self.validate()?;
        self.sections
            .windows(2)
            .map(|pair| coefficient_naturality(&pair[0], &pair[1]))
            .collect()
    }

    /// Compile the complete captured future relation into its locked finite receiver and retain
    /// that receiver on the card. The physical carrier sections remain reconstruction testimony;
    /// this face does not replace the Complex Parametron current carried by `parametron_atlas`.
    pub fn mount_resident(
        self,
    ) -> Result<ResidentForeignSectionWord, ResidentForeignSectionRefusal> {
        ResidentForeignSectionWord::mount(self.mount()?)
    }

    /// Present every captured section as one oriented Complex Parametron incidence against the
    /// receiver constitutive forms supplied by the caller. A form is a receiver declaration, so
    /// there is deliberately no implicit Euclidean default in this owner.
    pub fn parametron_atlas(
        &self,
        receiver_constitutive_forms: Vec<ForeignReceiverConstitutiveForm>,
    ) -> Result<ForeignParametronAtlas, ForeignSectionDescentRefusal> {
        self.validate()?;
        if receiver_constitutive_forms.len() != self.sections.len() {
            return Err(ForeignSectionDescentRefusal::ReceiverConstitutiveForm);
        }
        let sections = self
            .sections
            .iter()
            .zip(receiver_constitutive_forms)
            .map(|(section, form)| ForeignParametronSection::new(section, form))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ForeignParametronAtlas { sections })
    }
}

impl ForeignParametronSection {
    fn new(
        section: &CarrierSectionRest,
        receiver_constitutive_form: ForeignReceiverConstitutiveForm,
    ) -> Result<Self, ForeignSectionDescentRefusal> {
        if receiver_constitutive_form.extent()? != section.rows {
            return Err(ForeignSectionDescentRefusal::ReceiverConstitutiveForm);
        }
        let incidence = section.matrix()?;
        let pulled_storage = receiver_constitutive_form.pullback(&incidence)?;
        let complete_incidence_kernel = incidence.kernel_basis()?;
        let complete_radical = pulled_storage.kernel_basis()?;
        let incidence_rank = incidence.rank()?;
        Ok(Self {
            address: section.address.clone(),
            grain: section.grain,
            incidence,
            receiver_constitutive_form,
            pulled_storage,
            complete_incidence_kernel,
            complete_radical,
            incidence_rank,
        })
    }

    pub fn realize(
        &self,
        coefficients: &[ExactComplexWaveCurrent],
    ) -> Result<Vec<ExactComplexWaveCurrent>, ForeignSectionDescentRefusal> {
        apply_complex(&self.incidence, coefficients)
    }

    pub fn inspect_current(
        &self,
        coefficients: &[ExactComplexWaveCurrent],
        selected_reoriented_branches: &BTreeSet<usize>,
    ) -> Result<ForeignParametronReceipt, ForeignSectionDescentRefusal> {
        if coefficients.len() != self.incidence.columns()
            || selected_reoriented_branches
                .iter()
                .any(|branch| *branch >= self.incidence.rows())
        {
            return Err(ForeignSectionDescentRefusal::ComplexCurrentShape);
        }
        let realized_current = self.realize(coefficients)?;
        let pulled_storage = complex_quadratic(&self.pulled_storage, coefficients)?;
        let realized_storage =
            receiver_complex_quadratic(&self.receiver_constitutive_form, &realized_current)?;

        let signs = (0..self.incidence.rows())
            .map(|branch| {
                if selected_reoriented_branches.contains(&branch) {
                    -Rat::one()
                } else {
                    Rat::one()
                }
            })
            .collect::<Vec<_>>();
        let reoriented_incidence = ExactRatMatrix::new(
            self.incidence
                .to_rows()
                .into_iter()
                .enumerate()
                .map(|(branch, row)| {
                    row.into_iter()
                        .map(|entry| &signs[branch] * entry)
                        .collect()
                })
                .collect(),
        )?;
        let reoriented_form = self.receiver_constitutive_form.reorient(&signs)?;
        let reoriented_pulled = reoriented_form.pullback(&reoriented_incidence)?;
        let reoriented_current = apply_complex(&reoriented_incidence, coefficients)?;
        let expected_reoriented = realized_current
            .iter()
            .zip(&signs)
            .map(|(current, sign)| current.scaled(sign))
            .collect::<Vec<_>>();
        let reoriented_storage = receiver_complex_quadratic(&reoriented_form, &reoriented_current)?;

        let half_turned = coefficients
            .iter()
            .map(ExactComplexWaveCurrent::negated)
            .collect::<Vec<_>>();
        let half_turn_realized = self.realize(&half_turned)?;
        let expected_half_turn = realized_current
            .iter()
            .map(ExactComplexWaveCurrent::negated)
            .collect::<Vec<_>>();
        Ok(ForeignParametronReceipt {
            address: self.address.clone(),
            branch_population: self.incidence.rows(),
            coefficient_node_population: self.incidence.columns(),
            incidence_rank: self.incidence_rank,
            incidence_kernel_dimension: self.complete_incidence_kernel.len(),
            radical_dimension: self.complete_radical.len(),
            realized_current,
            pulled_storage: pulled_storage.to_string(),
            realized_storage: realized_storage.to_string(),
            storage_pullback_exact: pulled_storage == realized_storage,
            selected_reoriented_branches: selected_reoriented_branches.iter().copied().collect(),
            orientation_covariant: reoriented_pulled == self.pulled_storage
                && reoriented_current == expected_reoriented
                && reoriented_storage == realized_storage,
            half_turn_negates_complete_current: half_turn_realized == expected_half_turn,
            binary_receiver_taken: false,
        })
    }

    pub fn mount_resident(
        self,
    ) -> Result<ResidentForeignParametronSection, ResidentForeignSectionRefusal> {
        let entries = self
            .incidence
            .entries()
            .iter()
            .map(|entry| {
                if entry.denom().is_one() {
                    entry.numer().to_i64()
                } else {
                    None
                }
            })
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                ResidentForeignSectionRefusal::Apparatus(
                    "the captured incidence cannot enter the exact signed-word apparatus chart"
                        .to_owned(),
                )
            })?;
        let card = CudaRefineExecutor::new()
            .map_err(|error| ResidentForeignSectionRefusal::Apparatus(error.to_string()))?;
        let resident = ResidentComplexIncidence::mount(
            card,
            self.address.clone(),
            self.grain,
            self.incidence.rows(),
            self.incidence.columns(),
            &entries,
        )
        .map_err(|error| ResidentForeignSectionRefusal::Apparatus(error.to_string()))?;
        Ok(ResidentForeignParametronSection {
            exact: self,
            resident,
        })
    }
}

impl ResidentForeignParametronSection {
    pub fn exact(&self) -> &ForeignParametronSection {
        &self.exact
    }

    pub fn conduct(
        &mut self,
        fronts: &[Vec<ExactComplexWaveCurrent>],
    ) -> Result<ResidentComplexIncidenceReturn, ResidentForeignSectionRefusal> {
        self.resident
            .conduct(fronts)
            .map_err(|error| ResidentForeignSectionRefusal::Apparatus(error.to_string()))
    }
}

impl MountedForeignSectionWord {
    pub fn rest(&self) -> &ForeignReachableSectionRest {
        &self.rest
    }

    pub fn conduct_history(
        &self,
        history: usize,
    ) -> Result<Vec<ForeignSectionReturn>, ForeignSectionDescentRefusal> {
        if history >= self.rest.history_addresses.len() {
            return Err(ForeignSectionDescentRefusal::HistoryAddress);
        }
        // A captured history is already one addressed coefficient node. Naturality carries that
        // same coefficient section through every adjacent square:
        //
        //     A_(a+1) e_h = Wbar_a (A_a e_h).
        //
        // Recovering `e_h` afresh from every 2,560-coordinate carrier section would solve the
        // same affine preimage problem once per layer. Besides being needless, that serial solve
        // erases the very node lineage which makes the descended word exact.
        let particular = (0..self.rest.history_addresses.len())
            .map(|coefficient| {
                if coefficient == history {
                    Rat::one()
                } else {
                    Rat::zero()
                }
            })
            .collect::<Vec<_>>();
        let mut returns = Vec::with_capacity(self.maps.len());
        for (boundary, map) in self.maps.iter().enumerate() {
            let entering = self.rest.sections[boundary].column(history)?;
            let returned = self.rest.sections[boundary + 1].column(history)?;
            if map.entering.apply(&particular)? != entering
                || map.returned.apply(&particular)? != returned
            {
                return Err(ForeignSectionDescentRefusal::Naturality);
            }
            returns.push(ForeignSectionReturn {
                from_address: map.from_address.clone(),
                to_address: map.to_address.clone(),
                entering: entering.iter().map(ToString::to_string).collect(),
                returned: returned.iter().map(ToString::to_string).collect(),
                particular_coefficients: particular.iter().map(ToString::to_string).collect(),
                complete_coefficient_fibre: map
                    .complete_coefficient_kernel
                    .iter()
                    .map(|direction| direction.iter().map(ToString::to_string).collect())
                    .collect(),
                exact_reconstruction: true,
            });
        }
        Ok(returns)
    }
}

impl ResidentForeignSectionWord {
    fn mount(exact: MountedForeignSectionWord) -> Result<Self, ResidentForeignSectionRefusal> {
        let histories = exact.rest.history_addresses.len();
        let sections = exact.rest.sections.len();
        let mut future_classes = BTreeMap::<Vec<i64>, Vec<usize>>::new();
        for history in 0..histories {
            let mut future = Vec::with_capacity(sections * exact.rest.sections[0].rows);
            for section in &exact.rest.sections {
                future.extend(
                    (0..section.rows).map(|row| section.entries[row * section.columns + history]),
                );
            }
            future_classes.entry(future).or_default().push(history);
        }
        let mut history_class = vec![0; histories];
        let mut classes = Vec::with_capacity(future_classes.len());
        for (native_class, members) in future_classes.into_values().enumerate() {
            let native_class = u32::try_from(native_class)
                .map_err(|_| ResidentForeignSectionRefusal::DeviceReturn)?;
            for history in &members {
                history_class[*history] = native_class;
            }
            classes.push(ForeignHistoryClass {
                native_class,
                history_indices: members.clone(),
                history_addresses: members
                    .iter()
                    .map(|history| exact.rest.history_addresses[*history].clone())
                    .collect(),
                native_history_states: members
                    .iter()
                    .map(|history| exact.rest.native_history_states[*history])
                    .collect(),
            });
        }
        let class_count = classes.len();
        let state_count = sections
            .checked_mul(class_count)
            .ok_or(ResidentForeignSectionRefusal::DeviceReturn)?;
        let mut generator_table = Vec::with_capacity(state_count);
        for boundary in 0..sections {
            let returned_boundary = (boundary + 1).min(sections - 1);
            for native_class in 0..class_count {
                let state = returned_boundary
                    .checked_mul(class_count)
                    .and_then(|offset| offset.checked_add(native_class))
                    .ok_or(ResidentForeignSectionRefusal::DeviceReturn)?;
                generator_table.push(
                    u32::try_from(state)
                        .map_err(|_| ResidentForeignSectionRefusal::DeviceReturn)?,
                );
            }
        }
        let word = vec![0; sections - 1];
        let card = CudaRefineExecutor::new()
            .map_err(|error| ResidentForeignSectionRefusal::Apparatus(error.to_string()))?;
        let action = ResidentNativeWord::mount(card, state_count, 1, &generator_table, &word)
            .map_err(|error| ResidentForeignSectionRefusal::Apparatus(error.to_string()))?;
        Ok(Self {
            exact,
            history_class,
            classes,
            action,
        })
    }

    pub fn rest(&self) -> &ForeignReachableSectionRest {
        self.exact.rest()
    }

    pub fn maps(&self) -> &[DescendedForeignSection] {
        &self.exact.maps
    }

    pub fn classes(&self) -> &[ForeignHistoryClass] {
        &self.classes
    }

    pub fn conduct_native_history_states(
        &mut self,
        native_history_states: &[u64],
    ) -> Result<ResidentForeignSectionReturn, ResidentForeignSectionRefusal> {
        let history_by_native = self
            .exact
            .rest
            .native_history_states
            .iter()
            .enumerate()
            .map(|(history, native)| (*native, history))
            .collect::<BTreeMap<_, _>>();
        let mut histories = Vec::with_capacity(native_history_states.len());
        for native in native_history_states {
            let Some(history) = history_by_native.get(native).copied() else {
                return Err(ResidentForeignSectionRefusal::OutOfSection(
                    NativeHistoryOutOfSection {
                        native_history_state: *native,
                        admitted_native_history_states: self
                            .exact
                            .rest
                            .native_history_states
                            .clone(),
                        foreign_fallback_permitted: false,
                    },
                ));
            };
            histories.push(history);
        }
        self.conduct_histories(&histories)
    }

    pub fn conduct_histories(
        &mut self,
        histories: &[usize],
    ) -> Result<ResidentForeignSectionReturn, ResidentForeignSectionRefusal> {
        if let Some(history) = histories
            .iter()
            .copied()
            .find(|history| *history >= self.history_class.len())
        {
            let state = u64::try_from(history).unwrap_or(u64::MAX);
            return Err(ResidentForeignSectionRefusal::OutOfSection(
                NativeHistoryOutOfSection {
                    native_history_state: state,
                    admitted_native_history_states: self.exact.rest.native_history_states.clone(),
                    foreign_fallback_permitted: false,
                },
            ));
        }
        let entering = histories
            .iter()
            .map(|history| self.history_class[*history])
            .collect::<Vec<_>>();
        let returned = self
            .action
            .conduct(&entering)
            .map_err(|error| ResidentForeignSectionRefusal::Apparatus(error.to_string()))?;
        self.freeze_return(histories, entering, returned)
    }

    fn freeze_return(
        &self,
        histories: &[usize],
        entering: Vec<u32>,
        returned: ResidentNativeWordReturn,
    ) -> Result<ResidentForeignSectionReturn, ResidentForeignSectionRefusal> {
        let class_count = self.classes.len();
        let final_boundary = self.exact.rest.sections.len() - 1;
        let final_section = self
            .exact
            .rest
            .sections
            .last()
            .ok_or(ResidentForeignSectionRefusal::DeviceReturn)?;
        let mut returns = Vec::with_capacity(histories.len());
        for ((history, entering_native_state), returned_native_state) in histories
            .iter()
            .copied()
            .zip(entering.iter().copied())
            .zip(returned.native_end.iter().copied())
        {
            let native_class = self.history_class[history];
            let expected = final_boundary
                .checked_mul(class_count)
                .and_then(|offset| offset.checked_add(native_class as usize))
                .and_then(|state| u32::try_from(state).ok())
                .ok_or(ResidentForeignSectionRefusal::DeviceReturn)?;
            if returned_native_state != expected {
                return Err(ResidentForeignSectionRefusal::DeviceReturn);
            }
            let class = self
                .classes
                .get(native_class as usize)
                .ok_or(ResidentForeignSectionRefusal::DeviceReturn)?;
            returns.push(ResidentForeignHistoryReturn {
                history_index: history,
                history_address: self.exact.rest.history_addresses[history].clone(),
                native_history_state: self.exact.rest.native_history_states[history],
                native_class,
                entering_native_state,
                returned_native_state,
                complete_history_fibre: class.history_indices.clone(),
                final_section: (0..final_section.rows)
                    .map(|row| final_section.entries[row * final_section.columns + history])
                    .collect(),
            });
        }
        Ok(ResidentForeignSectionReturn {
            histories: returns,
            apparatus: ResidentForeignSectionApparatus {
                device: self.action.device_name().to_owned(),
                launches: returned.launches,
                synchronizations: returned.synchronizations,
                block_threads: self.action.block_threads(),
                mount_host_ingress_octets: self.action.mount_host_ingress_octets(),
                successor_host_ingress_octets: returned.host_ingress_octets,
                successor_host_egress_octets: returned.host_egress_octets,
                resident_invariant_octets: returned.resident_invariant_octets,
                resident_working_octets: returned.resident_working_octets,
                invariant_transport_reuploaded: returned.invariant_transport_reuploaded,
                cpu_semantic_replay_after_device: false,
            },
        })
    }
}

impl DescendedForeignSection {
    /// Return an exact coordinate perturbation outside the reachable image without repeatedly
    /// solving an ambient affine preimage problem.
    ///
    /// `particular` names a coefficient current whose realization is admitted. Choose a complete
    /// independent row family of the incidence. Any coordinate outside that family cannot be an
    /// isolated unit current in the image: an image point vanishing on the independent family is
    /// zero everywhere. Adding that unit current therefore leaves the reachable section.
    pub fn coordinate_obstruction_from(
        &self,
        particular: &[Rat],
    ) -> Result<OutOfReachableSection, ForeignSectionDescentRefusal> {
        if particular.len() != self.entering.columns() {
            return Err(ForeignSectionDescentRefusal::HistoryAddress);
        }
        let base = self.entering.apply(particular)?;
        let rows = self.entering.to_rows();
        let mut independent = Vec::<usize>::with_capacity(self.entering_rank);
        let mut current_rank = 0usize;
        for row in 0..rows.len() {
            let mut candidate = independent.clone();
            candidate.push(row);
            let rank = ExactRatMatrix::new(candidate.iter().map(|at| rows[*at].clone()).collect())?
                .rank()?;
            if rank > current_rank {
                independent.push(row);
                current_rank = rank;
                if current_rank == self.entering_rank {
                    break;
                }
            }
        }
        if current_rank != self.entering_rank {
            return Err(ForeignSectionDescentRefusal::Naturality);
        }
        let selected = independent.into_iter().collect::<BTreeSet<_>>();
        let outside = (0..self.entering.rows())
            .find(|row| !selected.contains(row))
            .ok_or(ForeignSectionDescentRefusal::CarrierSection)?;
        let mut entering = base;
        entering[outside] += Rat::one();
        Ok(self.obstruction(&entering))
    }

    pub fn conduct(&self, entering: &[Rat]) -> Result<ForeignSectionReturn, OutOfReachableSection> {
        let Some((particular, fibre)) = self
            .entering
            .preimage_fibre(entering)
            .map_err(|_| self.obstruction(entering))?
        else {
            return Err(self.obstruction(entering));
        };
        let returned = self
            .returned
            .apply(&particular)
            .map_err(|_| self.obstruction(entering))?;
        let reconstructed = self
            .entering
            .apply(&particular)
            .map_err(|_| self.obstruction(entering))?;
        Ok(ForeignSectionReturn {
            from_address: self.from_address.clone(),
            to_address: self.to_address.clone(),
            entering: entering.iter().map(ToString::to_string).collect(),
            returned: returned.iter().map(ToString::to_string).collect(),
            particular_coefficients: particular.iter().map(ToString::to_string).collect(),
            complete_coefficient_fibre: fibre
                .iter()
                .map(|direction| direction.iter().map(ToString::to_string).collect())
                .collect(),
            exact_reconstruction: reconstructed == entering,
        })
    }

    fn obstruction(&self, entering: &[Rat]) -> OutOfReachableSection {
        OutOfReachableSection {
            from_address: self.from_address.clone(),
            entering: entering.iter().map(ToString::to_string).collect(),
            reachable_rank: self.entering_rank,
            ambient_dimension: self.entering.rows(),
            foreign_fallback_permitted: false,
        }
    }
}

fn descend(
    entering_rest: &CarrierSectionRest,
    returned_rest: &CarrierSectionRest,
) -> Result<DescendedForeignSection, ForeignSectionDescentRefusal> {
    if entering_rest.rows != returned_rest.rows
        || entering_rest.columns != returned_rest.columns
        || entering_rest.grain != returned_rest.grain
    {
        return Err(ForeignSectionDescentRefusal::AdjacentSection);
    }
    let entering = entering_rest.matrix()?;
    let returned = returned_rest.matrix()?;
    let complete_coefficient_kernel = entering.kernel_basis()?;
    for direction in &complete_coefficient_kernel {
        if returned
            .apply(direction)?
            .iter()
            .any(|value| !value.is_zero())
        {
            return Err(ForeignSectionDescentRefusal::Naturality);
        }
    }
    let returned_coefficient_kernel = returned.kernel_basis()?;
    let mut shortest_history_separators = Vec::new();
    for left in 0..entering.columns() {
        for right in left + 1..entering.columns() {
            if let Some(coordinate) = (0..returned.rows())
                .find(|row| returned.get(*row, left).ok() != returned.get(*row, right).ok())
            {
                let left_value = returned_rest.entries[coordinate * returned_rest.columns + left];
                let right_value = returned_rest.entries[coordinate * returned_rest.columns + right];
                shortest_history_separators.push(HistorySeparator {
                    left_history: left,
                    right_history: right,
                    target_coordinate: coordinate,
                    left: left_value,
                    right: right_value,
                });
            }
        }
    }
    Ok(DescendedForeignSection {
        from_address: entering_rest.address.clone(),
        to_address: returned_rest.address.clone(),
        entering_rank: entering.rank()?,
        entering,
        returned,
        complete_coefficient_kernel,
        returned_coefficient_kernel,
        shortest_history_separators,
        naturality_commutes: true,
    })
}

fn coefficient_naturality(
    entering_rest: &CarrierSectionRest,
    returned_rest: &CarrierSectionRest,
) -> Result<CoefficientNaturalityCertificate, ForeignSectionDescentRefusal> {
    if entering_rest.rows != returned_rest.rows
        || entering_rest.columns != returned_rest.columns
        || entering_rest.grain != returned_rest.grain
    {
        return Err(ForeignSectionDescentRefusal::AdjacentSection);
    }
    let entering_storage = coefficient_storage(entering_rest)?;
    let returned_storage = coefficient_storage(returned_rest)?;
    let complete_coefficient_kernel = entering_storage.kernel_basis()?;
    let returned_coefficient_kernel = returned_storage.kernel_basis()?;
    let naturality_commutes = complete_coefficient_kernel.iter().all(|direction| {
        returned_storage
            .apply(direction)
            .map(|returned| returned.iter().all(Zero::is_zero))
            .unwrap_or(false)
    });
    if !naturality_commutes {
        return Err(ForeignSectionDescentRefusal::Naturality);
    }
    let mut shortest_history_separators = Vec::new();
    for left in 0..returned_rest.columns {
        for right in left + 1..returned_rest.columns {
            if let Some(coordinate) = (0..returned_rest.rows).find(|row| {
                returned_rest.entries[*row * returned_rest.columns + left]
                    != returned_rest.entries[*row * returned_rest.columns + right]
            }) {
                shortest_history_separators.push(HistorySeparator {
                    left_history: left,
                    right_history: right,
                    target_coordinate: coordinate,
                    left: returned_rest.entries[coordinate * returned_rest.columns + left],
                    right: returned_rest.entries[coordinate * returned_rest.columns + right],
                });
            }
        }
    }
    Ok(CoefficientNaturalityCertificate {
        from_address: entering_rest.address.clone(),
        to_address: returned_rest.address.clone(),
        coefficient_population: entering_rest.columns,
        carrier_population: entering_rest.rows,
        entering_rank: entering_storage.rank()?,
        returned_rank: returned_storage.rank()?,
        complete_coefficient_kernel: complete_coefficient_kernel
            .iter()
            .map(|direction| direction.iter().map(ToString::to_string).collect())
            .collect(),
        returned_coefficient_kernel: returned_coefficient_kernel
            .iter()
            .map(|direction| direction.iter().map(ToString::to_string).collect())
            .collect(),
        shortest_history_separators,
        naturality_commutes,
        carrier_elimination_performed: false,
    })
}

fn coefficient_storage(
    section: &CarrierSectionRest,
) -> Result<ExactRatMatrix, ForeignSectionDescentRefusal> {
    if section.rows == 0
        || section.columns == 0
        || section.entries.len() != section.rows * section.columns
    {
        return Err(ForeignSectionDescentRefusal::CarrierSection);
    }
    let coefficients = section.columns;
    let mut storage = vec![BigInt::zero(); coefficients * coefficients];
    for row in section.entries.chunks_exact(coefficients) {
        for left in 0..coefficients {
            for right in left..coefficients {
                storage[left * coefficients + right] +=
                    BigInt::from(row[left]) * BigInt::from(row[right]);
            }
        }
    }
    for left in 0..coefficients {
        for right in 0..left {
            storage[left * coefficients + right] = storage[right * coefficients + left].clone();
        }
    }
    ExactRatMatrix::new(
        storage
            .chunks_exact(coefficients)
            .map(|row| {
                row.iter()
                    .cloned()
                    .map(Rat::from_integer)
                    .collect::<Vec<_>>()
            })
            .collect(),
    )
    .map_err(Into::into)
}

fn apply_complex(
    matrix: &ExactRatMatrix,
    current: &[ExactComplexWaveCurrent],
) -> Result<Vec<ExactComplexWaveCurrent>, ForeignSectionDescentRefusal> {
    if matrix.columns() != current.len() {
        return Err(ForeignSectionDescentRefusal::ComplexCurrentShape);
    }
    let real = matrix.apply(
        &current
            .iter()
            .map(|coefficient| coefficient.real.clone())
            .collect::<Vec<_>>(),
    )?;
    let imaginary = matrix.apply(
        &current
            .iter()
            .map(|coefficient| coefficient.imaginary.clone())
            .collect::<Vec<_>>(),
    )?;
    Ok(real
        .into_iter()
        .zip(imaginary)
        .map(|(real, imaginary)| ExactComplexWaveCurrent::new(real, imaginary))
        .collect())
}

fn complex_quadratic(
    form: &ExactRatMatrix,
    current: &[ExactComplexWaveCurrent],
) -> Result<Rat, ForeignSectionDescentRefusal> {
    if form.rows() != current.len() || form.columns() != current.len() {
        return Err(ForeignSectionDescentRefusal::ComplexCurrentShape);
    }
    let real = current
        .iter()
        .map(|coefficient| coefficient.real.clone())
        .collect::<Vec<_>>();
    let imaginary = current
        .iter()
        .map(|coefficient| coefficient.imaginary.clone())
        .collect::<Vec<_>>();
    let form_real = form.apply(&real)?;
    let form_imaginary = form.apply(&imaginary)?;
    Ok(real
        .iter()
        .zip(form_real)
        .fold(Rat::zero(), |sum, (left, right)| sum + left * right)
        + imaginary
            .iter()
            .zip(form_imaginary)
            .fold(Rat::zero(), |sum, (left, right)| sum + left * right))
}

fn receiver_complex_quadratic(
    form: &ForeignReceiverConstitutiveForm,
    current: &[ExactComplexWaveCurrent],
) -> Result<Rat, ForeignSectionDescentRefusal> {
    if form.extent()? != current.len() {
        return Err(ForeignSectionDescentRefusal::ComplexCurrentShape);
    }
    let real = current
        .iter()
        .map(|coefficient| coefficient.real.clone())
        .collect::<Vec<_>>();
    let imaginary = current
        .iter()
        .map(|coefficient| coefficient.imaginary.clone())
        .collect::<Vec<_>>();
    let form_real = form.apply(&real)?;
    let form_imaginary = form.apply(&imaginary)?;
    Ok(real
        .iter()
        .zip(form_real)
        .fold(Rat::zero(), |sum, (left, right)| sum + left * right)
        + imaginary
            .iter()
            .zip(form_imaginary)
            .fold(Rat::zero(), |sum, (left, right)| sum + left * right))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn points(columns: &[&[i64]]) -> Vec<Vec<(i64, i64)>> {
        columns
            .iter()
            .map(|column| column.iter().map(|value| (*value, *value)).collect())
            .collect()
    }

    #[test]
    fn foreign_map_descends_exactly_on_the_reachable_span() {
        let entering =
            CarrierSectionRest::from_columns("layer-0", 0, &points(&[&[1, 0, 1], &[0, 1, 1]]))
                .expect("entering");
        let returned =
            CarrierSectionRest::from_columns("layer-1", 0, &points(&[&[2, 0, 2], &[0, 3, 3]]))
                .expect("returned");
        let rest = ForeignReachableSectionRest::seal(
            vec!["history-a".to_owned(), "history-b".to_owned()],
            vec![4, 9],
            vec![entering, returned],
        )
        .expect("rest");
        let bytes = rest.canonical_bytes().expect("bytes");
        let coefficient = ForeignReachableSectionRest::read(&bytes)
            .expect("coefficient read")
            .coefficient_naturality_certificates()
            .expect("coefficient certificate");
        let mounted = ForeignReachableSectionRest::read(&bytes)
            .expect("read")
            .mount()
            .expect("mount");
        let returned = mounted.conduct_history(0).expect("conduct");
        assert_eq!(returned.len(), 1);
        assert_eq!(returned[0].returned, vec!["2", "0", "2"]);
        assert!(returned[0].complete_coefficient_fibre.is_empty());
        assert!(returned[0].exact_reconstruction);
        assert_eq!(coefficient.len(), mounted.maps.len());
        assert_eq!(coefficient[0].entering_rank, mounted.maps[0].entering_rank);
        assert_eq!(
            coefficient[0].complete_coefficient_kernel.len(),
            mounted.maps[0].complete_coefficient_kernel.len()
        );
        assert!(coefficient[0].naturality_commutes);
        assert!(!coefficient[0].carrier_elimination_performed);
        let coordinate_obstruction = mounted.maps[0]
            .coordinate_obstruction_from(&[Rat::one(), Rat::zero()])
            .expect("derived coordinate obstruction");
        assert!(!coordinate_obstruction.foreign_fallback_permitted);
        assert_eq!(coordinate_obstruction.ambient_dimension, 3);
        let outside = vec![Rat::from_integer(1.into()); 3];
        assert_eq!(
            mounted.maps[0]
                .conduct(&outside)
                .expect_err("outside span")
                .foreign_fallback_permitted,
            false
        );
    }

    #[test]
    fn visible_return_along_an_entering_kernel_refuses_naturality() {
        let entering = CarrierSectionRest::from_columns("layer-0", 0, &points(&[&[1, 0], &[1, 0]]))
            .expect("entering");
        let returned = CarrierSectionRest::from_columns("layer-1", 0, &points(&[&[1, 0], &[0, 1]]))
            .expect("returned");
        let rest = ForeignReachableSectionRest::seal(
            vec!["history-a".to_owned(), "history-b".to_owned()],
            vec![4, 9],
            vec![entering, returned],
        )
        .expect("rest");
        assert!(matches!(
            rest.mount(),
            Err(ForeignSectionDescentRefusal::Naturality)
        ));
    }

    #[test]
    fn equal_carrier_words_share_a_receiver_class_without_losing_occurrence_lineage() {
        let entering =
            CarrierSectionRest::from_columns("layer-0", 0, &points(&[&[1, 2], &[1, 2], &[0, 3]]))
                .expect("entering");
        let returned =
            CarrierSectionRest::from_columns("layer-1", 0, &points(&[&[4, 5], &[4, 5], &[0, 6]]))
                .expect("returned");
        let rest = ForeignReachableSectionRest::seal(
            vec![
                "occurrence-a".to_owned(),
                "occurrence-b".to_owned(),
                "occurrence-c".to_owned(),
            ],
            vec![4, 9, 12],
            vec![entering, returned],
        )
        .expect("rest");
        let quotient = rest
            .coefficient_receiver_quotient()
            .expect("receiver quotient");
        assert_eq!(quotient.history_to_class, vec![0, 0, 1]);
        assert_eq!(quotient.classes.len(), 2);
        assert_eq!(quotient.classes[0].histories, vec![0, 1]);
        assert_eq!(quotient.classes[0].history_addresses.len(), 2);
        assert_eq!(quotient.shortest_separators.len(), 2);
        assert!(quotient.shortest_separators.iter().all(|separator| {
            separator.right_history == 2 && separator.section == 0 && separator.coordinate == 0
        }));
    }

    #[test]
    fn the_foreign_section_is_an_oriented_complex_parametron_before_binary_reception() {
        let entering =
            CarrierSectionRest::from_columns("carrier", 0, &points(&[&[1, 2, 0], &[0, 1, 3]]))
                .expect("section");
        let returned = CarrierSectionRest::from_columns(
            "returned-carrier",
            0,
            &points(&[&[1, 2, 0], &[0, 1, 3]]),
        )
        .expect("returned section");
        let rest = ForeignReachableSectionRest::seal(
            vec!["history-a".to_owned(), "history-b".to_owned()],
            vec![4, 9],
            vec![entering, returned],
        )
        .expect("rest");
        let forms = (0..rest.sections.len())
            .map(|_| ForeignReceiverConstitutiveForm::Diagonal(vec![Rat::one(); 3]))
            .collect();
        let atlas = rest.parametron_atlas(forms).expect("parametron atlas");
        let current = vec![
            ExactComplexWaveCurrent::one(),
            ExactComplexWaveCurrent::new(Rat::zero(), Rat::one()),
        ];
        let receipt = atlas.sections[0]
            .inspect_current(&current, &BTreeSet::from([1usize]))
            .expect("current receipt");
        assert_eq!(receipt.incidence_rank, 2);
        assert_eq!(receipt.incidence_kernel_dimension, 0);
        assert_eq!(receipt.radical_dimension, 0);
        assert!(receipt.storage_pullback_exact);
        assert!(receipt.orientation_covariant);
        assert!(receipt.half_turn_negates_complete_current);
        assert!(!receipt.binary_receiver_taken);
        assert_eq!(
            receipt.realized_current,
            vec![
                ExactComplexWaveCurrent::new(Rat::one(), Rat::zero()),
                ExactComplexWaveCurrent::new(Rat::from_integer(BigInt::from(2)), Rat::one(),),
                ExactComplexWaveCurrent::new(Rat::zero(), Rat::from_integer(BigInt::from(3)),),
            ]
        );
    }
}
