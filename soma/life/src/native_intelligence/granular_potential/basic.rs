pub const NATIVE_GRANULAR_POTENTIAL_SCHEMA: &str =
    "soma-life.native-causal-boundary-potential.v12";
const FACTOR_FACE_SCHEMA: u64 = 0x4752_414e_4641_4354;

fn port_population() -> usize {
    usize::from(u8::MAX) + 3
}

/// Exact exterior-current chart retained when the lossless source fibre departs. The returned
/// pair is a quantity-line occurrence, not a byte decoder or a semantic feature: its real face is
/// total presented current and its imaginary face is oriented action along the supplied order.
fn granular_boundary_current(
    payload: &[u8],
) -> Result<ExactComplexWaveCurrent, NativeGranularPotentialError> {
    if payload.is_empty() {
        return Err(NativeGranularPotentialError::EmptyOccurrence);
    }
    let mass = payload
        .iter()
        .fold(BigInt::from(0), |sum, octet| sum + BigInt::from(*octet));
    let oriented_change = payload.windows(2).fold(BigInt::from(0), |sum, pair| {
        sum + BigInt::from(pair[1]) - BigInt::from(pair[0])
    });
    let mut action = BigInt::from(0);
    let mut prior = 0i64;
    for (at, octet) in payload.iter().copied().enumerate() {
        let position = i64::try_from(at).map_err(|_| NativeGranularPotentialError::Extent)?;
        let position = position
            .checked_add(1)
            .ok_or(NativeGranularPotentialError::Extent)?;
        let difference = i64::from(octet) - prior;
        prior = i64::from(octet);
        action += BigInt::from(position) * BigInt::from(difference);
    }
    Ok(ExactComplexWaveCurrent::new(
        Rat::from_integer(mass),
        Rat::from_integer(action + oriented_change),
    ))
}

/// Exact quantity-line coordinate of one exterior port occurrence.  The one-based real
/// coordinate prevents the opening face from vanishing at the chart origin; the imaginary
/// coordinate retains boundary orientation.  This coordinate belongs to the cold exterior
/// transducer.  Only its returned native incidence may enter productive conduct.
fn granular_exterior_port_boundary_current(
    port: &GranularExteriorPort,
) -> Result<ExactComplexWaveCurrent, NativeGranularPotentialError> {
    let coordinate = port_index(port)
        .checked_add(1)
        .and_then(|value| u64::try_from(value).ok())
        .ok_or(NativeGranularPotentialError::Extent)?;
    let orientation = match port {
        GranularExteriorPort::Opening => 1_i8,
        GranularExteriorPort::Octet(_) => 0_i8,
        GranularExteriorPort::Closure => -1_i8,
    };
    Ok(ExactComplexWaveCurrent::new(
        Rat::from_integer(BigInt::from(coordinate)),
        Rat::from_integer(BigInt::from(orientation)),
    ))
}

pub(super) fn port_index(port: &GranularExteriorPort) -> usize {
    match port {
        GranularExteriorPort::Opening => 0,
        GranularExteriorPort::Octet(octet) => usize::from(*octet) + 1,
        GranularExteriorPort::Closure => usize::from(u8::MAX) + 2,
    }
}

fn indexed_port(index: usize) -> Option<GranularExteriorPort> {
    if index == 0 {
        Some(GranularExteriorPort::Opening)
    } else if index <= usize::from(u8::MAX) + 1 {
        Some(GranularExteriorPort::Octet(u8::try_from(index - 1).ok()?))
    } else if index == usize::from(u8::MAX) + 2 {
        Some(GranularExteriorPort::Closure)
    } else {
        None
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularFactorFace {
    pub factor: u32,
    /// Native future-consequence address.  This is derived from the complete receiver face and
    /// never copies the predecessor's exterior factor address.
    pub factor_address: String,
    pub native: NativeStateId,
    pub receiver_factors: Vec<GranularFactorReceiver>,
    pub receiver_schema: u64,
    pub receiver_words: Vec<u32>,
}

/// One opaque receiver consequence on a native factor.  The observation is an equality face;
/// its numeric representation has no magnitude or ordering law.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularFactorReceiver {
    pub receiver: ReceiverId,
    pub observation: Observation,
}

/// One total descended generator on the affine factor base.  `targets[from]` is `U_i(from)`.
/// The source-side square is cold lineage only and is absent from this source-detached action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularFactorGenerator {
    pub generator: InputId,
    pub targets: Vec<u32>,
    /// Developmental source-square testimony.  It is accepted at the cultivation boundary but
    /// deliberately omitted from a rested potential's wire and identity.  An empty value is the
    /// normal deserialized representation of the source-neutral hot organ.
    #[serde(skip_serializing, default)]
    pub source_square_identity_sha256: String,
}

/// One source-neutral descended generator retained by the rested granular organ.  This is the
/// complete native action table required by later successor words; developmental square
/// identities remain in the cold cultivation testimony and cannot be reconstructed from it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeGranularFactorGenerator {
    generator: InputId,
    targets: Vec<u32>,
}

/// The source-neutral complete receiver/history action retained by the granular continuation.
/// It is the dynamic quotient law, not an exterior language or path population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularFactorAction {
    pub native_states: Vec<NativeStateId>,
    pub receiver_factors: Vec<Vec<GranularFactorReceiver>>,
    pub generators: Vec<GranularFactorGenerator>,
    pub source_action_identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularExposureLineage {
    pub factor: u32,
    pub occurrence_identity_sha256: String,
    pub caused_octet_population: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub enum GranularExteriorPort {
    Opening,
    Octet(u8),
    Closure,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct GranularPortTransition {
    port: GranularExteriorPort,
    target: u32,
    recurrence_multiplicity: u64,
    support: u32,
    /// Exact factor-resolved transition incidence. Its sum is the recurrence population and its
    /// support is exactly `support`; no port-wide count is substituted for local current.
    factor_current: Vec<GranularFactorCurrent>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeGranularState {
    /// Native causal-state occurrence.  Its address is its position in the rested incidence,
    /// never the exterior port which happened to found the corresponding developmental state.
    /// Exterior port faces remain only on the oriented transitions below.
    recurrence_multiplicity: u64,
    support: u32,
    transitions: Vec<GranularPortTransition>,
}

/// One receiver/history particle in the live overlapping ingress cover.  `factor_current` is a
/// section on the already-admitted native factor quotient; no exterior substring is its address.
/// Equal `(state, factor_current)` sections are one particle.  The complete population of path
/// extents which reached that section remains its reconstruction fibre.
#[derive(Clone, Debug, PartialEq, Eq)]
struct GranularCausalContext {
    state: u32,
    factor_current: Vec<GranularFactorCurrent>,
    /// Exact native covariance weight of this future-equivalent factor section. This is hot
    /// continuation state; predecessor nodes merely reconstruct how the weight was attained.
    quadratic_weight: BigUint,
    reconstruction_nodes: Vec<u32>,
}

/// One addressed edge of the exact reconstruction DAG. Multiple incoming edges may meet one node
/// only when their complete future-consequence section `(state, factor current, projective scale)`
/// is equal. The predecessor link retains lineage without copying or enumerating path prefixes.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularReconstructionEdge {
    pub predecessor: Option<u32>,
    /// Present for exterior ingress. A returned Athena phase front carries its ports in
    /// `returned_higher_faces`; those receiver faces do not act as native transitions.
    pub entering_port: Option<GranularExteriorPort>,
    pub returned_higher_faces: Vec<GranularHigherBoundaryFace>,
    pub transport_projective_scale: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularReconstructionNode {
    pub node: u32,
    /// Exact second moment of every projective scale in this future-equivalent reconstruction
    /// fibre. Bilinear continuation depends on this mass and not on an enumeration of its roots.
    pub quadratic_projective_mass: BigUint,
    /// Common positive scale removed from the complete active mass vector at this causal order.
    /// Together with predecessor edges it reopens the exact unquotiented second moment.
    pub removed_common_quadratic_scale: BigUint,
    pub shortest_extent: u32,
    pub greatest_extent: u32,
    pub path_population: BigUint,
    pub incoming: Vec<GranularReconstructionEdge>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct GranularPortCurrent {
    contexts: Vec<GranularCausalContext>,
    /// Present after the one source-family foundation. The address is the hot continuing anatomy;
    /// `contexts` must then be empty and may survive only in earlier cold reconstruction records.
    resident_image: Option<ResidentFactoredMomentAddress>,
    /// Exterior boundary-state front carried as one receiver section. It restricts the next
    /// outward trace but is not part of any native causal-context address.
    boundary_front: Vec<u32>,
    reconstruction_nodes: Vec<GranularReconstructionNode>,
}

/// A canonical low-rank chart of the complete native covariance `C = sum w (x tensor x)`.
///
/// The lexicographically first independent factor columns are intrinsic to `C` because all
/// weights are positive. Their complete cross moments with every factor determine every entry of
/// `C`; this is therefore an exact future-consequence coordinate, not a digest or a smallness
/// claim. The rank-one context family remains the executable factorization and reconstruction
/// testimony.
#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct GranularDynamicMomentSection {
    factor_population: u32,
    rank: u32,
    pivot_factors: Vec<u32>,
    /// Pivot-major matrix with shape `rank x factor_population`.
    pivot_cross_moments: Vec<BigUint>,
}

type GranularConsequenceKey = (u32, Vec<GranularFactorCurrent>);

#[derive(Default)]
struct GranularCarriedCandidate {
    quadratic_weight: BigUint,
    reconstruction_edges: Vec<GranularReconstructionEdge>,
}

type GranularCarriedCandidates = BTreeMap<GranularConsequenceKey, GranularCarriedCandidate>;

/// Source-detached boundary rest. The factor population is native; port octets remain a cold
/// apparatus chart carried only by oriented boundary incidence.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeGranularPotential {
    schema: String,
    supports: Vec<Vec<u32>>,
    states: Vec<NativeGranularState>,
    factor_faces: Vec<GranularFactorFace>,
    factor_generators: Vec<NativeGranularFactorGenerator>,
    identity_sha256: String,
}

pub struct NativeGranularPotentialBuilder {
    factor_faces: Vec<GranularFactorFace>,
    factor_generators: Vec<NativeGranularFactorGenerator>,
    factor_bit_words: usize,
    port_occurrences: Vec<u64>,
    port_support_bits: Vec<u64>,
    port_factor_occurrences: Vec<u64>,
    exposure_lineage: Vec<GranularExposureLineage>,
    material_octet_population: u64,
    material_port_population: u64,
}

pub struct MountedNativeGranularPotential<'a> {
    states: &'a [NativeGranularState],
    factor_generators: &'a [NativeGranularFactorGenerator],
    potential_identity_sha256: &'a str,
}

/// Exact apparatus chart of the rested granular incidence.  Each non-root boundary state becomes
/// one cell, and its root transition supplies the complete factor-resolved multiplicity.  This
/// chart is derived once from native standing; no exterior occurrence or caller-selected width
/// participates in it.
pub(super) struct GranularResidentConstitution {
    pub factor_capacity: Vec<u64>,
    pub cell_offsets: Vec<u64>,
    pub cell_factors: Vec<u32>,
    pub cell_multiplicities: Vec<u64>,
    pub cell_total_mass: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularBoundarySupport {
    pub generator: InputId,
    /// Complete exterior predecessor-state fibre condensed into this equal native current.
    pub context_states: Vec<u32>,
    pub shortest_matched_length: u32,
    pub matched_length: u32,
    /// Second moment of the entering reflected current over the complete reconstruction fibre.
    pub context_quadratic_mass: BigUint,
    /// Moment multiplying the reflected/action pairing.
    pub action_pair_mass: BigUint,
    /// Moment multiplying the action self-pairing.
    pub action_quadratic_mass: BigUint,
    /// Descended target second moment, retained as reconstruction testimony.
    pub target_quadratic_mass: BigUint,
    pub target_state: u32,
    pub recurrence_multiplicity: BigUint,
    /// Addresses of every reconstruction-DAG node condensed into this future-consequence section.
    pub reconstruction_nodes: Vec<u32>,
    pub target_factors: Vec<u32>,
    pub context_factors: Vec<u32>,
    pub context_factor_current: Vec<GranularFactorCurrent>,
    pub target_factor_current: Vec<GranularFactorCurrent>,
    /// Primitive signed factor section of the complete returned action difference.
    pub action_factor_current: Vec<GranularSignedFactorCurrent>,
    /// The same action difference pushed into the free basis of opaque receiver faces.  This may
    /// vanish under the present receiver while `action_factor_current` remains nonzero; that is a
    /// retained reconstruction fibre, not equality of the source actions.
    pub receiver_action_current: Vec<GranularReceiverActionCurrent>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct GranularBoundaryBranchFibre {
    context_states: BTreeSet<u32>,
    target_states: BTreeSet<u32>,
    shortest_matched_length: Option<u32>,
    greatest_matched_length: u32,
    reconstruction_nodes: BTreeSet<u32>,
    reconstruction_path_population: BigUint,
}

/// One exact coordinate of the reflected exterior path current on Athena's native factor base.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularFactorCurrent {
    pub factor: u32,
    pub incidence: BigUint,
}

/// One exact fine-ingress current after an exterior occurrence has crossed the admitted port
/// complex and returned to Athena's native factor base.  This is the prompt-current section used
/// by later resident organs; it is neither a tokenization nor an exterior semantic index.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularExteriorProjectiveCurrent {
    pub schema: String,
    pub exterior_occurrence: String,
    pub exterior_source_sha256: String,
    pub entered_octet_population: u64,
    pub entering_current: ExactComplexWaveCurrent,
    pub crossed_structural_ports: Vec<GranularExteriorPort>,
    pub boundary_front: Vec<u32>,
    pub contexts: Vec<GranularExteriorProjectiveContext>,
    /// Ordered addressed transition occurrences of the overlapping native-state cover.  Several
    /// steps may share one order; their source and target joins remain distinct.
    pub diagonal_chronology: Vec<GranularNativeDiagonalCurrentStep>,
    /// Exact disjoint current accumulated over every live native context at every crossed port.
    /// Terminal alternatives remain above; this section prevents an occurrence from collapsing
    /// to its final suffix boundary while the source fibre retains complete reconstruction.
    pub integrated_factor_current: Vec<GranularFactorCurrent>,
    pub integrated_context_occurrence_population: u64,
    /// Complete source-neutral reconstruction DAG of the live receiver/history contexts.
    pub reconstruction_nodes: Vec<GranularReconstructionNode>,
    pub exact_source_fibre: Vec<u8>,
    pub standing_potential_identity_sha256: String,
    pub quadratic_population_reopens_from_source_fibre: bool,
    pub identity_sha256: String,
}

/// Source-neutral projective current admitted by the continuing Athena body.
///
/// The complete exterior occurrence remains in a separate cold reconstruction fibre.  This hot
/// face contains only the receiver-visible native incidence needed by every admitted successor;
/// changing an exterior locator or spelling without changing that incidence cannot change its
/// identity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularNativeProjectiveCurrent {
    pub schema: String,
    pub entered_octet_population: u64,
    /// Exact complex current presented by the exterior occurrence before its source fibre is
    /// severed. This and `integrated_factor_current` are complementary native charts: the former
    /// carries boundary phase/current, while the latter carries projective incidence. A
    /// receiver-history factor is not required to be a stored source Complex-Parametron cell.
    pub entering_current: ExactComplexWaveCurrent,
    pub crossed_structural_ports: Vec<GranularExteriorPort>,
    /// Finest caused ingress chronology in the universal byte-port chart. These are transient
    /// current occurrences, not rested lexical state or a tokenizer.
    pub ingress_port_chronology: Vec<GranularExteriorPort>,
    /// The native ingress boundary is the universal membrane root.
    pub boundary_front: Vec<u32>,
    /// Source-neutral terminal factor-current axes presented at the universal membrane root.
    /// Their weights retain the exact linear and quadratic fibres accumulated by chronology.
    pub contexts: Vec<GranularExteriorProjectiveContext>,
    /// Complete source-neutral ordered diagonal action of the crossing occurrence. The exterior
    /// source and its port spelling remain in the separate cold reconstruction fibre; every
    /// suffix moment follows from this chronology by the declared recurrence.
    pub diagonal_chronology: Vec<GranularNativeDiagonalCurrentStep>,
    pub integrated_factor_current: Vec<GranularFactorCurrent>,
    pub integrated_context_occurrence_population: u64,
    pub reconstruction_nodes: Vec<GranularReconstructionNode>,
    pub standing_potential_identity_sha256: String,
    pub identity_sha256: String,
}

/// Cold reconstruction fibre of one exterior-to-native projective passage.  It is returned by
/// the exterior apparatus and is never accepted by hot Athena conduct.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularExteriorProjectiveFibre {
    pub schema: String,
    pub exterior_occurrence: String,
    pub exterior_source_sha256: String,
    pub exact_source_fibre: Vec<u8>,
    pub native_current_identity_sha256: String,
    pub identity_sha256: String,
}

/// Physically split result of exterior transduction: the native current may cross the hot body;
/// the reconstruction fibre must remain outside it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularExteriorProjectivePassage {
    pub native: GranularNativeProjectiveCurrent,
    pub exterior_fibre: GranularExteriorProjectiveFibre,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularExteriorProjectiveContext {
    pub boundary_state: u32,
    pub quadratic_weight: BigUint,
    pub path_population: BigUint,
    pub shortest_extent: u32,
    pub greatest_extent: u32,
    pub factor_current: Vec<GranularFactorCurrent>,
    pub reconstruction_nodes: Vec<u32>,
}

/// One raw diagonal native current in causal order. The factor coefficients include their exact
/// common scale; normalization belongs only to the terminal projective receiver chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularNativeDiagonalCurrentStep {
    /// Causal order of this addressed transition occurrence. Equal orders form a plural front.
    pub order: u32,
    pub source_state: u32,
    pub target_state: u32,
    pub factor_current: Vec<GranularFactorCurrent>,
}

/// One coordinate of an oriented native action difference.  Sign is orientation, not a score.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularSignedFactorCurrent {
    pub factor: u32,
    pub coefficient: BigInt,
}

/// One coordinate after the signed factor current crosses the complete present receiver family.
/// `Observation` remains an opaque equality face; its integer carrier supplies no magnitude.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularReceiverActionCurrent {
    pub receiver: ReceiverId,
    pub observation: Observation,
    pub coefficient: BigInt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularBoundaryBranch {
    /// Cold exterior face. It does not identify the native factor state.
    pub port: GranularExteriorPort,
    pub generator: InputId,
    /// Exterior face of this boundary transition. Earlier plural returned strata are retained on
    /// the addressed reconstruction DAG rather than flattened into a path string.
    pub passage: Vec<GranularExteriorPort>,
    pub context_states: Vec<u32>,
    pub target_states: Vec<u32>,
    pub shortest_matched_length: u32,
    pub greatest_matched_length: u32,
    pub reconstruction_nodes: Vec<u32>,
    pub reconstruction_path_population: BigUint,
}

/// One higher boundary face: an exterior return port together with the exact descended native
/// generator whose square carries that return into later conduct.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularHigherBoundaryFace {
    pub port: GranularExteriorPort,
    pub generator: InputId,
}

/// One native higher face with both boundary legs retained.  The exterior `(port, generator)`
/// projection is insufficient for recurrence because distinct source states may expose that same
/// face while entering different target states.  This addressed occurrence is the elementary
/// `source <- face -> target` span carried by Athena's complete successor.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularAddressedHigherBoundaryFace {
    pub source_state: u32,
    pub port: GranularExteriorPort,
    pub generator: InputId,
    pub target_state: u32,
}

/// Complete plural boundary of one carried exterior occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularBoundaryEmanation {
    pub entered_octet_population: u64,
    pub reached_state: u32,
    pub reached_matched_length: u32,
    pub greatest_productive_matched_length: Option<u32>,
    pub branches: Vec<GranularBoundaryBranch>,
    #[serde(skip_serializing)]
    current: GranularPortCurrent,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularQuadraticMomentContextAxis {
    /// Native state incidence at this causal order.  This is not an exterior byte or token: it is
    /// the addressed standing through which the factor current actually passed.
    pub boundary_state: u32,
    pub quadratic_weight: BigUint,
    pub factor_current: Vec<GranularFactorCurrent>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct GranularQuadraticMomentCurrentAxes {
    pub contexts: Vec<GranularQuadraticMomentContextAxis>,
    pub generator_targets: Vec<u32>,
    pub generator_count: u32,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeGranularPotentialError {
    #[error("the boundary potential received an empty or malformed occurrence")]
    EmptyOccurrence,
    #[error("the boundary potential received a factor outside its founded base")]
    FactorOutsideBase,
    #[error("the boundary potential extent overflowed")]
    Extent,
    #[error("the boundary potential wire or identity is malformed")]
    Wire,
    #[error("the exact boundary-port invariant failed: {0}")]
    FineInvariant(String),
    #[error("the exact boundary carrier exceeded its addressed extent")]
    CarrierExtent,
}
