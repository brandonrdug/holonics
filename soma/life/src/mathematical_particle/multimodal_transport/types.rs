use serde::{Deserialize, Serialize};

pub const JOINT_MEDIA_STANDING_SCHEMA: &str = "holonics.r5.joint-media-standing.v1";
pub const JOINT_MEDIA_FIBRES_SCHEMA: &str = "holonics.r5.joint-media-fibres.v1";
pub const JOINT_MEDIA_DECODER_SCHEMA: &str = "holonics.r5.joint-media-decoder.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum MathematicalMediaPort {
    Notation,
    Vector,
    RasterVision,
}

impl MathematicalMediaPort {
    pub fn device_ordinal(self) -> u32 {
        match self {
            Self::Notation => 0,
            Self::Vector => 1,
            Self::RasterVision => 2,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductLineage {
    pub m0_source_sha256: String,
    pub m0_product_sha256: String,
    pub i4_rest_sha256: String,
    pub r4_boundary_sha256: String,
    pub source_occurrence: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MediaPortDeclaration {
    pub port: MathematicalMediaPort,
    pub boundary: String,
    pub family_widths: Vec<u32>,
    pub incidence: String,
}

/// One exact oriented axis in a source chart. The extent and scale remain rational and no
/// floating-point approximation can govern incidence or rendering.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactMediaAxis {
    pub name: String,
    pub extent_numerator: u32,
    pub extent_denominator: u32,
    pub common_scale_numerator: u32,
    pub common_scale_denominator: u32,
    pub forward_hand: i8,
}

/// Spatial testimony that exists before any notation or caption is consulted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactSpatialDeclaration {
    pub dimension: u32,
    pub axes: Vec<ExactMediaAxis>,
    pub uncertainty_fibre_sha256: String,
    pub source_lineage_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SharedMediaVertex {
    pub address: u32,
    pub port: Option<MathematicalMediaPort>,
    pub boundary: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SharedMediaContact {
    pub address: u32,
    pub from: u32,
    pub to: u32,
    pub hand: i8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SharedMediaHigherCell {
    pub address: u32,
    pub oriented_boundary: Vec<i64>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SharedMediaSubcomplex {
    pub common_world_receiver: String,
    pub generator_lineage: String,
    pub predecessor: u32,
    pub successor: u32,
    pub successor_action: Vec<u32>,
    pub vertices: Vec<SharedMediaVertex>,
    pub contacts: Vec<SharedMediaContact>,
    pub higher_cells: Vec<SharedMediaHigherCell>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AnchorSection {
    pub ordinal: u32,
    pub vector_candidates: u32,
    pub raster_four_candidates: u32,
    pub raster_eight_candidates: u32,
}

impl AnchorSection {
    pub fn raster_candidates(&self) -> Option<u32> {
        self.raster_four_candidates
            .checked_add(self.raster_eight_candidates)
    }
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JointMediaStanding {
    pub schema: String,
    pub lineage: ProductLineage,
    pub family_occurrences: Vec<String>,
    pub heldout_family: u32,
    pub ports: Vec<MediaPortDeclaration>,
    pub shared: SharedMediaSubcomplex,
    pub heldout_anchor_sections: Vec<AnchorSection>,
    pub open_exterior: Vec<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct MediaSourceInterior {
    pub family: u32,
    pub port: MathematicalMediaPort,
    pub artifact_occurrence: String,
    pub artifact_sha256: String,
    pub chart: String,
    pub occurrence_population: u32,
    pub contact_population: u32,
    pub incidence_sha256: String,
    pub spatial: ExactSpatialDeclaration,
    /// Canonical source testimony. It is length-framed in the decoder wire, never JSON-expanded
    /// into an array of octets.
    pub canonical_interior: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMediaConsequence {
    pub address: u32,
    pub family: u32,
    pub state: u32,
    pub port: MathematicalMediaPort,
    pub interior_at: u32,
    pub consequence_sha256: String,
    pub incidence_sha256: String,
}

#[derive(Debug, PartialEq, Eq)]
pub struct JointMediaDecoder {
    pub schema: String,
    pub consequences: Vec<NativeMediaConsequence>,
    pub interiors: Vec<MediaSourceInterior>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MediaCandidatePair {
    pub anchor: u32,
    pub member: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum UnmatchedMediaMember {
    Notation(u32),
    Vector(u32),
    RasterFour(u32),
    RasterEight(u32),
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FamilyCorrespondenceFibre {
    pub family: u32,
    pub anchor_population: u32,
    pub vector_population: u32,
    pub raster_four_population: u32,
    pub raster_eight_population: u32,
    pub text_vector: Vec<MediaCandidatePair>,
    pub text_raster_four: Vec<MediaCandidatePair>,
    pub text_raster_eight: Vec<MediaCandidatePair>,
    pub unmatched: Vec<UnmatchedMediaMember>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMediaFibre {
    pub native_address: u32,
    pub family: u32,
    pub state: u32,
    pub port: MathematicalMediaPort,
    pub interior_at: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MediaNaturalitySquare {
    pub family: u32,
    pub port: MathematicalMediaPort,
    pub source_interior_at: u32,
    pub native_predecessor: u32,
    pub native_successor: u32,
    pub generator_lineage: String,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JointMediaFibres {
    pub schema: String,
    pub correspondences: Vec<FamilyCorrespondenceFibre>,
    pub native_fibres: Vec<NativeMediaFibre>,
    pub naturality_squares: Vec<MediaNaturalitySquare>,
    pub open_exterior: Vec<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct MediaSourceFamily {
    pub family: u32,
    pub occurrence: String,
    pub notation: MediaSourceInterior,
    pub vector: MediaSourceInterior,
    pub raster: MediaSourceInterior,
    pub correspondences: FamilyCorrespondenceFibre,
}
