use serde::{Deserialize, Serialize};

pub const MANIFEST_SCHEMA: &str = "holonic-engine.phoenix.w3-cultivation-material.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum MaterialArm {
    Development,
    StructuralHeldOut,
    CodecVariant,
    SubjectDisjointControl,
    NoOp,
    MatchedFoil,
}

#[cfg(test)]
pub trait ExteriorTextCodec {
    fn variant_identity(&self) -> &str;
    fn encode(&self, text: &str) -> Result<Vec<u32>, String>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaterialInput<'a> {
    pub lineage: &'a str,
    pub subject: &'a str,
    pub arm: MaterialArm,
    pub related_to: Option<&'a str>,
    pub surface_rebase_identity: Option<&'a str>,
    pub text: &'a str,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ContiguousTokenWindow {
    pub development_start: u64,
    pub held_out_start: u64,
    pub length: u64,
    pub token_ids: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidenceChange {
    pub extent: u64,
    pub changed_positions: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialIdentity {
    pub identity: String,
    pub lineage: String,
    pub subject: String,
    pub arm: MaterialArm,
    pub related_to: Option<String>,
    pub surface_rebase_identity: Option<String>,
    pub text_sha256: String,
    pub text_octets: u64,
    pub token_ids: Vec<u32>,
    pub codec_variant: String,
    pub structural_overlap: Option<ContiguousTokenWindow>,
    pub incidence_change: Option<IncidenceChange>,
}

/// The two exterior routes used to found a codec variant.  This is a path witness, not a
/// semantic material label.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum CodecPath {
    TokenizerJson,
    PretokenizedCodebookSurface,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CultivationMaterialManifest {
    pub schema: String,
    pub w1_codebook_sha256: String,
    pub tokenizer_sha256: String,
    pub tokenizer_config_sha256: Option<String>,
    pub entries: Vec<MaterialIdentity>,
    pub manifest_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MaterialLineageRefusal {
    W1Boundary(String),
    EmptyField {
        field: &'static str,
    },
    AbsoluteLineage(String),
    EmptyText {
        identity: String,
    },
    #[cfg(test)]
    Codec {
        identity: String,
        reason: String,
    },
    TokenOutOfRange {
        identity: String,
        token: u32,
        extent: u32,
    },
    OpenToken {
        identity: String,
        token: u32,
    },
    DuplicateIdentity(String),
    MissingArm(MaterialArm),
    MissingRelation {
        identity: String,
        arm: MaterialArm,
    },
    UnknownRelation {
        identity: String,
        related_to: String,
    },
    LineageNotSeparated {
        identity: String,
        related_to: String,
    },
    SubjectNotDisjoint {
        identity: String,
        subject: String,
    },
    FoilSubjectMismatch {
        identity: String,
        related_to: String,
    },
    FoilPopulationMismatch {
        identity: String,
        related_to: String,
    },
    FoilIncidenceUnchanged {
        identity: String,
        related_to: String,
    },
    UnchangedRelatedMaterial {
        identity: String,
        related_to: String,
    },
    CodecVariantNeedsRebase {
        identity: String,
        related_to: String,
    },
    InvalidSurfaceRebaseIdentity {
        identity: String,
    },
    StructuralOverlapMismatch {
        identity: String,
    },
    UnexpectedOverlapEvidence {
        identity: String,
    },
    IncidenceEvidenceMismatch {
        identity: String,
    },
    UnexpectedIncidenceEvidence {
        identity: String,
    },
    NoOpCarriesMaterial {
        identity: String,
    },
    NoOpRequiresDevelopment {
        identity: String,
    },
    NoOpMaterialMismatch {
        identity: String,
        related_to: String,
    },
}

impl std::fmt::Display for MaterialLineageRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::W1Boundary(reason) => write!(f, "W1 exterior boundary refused: {reason}"),
            Self::EmptyField { field } => write!(f, "empty material field: {field}"),
            Self::AbsoluteLineage(value) => write!(f, "lineage is not host-independent: {value}"),
            Self::EmptyText { identity } => write!(f, "material {identity} has empty text"),
            #[cfg(test)]
            Self::Codec { identity, reason } => write!(f, "codec refused {identity}: {reason}"),
            Self::TokenOutOfRange {
                identity,
                token,
                extent,
            } => write!(
                f,
                "material {identity} token {token} is outside W1 extent {extent}"
            ),
            Self::OpenToken { identity, token } => {
                write!(f, "material {identity} token {token} remains open in W1")
            }
            Self::DuplicateIdentity(identity) => {
                write!(f, "duplicate material identity {identity}")
            }
            Self::MissingArm(arm) => write!(f, "required material arm absent: {arm:?}"),
            Self::MissingRelation { identity, arm } => {
                write!(f, "material {identity} ({arm:?}) has no declared relation")
            }
            Self::UnknownRelation {
                identity,
                related_to,
            } => write!(f, "material {identity} names unknown relation {related_to}"),
            Self::LineageNotSeparated {
                identity,
                related_to,
            } => write!(
                f,
                "material {identity} is not lineage-separated from {related_to}"
            ),
            Self::SubjectNotDisjoint { identity, subject } => write!(
                f,
                "subject-disjoint control {identity} shares subject {subject}"
            ),
            Self::FoilSubjectMismatch {
                identity,
                related_to,
            } => write!(
                f,
                "matched foil {identity} does not match subject of {related_to}"
            ),
            Self::FoilPopulationMismatch {
                identity,
                related_to,
            } => write!(
                f,
                "matched foil {identity} does not preserve token population of {related_to}"
            ),
            Self::FoilIncidenceUnchanged {
                identity,
                related_to,
            } => write!(
                f,
                "matched foil {identity} does not change order/incidence from {related_to}"
            ),
            Self::UnchangedRelatedMaterial {
                identity,
                related_to,
            } => write!(
                f,
                "material {identity} is byte/transport-identical to {related_to}"
            ),
            Self::CodecVariantNeedsRebase {
                identity,
                related_to,
            } => write!(
                f,
                "codec variant {identity} needs same text or a surface rebase from {related_to}"
            ),
            Self::InvalidSurfaceRebaseIdentity { identity } => write!(
                f,
                "codec variant {identity} has an invalid surface-rebase identity"
            ),
            Self::StructuralOverlapMismatch { identity } => {
                write!(f, "held-out {identity} has incorrect overlap evidence")
            }
            Self::UnexpectedOverlapEvidence { identity } => write!(
                f,
                "non-held-out material {identity} carries structural overlap evidence"
            ),
            Self::IncidenceEvidenceMismatch { identity } => write!(
                f,
                "matched foil {identity} has incorrect incidence evidence"
            ),
            Self::UnexpectedIncidenceEvidence { identity } => {
                write!(f, "non-foil material {identity} carries incidence evidence")
            }
            Self::NoOpCarriesMaterial { identity } => {
                write!(f, "no-op {identity} carries text or token material")
            }
            Self::NoOpRequiresDevelopment { identity } => {
                write!(f, "no-op {identity} must relate to a development material")
            }
            Self::NoOpMaterialMismatch {
                identity,
                related_to,
            } => write!(
                f,
                "no-op {identity} differs from development material {related_to}"
            ),
        }
    }
}

impl std::error::Error for MaterialLineageRefusal {}
