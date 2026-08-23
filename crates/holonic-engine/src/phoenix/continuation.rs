//! An addressed cultivation continuation over one authenticated Phoenix product.
//!
//! W3's cultivated rest is a morphology directly over W1.  A later return has a different
//! predecessor: the complete already-cultivated product.  Flattening both morphologies into a new
//! W3 rest would erase that causal edge and would make targeted ablation fall through to W1 rather
//! than restore the immediate predecessor. This owner carries the missing edge as one exact sparse
//! factor rebase: an addressed emission coordinate and the complete changed receiver-covector
//! support. The hot deed remains the existing resident rank-one overlay.

use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    cultivated_rest::{
        native_morphology_bytes, AlignedFactor, DirectoryCompanion, MorphologyPayload,
        NativeMorphologyInput, PredecessorProductIdentity, RuntimeLawReceipt, TypedLaw,
    },
    embedding_fiber::AlignedMaterial,
    exact_linear::ExactRatMatrix,
    native_occurrence::NativeOccurrence,
    phoenix::streamed::cultivation_overlay::{
        RankDerivationReceipt, SeparatingReceiver, SparseDefect, SupportedFactor,
    },
};

const SCHEMA: &str = "holonic-engine.phoenix.cultivation-continuation.v1";
const DIRECTORY_SCHEMA: &str = "holonic-engine.phoenix.cultivation-continuation-directory.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CultivatedBodyIdentity {
    pub product: PredecessorProductIdentity,
    pub predecessor: PredecessorProductIdentity,
    pub morphology: PredecessorProductIdentity,
    pub codec_companions: Vec<DirectoryCompanion>,
    pub runtime_law_sha256: String,
    pub complete_sha256: String,
}

impl CultivatedBodyIdentity {
    pub fn new(
        product: PredecessorProductIdentity,
        predecessor: PredecessorProductIdentity,
        morphology: PredecessorProductIdentity,
        codec_companions: Vec<DirectoryCompanion>,
        runtime_law: &RuntimeLawReceipt,
    ) -> Result<Self, ContinuationRefusal> {
        let runtime_law_sha256 = digest_json(runtime_law)?;
        let complete_sha256 = digest_json(&(
            &product,
            &predecessor,
            &morphology,
            &codec_companions,
            &runtime_law_sha256,
        ))?;
        let identity = Self {
            product,
            predecessor,
            morphology,
            codec_companions,
            runtime_law_sha256,
            complete_sha256,
        };
        identity.validate()?;
        Ok(identity)
    }

    fn validate(&self) -> Result<(), ContinuationRefusal> {
        for (name, value) in [
            ("product", &self.product.sha256),
            ("predecessor", &self.predecessor.sha256),
            ("morphology", &self.morphology.sha256),
            ("runtime law", &self.runtime_law_sha256),
            ("complete body", &self.complete_sha256),
        ] {
            require_digest(name, value)?;
        }
        let expected = digest_json(&(
            &self.product,
            &self.predecessor,
            &self.morphology,
            &self.codec_companions,
            &self.runtime_law_sha256,
        ))?;
        if expected != self.complete_sha256 {
            return Err(ContinuationRefusal::Identity(
                "complete cultivated predecessor".to_owned(),
            ));
        }
        Ok(())
    }
}

/// Digests only: the exchange occurrence remains exterior material and cannot be looked up from
/// the successor rest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedReturnLineage {
    pub exchange_source_sha256: String,
    pub a2_defect_complex_sha256: String,
    pub a2_fixed_body_sha256: String,
    pub leader_occurrence_sha256: String,
    pub leader_input_sha256: String,
    pub leader_history_sha256: String,
    pub receiver_causal_sha256: String,
    pub tower_admission_sha256: String,
    pub overlay_execution_sha256: String,
}

impl AddressedReturnLineage {
    fn validate(&self) -> Result<(), ContinuationRefusal> {
        for (name, value) in [
            ("exchange source", &self.exchange_source_sha256),
            ("A2 defect complex", &self.a2_defect_complex_sha256),
            ("A2 fixed body", &self.a2_fixed_body_sha256),
            ("leader occurrence", &self.leader_occurrence_sha256),
            ("leader input", &self.leader_input_sha256),
            ("leader history", &self.leader_history_sha256),
            ("receiver causal cut", &self.receiver_causal_sha256),
            ("tower admission", &self.tower_admission_sha256),
            ("overlay execution", &self.overlay_execution_sha256),
        ] {
            require_digest(name, value)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LocalEntryDelta {
    pub coordinate: u32,
    pub predecessor_entry: i64,
    pub delta_entry: i64,
    pub successor_entry: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LocalFactorDelta {
    pub target_row: u32,
    pub predecessor_entry: i64,
    pub delta_entry: i64,
    pub successor_entry: i64,
    pub left_exponent: i32,
    pub right_exponent: i32,
    pub selector_coordinate: u32,
    pub selector_entry: i64,
    pub right_changes: Vec<LocalEntryDelta>,
    pub predecessor_payload_sha256: String,
    pub successor_payload_sha256: String,
    pub predecessor_right_sha256: String,
    pub successor_right_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LocalMetricAdjointReturn {
    pub target_before: (i64, i64),
    pub maximum_other_upper: i64,
    pub activation_enclosure: (i128, i128),
    pub orientation: i8,
    pub receiver_gap: i128,
    pub oriented_activation_lower: i128,
    pub least_lattice_step: i64,
    pub guaranteed_target_lower: i128,
    pub forward_map: ExactRatMatrix,
    pub domain_metric: ExactRatMatrix,
    pub codomain_metric: ExactRatMatrix,
    pub metric_adjoint: ExactRatMatrix,
    pub bare_transpose: ExactRatMatrix,
    pub adjoint_defect: Rat,
    pub bare_transpose_defect: Rat,
}

impl LocalMetricAdjointReturn {
    pub fn derive(
        target_before: (i64, i64),
        maximum_other_upper: i64,
        activation_enclosure: (i128, i128),
    ) -> Result<Self, ContinuationRefusal> {
        if target_before.0 > target_before.1 || activation_enclosure.0 > activation_enclosure.1 {
            return Err(ContinuationRefusal::ForwardInterval);
        }
        let (orientation, oriented_activation_lower) = if activation_enclosure.0 > 0 {
            (1i8, activation_enclosure.0)
        } else if activation_enclosure.1 < 0 {
            (-1i8, -activation_enclosure.1)
        } else {
            return Err(ContinuationRefusal::ForwardDirectionCrossesZero);
        };
        let receiver_gap = i128::from(maximum_other_upper)
            .checked_sub(i128::from(target_before.0))
            .and_then(|gap| gap.checked_add(1))
            .ok_or(ContinuationRefusal::Carrier)?;
        if receiver_gap <= 0 {
            return Err(ContinuationRefusal::AlreadySeparated);
        }
        let magnitude = receiver_gap
            .checked_add(oriented_activation_lower - 1)
            .ok_or(ContinuationRefusal::Carrier)?
            / oriented_activation_lower;
        let magnitude_i64 = i64::try_from(magnitude).map_err(|_| ContinuationRefusal::Carrier)?;
        let least_lattice_step = i64::from(orientation)
            .checked_mul(magnitude_i64)
            .ok_or(ContinuationRefusal::Carrier)?;
        let guaranteed_target_lower = i128::from(target_before.0)
            .checked_add(
                magnitude
                    .checked_mul(oriented_activation_lower)
                    .ok_or(ContinuationRefusal::Carrier)?,
            )
            .ok_or(ContinuationRefusal::Carrier)?;
        if guaranteed_target_lower <= i128::from(maximum_other_upper) {
            return Err(ContinuationRefusal::Separation);
        }

        // The oriented one-coordinate forward map is T=[a].  The receiver metric is one and the
        // domain metric a/q is founded by the least lattice placement q, hence
        // G_X^-1 T^T G_Y=[q].  The bare transpose is returned separately and is not called the
        // adjoint merely because this chart has one coordinate.
        let a = Rat::from_integer(BigInt::from(oriented_activation_lower));
        let q = Rat::from_integer(BigInt::from(magnitude_i64));
        let forward_map = ExactRatMatrix::new(vec![vec![a.clone()]])?;
        let domain_metric = ExactRatMatrix::new(vec![vec![&a / &q]])?;
        let codomain_metric = ExactRatMatrix::identity(1)?;
        let metric_adjoint = forward_map.metric_adjoint(&domain_metric, &codomain_metric)?;
        let bare_transpose = forward_map.transpose()?;
        let unit = [Rat::one()];
        let adjoint_defect = forward_map.adjoint_defect(
            &metric_adjoint,
            &domain_metric,
            &codomain_metric,
            &unit,
            &unit,
        )?;
        let bare_transpose_defect = forward_map.adjoint_defect(
            &bare_transpose,
            &domain_metric,
            &codomain_metric,
            &unit,
            &unit,
        )?;
        if metric_adjoint != ExactRatMatrix::new(vec![vec![q]])? || !adjoint_defect.is_zero() {
            return Err(ContinuationRefusal::Adjoint);
        }
        Ok(Self {
            target_before,
            maximum_other_upper,
            activation_enclosure,
            orientation,
            receiver_gap,
            oriented_activation_lower,
            least_lattice_step,
            guaranteed_target_lower,
            forward_map,
            domain_metric,
            codomain_metric,
            metric_adjoint,
            bare_transpose,
            adjoint_defect,
            bare_transpose_defect,
        })
    }

    fn validate(&self) -> Result<(), ContinuationRefusal> {
        let derived = Self::derive(
            self.target_before,
            self.maximum_other_upper,
            self.activation_enclosure,
        )?;
        if &derived != self {
            return Err(ContinuationRefusal::Adjoint);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReconstructionFibre {
    pub target_row: u32,
    pub predecessor_entry: i64,
    pub successor_entry: i64,
    pub targeted_ablation_restores_predecessor: bool,
    pub every_non_target_left_entry_retained: bool,
    pub every_unlisted_right_entry_retained: bool,
    pub complete_right_difference_returned: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CultivationContinuationRest {
    pub schema: String,
    pub predecessor: CultivatedBodyIdentity,
    pub lineage: AddressedReturnLineage,
    pub local_delta: LocalFactorDelta,
    pub causal_adjoint: LocalMetricAdjointReturn,
    pub reconstruction_fibre: ReconstructionFibre,
    pub successor_morphology: PredecessorProductIdentity,
    pub open_fibres: Vec<String>,
}

impl CultivationContinuationRest {
    #[allow(clippy::too_many_arguments)]
    pub fn seal(
        predecessor: CultivatedBodyIdentity,
        lineage: AddressedReturnLineage,
        base: &AlignedFactor,
        target_row: u32,
        target_before: (i64, i64),
        maximum_other_upper: i64,
        activation_enclosure: (i128, i128),
        selector_coordinate: u32,
        selector_entry: i64,
        successor_morphology: PredecessorProductIdentity,
        open_fibres: Vec<String>,
    ) -> Result<Self, ContinuationRefusal> {
        predecessor.validate()?;
        lineage.validate()?;
        let causal_adjoint = LocalMetricAdjointReturn::derive(
            target_before,
            maximum_other_upper,
            activation_enclosure,
        )?;
        let target = target_row as usize;
        let predecessor_entry = *base
            .left
            .get(target)
            .ok_or(ContinuationRefusal::TargetOutsideFactor(target_row))?;
        let delta_entry = causal_adjoint.least_lattice_step;
        let successor_entry = predecessor_entry
            .checked_add(delta_entry)
            .ok_or(ContinuationRefusal::Carrier)?;
        let predecessor_payload_sha256 = payload_digest(base)?;
        let predecessor_right_sha256 = right_digest(base);
        let successor = selector_successor_factor(
            base,
            target_row,
            delta_entry,
            selector_coordinate,
            selector_entry,
        )?;
        if successor.left[target] != successor_entry {
            return Err(ContinuationRefusal::Reconstruction);
        }
        let mut right_changes = Vec::new();
        for (coordinate, (predecessor, next)) in base.right.iter().zip(&successor.right).enumerate()
        {
            if predecessor != next {
                right_changes.push(LocalEntryDelta {
                    coordinate: coordinate as u32,
                    predecessor_entry: *predecessor,
                    delta_entry: next
                        .checked_sub(*predecessor)
                        .ok_or(ContinuationRefusal::Carrier)?,
                    successor_entry: *next,
                });
            }
        }
        if right_changes.is_empty() {
            return Err(ContinuationRefusal::Reconstruction);
        }
        let successor_payload_sha256 = payload_digest(&successor)?;
        let successor_right_sha256 = right_digest(&successor);
        let rest = Self {
            schema: SCHEMA.to_owned(),
            predecessor,
            lineage,
            local_delta: LocalFactorDelta {
                target_row,
                predecessor_entry,
                delta_entry,
                successor_entry,
                left_exponent: base.left_exponent,
                right_exponent: base.right_exponent,
                selector_coordinate,
                selector_entry,
                right_changes,
                predecessor_payload_sha256,
                successor_payload_sha256,
                predecessor_right_sha256,
                successor_right_sha256,
            },
            causal_adjoint,
            reconstruction_fibre: ReconstructionFibre {
                target_row,
                predecessor_entry,
                successor_entry,
                targeted_ablation_restores_predecessor: true,
                every_non_target_left_entry_retained: true,
                every_unlisted_right_entry_retained: true,
                complete_right_difference_returned: true,
            },
            successor_morphology,
            open_fibres,
        };
        rest.validate(base)?;
        Ok(rest)
    }

    pub fn encode(&self) -> Result<Vec<u8>, ContinuationRefusal> {
        serde_json::to_vec(self).map_err(|error| ContinuationRefusal::Wire(error.to_string()))
    }

    pub fn read(bytes: &[u8], base: &AlignedFactor) -> Result<Self, ContinuationRefusal> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        rest.validate(base)?;
        Ok(rest)
    }

    pub fn successor_factor(
        &self,
        base: &AlignedFactor,
    ) -> Result<AlignedFactor, ContinuationRefusal> {
        self.validate(base)?;
        self.successor_factor_without_validation(base)
    }

    fn validate(&self, base: &AlignedFactor) -> Result<(), ContinuationRefusal> {
        if self.schema != SCHEMA {
            return Err(ContinuationRefusal::Schema(self.schema.clone()));
        }
        self.predecessor.validate()?;
        self.lineage.validate()?;
        self.causal_adjoint.validate()?;
        require_digest("successor morphology", &self.successor_morphology.sha256)?;
        let target = self.local_delta.target_row as usize;
        if base.left.get(target) != Some(&self.local_delta.predecessor_entry)
            || base.left_exponent != self.local_delta.left_exponent
            || base.right_exponent != self.local_delta.right_exponent
            || self.local_delta.delta_entry != self.causal_adjoint.least_lattice_step
            || self
                .local_delta
                .predecessor_entry
                .checked_add(self.local_delta.delta_entry)
                != Some(self.local_delta.successor_entry)
            || payload_digest(base)? != self.local_delta.predecessor_payload_sha256
            || right_digest(base) != self.local_delta.predecessor_right_sha256
            || self.reconstruction_fibre.target_row != self.local_delta.target_row
            || self.reconstruction_fibre.predecessor_entry != self.local_delta.predecessor_entry
            || self.reconstruction_fibre.successor_entry != self.local_delta.successor_entry
            || !self
                .reconstruction_fibre
                .targeted_ablation_restores_predecessor
            || !self
                .reconstruction_fibre
                .every_non_target_left_entry_retained
            || !self
                .reconstruction_fibre
                .every_unlisted_right_entry_retained
            || !self.reconstruction_fibre.complete_right_difference_returned
        {
            return Err(ContinuationRefusal::Reconstruction);
        }
        let successor = self.successor_factor_without_validation(base)?;
        if payload_digest(&successor)? != self.local_delta.successor_payload_sha256 {
            return Err(ContinuationRefusal::Reconstruction);
        }
        if right_digest(&successor) != self.local_delta.successor_right_sha256 {
            return Err(ContinuationRefusal::Reconstruction);
        }
        Ok(())
    }

    fn successor_factor_without_validation(
        &self,
        base: &AlignedFactor,
    ) -> Result<AlignedFactor, ContinuationRefusal> {
        let mut successor = base.clone();
        let entry = successor
            .left
            .get_mut(self.local_delta.target_row as usize)
            .ok_or(ContinuationRefusal::TargetOutsideFactor(
                self.local_delta.target_row,
            ))?;
        *entry = self.local_delta.successor_entry;
        let mut previous = None;
        for change in &self.local_delta.right_changes {
            if previous.is_some_and(|held| held >= change.coordinate)
                || change.predecessor_entry.checked_add(change.delta_entry)
                    != Some(change.successor_entry)
                || base.right.get(change.coordinate as usize) != Some(&change.predecessor_entry)
            {
                return Err(ContinuationRefusal::Reconstruction);
            }
            let right = successor
                .right
                .get_mut(change.coordinate as usize)
                .ok_or(ContinuationRefusal::Reconstruction)?;
            *right = change.successor_entry;
            previous = Some(change.coordinate);
        }
        if successor
            .right
            .get(self.local_delta.selector_coordinate as usize)
            != Some(&self.local_delta.selector_entry)
        {
            return Err(ContinuationRefusal::Reconstruction);
        }
        Ok(successor)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ContinuationDirectoryManifest {
    schema: String,
    rest: String,
    rest_identity: PredecessorProductIdentity,
    morphology: String,
    morphology_identity: PredecessorProductIdentity,
}

#[derive(Debug)]
pub struct MountedContinuation {
    root: PathBuf,
    manifest_identity: PredecessorProductIdentity,
    manifest: ContinuationDirectoryManifest,
    rest: CultivationContinuationRest,
    morphology: NativeOccurrence,
    successor_factor: AlignedFactor,
    rank_receipt: RankDerivationReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ContinuationRuntimeIdentity {
    pub rest: PredecessorProductIdentity,
    pub morphology: PredecessorProductIdentity,
    pub predecessor_complete_sha256: String,
    pub successor_payload_sha256: String,
    pub complete_sha256: String,
}

impl MountedContinuation {
    pub fn open(
        directory: impl AsRef<Path>,
        predecessor: &CultivatedBodyIdentity,
        base: &AlignedFactor,
        runtime_law: &RuntimeLawReceipt,
        laws: &[TypedLaw],
        w1_predecessor: &PredecessorProductIdentity,
    ) -> Result<Self, ContinuationRefusal> {
        let root = std::fs::canonicalize(directory.as_ref())
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        let manifest_path = root.join("manifest.json");
        let manifest_bytes = std::fs::read(&manifest_path)
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        let manifest: ContinuationDirectoryManifest = serde_json::from_slice(&manifest_bytes)
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        if manifest.schema != DIRECTORY_SCHEMA {
            return Err(ContinuationRefusal::Schema(manifest.schema));
        }
        let rest_path = contained(&root, &manifest.rest)?;
        let morphology_path = contained(&root, &manifest.morphology)?;
        let rest_bytes = std::fs::read(&rest_path)
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        if PredecessorProductIdentity::from_bytes(&rest_bytes) != manifest.rest_identity
            || PredecessorProductIdentity::from_path(&morphology_path)
                .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?
                != manifest.morphology_identity
        {
            return Err(ContinuationRefusal::Identity(
                "continuation directory member".to_owned(),
            ));
        }
        let rest = CultivationContinuationRest::read(&rest_bytes, base)?;
        if &rest.predecessor != predecessor
            || rest.successor_morphology != manifest.morphology_identity
        {
            return Err(ContinuationRefusal::Identity(
                "continuation predecessor/successor".to_owned(),
            ));
        }
        let successor_factor = rest.successor_factor(base)?;
        let expected_morphology = native_morphology_bytes(&NativeMorphologyInput {
            left_population: runtime_law.left_population.clone(),
            right_population: runtime_law.right_population.clone(),
            left_shape: vec![
                successor_factor.rows as usize,
                successor_factor.rank as usize,
            ],
            right_shape: vec![
                successor_factor.rank as usize,
                successor_factor.columns as usize,
            ],
            left_exponent: successor_factor.left_exponent,
            right_exponent: successor_factor.right_exponent,
            rank: successor_factor.rank,
            resident_grain: successor_factor.resident_grain,
            predecessor: w1_predecessor.clone(),
            laws: laws.to_vec(),
            left: successor_factor.left.clone(),
            right: successor_factor.right.clone(),
        })
        .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        if PredecessorProductIdentity::from_bytes(&expected_morphology)
            != manifest.morphology_identity
        {
            return Err(ContinuationRefusal::Identity(
                "successor morphology bytes".to_owned(),
            ));
        }
        let morphology = NativeOccurrence::read(
            morphology_path
                .to_str()
                .ok_or_else(|| ContinuationRefusal::Wire("non-unicode path".to_owned()))?,
        )
        .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        let rank_receipt = rank_receipt(&successor_factor)?;
        let mounted = Self {
            root,
            manifest_identity: PredecessorProductIdentity::from_bytes(&manifest_bytes),
            manifest,
            rest,
            morphology,
            successor_factor,
            rank_receipt,
        };
        mounted.verify_still()?;
        Ok(mounted)
    }

    pub fn write_directory(
        directory: impl AsRef<Path>,
        rest: &CultivationContinuationRest,
        morphology_bytes: &[u8],
    ) -> Result<(), ContinuationRefusal> {
        let directory = directory.as_ref();
        std::fs::create_dir_all(directory)
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        let rest_bytes = rest.encode()?;
        let rest_path = directory.join("continuation.rest");
        let morphology_path = directory.join("morphology.safetensors");
        std::fs::write(&rest_path, &rest_bytes)
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        std::fs::write(&morphology_path, morphology_bytes)
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        let manifest = ContinuationDirectoryManifest {
            schema: DIRECTORY_SCHEMA.to_owned(),
            rest: "continuation.rest".to_owned(),
            rest_identity: PredecessorProductIdentity::from_bytes(&rest_bytes),
            morphology: "morphology.safetensors".to_owned(),
            morphology_identity: PredecessorProductIdentity::from_bytes(morphology_bytes),
        };
        if manifest.morphology_identity != rest.successor_morphology {
            return Err(ContinuationRefusal::Identity(
                "successor morphology at write".to_owned(),
            ));
        }
        let manifest_bytes = serde_json::to_vec(&manifest)
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        std::fs::write(directory.join("manifest.json"), manifest_bytes)
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))
    }

    pub fn verify_still(&self) -> Result<(), ContinuationRefusal> {
        let root = std::fs::canonicalize(&self.root)
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        if root != self.root {
            return Err(ContinuationRefusal::Identity(
                "continuation root".to_owned(),
            ));
        }
        let manifest_bytes = std::fs::read(root.join("manifest.json"))
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        if PredecessorProductIdentity::from_bytes(&manifest_bytes) != self.manifest_identity {
            return Err(ContinuationRefusal::Identity(
                "continuation manifest".to_owned(),
            ));
        }
        for (name, declared) in [
            (&self.manifest.rest, &self.manifest.rest_identity),
            (
                &self.manifest.morphology,
                &self.manifest.morphology_identity,
            ),
        ] {
            let path = contained(&root, name)?;
            let actual = PredecessorProductIdentity::from_path(path)
                .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
            if &actual != declared {
                return Err(ContinuationRefusal::Identity(format!(
                    "continuation member {name}"
                )));
            }
        }
        self.morphology
            .container
            .verify_still()
            .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
        Ok(())
    }

    pub fn rest(&self) -> &CultivationContinuationRest {
        &self.rest
    }

    pub fn morphology(&self) -> &NativeOccurrence {
        &self.morphology
    }

    pub fn aligned_left(&self) -> AlignedMaterial {
        aligned(
            &self.successor_factor.left,
            self.successor_factor.left_exponent,
        )
    }

    pub fn aligned_right(&self) -> AlignedMaterial {
        aligned(
            &self.successor_factor.right,
            self.successor_factor.right_exponent,
        )
    }

    pub fn rank_receipt(&self) -> &RankDerivationReceipt {
        &self.rank_receipt
    }

    pub fn runtime_identity(&self) -> Result<ContinuationRuntimeIdentity, ContinuationRefusal> {
        let rest = self.manifest.rest_identity.clone();
        let morphology = self.manifest.morphology_identity.clone();
        let complete_sha256 = digest_json(&(
            &rest,
            &morphology,
            &self.rest.predecessor.complete_sha256,
            &self.rest.local_delta.successor_payload_sha256,
        ))?;
        Ok(ContinuationRuntimeIdentity {
            rest,
            morphology,
            predecessor_complete_sha256: self.rest.predecessor.complete_sha256.clone(),
            successor_payload_sha256: self.rest.local_delta.successor_payload_sha256.clone(),
            complete_sha256,
        })
    }
}

pub fn selector_successor_factor(
    base: &AlignedFactor,
    target_row: u32,
    left_delta: i64,
    selector_coordinate: u32,
    selector_entry: i64,
) -> Result<AlignedFactor, ContinuationRefusal> {
    if base.rank != 1 || selector_entry == 0 {
        return Err(ContinuationRefusal::Rank);
    }
    let target = target_row as usize;
    let coordinate = selector_coordinate as usize;
    let mut successor = base.clone();
    let left = successor
        .left
        .get_mut(target)
        .ok_or(ContinuationRefusal::TargetOutsideFactor(target_row))?;
    *left = left
        .checked_add(left_delta)
        .ok_or(ContinuationRefusal::Carrier)?;
    if coordinate >= successor.right.len() {
        return Err(ContinuationRefusal::SelectorOutsideFactor(
            selector_coordinate,
        ));
    }
    successor.right.fill(0);
    successor.right[coordinate] = selector_entry;
    Ok(successor)
}

pub fn successor_morphology_bytes(
    rest: &CultivationContinuationRest,
    base: &AlignedFactor,
    runtime_law: &RuntimeLawReceipt,
    laws: &[TypedLaw],
    w1_predecessor: &PredecessorProductIdentity,
) -> Result<Vec<u8>, ContinuationRefusal> {
    let factor = rest.successor_factor(base)?;
    native_morphology_bytes(&NativeMorphologyInput {
        left_population: runtime_law.left_population.clone(),
        right_population: runtime_law.right_population.clone(),
        left_shape: vec![factor.rows as usize, factor.rank as usize],
        right_shape: vec![factor.rank as usize, factor.columns as usize],
        left_exponent: factor.left_exponent,
        right_exponent: factor.right_exponent,
        rank: factor.rank,
        resident_grain: factor.resident_grain,
        predecessor: w1_predecessor.clone(),
        laws: laws.to_vec(),
        left: factor.left,
        right: factor.right,
    })
    .map_err(|error| ContinuationRefusal::Wire(error.to_string()))
}

pub fn rank_receipt(factor: &AlignedFactor) -> Result<RankDerivationReceipt, ContinuationRefusal> {
    let rows = factor
        .left
        .iter()
        .enumerate()
        .filter_map(|(index, value)| (*value != 0).then_some(index))
        .collect::<Vec<_>>();
    let columns = factor
        .right
        .iter()
        .enumerate()
        .filter_map(|(index, value)| (*value != 0).then_some(index))
        .collect::<Vec<_>>();
    if rows.is_empty() || columns.is_empty() {
        return Err(ContinuationRefusal::Rank);
    }
    let left_values = rows
        .iter()
        .map(|row| scale(factor.left[*row], factor.left_exponent))
        .collect::<Vec<_>>();
    let right_values = columns
        .iter()
        .map(|column| scale(factor.right[*column], factor.right_exponent))
        .collect::<Vec<_>>();
    let supported = ExactRatMatrix::new(
        left_values
            .iter()
            .map(|left| right_values.iter().map(|right| left * right).collect())
            .collect(),
    )?;
    if supported.rank()? != 1 {
        return Err(ContinuationRefusal::Rank);
    }
    let zero = ExactRatMatrix::zero(rows.len(), columns.len())?;
    let separator_ordinal = supported
        .entries()
        .iter()
        .position(|entry| !entry.is_zero())
        .ok_or(ContinuationRefusal::Rank)?;
    let separator_row = separator_ordinal / columns.len();
    let separator_column = separator_ordinal % columns.len();
    Ok(RankDerivationReceipt {
        defect: SparseDefect {
            ambient_rows: factor.rows as usize,
            ambient_columns: factor.columns as usize,
            support_rows: rows.clone(),
            support_columns: columns.clone(),
            supported: supported.clone(),
        },
        left: SupportedFactor {
            ambient: factor.rows as usize,
            support: rows.clone(),
            values: left_values,
        },
        right: SupportedFactor {
            ambient: factor.columns as usize,
            support: columns.clone(),
            values: right_values,
        },
        zero_rank_foil: SparseDefect {
            ambient_rows: factor.rows as usize,
            ambient_columns: factor.columns as usize,
            support_rows: rows.clone(),
            support_columns: columns.clone(),
            supported: zero,
        },
        separator: SeparatingReceiver {
            target: (rows[separator_row], columns[separator_column]),
            predecessor: Rat::zero(),
            candidate: supported.get(separator_row, separator_column)?.clone(),
        },
    })
}

pub fn aligned(entries: &[i64], exponent: i32) -> AlignedMaterial {
    let entry_octaves = entries
        .iter()
        .map(|value| value.unsigned_abs().max(1).ilog2() + 1)
        .max()
        .unwrap_or(0);
    AlignedMaterial {
        entries: entries.to_vec(),
        exponent,
        entry_octaves,
        negatives: entries.iter().filter(|value| **value < 0).count() as u64,
    }
}

fn payload_digest(factor: &AlignedFactor) -> Result<String, ContinuationRefusal> {
    MorphologyPayload::AlignedFactor(factor.clone())
        .canonical_digest()
        .map_err(|error| ContinuationRefusal::Wire(error.to_string()))
}

fn right_digest(factor: &AlignedFactor) -> String {
    let mut bytes = Vec::with_capacity(4 + factor.right.len() * 8);
    bytes.extend_from_slice(&factor.right_exponent.to_le_bytes());
    for entry in &factor.right {
        bytes.extend_from_slice(&entry.to_le_bytes());
    }
    digest(&bytes)
}

fn scale(value: i64, exponent: i32) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::from(value) * (BigInt::one() << exponent as usize))
    } else {
        Rat::new(BigInt::from(value), BigInt::one() << (-exponent) as usize)
    }
}

fn contained(root: &Path, relative: &str) -> Result<PathBuf, ContinuationRefusal> {
    let path = Path::new(relative);
    if path.is_absolute()
        || path
            .components()
            .any(|component| matches!(component, std::path::Component::ParentDir))
    {
        return Err(ContinuationRefusal::DirectoryEscape(relative.to_owned()));
    }
    let candidate = std::fs::canonicalize(root.join(path))
        .map_err(|error| ContinuationRefusal::Wire(error.to_string()))?;
    if !candidate.starts_with(root) {
        return Err(ContinuationRefusal::DirectoryEscape(relative.to_owned()));
    }
    Ok(candidate)
}

fn digest_json(value: &impl Serialize) -> Result<String, ContinuationRefusal> {
    serde_json::to_vec(value)
        .map(|bytes| digest(&bytes))
        .map_err(|error| ContinuationRefusal::Wire(error.to_string()))
}

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn require_digest(name: &str, value: &str) -> Result<(), ContinuationRefusal> {
    if value.len() == 64 && value.bytes().all(|octet| octet.is_ascii_hexdigit()) {
        Ok(())
    } else {
        Err(ContinuationRefusal::Identity(name.to_owned()))
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ContinuationRefusal {
    #[error("continuation wire refused: {0}")]
    Wire(String),
    #[error("unknown cultivation-continuation schema {0}")]
    Schema(String),
    #[error("invalid continuation identity: {0}")]
    Identity(String),
    #[error("the target row {0} lies outside the inherited left factor")]
    TargetOutsideFactor(u32),
    #[error("the selector coordinate {0} lies outside the inherited right factor")]
    SelectorOutsideFactor(u32),
    #[error("the forward interval is malformed")]
    ForwardInterval,
    #[error("the inherited forward direction crosses zero")]
    ForwardDirectionCrossesZero,
    #[error("the development receiver was already separated")]
    AlreadySeparated,
    #[error("the exact continuation left the integer carrier")]
    Carrier,
    #[error("the least lattice step did not separate the development receiver")]
    Separation,
    #[error("the metric-adjoint receipt does not reconstruct")]
    Adjoint,
    #[error("the local reconstruction fibre does not restore the predecessor")]
    Reconstruction,
    #[error("the successor morphology is not rank one")]
    Rank,
    #[error("the continuation directory escaped through {0}")]
    DirectoryEscape(String),
    #[error("exact local linear algebra refused: {0}")]
    ExactLinear(String),
}

impl From<crate::exact_linear::ExactLinearError> for ContinuationRefusal {
    fn from(error: crate::exact_linear::ExactLinearError) -> Self {
        Self::ExactLinear(error.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn identity(seed: u8) -> PredecessorProductIdentity {
        PredecessorProductIdentity {
            sha256: digest(&[seed]),
            extent: 1,
        }
    }

    fn body() -> CultivatedBodyIdentity {
        CultivatedBodyIdentity::new(
            identity(1),
            identity(2),
            identity(3),
            Vec::new(),
            &RuntimeLawReceipt {
                schema: "holonic-engine.phoenix.runtime-law.v1".to_owned(),
                grain: 48,
                series_aperture: 1,
                band_terms: 1,
                vocabulary_extent: 4,
                hidden_extent: 2,
                rank: 1,
                left_population: "left".to_owned(),
                right_population: "right".to_owned(),
                chart: crate::cultivated_rest::RuntimeChart::Midpoint,
                fuse: true,
                add_special_tokens: false,
            },
        )
        .expect("body")
    }

    fn lineage() -> AddressedReturnLineage {
        let value = digest(b"lineage");
        AddressedReturnLineage {
            exchange_source_sha256: value.clone(),
            a2_defect_complex_sha256: value.clone(),
            a2_fixed_body_sha256: value.clone(),
            leader_occurrence_sha256: value.clone(),
            leader_input_sha256: value.clone(),
            leader_history_sha256: value.clone(),
            receiver_causal_sha256: value.clone(),
            tower_admission_sha256: value.clone(),
            overlay_execution_sha256: value,
        }
    }

    fn factor() -> AlignedFactor {
        AlignedFactor {
            rows: 4,
            columns: 2,
            rank: 1,
            resident_grain: 48,
            left_exponent: 0,
            right_exponent: -1,
            entry_octets: 8,
            left: vec![0, 1, 0, 0],
            right: vec![2, -1],
        }
    }

    #[test]
    fn the_least_metric_return_changes_one_row_and_ablation_recovers_it() {
        let base = factor();
        let successor_factor = {
            let mut successor = base.clone();
            successor.left[3] = 4;
            successor.right[1] = 0;
            successor
        };
        let morphology = identity(9);
        let rest = CultivationContinuationRest::seal(
            body(),
            lineage(),
            &base,
            3,
            (-10, -9),
            5,
            (5, 6),
            0,
            2,
            morphology,
            vec!["held-out successors remain an open fibre".to_owned()],
        )
        .expect("continuation");
        assert_eq!(rest.local_delta.delta_entry, 4);
        assert_eq!(
            rest.successor_factor(&base).expect("factor"),
            successor_factor
        );
        assert_eq!(
            rest.causal_adjoint.metric_adjoint.entries(),
            &[Rat::from_integer(4.into())]
        );
        assert!(!rest.causal_adjoint.bare_transpose_defect.is_zero());
        assert_eq!(
            CultivationContinuationRest::read(&rest.encode().expect("bytes"), &base)
                .expect("remount"),
            rest
        );
        assert_eq!(base.left[3], rest.reconstruction_fibre.predecessor_entry);
        assert_eq!(
            rank_receipt(&successor_factor)
                .expect("rank")
                .defect
                .support_rows,
            vec![1, 3]
        );
    }
}
