//! Source-detached cultivated-product runtime.
//!
//! This is the application-facing composition of the authenticated product directory, its
//! addressed W1 predecessor, the recovered exterior codec and the resident W3 tail. It owns no
//! model semantics: the tower/overlay owners conduct the card deed and return their exact receipts.

use std::path::Path;

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::cultivated_rest::{
    CultivatedRest, DirectoryCompanion, MorphologyPayload, OctaveBoundOrigin,
    PredecessorProductIdentity, RuntimeChart, RuntimeLawReceipt,
};
use crate::cultivation_derivation::CultivationDerivation;
use crate::embedding_fiber::{AlignedMaterial, ResidentReadout};
use crate::exact_work::ExactWork;
use crate::front_passage::{ApparatusPrediction, DeedAdmission};
use crate::phoenix::native_streamed::NativeMaterialSource;
use crate::phoenix::streamed::streamed_cultivation::{ExecutionReceipt, OverlayExecutionIdentity};
use crate::phoenix::streamed::{self, CultivatedCirculated, MaterialSource};
use crate::phoenix::tower;
use crate::resident_section::{ResidentGrain, ResidentSurface, SeriesAperture};
use crate::streamed_standing::StreamedCensus;

/// The source-detached runtime's returned semantic face and its complete resident receipt.
pub struct RuntimeReturn {
    pub cultivated: CultivatedCirculated,
    pub receipt: RuntimeReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceAccessAudit {
    pub product_root: String,
    pub descriptors: Vec<String>,
    pub forbidden: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RuntimeInputReceipt {
    pub text_sha256: String,
    pub text_octets: u64,
    pub native_ids: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GeneratedCandidate {
    pub native_id: u32,
    pub surface: String,
    pub lower: i64,
    pub upper: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GeneratedFuture {
    pub terminal_position: usize,
    pub row_count: usize,
    pub vocabulary_extent: usize,
    pub grain: u32,
    pub top_lower: i64,
    pub plural: Vec<GeneratedCandidate>,
    pub separated: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RuntimeReceipt {
    pub schema: &'static str,
    pub product_identity: PredecessorProductIdentity,
    pub predecessor_identity: PredecessorProductIdentity,
    pub morphology_identity: PredecessorProductIdentity,
    pub codec_companion_identities: Vec<DirectoryCompanion>,
    pub runtime_law: RuntimeLawReceipt,
    pub frozen_members_verified: bool,
    pub source_access: SourceAccessAudit,
    pub input: RuntimeInputReceipt,
    pub generated: GeneratedFuture,
    pub reconstruction_identity: String,
    pub codec_identity: String,
    pub total_work: ExactWork,
    pub overlay_work: ExactWork,
    pub admission: DeedAdmission,
    pub apparatus_prediction: ApparatusPrediction,
    pub overlay_execution: OverlayExecutionIdentity,
    pub execution: ExecutionReceipt,
    pub streamed: StreamedCensus,
}

fn source_access_audit(product_root: &Path) -> SourceAccessAudit {
    let mut descriptors = Vec::new();
    if let Ok(entries) = std::fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = std::fs::read_link(entry.path()) {
                descriptors.push(target.to_string_lossy().into_owned());
            }
        }
    }
    descriptors.sort();
    descriptors.dedup();
    let forbidden_needles = [
        "/canon/",
        "/research/",
        "/blueprint/",
        "/examples/",
        "model.safetensors",
        "modeling_gemma4.py",
        "gemma",
        ".gguf",
    ];
    let forbidden = descriptors
        .iter()
        .filter(|target| {
            let lowered = target.to_ascii_lowercase();
            forbidden_needles
                .iter()
                .any(|needle| lowered.contains(needle))
        })
        .cloned()
        .collect();
    SourceAccessAudit {
        product_root: product_root.display().to_string(),
        descriptors,
        forbidden,
    }
}

fn scale(value: i64, exponent: i32) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::from(value) * (BigInt::one() << exponent as usize))
    } else {
        Rat::new(BigInt::from(value), BigInt::one() << (-exponent) as usize)
    }
}

fn factor_runtime(
    product: &CultivatedRest,
    runtime_law: &RuntimeLawReceipt,
) -> Result<
    (
        AlignedMaterial,
        AlignedMaterial,
        streamed::cultivation_overlay::RankDerivationReceipt,
        CultivationDerivation,
    ),
    String,
> {
    let factor = match product.morphology_payload().map_err(|e| e.to_string())? {
        MorphologyPayload::AlignedFactor(value) => value,
        MorphologyPayload::SparseDelta(_) => {
            return Err("cultivated product has no resident factor".to_owned());
        }
    };
    if factor.rank != runtime_law.rank
        || factor.rows != runtime_law.vocabulary_extent
        || factor.columns != runtime_law.hidden_extent
        || factor.resident_grain == 0
        || factor.resident_grain != runtime_law.grain
    {
        return Err(
            "cultivated factor shape/grain is not the admitted W3 resident morphology".to_owned(),
        );
    }
    let derivation: CultivationDerivation =
        serde_json::from_slice(product.receipt().derivation.canonical_bytes())
            .map_err(|e| format!("derivation certificate: {e}"))?;
    if derivation
        .canonical_receipt_bytes()
        .map_err(|e| e.to_string())?
        != product.receipt().derivation.canonical_bytes()
        || derivation
            .canonical_adjoint_bytes()
            .map_err(|e| e.to_string())?
            != product.receipt().adjoint.canonical_bytes()
    {
        return Err("product derivation/adjoint certificate drifted".to_owned());
    }
    let rows: Vec<usize> = factor
        .left
        .iter()
        .enumerate()
        .filter_map(|(i, v)| (*v != 0).then_some(i))
        .collect();
    let columns: Vec<usize> = factor
        .right
        .iter()
        .enumerate()
        .filter_map(|(i, v)| (*v != 0).then_some(i))
        .collect();
    if rows.len() != 1
        || columns.is_empty()
        || columns.len() > 2
        || rows[0] != derivation.target_vocabulary
    {
        return Err("product factor support does not reconstruct its derivation".to_owned());
    }
    let left_value = scale(factor.left[rows[0]], factor.left_exponent);
    let right_values: Vec<Rat> = columns
        .iter()
        .map(|i| scale(factor.right[*i], factor.right_exponent))
        .collect();
    let supported = crate::exact_linear::ExactRatMatrix::new(vec![
        right_values.iter().map(|v| &left_value * v).collect(),
    ])
    .map_err(|e| e.to_string())?;
    let zero =
        crate::exact_linear::ExactRatMatrix::zero(1, columns.len()).map_err(|e| e.to_string())?;
    let receipt = streamed::cultivation_overlay::RankDerivationReceipt {
        defect: streamed::cultivation_overlay::SparseDefect {
            ambient_rows: runtime_law.vocabulary_extent as usize,
            ambient_columns: runtime_law.hidden_extent as usize,
            support_rows: rows.clone(),
            support_columns: columns.clone(),
            supported: supported.clone(),
        },
        left: streamed::cultivation_overlay::SupportedFactor {
            ambient: runtime_law.vocabulary_extent as usize,
            support: rows.clone(),
            values: vec![left_value],
        },
        right: streamed::cultivation_overlay::SupportedFactor {
            ambient: runtime_law.hidden_extent as usize,
            support: columns.clone(),
            values: right_values,
        },
        zero_rank_foil: streamed::cultivation_overlay::SparseDefect {
            ambient_rows: runtime_law.vocabulary_extent as usize,
            ambient_columns: runtime_law.hidden_extent as usize,
            support_rows: rows.clone(),
            support_columns: columns.clone(),
            supported: zero,
        },
        separator: streamed::cultivation_overlay::SeparatingReceiver {
            target: (rows[0], columns[0]),
            predecessor: Rat::zero(),
            candidate: supported.get(0, 0).map_err(|e| e.to_string())?.clone(),
        },
    };
    if streamed::cultivation_overlay::canonical_rank_derivation_bytes(&receipt)
        != product.receipt().rank.bytes()
        || streamed::cultivation_overlay::canonical_rank_derivation_digest(&receipt)
            != product.receipt().rank.sha256
    {
        return Err("authenticated rank/reconstruction identity does not reconstruct".to_owned());
    }
    let octaves = |entries: &[i64]| {
        entries
            .iter()
            .map(|v| v.unsigned_abs().max(1).ilog2() + 1)
            .max()
            .unwrap_or(0)
    };
    let left = factor.left;
    let right = factor.right;
    let u = AlignedMaterial {
        entries: left.clone(),
        exponent: factor.left_exponent,
        entry_octaves: octaves(&left),
        negatives: left.iter().filter(|v| **v < 0).count() as u64,
    };
    let v = AlignedMaterial {
        entries: right.clone(),
        exponent: factor.right_exponent,
        entry_octaves: octaves(&right),
        negatives: right.iter().filter(|v| **v < 0).count() as u64,
    };
    Ok((u, v, receipt, derivation))
}

fn rested_bound(product: &CultivatedRest, name: &str) -> Result<u32, String> {
    product
        .ports()
        .iter()
        .find(|port| port.name == name)
        .and_then(|port| match port.octave_bound {
            OctaveBoundOrigin::Rested(value) => u32::try_from(value).ok(),
            _ => None,
        })
        .ok_or_else(|| format!("rested bound {name} absent"))
}

fn testimony(
    left_population: &str,
    right_population: &str,
    vocabulary_extent: usize,
    hidden_extent: usize,
) -> streamed::cultivation_overlay::OverlayTestimony {
    use crate::ported_operation::SourceTestimony;
    let statement = |value: &str| {
        vec![SourceTestimony::AuthoritativeDescription {
            statement: value.to_owned(),
        }]
    };
    let mut left = statement(left_population);
    left.push(SourceTestimony::DeclaredShape {
        population: left_population.to_owned(),
        shape: vec![vocabulary_extent, 1],
    });
    let mut right = statement(right_population);
    right.push(SourceTestimony::DeclaredShape {
        population: right_population.to_owned(),
        shape: vec![1, hidden_extent],
    });
    streamed::cultivation_overlay::OverlayTestimony {
        input: statement("phoenix.overlay.standing.input"),
        predecessor: statement("phoenix.overlay.standing.predecessor"),
        terminal_withdraw: vec![SourceTestimony::Intervention {
            statement: "withdraw rows [0, terminal)".to_owned(),
        }],
        v: right,
        u: left,
        re_entry: statement("phoenix.overlay.re-entry"),
    }
}

fn terminal_plural(
    face: &[(i64, i64)],
    vocabulary: usize,
) -> Result<(usize, i64, Vec<(usize, (i64, i64))>), String> {
    if vocabulary == 0 || face.is_empty() || face.len() % vocabulary != 0 {
        return Err(
            "cultivated terminal face is not row-addressable by the admitted vocabulary".to_owned(),
        );
    }
    let rows = face.len() / vocabulary;
    let terminal = &face[(rows - 1) * vocabulary..];
    let top_lower = terminal
        .iter()
        .map(|(lower, _)| *lower)
        .max()
        .ok_or("cultivated terminal face is empty")?;
    let selected = terminal
        .iter()
        .enumerate()
        .filter_map(|(native_id, point)| (point.1 >= top_lower).then_some((native_id, *point)))
        .collect();
    Ok((rows, top_lower, selected))
}

/// Mount one authenticated product directory and conduct one unseen text on the resident card.
pub fn infer(product_directory: impl AsRef<Path>, text: &str) -> Result<RuntimeReturn, String> {
    let product_directory = product_directory.as_ref();
    let product_root = std::fs::canonicalize(product_directory)
        .map_err(|error| format!("product directory {}: {error}", product_directory.display()))?;
    let mounted =
        crate::cultivated_rest::mount_directory(product_directory).map_err(|e| e.to_string())?;
    mounted.verify_still().map_err(|e| e.to_string())?;
    let product_identity = mounted.product_identity().clone();
    let predecessor_identity = mounted.predecessor_identity().clone();
    let morphology_identity = mounted.morphology_identity().clone();
    let codec_companion_identities = mounted.codec_companion_identities().to_vec();
    let artifact = mounted
        .exterior_codec_artifact()
        .map_err(|e| e.to_string())?;
    let runtime_law = mounted.product.runtime_law().clone();
    if runtime_law.schema != "holonic-engine.phoenix.runtime-law.v1"
        || runtime_law.series_aperture == 0
        || runtime_law.band_terms == 0
        || runtime_law.rank != 1
    {
        return Err("cultivated product runtime-law receipt is invalid".to_owned());
    }
    let vocabulary_extent = runtime_law.vocabulary_extent as usize;
    let hidden_extent = runtime_law.hidden_extent as usize;
    // This compiled owner is the first Gemma instance. The product supplies the extents; this
    // check says explicitly whether this binary is the owner capable of conducting them.
    if vocabulary_extent != tower::VOCABULARY || hidden_extent != tower::HIDDEN {
        return Err(format!(
            "rested runtime extents [{vocabulary_extent},{hidden_extent}] do not match this compiled Phoenix instance [{},{}]",
            tower::VOCABULARY,
            tower::HIDDEN,
        ));
    }
    let morphology = mounted
        .product
        .native_morphology()
        .ok_or("cultivated product lacks authenticated native morphology")?;
    if morphology.predecessor_sha256 != mounted.predecessor_identity().sha256
        || morphology.left_shape != vec![vocabulary_extent, runtime_law.rank as usize]
        || morphology.right_shape != vec![runtime_law.rank as usize, hidden_extent]
        || morphology.rank != runtime_law.rank
        || morphology.left_population != runtime_law.left_population
        || morphology.right_population != runtime_law.right_population
        || mounted.predecessor().codebook().vocabulary_extent as usize != vocabulary_extent
    {
        return Err("cultivated morphology/population binding does not match the authenticated W1 predecessor".to_owned());
    }
    let chart = match runtime_law.chart {
        RuntimeChart::Midpoint => tower::Chart::Midpoint,
        RuntimeChart::Interval => tower::Chart::Interval,
    };
    let native_ids = mounted
        .predecessor()
        .codebook()
        .encode_text(&artifact, text, runtime_law.add_special_tokens)
        .map_err(|e| e.to_string())?;
    if native_ids.is_empty() {
        return Err("authenticated codec returned no runtime tokens".to_owned());
    }
    let (u, v, derivation_receipt, _derivation) = factor_runtime(&mounted.product, &runtime_law)?;
    let candidate = streamed::cultivation_overlay::RankOneCandidate::new(
        morphology.left_population.clone(),
        morphology.right_population.clone(),
        streamed::cultivation_overlay::OverlayShape {
            rows: vocabulary_extent,
            input_width: hidden_extent,
        },
        native_ids.len(),
        testimony(
            &morphology.left_population,
            &morphology.right_population,
            vocabulary_extent,
            hidden_extent,
        ),
    );
    let readout = ResidentReadout::new().map_err(|e| format!("resident card: {e:?}"))?;
    let surface = ResidentSurface::on(&readout).map_err(|e| format!("resident surface: {e:?}"))?;
    let witness = &mounted.morphology;
    let mut source = NativeMaterialSource::from_mounted(mounted.predecessor());
    let request = streamed::CultivationRequest {
        candidate: &candidate,
        derivation: &derivation_receipt,
        u: &u,
        v: &v,
        witness,
        input_bound: rested_bound(&mounted.product, "phoenix.overlay/input")?,
        predecessor_bound: rested_bound(&mounted.product, "phoenix.overlay/w2-predecessor-output")?,
        band_terms: runtime_law.band_terms as usize,
    };
    let cultivated = streamed::circulate_cultivated(
        &surface,
        &readout,
        &mut source,
        &native_ids.iter().map(|id| *id as usize).collect::<Vec<_>>(),
        ResidentGrain(runtime_law.grain),
        SeriesAperture(runtime_law.series_aperture),
        chart,
        runtime_law.fuse,
        &request,
    )?;
    source.verify_stable()?;
    mounted.verify_still().map_err(|e| e.to_string())?;
    let frozen_identity_equal = product_identity == *mounted.product_identity()
        && predecessor_identity == *mounted.predecessor_identity()
        && morphology_identity == *mounted.morphology_identity()
        && codec_companion_identities == mounted.codec_companion_identities();
    let source_access = source_access_audit(&product_root);
    let (terminal_rows, top_lower, selected) =
        terminal_plural(&cultivated.cultivated_potential, vocabulary_extent)?;
    let plural = selected
        .iter()
        .map(|(native_id, face)| {
            mounted
                .predecessor()
                .codebook()
                .native_surface(*native_id as u32)
                .map(|surface| GeneratedCandidate {
                    native_id: *native_id as u32,
                    surface: surface.to_owned(),
                    lower: face.0,
                    upper: face.1,
                })
                .map_err(|error| error.to_string())
        })
        .collect::<Result<Vec<_>, _>>()?;
    if !frozen_identity_equal {
        return Err(
            "product/predecessor/morphology/codec identity moved under resident deed".to_owned(),
        );
    }
    if !source_access.forbidden.is_empty() {
        return Err(format!(
            "source-access audit found forbidden targets: {:?}",
            source_access.forbidden
        ));
    }
    let reconstruction_identity =
        streamed::cultivation_overlay::canonical_rank_derivation_digest(&derivation_receipt);
    let codec_identity = artifact.descriptor().tokenizer_json_sha256;
    let runtime_grain = runtime_law.grain;
    let receipt = RuntimeReceipt {
        schema: "holonic-engine.phoenix.runtime-return.v1",
        product_identity,
        predecessor_identity,
        morphology_identity,
        codec_companion_identities,
        runtime_law,
        frozen_members_verified: frozen_identity_equal,
        source_access,
        input: RuntimeInputReceipt {
            text_sha256: format!("{:x}", Sha256::digest(text.as_bytes())),
            text_octets: text.len() as u64,
            native_ids,
        },
        generated: GeneratedFuture {
            terminal_position: terminal_rows - 1,
            row_count: terminal_rows,
            vocabulary_extent,
            grain: runtime_grain,
            top_lower,
            plural,
            separated: vocabulary_extent - selected.len(),
        },
        reconstruction_identity,
        codec_identity,
        total_work: cultivated.total_work.clone(),
        overlay_work: cultivated.overlay_work.clone(),
        admission: cultivated.overlay_admission.clone(),
        apparatus_prediction: cultivated.overlay_apparatus.clone(),
        overlay_execution: cultivated.overlay_execution.clone(),
        execution: cultivated.execution.clone(),
        streamed: cultivated.base.streamed.clone(),
    };
    Ok(RuntimeReturn {
        cultivated,
        receipt,
    })
}

#[cfg(test)]
mod tests {
    use super::terminal_plural;

    #[test]
    fn multi_token_face_reads_only_the_terminal_row() {
        let face = vec![(100, 101), (90, 99), (5, 9), (10, 70), (20, 70), (70, 80)];
        let (rows, top, selected) = terminal_plural(&face, 3).expect("two token rows");
        assert_eq!(rows, 2);
        assert_eq!(top, 70);
        assert_eq!(selected, vec![(0, (10, 70)), (1, (20, 70)), (2, (70, 80))]);
    }
}
