//! W3: cultivate the lifted native rest, seal the actual returned factors, and grade a detached child.

use std::path::{Path, PathBuf};
use std::process::Command;

use holonic_engine::cultivated_rest::{
    AlignedFactor, CultivatedRest, MorphologyPayload, OctaveBoundOrigin,
};
use holonic_engine::embedding_fiber::{AlignedMaterial, ResidentReadout};
use holonic_engine::foreign_codec_rest::ExteriorCodecArtifact;
use holonic_engine::native_rest::MountedNativeRest;
use holonic_engine::resident_section::{ResidentGrain, ResidentSurface, SeriesAperture};
use num_bigint::BigInt;
use num_traits::One;
use num_traits::Zero;
use relational_geometry::Rat;
use serde_json::json;
use sha2::Digest;

#[path = "phoenix/cultivation_material.rs"]
mod cultivation_material;
#[path = "phoenix/native_streamed.rs"]
mod native_streamed;
#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/streamed.rs"]
mod streamed;
#[path = "phoenix/tower.rs"]
mod tower;
#[path = "phoenix/w3_fixture.rs"]
mod w3_fixture;
#[path = "phoenix/w3_grade.rs"]
mod w3_grade;
#[path = "phoenix/w3_seal.rs"]
mod w3_seal;

use cultivation_material::{
    AddSpecialTokens, CodecEquivalenceReceipt, CultivationMaterialManifest, MaterialArm,
    MaterialInput, TokenizedMaterial, admit_tokenized, material_identity, recover_codec_paths,
    tokenized_codec_variant,
};
use native_streamed::NativeMaterialSource;
use streamed::cultivation_overlay::{
    RankDerivationReceipt, SeparatingReceiver, SparseDefect, SupportedFactor,
};

const W1: &str = "output/the_whole_foreign_map_crosses_into_native_rest/gemma_native_rest.bin";
const CODEC: &str = "output/the_whole_foreign_map_crosses_into_native_rest/codec";
const GRAIN: ResidentGrain = ResidentGrain(48);

fn digest_file(path: &Path) -> Result<String, String> {
    Ok(format!(
        "{:x}",
        sha2::Sha256::digest(std::fs::read(path).map_err(|e| e.to_string())?)
    ))
}

fn codec_companions(
    rest: &MountedNativeRest,
) -> Result<(ExteriorCodecArtifact, Vec<(String, PathBuf)>), String> {
    let descriptor = rest
        .codebook()
        .codec
        .as_ref()
        .ok_or("W1 codebook has no codec descriptor")?;
    let json_path = Path::new(CODEC).join(&descriptor.tokenizer_json_sha256);
    let config_path = descriptor
        .tokenizer_config_sha256
        .as_ref()
        .map(|hash| Path::new(CODEC).join(hash));
    let artifact = ExteriorCodecArtifact::from_bytes(
        std::fs::read(&json_path).map_err(|e| e.to_string())?,
        config_path
            .as_ref()
            .map(|p| std::fs::read(p))
            .transpose()
            .map_err(|e| e.to_string())?,
    );
    rest.codebook()
        .validate_with_codec(&artifact)
        .map_err(|e| e.to_string())?;
    let mut paths = vec![(descriptor.tokenizer_json_sha256.clone(), json_path)];
    if let Some(hash) = &descriptor.tokenizer_config_sha256 {
        paths.push((hash.clone(), Path::new(CODEC).join(hash)));
    }
    Ok((artifact, paths))
}

fn token_ids(rest: &MountedNativeRest, ids: &[u32]) -> Result<Vec<u32>, String> {
    ids.iter()
        .map(|id| {
            rest.codebook()
                .native_id(*id)
                .map_err(|e| format!("W1 source token {id}: {e}"))
        })
        .collect()
}

fn material(
    rest: &MountedNativeRest,
    artifact: &ExteriorCodecArtifact,
) -> Result<(CultivationMaterialManifest, CodecEquivalenceReceipt), String> {
    let dev_source_ids = [818, 4187, 563, 506, 9199, 24974];
    let held_source_ids = [1509, 563, 506, 15374, 24974];
    let control_source_ids = [236776, 3761, 5192, 563, 614, 19396, 161544];
    let foil_source_ids = [818, 9199, 4187, 563, 506, 24974];
    let dev_tokens = token_ids(rest, &dev_source_ids)?;
    let held_tokens = token_ids(rest, &held_source_ids)?;
    let control_tokens = token_ids(rest, &control_source_ids)?;
    let foil_tokens = token_ids(rest, &foil_source_ids)?;
    let surface = |tokens: &[u32]| -> Result<&'static str, String> {
        let text = tokens
            .iter()
            .map(|id| rest.codebook().native_surface(*id))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| e.to_string())?
            .concat();
        Ok(Box::leak(text.into_boxed_str()))
    };
    let dev_text = surface(&dev_tokens)?;
    let held_text = surface(&held_tokens)?;
    let control_text = surface(&control_tokens)?;
    let foil_text = surface(&foil_tokens)?;
    let dev = MaterialInput {
        lineage: "canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md:3",
        subject: "subject-development",
        arm: MaterialArm::Development,
        related_to: None,
        surface_rebase_identity: None,
        text: dev_text,
    };
    let dev_identity = material_identity(&dev, &dev_tokens, "w1");
    let held = MaterialInput {
        lineage: "AGENTS.md:161",
        subject: "subject-development",
        arm: MaterialArm::StructuralHeldOut,
        related_to: Some(&dev_identity),
        surface_rebase_identity: None,
        text: held_text,
    };
    let codec = MaterialInput {
        lineage: "canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md:3#pretokenized-codebook",
        subject: "subject-development",
        arm: MaterialArm::CodecVariant,
        related_to: Some(&dev_identity),
        surface_rebase_identity: None,
        text: dev_text,
    };
    let control = MaterialInput {
        lineage: "AGENTS.md:61",
        subject: "subject-control",
        arm: MaterialArm::SubjectDisjointControl,
        related_to: None,
        surface_rebase_identity: None,
        text: control_text,
    };
    let no_op = MaterialInput {
        lineage: "blueprint/THE_ROADMAP.md:329",
        subject: "subject-no-op",
        arm: MaterialArm::NoOp,
        related_to: Some(&dev_identity),
        surface_rebase_identity: None,
        text: dev_text,
    };
    let foil = MaterialInput {
        lineage: "canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md:3#matched-order-control",
        subject: "subject-development",
        arm: MaterialArm::MatchedFoil,
        related_to: Some(&dev_identity),
        surface_rebase_identity: None,
        text: foil_text,
    };
    let codec_receipt = recover_codec_paths(
        rest.codebook(),
        artifact,
        dev_text,
        &dev_source_ids,
        AddSpecialTokens::Disabled,
    )
    .map_err(|e| e.to_string())?;
    let codec_passage =
        tokenized_codec_variant(codec, &codec_receipt).map_err(|e| e.to_string())?;
    let passages = vec![
        TokenizedMaterial {
            input: dev,
            token_ids: dev_tokens.clone(),
            codec_variant: "w1".to_owned(),
        },
        TokenizedMaterial {
            input: held,
            token_ids: held_tokens,
            codec_variant: "w1".to_owned(),
        },
        codec_passage,
        TokenizedMaterial {
            input: control,
            token_ids: control_tokens,
            codec_variant: "w1".to_owned(),
        },
        TokenizedMaterial {
            input: no_op,
            token_ids: dev_tokens,
            codec_variant: "w1".to_owned(),
        },
        TokenizedMaterial {
            input: foil,
            token_ids: foil_tokens,
            codec_variant: "w1".to_owned(),
        },
    ];
    Ok((
        admit_tokenized(rest.codebook(), artifact, passages).map_err(|e| e.to_string())?,
        codec_receipt,
    ))
}

fn codec_receipt_json(receipt: &CodecEquivalenceReceipt) -> serde_json::Value {
    json!({"equivalent": receipt.equivalent, "add_special_tokens": format!("{:?}", receipt.add_special_tokens), "tokenizer_identity": receipt.tokenizer.identity, "pretokenized_identity": receipt.pretokenized.identity, "tokenizer_source_ids": receipt.tokenizer.source_ids, "pretokenized_source_ids": receipt.pretokenized.source_ids, "tokenizer_native_ids": receipt.tokenizer.native_ids, "pretokenized_native_ids": receipt.pretokenized.native_ids})
}

fn base(
    source: &mut NativeMaterialSource,
    surface: &'static ResidentSurface<'static>,
    readout: &'static ResidentReadout,
    tokens: &[u32],
) -> Result<streamed::Circulated, String> {
    streamed::circulate(
        surface,
        readout,
        source,
        &tokens.iter().map(|id| *id as usize).collect::<Vec<_>>(),
        GRAIN,
        SeriesAperture(14),
        tower::Chart::Midpoint,
        true,
        tower::LAYERS,
        false,
    )
}

fn child(
    product_dir: &Path,
    fixture_path: &Path,
    material_path: &Path,
    codec_path: &Path,
    expected_base_digest: &str,
) -> Result<(), String> {
    let fixture = w3_fixture::read(fixture_path)?;
    let manifest: CultivationMaterialManifest =
        serde_json::from_slice(&std::fs::read(material_path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    manifest.validate().map_err(|e| e.to_string())?;
    fixture.validate_against(&manifest)?;
    let codec_record: serde_json::Value =
        serde_json::from_slice(&std::fs::read(codec_path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    let mounted = CultivatedRest::mount_directory(product_dir).map_err(|e| e.to_string())?;
    mounted.verify_still().map_err(|e| e.to_string())?;
    let artifact = mounted
        .exterior_codec_artifact()
        .map_err(|e| e.to_string())?;
    if mounted.product.material_lineage_sha256() != &fixture.material_manifest_sha256 {
        return Err("fixture/material lineage mismatch".to_owned());
    }
    let factor = match mounted
        .product
        .morphology_payload()
        .map_err(|e| e.to_string())?
    {
        MorphologyPayload::AlignedFactor(value) => value,
        _ => return Err("cultivated product did not return aligned factors".to_owned()),
    };
    let (u, v, receipt, derivation) = reconstruct(&factor, &mounted.product)?;
    let product_before = digest_file(&product_dir.join("cultivated.rest"))?;
    let target = receipt.separator.target.0;
    if derivation.target_vocabulary != target || derivation.pair.first != receipt.separator.target.1
    {
        return Err("product derivation target disagrees with rank receipt".to_owned());
    }
    let readout = Box::leak(Box::new(
        ResidentReadout::new().map_err(|e| format!("card: {e:?}"))?,
    ));
    let surface = Box::leak(Box::new(
        ResidentSurface::on(readout).map_err(|e| format!("surface: {e:?}"))?,
    ));
    let mut source = NativeMaterialSource::from_mounted(mounted.predecessor());
    source.rest.verify_still().map_err(|e| e.to_string())?;
    let dev_entry = manifest
        .entries
        .iter()
        .find(|entry| entry.arm == MaterialArm::Development)
        .ok_or("development material absent")?;
    let dev_source_ids: Vec<u32> = dev_entry
        .token_ids
        .iter()
        .map(|id| {
            source
                .rest
                .codebook()
                .source_id(*id)
                .ok_or_else(|| format!("native token {id} has no source address"))
        })
        .collect::<Result<_, _>>()?;
    let dev_text = dev_entry
        .token_ids
        .iter()
        .map(|id| source.rest.codebook().native_surface(*id))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| e.to_string())?
        .concat();
    let actual_codec = recover_codec_paths(
        source.rest.codebook(),
        &artifact,
        &dev_text,
        &dev_source_ids,
        AddSpecialTokens::Disabled,
    )
    .map_err(|e| e.to_string())?;
    let actual_codec_json = codec_receipt_json(&actual_codec);
    for key in [
        "equivalent",
        "tokenizer_identity",
        "pretokenized_identity",
        "tokenizer_source_ids",
        "pretokenized_source_ids",
        "tokenizer_native_ids",
        "pretokenized_native_ids",
    ] {
        if actual_codec_json[key] != codec_record[key] {
            return Err(format!("codec receipt field {key} drifted"));
        }
    }
    if !actual_codec.equivalent {
        return Err("codec paths are not equivalent".to_owned());
    }
    let development_target = w3_fixture::address_for(&fixture, MaterialArm::Development)?
        .target
        .ok_or("development target absent")?;
    for arm in [
        MaterialArm::StructuralHeldOut,
        MaterialArm::CodecVariant,
        MaterialArm::MatchedFoil,
    ] {
        if w3_fixture::address_for(&fixture, arm)?.target != Some(development_target) {
            return Err(format!("{arm:?} target does not match development"));
        }
    }
    let no_op_address = w3_fixture::address_for(&fixture, MaterialArm::NoOp)?;
    let development_address = w3_fixture::address_for(&fixture, MaterialArm::Development)?;
    if no_op_address.prompt != development_address.prompt
        || no_op_address.target != development_address.target
    {
        return Err("no-op address does not equal development address".to_owned());
    }
    let witness = &mounted.morphology;
    let mut cultivated_runs = Vec::new();
    for arm in [
        MaterialArm::Development,
        MaterialArm::StructuralHeldOut,
        MaterialArm::SubjectDisjointControl,
        MaterialArm::MatchedFoil,
    ] {
        let address = w3_fixture::address_for(&fixture, arm)?;
        let candidate = w3_seal::candidate(
            streamed::cultivation_overlay::OverlayShape {
                rows: tower::VOCABULARY,
                input_width: tower::HIDDEN,
            },
            address.prompt.len(),
        );
        let request = streamed::CultivationRequest {
            candidate: &candidate,
            derivation: &receipt,
            u: &u,
            v: &v,
            witness,
            input_bound: rested_bound(&mounted.product, "phoenix.overlay/input")?,
            predecessor_bound: rested_bound(
                &mounted.product,
                "phoenix.overlay/w2-predecessor-output",
            )?,
        };
        let result = streamed::circulate_cultivated(
            surface,
            readout,
            &mut source,
            &address
                .prompt
                .iter()
                .map(|id| *id as usize)
                .collect::<Vec<_>>(),
            GRAIN,
            SeriesAperture(14),
            tower::Chart::Midpoint,
            true,
            &request,
        )?;
        cultivated_runs.push(result);
    }
    let development_cultivated = cultivated_runs
        .first()
        .ok_or("development cultivated return absent")?;
    let base_only = base(
        &mut source,
        surface,
        readout,
        &w3_fixture::address_for(&fixture, MaterialArm::Development)?.prompt,
    )?;
    let base_grade = w3_grade::grade_base_only(&base_only, development_cultivated);
    if !base_grade.complete_equal
        || !base_grade.potential_equal
        || !base_grade.final_normed_equal
        || !base_grade.admission_consequence_equal
        || format!(
            "{:x}",
            sha2::Sha256::digest(
                serde_json::to_vec(&base_only.potential).map_err(|e| e.to_string())?
            )
        ) != expected_base_digest
    {
        return Err(format!(
            "detached base-only return disagrees: {base_grade:?}"
        ));
    }
    let development = w3_grade::from_circulated(cultivated_runs.remove(0));
    let held_out = w3_grade::from_circulated(cultivated_runs.remove(0));
    let control = w3_grade::from_circulated(cultivated_runs.remove(0));
    let foil = w3_grade::from_circulated(cultivated_runs.remove(0));
    source.rest.verify_still().map_err(|e| e.to_string())?;
    mounted.verify_still().map_err(|e| e.to_string())?;
    if source.rest.codebook().codebook_sha256 != fixture.codebook_sha256 {
        return Err("child W1 codebook drifted".to_owned());
    }
    let forbidden_fd = [
        "model.safetensors",
        "modeling_gemma4.py",
        "config.json",
        "tokenizer.json",
        "tokenizer_config.json",
    ];
    for entry in std::fs::read_dir("/proc/self/fd").map_err(|e| e.to_string())? {
        if let Ok(target) = std::fs::read_link(entry.map_err(|e| e.to_string())?.path()) {
            let text = target.to_string_lossy();
            if forbidden_fd.iter().any(|name| text.contains(name)) {
                return Err(format!("source fd leaked: {text}"));
            }
        }
    }
    let codec = w3_fixture::address_for(&fixture, MaterialArm::CodecVariant)?;
    let codec_reused = codec.prompt == development_address.prompt;
    let no_op_base = no_op_address.prompt == development_address.prompt
        && no_op_address.target == development_address.target
        && base_grade.complete_equal;
    let ablation_base = base_grade.complete_equal
        && expected_base_digest == development.base_face_digest
        && mounted.product.ablation_predecessor_identity() == mounted.product.predecessor().clone();
    let product_after = digest_file(&product_dir.join("cultivated.rest"))?;
    let product_stable = product_before == product_after && mounted.verify_still().is_ok();
    let grade = w3_grade::grade(
        &development,
        &held_out,
        &control,
        &foil,
        &receipt,
        target,
        product_stable,
        codec_reused,
        no_op_base,
        ablation_base,
    )?;
    if !grade.passes() {
        return Err(format!("W3 grade failed: {grade:?}"));
    }
    if product_before != product_after {
        return Err("cultivated product changed during child circulation".to_owned());
    }
    let grade_runs = [&development, &held_out, &control, &foil];
    let output = json!({"schema":"holonic-engine.phoenix.w3-receipt.v1","grade":grade,"codec":actual_codec_json,"no_op":"base-only-development-return","ablation":"base-only-development-return","product_sha256":product_after,"development_base_digest":development.base_face_digest,"target":target,"exact_work":grade_runs.iter().map(|run| &run.overlay_work).collect::<Vec<_>>(),"total_work":grade_runs.iter().map(|run| &run.total_work).collect::<Vec<_>>(),"apparatus":grade_runs.iter().map(|run| &run.overlay_apparatus).collect::<Vec<_>>(),"admission_front_reconciliation":grade_runs.iter().map(|run| json!({"admitted":run.admitted,"fronts":run.overlay_front_count,"obstructions":run.overlay_obstruction_count,"refusals":run.overlay_refusal_count,"factor_reconciliation":run.reconciliation,"execution":{"nodes":run.overlay_execution.graph_nodes,"edges":run.overlay_execution.graph_edges,"captured_launches":run.overlay_execution.captured_launches,"graph_execs":run.overlay_execution.graph_execs,"deed_launches":run.overlay_execution.deed_launches,"identity_sha256":run.overlay_execution.identity_sha256}})).collect::<Vec<_>>(),"base_only":base_grade});
    println!("CHILD_RETURN {output}");
    Ok(())
}

fn reconstruct(
    factor: &AlignedFactor,
    product: &CultivatedRest,
) -> Result<
    (
        AlignedMaterial,
        AlignedMaterial,
        RankDerivationReceipt,
        holonic_engine::cultivation_derivation::CultivationDerivation,
    ),
    String,
> {
    if factor.rank != 1
        || factor.rows as usize != tower::VOCABULARY
        || factor.columns as usize != tower::HIDDEN
    {
        return Err("product factor shape drifted".to_owned());
    }
    if factor.resident_grain != w3_seal::GRAIN as u32 {
        return Err("product resident grain drifted".to_owned());
    }
    let derivation: holonic_engine::cultivation_derivation::CultivationDerivation =
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
        return Err("product derivation/adjoint certificate bytes drifted".to_owned());
    }
    let octaves = |entries: &[i64]| {
        entries
            .iter()
            .map(|v| v.unsigned_abs().max(1).ilog2() + 1)
            .max()
            .unwrap_or(0)
    };
    let u = AlignedMaterial {
        entries: factor.left.clone(),
        exponent: factor.left_exponent,
        entry_octaves: octaves(&factor.left),
        negatives: factor.left.iter().filter(|v| **v < 0).count() as u64,
    };
    let v = AlignedMaterial {
        entries: factor.right.clone(),
        exponent: factor.right_exponent,
        entry_octaves: octaves(&factor.right),
        negatives: factor.right.iter().filter(|v| **v < 0).count() as u64,
    };
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
    if rows.len() != 1 || columns.is_empty() || columns.len() > 2 {
        return Err("product factors do not reconstruct the bounded rank-one support".to_owned());
    }
    let scale = |value: i64, exponent: i32| -> Rat {
        let magnitude = if exponent >= 0 {
            Rat::from_integer(BigInt::from(value) * (BigInt::one() << exponent as usize))
        } else {
            Rat::new(BigInt::from(value), BigInt::one() << (-exponent) as usize)
        };
        magnitude
    };
    let left_value = scale(factor.left[rows[0]], factor.left_exponent);
    let right_values = columns
        .iter()
        .map(|i| scale(factor.right[*i], factor.right_exponent))
        .collect::<Vec<_>>();
    let supported = holonic_engine::exact_linear::ExactRatMatrix::new(vec![
        right_values.iter().map(|v| &left_value * v).collect(),
    ])
    .map_err(|e| e.to_string())?;
    let zero = holonic_engine::exact_linear::ExactRatMatrix::zero(1, columns.len())
        .map_err(|e| e.to_string())?;
    let candidate = supported.get(0, 0).map_err(|e| e.to_string())?.clone();
    let receipt = RankDerivationReceipt {
        defect: SparseDefect {
            ambient_rows: tower::VOCABULARY,
            ambient_columns: tower::HIDDEN,
            support_rows: rows.clone(),
            support_columns: columns.clone(),
            supported: supported.clone(),
        },
        left: SupportedFactor {
            ambient: tower::VOCABULARY,
            support: rows.clone(),
            values: vec![left_value],
        },
        right: SupportedFactor {
            ambient: tower::HIDDEN,
            support: columns.clone(),
            values: right_values,
        },
        zero_rank_foil: SparseDefect {
            ambient_rows: tower::VOCABULARY,
            ambient_columns: tower::HIDDEN,
            support_rows: rows.clone(),
            support_columns: columns.clone(),
            supported: zero,
        },
        separator: SeparatingReceiver {
            target: (rows[0], columns[0]),
            predecessor: Rat::zero(),
            candidate,
        },
    };
    let rank_bytes = streamed::cultivation_overlay::canonical_rank_derivation_bytes(&receipt);
    if rank_bytes != product.receipt().rank.bytes
        || streamed::cultivation_overlay::canonical_rank_derivation_digest(&receipt)
            != product.receipt().rank.sha256
    {
        return Err("authenticated rank receipt does not reconstruct".to_owned());
    }
    let (expected_u, expected_v) = w3_seal::materials(&derivation)?;
    if expected_u != u || expected_v != v {
        return Err("product factors disagree with derivation certificate".to_owned());
    }
    Ok((u, v, receipt, derivation))
}

fn rested_bound(product: &CultivatedRest, name: &str) -> Result<u32, String> {
    product
        .ports()
        .iter()
        .find(|p| p.name == name)
        .and_then(|p| match p.octave_bound {
            OctaveBoundOrigin::Rested(value) => u32::try_from(value).ok(),
            _ => None,
        })
        .ok_or_else(|| format!("rested bound {name} absent"))
}

fn parent(out: &Path) -> Result<(), String> {
    std::fs::create_dir_all(out).map_err(|e| e.to_string())?;
    let product_dir = out.join("product");
    std::fs::create_dir_all(&product_dir).map_err(|e| e.to_string())?;
    let base_link = product_dir.join("base.w1.rest");
    if !base_link.exists() {
        std::fs::hard_link(W1, &base_link).map_err(|e| e.to_string())?;
    }
    let rest = MountedNativeRest::open(&base_link).map_err(|e| e.to_string())?;
    let (artifact, companions) = codec_companions(&rest)?;
    let (manifest, codec_receipt) = material(&rest, &artifact)?;
    let fixture = w3_fixture::from_material_manifest(&manifest)?;
    std::fs::write(
        out.join("material_manifest.json"),
        serde_json::to_vec_pretty(&manifest).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    std::fs::write(
        out.join("codec_equivalence.json"),
        serde_json::to_vec_pretty(&codec_receipt_json(&codec_receipt))
            .map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    let fixture_path = out.join("process-addresses.json");
    w3_fixture::write(&fixture_path, &fixture)?;
    let dev = w3_fixture::address_for(&fixture, MaterialArm::Development)?;
    let control = w3_fixture::address_for(&fixture, MaterialArm::SubjectDisjointControl)?;
    let readout = Box::leak(Box::new(
        ResidentReadout::new().map_err(|e| format!("card: {e:?}"))?,
    ));
    let surface = Box::leak(Box::new(
        ResidentSurface::on(readout).map_err(|e| format!("surface: {e:?}"))?,
    ));
    let mut source = NativeMaterialSource::from_mounted(&rest);
    let development = base(&mut source, surface, readout, &dev.prompt)?;
    let control_base = base(&mut source, surface, readout, &control.prompt)?;
    let target = usize::try_from(dev.target.ok_or("development target absent")?)
        .map_err(|e| e.to_string())?;
    let hidden_start_dev = development
        .tokens
        .len()
        .checked_sub(1)
        .ok_or("development hidden row absent")?
        * tower::HIDDEN;
    let hidden_start_control = control_base
        .tokens
        .len()
        .checked_sub(1)
        .ok_or("control hidden row absent")?
        * tower::HIDDEN;
    let potential_start = development
        .tokens
        .len()
        .checked_sub(1)
        .ok_or("development potential row absent")?
        * tower::VOCABULARY;
    let hidden_dev = development
        .final_normed
        .get(hidden_start_dev..hidden_start_dev + tower::HIDDEN)
        .ok_or("development hidden row drifted")?;
    let hidden_control = control_base
        .final_normed
        .get(hidden_start_control..hidden_start_control + tower::HIDDEN)
        .ok_or("control hidden row drifted")?;
    let potential_dev = development
        .potential
        .get(potential_start..potential_start + tower::VOCABULARY)
        .ok_or("development potential row drifted")?;
    let derivation = w3_seal::derive_from_w2(hidden_dev, hidden_control, potential_dev, target)?;
    std::fs::write(
        out.join("derivation.json"),
        serde_json::to_vec_pretty(&derivation).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    drop(source);
    let sealed = w3_seal::seal_product(
        &product_dir,
        &rest,
        &companions,
        &fixture,
        derivation,
        development.final_normed_bound,
        development.potential_bound,
    )?;
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let expected_base_digest = format!(
        "{:x}",
        sha2::Sha256::digest(
            serde_json::to_vec(&development.potential).map_err(|e| e.to_string())?
        )
    );
    let child = Command::new(exe)
        .arg("--child")
        .arg(&product_dir)
        .arg(&fixture_path)
        .arg(out.join("material_manifest.json"))
        .arg(out.join("codec_equivalence.json"))
        .arg(&expected_base_digest)
        .output()
        .map_err(|e| e.to_string())?;
    if !child.status.success() {
        return Err(format!(
            "W3 child failed: {}",
            String::from_utf8_lossy(&child.stderr)
        ));
    }
    let child_stdout = String::from_utf8(child.stdout).map_err(|e| e.to_string())?;
    let child_return = child_stdout
        .lines()
        .find_map(|line| line.strip_prefix("CHILD_RETURN "))
        .ok_or("child returned no receipt")?;
    let receipt: serde_json::Value =
        serde_json::from_str(child_return).map_err(|e| e.to_string())?;
    if receipt["schema"] != "holonic-engine.phoenix.w3-receipt.v1" {
        return Err("child receipt schema drifted".to_owned());
    }
    if receipt["development_base_digest"] != expected_base_digest {
        return Err("detached development base face drifted".to_owned());
    }
    std::fs::write(
        out.join("receipt.json"),
        serde_json::to_vec_pretty(&receipt).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    println!("W3_RECEIPT {receipt}");
    let _ = sealed.product;
    Ok(())
}

fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some("--child") {
        child(
            Path::new(args.get(2).ok_or("--child product")?),
            Path::new(args.get(3).ok_or("--child fixture")?),
            Path::new(args.get(4).ok_or("--child material manifest")?),
            Path::new(args.get(5).ok_or("--child codec receipt")?),
            args.get(6).ok_or("--child expected base digest")?,
        )
    } else {
        parent(Path::new(args.get(1).map(String::as_str).unwrap_or(
            "output/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest",
        )))
    }
}
