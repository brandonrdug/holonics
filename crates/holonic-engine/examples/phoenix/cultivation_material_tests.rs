use super::*;
use holonic_engine::foreign_codec_rest::{
    CodebookEntry, CoverageSummary, ExteriorCodebookRest, ExteriorCodecArtifact,
    SourceAssetIdentity,
};
use sha2::Digest;

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", sha2::Sha256::digest(bytes))
}

fn fixture() -> (ExteriorCodebookRest, ExteriorCodecArtifact) {
    let tokenizer = br#"{"version":"1.0","truncation":null,"padding":null,"added_tokens":[],"normalizer":null,"pre_tokenizer":{"type":"Whitespace"},"post_processor":null,"decoder":null,"model":{"type":"WordLevel","vocab":{"[UNK]":0,"alpha":1,"held":2,"out":3,"variant":4,"control":5,"foil":6},"unk_token":"[UNK]"}}"#.to_vec();
    let config = br#"{"add_bos_token":false}"#.to_vec();
    let artifact = ExteriorCodecArtifact::from_bytes(tokenizer.clone(), Some(config.clone()));
    let source = SourceAssetIdentity {
        model_sha256: "model".to_owned(),
        tokenizer_sha256: digest(&tokenizer),
        tokenizer_config_sha256: digest(&config),
        config_sha256: "config".to_owned(),
        model_content_sha256: "model-content".to_owned(),
    };
    let entries = (0..8)
        .map(|id| CodebookEntry {
            source_id: id,
            source_piece: format!("piece-{id}"),
            native_id: id,
            native_surface: format!("surface-{id}"),
        })
        .collect();
    let rest = ExteriorCodebookRest::seal_with_codec(
        source,
        8,
        entries,
        CoverageSummary {
            represented_token_ids: 8,
        },
        Vec::new(),
        Some(ExteriorCodecArtifact::from_bytes(
            tokenizer.clone(),
            Some(config.clone()),
        )),
    )
    .expect("fixture W1 rest");
    (rest, artifact)
}

fn inputs() -> Vec<TokenizedMaterial<'static>> {
    let development = MaterialInput {
        lineage: "repo/development/a",
        subject: "subject-a",
        arm: MaterialArm::Development,
        related_to: None,
        surface_rebase_identity: None,
        text: "alpha",
    };
    let development_id: &'static str =
        Box::leak(material_identity(&development, &[1, 2], "w1").into_boxed_str());
    let rebase_identity: &'static str = Box::leak(
        surface_rebase_identity(development_id, &digest(b"alpha"), &digest(b"alpha-variant"))
            .into_boxed_str(),
    );
    let held_out = MaterialInput {
        lineage: "repo/held-out/a",
        subject: "subject-a",
        arm: MaterialArm::StructuralHeldOut,
        related_to: Some(&development_id),
        surface_rebase_identity: None,
        text: "alpha-held-out",
    };
    let codec_variant = MaterialInput {
        lineage: "repo/codec-variant/a",
        subject: "subject-a",
        arm: MaterialArm::CodecVariant,
        related_to: Some(&development_id),
        surface_rebase_identity: Some(rebase_identity),
        text: "alpha-variant",
    };
    let subject_control = MaterialInput {
        lineage: "repo/control/z",
        subject: "subject-z",
        arm: MaterialArm::SubjectDisjointControl,
        related_to: None,
        surface_rebase_identity: None,
        text: "control",
    };
    let no_op = MaterialInput {
        lineage: "repo/no-op",
        subject: "no-op",
        arm: MaterialArm::NoOp,
        related_to: Some(&development_id),
        surface_rebase_identity: None,
        text: "alpha",
    };
    let foil = MaterialInput {
        lineage: "repo/foil/a",
        subject: "subject-a",
        arm: MaterialArm::MatchedFoil,
        related_to: Some(&development_id),
        surface_rebase_identity: None,
        text: "alpha-foil",
    };
    vec![
        TokenizedMaterial {
            input: development,
            token_ids: vec![1, 2],
            codec_variant: "w1".to_owned(),
        },
        TokenizedMaterial {
            input: held_out,
            token_ids: vec![1, 3],
            codec_variant: "w1".to_owned(),
        },
        TokenizedMaterial {
            input: codec_variant,
            token_ids: vec![3],
            codec_variant: "variant".to_owned(),
        },
        TokenizedMaterial {
            input: subject_control,
            token_ids: vec![4],
            codec_variant: "w1".to_owned(),
        },
        TokenizedMaterial {
            input: no_op,
            token_ids: vec![1, 2],
            codec_variant: "w1".to_owned(),
        },
        TokenizedMaterial {
            input: foil,
            token_ids: vec![2, 1],
            codec_variant: "w1".to_owned(),
        },
    ]
}

#[test]
fn manifest_is_content_addressed_and_preserves_all_cohort_arms() {
    let (codebook, artifact) = fixture();
    let manifest = admit_tokenized(&codebook, &artifact, inputs()).expect("admit fixture");
    assert_eq!(manifest.entries.len(), 6);
    assert_eq!(manifest.identities(MaterialArm::Development).count(), 1);
    assert_eq!(
        manifest.identities(MaterialArm::StructuralHeldOut).count(),
        1
    );
    assert_eq!(manifest.identities(MaterialArm::CodecVariant).count(), 1);
    assert_eq!(
        manifest
            .identities(MaterialArm::SubjectDisjointControl)
            .count(),
        1
    );
    assert_eq!(manifest.identities(MaterialArm::NoOp).count(), 1);
    assert_eq!(manifest.identities(MaterialArm::MatchedFoil).count(), 1);
    let overlap = manifest
        .identities(MaterialArm::StructuralHeldOut)
        .next()
        .and_then(|entry| entry.structural_overlap.as_ref())
        .expect("held-out overlap evidence");
    assert_eq!(overlap.length, 1);
    assert_eq!(overlap.development_start, 0);
    assert_eq!(overlap.held_out_start, 0);
    assert_eq!(overlap.token_ids, vec![1]);
    let foil = manifest
        .identities(MaterialArm::MatchedFoil)
        .next()
        .expect("foil identity");
    assert_eq!(
        foil.incidence_change
            .as_ref()
            .expect("foil incidence evidence")
            .changed_positions,
        vec![0, 1]
    );
    manifest.validate().expect("manifest validates");
    let second = admit_tokenized(&codebook, &artifact, inputs()).expect("repeat admission");
    assert_eq!(manifest, second);
    assert_eq!(manifest.manifest_sha256.len(), 64);
}

#[test]
fn text_seam_reports_external_codec_failure_without_fabricating_tokens() {
    struct RefusingCodec;
    impl ExteriorTextCodec for RefusingCodec {
        fn variant_identity(&self) -> &str {
            "refusing"
        }

        fn encode(&self, _: &str) -> Result<Vec<u32>, String> {
            Err("external process unavailable".to_owned())
        }
    }
    let (codebook, artifact) = fixture();
    let input = [MaterialInput {
        lineage: "repo/development/a",
        subject: "subject-a",
        arm: MaterialArm::Development,
        related_to: None,
        surface_rebase_identity: None,
        text: "alpha",
    }];
    assert!(matches!(
        admit_text(&codebook, &artifact, &RefusingCodec, &input),
        Err(MaterialLineageRefusal::Codec { .. })
    ));
}

#[test]
fn open_w1_address_and_subject_overlap_are_refused() {
    let (codebook, artifact) = fixture();
    let mut passages = inputs();
    passages[0].token_ids = vec![7];
    passages[1].token_ids = vec![8];
    assert!(matches!(
        admit_tokenized(&codebook, &artifact, passages),
        Err(MaterialLineageRefusal::TokenOutOfRange { token: 8, .. })
    ));

    let mut passages = inputs();
    passages[3].input.subject = "subject-a";
    assert!(matches!(
        admit_tokenized(&codebook, &artifact, passages),
        Err(MaterialLineageRefusal::SubjectNotDisjoint { .. })
    ));
}

#[test]
fn related_held_out_cannot_be_a_renamed_replay() {
    let (codebook, artifact) = fixture();
    let mut passages = inputs();
    passages[1].input.text = "alpha";
    passages[1].token_ids = vec![1, 2];
    assert!(matches!(
        admit_tokenized(&codebook, &artifact, passages),
        Err(MaterialLineageRefusal::UnchangedRelatedMaterial { .. })
    ));
}

#[test]
fn arbitrary_codec_variant_text_requires_a_surface_rebase() {
    let (codebook, artifact) = fixture();
    let mut passages = inputs();
    passages[2].input.surface_rebase_identity = None;
    assert!(matches!(
        admit_tokenized(&codebook, &artifact, passages),
        Err(MaterialLineageRefusal::CodecVariantNeedsRebase { .. })
    ));
}

#[test]
fn unmatched_foil_population_is_refused() {
    let (codebook, artifact) = fixture();
    let mut passages = inputs();
    passages[5].token_ids = vec![1, 3];
    assert!(matches!(
        admit_tokenized(&codebook, &artifact, passages),
        Err(MaterialLineageRefusal::FoilPopulationMismatch { .. })
    ));
}

#[test]
fn no_op_is_same_material_with_distinct_lineage_and_no_return() {
    let (codebook, artifact) = fixture();
    let manifest = admit_tokenized(&codebook, &artifact, inputs()).expect("admit fixture");
    let no_op = manifest
        .identities(MaterialArm::NoOp)
        .next()
        .expect("no-op");
    let development = manifest
        .identities(MaterialArm::Development)
        .next()
        .expect("development");
    assert_eq!(
        no_op.related_to.as_deref(),
        Some(development.identity.as_str())
    );
    assert_eq!(no_op.text_sha256, development.text_sha256);
    assert_eq!(no_op.token_ids, development.token_ids);
    assert_eq!(no_op.codec_variant, development.codec_variant);
    assert_ne!(no_op.lineage, development.lineage);
}

#[test]
fn codec_variant_receives_both_exterior_paths() {
    let (codebook, artifact) = fixture();
    let receipt = recover_codec_paths(
        &codebook,
        &artifact,
        "alpha",
        &[1],
        AddSpecialTokens::Disabled,
    )
    .expect("codec paths");
    assert_eq!(receipt.tokenizer.path, CodecPath::TokenizerJson);
    assert_eq!(
        receipt.pretokenized.path,
        CodecPath::PretokenizedCodebookSurface
    );
    assert_eq!(receipt.tokenizer.source_ids, vec![1]);
    assert_eq!(receipt.tokenizer.native_ids, vec![1]);
    assert_eq!(receipt.pretokenized.native_ids, vec![1]);
    assert!(receipt.equivalent);
    assert_ne!(receipt.tokenizer.identity, receipt.pretokenized.identity);
}

#[test]
fn unsupported_codec_bytes_are_refused() {
    let (codebook, _) = fixture();
    let artifact = ExteriorCodecArtifact::from_bytes(br#"{"not":"a tokenizer"}"#.to_vec(), None);
    assert!(matches!(
        tokenizer_json_path(&codebook, &artifact, "alpha", AddSpecialTokens::Disabled),
        Err(CodecPathRefusal::UnsupportedCodec(_))
    ));
}
