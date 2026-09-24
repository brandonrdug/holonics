use super::*;

fn source() -> SourceAssetIdentity {
    SourceAssetIdentity {
        model_sha256: "model".into(),
        tokenizer_sha256: "tokenizer".into(),
        tokenizer_config_sha256: "tokenizer-config".into(),
        config_sha256: "config".into(),
        model_content_sha256: "content".into(),
    }
}

fn coverage() -> CoverageSummary {
    CoverageSummary {
        represented_token_ids: 2,
    }
}

#[test]
fn seals_and_mounts_without_source_access() {
    let rest = ExteriorCodebookRest::seal(
        source(),
        262_144,
        vec![
            CodebookEntry {
                source_id: 818,
                source_piece: "The".into(),
                native_id: 818,
                native_surface: "The".into(),
            },
            CodebookEntry {
                source_id: 5_279,
                source_piece: "▁capital".into(),
                native_id: 5_279,
                native_surface: " capital".into(),
            },
        ],
        coverage(),
        vec![OpenFibre {
            axis: "vocabulary-id".into(),
            extent: 262_144,
            represented: 2,
            reason: "active Station C closure only; remaining source codebook is unread/open"
                .into(),
        }],
    )
    .unwrap();
    let digest = rest.codebook_sha256.clone();
    let mounted = ExteriorCodebookRest::mount(rest).unwrap();
    assert_eq!(mounted.native_surface(5_279).unwrap(), " capital");
    assert_eq!(mounted.source_id(818), Some(818));
    assert_eq!(
        mounted.read_native(7),
        NativeRead::Open {
            native_id: 7,
            extent: 262_144,
            represented: 2
        }
    );
    assert_eq!(mounted.codebook_sha256, digest);
}

#[test]
fn duplicate_or_unrepresented_material_is_refused_by_name() {
    let mut rows = vec![
        CodebookEntry {
            source_id: 1,
            source_piece: "a".into(),
            native_id: 1,
            native_surface: "a".into(),
        },
        CodebookEntry {
            source_id: 1,
            source_piece: "b".into(),
            native_id: 2,
            native_surface: "b".into(),
        },
    ];
    assert!(matches!(
        ExteriorCodebookRest::seal(
            source(),
            4,
            std::mem::take(&mut rows),
            CoverageSummary {
                represented_token_ids: 2,
                ..coverage()
            },
            vec![]
        ),
        Err(RestError::RepeatedSourceId(1))
    ));
    let rest = ExteriorCodebookRest::seal(
        source(),
        4,
        vec![CodebookEntry {
            source_id: 1,
            source_piece: "a".into(),
            native_id: 1,
            native_surface: "a".into(),
        }],
        CoverageSummary {
            represented_token_ids: 1,
            ..coverage()
        },
        vec![OpenFibre {
            axis: "vocabulary-id".into(),
            extent: 4,
            represented: 1,
            reason: "unrepresented vocabulary remains open".into(),
        }],
    )
    .unwrap();
    assert!(matches!(
        rest.native_surface(3),
        Err(RestError::MissingNativeId { .. })
    ));
}

#[test]
fn caller_order_is_part_of_the_seal_and_cannot_be_silently_rewritten() {
    let rows = vec![
        CodebookEntry {
            source_id: 2,
            source_piece: "b".into(),
            native_id: 2,
            native_surface: "b".into(),
        },
        CodebookEntry {
            source_id: 1,
            source_piece: "a".into(),
            native_id: 1,
            native_surface: "a".into(),
        },
    ];
    assert!(matches!(
        ExteriorCodebookRest::seal(
            source(),
            4,
            rows,
            CoverageSummary {
                represented_token_ids: 2,
                ..coverage()
            },
            vec![]
        ),
        Err(RestError::UnsortedEntries)
    ));
}

#[test]
fn arbitrary_native_permutation_has_indexed_lookup() {
    let rest = ExteriorCodebookRest::seal(
        source(),
        3,
        vec![
            CodebookEntry {
                source_id: 0,
                source_piece: "a".into(),
                native_id: 2,
                native_surface: "A".into(),
            },
            CodebookEntry {
                source_id: 1,
                source_piece: "b".into(),
                native_id: 0,
                native_surface: "B".into(),
            },
            CodebookEntry {
                source_id: 2,
                source_piece: "c".into(),
                native_id: 1,
                native_surface: "C".into(),
            },
        ],
        CoverageSummary {
            represented_token_ids: 3,
        },
        vec![],
    )
    .unwrap();
    assert_eq!(rest.native_surface(0).unwrap(), "B");
    assert_eq!(rest.native_surface(1).unwrap(), "C");
    assert_eq!(rest.native_surface(2).unwrap(), "A");
    assert_eq!(rest.source_id(0), Some(1));
    assert_eq!(rest.native_id(0).unwrap(), 2);
    assert_eq!(rest.native_id(1).unwrap(), 0);
    assert_eq!(rest.native_id(2).unwrap(), 1);
    assert_eq!(
        rest.read_source(9),
        SourceRead::Open {
            source_id: 9,
            extent: 3,
            represented: 3
        }
    );
    assert!(matches!(
        rest.native_id(9),
        Err(RestError::MissingSourceId { id: 9, extent: 3 })
    ));
}

#[test]
fn mount_rejects_descriptor_identity_without_companion_bytes() {
    let mut rest = ExteriorCodebookRest::seal(
        source(),
        1,
        vec![CodebookEntry {
            source_id: 0,
            source_piece: "a".into(),
            native_id: 0,
            native_surface: "a".into(),
        }],
        CoverageSummary {
            represented_token_ids: 1,
        },
        vec![],
    )
    .unwrap();
    rest.codec = Some(ExteriorCodecDescriptor {
        tokenizer_json_sha256: "wrong".into(),
        tokenizer_json_len: 1,
        tokenizer_config_sha256: Some(source().tokenizer_config_sha256.clone()),
        tokenizer_config_json_len: Some(1),
    });
    rest.codebook_sha256 = rest.digest();
    assert!(matches!(
        ExteriorCodebookRest::mount(rest),
        Err(RestError::CodecIdentityMismatch {
            kind: "tokenizer",
            ..
        })
    ));
}
