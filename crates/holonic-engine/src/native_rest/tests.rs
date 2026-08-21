#[cfg(test)]
pub(crate) mod tests {
    use super::super::*;
    use crate::ported_operation::{
        CandidateDiagrams, OperationSpecies, PortedOperationComplex, SourceTestimony,
    };
    use crate::source_occurrence::{
        AssetDeclaration, AuthenticatedContainer, AuthenticatedText, OccurrenceWitness,
        RegionIdentity, SourceOccurrence,
    };
    use sha2::{Digest, Sha256};
    use std::collections::BTreeMap;
    use std::io::Cursor;

    pub(crate) fn fixture() -> NativeRestInput {
        let tokenizer_json = br#"{"model":"tiny"}"#.to_vec();
        let tokenizer_config_json = br#"{"tiny":true}"#.to_vec();
        let digest = |bytes: &[u8]| format!("{:x}", Sha256::digest(bytes));
        let mut complex = PortedOperationComplex::new("gemma-shaped fixture");
        let input = complex.port("input");
        let output = complex.port("output");
        complex
            .bind_operation(
                "foreign law",
                OperationSpecies::Transport,
                vec![input],
                vec![output],
                Some("layer.weight".to_owned()),
                vec![SourceTestimony::Implementation {
                    locator: "/original/modeling_gemma4.py".to_owned(),
                    symbol: "Attention.forward (return self.weight)".to_owned(),
                }],
            )
            .unwrap();
        let region = RegionIdentity {
            population: "layer.weight".to_owned(),
            dtype: "BF16".to_owned(),
            shape: vec![2, 2],
            start: 0,
            end: 8,
            sha256: Some(
                "8a851ff82ee7048ad09ec3847f1ddf44944104d2cbd17ef4e3db22c6785a0d45".to_owned(),
            ),
        };
        let source = SourceOccurrence {
            implementation: AuthenticatedText::of_text(
                "/original/modeling_gemma4.py",
                "class Attention:\n  def forward(self):\n    return self.weight\n",
                None,
            ),
            configuration: AuthenticatedText::of_text("/original/config.json", "{}", None),
            configuration_scope: Vec::new(),
            container: AuthenticatedContainer {
                locator: "/original/model.safetensors".to_owned(),
                octets: 8,
                header_octets: 0,
                header_sha256: "header".to_owned(),
                content_sha256: Some("content".to_owned()),
                regions: BTreeMap::from([(region.population.clone(), region.clone())]),
                identity: None,
            },
            assets: vec![AssetDeclaration {
                role: "tokenizer".to_owned(),
                locator: "/original/tokenizer.json".to_owned(),
                sha256: Some("asset-hash".to_owned()),
                used: true,
            }],
        };
        let graph = crate::operation_correspondence::NativeGraphIdentity::derived_with_topology(
            1,
            0,
            "cooperative",
            vec!["reduce-0".to_owned()],
            vec!["foreign law".to_owned()],
            vec!["input->output".to_owned()],
        );
        NativeRestInput {
            topology: vec![complex],
            source,
            populations: vec![NativePopulation::exact(
                region,
                vec![0, 1, 2, 3, 4, 5, 6, 7],
            )],
            laws: vec![NativeLawIdentity {
                law: "foreign law".to_owned(),
                species: OperationSpecies::Transport,
                owner: "resident-law.foreign".to_owned(),
                graph_identity: graph.key.clone(),
            }],
            tilings: vec![NativeOwnerIdentity {
                owner: "section_partition".to_owned(),
                identity: "tile-0".to_owned(),
            }],
            reductions: vec![NativeOwnerIdentity {
                owner: "reduction_junction".to_owned(),
                identity: "reduce-0".to_owned(),
            }],
            correspondence: crate::operation_correspondence::OperationCorrespondenceSeal::new(
                vec![],
                vec![],
                vec!["layer.weight".to_owned()],
                vec![crate::operation_correspondence::PopulationCorrespondence {
                    source_population: "layer.weight".to_owned(),
                    resolution: crate::operation_correspondence::PopulationResolution::Native {
                        native_population: "layer.weight".to_owned(),
                    },
                }],
                vec![graph],
            )
            .seal()
            .unwrap(),
            codebook: crate::foreign_codec_rest::ExteriorCodebookRest::seal_with_codec(
                crate::foreign_codec_rest::SourceAssetIdentity {
                    model_sha256: "model".into(),
                    tokenizer_sha256: digest(&tokenizer_json),
                    tokenizer_config_sha256: digest(&tokenizer_config_json),
                    config_sha256: "config".into(),
                    model_content_sha256: "content".into(),
                },
                1,
                vec![],
                crate::foreign_codec_rest::CoverageSummary {
                    represented_token_ids: 0,
                },
                vec![crate::foreign_codec_rest::OpenFibre {
                    axis: "vocabulary-id".to_owned(),
                    extent: 1,
                    represented: 0,
                    reason: "fixture leaves the vocabulary remainder open".to_owned(),
                }],
                Some(
                    crate::foreign_codec_rest::ExteriorCodecArtifact::from_bytes(
                        tokenizer_json,
                        Some(tokenizer_config_json),
                    ),
                ),
            )
            .unwrap(),
        }
    }

    pub(crate) fn fixture_bytes() -> Vec<u8> {
        NativeRest::seal(fixture())
            .unwrap()
            .encode_native_bytes()
            .unwrap()
    }

    #[test]
    fn seal_round_trip_is_byte_exact_and_drops_source_paths() {
        let rest = NativeRest::seal(fixture()).unwrap();
        let bytes = rest.encode_native_bytes().unwrap();
        assert!(!String::from_utf8_lossy(&bytes).contains("modeling_gemma4.py"));
        assert!(!String::from_utf8_lossy(&bytes).contains("model.safetensors"));
        let mounted = NativeRest::read(&bytes).unwrap();
        assert_eq!(bytes, mounted.encode_native_bytes().unwrap());
        assert_eq!(mounted.populations()[0].source.shape, vec![2, 2]);
        assert_eq!(mounted.topology().shape, rest.topology().shape);
    }

    #[test]
    fn every_source_region_must_cross_exactly_or_as_a_fibre() {
        let mut input = fixture();
        let unmounted = RegionIdentity {
            population: "unmounted".to_owned(),
            dtype: "BF16".to_owned(),
            shape: vec![1],
            start: 8,
            end: 10,
            sha256: None,
        };
        input
            .source
            .container
            .regions
            .insert("unmounted".to_owned(), unmounted.clone());
        let refusal = NativeRest::seal(input).unwrap_err();
        assert!(
            matches!(refusal, NativeRestRefusal::ActivePopulationMissing { population } if population == "unmounted")
        );
    }

    #[test]
    fn streamed_seal_refuses_duplicate_population_instead_of_overwriting() {
        let mut input = fixture();
        let duplicate_source = input.populations[0].source.clone();
        input.populations.push(NativePopulation::exact(
            duplicate_source,
            vec![0, 1, 2, 3, 4, 5, 6, 7],
        ));
        let mut wire = Cursor::new(Vec::new());
        assert!(matches!(
            NativeRest::seal_streamed(input, &mut wire),
            Err(NativeRestRefusal::DuplicatePopulation { population })
                if population == "layer.weight"
        ));
        assert!(wire.into_inner().is_empty());
    }

    #[test]
    fn exact_population_digest_is_authenticated_before_seal() {
        let mut input = fixture();
        input.populations[0].payload = NativePopulationPayload::Exact {
            bytes: vec![0, 1, 2, 3, 4, 5, 6, 9],
        };
        assert!(matches!(
            NativeRest::seal(input),
            Err(NativeRestRefusal::PopulationDigest { population, .. })
                if population == "layer.weight"
        ));
    }

    #[test]
    fn remount_refuses_a_gap_between_exact_payload_regions() {
        let rest = NativeRest::seal(fixture()).unwrap();
        let mut bytes = rest.encode_native_bytes().unwrap();
        let marker = b"\"start\":0";
        let start = bytes
            .windows(marker.len())
            .rposition(|window| window == marker)
            .expect("exact descriptor start");
        bytes[start + marker.len() - 1] = b'1';
        assert!(NativeRest::read(&bytes).is_err());
    }

    #[test]
    fn manifest_metadata_tamper_is_refused_before_json_payload_validation() {
        let rest = NativeRest::seal(fixture()).unwrap();
        let mut bytes = rest.encode_native_bytes().unwrap();
        let manifest_start = NATIVE_REST_PREFIX.len() + 8 + MANIFEST_DIGEST_OCTETS;
        let marker = b"\"BF16\"";
        let position = bytes[manifest_start..]
            .windows(marker.len())
            .position(|window| window == marker)
            .expect("dtype metadata");
        bytes[manifest_start + position + 1..manifest_start + position + marker.len() - 1]
            .copy_from_slice(b"I8__");
        assert!(matches!(
            NativeRest::read(&bytes),
            Err(NativeRestRefusal::ManifestDigest { .. })
        ));
        let mut cursor = Cursor::new(bytes);
        assert!(matches!(
            NativeRest::read_from(&mut cursor),
            Err(NativeRestRefusal::ManifestDigest { .. })
        ));
    }

    #[test]
    fn mounted_open_refuses_source_identity_hash_tamper() {
        let rest = NativeRest::seal(fixture()).unwrap();
        let mut bytes = rest.encode_native_bytes().unwrap();
        let manifest_start = NATIVE_REST_PREFIX.len() + 8 + MANIFEST_DIGEST_OCTETS;
        let marker = b"\"container_content_sha256\":\"content\"";
        let position = bytes[manifest_start..]
            .windows(marker.len())
            .position(|window| window == marker)
            .expect("source container content identity");
        let replacement = b"\"container_content_sha256\":\"tamper!\"";
        assert_eq!(replacement.len(), marker.len());
        bytes[manifest_start + position..manifest_start + position + marker.len()]
            .copy_from_slice(replacement);
        let path = std::env::temp_dir().join(format!(
            "native-rest-source-identity-tamper-{}.rest",
            std::process::id()
        ));
        std::fs::write(&path, bytes).unwrap();
        assert!(matches!(
            MountedNativeRest::open(&path),
            Err(NativeRestRefusal::ManifestDigest { .. })
        ));
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn source_locator_relocation_preserves_native_rest_bytes() {
        let original = NativeRest::seal(fixture())
            .unwrap()
            .encode_native_bytes()
            .unwrap();
        let mut relocated = fixture();
        relocated.source.implementation.locator = "/relocated/code.py".to_owned();
        relocated.source.configuration.locator = "/relocated/config.json".to_owned();
        relocated.source.container.locator = "/relocated/model.safetensors".to_owned();
        relocated.source.assets[0].locator = "/relocated/tokenizer.json".to_owned();
        let moved = NativeRest::seal(relocated)
            .unwrap()
            .encode_native_bytes()
            .unwrap();
        assert_eq!(original, moved);
        assert!(!String::from_utf8_lossy(&moved).contains("/relocated/"));
    }

    #[test]
    fn remount_requires_the_complete_correspondence_population_closure() {
        let mut input = fixture();
        input
            .correspondence
            .source_populations
            .push("deleted-non-carrier".to_owned());
        input.correspondence.populations.push(
            crate::operation_correspondence::PopulationCorrespondence {
                source_population: "deleted-non-carrier".to_owned(),
                resolution: crate::operation_correspondence::PopulationResolution::Open(
                    crate::operation_correspondence::OpenRemainder {
                        name: "deleted-non-carrier".to_owned(),
                        reason: "fixture omission".to_owned(),
                        reopening: "admit the region".to_owned(),
                    },
                ),
            },
        );
        assert!(matches!(
            NativeRest::seal(input),
            Err(NativeRestRefusal::CorrespondencePopulationMismatch { population })
                if population == "deleted-non-carrier"
        ));
    }

    #[test]
    fn concrete_topology_instances_remain_separate_on_the_wire() {
        let mut input = fixture();
        let mut second = input.topology[0].clone();
        second.name = "second concrete deed".to_owned();
        input.topology.push(second);
        let rest = NativeRest::seal(input).unwrap();
        assert_eq!(rest.topologies().len(), 2);
        assert_ne!(rest.topologies()[0].identity, rest.topologies()[1].identity);
        let remounted = NativeRest::read(&rest.encode_native_bytes().unwrap()).unwrap();
        assert_eq!(remounted.topologies().len(), 2);
    }

    #[test]
    fn open_population_retains_the_complete_fibre() {
        let mut input = fixture();
        let region = input.populations.remove(0).source;
        input.populations.push(NativePopulation::open(
            region,
            CandidateDiagrams {
                question: "decode".to_owned(),
                candidates: vec!["a".to_owned(), "b".to_owned()],
                would_be_decided_by: vec!["source-detached receiver".to_owned()],
            },
        ));
        let rest = NativeRest::seal(input).unwrap();
        assert!(matches!(
            rest.populations()[0].payload,
            NativePayloadDescriptor::Open { .. }
        ));
    }

    #[test]
    fn streamed_external_seal_does_not_retain_the_source_locator_or_payload_form() {
        let path = std::env::temp_dir().join(format!(
            "native-rest-source-stream-{}.bin",
            std::process::id()
        ));
        let mut source_bytes = vec![0u8; 8];
        source_bytes.extend_from_slice(&[0, 1, 2, 3, 4, 5, 6, 7]);
        std::fs::write(&path, source_bytes).unwrap();
        let mut input = fixture();
        input.populations[0].payload = NativePopulationPayload::External {
            locator: path.to_string_lossy().into_owned(),
        };
        let mut wire = Cursor::new(Vec::new());
        NativeRest::seal_streamed(input, &mut wire).unwrap();
        let wire_bytes = wire.into_inner();
        let mounted = NativeRest::read(&wire_bytes).unwrap();
        assert!(
            mounted.population_bytes(&mounted.populations()[0].source.population)
                == Some(&[0, 1, 2, 3, 4, 5, 6, 7][..])
        );
        assert!(!String::from_utf8_lossy(&wire_bytes).contains(path.to_string_lossy().as_ref()));
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn file_backed_remount_hashes_manifest_payload_and_reads_one_named_region() {
        let source_path = std::env::temp_dir().join(format!(
            "native-rest-source-file-{}.bin",
            std::process::id()
        ));
        let rest_path =
            std::env::temp_dir().join(format!("native-rest-mounted-{}.rest", std::process::id()));
        let mut source_bytes = vec![0u8; 8];
        source_bytes.extend_from_slice(&[0, 1, 2, 3, 4, 5, 6, 7]);
        std::fs::write(&source_path, source_bytes).unwrap();
        let mut input = fixture();
        input.populations[0].payload = NativePopulationPayload::External {
            locator: source_path.to_string_lossy().into_owned(),
        };
        let mut output = std::fs::File::create(&rest_path).unwrap();
        NativeRest::seal_streamed(input, &mut output).unwrap();
        drop(output);
        let mounted = MountedNativeRest::open(&rest_path).unwrap();
        let whole = std::fs::read(&rest_path).unwrap();
        assert_eq!(mounted.content_identity().extent, whole.len() as u64);
        assert_eq!(mounted.content_identity().sha256, format!("{:x}", Sha256::digest(&whole)));
        assert!(mounted.total_file_octets() > mounted.payload_offset());
        let extent = mounted.population_extent("layer.weight").unwrap();
        assert_eq!(extent.start, mounted.payload_offset());
        assert_eq!(extent.end - extent.start, 8);
        assert_eq!(extent.shape, vec![2, 2]);
        assert_eq!(extent.dtype, "BF16");
        let mut handle = mounted.open_file().unwrap();
        use std::io::Seek;
        handle.seek(std::io::SeekFrom::Start(extent.start)).unwrap();
        let mut region = Vec::new();
        mounted
            .read_population_to("layer.weight", &mut region)
            .unwrap();
        assert_eq!(region, vec![0, 1, 2, 3, 4, 5, 6, 7]);
        std::fs::remove_file(source_path).unwrap();
        std::fs::remove_file(rest_path).unwrap();
    }

    #[test]
    fn mounted_witness_accepts_locator_rebase_but_refuses_foreign_topologies() {
        let path =
            std::env::temp_dir().join(format!("native-rest-witness-{}.rest", std::process::id()));
        let input = fixture();
        let mut output = std::fs::File::create(&path).unwrap();
        NativeRest::seal_streamed(input, &mut output).unwrap();
        drop(output);
        let mounted = MountedNativeRest::open(&path).unwrap();
        let mut relocated = fixture().topology.remove(0);
        if let SourceTestimony::Implementation { locator, .. } =
            &mut relocated.operations.values_mut().next().unwrap().testimony[0]
        {
            *locator = "/a/different/apparatus/path.py".to_owned();
        }
        let validated = mounted.validate(&relocated).unwrap();
        assert_eq!(validated.len(), 1);

        for mutate in [
            |complex: &mut PortedOperationComplex| {
                if let SourceTestimony::Implementation { symbol, .. } =
                    &mut complex.operations.values_mut().next().unwrap().testimony[0]
                {
                    *symbol = "Foreign.forward".to_owned();
                }
            },
            |complex: &mut PortedOperationComplex| {
                complex
                    .operations
                    .values_mut()
                    .next()
                    .unwrap()
                    .testimony
                    .push(SourceTestimony::Configuration {
                        field: "hidden_size".to_owned(),
                        value: "2560".to_owned(),
                    });
            },
            |complex: &mut PortedOperationComplex| {
                if let SourceTestimony::Implementation { symbol, .. } =
                    &mut complex.operations.values_mut().next().unwrap().testimony[0]
                {
                    *symbol = "Attention.forward (changed)".to_owned();
                }
            },
            |complex: &mut PortedOperationComplex| {
                complex.operations.values_mut().next().unwrap().carrier =
                    Some("foreign.carrier".to_owned());
            },
            |complex: &mut PortedOperationComplex| complex.name = "different topology".to_owned(),
        ] {
            let mut changed = fixture().topology.remove(0);
            mutate(&mut changed);
            assert!(mounted.validate(&changed).is_err());
        }
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn mounted_witness_accepts_canonical_bf16_spellings() {
        let path = std::env::temp_dir().join(format!(
            "native-rest-witness-bf16-{}.rest",
            std::process::id()
        ));
        let mut input = fixture();
        input.populations[0].source.dtype = "Bf16".to_owned();
        input
            .source
            .container
            .regions
            .get_mut("layer.weight")
            .unwrap()
            .dtype = "Bf16".to_owned();
        let complex = input.topology[0].clone();
        let mut output = std::fs::File::create(&path).unwrap();
        NativeRest::seal_streamed(input, &mut output).unwrap();
        drop(output);
        let mounted = MountedNativeRest::open(&path).unwrap();
        assert!(mounted.validate(&complex).is_ok());
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn interval_source_accepts_midpoint_quotient_extension_but_not_fake_source_or_carrier() {
        let path = std::env::temp_dir().join(format!(
            "native-rest-witness-midpoint-{}.rest",
            std::process::id()
        ));
        let input = fixture();
        let source = input.topology[0].clone();
        let mut output = std::fs::File::create(&path).unwrap();
        NativeRest::seal_streamed(input, &mut output).unwrap();
        drop(output);
        let mounted = MountedNativeRest::open(&path).unwrap();

        let mut midpoint = source.clone();
        let input_port = *midpoint.shape.boundaries.objects.keys().next().unwrap();
        let output_port = *midpoint
            .shape
            .boundaries
            .objects
            .keys()
            .next_back()
            .unwrap();
        midpoint
            .bind_operation(
                "midpoint quotient",
                OperationSpecies::Quotient,
                vec![input_port],
                vec![output_port],
                None,
                vec![SourceTestimony::Intervention {
                    statement: "the interval remainder is sealed at its midpoint".to_owned(),
                }],
            )
            .unwrap();
        let validation = mounted.validate(&midpoint).unwrap();
        assert!(validation.iter().any(|entry| {
            entry.operation == "midpoint quotient"
                && entry.interventions == vec!["the interval remainder is sealed at its midpoint"]
        }));

        let mut fake_source = source.clone();
        fake_source
            .bind_operation(
                "fake source operation",
                OperationSpecies::Transport,
                vec![input_port],
                vec![output_port],
                None,
                vec![SourceTestimony::Implementation {
                    locator: "/foreign.py".to_owned(),
                    symbol: "Fake.forward".to_owned(),
                }],
            )
            .unwrap();
        assert!(matches!(
            mounted.validate(&fake_source),
            Err(crate::source_occurrence::SourceRefusal::OperationForeign { operation })
                if operation == "fake source operation"
        ));

        let mut carrier_intervention = source;
        carrier_intervention
            .bind_operation(
                "carrier midpoint quotient",
                OperationSpecies::Quotient,
                vec![input_port],
                vec![output_port],
                Some("layer.weight".to_owned()),
                vec![SourceTestimony::Intervention {
                    statement: "carrier-bearing intervention is forbidden".to_owned(),
                }],
            )
            .unwrap();
        assert!(matches!(
            mounted.validate(&carrier_intervention),
            Err(crate::source_occurrence::SourceRefusal::OperationForeign { operation })
                if operation == "carrier midpoint quotient"
        ));
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn stored_source_may_be_replaced_only_by_its_typed_intervention_name() {
        let path = std::env::temp_dir().join(format!(
            "native-rest-witness-replacement-{}.rest",
            std::process::id()
        ));
        let input = fixture();
        let source = input.topology[0].clone();
        let source_law = *source.operations.keys().next().unwrap();
        let source_name = source.shape.laws.get(&source_law).unwrap().name.clone();
        let input_port = *source.shape.boundaries.objects.keys().next().unwrap();
        let output_port = *source.shape.boundaries.objects.keys().next_back().unwrap();
        let mut output = std::fs::File::create(&path).unwrap();
        NativeRest::seal_streamed(input, &mut output).unwrap();
        drop(output);
        let mounted = MountedNativeRest::open(&path).unwrap();

        let mut replacement = source.clone();
        replacement.operations.remove(&source_law);
        replacement
            .bind_operation(
                format!("{source_name} (intervention)"),
                OperationSpecies::Transport,
                vec![input_port],
                vec![output_port],
                None,
                vec![SourceTestimony::Intervention {
                    statement: "reverse the presented chronology".to_owned(),
                }],
            )
            .unwrap();
        let validation = mounted.validate(&replacement).unwrap();
        assert_eq!(validation.len(), 1);
        assert!(validation[0].symbols.is_empty());
        assert_eq!(
            validation[0].interventions,
            vec!["reverse the presented chronology"]
        );

        let mut near_name = source.clone();
        near_name.operations.remove(&source_law);
        near_name
            .bind_operation(
                format!("{source_name} intervention"),
                OperationSpecies::Transport,
                vec![input_port],
                vec![output_port],
                None,
                vec![SourceTestimony::Intervention {
                    statement: "near name is not a replacement".to_owned(),
                }],
            )
            .unwrap();
        assert!(mounted.validate(&near_name).is_err());

        let mut wrong_ports = source.clone();
        wrong_ports.operations.remove(&source_law);
        wrong_ports
            .bind_operation(
                format!("{source_name} (intervention)"),
                OperationSpecies::Transport,
                vec![output_port],
                vec![input_port],
                None,
                vec![SourceTestimony::Intervention {
                    statement: "wrong ports are not a replacement".to_owned(),
                }],
            )
            .unwrap();
        assert!(mounted.validate(&wrong_ports).is_err());
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn mounted_witness_refuses_a_replaced_rest_occurrence() {
        let path = std::env::temp_dir().join(format!(
            "native-rest-witness-drift-{}.rest",
            std::process::id()
        ));
        let replacement = path.with_extension("replacement");
        let input = fixture();
        let mut output = std::fs::File::create(&path).unwrap();
        NativeRest::seal_streamed(input, &mut output).unwrap();
        drop(output);
        let mounted = MountedNativeRest::open(&path).unwrap();
        std::fs::copy(&path, &replacement).unwrap();
        std::fs::rename(&replacement, &path).unwrap();
        assert!(mounted.verify_still().is_err());
        std::fs::remove_file(path).unwrap();
    }
}
