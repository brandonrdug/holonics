//! Compact M1 semantic receipt and executable/source closure.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use holonic_engine::exact_value::ExactValue;
use life::mathematical_particle::{
    MathematicalParticle, PassageEndpoint, PassageEquivalence, RelationWitness,
};
use life::mathematical_source::{ArtifactIdentity, PlacedCarrier};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use super::particle::Construction;

const M0_RETURN: &str =
    "output/m0_mathematical_source_circulation/m0-mathematical-source-circulation.json";

pub fn write(root: &Path, default_out: &str, construction: &Construction) -> Result<(), String> {
    let directory = resolve_output(root, default_out)?;
    let locator = directory
        .strip_prefix(root)
        .map_err(|_| "the M1 output left the workspace".to_owned())?
        .to_string_lossy()
        .into_owned();
    let report = report(root, &locator, construction)?;
    let documents = family_documents(&report)?;
    fs::create_dir_all(&directory).map_err(|error| error.to_string())?;

    let mut manifest = BTreeMap::new();
    let mut family = Sha256::new();
    for (name, document) in documents {
        let encoded = serde_json::to_vec_pretty(&document).map_err(|error| error.to_string())?;
        fs::write(directory.join(name), &encoded).map_err(|error| error.to_string())?;
        family.update(name.as_bytes());
        family.update([0]);
        family.update(&encoded);
        manifest.insert(
            name,
            json!({"octets": encoded.len(), "sha256": digest(&encoded)}),
        );
    }
    let family_sha256 = hex(&family.finalize());
    let grade = json!({
        "schema": "eros.m1.grade.v1",
        "truth_status": "ESTABLISHED-BOUNDED",
        "boundary": required(&report, &["boundary"] )?,
        "output_locator": locator,
        "member_manifest_excluding_grade": manifest,
        "member_family_sha256": family_sha256,
        "controls": required(&report, &["controls"] )?,
        "closure": required(&report, &["closure"] )?,
        "external_control_obligations": [
            "mathematical_particle::lineage::tests::two_cuts_of_one_three_occurrence_passage_keep_the_same_outer_boundaries",
            "mathematical_particle::tests::attacks::a_bare_occurrence_bijection_cannot_move_passage_boundaries",
            "mathematical_particle::tests::attacks::one_relational_shadow_can_hide_two_carrying_occurrences"
        ],
    });
    let encoded_grade = serde_json::to_vec_pretty(&grade).map_err(|error| error.to_string())?;
    fs::write(directory.join("grade.form"), &encoded_grade).map_err(|error| error.to_string())?;

    println!("M1 ADDRESSED MATHEMATICAL PARTICLE RETURNED");
    println!("  family: {}", directory.display());
    println!("  member population: 14");
    println!("  member family sha256: {family_sha256}");
    println!("  grade sha256: {}", digest(&encoded_grade));
    Ok(())
}

fn family_documents(report: &Value) -> Result<BTreeMap<&'static str, Value>, String> {
    let source = required(report, &["source_reauthentication"])?;
    let operation = required(report, &["operation_complex"])?;
    let particle = required(report, &["typed_particle"])?;
    let passages = required(report, &["typed_particle", "passages"])?;
    let resident = required(report, &["post_card_return", "resident"])?;
    let passage_documents = passages
        .as_array()
        .ok_or_else(|| "the M1 passage population is not an array".to_owned())?;
    let addressed = passage_documents
        .iter()
        .map(|passage| {
            select(
                passage,
                &[
                    "occurrence",
                    "source_occurrences",
                    "staging_sources",
                    "addressed_occurrence_population",
                    "source_boundary_map",
                    "target_boundary_map",
                    "boundary_preserving_identity_equivalence",
                    "presentation_rebase_boundary_equivalence",
                ],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let joins = passage_documents
        .iter()
        .map(|passage| {
            select(
                passage,
                &["occurrence", "pullback_join_population", "ordered_words"],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let shadows = passage_documents
        .iter()
        .map(|passage| {
            select(
                passage,
                &["occurrence", "relational_shadow_with_reconstruction_fibres"],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let equality_passages = passage_documents
        .iter()
        .map(|passage| {
            select(
                passage,
                &[
                    "occurrence",
                    "source_boundary_map",
                    "target_boundary_map",
                    "boundary_preserving_identity_equivalence",
                    "presentation_rebase_boundary_equivalence",
                ],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let wrap = |schema: &str, content: Value| {
        json!({
            "schema": schema,
            "truth_status": "ESTABLISHED-BOUNDED",
            "boundary": required(report, &["boundary"]).expect("the M1 report owns its boundary"),
            "content": content,
        })
    };

    Ok(BTreeMap::from([
        (
            "source-and-mode.form",
            wrap(
                "eros.m1.source-and-mode.v1",
                json!({
                    "source_reauthentication": source,
                    "placement": required(report, &["placement"] )?,
                    "output_locator": required(report, &["output_locator"] )?,
                }),
            ),
        ),
        (
            "particle-population.form",
            wrap(
                "eros.m1.particle-population.v1",
                select(
                    particle,
                    &[
                        "occurrence",
                        "proposals",
                        "refusals",
                        "classification_receivers",
                    ],
                )?,
            ),
        ),
        (
            "addressed-passages.form",
            wrap(
                "eros.m1.addressed-passages.v1",
                json!({"passages": addressed}),
            ),
        ),
        (
            "pullback-joins.form",
            wrap("eros.m1.pullback-joins.v1", json!({"passages": joins})),
        ),
        (
            "relational-shadows.form",
            wrap(
                "eros.m1.relational-shadows.v1",
                json!({"passages": shadows}),
            ),
        ),
        (
            "typed-carriers-and-ports.form",
            wrap(
                "eros.m1.typed-carriers-and-ports.v1",
                json!({
                    "operation_complex": operation,
                    "particle_typing": select(
                        particle,
                        &["carriers", "ports", "binders", "hypotheses", "operations"],
                    )?,
                }),
            ),
        ),
        (
            "exact-owner-conduct.form",
            wrap(
                "eros.m1.exact-owner-conduct.v1",
                json!({
                    "licenses": required(particle, &["exact_owner_licenses"] )?,
                    "linear_returns": required(particle, &["linear_returns"] )?,
                    "quantity_returns": required(particle, &["quantity_returns"] )?,
                    "resident_bindings": required(report, &["post_card_return", "bindings"] )?,
                }),
            ),
        ),
        (
            "tiling-and-reduction.form",
            wrap(
                "eros.m1.tiling-and-reduction.v1",
                json!({
                    "resident": resident,
                    "opaque_receipt": required(report, &["post_card_return", "opaque_receipt"] )?,
                    "operation_complex_identity": required(report, &["post_card_return", "operation_complex_identity"] )?,
                    "selected_subcomplex_identity": required(report, &["post_card_return", "selected_subcomplex_identity"] )?,
                }),
            ),
        ),
        (
            "receiver-history-family.form",
            wrap(
                "eros.m1.receiver-history-family.v1",
                json!({
                    "value_receivers": required(particle, &["value_receivers"] )?,
                    "rendering_receivers": required(particle, &["rendering_receivers"] )?,
                    "receiver_history_returns": required(particle, &["receiver_history_returns"] )?,
                    "event_readbacks": required(report, &["post_card_return", "event_readbacks"] )?,
                }),
            ),
        ),
        (
            "reconstruction-fibres.form",
            wrap(
                "eros.m1.reconstruction-fibres.v1",
                json!({
                    "open_fibres": required(particle, &["open_fibres"] )?,
                    "passage_relational_shadow_fibres": shadows,
                    "source_disagreement_and_open_lineage": source,
                }),
            ),
        ),
        (
            "equality-family.form",
            wrap(
                "eros.m1.equality-family.v1",
                json!({
                    "passage_boundary_equivalence": equality_passages,
                    "receiver_indexed_sameness": required(report, &["sameness_panels"] )?,
                }),
            ),
        ),
        (
            "exact-work.form",
            wrap(
                "eros.m1.exact-work.v1",
                json!({
                    "controls": required(report, &["controls"] )?,
                    "resident_work": resident,
                }),
            ),
        ),
        (
            "apparatus-telemetry.form",
            wrap(
                "eros.m1.apparatus-telemetry.v1",
                json!({
                    "placement": required(report, &["placement"] )?,
                    "telemetry": resident,
                }),
            ),
        ),
    ]))
}

fn required<'a>(value: &'a Value, path: &[&str]) -> Result<&'a Value, String> {
    let mut current = value;
    for segment in path {
        current = current
            .get(*segment)
            .ok_or_else(|| format!("the M1 receipt lacks {}", path.join(".")))?;
    }
    Ok(current)
}

fn select(value: &Value, fields: &[&str]) -> Result<Value, String> {
    let mut selected = serde_json::Map::new();
    for field in fields {
        selected.insert((*field).to_owned(), required(value, &[*field])?.clone());
    }
    Ok(Value::Object(selected))
}

fn report(root: &Path, output_locator: &str, construction: &Construction) -> Result<Value, String> {
    let particle = &construction.particle;
    let operation = particle.operation();
    let receipt = particle.admission().passage_receipt();
    let source = particle
        .source_testimonies()
        .iter()
        .map(|testimony| {
            json!({
                "artifact": testimony.artifact,
                "chart": testimony.chart,
                "extent": testimony.extent,
                "occurrences": testimony.occurrences.iter().map(occurrence).collect::<Vec<_>>(),
                "contacts": testimony.contacts,
                "work": testimony.work,
                "outside_declared_artifact_open": testimony.outside_declared_artifact_open,
            })
        })
        .collect::<Vec<_>>();
    let source_mark_map_sha256 = digest(
        &serde_json::to_vec(&construction.sameness.source_mark_map)
            .map_err(|error| error.to_string())?,
    );
    let passages = particle
        .passages()
        .iter()
        .map(|passage| {
            let addressed = passage.addressed();
            let identity_map = addressed
                .occurrences()
                .keys()
                .map(|occurrence| (*occurrence, *occurrence))
                .collect();
            let equivalence = PassageEquivalence::found(addressed, addressed, identity_map)
                .expect("an addressed passage is boundary-equivalent to itself");
            let rebase_preserves_sources = addressed.occurrences().values().all(|occurrence| {
                endpoint_rebase_invariant(
                    occurrence.source(),
                    &construction.sameness.source_mark_map,
                )
            });
            let rebase_preserves_targets = addressed.occurrences().values().all(|occurrence| {
                endpoint_rebase_invariant(
                    occurrence.target(),
                    &construction.sameness.source_mark_map,
                )
            });
            let moved_source_occurrences = passage
                .source_occurrences()
                .iter()
                .filter(|source| {
                    construction
                        .sameness
                        .source_mark_map
                        .get(*source)
                        .is_some_and(|target| target != *source)
                })
                .count();
            json!({
                "occurrence": passage.occurrence(),
                "source_occurrences": passage.source_occurrences(),
                "staging_sources": passage.staging_sources().iter().map(|(branch, sources)| {
                    (branch.0, sources)
                }).collect::<BTreeMap<_, _>>(),
                "staging_front_depth": passage.staging_front_depth(),
                "terminal_front_depth": passage.front_depth(),
                "staging": passage.staging().iter().map(|(branch, step)| json!({
                    "branch": branch.0,
                    "event": step.event.0,
                    "law": step.law.0,
                    "outputs": step.outputs.iter().map(|port| port.0).collect::<Vec<_>>(),
                })).collect::<Vec<_>>(),
                "ordered_words": passage.branches().iter().map(|(branch, word)| json!({
                    "branch": branch.0,
                    "occurrence": word.occurrence,
                    "steps": word.steps.iter().map(|step| json!({
                        "event": step.event.0,
                        "law": step.law.0,
                        "inputs": step.inputs.iter().map(|port| port.0).collect::<Vec<_>>(),
                        "outputs": step.outputs.iter().map(|port| port.0).collect::<Vec<_>>(),
                    })).collect::<Vec<_>>(),
                })).collect::<Vec<_>>(),
                "terminal_events": passage.terminal_events().iter().map(|(branch, event)| [branch.0, event.0]).collect::<Vec<_>>(),
                "addressed_occurrence_population": addressed.occurrences().values().map(|occurrence| json!({
                    "occurrence": occurrence.occurrence().0,
                    "law": occurrence.law().0,
                    "source": endpoint(occurrence.source()),
                    "target": endpoint(occurrence.target()),
                })).collect::<Vec<_>>(),
                "source_boundary_map": addressed.occurrences().values().map(|occurrence| {
                    (occurrence.occurrence().0, endpoint(occurrence.source()))
                }).collect::<BTreeMap<_, _>>(),
                "target_boundary_map": addressed.occurrences().values().map(|occurrence| {
                    (occurrence.occurrence().0, endpoint(occurrence.target()))
                }).collect::<BTreeMap<_, _>>(),
                "pullback_join_population": addressed.pullback_joins().iter().map(|join| {
                    let retained = addressed
                        .split_rejoin(join.left(), join.right())
                        .is_ok_and(|returned| returned == join);
                    json!({
                        "left_occurrence": join.left().0,
                        "right_occurrence": join.right().0,
                        "joining_equality": endpoint(join.shared()),
                        "interaction_witnesses": join.interactions().iter().map(|id| id.0).collect::<Vec<_>>(),
                        "split_rejoin_retained": retained,
                    })
                }).collect::<Vec<_>>(),
                "relational_shadow_with_reconstruction_fibres": addressed.shadow_fibres().iter().map(|(shadow, fibre)| json!({
                    "source": endpoint(shadow.source()),
                    "target": endpoint(shadow.target()),
                    "carrying_occurrences": fibre.iter().map(|event| event.0).collect::<Vec<_>>(),
                })).collect::<Vec<_>>(),
                "boundary_preserving_identity_equivalence": equivalence.occurrence_map().iter().map(|(left, right)| [left.0, right.0]).collect::<Vec<_>>(),
                "presentation_rebase_boundary_equivalence": {
                    "source_mark_map_sha256": source_mark_map_sha256,
                    "moved_source_occurrence_population": moved_source_occurrences,
                    "source_boundary_map_preserved": rebase_preserves_sources,
                    "target_boundary_map_preserved": rebase_preserves_targets,
                    "occurrence_map": equivalence.occurrence_map().iter().map(|(left, right)| [left.0, right.0]).collect::<Vec<_>>(),
                },
            })
        })
        .collect::<Vec<_>>();
    let linear_returns = particle
        .linear_returns()
        .iter()
        .map(|returned| {
            let truth_status = if returned.passage().branch().0 == 1 {
                "ESTABLISHED-CONDITIONAL fixture consequence under addressed Euclidean/t>0 hypotheses; not a proof of the paper tensor identity"
            } else {
                "ESTABLISHED-BOUNDED exact-owner return"
            };
            json!({
                "passage": returned.passage().passage(),
                "branch": returned.passage().branch().0,
                "realization_word": returned.realization_word(),
                "truth_status": truth_status,
                "lineage": returned.lineage(),
                "terminal_value_face": returned.terminal_value_face().iter().map(exact_value).collect::<Vec<_>>(),
                "steps": returned.steps().iter().map(|step| json!({
                    "event": step.event.0,
                    "law": step.law.0,
                    "inputs": step.inputs.iter().map(|port| port.0).collect::<Vec<_>>(),
                    "outputs": step.outputs.iter().map(|port| port.0).collect::<Vec<_>>(),
                    "matrix_sha256": step.matrix_sha256,
                    "owner_evidence_sha256": step.owner_evidence_sha256,
                })).collect::<Vec<_>>(),
            })
        })
        .collect::<Vec<_>>();
    let quantity_returns = particle
        .quantity_returns()
        .iter()
        .map(|returned| {
            json!({
                "passage": returned.passage().passage(),
                "branch": returned.passage().branch().0,
                "factors": returned.factors(),
                "powered_factors": returned.powered_factors(),
                "kernel_word": returned.kernel_word(),
                "dimension_rows": returned.dimension_matrix().rows(),
                "boundary_columns": returned.boundary_columns().iter().map(|(law, columns)| json!({
                    "law": law.0,
                    "columns": columns.iter().map(|(port, positions)| (port.0, positions)).collect::<BTreeMap<_, _>>(),
                })).collect::<Vec<_>>(),
                "owner_evidence_sha256": returned.owner_evidence_sha256().iter().map(|(law, sha)| (law.0, sha)).collect::<BTreeMap<_, _>>(),
                "returned": returned.returned(),
            })
        })
        .collect::<Vec<_>>();
    let readbacks = receipt
        .readbacks()
        .iter()
        .map(|(event, values)| (event.0, values))
        .collect::<BTreeMap<_, _>>();
    let source_span_receipts = construction
        .proposal_source_spans
        .iter()
        .map(|(name, addresses)| {
            let occurrences = addresses
                .iter()
                .map(|address| {
                    particle
                        .source_testimonies()
                        .iter()
                        .flat_map(|testimony| &testimony.occurrences)
                        .find(|occurrence| &occurrence.address == address)
                        .map(occurrence)
                        .ok_or_else(|| format!("addressed source occurrence {address} vanished"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok((name.clone(), occurrences))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    let closure_artifacts = particle
        .source_testimonies()
        .iter()
        .map(|testimony| testimony.artifact.clone())
        .chain(particle.exterior_artifacts().iter().cloned())
        .collect::<Vec<_>>();
    let closure = closure(root, &closure_artifacts)?;

    Ok(json!({
        "schema": "eros.m1-mathematical-operation-complex.v1",
        "grade": "established-bounded",
        "boundary": "one conditional M1 fixture; no proof of the paper, no M2 excitation, learning, generator recovery, compression, or Phoenix completion",
        "source_reauthentication": {
            "kind": "bounded exterior remount of admitted M0 material; not new M0 conduct",
            "addressing_rule": "authenticated artifact digest plus admitted serial ordinal; no spelling or atlas ID routes acceptance",
            "testimonies": source,
            "exterior_artifacts": particle.exterior_artifacts(),
            "proposal_spans": source_span_receipts,
            "rigidity_lineage_only_open": {
                "grade": "OPEN",
                "addresses": construction.rigidity_lineage,
                "standing": "lineage-only exterior proposal; no coefficient tensor was typed, licensed, or admitted as resident work",
            },
        },
        "operation_complex": operation,
        "typed_particle": {
            "occurrence": particle.occurrence(),
            "carriers": particle.carriers().iter().map(|carrier| json!({
                "id": carrier.id.0,
                "source_occurrences": carrier.source_occurrences,
                "owner_carrier": carrier.owner_carrier,
                "equality_law_lineage": carrier.equality_law_lineage,
            })).collect::<Vec<_>>(),
            "ports": particle.ports().iter().map(|port| json!({
                "boundary": port.boundary,
                "carrier": port.carrier.0,
                "unit_frame": port.unit_frame,
                "exposed": port.exposed,
            })).collect::<Vec<_>>(),
            "binders": particle.binders().iter().map(|binder| json!({
                "id": binder.id.0,
                "source_occurrences": binder.source_occurrences,
                "ports": binder.ports.iter().map(|port| port.0).collect::<Vec<_>>(),
                "laws": binder.laws.iter().map(|law| law.0).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
            "hypotheses": particle.hypotheses().iter().map(|hypothesis| json!({
                "id": hypothesis.id.0,
                "source_occurrences": hypothesis.source_occurrences,
                "laws": hypothesis.licenses.iter().map(|law| law.0).collect::<Vec<_>>(),
                "branches": hypothesis.branches.iter().map(|branch| branch.0).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
            "operations": particle.operations().iter().map(|typed| json!({
                "law": typed.law.0,
                "input_arity": typed.input_arity,
                "output_arity": typed.output_arity,
                "hypotheses": typed.hypotheses.iter().map(|id| id.0).collect::<Vec<_>>(),
                "branches": typed.branches.iter().map(|id| id.0).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
            "passages": passages,
            "exact_owner_licenses": construction.licenses,
            "linear_returns": linear_returns,
            "quantity_returns": quantity_returns,
            "value_receivers": particle.value_receivers().iter().map(|receiver| json!({
                "occurrence": receiver.occurrence(),
                "port": receiver.port().0,
                "values": receiver.values().iter().map(exact_value).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
            "rendering_receivers": particle.rendering_receivers().iter().map(|receiver| json!({
                "occurrence": receiver.occurrence(),
                "port": receiver.port().0,
                "prior_m0_vector_artifact_occurrence": receiver.artifact_occurrence(),
            })).collect::<Vec<_>>(),
            "classification_receivers": particle.classification_receivers().iter().map(|receiver| json!({
                "occurrence": receiver.occurrence(),
                "classes": receiver.classes(),
            })).collect::<Vec<_>>(),
            "receiver_history_returns": particle.receiver_history_returns().iter().map(|receiver| json!({
                "occurrence": receiver.occurrence(),
                "reading": history_reading(receiver.reading()),
            })).collect::<Vec<_>>(),
            "proposals": construction.proposals,
            "refusals": particle.refusals().iter().map(|refusal| json!({
                "proposal": refusal.proposal(),
                "obstruction": format!("{:?}", refusal.obstruction()),
            })).collect::<Vec<_>>(),
            "open_fibres": particle.open_fibres().iter().map(|fibre| json!({
                "occurrence": fibre.occurrence,
                "question": fibre.question,
                "candidates": fibre.candidates,
                "would_be_decided_by": fibre.would_be_decided_by,
            })).collect::<Vec<_>>(),
        },
        "post_card_return": {
            "opaque_receipt": receipt.address(),
            "operation_complex_identity": receipt.operation_complex_identity(),
            "selected_subcomplex_identity": receipt.selected_subcomplex_identity(),
            "event_readbacks": readbacks,
            "bindings": particle.admission().bindings().iter().map(|binding| json!({
                "operation": binding.operation,
                "species": binding.species,
                "symbols": binding.symbols.iter().map(|symbol| format!("{symbol:?}")).collect::<Vec<_>>(),
                "fields": binding.fields,
                "shapes": binding.shapes,
                "interventions": binding.interventions,
                "descriptions": binding.descriptions,
                "exact_owner_licenses": binding.exact_owner_licenses,
            })).collect::<Vec<_>>(),
            "resident": construction.resident,
        },
        "sameness_panels": sameness(construction, particle)?,
        "controls": controls(construction, particle),
        "placement": {
            "cpu_role": "bounded exterior/offline source-admission and artifact audit",
            "resident_hot_deed": "one GPU FrontPassage over all six events",
            "cpu_semantic_cells": construction.resident.cpu_cells,
            "gpu_device": construction.resident.device,
            "ptx_sha256": construction.resident.ptx_sha256,
        },
        "output_locator": output_locator,
        "closure": closure,
    }))
}

fn resolve_output(root: &Path, default_out: &str) -> Result<PathBuf, String> {
    let requested = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(default_out));
    let out = if requested.is_absolute() {
        requested
    } else {
        root.join(requested)
    };
    let relative = out
        .strip_prefix(root)
        .map_err(|_| "the M1 output must remain under the workspace".to_owned())?;
    let parts = relative
        .components()
        .map(|component| component.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    let valid = |slug: &str| {
        !slug.is_empty()
            && slug.bytes().all(|octet| {
                octet.is_ascii_lowercase() || octet.is_ascii_digit() || b"_-.".contains(&octet)
            })
    };
    if parts.len() != 2
        || parts[0] != "output"
        || parts[1] != "the_mathematical_particle_is_an_addressed_passage"
        || !valid(&parts[1])
    {
        return Err(
            "the M1 output must be output/the_mathematical_particle_is_an_addressed_passage"
                .to_owned(),
        );
    }
    Ok(out)
}

fn sameness(construction: &Construction, particle: &MathematicalParticle) -> Result<Value, String> {
    let sameness = &construction.sameness;
    let value = particle
        .value_receivers()
        .first()
        .ok_or_else(|| "the M1 value receiver vanished".to_owned())?;
    let [left_index, right_index] = sameness.receiver_indices;
    let left = value
        .values()
        .get(left_index)
        .ok_or_else(|| "left returned value vanished".to_owned())?;
    let right = value
        .values()
        .get(right_index)
        .ok_or_else(|| "right returned value vanished".to_owned())?;
    let (left_testimony, left_source) = source_occurrence(particle, &sameness.left_occurrence)?;
    let (right_testimony, right_source) = source_occurrence(particle, &sameness.right_occurrence)?;
    let left_bytes = &sameness.classification_classes[&sameness.left_occurrence];
    let right_bytes = &sameness.classification_classes[&sameness.right_occurrence];
    let characteristic_pairs = sameness.similarity_characteristics[&sameness.left_occurrence]
        .iter()
        .map(|(name, left)| {
            let right = &sameness.similarity_characteristics[&sameness.right_occurrence][name];
            (
                name.clone(),
                json!({"left": left, "right": right, "equal": left == right}),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let affine = particle
        .linear_returns()
        .first()
        .ok_or_else(|| "the affine exact return vanished".to_owned())?;
    if affine.lineage().len() != 4 || affine.lineage().iter().any(|row| row.is_empty()) {
        return Err("the four-role affine population vanished from the exact return".to_owned());
    }
    let affine_rows = affine
        .lineage()
        .iter()
        .map(|row| row[0].clone())
        .collect::<Vec<_>>();
    Ok(json!({
        "occurrence_identity": {
            "left": sameness.left_occurrence,
            "right": sameness.right_occurrence,
            "equal": sameness.left_occurrence == sameness.right_occurrence,
        },
        "typed_carrier_equality": {
            "left": exact_value(left),
            "right": exact_value(right),
            "ordering": format!("{:?}", left.compare(right)),
        },
        "marked_diagram_isomorphism": {
            "source_mark_map": sameness.source_mark_map,
            "operation_ports": particle.operation().shape.boundaries.objects,
            "laws": particle.operation().shape.laws,
            "events": particle.operation().shape.occurrences,
            "interactions": particle.operation().shape.interactions,
        },
        "doctrine_equivalence": {
            "forward": sameness.doctrine_forward,
            "reverse": sameness.doctrine_reverse,
            "left_composition": sameness.doctrine_reverse.multiply(&sameness.doctrine_forward).map_err(|error| error.to_string())?,
            "right_composition": sameness.doctrine_forward.multiply(&sameness.doctrine_reverse).map_err(|error| error.to_string())?,
            "population_roles": {
                "row_0_baseline_original": affine_rows[0],
                "row_1_reflow_original": affine_rows[1],
                "row_2_baseline_rebased": affine_rows[2],
                "row_3_reflow_rebased": affine_rows[3],
                "presentation_receiver_indices": sameness.receiver_indices,
                "rebase_pairs": [[0, 2], [1, 3]],
            },
        },
        "receiver_history_equivalence": witness(&sameness.history_witness),
        "receiver_face": {"indices": sameness.receiver_indices, "equal": left == right},
        "classification": {"left": left_bytes, "right": right_bytes, "equal": left_bytes == right_bytes},
        "characteristic_similarity": characteristic_pairs,
        "presentation": {
            "left_bounds": left_source.bounds,
            "right_bounds": right_source.bounds,
            "equal": left_source.bounds == right_source.bounds,
        },
        "source_bytes": {
            "left_artifact_occurrence": left_testimony.artifact.occurrence,
            "left_octets": left_testimony.artifact.octets,
            "right_artifact_occurrence": right_testimony.artifact.occurrence,
            "right_octets": right_testimony.artifact.octets,
            "equal_under_authenticated_sha256": left_testimony.artifact.sha256 == right_testimony.artifact.sha256,
        },
        "source_digest": {
            "map": "sha256",
            "left": left_testimony.artifact.sha256,
            "right": right_testimony.artifact.sha256,
            "equal": left_testimony.artifact.sha256 == right_testimony.artifact.sha256,
        },
        "rendering": {
            "grade": "prior-M0-admitted-vector-face",
            "artifact_occurrence": sameness.rendering_artifact_occurrence,
        },
    }))
}

fn source_occurrence<'a>(
    particle: &'a MathematicalParticle,
    address: &str,
) -> Result<
    (
        &'a life::mathematical_source::SourceLayoutTestimony,
        &'a PlacedCarrier,
    ),
    String,
> {
    particle
        .source_testimonies()
        .iter()
        .find_map(|testimony| {
            testimony
                .occurrences
                .iter()
                .find(|occurrence| occurrence.address == address)
                .map(|occurrence| (testimony, occurrence))
        })
        .ok_or_else(|| format!("sameness source occurrence {address} vanished"))
}

fn controls(construction: &Construction, particle: &MathematicalParticle) -> Value {
    let operation = particle.operation();
    let addressed_occurrence_population = particle
        .passages()
        .iter()
        .map(|passage| passage.addressed().occurrences().len())
        .sum::<usize>();
    let pullback_join_population = particle
        .passages()
        .iter()
        .map(|passage| passage.addressed().pullback_joins().len())
        .sum::<usize>();
    let all_pullback_joins_split_rejoin = particle.passages().iter().all(|passage| {
        passage.addressed().pullback_joins().iter().all(|join| {
            passage
                .addressed()
                .split_rejoin(join.left(), join.right())
                .is_ok_and(|returned| returned == join)
        })
    });
    let presentation_rebase_preserves_every_boundary = particle.passages().iter().all(|passage| {
        passage
            .addressed()
            .occurrences()
            .values()
            .all(|occurrence| {
                endpoint_rebase_invariant(
                    occurrence.source(),
                    &construction.sameness.source_mark_map,
                ) && endpoint_rebase_invariant(
                    occurrence.target(),
                    &construction.sameness.source_mark_map,
                )
            })
    });
    let terminal_events = particle
        .passages()
        .iter()
        .flat_map(|passage| passage.terminal_events().values())
        .copied()
        .collect::<BTreeSet<_>>();
    let returned_terminals = particle
        .admission()
        .passage_receipt()
        .readbacks()
        .iter()
        .filter(|(event, values)| {
            terminal_events.contains(event) && values.iter().all(|word| *word == (0, 0))
        })
        .map(|(event, _)| *event)
        .collect::<BTreeSet<_>>();
    let licensed_laws = construction
        .licenses
        .iter()
        .map(|license| license.constraint().law())
        .collect::<BTreeSet<_>>();
    let operation_laws = operation
        .shape
        .laws
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    json!({
        "operation_complex_population": usize::from(!operation.name.is_empty()),
        "passage_population": particle.passages().len(),
        "addressed_occurrence_population": addressed_occurrence_population,
        "pullback_join_population": pullback_join_population,
        "all_pullback_joins_split_rejoin": all_pullback_joins_split_rejoin,
        "presentation_rebase_preserves_every_boundary": presentation_rebase_preserves_every_boundary,
        "licensed_law_population": licensed_laws.len(),
        "operation_law_population": operation_laws.len(),
        "licensed_law_set_equals_operation_law_set": licensed_laws == operation_laws,
        "terminal_event_population": terminal_events.len(),
        "zero_returned_terminal_population": returned_terminals.len(),
        "all_terminal_events_returned_exact_zero": terminal_events == returned_terminals,
        "affine_returned_face_population": particle.linear_returns().first().map(|returned| returned.terminal_value_face().len()),
        "resident_deed_launches": construction.resident.deed_launches,
        "resident_synchronizations": construction.resident.synchronizations,
        "resident_obstruction_population": construction.resident.obstruction_population,
        "cpu_semantic_cells": construction.resident.cpu_cells,
        "receiver_history_grade": particle.receiver_history_returns().first().map(|returned| {
            let reading = returned.reading();
            if reading.root_conduct_blocks.is_empty() && reading.shortest_separators.is_empty() { "OPEN" } else { "reopened-by-return" }
        }),
        "open_fibre_population": particle.open_fibres().len(),
    })
}

fn history_reading(reading: &life::causal_section::CausalSectionReading) -> Value {
    json!({
        "schema": reading.schema,
        "receivers": reading.receivers,
        "presentations": reading.presentations.iter().map(|presentation| json!({
            "identity": presentation.identity,
            "lineage": presentation.lineage,
            "states": presentation.states,
            "sites": presentation.sites,
            "bonds": presentation.bonds,
            "compounds": presentation.compounds,
            "contact_faces": presentation.contact_faces,
        })).collect::<Vec<_>>(),
        "root_one_shot_blocks": reading.root_one_shot_blocks,
        "root_conduct_blocks": reading.root_conduct_blocks,
        "reconstruction_fibres": reading.reconstruction_fibers.iter().map(|fibre| json!({
            "presentations": fibre.presentations,
            "outside_declared_population_open": fibre.outside_declared_population_open,
        })).collect::<Vec<_>>(),
        "shortest_separators": reading.shortest_separators.iter().map(|separator| json!({
            "left": separator.left,
            "right": separator.right,
            "interventions": separator.interventions,
            "receiver": separator.receiver,
            "left_observation": separator.left_observation,
            "right_observation": separator.right_observation,
            "separated_by_terminus": separator.separated_by_terminus,
        })).collect::<Vec<_>>(),
        "compression": reading.compression,
        "work": {
            "presentations": reading.work.presentations,
            "states": reading.work.states,
            "contacts": reading.work.contacts,
            "transitions": reading.work.transitions,
            "observations": reading.work.observations,
            "complete_state_pair_chart": reading.work.complete_state_pair_chart.to_string(),
        },
    })
}

fn closure(root: &Path, artifacts: &[ArtifactIdentity]) -> Result<Vec<Value>, String> {
    let mut paths = BTreeSet::from([
        "Cargo.lock".to_owned(),
        "Cargo.toml".to_owned(),
        M0_RETURN.to_owned(),
        "soma/life/Cargo.toml".to_owned(),
        "crates/holonic-engine/Cargo.toml".to_owned(),
        "crates/holonic-engine/build.rs".to_owned(),
        "soma/life/examples/the_affine_swing_is_a_typed_mathematical_particle.rs".to_owned(),
    ]);
    collect_extension(root, "soma/life/examples/m1", "rs", &mut paths)?;
    collect_extension(root, "soma/life/src", "rs", &mut paths)?;
    collect_extension(root, "crates/holonic-engine/src", "rs", &mut paths)?;
    collect_extension(root, "crates/holonic-engine/kernels", "cu", &mut paths)?;
    paths.extend(artifacts.iter().map(|artifact| artifact.locator.clone()));
    paths
        .into_iter()
        .map(|relative| {
            let bytes = fs::read(root.join(&relative))
                .map_err(|error| format!("read closure {relative}: {error}"))?;
            let mut addressed = Sha256::new();
            addressed.update(relative.as_bytes());
            addressed.update([0]);
            addressed.update(&bytes);
            Ok(json!({
                "path": relative,
                "octets": bytes.len(),
                "content_sha256": digest(&bytes),
                "path_and_content_sha256": hex(&addressed.finalize()),
            }))
        })
        .collect()
}

fn collect_extension(
    root: &Path,
    relative: &str,
    extension: &str,
    paths: &mut BTreeSet<String>,
) -> Result<(), String> {
    let directory = root.join(relative);
    for entry in fs::read_dir(&directory)
        .map_err(|error| format!("read closure directory {relative}: {error}"))?
    {
        let entry = entry.map_err(|error| format!("read closure entry: {error}"))?;
        let file_type = entry
            .file_type()
            .map_err(|error| format!("read closure file type: {error}"))?;
        let path = entry.path();
        if file_type.is_dir() {
            let nested = path
                .strip_prefix(root)
                .map_err(|error| error.to_string())?
                .to_string_lossy()
                .into_owned();
            collect_extension(root, &nested, extension, paths)?;
        } else if file_type.is_file()
            && path.extension().and_then(|value| value.to_str()) == Some(extension)
        {
            paths.insert(
                path.strip_prefix(root)
                    .map_err(|error| error.to_string())?
                    .to_string_lossy()
                    .into_owned(),
            );
        }
    }
    Ok(())
}

fn occurrence(occurrence: &PlacedCarrier) -> Value {
    json!({
        "address": occurrence.address,
        "payload_sha256": occurrence.payload_sha256,
        "payload_octets": occurrence.payload_octets,
        "serial_ordinal": occurrence.serial_ordinal,
        "bounds": occurrence.bounds,
    })
}

fn exact_value(value: &ExactValue) -> Value {
    serde_json::to_value(value).expect("ExactValue serialization is infallible")
}

fn endpoint(endpoint: &PassageEndpoint) -> Value {
    match endpoint {
        PassageEndpoint::Exterior(sources) => json!({
            "kind": "exterior-source-population",
            "occurrences": sources,
        }),
        PassageEndpoint::Ports(ports) => json!({
            "kind": "typed-port-word",
            "ports": ports.iter().map(|port| port.0).collect::<Vec<_>>(),
        }),
    }
}

fn endpoint_rebase_invariant(
    endpoint: &PassageEndpoint,
    source_mark_map: &BTreeMap<String, String>,
) -> bool {
    match endpoint {
        PassageEndpoint::Exterior(sources) => {
            sources
                .iter()
                .map(|source| {
                    source_mark_map
                        .get(source)
                        .cloned()
                        .unwrap_or_else(|| source.clone())
                })
                .collect::<BTreeSet<_>>()
                == *sources
        }
        PassageEndpoint::Ports(_) => true,
    }
}

fn witness(witness: &RelationWitness) -> Value {
    match witness {
        RelationWitness::Established {
            evidence_occurrences,
        } => json!({
            "grade": "ESTABLISHED",
            "evidence_occurrences": evidence_occurrences,
        }),
        RelationWitness::Separated { shortest_separator } => json!({
            "grade": "SEPARATED",
            "shortest_separator": shortest_separator,
        }),
        RelationWitness::Open {
            obstruction,
            reconstruction_fibre,
        } => json!({
            "grade": "OPEN",
            "obstruction": obstruction,
            "reconstruction_fibre": reconstruction_fibre,
        }),
    }
}

fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|octet| format!("{octet:02x}")).collect()
}
