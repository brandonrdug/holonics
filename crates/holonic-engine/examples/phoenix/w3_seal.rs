//! W3's material-founded derivation and source-detached product seal.

use std::path::{Path, PathBuf};

use holonic_engine::cultivated_rest::{
    AlignedFactor, CodebookGraphIdentity, CultivatedRest, CultivatedRestInput,
    DerivationAdjointRankReceipt, DirectoryCompanion, ExtentOrigin, MorphologyPayload,
    NativeMorphologyInput, OctaveBoundOrigin, PortDirection, PortExtentAgreement,
    PredecessorProductIdentity, ReconstructionCandidate, ReconstructionFibre, RuntimeChart,
    RuntimeLawReceipt, TargetedAblation, TypedLaw, TypedPort, write_native_morphology,
};
use holonic_engine::cultivation_derivation::{
    CultivationDerivation, HiddenPointSection, derive_w3_return_at_grain_with_target,
    to_aligned_material,
};
use holonic_engine::embedding_fiber::AlignedMaterial;
use holonic_engine::native_occurrence::NativeOccurrence;
use holonic_engine::native_rest::MountedNativeRest;
use holonic_engine::ported_operation::SourceTestimony;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use sha2::{Digest, Sha256};

use super::streamed::cultivation_overlay::{
    FactorizedCandidate, OverlayShape, OverlayTestimony, RankDerivationReceipt,
    SeparatingReceiver, SparseDefect, SupportedFactor,
};
use super::{streamed, tower, w3_fixture};

pub const LEFT_POPULATION: &str = "phoenix.w3.factor.left";
pub const RIGHT_POPULATION: &str = "phoenix.w3.factor.right";
pub const GRAIN: i32 = 48;

pub fn runtime_law() -> RuntimeLawReceipt {
    RuntimeLawReceipt {
        schema: "holonic-engine.phoenix.runtime-law.v1".to_owned(),
        grain: GRAIN as u32,
        series_aperture: 14,
        band_terms: tower::BAND_TERMS as u32,
        vocabulary_extent: tower::VOCABULARY as u32,
        hidden_extent: tower::HIDDEN as u32,
        rank: 1,
        left_population: LEFT_POPULATION.to_owned(),
        right_population: RIGHT_POPULATION.to_owned(),
        chart: RuntimeChart::Midpoint,
        fuse: true,
        add_special_tokens: false,
    }
}

pub struct SealedProduct {
    pub product: CultivatedRest,
}

fn digest_bytes(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn law(
    name: &str,
    inputs: &[&str],
    outputs: &[&str],
    extent_agreements: Vec<PortExtentAgreement>,
) -> TypedLaw {
    TypedLaw {
        name: name.to_owned(),
        inputs: inputs.iter().map(|value| (*value).to_owned()).collect(),
        outputs: outputs.iter().map(|value| (*value).to_owned()).collect(),
        constitutive_digest: digest_bytes(name.as_bytes()),
        extent_agreements,
    }
}

pub fn laws() -> Vec<TypedLaw> {
    vec![
        law(
            "phoenix.overlay.standing.input",
            &[],
            &["phoenix.overlay/input"],
            Vec::new(),
        ),
        law(
            "phoenix.overlay.standing.predecessor",
            &[],
            &["phoenix.overlay/w2-predecessor-output"],
            Vec::new(),
        ),
        law(
            "phoenix.overlay.withdraw-terminal",
            &["phoenix.overlay/input"],
            &["phoenix.overlay/terminal-input"],
            vec![
                PortExtentAgreement::Rows {
                    left: "phoenix.overlay/input".to_owned(),
                    right: "phoenix.overlay/terminal-input".to_owned(),
                },
                PortExtentAgreement::Width {
                    left: "phoenix.overlay/input".to_owned(),
                    right: "phoenix.overlay/terminal-input".to_owned(),
                },
            ],
        ),
        law(
            "phoenix.overlay.factorized-contract",
            &["phoenix.overlay/terminal-input"],
            &["phoenix.overlay/delta-output"],
            vec![PortExtentAgreement::Rows {
                left: "phoenix.overlay/terminal-input".to_owned(),
                right: "phoenix.overlay/delta-output".to_owned(),
            }],
        ),
        law(
            "phoenix.overlay.re-entry",
            &[
                "phoenix.overlay/w2-predecessor-output",
                "phoenix.overlay/delta-output",
            ],
            &["phoenix.overlay/output"],
            vec![
                PortExtentAgreement::Rows {
                    left: "phoenix.overlay/w2-predecessor-output".to_owned(),
                    right: "phoenix.overlay/output".to_owned(),
                },
                PortExtentAgreement::Width {
                    left: "phoenix.overlay/w2-predecessor-output".to_owned(),
                    right: "phoenix.overlay/output".to_owned(),
                },
                PortExtentAgreement::Rows {
                    left: "phoenix.overlay/delta-output".to_owned(),
                    right: "phoenix.overlay/output".to_owned(),
                },
                PortExtentAgreement::Width {
                    left: "phoenix.overlay/delta-output".to_owned(),
                    right: "phoenix.overlay/output".to_owned(),
                },
            ],
        ),
    ]
}

pub fn ports(input_bound: u32, predecessor_bound: u32) -> Vec<TypedPort> {
    let runtime = ExtentOrigin::Runtime;
    vec![
        TypedPort {
            name: "phoenix.overlay/input".to_owned(),
            direction: PortDirection::Input,
            carrier: "exact-i64".to_owned(),
            rows: runtime,
            width: tower::HIDDEN as u64,
            octave_bound: OctaveBoundOrigin::Rested(input_bound as u64),
        },
        TypedPort {
            name: "phoenix.overlay/w2-predecessor-output".to_owned(),
            direction: PortDirection::Input,
            carrier: "exact-i64".to_owned(),
            rows: runtime,
            width: tower::VOCABULARY as u64,
            octave_bound: OctaveBoundOrigin::Rested(predecessor_bound as u64),
        },
        TypedPort {
            name: "phoenix.overlay/terminal-input".to_owned(),
            direction: PortDirection::Output,
            carrier: "exact-i64".to_owned(),
            rows: runtime,
            width: tower::HIDDEN as u64,
            octave_bound: OctaveBoundOrigin::RuntimeDerived,
        },
        TypedPort {
            name: "phoenix.overlay/delta-output".to_owned(),
            direction: PortDirection::Output,
            carrier: "exact-i64".to_owned(),
            rows: runtime,
            width: tower::VOCABULARY as u64,
            octave_bound: OctaveBoundOrigin::RuntimeDerived,
        },
        TypedPort {
            name: "phoenix.overlay/output".to_owned(),
            direction: PortDirection::Output,
            carrier: "exact-i64".to_owned(),
            rows: runtime,
            width: tower::VOCABULARY as u64,
            octave_bound: OctaveBoundOrigin::RuntimeDerived,
        },
    ]
}

pub fn testimony() -> OverlayTestimony {
    let statement = |value: &str| {
        vec![SourceTestimony::AuthoritativeDescription {
            statement: value.to_owned(),
        }]
    };
    let mut v = statement(RIGHT_POPULATION);
    v.push(SourceTestimony::DeclaredShape {
        population: RIGHT_POPULATION.to_owned(),
        shape: vec![1, tower::HIDDEN],
    });
    let mut u = statement(LEFT_POPULATION);
    u.push(SourceTestimony::DeclaredShape {
        population: LEFT_POPULATION.to_owned(),
        shape: vec![tower::VOCABULARY, 1],
    });
    OverlayTestimony {
        input: statement("phoenix.overlay.standing.input"),
        predecessor: statement("phoenix.overlay.standing.predecessor"),
        terminal_withdraw: vec![SourceTestimony::Intervention {
            statement: "withdraw rows [0, terminal)".to_owned(),
        }],
        v,
        u,
        re_entry: statement("phoenix.overlay.re-entry"),
    }
}

fn lower_face(value: (i64, i64)) -> Rat {
    Rat::new(BigInt::from(value.0), BigInt::one() << GRAIN as usize)
}
fn upper_face(value: (i64, i64)) -> Rat {
    Rat::new(BigInt::from(value.1), BigInt::one() << GRAIN as usize)
}

/// Return the actual derivation from the two W2 receiver sections. No target or competitor value
/// is authored: both are read from the returned potential face before this function is called.
pub fn derive_from_w2(
    dev_hidden: &[(i64, i64)],
    control_hidden: &[(i64, i64)],
    dev_potential: &[(i64, i64)],
    target: usize,
) -> Result<CultivationDerivation, String> {
    if dev_potential.len() <= target
        || control_hidden.len() != dev_hidden.len()
        || dev_hidden.len() < 2
        || dev_hidden
            .iter()
            .chain(control_hidden.iter())
            .any(|value| value.0 != value.1)
    {
        return Err("W2 hidden sections are not exact point faces".to_owned());
    }
    // The strict receiver is interval-facing: the target enters through its LOWER face while
    // every competitor enters through its UPPER face at the resident 2^-48 grain.  Using one
    // endpoint for both would silently turn a strict separation into an ordinal comparison.
    let target_potential = lower_face(dev_potential[target]);
    let strongest = dev_potential
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != target)
        .map(|(_, value)| upper_face(*value))
        .max()
        .ok_or_else(|| "W2 potential has no competitor".to_owned())?;
    let hidden_dev =
        HiddenPointSection::new(dev_hidden.iter().map(|value| lower_face(*value)).collect());
    let hidden_control = HiddenPointSection::new(
        control_hidden
            .iter()
            .map(|value| lower_face(*value))
            .collect(),
    );
    derive_w3_return_at_grain_with_target(
        &hidden_dev,
        &hidden_control,
        target_potential,
        strongest,
        GRAIN,
        target,
    )
    .map_err(|error| error.to_string())
}

fn overlay_receipt(derivation: &CultivationDerivation) -> Result<RankDerivationReceipt, String> {
    let pair = &derivation.pair;
    // `pair` retains the two-coordinate lineage that founded the annihilator, while the sparse
    // defect carries only its actual nonzero support. A zero control coordinate can lawfully
    // found a one-coordinate annihilator; storing it as supported would contradict
    // `SupportedFactor` and fabricate work.
    let right_support = [
        (pair.first, pair.control_annihilator[0].clone()),
        (pair.second, pair.control_annihilator[1].clone()),
    ]
    .into_iter()
    .filter(|(_, value)| !value.is_zero())
    .collect::<Vec<_>>();
    if right_support.is_empty() {
        return Err("the control annihilator has empty support".to_owned());
    }
    let supported = holonic_engine::exact_linear::ExactRatMatrix::new(vec![
        right_support
            .iter()
            .map(|(_, value)| &derivation.u_scale * value)
            .collect(),
    ])
    .map_err(|error| error.to_string())?;
    let zero = holonic_engine::exact_linear::ExactRatMatrix::zero(1, right_support.len())
        .map_err(|error| error.to_string())?;
    let candidate = supported
        .get(0, 0)
        .map_err(|error| error.to_string())?
        .clone();
    let support_columns = right_support
        .iter()
        .map(|(column, _)| *column)
        .collect::<Vec<_>>();
    // Canonical rank-one gauge: the left incidence is unit and the complete dyadic scale lives
    // in the receiver covector.  The outer product is unchanged, while the resident factor's
    // exponent no longer pays an artificial positive shift on the final output front.
    let right_values = right_support
        .into_iter()
        .map(|(_, value)| &derivation.u_scale * &value)
        .collect::<Vec<_>>();
    Ok(RankDerivationReceipt {
        defect: SparseDefect {
            ambient_rows: tower::VOCABULARY,
            ambient_columns: tower::HIDDEN,
            support_rows: vec![derivation.target_vocabulary],
            support_columns: support_columns.clone(),
            supported,
        },
        left: SupportedFactor {
            ambient: tower::VOCABULARY,
            support: vec![derivation.target_vocabulary],
            values: vec![Rat::one()],
        },
        right: SupportedFactor {
            ambient: tower::HIDDEN,
            support: support_columns.clone(),
            values: right_values,
        },
        zero_rank_foil: SparseDefect {
            ambient_rows: tower::VOCABULARY,
            ambient_columns: tower::HIDDEN,
            support_rows: vec![derivation.target_vocabulary],
            support_columns: support_columns.clone(),
            supported: zero,
        },
        separator: SeparatingReceiver {
            target: (derivation.target_vocabulary, support_columns[0]),
            predecessor: Rat::zero(),
            candidate,
        },
    })
}

pub fn candidate(shape: OverlayShape, terminal_rows: usize) -> FactorizedCandidate {
    FactorizedCandidate::new(
        LEFT_POPULATION,
        RIGHT_POPULATION,
        shape,
        1,
        terminal_rows,
        testimony(),
    )
}

pub fn materials(
    derivation: &CultivationDerivation,
) -> Result<(AlignedMaterial, AlignedMaterial), String> {
    let mut u = vec![Rat::zero(); tower::VOCABULARY];
    u[derivation.target_vocabulary] = Rat::one();
    let mut v = vec![Rat::zero(); tower::HIDDEN];
    v[derivation.pair.first] = &derivation.u_scale * &derivation.pair.control_annihilator[0];
    v[derivation.pair.second] = &derivation.u_scale * &derivation.pair.control_annihilator[1];
    Ok((
        to_aligned_material(&u).map_err(|error| error.to_string())?,
        to_aligned_material(&v).map_err(|error| error.to_string())?,
    ))
}

pub fn seal_product(
    directory: &Path,
    mounted: &MountedNativeRest,
    tokenizer_paths: &[(String, PathBuf)],
    fixture: &w3_fixture::FixtureManifest,
    derivation: CultivationDerivation,
    input_bound: u32,
    predecessor_bound: u32,
) -> Result<SealedProduct, String> {
    std::fs::create_dir_all(directory).map_err(|error| error.to_string())?;
    mounted.verify_still().map_err(|error| error.to_string())?;
    if mounted.codebook().codebook_sha256 != fixture.codebook_sha256 {
        return Err("fixture codebook identity disagrees with W1 rest".to_owned());
    }
    let predecessor = PredecessorProductIdentity {
        sha256: mounted.content_identity().sha256.clone(),
        extent: mounted.content_identity().extent,
    };
    let overlay = overlay_receipt(&derivation)?;
    let (left, right) = materials(&derivation)?;
    let fixture_digest = fixture.material_manifest_sha256.clone();
    let laws = laws();
    let graph_bytes = serde_json::to_vec(mounted.graphs()).map_err(|error| error.to_string())?;
    let codebook_graph = CodebookGraphIdentity {
        codebook_sha256: mounted.codebook().codebook_sha256.clone(),
        graph_identity: digest_bytes(&graph_bytes),
    };
    let morphology_path = directory.join("morphology.safetensors");
    write_native_morphology(
        &morphology_path,
        &NativeMorphologyInput {
            left_population: LEFT_POPULATION.to_owned(),
            right_population: RIGHT_POPULATION.to_owned(),
            left_shape: vec![tower::VOCABULARY, 1],
            right_shape: vec![1, tower::HIDDEN],
            left_exponent: left.exponent,
            right_exponent: right.exponent,
            rank: 1,
            resident_grain: GRAIN as u32,
            predecessor: predecessor.clone(),
            laws: laws.clone(),
            left: left.entries.clone(),
            right: right.entries.clone(),
        },
    )
    .map_err(|error| error.to_string())?;
    let rank_bytes = streamed::cultivation_overlay::canonical_rank_derivation_bytes(&overlay);
    let payload = MorphologyPayload::AlignedFactor(AlignedFactor {
        rows: tower::VOCABULARY as u32,
        columns: tower::HIDDEN as u32,
        rank: 1,
        resident_grain: GRAIN as u32,
        left_exponent: left.exponent,
        right_exponent: right.exponent,
        entry_octets: 8,
        left: left.entries.clone(),
        right: right.entries.clone(),
    });
    let payload_bytes = payload
        .canonical_bytes()
        .map_err(|error| error.to_string())?;
    let morphology = NativeOccurrence::read(
        morphology_path
            .to_str()
            .ok_or_else(|| "morphology path is not unicode".to_owned())?,
    )
    .map_err(|error| error.to_string())?;
    let support_base = (derivation.target_vocabulary as u64)
        .checked_mul(tower::HIDDEN as u64)
        .ok_or_else(|| "W3 reconstruction support overflow".to_owned())?;
    let reconstruction_support = [
        (
            derivation.pair.first,
            &derivation.pair.control_annihilator[0],
        ),
        (
            derivation.pair.second,
            &derivation.pair.control_annihilator[1],
        ),
    ]
    .into_iter()
    .filter_map(|(column, value)| (!value.is_zero()).then_some(support_base + column as u64))
    .collect();
    let input = CultivatedRestInput {
        predecessor: predecessor.clone(),
        codebook_graph,
        material_lineage_sha256: fixture_digest.clone(),
        ports: ports(input_bound, predecessor_bound),
        laws,
        payload,
        receipt: DerivationAdjointRankReceipt::from_derivation(&derivation, rank_bytes)
            .map_err(|error| error.to_string())?,
        reconstruction_fibre: ReconstructionFibre {
            candidates: vec![ReconstructionCandidate {
                identity: "phoenix.w3.derivation-fibre".to_owned(),
                payload_sha256: digest_bytes(&payload_bytes),
                support: reconstruction_support,
            }],
            omitted_sha256: None,
        },
        ablation: TargetedAblation {
            target: "phoenix.w3.rank-one".to_owned(),
            removed_payload_sha256: digest_bytes(&payload_bytes),
            predecessor: predecessor.clone(),
        },
        runtime_law: runtime_law(),
    };
    let product = CultivatedRest::seal_with_native_occurrence(input, &morphology)
        .map_err(|error| error.to_string())?;
    std::fs::write(
        directory.join("cultivated.rest"),
        product.encode().map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let mut companions = Vec::new();
    for (name, source) in tokenizer_paths {
        let destination = directory.join(name);
        if !destination.exists() {
            std::fs::hard_link(source, &destination).map_err(|error| error.to_string())?;
        }
        let mut companion =
            DirectoryCompanion::from_path(&destination).map_err(|error| error.to_string())?;
        companion.path = name.clone();
        companions.push(companion);
    }
    CultivatedRest::write_directory_manifest(
        directory,
        "cultivated.rest",
        "base.w1.rest",
        "morphology.safetensors",
        companions,
        predecessor.clone(),
    )
    .map_err(|error| error.to_string())?;
    Ok(SealedProduct { product })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn material_value(material: &AlignedMaterial, index: usize) -> Rat {
        let entry = BigInt::from(material.entries[index]);
        if material.exponent >= 0 {
            Rat::from_integer(entry << material.exponent as usize)
        } else {
            Rat::new(entry, BigInt::one() << (-material.exponent) as usize)
        }
    }

    #[test]
    fn derives_from_separate_scaled_w2_faces() {
        let unit = 1_i64 << 48;
        let development_hidden = vec![(2 * unit, 2 * unit), (unit, unit)];
        let control_hidden = vec![(0, 0), (unit, unit)];
        let development_potential = vec![(0, 0), (1, 1), (0, 1)];
        let derivation = derive_from_w2(
            &development_hidden,
            &control_hidden,
            &development_potential,
            0,
        )
        .expect("separate W2 faces must found a strict return");
        assert_eq!(derivation.target_potential, Rat::zero());
        assert!(derivation.strongest_competing_upper_face > derivation.target_potential);
        assert!(derivation.placed_activation.lower > Rat::zero());
    }

    #[test]
    fn canonical_rank_one_gauge_preserves_the_sparse_defect_exactly() {
        let derivation =
            holonic_engine::cultivation_derivation::derive_w3_return_at_grain_with_target(
                &holonic_engine::cultivation_derivation::HiddenPointSection::new(vec![
                    Rat::from_integer(BigInt::from(2)),
                    Rat::from_integer(BigInt::from(1)),
                ]),
                &holonic_engine::cultivation_derivation::HiddenPointSection::new(vec![
                    Rat::from_integer(BigInt::from(1)),
                    Rat::from_integer(BigInt::from(1)),
                ]),
                Rat::zero(),
                Rat::from_integer(BigInt::from(1)),
                0,
                7,
            )
            .expect("the bounded fixture admits a return");
        let receipt = overlay_receipt(&derivation).expect("rank receipt");
        assert_eq!(receipt.defect.supported, derivation.sparse_defect);
        assert_eq!(receipt.left.values, vec![Rat::one()]);
        let (left, right) = materials(&derivation).expect("canonical materials");
        assert_eq!(
            material_value(&left, derivation.target_vocabulary),
            Rat::one()
        );
        for (offset, column) in receipt.defect.support_columns.iter().enumerate() {
            assert_eq!(
                material_value(&right, *column),
                receipt.right.values[offset]
            );
        }
        for row in receipt.defect.support_rows.iter().copied() {
            for (offset, column) in receipt.defect.support_columns.iter().copied().enumerate() {
                assert_eq!(
                    material_value(&left, row) * material_value(&right, column),
                    receipt
                        .defect
                        .supported
                        .get(0, offset)
                        .expect("defect entry")
                        .clone()
                );
            }
        }
    }
}
