//! L4 — one situated Athena body emanates through six declared receiver deeds, receives actual
//! structural returns, and carries each non-scalar difference through the causal adjoint.

use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
};

use life::athena_native::{
    AddressedEmanationIngress, AddressedEmanationWorldReturn, AddressedMaterialOccurrence,
    CausalOperationWorldReturn, CausalResultCell, EmanationDeed, EmanationParticipant,
    EmanationSurface, EmanationVoice, ExteriorWorldReturnTestimony, MaterialFactorizationAperture,
    NativePotentialCellKind, PerspectiveChart, SituatedCultivatedAthenaRest,
    SituatedEmanationDifference, SituatedEmanationPassage,
};
use serde::Serialize;
use serde_json::json;

const L2_REST: &str = "output/the_causal_adjoint_cultivates_one_source_detached_athena_rest_l2/athena-situated-cultivated.rest";
const DEFAULT_OUT: &str = "output/the_perspective_return_changes_one_emanating_athena_body_l4";

#[derive(Serialize)]
struct EmanationCampaign<'a> {
    predecessor_rest_identity_sha256: &'a str,
    initial_body_identity_sha256: &'a str,
    final_body_identity_sha256: &'a str,
    surfaces: &'a [EmanationSurface],
    differences: &'a [SituatedEmanationDifference],
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let out = root.join(DEFAULT_OUT);
    if out.exists() {
        return Err(format!(
            "L4 output already exists; preserve or explicitly remove {} before another occurrence",
            out.display()
        ));
    }

    let rest_bytes = fs::read(root.join(L2_REST)).map_err(|error| error.to_string())?;
    let rest =
        SituatedCultivatedAthenaRest::read(&rest_bytes).map_err(|error| error.to_string())?;
    let rest_identity = rest.identity().to_owned();
    let material = AddressedMaterialOccurrence::found(
        "l4/material/ordinary-prose/addition",
        b"Describe the situated operation from my perspective, retaining its open derivation.",
        None,
        vec![
            "ordinary-English".to_owned(),
            "laboratory-address".to_owned(),
        ],
        vec!["later conversational and mathematical continuations".to_owned()],
    )
    .map_err(|error| error.to_string())?;
    let world = union_return(&material)?;
    let aperture =
        MaterialFactorizationAperture::found(&rest).map_err(|error| error.to_string())?;
    let factorization = aperture
        .factor(&material, &world)
        .map_err(|error| error.to_string())?;

    // The potential is founded from actual card-returned primary and mixed currents, not from the
    // prose bytes or a host-authored feature vector.
    let mut resident = rest.mount().map_err(|error| error.to_string())?;
    let resident_return = resident.conduct().map_err(|error| error.to_string())?;
    let apparatus = resident_return.apparatus.clone();
    let rest = resident.into_rest();

    let brandon = EmanationParticipant {
        occurrence: "participant-occurrence/brandon/l4".to_owned(),
        identity: "participant/brandon".to_owned(),
        proper_name: "Brandon".to_owned(),
    };
    let athena = EmanationParticipant {
        occurrence: "participant-occurrence/athena/l4".to_owned(),
        identity: "participant/athena".to_owned(),
        proper_name: "Athena".to_owned(),
    };
    let ingress = AddressedEmanationIngress::found(
        "l4/ingress/original",
        material.occurrence.clone(),
        b"Describe the situated operation from my perspective, retaining its open derivation.",
        None,
        brandon.identity.clone(),
        vec![brandon.clone(), athena],
        EmanationDeed::Describe,
        vec![
            "preserve the exact successor separator".to_owned(),
            "retain the open reconstruction fibre".to_owned(),
        ],
        PerspectiveChart::found("l4/chart/referent", None, None)
            .map_err(|error| error.to_string())?,
        vec![
            "l4/chronology/material-return".to_owned(),
            "l4/chronology/resident-current".to_owned(),
            "l4/chronology/emanation".to_owned(),
        ],
        vec!["successor histories beyond the admitted one-member extension".to_owned()],
        vec!["later receiver families remain open".to_owned()],
    )
    .map_err(|error| error.to_string())?;
    let mut passage =
        SituatedEmanationPassage::found(rest, factorization, resident_return, ingress)
            .map_err(|error| error.to_string())?;
    let initial_body_identity = passage.body_identity().to_owned();
    let initial_potential = passage.potential().clone();
    let complete_family = passage
        .potential()
        .cells
        .iter()
        .map(|cell| cell.body.kind())
        .collect::<BTreeSet<_>>();
    let mut reverse_order = complete_family.iter().copied().collect::<Vec<_>>();
    reverse_order.reverse();
    let compressed_family = BTreeSet::from([
        NativePotentialCellKind::ExactConsequence,
        NativePotentialCellKind::Participant,
    ]);

    let mut surfaces = Vec::new();
    let mut differences = Vec::new();

    surfaces.push(passage.emanate().map_err(|error| error.to_string())?);
    differences.push(receive(
        &mut passage,
        surfaces.last().unwrap(),
        "identify-return",
        Some(EmanationDeed::Identify),
        Some(
            PerspectiveChart::found(
                "l4/chart/brandon-speaks",
                Some(brandon.identity.clone()),
                None,
            )
            .map_err(|error| error.to_string())?,
        ),
        None,
        None,
        None,
    )?);

    surfaces.push(passage.emanate().map_err(|error| error.to_string())?);
    differences.push(receive(
        &mut passage,
        surfaces.last().unwrap(),
        "infer-return",
        Some(EmanationDeed::Infer),
        Some(
            PerspectiveChart::found(
                "l4/chart/brandon-addressed",
                None,
                Some(brandon.identity.clone()),
            )
            .map_err(|error| error.to_string())?,
        ),
        None,
        None,
        Some(compressed_family),
    )?);

    surfaces.push(passage.emanate().map_err(|error| error.to_string())?);
    differences.push(receive(
        &mut passage,
        surfaces.last().unwrap(),
        "explain-return",
        Some(EmanationDeed::Explain),
        Some(
            PerspectiveChart::found("l4/chart/exterior-observer", None, None)
                .map_err(|error| error.to_string())?,
        ),
        None,
        None,
        Some(complete_family.clone()),
    )?);

    surfaces.push(passage.emanate().map_err(|error| error.to_string())?);
    differences.push(receive(
        &mut passage,
        surfaces.last().unwrap(),
        "rewrite-return",
        Some(EmanationDeed::Rewrite),
        None,
        Some(EmanationVoice::Passive),
        Some(reverse_order),
        None,
    )?);

    surfaces.push(passage.emanate().map_err(|error| error.to_string())?);
    differences.push(receive(
        &mut passage,
        surfaces.last().unwrap(),
        "derive-return",
        Some(EmanationDeed::Derive),
        None,
        Some(EmanationVoice::Active),
        Some(complete_family.iter().copied().collect()),
        None,
    )?);

    surfaces.push(passage.emanate().map_err(|error| error.to_string())?);
    differences.push(receive(
        &mut passage,
        surfaces.last().unwrap(),
        "final-continuation-return",
        None,
        None,
        None,
        None,
        None,
    )?);
    let final_body_identity = passage.body_identity().to_owned();
    let returned_rest = passage.into_rest().map_err(|error| error.to_string())?;

    let texts = surfaces
        .iter()
        .map(|surface| surface.text.as_str())
        .collect::<BTreeSet<_>>();
    let signatures = surfaces
        .iter()
        .map(|surface| surface.native_successor_identity_sha256.as_str())
        .collect::<BTreeSet<_>>();
    let deeds = surfaces
        .iter()
        .map(|surface| surface.deed)
        .collect::<BTreeSet<_>>();
    let first_person = surfaces[1]
        .participant_faces
        .iter()
        .find(|face| face.participant_identity == brandon.identity)
        .map(|face| face.exterior_surface.as_str())
        == Some("I");
    let second_person = surfaces[2]
        .participant_faces
        .iter()
        .find(|face| face.participant_identity == brandon.identity)
        .map(|face| face.exterior_surface.as_str())
        == Some("you");
    let proper_name = surfaces[0]
        .participant_faces
        .iter()
        .find(|face| face.participant_identity == brandon.identity)
        .map(|face| face.exterior_surface.as_str())
        == Some("Brandon");
    let compressed = !surfaces[2].hidden_reconstruction_fibre.is_empty();
    let expanded = surfaces[3].hidden_reconstruction_fibre.is_empty();
    let all_differences_nonzero = differences.iter().all(|difference| {
        !difference.changed_atoms.is_empty()
            && difference
                .oriented_difference
                .iter()
                .any(|coefficient| *coefficient != 0)
            && difference.participant_lineage_preserved
    });
    let revoice_preserved_content = differences[3].causal_content_preserved;
    let all_pass = texts.len() == surfaces.len()
        && signatures.len() == surfaces.len()
        && deeds
            == BTreeSet::from([
                EmanationDeed::Describe,
                EmanationDeed::Identify,
                EmanationDeed::Infer,
                EmanationDeed::Explain,
                EmanationDeed::Rewrite,
                EmanationDeed::Derive,
            ])
        && first_person
        && second_person
        && proper_name
        && compressed
        && expanded
        && all_differences_nonzero
        && revoice_preserved_content
        && initial_body_identity != final_body_identity
        && returned_rest.identity() == rest_identity
        && !apparatus.device.is_empty()
        && !apparatus.cpu_semantic_replay_after_device
        && !apparatus.invariant_transport_reuploaded;
    if !all_pass {
        return Err(format!(
            "L4 gate failed: distinct_texts={}/{} distinct_signatures={}/{} deeds={} first={first_person} second={second_person} name={proper_name} compressed={compressed} expanded={expanded} nonzero={all_differences_nonzero} revoice={revoice_preserved_content} body_changed={} rest_preserved={} cuda={} no_cpu={} no_reupload={}",
            texts.len(),
            surfaces.len(),
            signatures.len(),
            surfaces.len(),
            deeds.len(),
            initial_body_identity != final_body_identity,
            returned_rest.identity() == rest_identity,
            apparatus.device.starts_with("CUDA"),
            !apparatus.cpu_semantic_replay_after_device,
            !apparatus.invariant_transport_reuploaded,
        ));
    }

    fs::create_dir_all(&out).map_err(|error| error.to_string())?;
    write_json(
        &out.join("00-standing-body-and-native-potential.json"),
        &json!({
            "rest_identity_sha256": rest_identity,
            "initial_body_identity_sha256": initial_body_identity,
            "potential": initial_potential,
            "resident_apparatus": apparatus,
        }),
    )?;
    write_json(
        &out.join("01-six-perspective-sensitive-emanations.json"),
        &EmanationCampaign {
            predecessor_rest_identity_sha256: &rest_identity,
            initial_body_identity_sha256: &initial_body_identity,
            final_body_identity_sha256: &final_body_identity,
            surfaces: &surfaces,
            differences: &differences,
        },
    )?;
    for (at, surface) in surfaces.iter().enumerate() {
        fs::write(
            out.join(format!("surface-{at:02}-{:?}.md", surface.deed).to_lowercase()),
            &surface.text,
        )
        .map_err(|error| error.to_string())?;
    }
    write_json(
        &out.join("02-l4-primary-grade.json"),
        &json!({
            "status": "passed",
            "truth_status": ["established-bounded", "implemented-exact", "measured"],
            "one_rest_identity_preserved": true,
            "one_continuing_body_changed": true,
            "six_declared_deeds_returned_distinct_native_successors": true,
            "six_surfaces_are_nonidentical": true,
            "participant_lineage_survived_i_you_name_chart": true,
            "revoice_preserved_causal_content": true,
            "compression_retained_hidden_reconstruction_fibre": true,
            "expansion_reopened_complete_cell_population": true,
            "every_returned_difference_is_nonzero_and_causal_adjoint_bearing": true,
            "candidate_strings_generated_or_ranked": false,
            "caller_fixed_clause_cell_token_or_answer_extent": false,
            "cpu_semantic_fallback": false,
        }),
    )?;
    println!(
        "L4 passed: one body returned six distinct deed/perspective surfaces and five refinement returns plus one continuation return changed its addressed morphology through exact causal adjoints."
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn receive(
    passage: &mut SituatedEmanationPassage,
    surface: &EmanationSurface,
    suffix: &str,
    deed: Option<EmanationDeed>,
    perspective: Option<PerspectiveChart>,
    voice: Option<EmanationVoice>,
    kind_order: Option<Vec<NativePotentialCellKind>>,
    future_receiver_family: Option<BTreeSet<NativePotentialCellKind>>,
) -> Result<SituatedEmanationDifference, String> {
    let continuation = (suffix == "final-continuation-return")
        .then(|| "l4/continuation/future-mathematical-world-tube".to_owned());
    let returned = AddressedEmanationWorldReturn::found(
        format!("l4/world-return/{suffix}"),
        surface.occurrence.clone(),
        format!("structural returned occurrence {suffix}").as_bytes(),
        deed,
        perspective,
        voice,
        kind_order,
        future_receiver_family,
        None,
        continuation,
        vec!["future receiver histories remain open".to_owned()],
    )
    .map_err(|error| error.to_string())?;
    passage
        .receive_world_return(returned)
        .map_err(|error| error.to_string())
}

fn union_return(
    material: &AddressedMaterialOccurrence,
) -> Result<CausalOperationWorldReturn, String> {
    let left = vec!["left/0".to_owned(), "left/1".to_owned()];
    let right = vec!["right/0".to_owned(), "right/1".to_owned()];
    let result_cells = left
        .iter()
        .map(|member| CausalResultCell {
            occurrence: format!("result/{member}"),
            left_member: Some(member.clone()),
            right_member: None,
        })
        .chain(right.iter().map(|member| CausalResultCell {
            occurrence: format!("result/{member}"),
            left_member: None,
            right_member: Some(member.clone()),
        }))
        .collect();
    let apparatus = ExteriorWorldReturnTestimony::found(
        "l4/apparatus/union-return",
        "causal-population-return",
        true,
        b"4",
        vec!["successor histories outside the declared extension".to_owned()],
    )
    .map_err(|error| error.to_string())?;
    CausalOperationWorldReturn::found(
        "l4/world/union-return",
        material.occurrence.clone(),
        left,
        right,
        result_cells,
        apparatus,
        vec!["later operation interventions remain open".to_owned()],
    )
    .map_err(|error| error.to_string())
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    fs::write(path, bytes).map_err(|error| error.to_string())
}

fn workspace_root() -> Result<PathBuf, String> {
    let mut path = env::current_dir().map_err(|error| error.to_string())?;
    loop {
        if path.join("Cargo.toml").is_file() && path.join("blueprint").is_dir() {
            return Ok(path);
        }
        if !path.pop() {
            return Err("could not locate the holonics workspace root".to_owned());
        }
    }
}
