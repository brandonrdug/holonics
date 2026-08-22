//! **Deed P5: the intervention atlas is repeated on the NATIVE arm — predecessor and cultivated
//! successor — the four bodies are placed under one declared material, and the thirteen-item
//! Phoenix grade is assembled item by item WITH EACH ITEM'S DECLARED APERTURE NAMED.**
//!
//! Plan: `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md` §0 (the
//! indivisible thirteen-item grade), §8 Deed P5, §11. Owners composed:
//! `soma/life/src/atlas_cultivation.rs` (the cultivation law, P3's, plus this deed's rest
//! interventions), `soma/life/src/phoenix_rest.rs` (the seal, the mount, the refusals),
//! `crates/holonic-engine/src/receiver_exact_compression.rs` (the separator words).
//!
//! # The honesty bar, which is the deed
//!
//! This driver's product is a GRADE, and a grade whose apertures are not named is an assertion.
//! Every item below carries the deed that returned it, the aperture that deed DECLARED, and the
//! falsifier that would reopen it. Two boundaries govern the whole reading and are printed first:
//!
//! - **The lift (P1) is the lift LAW on bounded real families**, not the whole foreign map lifted.
//!   Its own record declares hidden window 64 of 2,560, head window 16 of 256, family 0 of 2.
//! - **The native arm (ARM N) is INDEPENDENT of the foreign source by construction.** It is not a
//!   Gemma lift. Its material is eight declared canon documents; its codec is the native lexical
//!   reading; no Φ in this tree carries the source codebook to the native vocabulary. So the
//!   four-body table compares arms that share MATERIAL and receivers, never topology.
//!
//! # What is new here, stated as the absent relation
//!
//! Station D dissected the SOURCE by intervention. Nothing repeated that discipline on the native
//! arm, because the native arm's material is a sparse integer transport addressed by (class, germ)
//! and Station D's two intervention laws address a dense device section by row and column. The
//! three new interventions — a germ family, a suffix-height band, a germ-label transposition — are
//! in `atlas_cultivation` beside the cultivation they dissect, and the four that already stood
//! (the delta withdrawal, the cultivation itself, the extent-region withdrawal, the codec variant)
//! are composed, not restated.
//!
//! ```text
//! cargo build --release -p life --bin eros
//! cargo run --release -q -p life --example the_reborn_body_is_dissected_and_the_grade_is_assembled
//! ```

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::Write as _;
use std::path::Path;
use std::process::Command;

use holonic_engine::receiver_exact_compression::{
    exhibit_collapsed_within, refine, separated_pair_population, InputId, ItemId, Observation,
    ObservedSystem, ReceiverId,
};
use life::atlas_cultivation::{
    class_heights, commit, conduct, derive, intervene, read_residual, unit_covector, withdraw,
    AthenaRest, ConductedSection, CultivationDelta, DepositIncidence, FoundedSpecies,
    MetricDeclaration, RestIntervention, EXTENT_REGION,
};
use life::causal_language::{
    lexical_tokens, lexical_tokens_under, token_germs_public, LexicalAperture,
};
use life::phoenix_rest::{
    content_bar, cultivate, extents_of, loss_digest, mount_atlas, read_rest, regions,
};

const OUT: &str = "output/the_reborn_body_is_dissected";
/// The P4 seal: the P0 rest plus the one native region a deposit reads. Its extent region stripped
/// is octet-identical to the committed P0 artifact, and this driver re-takes that identity.
const P4_SEAL: &str = "output/the_application_infers/rest.safetensors";
const P0_REST: &str = "output/the_native_baseline_conducts/rest.safetensors";
const P3_SUCCESSOR: &str = "output/the_rest_is_cultivated/successor-rest.safetensors";
const STATION_D: &str = "output/the_source_is_dissected/dissection-5-tokens-grain-48-terms-14.form";
/// P3's declared development material — the same subject, so ARM N-post here is P3's successor.
const DEVELOPMENT: &str = "canon/TABLET_THE_CHART.md";

/// **The probes, fixed before any intervention and never used as material.** The P0 eight are the
/// committed baseline's own; the three development-subject probes and the two held-out-subject
/// probes are P3's, carried unchanged so the two deeds read the same faces.
const PROBES: &[(&str, &str)] = &[
    ("P0", "the receiver"),
    ("P0", "a compression is a codec"),
    ("P0", "hexis is rested conditional transport"),
    ("P0", "the suffix link"),
    ("P0", "cultivation relative to inherited rest"),
    ("P0", "the document law"),
    ("P0", "an operation is a construction"),
    ("P0", "the quantum wobbleflux"),
    ("DEV", "a coordinate system is a receiver"),
    ("DEV", "a radical is a chart that forgets a winding"),
    ("DEV", "the chart refuses"),
    (
        "HELD-OUT",
        "a phase is a maximal connected transport stratum",
    ),
    ("HELD-OUT", "a phase transition is a discrete event"),
];

/// **The one material the four-body table declares.** Station D's fixed predecessor conducted this
/// text through the source's own tokenizer at 5 tokens; ARM N conducts the same text through the
/// native lexical codec. The arms share the material; they share nothing else.
const SHARED_MATERIAL: &str = "The capital of France is";

/// The committed P0/P3 conduct table, cited rather than regenerated: what the card returned for the
/// eight prompts (P0's receipt) and what P3's CPU reading agreed with, 8 of 8.
const COMMITTED_P0_CONDUCT: &[(&str, u32, u64, usize)] = &[
    ("the receiver", 7812, 17, 12),
    ("a compression is a codec", 48389, 1, 1),
    ("hexis is rested conditional transport", 56428, 1, 1),
    ("the suffix link", 1093, 15, 11),
    ("cultivation relative to inherited rest", 56966, 3, 2),
    ("the document law", 25667, 1, 1),
    ("an operation is a construction", 42299, 1, 1),
    ("the quantum wobbleflux", 0, 47825, 5385),
];

macro_rules! line {
    ($form:expr, $($argument:tt)*) => {{
        let _ = writeln!($form, $($argument)*);
    }};
}

fn main() -> Result<(), String> {
    let start = std::time::Instant::now();
    std::fs::create_dir_all(OUT).map_err(|error| error.to_string())?;
    let mut receipt = String::new();
    let mut atlas_form = String::new();
    let mut grade_form = String::new();

    // =========================================================================================
    // 0. the honesty bar, printed before anything is measured
    // =========================================================================================
    line!(
        receipt,
        "THE REBORN BODY IS DISSECTED AND THE GRADE IS ASSEMBLED — Deed P5"
    );
    line!(receipt, "");
    line!(
        receipt,
        "THE HONESTY BAR, FIRST — and it governs every line below"
    );
    for row in HONESTY_BAR {
        line!(receipt, "  {row}");
    }
    line!(receipt, "");
    line!(receipt, "THE FOUR BODIES, AS THIS TREE HOLDS THEM");
    for row in FOUR_BODIES {
        line!(receipt, "  {row}");
    }
    line!(receipt, "");

    // =========================================================================================
    // 1. the fixed predecessor, verified before anything is intervened
    // =========================================================================================
    line!(
        receipt,
        "== 1. THE FIXED PREDECESSOR — verified before any intervention =="
    );
    let (pre_octets, pre) = read_rest(Path::new(P4_SEAL)).map_err(|error| error.to_string())?;
    let committed_p0 = std::fs::read(P0_REST).map_err(|error| error.to_string())?;
    let mut stripped = pre.clone();
    stripped.extent.clear();
    let stripped_octets = stripped
        .write_container()
        .map_err(|error| error.to_string())?;
    let strip_identical = stripped_octets == committed_p0;
    line!(receipt, "  ARM N-pre        {P4_SEAL}");
    line!(
        receipt,
        "    {} octets · {} classes · {} transitions · {} vocabulary · tree height {} · {} extents",
        pre_octets.len(),
        pre.classes(),
        pre.transitions(),
        pre.vocabulary.len(),
        pre.height,
        pre.extent.len()
    );
    line!(
        receipt,
        "    with athena.class.extent STRIPPED, against the committed P0 artifact: {} ({} against {} octets)",
        if strip_identical { "OCTET-IDENTICAL" } else { "DIFFERENT" },
        stripped_octets.len(),
        committed_p0.len()
    );
    if !strip_identical {
        return Err("the fixed predecessor is not the committed P0 rest".to_owned());
    }
    // Nothing in this deed writes a committed artifact; the working copies live under OUT.
    std::fs::write(
        format!("{OUT}/copy-of-the-predecessor.safetensors"),
        &pre_octets,
    )
    .map_err(|error| error.to_string())?;

    line!(receipt, "");
    line!(receipt, "  AND ITS CONDUCT IS THE COMMITTED ONE — the R1 face against P0's card receipt, cited not regenerated");
    line!(
        receipt,
        "    {:<44} {:>7} {:>9} {:>8} {}",
        "prompt",
        "class",
        "standing",
        "depth-0",
        "agrees"
    );
    let mut agreed = 0usize;
    for (prompt, class, standing, depth_zero) in COMMITTED_P0_CONDUCT {
        let section = conduct(&pre, prompt, &lexical_tokens(prompt));
        let zero = section
            .offered
            .iter()
            .filter(|(_, _, depth)| *depth == 0)
            .count();
        let agrees =
            section.class == *class && section.standing == *standing && zero == *depth_zero;
        agreed += usize::from(agrees);
        line!(
            receipt,
            "    {:<44} {:>7} {:>9} {:>8} {}",
            format!("{prompt:?}"),
            section.class,
            section.standing,
            zero,
            if agrees { "yes" } else { "NO" }
        );
    }
    line!(
        receipt,
        "    {agreed} of {} agree with the committed receipt exactly",
        COMMITTED_P0_CONDUCT.len()
    );
    if agreed != COMMITTED_P0_CONDUCT.len() {
        return Err("the predecessor's conduct is not the committed one".to_owned());
    }

    // =========================================================================================
    // 2. the declared receiver family and the probes — before the panel
    // =========================================================================================
    line!(receipt, "");
    line!(
        receipt,
        "== 2. THE RECEIVER FAMILY AND THE PROBES — declared BEFORE the panel =="
    );
    for row in RECEIVER_FAMILY {
        line!(receipt, "  {row}");
    }
    line!(
        receipt,
        "  the probes, {} of them, fixed and never used as material:",
        PROBES.len()
    );
    for (role, probe) in PROBES {
        line!(receipt, "    {role:<9} {probe:?}");
    }

    // =========================================================================================
    // 3. ARM N-post — the cultivated successor, from the rest alone
    // =========================================================================================
    line!(receipt, "");
    line!(
        receipt,
        "== 3. ARM N-post — THE CULTIVATED SUCCESSOR, mounted from the rest alone =="
    );
    let development = std::fs::read_to_string(DEVELOPMENT).map_err(|error| error.to_string())?;
    let metric = MetricDeclaration::identity();
    let cultivated = cultivate(&pre, P4_SEAL, DEVELOPMENT, &development, &metric)
        .map_err(|error| error.to_string())?;
    let post = cultivated.successor.clone();
    let delta = cultivated.delta.clone();
    line!(
        receipt,
        "  the exposure          {DEVELOPMENT} · {} germ occurrences · aperture LexicalAperture::inherited",
        cultivated.germs
    );
    line!(
        receipt,
        "  the successor         {} classes · {} transitions · {} vocabulary · height {}",
        post.classes(),
        post.transitions(),
        post.vocabulary.len(),
        post.height
    );
    line!(
        receipt,
        "  the derived delta     germs +{} · classes +{} of which {} splits · transitions founded {} ({} inside the standing body) · links rebased {} · standings moved at {}",
        delta.germs_founded.len(),
        delta.classes_after - delta.classes_before,
        delta.classes_split(),
        delta.transitions_founded.len(),
        delta.transitions_founded_on_standing(),
        delta.suffix_rebased.len(),
        delta.standing_increments.len()
    );
    line!(
        receipt,
        "  commit == derive      the committed container against the container the transport itself emits, on the germ side: {}",
        if cultivated.germ_side_identical { "OCTET-IDENTICAL" } else { "DIFFERENT" }
    );

    // The committed P3 successor is the independent predecessor for this arm. Compared by ARRAY,
    // which is stronger than a metadata-carrying octet compare and does not need P3's declarations.
    let (_, p3_successor) =
        read_rest(Path::new(P3_SUCCESSOR)).map_err(|error| error.to_string())?;
    let arrays_equal = post.indptr == p3_successor.indptr
        && post.germ == p3_successor.germ
        && post.target == p3_successor.target
        && post.standing == p3_successor.standing
        && post.suffix == p3_successor.suffix
        && post.vocabulary == p3_successor.vocabulary
        && post.height == p3_successor.height;
    line!(
        receipt,
        "  against the COMMITTED P3 successor, array by array (indptr, germ, target, standing, suffix, vocabulary, height): {}",
        if arrays_equal { "IDENTICAL" } else { "DIFFERENT" }
    );
    if !arrays_equal {
        return Err("this deed's ARM N-post is not the committed P3 successor".to_owned());
    }
    line!(
        receipt,
        "  so ARM N-post here IS P3's committed successor, reached from the rest alone rather than from the corpus."
    );

    // =========================================================================================
    // 4. the native dissection atlas
    // =========================================================================================
    let heights = class_heights(&pre);
    let mut census: BTreeMap<u32, usize> = BTreeMap::new();
    for class in 0..pre.classes() {
        *census.entry(heights[class]).or_default() += 1;
    }
    let mut target_census: BTreeMap<u32, usize> = BTreeMap::new();
    for target in &pre.target {
        *target_census.entry(heights[*target as usize]).or_default() += 1;
    }

    line!(
        atlas_form,
        "THE NATIVE DISSECTION ATLAS — Deed P5, ARM N predecessor and cultivated successor"
    );
    line!(atlas_form, "");
    line!(
        atlas_form,
        "Station D's discipline, on the native arm: one fixed predecessor per body, a matched"
    );
    line!(atlas_form, "sibling per taxon, one declared receiver family, the caused change, the shortest separating");
    line!(
        atlas_form,
        "history, the unchanged unrelated control MEASURED, and the remaining ambiguity."
    );
    line!(atlas_form, "");
    for row in RECEIVER_FAMILY {
        line!(atlas_form, "  {row}");
    }
    line!(atlas_form, "");
    line!(
        atlas_form,
        "THE CLASS-HEIGHT CENSUS of the predecessor, read off athena.class.suffix alone"
    );
    line!(atlas_form, "  height  classes  transitions arriving");
    for (height, classes) in &census {
        line!(
            atlas_form,
            "  {height:>6}  {classes:>7}  {:>7}",
            target_census.get(height).copied().unwrap_or(0)
        );
    }

    // ---- the declared intervention parameters, by RULE and before any effect is read ----
    let mut family_by_size: BTreeMap<u64, usize> = BTreeMap::new();
    for germ in &pre.germ {
        *family_by_size.entry(*germ).or_default() += 1;
    }
    let probe_surfaces: BTreeSet<String> = PROBES
        .iter()
        .flat_map(|(_, probe)| lexical_tokens(probe))
        .collect();
    // RULE: the withdrawn family is the largest transport family carried by a probe's own tokens,
    // so the intervention is one the declared receivers can reach; ties by germ index.
    let withdrawn_family = pre
        .vocabulary
        .iter()
        .enumerate()
        .filter(|(_, surface)| probe_surfaces.contains(*surface))
        .max_by_key(|(at, _)| {
            (
                family_by_size.get(&(*at as u64)).copied().unwrap_or(0),
                usize::MAX - *at,
            )
        })
        .map(|(at, surface)| (at as u64, surface.clone()))
        .ok_or("no probe surface is in the vocabulary")?;
    // RULE: the band is the two deepest heights the census reports.
    let deepest: Vec<u32> = census.keys().rev().take(2).copied().collect();
    let band = (
        *deepest.iter().min().ok_or("the census is empty")?,
        *deepest.iter().max().ok_or("the census is empty")?,
    );
    // RULE: the transposed pair is the two largest transport families overall, ties by germ index.
    let mut by_size: Vec<(u64, usize)> = family_by_size.iter().map(|(g, n)| (*g, *n)).collect();
    by_size.sort_by_key(|(germ, size)| (usize::MAX - *size, *germ));
    let transposed = (by_size[0].0, by_size[1].0);

    line!(atlas_form, "");
    line!(
        atlas_form,
        "THE INTERVENTION PARAMETERS, DECLARED BY RULE — each rule fixed before its effect is read"
    );
    line!(
        atlas_form,
        "  germ family      RULE: the largest transport family whose surface a declared probe carries, ties by germ index"
    );
    line!(
        atlas_form,
        "                   -> germ {} ({:?}), carried by {} transitions",
        withdrawn_family.0,
        withdrawn_family.1,
        family_by_size
            .get(&withdrawn_family.0)
            .copied()
            .unwrap_or(0)
    );
    line!(
        atlas_form,
        "  height band      RULE: the two deepest heights the class-height census reports"
    );
    line!(
        atlas_form,
        "                   -> heights {}..={} · {} transitions arrive there",
        band.0,
        band.1,
        target_census.get(&band.0).copied().unwrap_or(0)
            + target_census.get(&band.1).copied().unwrap_or(0)
    );
    line!(
        atlas_form,
        "  transposition    RULE: the two largest transport families overall, ties by germ index"
    );
    line!(
        atlas_form,
        "                   -> germs {} ({:?}, {} transitions) and {} ({:?}, {} transitions)",
        transposed.0,
        pre.vocabulary[transposed.0 as usize],
        by_size[0].1,
        transposed.1,
        pre.vocabulary[transposed.1 as usize],
        by_size[1].1
    );

    // ---- the panel ----
    let mut taxa: Vec<TaxonReading> = Vec::new();

    // T1 — cultivation itself, pre against post
    taxa.push(read_taxon(
        "cultivation (the deposit itself)",
        "ARM N-pre -> ARM N-post",
        &format!(
            "the exposure of {DEVELOPMENT} deposited: +{} germs, +{} classes ({} splits), +{} transitions",
            delta.germs_founded.len(),
            delta.classes_after - delta.classes_before,
            delta.classes_split(),
            delta.transitions_founded.len()
        ),
        &pre,
        &post,
        Matched {
            transitions_before: pre.transitions(),
            transitions_after: post.transitions(),
            population_preserved: false,
            classes_touched: delta.standing_increments.len(),
        },
        "a HELD-OUT subject's probe at the depth-0 support: the material never touched it",
    ));

    // T2 — the delta withdrawn in place (P3's ablation, re-taken on this body)
    let restored = withdraw(&post, &delta).map_err(|error| error.to_string())?;
    let restored_octets = restored
        .write_container()
        .map_err(|error| error.to_string())?;
    let ablation_identical = restored_octets == stripped_octets;
    taxa.push(read_taxon(
        "the delta withdrawn in place (the cultivation ablation)",
        "ARM N-post -> the withdrawal",
        &format!(
            "withdraw(successor, delta): {} classes -> {}, {} transitions -> {}, vocabulary {} -> {}; against the predecessor container: {}",
            post.classes(),
            restored.classes(),
            post.transitions(),
            restored.transitions(),
            post.vocabulary.len(),
            restored.vocabulary.len(),
            if ablation_identical { "OCTET-IDENTICAL" } else { "DIFFERENT" }
        ),
        &post,
        &restored,
        Matched {
            transitions_before: post.transitions(),
            transitions_after: restored.transitions(),
            population_preserved: false,
            classes_touched: delta.standing_increments.len(),
        },
        "every probe: the withdrawal must return the PREDECESSOR's face, so the control is the whole panel",
    ));

    // T3 — the germ family, on both bodies
    for (label, body) in [("ARM N-pre", &pre), ("ARM N-post", &post)] {
        let germ = germ_index(body, &withdrawn_family.1)?;
        let (sibling, sibling_receipt) =
            intervene(body, &RestIntervention::WithdrawGermFamily { germ })
                .map_err(|error| error.to_string())?;
        taxa.push(read_taxon(
            &format!("the germ family {:?} withdrawn", withdrawn_family.1),
            label,
            &sibling_receipt.declaration,
            body,
            &sibling,
            Matched {
                transitions_before: sibling_receipt.transitions_before,
                transitions_after: sibling_receipt.transitions_after,
                population_preserved: sibling_receipt.population_preserved,
                classes_touched: sibling_receipt.classes_touched.len(),
            },
            "the WALK face of every probe whose tokens do not carry the surface: the walk never takes that arc",
        ));
    }

    // T4 — the suffix-height band, on both bodies
    for (label, body) in [("ARM N-pre", &pre), ("ARM N-post", &post)] {
        let (sibling, sibling_receipt) = intervene(
            body,
            &RestIntervention::WithdrawHeightBand {
                low: band.0,
                high: band.1,
            },
        )
        .map_err(|error| error.to_string())?;
        taxa.push(read_taxon(
            &format!("the suffix-height band {}..={} withdrawn (the scale intervention)", band.0, band.1),
            label,
            &sibling_receipt.declaration,
            body,
            &sibling,
            Matched {
                transitions_before: sibling_receipt.transitions_before,
                transitions_after: sibling_receipt.transitions_after,
                population_preserved: sibling_receipt.population_preserved,
                classes_touched: sibling_receipt.classes_touched.len(),
            },
            "a probe whose whole ladder sits outside the band: nothing on it arrives at a banded class",
        ));
    }

    // T5 — the germ-label transposition, on both bodies
    for (label, body) in [("ARM N-pre", &pre), ("ARM N-post", &post)] {
        let left = germ_index(body, &pre.vocabulary[transposed.0 as usize])?;
        let right = germ_index(body, &pre.vocabulary[transposed.1 as usize])?;
        let (sibling, sibling_receipt) =
            intervene(body, &RestIntervention::TransposeGermLabels { left, right })
                .map_err(|error| error.to_string())?;
        taxa.push(read_taxon(
            &format!(
                "the germ labels {:?} and {:?} transposed (the adjacency permutation)",
                pre.vocabulary[transposed.0 as usize], pre.vocabulary[transposed.1 as usize]
            ),
            label,
            &sibling_receipt.declaration,
            body,
            &sibling,
            Matched {
                transitions_before: sibling_receipt.transitions_before,
                transitions_after: sibling_receipt.transitions_after,
                population_preserved: sibling_receipt.population_preserved,
                classes_touched: sibling_receipt.classes_touched.len(),
            },
            "the WALK face of a probe carrying neither surface",
        ));
    }

    // T6 — the extent region withdrawn: a typed refusal at the deposit, conduct bit-identical
    let mut extentless_pre = pre.clone();
    extentless_pre.extent.clear();
    let mut extentless_post = post.clone();
    extentless_post.extent.clear();
    let mut extent_refusals: Vec<(String, String)> = Vec::new();
    for (label, body) in [
        ("ARM N-pre", &extentless_pre),
        ("ARM N-post", &extentless_post),
    ] {
        match mount_atlas(body, label) {
            Ok(_) => extent_refusals.push((
                label.to_owned(),
                "ADMITTED — the region is not load-bearing".to_owned(),
            )),
            Err(refusal) => extent_refusals.push((label.to_owned(), refusal.to_string())),
        }
    }
    for (label, body, stripped_body) in [
        ("ARM N-pre", &pre, &extentless_pre),
        ("ARM N-post", &post, &extentless_post),
    ] {
        taxa.push(read_taxon(
            "the athena.class.extent region withdrawn (the typed refusal face)",
            label,
            &format!(
                "the container's {EXTENT_REGION} region cleared: {} extents -> {}; the three declared conduct laws read none of them",
                body.extent.len(),
                stripped_body.extent.len()
            ),
            body,
            stripped_body,
            Matched {
                transitions_before: body.transitions(),
                transitions_after: stripped_body.transitions(),
                population_preserved: true,
                classes_touched: 0,
            },
            "EVERY probe at EVERY face: conduct reads the transport, the standings, the links and the vocabulary, and none of them moved",
        ));
    }

    // T7 — the codec variant sibling: the same subject through a declared lexical aperture
    let variant_tokens = lexical_tokens_under(&development, &LexicalAperture::runs_are_maximal());
    let variant_germs =
        token_germs_public(&variant_tokens).map_err(|error| format!("{error:?}"))?;
    let variant_surfaces =
        life::atlas_cultivation::surfaces_of(&variant_germs).map_err(|error| error.to_string())?;
    let variant_residual = read_residual(&pre, "codec-variant", &variant_surfaces);
    let mut variant_atlas = mount_atlas(&pre, P4_SEAL).map_err(|error| error.to_string())?;
    let variant_lineage = variant_atlas
        .absorb_returning_lineage(&variant_germs)
        .map_err(|error| format!("{error:?}"))?;
    let variant_incidence = DepositIncidence::of(&variant_atlas, &variant_lineage);
    let variant_covector = unit_covector(&variant_residual);
    let variant_delta = derive(
        &pre,
        &variant_residual,
        &variant_lineage,
        &variant_incidence,
        &metric,
        &variant_covector,
        &variant_surfaces,
    )
    .map_err(|error| error.to_string())?;
    let mut variant_post = commit(&pre, &variant_delta).map_err(|error| error.to_string())?;
    variant_post.extent = extents_of(&variant_atlas);
    taxa.push(read_taxon(
        "the codec-variant sibling (LexicalAperture::runs_are_maximal)",
        "ARM N-post (inherited) -> ARM N-post (maximal)",
        &format!(
            "the SAME subject through a declared lexical aperture: {} germ occurrences against {}, {} distinct surfaces against {}; germs founded {} against {}, classes founded {} against {}",
            variant_surfaces.len(),
            cultivated.germs,
            variant_surfaces.iter().collect::<BTreeSet<_>>().len(),
            lexical_tokens(&development).len(),
            variant_delta.germs_founded.len(),
            delta.germs_founded.len(),
            variant_delta.classes_after - variant_delta.classes_before,
            delta.classes_after - delta.classes_before
        ),
        &post,
        &variant_post,
        Matched {
            transitions_before: post.transitions(),
            transitions_after: variant_post.transitions(),
            population_preserved: false,
            classes_touched: variant_delta.standing_increments.len(),
        },
        "a HELD-OUT subject's probe at the depth-0 support",
    ));

    // ---- exhibit the panel ----
    line!(atlas_form, "");
    line!(
        atlas_form,
        "THE PANEL — {} taxa, each a matched sibling of one fixed predecessor",
        taxa.len()
    );
    line!(atlas_form, "");
    line!(
        atlas_form,
        "{:<58} {:<12} {:>5} {:>5} {:>5} {:>5}  {}",
        "taxon",
        "body",
        "walk",
        "d-0",
        "supp",
        "face",
        "shortest separating history"
    );
    for taxon in &taxa {
        line!(
            atlas_form,
            "{:<58} {:<12} {:>5} {:>5} {:>5} {:>5}  {}",
            truncate(&taxon.taxon, 58),
            taxon.body,
            taxon.walk_moved,
            taxon.depth_zero_moved,
            taxon.support_moved,
            taxon.face_moved,
            taxon.headline()
        );
    }

    line!(atlas_form, "");
    line!(atlas_form, "THE PANEL, TAXON BY TAXON");
    for taxon in &taxa {
        line!(atlas_form, "");
        line!(atlas_form, "  {} · {}", taxon.taxon, taxon.body);
        line!(atlas_form, "    declaration        {}", taxon.declaration);
        line!(
            atlas_form,
            "    matched            transitions {} -> {} · population preserved {} · classes touched {}",
            taxon.matched.transitions_before,
            taxon.matched.transitions_after,
            taxon.matched.population_preserved,
            taxon.matched.classes_touched
        );
        line!(
            atlas_form,
            "    caused change      walk {}/{} · depth-0 support {}/{} · support {}/{} · face {}/{} probes moved",
            taxon.walk_moved, PROBES.len(),
            taxon.depth_zero_moved, PROBES.len(),
            taxon.support_moved, PROBES.len(),
            taxon.face_moved, PROBES.len()
        );
        for shortest in &taxon.shortest {
            match shortest.prefix {
                Some(prefix) => line!(
                    atlas_form,
                    "    shortest history   {:<15} {} token(s) of {:?} — the token {:?}",
                    shortest.face,
                    prefix,
                    shortest.probe,
                    shortest.token
                ),
                None => line!(
                    atlas_form,
                    "    shortest history   {:<15} NONE — no probe separates at this face",
                    shortest.face
                ),
            }
        }
        line!(
            atlas_form,
            "    control declared   {}",
            taxon.control_declaration
        );
        line!(
            atlas_form,
            "    control measured   {}",
            taxon.control_measured
        );
        for row in &taxon.per_probe {
            line!(atlas_form, "      {row}");
        }
        line!(
            atlas_form,
            "    remaining ambiguity {}",
            ambiguity_of(&taxon.taxon)
        );
    }

    // =========================================================================================
    // 5. the retained separator words — the compression owner, on a declared closed scope
    // =========================================================================================
    line!(atlas_form, "");
    line!(
        atlas_form,
        "THE RETAINED SEPARATOR WORDS — receiver_exact_compression on a declared CLOSED scope"
    );
    line!(
        atlas_form,
        "  the scope, declared: the forward closure of the class {:?} lands in, which is closed under the",
        "a compression is a codec"
    );
    line!(atlas_form, "  transport by construction, so Moore's round count IS the memory order and no per-pair search is needed.");
    line!(atlas_form, "  the receiver family R1: (a) the class's own out-degree, (b) whether it is a link root, (c) its standing.");
    let landed = conduct(
        &pre,
        "a compression is a codec",
        &lexical_tokens("a compression is a codec"),
    )
    .class;
    let scope = forward_closure(&pre, landed);
    let scope_items: Vec<ItemId> = scope
        .iter()
        .map(|class| ItemId(u64::from(*class)))
        .collect();
    let mut scope_inputs: BTreeSet<u64> = BTreeSet::new();
    for class in &scope {
        for germ in pre.offered(*class) {
            scope_inputs.insert(*germ);
        }
    }
    let inputs: Vec<InputId> = scope_inputs.iter().map(|germ| InputId(*germ)).collect();
    line!(
        atlas_form,
        "  scope: class {landed} closes over {} classes and {} germs",
        scope.len(),
        inputs.len()
    );
    line!(
        atlas_form,
        "  {:<64} {:>8} {:>8} {:>7} {:>14}",
        "body",
        "one-shot",
        "conduct",
        "rounds",
        "separated"
    );
    let mut separator_rows: Vec<String> = Vec::new();
    let compression_bodies: Vec<(String, AthenaRest)> = {
        let germ = germ_index(&pre, &withdrawn_family.1)?;
        let (family_sibling, _) = intervene(&pre, &RestIntervention::WithdrawGermFamily { germ })
            .map_err(|error| error.to_string())?;
        let (band_sibling, _) = intervene(
            &pre,
            &RestIntervention::WithdrawHeightBand {
                low: band.0,
                high: band.1,
            },
        )
        .map_err(|error| error.to_string())?;
        let left = germ_index(&pre, &pre.vocabulary[transposed.0 as usize])?;
        let right = germ_index(&pre, &pre.vocabulary[transposed.1 as usize])?;
        let (swap_sibling, _) =
            intervene(&pre, &RestIntervention::TransposeGermLabels { left, right })
                .map_err(|error| error.to_string())?;
        vec![
            ("ARM N-pre (the base)".to_owned(), pre.clone()),
            (
                format!("the germ family {:?} withdrawn", withdrawn_family.1),
                family_sibling,
            ),
            (
                format!("the height band {}..={} withdrawn", band.0, band.1),
                band_sibling,
            ),
            (
                format!(
                    "the germ labels {:?}/{:?} transposed",
                    pre.vocabulary[transposed.0 as usize], pre.vocabulary[transposed.1 as usize]
                ),
                swap_sibling,
            ),
        ]
    };
    for (label, body) in &compression_bodies {
        let system = AtlasScope {
            rest: body,
            items: scope_items.clone(),
            inputs: inputs.clone(),
        };
        let reading = refine(&system);
        let separated = separated_pair_population(&reading.one_shot, &reading.conduct);
        line!(
            atlas_form,
            "  {:<64} {:>8} {:>8} {:>7} {:>14}",
            truncate(label, 64),
            reading.one_shot.blocks.len(),
            reading.conduct.blocks.len(),
            reading.rounds,
            separated
        );
        let exhibited =
            exhibit_collapsed_within(&system, &reading.one_shot, &reading.conduct, Some(4));
        for pair in exhibited {
            separator_rows.push(format!(
                "{:<52} classes {} and {} separated by {:?}{}",
                truncate(label, 52),
                pair.left.0,
                pair.right.0,
                pair.distinguishing_word
                    .iter()
                    .map(|input| body.vocabulary[input.0 as usize].clone())
                    .collect::<Vec<_>>(),
                if pair.separated_by_terminus {
                    " (a terminus)"
                } else {
                    ""
                }
            ));
        }
    }
    line!(atlas_form, "  the retained separator words, four per body in canonical order (an APERTURE, a prefix of the complete population):");
    for row in &separator_rows {
        line!(atlas_form, "    {row}");
    }

    // =========================================================================================
    // 6. retained / split / merged / obstructed families
    // =========================================================================================
    let families = family_census(&pre, &post, &delta);
    line!(receipt, "");
    line!(receipt, "== 4. RETAINED / SPLIT / MERGED / OBSTRUCTED — the P3 delta re-read as an atlas comparison ==");
    for row in FAMILY_DEFINITIONS {
        line!(receipt, "  {row}");
    }
    line!(
        receipt,
        "  families (germ transport families) in the predecessor: {} · in the successor: {}",
        pre.vocabulary.len(),
        post.vocabulary.len()
    );
    line!(
        receipt,
        "  {:<14} {:>8}  {}",
        "disposition",
        "families",
        "what it is"
    );
    line!(
        receipt,
        "  {:<14} {:>8}  {}",
        "RETAINED",
        families.retained,
        "every standing arc bit-identical and nothing founded at a standing class"
    );
    line!(
        receipt,
        "  {:<14} {:>8}  {}",
        "SPLIT",
        families.split,
        "the family now runs through a class founded as a SPLIT of a class it already ran through"
    );
    line!(
        receipt,
        "  {:<14} {:>8}  {}",
        "MERGED",
        families.merged,
        "two families distinct before whose standing arc sets coincide after"
    );
    line!(
        receipt,
        "  {:<14} {:>8}  {}",
        "OBSTRUCTED",
        families.obstructed,
        "a standing arc whose target MOVED, or a standing class that offered it and no longer does"
    );
    line!(
        receipt,
        "  {:<14} {:>8}  {}",
        "FOUNDED",
        families.founded,
        "families the successor has and the predecessor had not"
    );
    line!(
        receipt,
        "  {:<14} {:>8}  {}",
        "GREW",
        families.grew,
        "a standing arc founded inside the standing body, no arc moved"
    );
    line!(
        receipt,
        "  the split census against the committed P3 delta: {} classes founded as splits, {} distinct standing origins",
        delta.classes_split(),
        families.split_origins
    );
    line!(receipt, "  SAMPLES, by name:");
    for row in &families.samples {
        line!(receipt, "    {row}");
    }
    line!(
        receipt,
        "  MERGED is {} and that is the finding, not an omission: a deposit into a suffix automaton founds and rebases,",
        families.merged
    );
    line!(receipt, "  and nothing in the law identifies two classes that stood. P2 measured the same thing from the other side —");
    line!(receipt, "  the conduct quotient merges 14 of 59,698 classes at a family that factors R1, so the transport does not condense.");

    // =========================================================================================
    // 7. the four-body table
    // =========================================================================================
    let shared_native_pre = conduct(&pre, SHARED_MATERIAL, &lexical_tokens(SHARED_MATERIAL));
    let shared_native_post = conduct(&post, SHARED_MATERIAL, &lexical_tokens(SHARED_MATERIAL));
    let work_pre = native_work(&pre, &lexical_tokens(SHARED_MATERIAL));
    let work_post = native_work(&post, &lexical_tokens(SHARED_MATERIAL));
    let post_octets = post.write_container().map_err(|error| error.to_string())?;
    line!(receipt, "");
    line!(receipt, "== 5. THE FOUR-BODY TABLE — one declared material, four bodies, and the codec boundary named ==");
    line!(receipt, "  THE DECLARED MATERIAL: {SHARED_MATERIAL:?}");
    line!(receipt, "    ARM F reads it through the SOURCE's own tokenizer at 5 tokens (Station D's fixed predecessor, committed).");
    line!(
        receipt,
        "    ARM N reads it through the NATIVE lexical codec at {} tokens: {:?}",
        lexical_tokens(SHARED_MATERIAL).len(),
        lexical_tokens(SHARED_MATERIAL)
    );
    line!(receipt, "    THE ARMS SHARE THE MATERIAL AND THE RECEIVER DISCIPLINE. THEY SHARE NO FACE, and the reason is a codec");
    line!(receipt, "    boundary rather than a missing measurement: ARM F's potential is 262,144 wide over the source codebook,");
    line!(receipt, "    ARM N's plural section is {} wide over the native vocabulary, and the two codebooks are disjoint populations.", pre.vocabulary.len());
    line!(receipt, "    P1's Φ is what connects charts in this tree, and its charts are SOURCE-INTERNAL — the input and post-attention");
    line!(receipt, "    gain rebases, the grouped-sharing quotient, and the BF16 fibre law. NO Φ in this tree carries the source");
    line!(receipt, "    codebook to the native vocabulary, and none is claimed. That absence is what ARM N's independence IS.");
    line!(receipt, "");
    for row in four_body_rows(
        &pre_octets,
        &post_octets,
        &pre,
        &post,
        &shared_native_pre,
        &shared_native_post,
        &work_pre,
        &work_post,
    ) {
        line!(receipt, "  {row}");
    }
    line!(receipt, "");
    line!(
        receipt,
        "  THE SHARED MATERIAL'S NATIVE RETURN, verbatim (the plural section, no winner taken)"
    );
    for (label, section) in [
        ("ARM N-pre", &shared_native_pre),
        ("ARM N-post", &shared_native_post),
    ] {
        line!(
            receipt,
            "    {label:<11} walk {:?} · landed class {} · standing {} · {} germs offered over {} ladder depth(s)",
            section.trace.join(" · "),
            section.class,
            section.standing,
            section.offered.len(),
            section.offered.iter().map(|(_, _, depth)| depth).collect::<BTreeSet<_>>().len()
        );
        let zero: Vec<&str> = section
            .offered
            .iter()
            .filter(|(_, _, depth)| *depth == 0)
            .map(|(surface, _, _)| surface.as_str())
            .collect();
        line!(
            receipt,
            "                depth-0 ({}): {:?}",
            zero.len(),
            zero.iter().take(24).collect::<Vec<_>>()
        );
    }

    // =========================================================================================
    // 8. native recombinations, condensation losses, and the manifest
    // =========================================================================================
    line!(receipt, "");
    line!(
        receipt,
        "== 6. NATIVE RECOMBINATIONS — cited with their ablations and their bounded scopes =="
    );
    for row in RECOMBINATIONS {
        line!(receipt, "  {row}");
    }
    line!(receipt, "");
    line!(
        receipt,
        "== 7. CONDENSATION LOSSES — cited, and the near-empty loss table IS the finding =="
    );
    for row in CONDENSATION {
        line!(receipt, "  {row}");
    }

    line!(receipt, "");
    line!(
        receipt,
        "== 8. THE TYPED REFUSAL FACES THIS DEED RETURNED =="
    );
    for (label, refusal) in &extent_refusals {
        line!(
            receipt,
            "  {label:<12} mount_atlas on a rest with no extents -> {refusal}"
        );
    }
    let manifest = regions(&pre_octets);
    let bar = content_bar(&pre_octets, &pre);
    line!(receipt, "");
    line!(
        receipt,
        "== 9. THE PREDECESSOR'S OWN MANIFEST AND CONTENT BAR, re-read from the container =="
    );
    line!(
        receipt,
        "  {} regions · loss digest {}",
        manifest.len(),
        loss_digest(&pre_octets)
    );
    for region in &manifest {
        line!(
            receipt,
            "    {:<28} {:<6} {:>10} octets",
            region.name,
            region.dtype,
            region.octets()
        );
    }
    for row in &bar {
        line!(
            receipt,
            "    BAR {:<52} {:<6} {}",
            row.claim,
            row.held,
            row.evidence
        );
    }

    // =========================================================================================
    // 9. the grade table
    // =========================================================================================
    line!(
        grade_form,
        "THE COMPLETE PHOENIX GRADE — the blueprint's §0 thirteen items, INDIVISIBLE"
    );
    line!(grade_form, "");
    for row in HONESTY_BAR {
        line!(grade_form, "{row}");
    }
    line!(grade_form, "");
    line!(
        grade_form,
        "{:<3} {:<44} {:<12} {:<10}",
        "#",
        "item",
        "deed(s)",
        "verdict"
    );
    for (at, item) in GRADE.iter().enumerate() {
        line!(
            grade_form,
            "{:<3} {:<44} {:<12} {:<10}",
            at + 1,
            item.item,
            item.deeds,
            item.verdict
        );
    }
    line!(grade_form, "");
    line!(
        grade_form,
        "EACH ITEM, WITH ITS DECLARED APERTURE AND ITS FALSIFIER"
    );
    for (at, item) in GRADE.iter().enumerate() {
        line!(grade_form, "");
        line!(grade_form, "{:>2}. {}", at + 1, item.item);
        line!(grade_form, "    deed(s)            {}", item.deeds);
        line!(grade_form, "    DECLARED APERTURE  {}", item.aperture);
        line!(grade_form, "    verdict            {}", item.verdict);
        line!(grade_form, "    falsifier          {}", item.falsifier);
    }
    line!(grade_form, "");
    line!(grade_form, "THE HONEST VERDICT SENTENCE");
    line!(grade_form, "");
    for row in VERDICT {
        line!(grade_form, "{row}");
    }

    line!(receipt, "");
    line!(receipt, "== 10. THE GRADE ==");
    line!(
        receipt,
        "  the thirteen items, their apertures and their falsifiers: {OUT}/grade-table.form"
    );
    for (at, item) in GRADE.iter().enumerate() {
        line!(
            receipt,
            "  {:>2}. {:<44} {:<12} {}",
            at + 1,
            item.item,
            item.deeds,
            item.verdict
        );
    }
    line!(receipt, "");
    line!(receipt, "  THE HONEST VERDICT SENTENCE");
    for row in VERDICT {
        line!(receipt, "  {row}");
    }

    // ---- the application face, through the built binary ----
    line!(receipt, "");
    line!(
        receipt,
        "== 11. THE APPLICATION FACE — the built eros binary, on the copy of the predecessor =="
    );
    let application = Command::new("target/release/eros")
        .args([
            "phoenix",
            "infer",
            "--rest",
            &format!("{OUT}/copy-of-the-predecessor.safetensors"),
            "--text",
            SHARED_MATERIAL,
        ])
        .output();
    match application {
        Ok(returned) => {
            let printed = String::from_utf8_lossy(&returned.stdout);
            line!(
                receipt,
                "  exit {:?} · {} octets printed",
                returned.status.code(),
                printed.len()
            );
            for row in printed.lines().take(14) {
                line!(receipt, "  | {row}");
            }
            let after = std::fs::read(format!("{OUT}/copy-of-the-predecessor.safetensors"))
                .map_err(|error| error.to_string())?;
            line!(
                receipt,
                "  the rest after the application conducted: {} ({} octets)",
                if after == pre_octets {
                    "BYTE-IDENTICAL"
                } else {
                    "MOVED"
                },
                after.len()
            );
        }
        Err(error) => line!(receipt, "  the binary was not reachable: {error}"),
    }

    line!(receipt, "");
    line!(
        receipt,
        "  the source dissection atlas placed beside the native one: {STATION_D} ({} octets, committed, unmoved)",
        std::fs::metadata(STATION_D).map(|held| held.len()).unwrap_or(0)
    );
    line!(
        receipt,
        "  the native dissection atlas: {OUT}/native-dissection-atlas.form"
    );
    line!(receipt, "");
    line!(
        receipt,
        "elapsed {:.1} s, CPU-exact throughout; no card, no float in any semantic path.",
        start.elapsed().as_secs_f64()
    );

    std::fs::write(format!("{OUT}/receipt.form"), &receipt).map_err(|error| error.to_string())?;
    std::fs::write(format!("{OUT}/native-dissection-atlas.form"), &atlas_form)
        .map_err(|error| error.to_string())?;
    std::fs::write(format!("{OUT}/grade-table.form"), &grade_form)
        .map_err(|error| error.to_string())?;
    print!("{receipt}");
    Ok(())
}

// =============================================================================================
// the declared prose — every row is a statement this deed either measured or cites by record
// =============================================================================================

const HONESTY_BAR: &[&str] = &[
    "The grade below stands, where it stands, AT ITS DECLARED APERTURES, and every item names its own.",
    "This deed does not return \"Phoenix rebirth complete\". Three boundaries are load-bearing:",
    "  (1) THE LIFT IS BOUNDED. P1 demonstrated the lift LAW on real admitted families under a declared",
    "      hidden window of 64 of 2,560 columns, a head window of 16 of 256, and family 0 of 2. The whole",
    "      foreign map was not lifted, and P1's own record says so.",
    "  (2) THE TRANSPORT DOES NOT CONDENSE. P2 measured the native conduct quotient merging 14 classes of",
    "      59,698, and its cost vector does not strictly fall, so no compression factor is quoted anywhere.",
    "  (3) ARM N IS NOT A GEMMA LIFT. The native arm is independent of the foreign source BY CONSTRUCTION.",
    "      The full-scale re-expression of the foreign map as a native executable ecology is NOT what this",
    "      tree holds. What it holds is the lift law proven boundedly, the source dissected completely, and",
    "      an independent native ecology built, condensed, cultivated, sealed and runnable.",
];

const FOUR_BODIES: &[&str] = &[
    "ARM F               the foreign source, executable (the streamed circulation, H4/H5) and dissected",
    "                    (Station D's sixteen matched siblings, reproduced unchanged through prefix sharing in H5).",
    "ARM N-pre           the P0 rest — the native body before cultivation. INDEPENDENT of the source by",
    "                    construction. This is this tree's honest form of \"the lifted predecessor at the native",
    "                    side\": the two arms are joined by the lift LAW (P1), not by a lifted body.",
    "ARM N-post          the cultivated successor (P3's delta, re-derived here from the rest alone, and P4's",
    "                    application path).",
    "THE LIFTED FAMILIES P1's bounded lift objects — the grouped-sharing quotient and the BF16 fibre law and",
    "                    their recombination — executable as exact compositions, with their two-cause ablation.",
];

const RECEIVER_FAMILY: &[&str] = &[
    "THE RECEIVER FAMILY, four faces of one plural section, ordered by what growth can and cannot forge:",
    "  WALK           the landed class and the walk's own trace. Nothing a deposit does to occupancy moves it.",
    "  DEPTH-0 SUPPORT what the full context ALONE licenses. P4 measured that this is the only face a",
    "                 subject-disjoint control can honestly be taken on.",
    "  SUPPORT        every offered germ with the depth it was first offered at, standings dropped.",
    "  FACE           the whole section: every offered germ, the standing of the class it reaches, the depth.",
    "                 A deposit re-folds occurrence counts over the whole tree, so this face moves everywhere",
    "                 after any cultivation whatever its subject — that is the law's face, not a caveat.",
    "  two faces are SEPARATED when their octets differ; IDENTICAL when bit-equal. No winner is ever taken.",
];

const FAMILY_DEFINITIONS: &[&str] = &[
    "A FAMILY here is a germ transport family: for one germ, the whole arc set {(class -> target)} carrying it.",
    "The comparison is taken over the STANDING classes alone (the predecessor's own index range), because a",
    "class the successor founded has no predecessor arc to compare with and is counted as growth, not change.",
];

const RECOMBINATIONS: &[&str] = &[
    "P1's recombination — bounded, and declared bounded before its result. The declared source closure is the",
    "  committed Station B/C deposit's 35 operation words; none of preimage/fibre/inverse/kernel occurs in any",
    "  of them (measured, zero hits), so the source descends and returns no preimage. The recombined return",
    "  composes the grouped-sharing quotient with the BF16 fibre law: the exact reconstruction fibre of a family",
    "  coordinate, the Minkowski sum of the four sharing heads' cells at width 9/16384, beside the exhibited",
    "  48-dimensional kernel. ITS ABLATION IS TWO-CAUSE AND PLURAL-DIFFED: withdrawing the grouped-sharing lift",
    "  leaves the kernel DIMENSION unchanged at 48 (which is precisely why a dimension is not the reading) while",
    "  48 of 48 baseline basis directions leave and the identified spaces intersect in only 32 of 48; withdrawing",
    "  the fibre lift leaves the kernel bit-identical and takes the interval's width to 0. Unrelated control",
    "  bit-identical under all three settings, digest 3be4ff41.",
    "  BOUNDED BY: the hidden window 64 of 2,560, the head window 16 of 256, family 0 of 2, grain 2^-8. The",
    "  recombination is a demonstration of the LAW on real material, not a lifted model.",
    "P3's recombination — the derived delta's own conduct change, and its in-body ablation. The delta is derived",
    "  by the declared return law (dq = G_X^-1 A^T G_Y r) and never read out of the deposited body; committing it",
    "  reproduces the successor octet for octet; withdrawing it in place returns the predecessor container octet",
    "  for octet and reverts the changed conduct 3 of 3. BOUNDED BY: one exposure, one subject, one aperture, one",
    "  declared metric; and the successor's extents come from the transport rather than from the delta.",
];

const CONDENSATION: &[&str] = &[
    "P2's condensation, cited: at any family that factors R1 the native atlas is essentially receiver-discrete —",
    "  the conduct quotient merges 14 classes of 59,698 in two plural blocks, block sizes [(1, 59684), (6, 1),",
    "  (8, 1)]. THAT NEGATIVE IS THE RESULT: the search was structural and the structure says no.",
    "  The tree half condenses for FREE with an EMPTY remainder (219,048 ancestry pairs to the interval chart,",
    "  3.67x against a materialised ancestry relation and 2.00x AGAINST the stored parent array — a trade the",
    "  additive law makes visible where a ratio would hide it).",
    "  The certified retained remainder: 43,215 reconvergent arcs at 27,628 classes, cycle rank 43,207, retained",
    "  whole; one collapsed pair reopened from the condensed rest alone by its retained word ([\"<\"] carrying",
    "  classes 1 and 326 to receivers returning (2,2) against (4,10)).",
    "  Unexcited material 54,100 of 59,698 classes, retained in every section and in the complete cost.",
    "  THE COST VECTOR DOES NOT STRICTLY FALL — artifact 1,642,928 -> 2,511,460 octets, decoder 4,984 -> 10,418,",
    "  decoder steps 262,353 -> 381,746 — so NO COMPRESSION FACTOR IS QUOTED, per the additive law.",
    "  THE LOSS TABLE IS THEREFORE NEARLY EMPTY, AND THAT IS THE FINDING: there is almost nothing to lose because",
    "  there is almost nothing the declared receiver family cannot see.",
];

struct GradeRow {
    item: &'static str,
    deeds: &'static str,
    aperture: &'static str,
    verdict: &'static str,
    falsifier: &'static str,
}

const GRADE: &[GradeRow] = &[
    GradeRow {
        item: "complete source admission",
        deeds: "Station B",
        aperture: "the whole gemma-4-E4B-it container: 2,130 of 2,130 declared populations manifested over their exact spans, 15,992,314,836 payload octets, 0 uncovered, every BF16 codeword decoded exactly through the one float mouth. Peak residency 33,558,700 octets against 15,992,595,884 — a streamed admission, never a full residency.",
        verdict: "STANDING",
        falsifier: "one declared population unmanifested, one payload octet uncovered, or one codeword whose decode disagrees with the mouth.",
    },
    GradeRow {
        item: "potential and active transport",
        deeds: "Station B, Station C, H2-H5",
        aperture: "potential: the atlas covers the full 42-layer tower. ACTIVE: one runtime-supplied input of 5 tokens under the DECLARED MidpointQuotient chart at grain 2^-48 with 14 series terms, whose composition is NOT certified — the composed enclosure diverges at 2^35 per layer, so a separation is read at that chart's collapsed points with the enclosure retained per occurrence.",
        verdict: "STANDING at the declared chart",
        falsifier: "an active transport whose per-occurrence enclosure is not retained, or a separation claimed outside the declared chart's collapsed points.",
    },
    GradeRow {
        item: "source intervention atlas",
        deeds: "Station D, H5",
        aperture: "one input, one site per taxon (two for the K/V family), one span or permutation per kind: sixteen matched siblings plus the vision sibling against one fixed predecessor, 128 receiver faces, 12 of 12 falsifiers, 21 of 21 controls. H5 reproduced all 168 committed cells UNCHANGED through prefix sharing; 15 of the 21 controls become STRUCTURAL there and the receipt says so.",
        verdict: "STANDING",
        falsifier: "a sibling whose shortest separating history begins before its own site; a control predicted unmoved that moves; a cell that drifts on replay.",
    },
    GradeRow {
        item: "native Eros/Athena baseline",
        deeds: "P0",
        aperture: "eight declared canon documents -> 59,698 classes, 102,904 germ transitions, 5,385 vocabulary germs, 1,642,928 octets. Executable ON THE CARD from its own rest, plural (no argmax, no sampler, no temperature), fresh-process remounted with 5,342,912 octets of faces bit-equal, hidden card refusing typed. The manifest's winding/phase rows are OPEN with falsifiers and NO GROUP ACTION IS FOUNDED — the transport generates a monoid, measured.",
        verdict: "STANDING; the manifest's winding/phase rows OPEN",
        falsifier: "a conduct that differs between card and CPU; a remount that is not bit-equal; a group element with a nontrivial winding, which would move the OPEN rows.",
    },
    GradeRow {
        item: "cross-chart lift and defect",
        deeds: "P1",
        aperture: "THE LIFT LAW ON BOUNDED REAL FAMILIES, NOT THE WHOLE MAP. Hidden window 64 of 2,560 columns; head window 16 of 256; family 0 of 2; grain 2^-8; compression scope 512 codewords. Four families' chi computed exactly with kernel/image/cokernel; the chain law verified as an operator identity; the BF16 fibres censused over the WHOLE q_proj map (5,242,880 of 5,242,880 entries, 0 residuals outside their fibre, 0 overlaps in 10,481,059 neighbour checks).",
        verdict: "STANDING at the bounded aperture",
        falsifier: "a chi whose chain law residual is nonzero; a probe landing outside its fibre; the same lift attempted at full width returning a different law rather than the same law at greater cost.",
    },
    GradeRow {
        item: "material-founded native morphology",
        deeds: "P0, P2",
        aperture: "every measured row of the NativeEcologyManifest computed from the rest alone — incidence 59,698/102,904/5,385, cycle rank 43,207 with 27,628 reconvergent classes EXHIBITED BY NAME, the germ transport measured a DAG, tree height 9 with its per-height census, memory order 3 at P0's declared scope and 56 over the whole atlas. No layer count, no latent width, no head, no rank anywhere; the only depth receiver is the suffix-link height, read off the material.",
        verdict: "STANDING",
        falsifier: "an authored layer, width, head or rank entering the morphology; a manifest row that cannot be recomputed from the container alone.",
    },
    GradeRow {
        item: "receiver-exact condensation and complete fibres",
        deeds: "P2",
        aperture: "receiver family declared BEFORE fitting (R1 plural sections, R2 remount, R3 intervention factoring, R4 the scale action, R5 the Nerode face, R6 cost, R7 the P1 recombination), all seven verified. TYPED CORRECTNESS PASSES AND NO FACTOR IS QUOTED: the transport condensation merges 14 classes of 59,698, the tree axis falls for free with an EMPTY remainder, and the cost vector does not strictly fall.",
        verdict: "STANDING on typed correctness; NO FACTOR QUOTED",
        falsifier: "a collapsed pair with no retained separator; a condensation whose ablation diff differs from the diff of the ablation; a factor quoted without its decoder.",
    },
    GradeRow {
        item: "cultivation and attributable adjoint return",
        deeds: "P3, P4",
        aperture: "the NATIVE arm, one development subject, one exposure, one declared metric (G_Y = I over the four residual species, G_X = I). The delta is DERIVED by dq = G_X^-1 A^T G_Y r and never read out of the deposited body; committing it reproduces the successor octet for octet; the metric is load-bearing by perturbation (5,462 classes' committed increments move). The FOIL separates structure from population on an identical germ multiset.",
        verdict: "STANDING at one subject and one metric",
        falsifier: "a delta that cannot be re-derived from the residual and the forward lineage; a metric perturbation that moves nothing; a foil whose delta equals the development delta.",
    },
    GradeRow {
        item: "source-detached rest",
        deeds: "P0, P3, P4",
        aperture: "measured three ways: P0's fresh-process remount with a live descriptor audit; P3's successor remount, faces bit-equal 3 of 3; P4's application printing its OWN descriptor audit with no canon/, no research/, no blueprint/, no examples/, no gemma, no .gguf, no /dev/nvidia*, no /dev/dri open. The P4 deed's own finding is that reaching this required REMOVING a corpus lookup the P3 driver still carried.",
        verdict: "STANDING",
        falsifier: "any forbidden descriptor open during a conduct or a deposit; a rest that cannot be mounted without a second file.",
    },
    GradeRow {
        item: "frozen native runtime accepting new material",
        deeds: "P4",
        aperture: "the built eros binary, two application deeds (phoenix infer, phoenix cultivate), ten of ten controls: two-process seal byte identity, the self-audit, the typed refusal on a missing rest with exit 1 and no plausible output, frozen inference leaving the rest byte-identical, cultivation founding a distinct successor with the THREE-FACE honesty table, unseen material at run time plus a second-generation cultivation, the honest GPU form (--card refuses UNWIRED), no subprocess in the application's code path, the export round trip 0 of 59,698 classes differing, and the content bar measured. THE GGUF VERDICT IS A REFUSAL WITH ITS REASON: the payload is expressible, the law has no lawful home.",
        verdict: "STANDING; CPU-exact, and --card is UNWIRED",
        falsifier: "an inference that moves the rest; a cultivation the successor cannot itself be cultivated from; a station that prints a plausible face for a surface it never touched.",
    },
    GradeRow {
        item: "reborn-body dissection",
        deeds: "P5 (this deed)",
        aperture: "the NATIVE arm only, predecessor AND cultivated successor, thirteen fixed probes, four declared receiver faces, and eleven matched siblings over seven taxa. The intervention parameters are chosen BY DECLARED RULE, not by effect. The source arm's atlas is Station D's and is placed beside this one, NOT merged with it: the two arms share the material and the receiver discipline and no face.",
        verdict: "STANDING on the native arm; the two atlases stand SIDE BY SIDE",
        falsifier: "an intervention whose shortest separating history begins before its own site; a control predicted unmoved that moves; a taxon whose sibling is not matched.",
    },
    GradeRow {
        item: "matched siblings and targeted ablation",
        deeds: "Station D, H5, P0, P1, P3, P5",
        aperture: "five ablation species stand, at five different strengths, and they are NOT one thing: Station D's sixteen in-tower interventions; P1's two-cause lift ablation, plural-diffed; P0's CONSTRUCTION-LEVEL rebuild without one document (which moves every class index, and says so); P3's IN-BODY withdrawal returning the predecessor container octet for octet (strictly stronger); and this deed's in-body rest interventions on both bodies.",
        verdict: "STANDING",
        falsifier: "an ablation whose consequence does not disappear with the structure removed; a construction-level rebuild reported as an in-body deletion.",
    },
    GradeRow {
        item: "semantic work and calibrated apparatus utility",
        deeds: "H0, H2-H5, P0, P2, P5",
        aperture: "SEMANTIC WORK IS EXACT AND SEPARATE FROM TELEMETRY: ARM F's per-tower work is 23,363,161,920 additions, 23,458,347,840 multiplications, 76,538,880 entries written, 43 launches; the apparatus face (167.2 GB -> 9.29 GB read, ~12,672 -> 704 stagings, ~8 min -> 38.9 s) is reported BESIDE it and never in place of it, and launch counts are excluded from the semantic comparison by name. ARM N's work is the ladder/row/cell vector this deed returns. CALIBRATED APPARATUS UTILITY IS NOT CLOSED: every ncu-only face (active/eligible/issued warps, stall classes, registers, achieved occupancy, L1/L2/DRAM traffic) is UNKNOWN because RmProfilingAdminOnly is 1, and it is stated unknown rather than inferred.",
        verdict: "SEMANTIC WORK STANDING; CALIBRATED APPARATUS UTILITY OPEN (unknown, not zero)",
        falsifier: "a scalar utilization, speedup or energy quotient governing a semantic choice; an apparatus figure standing in for the semantic one; an ncu-only face reported as measured.",
    },
];

const VERDICT: &[&str] = &[
    "Of the blueprint's thirteen indivisible Phoenix items, TWELVE STAND AT THEIR DECLARED APERTURES and ONE IS",
    "OPEN. What is genuinely admitted is this: the foreign source is admitted whole and dissected completely by",
    "intervention; the lift LAW between charts is proven exactly on bounded real families — a hidden window of 64",
    "of 2,560 columns, a head window of 16 of 256, family 0 of 2 — and NOT on the whole map; and an INDEPENDENT",
    "native ecology, founded on eight declared canon documents rather than on the foreign map, is built, measured,",
    "condensed where a declared receiver family factors, cultivated by a derived adjoint return, sealed, remounted",
    "in a fresh process with the source absent, run behind a real application entry, and dissected in turn on both",
    "its predecessor and its cultivated successor. The named boundaries are equally the result: the lift is bounded",
    "and its record says so; the native transport DOES NOT CONDENSE (14 classes of 59,698 merge, the cost vector",
    "does not strictly fall, and no compression factor is quoted); calibrated apparatus utility is UNKNOWN rather",
    "than measured because the card's counters are admin-only; and ARM N IS NOT A GEMMA LIFT. THE FULL-SCALE",
    "RE-EXPRESSION OF THE FOREIGN MAP AS A NATIVE EXECUTABLE ECOLOGY IS NOT WHAT THIS TREE HOLDS. What this tree",
    "holds is the lift law proven boundedly, the source dissected completely, and an independent native ecology",
    "built, condensed, cultivated, sealed and runnable.",
];

// =============================================================================================
// the machinery
// =============================================================================================

struct Matched {
    transitions_before: usize,
    transitions_after: usize,
    population_preserved: bool,
    classes_touched: usize,
}

/// The shortest separating history AT ONE FACE: the fewest tokens of any probe's own chronology
/// after which that face separates. `None` is a genuine "this face never separates on this panel".
struct Shortest {
    face: &'static str,
    prefix: Option<usize>,
    probe: String,
    token: String,
}

const FACE_NAMES: [&str; 4] = ["walk", "depth-0 support", "support", "face"];

struct TaxonReading {
    taxon: String,
    body: &'static str,
    declaration: String,
    matched: Matched,
    walk_moved: usize,
    depth_zero_moved: usize,
    support_moved: usize,
    face_moved: usize,
    shortest: Vec<Shortest>,
    control_declaration: String,
    control_measured: String,
    control_extra: Vec<String>,
    per_probe: Vec<String>,
}

impl TaxonReading {
    /// The panel line's one-line summary: the coarsest face that separates, at its own shortest
    /// prefix. The coarsest is the informative one — a face that moves everywhere says least.
    fn headline(&self) -> String {
        for held in &self.shortest {
            if let Some(prefix) = held.prefix {
                return format!("{} at {} token(s) of {:?}", held.face, prefix, held.probe);
            }
        }
        "NONE — no face separates on any probe".to_owned()
    }
}

fn faces_of(section: &ConductedSection) -> (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>) {
    let mut walk = Vec::new();
    walk.extend_from_slice(&section.class.to_le_bytes());
    for step in &section.trace {
        walk.extend_from_slice(step.as_bytes());
        walk.push(0x1f);
    }
    (
        walk,
        section.depth_zero_support(),
        section.support(),
        section.face(),
    )
}

#[allow(clippy::too_many_arguments)]
fn read_taxon(
    taxon: &str,
    body_label: &'static str,
    declaration: &str,
    base: &AthenaRest,
    sibling: &AthenaRest,
    matched: Matched,
    control_declaration: &str,
) -> TaxonReading {
    let mut walk_moved = 0usize;
    let mut depth_zero_moved = 0usize;
    let mut support_moved = 0usize;
    let mut face_moved = 0usize;
    let mut per_probe = Vec::new();
    let mut control_holds = Vec::new();
    // per face: the shortest prefix seen so far, with the probe and token that carried it
    let mut earliest: [Option<(usize, String, String)>; 4] = [None, None, None, None];

    for (role, probe) in PROBES {
        let tokens = lexical_tokens(probe);
        let (walk_a, zero_a, support_a, face_a) = faces_of(&conduct(base, probe, &tokens));
        let (walk_b, zero_b, support_b, face_b) = faces_of(&conduct(sibling, probe, &tokens));
        let moved = [
            walk_a != walk_b,
            zero_a != zero_b,
            support_a != support_b,
            face_a != face_b,
        ];
        walk_moved += usize::from(moved[0]);
        depth_zero_moved += usize::from(moved[1]);
        support_moved += usize::from(moved[2]);
        face_moved += usize::from(moved[3]);
        per_probe.push(format!(
            "{role:<9} {:<52} walk {:<9} depth-0 {:<9} support {:<9} face {}",
            format!("{probe:?}"),
            if moved[0] { "MOVED" } else { "identical" },
            if moved[1] { "MOVED" } else { "identical" },
            if moved[2] { "MOVED" } else { "identical" },
            if moved[3] { "MOVED" } else { "identical" }
        ));
        if *role == "HELD-OUT" {
            control_holds.push((probe.to_string(), moved));
        }

        // the shortest separating history at each face, along this probe's own chronology
        let mut found = [false; 4];
        for prefix in 0..=tokens.len() {
            if found.iter().all(|held| *held) {
                break;
            }
            let held = &tokens[..prefix];
            let (wa, za, sa, fa) = faces_of(&conduct(base, probe, held));
            let (wb, zb, sb, fb) = faces_of(&conduct(sibling, probe, held));
            let separated = [wa != wb, za != zb, sa != sb, fa != fb];
            for at in 0..4 {
                if found[at] || !separated[at] {
                    continue;
                }
                found[at] = true;
                let token = if prefix == 0 {
                    "<the empty prompt — the root's own family>".to_owned()
                } else {
                    tokens[prefix - 1].clone()
                };
                let better = earliest[at]
                    .as_ref()
                    .is_none_or(|(seen, _, _)| prefix < *seen);
                if better {
                    earliest[at] = Some((prefix, probe.to_string(), token));
                }
            }
        }
    }

    let shortest: Vec<Shortest> = FACE_NAMES
        .iter()
        .enumerate()
        .map(|(at, face)| match &earliest[at] {
            Some((prefix, probe, token)) => Shortest {
                face,
                prefix: Some(*prefix),
                probe: probe.clone(),
                token: token.clone(),
            },
            None => Shortest {
                face,
                prefix: None,
                probe: String::new(),
                token: String::new(),
            },
        })
        .collect();

    let control_measured = if control_holds.is_empty() {
        "no HELD-OUT probe in the panel".to_owned()
    } else {
        let held_at = |at: usize| control_holds.iter().filter(|(_, moved)| !moved[at]).count();
        format!(
            "HELD-OUT probes: {} of {} hold the WALK bit-identical · {} of {} the DEPTH-0 SUPPORT · {} of {} the SUPPORT · {} of {} the whole FACE",
            held_at(0), control_holds.len(),
            held_at(1), control_holds.len(),
            held_at(2), control_holds.len(),
            held_at(3), control_holds.len()
        )
    };

    TaxonReading {
        taxon: taxon.to_owned(),
        body: body_label,
        declaration: declaration.to_owned(),
        matched,
        walk_moved,
        depth_zero_moved,
        support_moved,
        face_moved,
        shortest,
        control_declaration: control_declaration.to_owned(),
        control_measured,
        control_extra: Vec::new(),
        per_probe,
    }
}

/// Every probe, at every face, base against sibling — the whole panel as one bit-identity control.
fn whole_panel_identity(base: &AthenaRest, sibling: &AthenaRest) -> String {
    let mut equal = [0usize; 4];
    for (_, probe) in PROBES {
        let tokens = lexical_tokens(probe);
        let (wa, za, sa, fa) = faces_of(&conduct(base, probe, &tokens));
        let (wb, zb, sb, fb) = faces_of(&conduct(sibling, probe, &tokens));
        for (at, same) in [wa == wb, za == zb, sa == sb, fa == fb].iter().enumerate() {
            equal[at] += usize::from(*same);
        }
    }
    format!(
        "the WHOLE panel, bit-identical: walk {}/{} · depth-0 support {}/{} · support {}/{} · face {}/{}",
        equal[0], PROBES.len(),
        equal[1], PROBES.len(),
        equal[2], PROBES.len(),
        equal[3], PROBES.len()
    )
}

fn ambiguity_of(taxon: &str) -> &'static str {
    if taxon.starts_with("cultivation") {
        "a deposit founds AND re-folds occupancy, and this taxon does not separate the two. P3's foil separates structure from population on an identical germ multiset; nothing here separates the standing increment from the founded row at one class."
    } else if taxon.starts_with("the delta withdrawn") {
        "the withdrawal returns the container; it does not testify that no OTHER delta would have returned the same container. The identity is octet-level and one-sided."
    } else if taxon.starts_with("the germ family") {
        "the germ stays in the vocabulary, so a walk can still ask for it; this does not separate the family's role as a WALK arc from its role as a FUTURE offer. Every ladder ends at the root and the root offers the whole vocabulary, so the family leaves every probe's support by construction."
    } else if taxon.starts_with("the suffix-height band") {
        "a height is a property of the TARGET, so the band withdraws arcs that arrive at a scale and never arcs that depart from one; the two are not separated here."
    } else if taxon.starts_with("the germ labels") {
        "a transposition moves the label and not the target, so the target multiset is unmoved and the walk's arithmetic is unmoved; what moves is only which germ addresses which continuation. It does not separate the label from the surface, because the vocabulary is unmoved."
    } else if taxon.starts_with("the athena.class.extent") {
        "this taxon separates the DEPOSIT capability from the CONDUCT capability and nothing finer. It says the extents are not read by the three conduct laws; it does not say which of the deposit's three uses of an extent is load-bearing."
    } else {
        "the codec variant changes the token population AND its adjacency at once, so it does not separate an aperture that splits a run from one that merges two. P3's foil holds the population fixed; this taxon does not."
    }
}

fn germ_index(rest: &AthenaRest, surface: &str) -> Result<u64, String> {
    rest.vocabulary
        .iter()
        .position(|held| held == surface)
        .map(|at| at as u64)
        .ok_or_else(|| format!("the surface {surface:?} is not in this body's vocabulary"))
}

fn truncate(text: &str, width: usize) -> String {
    if text.chars().count() <= width {
        text.to_owned()
    } else {
        text.chars()
            .take(width.saturating_sub(1))
            .collect::<String>()
            + "~"
    }
}

/// The forward closure of one class under the germ transport: closed by construction, which is the
/// condition under which Moore's round count IS the memory order.
fn forward_closure(rest: &AthenaRest, from: u32) -> Vec<u32> {
    let mut seen = BTreeSet::from([from]);
    let mut frontier = VecDeque::from([from]);
    while let Some(class) = frontier.pop_front() {
        let (start, end) = (
            rest.indptr[class as usize] as usize,
            rest.indptr[class as usize + 1] as usize,
        );
        for slot in start..end {
            let target = rest.target[slot] as u32;
            if seen.insert(target) {
                frontier.push_back(target);
            }
        }
    }
    seen.into_iter().collect()
}

struct AtlasScope<'a> {
    rest: &'a AthenaRest,
    items: Vec<ItemId>,
    inputs: Vec<InputId>,
}

impl ObservedSystem for AtlasScope<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.items.clone()
    }
    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0), ReceiverId(1), ReceiverId(2)]
    }
    fn inputs(&self) -> Vec<InputId> {
        self.inputs.clone()
    }
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let class = item.0 as u32;
        match receiver.0 {
            0 => Observation(self.rest.offered(class).len() as u64),
            1 => Observation(u64::from(
                self.rest.suffix[class as usize] == u64::from(class),
            )),
            _ => Observation(self.rest.standing[class as usize]),
        }
    }
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.rest
            .reaches(item.0 as u32, input.0)
            .map(|target| ItemId(u64::from(target)))
    }
    fn admitted(&self, input: InputId) -> Option<Vec<(ItemId, ItemId)>> {
        let mut pairs = Vec::new();
        for item in &self.items {
            if let Some(target) = self.rest.reaches(item.0 as u32, input.0) {
                pairs.push((*item, ItemId(u64::from(target))));
            }
        }
        Some(pairs)
    }
}

struct FamilyCensus {
    retained: usize,
    split: usize,
    merged: usize,
    obstructed: usize,
    founded: usize,
    grew: usize,
    split_origins: usize,
    samples: Vec<String>,
}

/// The P3 delta re-read as an ATLAS COMPARISON: what happened to each germ transport family.
fn family_census(pre: &AthenaRest, post: &AthenaRest, delta: &CultivationDelta) -> FamilyCensus {
    let standing = pre.classes() as u32;
    let arcs = |rest: &AthenaRest, surface: &str| -> BTreeMap<u32, u32> {
        let mut held = BTreeMap::new();
        let Ok(germ) = germ_index(rest, surface) else {
            return held;
        };
        for class in 0..standing.min(rest.classes() as u32) {
            if let Some(target) = rest.reaches(class, germ) {
                held.insert(class, target);
            }
        }
        held
    };
    // which standing classes each family runs through, and which splits inherit from them
    let mut split_from: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    for founded in &delta.classes_founded {
        if let FoundedSpecies::Split { from } = founded.species {
            split_from.entry(from).or_default().push(founded.class);
        }
    }
    let mut retained = 0usize;
    let mut split = 0usize;
    let mut obstructed = 0usize;
    let mut grew = 0usize;
    let mut samples: Vec<String> = Vec::new();
    let mut post_signature: BTreeMap<Vec<(u32, u32)>, Vec<String>> = BTreeMap::new();
    let mut pre_signature: BTreeMap<Vec<(u32, u32)>, Vec<String>> = BTreeMap::new();

    for surface in &pre.vocabulary {
        let before = arcs(pre, surface);
        let after = arcs(post, surface);
        pre_signature
            .entry(before.iter().map(|(a, b)| (*a, *b)).collect())
            .or_default()
            .push(surface.clone());
        post_signature
            .entry(after.iter().map(|(a, b)| (*a, *b)).collect())
            .or_default()
            .push(surface.clone());
        let moved: Vec<(u32, u32, u32)> = before
            .iter()
            .filter_map(|(class, target)| {
                after
                    .get(class)
                    .filter(|held| *held != target)
                    .map(|held| (*class, *target, *held))
            })
            .collect();
        let lost: Vec<u32> = before
            .keys()
            .filter(|class| !after.contains_key(class))
            .copied()
            .collect();
        let gained: Vec<u32> = after
            .keys()
            .filter(|class| !before.contains_key(class))
            .copied()
            .collect();
        let inherits: bool = before.keys().any(|class| split_from.contains_key(class));
        if !moved.is_empty() || !lost.is_empty() {
            obstructed += 1;
            if samples.len() < 12 {
                if let Some((class, was, now)) = moved.first() {
                    samples.push(format!(
                        "OBSTRUCTED  family {surface:?}: class {class} reached {was} and now reaches {now} ({} arcs moved, {} lost)",
                        moved.len(),
                        lost.len()
                    ));
                } else {
                    samples.push(format!(
                        "OBSTRUCTED  family {surface:?}: {} standing arcs LOST and none moved",
                        lost.len()
                    ));
                }
            }
        } else if !gained.is_empty() {
            grew += 1;
            if samples.len() < 12 {
                samples.push(format!(
                    "GREW        family {surface:?}: {} arcs founded inside the standing body, first at class {}",
                    gained.len(),
                    gained[0]
                ));
            }
        } else if inherits {
            split += 1;
            if samples.len() < 12 {
                let class = before
                    .keys()
                    .find(|class| split_from.contains_key(class))
                    .copied()
                    .unwrap_or(0);
                samples.push(format!(
                    "SPLIT       family {surface:?}: runs through class {class}, which split into {:?}",
                    split_from.get(&class).map(|held| held.as_slice()).unwrap_or(&[])
                ));
            }
        } else {
            retained += 1;
        }
    }
    // MERGED: two families distinct before whose standing arc sets coincide after.
    let mut merged = 0usize;
    for (signature, surfaces) in &post_signature {
        if surfaces.len() < 2 || signature.is_empty() {
            continue;
        }
        let distinct_before = surfaces
            .iter()
            .map(|surface| {
                pre_signature
                    .iter()
                    .find(|(_, held)| held.contains(surface))
                    .map(|(held, _)| held.clone())
                    .unwrap_or_default()
            })
            .collect::<BTreeSet<_>>();
        if distinct_before.len() > 1 {
            merged += surfaces.len();
        }
    }
    let founded = post.vocabulary.len() - pre.vocabulary.len();
    let split_origins = split_from.len();
    FamilyCensus {
        retained,
        split,
        merged,
        obstructed,
        founded,
        grew,
        split_origins,
        samples,
    }
}

struct NativeWork {
    ladder_hops: u64,
    row_comparisons: u64,
    arcs_taken: u64,
    germ_cells_folded: u64,
    landed: u32,
}

/// **The exact work one native conduct performs**, counted while replaying the rest's own three
/// declared laws. The landed class is asserted against `conduct`'s, so this counter cannot drift
/// away from the law it is counting.
fn native_work(rest: &AthenaRest, tokens: &[String]) -> NativeWork {
    let index_of: BTreeMap<&str, u64> = rest
        .vocabulary
        .iter()
        .enumerate()
        .map(|(at, surface)| (surface.as_str(), at as u64))
        .collect();
    let mut ladder_hops = 0u64;
    let mut row_comparisons = 0u64;
    let mut arcs_taken = 0u64;
    let mut class: u32 = 0;
    for token in tokens {
        match index_of.get(token.as_str()) {
            None => class = 0,
            Some(germ) => {
                let ladder = rest.ladder(class);
                let mut reached = None;
                for held in &ladder {
                    ladder_hops += 1;
                    let row = rest.offered(*held).len() as u64;
                    row_comparisons += 64 - (row + 1).leading_zeros() as u64;
                    if let Some(target) = rest.reaches(*held, *germ) {
                        reached = Some(target);
                        break;
                    }
                }
                match reached {
                    Some(target) => {
                        arcs_taken += 1;
                        class = target;
                    }
                    None => class = 0,
                }
            }
        }
    }
    let ladder = rest.ladder(class);
    let germ_cells_folded: u64 = ladder
        .iter()
        .map(|held| rest.offered(*held).len() as u64)
        .sum();
    NativeWork {
        ladder_hops: ladder_hops + ladder.len() as u64,
        row_comparisons,
        arcs_taken,
        germ_cells_folded,
        landed: class,
    }
}

#[allow(clippy::too_many_arguments)]
fn four_body_rows(
    pre_octets: &[u8],
    post_octets: &[u8],
    pre: &AthenaRest,
    post: &AthenaRest,
    shared_pre: &ConductedSection,
    shared_post: &ConductedSection,
    work_pre: &NativeWork,
    work_post: &NativeWork,
) -> Vec<String> {
    let mut rows = Vec::new();
    rows.push(format!(
        "{:<20} {:<58} {:<40}",
        "body", "exact semantic work on the declared material", "artifact / resident octets"
    ));
    rows.push(format!(
        "{:<20} {:<58} {:<40}",
        "ARM F",
        "43 launches · 23,363,161,920 additions · 23,458,347,840 multiplications",
        "container 15,992,314,836 payload octets"
    ));
    rows.push(format!(
        "{:<20} {:<58} {:<40}",
        "(committed: H5)",
        "· 76,538,880 entries written (one whole tower, 5 source tokens)",
        "staged 9,288,903,168 · pinned 1,983,208,960"
    ));
    rows.push(format!(
        "{:<20} {:<58} {:<40}",
        "",
        "faces returned: 128 (42 layer triples + the final normed + the potential)",
        "peak admission residency 33,558,700"
    ));
    rows.push(format!(
        "{:<20} {:<58} {:<40}",
        "ARM N-pre",
        format!(
            "{} ladder hops · {} row comparisons · {} arcs taken · {} germ cells folded",
            work_pre.ladder_hops,
            work_pre.row_comparisons,
            work_pre.arcs_taken,
            work_pre.germ_cells_folded
        ),
        format!(
            "artifact {} octets (P0: 1,642,928 without extents)",
            pre_octets.len()
        )
    ));
    rows.push(format!(
        "{:<20} {:<58} {:<40}",
        "(P0, P4 seal)",
        format!(
            "faces returned: 1 plural section, {} germs over {} ladder depths, landed {}",
            shared_pre.offered.len(),
            shared_pre
                .offered
                .iter()
                .map(|(_, _, depth)| depth)
                .collect::<BTreeSet<_>>()
                .len(),
            shared_pre.class
        ),
        format!(
            "resident = the whole artifact ({} octets)",
            pre_octets.len()
        )
    ));
    rows.push(format!(
        "{:<20} {:<58} {:<40}",
        "ARM N-post",
        format!(
            "{} ladder hops · {} row comparisons · {} arcs taken · {} germ cells folded",
            work_post.ladder_hops,
            work_post.row_comparisons,
            work_post.arcs_taken,
            work_post.germ_cells_folded
        ),
        format!("artifact {} octets", post_octets.len())
    ));
    rows.push(format!(
        "{:<20} {:<58} {:<40}",
        "(P3, P5)",
        format!(
            "faces returned: 1 plural section, {} germs over {} ladder depths, landed {}",
            shared_post.offered.len(),
            shared_post
                .offered
                .iter()
                .map(|(_, _, depth)| depth)
                .collect::<BTreeSet<_>>()
                .len(),
            shared_post.class
        ),
        format!(
            "resident = the whole artifact ({} octets)",
            post_octets.len()
        )
    ));
    rows.push(format!(
        "{:<20} {:<58} {:<40}",
        "THE LIFTED",
        "exact rational compositions over Rat; no launch, no card, no float.",
        "chi-faces.tsv 407 · bf16-fibre-census.tsv"
    ));
    rows.push(format!(
        "{:<20} {:<58} {:<40}",
        "FAMILIES (P1)",
        "faces returned: 4 chi with kernel/image/cokernel + the whole-map fibre census",
        "299,268 octets"
    ));
    rows.push(String::new());
    rows.push(format!(
        "{:<20} {:<58}",
        "body", "the dissection atlas and the ablations that stand on it"
    ));
    rows.push(format!(
        "{:<20} {:<58}",
        "ARM F",
        "Station D's 16 matched siblings + the vision sibling; H5 reproduced 168 of 168 cells"
    ));
    rows.push(format!(
        "{:<20} {:<58}",
        "ARM N-pre",
        "this deed's 7 taxa; P0's construction-level rebuild ablation (honest boundary named)"
    ));
    rows.push(format!(
        "{:<20} {:<58}",
        "ARM N-post",
        "this deed's 7 taxa; P3's IN-BODY withdrawal, octet-identical to the predecessor"
    ));
    rows.push(format!(
        "{:<20} {:<58}",
        "THE LIFTED FAMILIES",
        "P1's two-cause ablation, plural-diffed, with a bit-identical unrelated control"
    ));
    rows.push(String::new());
    rows.push(format!(
        "  the native codec landed the shared material at class {} (pre) and {} (post); the work counter's landed class agrees with the law's: {} / {}",
        shared_pre.class,
        shared_post.class,
        work_pre.landed == shared_pre.class,
        work_post.landed == shared_post.class
    ));
    rows.push(format!(
        "  the two bodies' vocabularies: {} germs (pre) and {} (post); ARM F's codebook is 262,144 wide and shares no germ with either.",
        pre.vocabulary.len(),
        post.vocabulary.len()
    ));
    rows
}
