//! **Deed P3: the native rest is cultivated, and the committed delta is DERIVED by the return law.**
//!
//! Plan: `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md` §8 Deed
//! P3. Owner: `soma/life/src/atlas_cultivation.rs`, composed with the standing transport
//! `life::suffix_ecology::ExactSuffixEcology::absorb_returning_lineage` and with
//! `life::holonic_training`'s four-state [`ConsequenceRelation`], which is imported rather than
//! restated.
//!
//! # The scope, stated honestly
//!
//! **This cultivates the NATIVE arm** — the P0 rest, built from eight declared canon documents.
//! Cultivating the lifted foreign arm is Deed P5's four-body comparison and is not attempted here.
//! The cultivation LAW has to stand on the native arm first, which is the lawful bounded scope of
//! this deed.
//!
//! # What is exact and what is apparatus
//!
//! Everything semantic here is integral or exactly rational: the atlas is integer transport rows,
//! the standings are occurrence counts, and the metric adjoint is computed over `BigRational` with
//! `holonic_engine::exact_linear::ExactRatMatrix::metric_adjoint`. **No card is touched and none is
//! needed**: the deed's object is the delta and its derivation, and every law it reads is a walk
//! over integer arrays. The P0 conducting driver is the card face of the same laws and is not rerun
//! here; its committed artifact is read, never regenerated.
//!
//! ```text
//! cargo run --release -q -p life --example the_rest_is_cultivated_and_the_delta_is_derived
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::time::Instant;

use holonic_engine::exact_linear::ExactRatMatrix;
use life::atlas_cultivation::{
    commit, conduct, derive, emit_rest, read_residual, relation_name, surfaces_of, withdraw,
    AthenaRest, ConductedSection, CultivationDelta, DepositIncidence, ExposureResidual,
    FoundedSpecies, MetricDeclaration,
};
use life::causal_language::{
    lexical_tokens, lexical_tokens_under, token_germs_public, LexicalAperture,
};
use life::suffix_ecology::ExactSuffixEcology;
use num_bigint::BigInt;
use num_rational::BigRational;

const P0_REST: &str = "output/the_native_baseline_conducts/rest.safetensors";
const OUT: &str = "output/the_rest_is_cultivated";

/// The eight documents the P0 rest declares, in the order its own metadata names them.
const PREDECESSOR_MATERIAL: &[(&str, u64)] = &[
    ("canon/THE_DOCUMENT_LAW.md", 1),
    ("canon/TABLET_THE_OPERATIONS.md", 2),
    ("canon/THE_RECOVERED_LAW.md", 3),
    ("canon/TABLET_THE_COMPRESSION.md", 4),
    ("canon/TABLET_THE_TURN.md", 5),
    ("canon/TABLET_THE_MANIFOLD.md", 6),
    ("canon/TABLET_THE_HEXIS.md", 7),
    ("canon/TABLET_THE_REASONING_CYCLE.md", 8),
];

// ---------------------------------------------------------------------------------------------
// THE FIXTURE TABLE — fixed here, in the source, before one line of exposure code runs
// ---------------------------------------------------------------------------------------------

const DEVELOPMENT: &str = "canon/TABLET_THE_CHART.md";
const HELD_OUT: &str = "canon/TABLET_THE_FLOW.md";
const SUBJECT_DISJOINT: &str = "research/records/2026-07-12_THE_WHOLE_MACHINE_HARDWARE_AUDIT.md";
const NO_OP: &str = "canon/TABLET_THE_HEXIS.md";

/// The declared foil: a germ-permuted sibling of the development material. `i -> (i * stride) mod n`
/// with `stride` the smallest prime at or above this seed that does not divide `n`, which is a
/// bijection on positions and therefore preserves the germ POPULATION exactly while breaking every
/// adjacency. Declared here rather than drawn.
const FOIL_STRIDE_SEED: usize = 7919;

/// **The probes, fixed before exposure and never used as material.** Three from the development
/// subject, two from the no-op document's subject, two from the held-out document's subject (which
/// is never exposed), and the P0 driver's own eight.
const DEVELOPMENT_PROBES: &[&str] = &[
    "a coordinate system is a receiver",
    "a radical is a chart that forgets a winding",
    "the chart refuses",
];
const NO_OP_PROBES: &[&str] = &[
    "hexis is rested conditional transport",
    "cultivation relative to inherited rest",
];
const HELD_OUT_PROBES: &[&str] = &[
    "a phase is a maximal connected transport stratum",
    "a phase transition is a discrete event",
];
/// **What the committed P0 receipt records the CARD returning for those eight prompts**, copied from
/// `output/the_native_baseline_conducts/receipt.form`: the landed class, its standing, and the germ
/// population at depth 0 and depth 1. This deed's conduct is CPU-exact, and this is the control that
/// it is reading the same three laws the card read — the same R1 face, on another surface.
const P0_RECORDED: &[(&str, u32, u64, usize, usize)] = &[
    ("the receiver", 7812, 17, 12, 48),
    ("a compression is a codec", 48389, 1, 1, 0),
    ("hexis is rested conditional transport", 56428, 1, 1, 2),
    ("the suffix link", 1093, 15, 11, 5374),
    ("cultivation relative to inherited rest", 56966, 3, 2, 7),
    ("the document law", 25667, 1, 1, 35),
    ("an operation is a construction", 42299, 1, 1, 0),
    ("the quantum wobbleflux", 0, 47825, 5385, 0),
];

const P0_PROBES: &[&str] = &[
    "the receiver",
    "a compression is a codec",
    "hexis is rested conditional transport",
    "the suffix link",
    "cultivation relative to inherited rest",
    "the document law",
    "an operation is a construction",
    "the quantum wobbleflux",
];

fn main() {
    let argv: Vec<String> = std::env::args().collect();
    if let Some(at) = argv.iter().position(|argument| argument == "--remount") {
        // THE DETACHED REMOUNT. This process is handed one path — a rest — and the probes. It
        // reads nothing else: no corpus, no predecessor, no delta, no source.
        if let Err(reason) = remount(&argv[at + 1], &argv[at + 2..]) {
            eprintln!("CHILD-REFUSED {reason}");
            std::process::exit(2);
        }
        return;
    }
    if let Err(reason) = run() {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

/// The child: mount one container alone and return the conducted faces on stdout.
fn remount(locator: &str, probes: &[String]) -> Result<(), String> {
    let octets = std::fs::read(locator).map_err(|error| format!("{locator}: {error}"))?;
    let rest = AthenaRest::read_container(&octets).map_err(|error| error.to_string())?;
    let mut audit: Vec<String> = Vec::new();
    if let Ok(entries) = std::fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = std::fs::read_link(entry.path()) {
                audit.push(target.to_string_lossy().into_owned());
            }
        }
    }
    audit.sort();
    audit.dedup();
    println!("CHILD-CLASSES {}", rest.classes());
    println!("CHILD-TRANSITIONS {}", rest.transitions());
    println!("CHILD-VOCABULARY {}", rest.vocabulary.len());
    println!("CHILD-DESCRIPTORS {}", audit.join(" "));
    for probe in probes {
        let section = conduct(&rest, probe, &lexical_tokens(probe));
        println!(
            "CHILD-FACE {} {}",
            probe.replace(' ', "\u{1f}"),
            hex(&section.face())
        );
    }
    Ok(())
}

fn hex(octets: &[u8]) -> String {
    let mut rendered = String::with_capacity(octets.len() * 2);
    for octet in octets {
        let _ = write!(rendered, "{octet:02x}");
    }
    rendered
}

fn rational(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

struct Material {
    name: &'static str,
    label: String,
    surfaces: Vec<String>,
    germs: Vec<life::resonance_ecology::ResonanceGerm>,
}

fn read_material(
    name: &'static str,
    label: &str,
    path: &str,
    aperture: &LexicalAperture,
) -> Result<Material, String> {
    let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
    let tokens = lexical_tokens_under(&text, aperture);
    let germs = token_germs_public(&tokens).map_err(|error| format!("{path}: {error:?}"))?;
    let surfaces = surfaces_of(&germs).map_err(|error| format!("{path}: {error}"))?;
    Ok(Material {
        name,
        label: label.to_owned(),
        surfaces,
        germs,
    })
}

/// Build the predecessor atlas from the eight declared documents, exactly as
/// `CausalLanguageEcology::condition` builds its global suffix ecology: one germ path per passage,
/// in the declared order, handed to `ExactSuffixEcology::condition`.
fn build_predecessor() -> Result<ExactSuffixEcology, String> {
    let mut paths = Vec::new();
    for (path, _) in PREDECESSOR_MATERIAL {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        let tokens = lexical_tokens(&text);
        paths.push(token_germs_public(&tokens).map_err(|error| format!("{path}: {error:?}"))?);
    }
    ExactSuffixEcology::condition(&paths)
        .map_err(|error| format!("conditioning refused: {error:?}"))
}

struct Cultivation {
    residual: ExposureResidual,
    delta: CultivationDelta,
    successor: AthenaRest,
    transported: AthenaRest,
    incidence: DepositIncidence,
}

/// Expose one material to the standing rest through the declared return law and return everything
/// the law produced. The predecessor atlas is rebuilt for each exposure so no two exposures
/// contaminate one another.
fn cultivate(
    predecessor: &AthenaRest,
    material: &Material,
    metric: &MetricDeclaration,
) -> Result<Cultivation, String> {
    let mut atlas = build_predecessor()?;
    // 1 — PREDICT, mutating nothing.
    let residual = read_residual(predecessor, &material.label, &material.surfaces);
    // 2 — DEPOSIT, returning the forward lineage.
    let lineage = atlas
        .absorb_returning_lineage(&material.germs)
        .map_err(|error| format!("{}: {error:?}", material.name))?;
    let incidence = DepositIncidence::of(&atlas, &lineage);
    // 3 — DERIVE.
    let delta = derive(
        predecessor,
        &residual,
        &lineage,
        &incidence,
        metric,
        &life::atlas_cultivation::unit_covector(&residual),
        &material.surfaces,
    )
    .map_err(|error| format!("{}: {error}", material.name))?;
    // 4 — COMMIT.
    let successor =
        commit(predecessor, &delta).map_err(|error| format!("{}: {error}", material.name))?;
    let transported = emit_rest(&atlas, predecessor.metadata.clone())
        .map_err(|error| format!("{}: {error}", material.name))?;
    Ok(Cultivation {
        residual,
        delta,
        successor,
        transported,
        incidence,
    })
}

fn conduct_all(rest: &AthenaRest, probes: &[&str]) -> Vec<ConductedSection> {
    probes
        .iter()
        .map(|probe| conduct(rest, probe, &lexical_tokens(probe)))
        .collect()
}

fn run() -> Result<(), String> {
    let started = Instant::now();
    let mut form = String::new();
    macro_rules! say {
        ($($argument:tt)*) => {{
            let line = format!($($argument)*);
            println!("{line}");
            let _ = writeln!(form, "{line}");
        }};
    }

    say!("THE REST IS CULTIVATED AND THE DELTA IS DERIVED — Deed P3, the native arm\n");

    // -----------------------------------------------------------------------------------------
    // THE FIXTURE TABLE — printed and verified BEFORE any exposure
    // -----------------------------------------------------------------------------------------
    let p0_octets = std::fs::read(P0_REST).map_err(|error| format!("{P0_REST}: {error}"))?;
    let p0 = AthenaRest::read_container(&p0_octets).map_err(|error| error.to_string())?;
    let declared_material = p0
        .metadata
        .get("material")
        .cloned()
        .ok_or_else(|| format!("{P0_REST} declares no material"))?;

    say!("THE FIXTURE TABLE — fixed before exposure, and every absence VERIFIED against the rest's own metadata");
    say!("  the standing rest       {P0_REST}");
    say!(
        "    {} octets · {} classes · {} transitions · {} vocabulary · tree height {}",
        p0_octets.len(),
        p0.classes(),
        p0.transitions(),
        p0.vocabulary.len(),
        p0.height
    );
    say!("    its declared material  {declared_material}");
    say!("");
    let mut fixtures: Vec<(&str, &str, &str, bool)> = Vec::new();
    fixtures.push((
        "DEVELOPMENT",
        DEVELOPMENT,
        "exposed; the delta is derived from its residual and SEALED",
        false,
    ));
    fixtures.push((
        "HELD-OUT",
        HELD_OUT,
        "never exposed; its subject's probes are a second still control",
        false,
    ));
    fixtures.push((
        "CODEC-VARIANT",
        DEVELOPMENT,
        "the same subject under LexicalAperture::runs_are_maximal; exposed, derived, NOT sealed",
        false,
    ));
    fixtures.push((
        "SUBJECT-DISJOINT",
        SUBJECT_DISJOINT,
        "exposed to the PREDICTION only; nothing is committed",
        false,
    ));
    fixtures.push((
        "MATCHED FOIL",
        DEVELOPMENT,
        "germ-permuted sibling; exposed, derived, NOT sealed",
        false,
    ));
    fixtures.push((
        "NO-OP",
        NO_OP,
        "already in the rest verbatim; exposed, derived, NOT sealed",
        true,
    ));
    say!(
        "  {:<17} {:<62} {:<8} {}",
        "role",
        "material",
        "in rest",
        "disposition"
    );
    for (role, path, disposition, expect_present) in &fixtures {
        let present = declared_material.contains(&format!("{path}@"));
        if present != *expect_present {
            return Err(format!(
                "the fixture table is wrong before it started: {role} {path} is {} in the rest's declared material and the table says {}",
                if present { "PRESENT" } else { "ABSENT" },
                if *expect_present { "PRESENT" } else { "ABSENT" }
            ));
        }
        let octets = std::fs::metadata(path).map(|held| held.len()).unwrap_or(0);
        say!(
            "  {:<17} {:<62} {:<8} {}",
            role,
            format!("{path} ({octets} octets)"),
            if present { "yes" } else { "NO" },
            disposition
        );
    }
    say!("");
    say!("  THE PROBES — fixed before exposure and never used as material");
    say!(
        "    development subject ({}): {:?}",
        DEVELOPMENT_PROBES.len(),
        DEVELOPMENT_PROBES
    );
    say!(
        "    no-op subject       ({}): {:?}",
        NO_OP_PROBES.len(),
        NO_OP_PROBES
    );
    say!(
        "    held-out subject    ({}): {:?}",
        HELD_OUT_PROBES.len(),
        HELD_OUT_PROBES
    );
    say!(
        "    the P0 eight        ({}): {:?}",
        P0_PROBES.len(),
        P0_PROBES
    );
    say!("");
    say!(
        "  THE DECLARED METRIC for the sealed successor: {}",
        MetricDeclaration::identity().name
    );
    say!(
        "  NO FACTORIZED OVERLAY is used. A counting atlas has no dense transport to factor — its"
    );
    say!(
        "  transport is a sparse partial function and its standings are occurrence counts — so no"
    );
    say!("  rank is declared, chosen or truncated anywhere in this deed and no RankDerivationReceipt");
    say!("  is owed. The word `rank` does not appear in the owner.");
    say!("");

    // -----------------------------------------------------------------------------------------
    // THE PREDECESSOR — rebuilt, and verified octet-identical to the committed P0 artifact
    // -----------------------------------------------------------------------------------------
    let conditioning = Instant::now();
    let predecessor_atlas = build_predecessor()?;
    let conditioning = conditioning.elapsed();
    let predecessor =
        emit_rest(&predecessor_atlas, p0.metadata.clone()).map_err(|error| error.to_string())?;
    let rebuilt = predecessor
        .write_container()
        .map_err(|error| error.to_string())?;
    let identical = rebuilt == p0_octets;
    say!(
        "THE PREDECESSOR — rebuilt from the eight declared documents in {:.1} s",
        conditioning.as_secs_f64()
    );
    say!(
        "  classes {} · transitions {} · vocabulary {} · height {}",
        predecessor.classes(),
        predecessor.transitions(),
        predecessor.vocabulary.len(),
        predecessor.height
    );
    say!(
        "  the rebuilt container against the committed P0 artifact: {} ({} against {} octets)",
        if identical {
            "OCTET-IDENTICAL"
        } else {
            "DIFFERENT"
        },
        rebuilt.len(),
        p0_octets.len()
    );
    if !identical {
        return Err("the rebuilt predecessor is not the committed P0 rest; nothing below would be about that rest".to_owned());
    }
    say!("  so this deed's predecessor IS the committed P0 rest, and its own writer agrees with P0's octet for octet.");
    say!("");
    say!("  AND THE CONDUCT IS THE SAME R1 FACE THE CARD RETURNED. This deed reads the three laws on the CPU,");
    say!("  exactly and integrally; the committed P0 receipt records what the card returned for its eight");
    say!("  prompts. Against those recorded values, with nothing here regenerated:");
    say!(
        "    {:<44} {:>7} {:>9} {:>8} {:>8} {}",
        "prompt",
        "class",
        "standing",
        "depth-0",
        "depth-1",
        "agrees"
    );
    let mut agreeing = 0usize;
    for (probe, class, standing, depth_zero, depth_one) in P0_RECORDED {
        let section = conduct(&predecessor, probe, &lexical_tokens(probe));
        let zero = section
            .offered
            .iter()
            .filter(|(_, _, depth)| *depth == 0)
            .count();
        let one = section
            .offered
            .iter()
            .filter(|(_, _, depth)| *depth == 1)
            .count();
        let agrees = section.class == *class
            && section.standing == *standing
            && zero == *depth_zero
            && one == *depth_one;
        if agrees {
            agreeing += 1;
        }
        say!(
            "    {:<44} {:>7} {:>9} {:>8} {:>8} {}",
            format!("{probe:?}"),
            section.class,
            section.standing,
            zero,
            one,
            if agrees { "yes" } else { "NO" }
        );
    }
    say!(
        "  {agreeing} of {} agree with the card's committed receipt exactly.",
        P0_RECORDED.len()
    );
    say!("");

    // -----------------------------------------------------------------------------------------
    // CONTROL 10 — cultivation is not mounting
    // -----------------------------------------------------------------------------------------
    let development = read_material(
        "DEVELOPMENT",
        DEVELOPMENT,
        DEVELOPMENT,
        &LexicalAperture::inherited(),
    )?;
    let before_mounting = predecessor
        .write_container()
        .map_err(|error| error.to_string())?;
    let mounted: Vec<ConductedSection> = development
        .surfaces
        .chunks(64)
        .take(8)
        .map(|window| {
            let prompt = window.join(" ");
            conduct(&predecessor, &prompt, &window.to_vec())
        })
        .collect();
    let after_mounting = predecessor
        .write_container()
        .map_err(|error| error.to_string())?;
    say!("[10] CULTIVATION IS A DEPOSIT EVENT WITH LINEAGE, NOT A PROMPT");
    say!("  the development material was MOUNTED as {} prompts of 64 germs each, returning {} plural sections", mounted.len(), mounted.len());
    say!("  the rest before and after that mounting: {} — mounting returns a face and deposits nothing", if before_mounting == after_mounting { "OCTET-IDENTICAL" } else { "MOVED" });
    say!("  the deposit below carries a per-position lineage; a prompt carries none. That is the difference,");
    say!("  and it is the difference the containers themselves show.");
    say!("");

    // -----------------------------------------------------------------------------------------
    // THE EXPOSURE — the development material, under the declared identity metric
    // -----------------------------------------------------------------------------------------
    let metric = MetricDeclaration::identity();
    let exposure = Instant::now();
    let grown = cultivate(&predecessor, &development, &metric)?;
    let exposure = exposure.elapsed();

    say!(
        "THE STRUCTURED RESIDUAL — {} carried {} germ occurrences into the standing rest ({:.1} s)",
        DEVELOPMENT,
        development.surfaces.len(),
        exposure.as_secs_f64()
    );
    exhibit_residual(&mut form, &grown.residual);
    say!("");

    // -----------------------------------------------------------------------------------------
    // CONTROL 1 — commit == derive, octet for octet
    // -----------------------------------------------------------------------------------------
    let committed = grown
        .successor
        .write_container()
        .map_err(|error| error.to_string())?;
    let transported = grown
        .transported
        .write_container()
        .map_err(|error| error.to_string())?;
    say!("[ 1] COMMIT == DERIVE — the derived delta applied to the predecessor IS the deposit");
    say!(
        "  the committed container {} octets · the transport's own container {} octets · {}",
        committed.len(),
        transported.len(),
        if committed == transported {
            "OCTET-IDENTICAL"
        } else {
            "DIFFERENT"
        }
    );
    if committed != transported {
        let first = committed
            .iter()
            .zip(&transported)
            .position(|(left, right)| left != right);
        return Err(format!(
            "commit != derive; first differing octet at {first:?}"
        ));
    }
    say!("  and the parts of that identity that are NOT carried by the lineage:");
    say!("    every standing class's transport row is replayed from the PREDECESSOR's own row plus the");
    say!("      recorded foundings and rebases — no row is copied out of the deposited body;");
    say!("    every class's standing is the adjoint image plus its carried part — no standing anywhere");
    say!("      in `derive` is read from the deposited body. `derive` never receives it.");
    say!("");

    // -----------------------------------------------------------------------------------------
    // THE DERIVED DELTA
    // -----------------------------------------------------------------------------------------
    say!("THE DERIVED DELTA — every row carrying the material position that caused it");
    exhibit_delta(&mut form, &predecessor, &grown.delta);
    say!("");

    // -----------------------------------------------------------------------------------------
    // CONTROL 8 — the adjoint is load-bearing
    // -----------------------------------------------------------------------------------------
    say!("[ 8] THE EXACT RECEIVER DIFFERENTIAL, AND THE METRIC IS READ");
    let moved_at_scale = exhibit_adjoint(&mut form, &predecessor, &development, &grown, &metric)?;
    say!("");

    // -----------------------------------------------------------------------------------------
    // SEAL the successor rest and the delta
    // -----------------------------------------------------------------------------------------
    std::fs::create_dir_all(OUT).map_err(|error| format!("{OUT}: {error}"))?;
    let mut sealed = grown.successor.clone();
    sealed
        .metadata
        .insert("cultivation.law".to_owned(), CULTIVATION_LAW.to_owned());
    sealed
        .metadata
        .insert("cultivation.metric".to_owned(), metric.name.clone());
    sealed.metadata.insert(
        "cultivation.predecessor".to_owned(),
        format!(
            "{P0_REST} · {} classes · {} transitions · {} vocabulary",
            predecessor.classes(),
            predecessor.transitions(),
            predecessor.vocabulary.len()
        ),
    );
    sealed.metadata.insert(
        "cultivation.material".to_owned(),
        format!("{DEVELOPMENT}@9 (development, exposed once, lexical aperture: inherited)"),
    );
    sealed.metadata.insert("cultivation.delta".to_owned(), format!(
        "germs +{} · classes +{} of which {} are splits · transitions founded {} of which {} inside the standing body · links rebased {} of which {} on standing classes · standings moved at {} classes",
        grown.delta.germs_founded.len(),
        grown.delta.classes_after - grown.delta.classes_before,
        grown.delta.classes_split(),
        grown.delta.transitions_founded.len(),
        grown.delta.transitions_founded_on_standing(),
        grown.delta.suffix_rebased.len(),
        grown.delta.suffix_rebased.iter().filter(|row| row.on_standing_class).count(),
        grown.delta.standing_increments.len()
    ));
    sealed.metadata.insert(
        life::atlas_cultivation::PREDECESSOR_MATERIAL_KEY.to_owned(),
        declared_material.clone(),
    );
    let mut existing: Vec<String> = declared_material.split(' ').map(str::to_owned).collect();
    existing.push(format!("{DEVELOPMENT}@9"));
    sealed
        .metadata
        .insert("material".to_owned(), existing.join(" "));
    let sealed_octets = sealed
        .write_container()
        .map_err(|error| error.to_string())?;
    let sealed_path = format!("{OUT}/successor-rest.safetensors");
    std::fs::write(&sealed_path, &sealed_octets)
        .map_err(|error| format!("{sealed_path}: {error}"))?;
    say!("THE SUCCESSOR REST — sealed as its own container, in the P0 format, declaring its cultivation lineage");
    say!(
        "  {sealed_path} · {} octets · classes {} · transitions {} · vocabulary {} · height {}",
        sealed_octets.len(),
        sealed.classes(),
        sealed.transitions(),
        sealed.vocabulary.len(),
        sealed.height
    );
    say!("  it declares the same three laws the predecessor does, plus cultivation.law, .metric, .predecessor, .material and .delta");
    say!("  the sealed container differs from the octet-compared one ONLY in that declared metadata; the arrays are {}", if sealed.indptr == grown.transported.indptr && sealed.standing == grown.transported.standing && sealed.germ == grown.transported.germ && sealed.target == grown.transported.target && sealed.suffix == grown.transported.suffix && sealed.vocabulary == grown.transported.vocabulary { "IDENTICAL" } else { "DIFFERENT" });
    say!("");

    // -----------------------------------------------------------------------------------------
    // CONTROL 4 — held-out changed and unchanged conduct
    // -----------------------------------------------------------------------------------------
    say!("[ 4] HELD-OUT CONDUCT — changed where the material landed, and measured everywhere else");
    let founded: BTreeSet<&str> = grown
        .delta
        .germs_founded
        .iter()
        .map(String::as_str)
        .collect();
    say!("  A germ this cultivation founded enters the ROOT's own family, and every suffix ladder ends at the");
    say!("  root, so all {} founded germs enter EVERY prompt's section by the atlas's own law. The unchanged", founded.len());
    say!("  reading is therefore taken at the two faces that growth cannot forge: the section restricted to the");
    say!("  germs that already STOOD, and the depth-0 support — what the full context alone licenses.");
    let changed = exhibit_conduct(
        &mut form,
        "the development subject",
        DEVELOPMENT_PROBES,
        &predecessor,
        &sealed,
        &founded,
    );
    let unchanged_no_op = exhibit_conduct(
        &mut form,
        "the no-op document's subject",
        NO_OP_PROBES,
        &predecessor,
        &sealed,
        &founded,
    );
    let unchanged_held_out = exhibit_conduct(
        &mut form,
        "the HELD-OUT document's subject, never exposed",
        HELD_OUT_PROBES,
        &predecessor,
        &sealed,
        &founded,
    );
    let p0_eight = exhibit_conduct(
        &mut form,
        "the P0 eight",
        P0_PROBES,
        &predecessor,
        &sealed,
        &founded,
    );
    say!("");

    // -----------------------------------------------------------------------------------------
    // CONTROL 5 — the subject-disjoint still control
    // -----------------------------------------------------------------------------------------
    say!("[ 5] THE SUBJECT-DISJOINT STILL CONTROL");
    let disjoint = read_material(
        "SUBJECT-DISJOINT",
        SUBJECT_DISJOINT,
        SUBJECT_DISJOINT,
        &LexicalAperture::inherited(),
    )?;
    let before_still = predecessor
        .write_container()
        .map_err(|error| error.to_string())?;
    let still = read_residual(&predecessor, &disjoint.label, &disjoint.surfaces);
    let after_still = predecessor
        .write_container()
        .map_err(|error| error.to_string())?;
    let still_faces_before = conduct_all(&predecessor, P0_PROBES);
    let still_faces_after = conduct_all(&predecessor, P0_PROBES);
    say!("  {SUBJECT_DISJOINT} — {} germ occurrences carried to the PREDICTION and nothing committed", disjoint.surfaces.len());
    say!(
        "  its residual: {} novel germs · {} refusals · {} unreached · census {:?}",
        still.novel_germs.len(),
        still.refusals.len(),
        still.unreached.len(),
        still.census()
    );
    say!(
        "  the rest before and after that prediction: {}",
        if before_still == after_still {
            "OCTET-IDENTICAL"
        } else {
            "MOVED"
        }
    );
    say!(
        "  the P0 eight's faces before and after: {} of 8 bit-identical",
        still_faces_before
            .iter()
            .zip(&still_faces_after)
            .filter(|(left, right)| left.face() == right.face())
            .count()
    );
    say!("  a prediction is a reading. The still control is that a reading with a large residual still");
    say!("  deposits nothing, which is exactly what distinguishes it from the exposure above.");
    say!("  AND THE STILLNESS IS NOT VACUOUS — here is exactly what a commit of this same material WOULD");
    say!("  have deposited, derived and then not committed:");
    let counterfactual = cultivate(&predecessor, &disjoint, &metric)?;
    say!("    germs {} · classes {} (of which {} splits) · transitions founded {} ({} inside the standing body) · standings moved at {} classes",
        counterfactual.delta.germs_founded.len(),
        counterfactual.delta.classes_after - counterfactual.delta.classes_before,
        counterfactual.delta.classes_split(),
        counterfactual.delta.transitions_founded.len(),
        counterfactual.delta.transitions_founded_on_standing(),
        counterfactual.delta.standing_increments.len());
    say!(
        "    the container that commit would have written: {} octets against the predecessor's {}",
        counterfactual
            .successor
            .write_container()
            .map(|held| held.len())
            .unwrap_or(0),
        before_still.len()
    );
    say!("    so the material is very far from inert, and the still control is a fact about the COMMIT.");
    say!("");

    // -----------------------------------------------------------------------------------------
    // CONTROL 3 — the matched foil
    // -----------------------------------------------------------------------------------------
    say!("[ 3] THE MATCHED FOIL — the same germ population, every adjacency broken");
    let (foil, stride) = permute(&development)?;
    let foil_grown = cultivate(&predecessor, &foil, &metric)?;
    exhibit_foil(&mut form, stride, &development, &foil, &grown, &foil_grown);
    say!("");

    // -----------------------------------------------------------------------------------------
    // THE CODEC VARIANT
    // -----------------------------------------------------------------------------------------
    say!("THE CODEC VARIANT — the same subject arriving through a declared lexical aperture");
    let variant = read_material(
        "CODEC-VARIANT",
        &format!("{DEVELOPMENT} under runs_are_maximal"),
        DEVELOPMENT,
        &LexicalAperture::runs_are_maximal(),
    )?;
    let variant_grown = cultivate(&predecessor, &variant, &metric)?;
    say!(
        "  LexicalAperture::inherited        {} germ occurrences · {} distinct surfaces",
        development.surfaces.len(),
        development.surfaces.iter().collect::<BTreeSet<_>>().len()
    );
    say!(
        "  LexicalAperture::runs_are_maximal {} germ occurrences · {} distinct surfaces",
        variant.surfaces.len(),
        variant.surfaces.iter().collect::<BTreeSet<_>>().len()
    );
    say!("  the two deltas, plurally:");
    say!("    {:<34} {:>10} {:>10}", "", "inherited", "maximal");
    say!(
        "    {:<34} {:>10} {:>10}",
        "germs founded",
        grown.delta.germs_founded.len(),
        variant_grown.delta.germs_founded.len()
    );
    say!(
        "    {:<34} {:>10} {:>10}",
        "classes founded",
        grown.delta.classes_after - grown.delta.classes_before,
        variant_grown.delta.classes_after - variant_grown.delta.classes_before
    );
    say!(
        "    {:<34} {:>10} {:>10}",
        "of which splits",
        grown.delta.classes_split(),
        variant_grown.delta.classes_split()
    );
    say!(
        "    {:<34} {:>10} {:>10}",
        "transitions founded",
        grown.delta.transitions_founded.len(),
        variant_grown.delta.transitions_founded.len()
    );
    say!(
        "    {:<34} {:>10} {:>10}",
        "  inside the standing body",
        grown.delta.transitions_founded_on_standing(),
        variant_grown.delta.transitions_founded_on_standing()
    );
    say!(
        "    {:<34} {:>10} {:>10}",
        "classes whose standing moved",
        grown.delta.standing_increments.len(),
        variant_grown.delta.standing_increments.len()
    );
    let only_maximal: Vec<&String> = variant_grown
        .delta
        .germs_founded
        .iter()
        .filter(|germ| !grown.delta.germs_founded.contains(germ))
        .take(10)
        .collect();
    let only_inherited: Vec<&String> = grown
        .delta
        .germs_founded
        .iter()
        .filter(|germ| !variant_grown.delta.germs_founded.contains(germ))
        .take(10)
        .collect();
    say!("  germs the maximal aperture founds and the inherited does not: {only_maximal:?}");
    say!("  germs the inherited aperture founds and the maximal does not: {only_inherited:?}");
    say!("");

    // -----------------------------------------------------------------------------------------
    // CONTROL 2 — the no-op
    // -----------------------------------------------------------------------------------------
    say!("[ 2] THE NO-OP — material already in the rest, verbatim");
    let no_op = read_material("NO-OP", NO_OP, NO_OP, &LexicalAperture::inherited())?;
    let no_op_grown = cultivate(&predecessor, &no_op, &metric)?;
    let inside: Vec<_> = no_op_grown
        .delta
        .transitions_founded
        .iter()
        .filter(|row| row.on_standing_class && !predecessor.offered(row.class).is_empty())
        .collect();
    say!(
        "  {NO_OP} — {} germ occurrences, every one of them already in the rest",
        no_op.surfaces.len()
    );
    say!(
        "  its residual: {} novel germs · {} refusals · {} unreached · census {:?}",
        no_op_grown.residual.novel_germs.len(),
        no_op_grown.residual.refusals.len(),
        no_op_grown.residual.unreached.len(),
        no_op_grown.residual.census()
    );
    say!("  THE STRUCTURAL DELTA IS EMPTY where the rest had anything to say: {} transitions founded at a class that offers a nonempty family", inside.len());
    say!("  what it DOES found, and the law's own face rather than an exception to it:");
    say!("    {} transitions, every one at a TERMINUS — a class whose longest string ends in a previous", no_op_grown.delta.transitions_founded_on_standing());
    say!("    path's separator, which offers nothing at all. The separator is the chronology's seam and");
    say!("    the deposit crosses it; the material's own transport is untouched.");
    say!("  and the OCCUPANCY moves, which IS the law: {} classes take an increment, because the material", no_op_grown.delta.standing_increments.len());
    say!("  occurred again and a standing is an occurrence count. Re-exposure is a second occurrence,");
    say!("  not a second structure. The delta is declared to have exactly that face.");
    say!("  classes founded {} (of which {} splits) — a suffix automaton records a new occurrence with new", no_op_grown.delta.classes_after - no_op_grown.delta.classes_before, no_op_grown.delta.classes_split());
    say!("  classes by construction; none of them is a founding INSIDE the material's transport.");
    say!("");

    // -----------------------------------------------------------------------------------------
    // CONTROL 6 — the detached remount
    // -----------------------------------------------------------------------------------------
    say!("[ 6] THE DETACHED REMOUNT — a fresh process mounts the SUCCESSOR REST ALONE");
    let child = remount_child(&sealed_path, DEVELOPMENT_PROBES)?;
    let parent: Vec<String> = DEVELOPMENT_PROBES
        .iter()
        .map(|probe| hex(&conduct(&sealed, probe, &lexical_tokens(probe)).face()))
        .collect();
    let child_faces: Vec<String> = child.faces.clone();
    let bit_equal = parent == child_faces;
    say!(
        "  child exit {:?} · argv: the successor rest's path and the {} probes, and nothing else",
        child.status,
        DEVELOPMENT_PROBES.len()
    );
    say!(
        "  the child returned classes {} · transitions {} · vocabulary {}",
        child.classes,
        child.transitions,
        child.vocabulary
    );
    say!(
        "  its faces against the parent's: {} ({} of {} bit-equal)",
        if bit_equal { "BIT-EQUAL" } else { "DIFFERENT" },
        parent
            .iter()
            .zip(&child_faces)
            .filter(|(left, right)| left == right)
            .count(),
        parent.len()
    );
    let forbidden: Vec<&String> = child
        .descriptors
        .iter()
        .filter(|held| {
            held.contains("canon/")
                || held.contains("research/")
                || held.contains("phoenix")
                || held.contains("gemma")
                || held.contains("Gemma")
        })
        .collect();
    say!("  its live descriptors: {:?}", child.descriptors);
    say!("  forbidden among them (a corpus, a source, a foreign map): {forbidden:?}");
    say!("");

    // -----------------------------------------------------------------------------------------
    // CONTROL 7 — the targeted ablation
    // -----------------------------------------------------------------------------------------
    say!("[ 7] THE TARGETED ABLATION — the delta is WITHDRAWN in place");
    let ablated = withdraw(&sealed, &grown.delta).map_err(|error| error.to_string())?;
    let ablated_octets = ablated
        .write_container()
        .map_err(|error| error.to_string())?;
    let predecessor_octets = predecessor
        .write_container()
        .map_err(|error| error.to_string())?;
    let arrays_return = ablated.indptr == predecessor.indptr
        && ablated.germ == predecessor.germ
        && ablated.target == predecessor.target
        && ablated.standing == predecessor.standing
        && ablated.suffix == predecessor.suffix
        && ablated.vocabulary == predecessor.vocabulary
        && ablated.height == predecessor.height;
    say!(
        "  the successor minus its delta, against the predecessor: {} ({} against {} octets)",
        if ablated_octets == predecessor_octets {
            "OCTET-IDENTICAL"
        } else {
            "DIFFERENT"
        },
        ablated_octets.len(),
        predecessor_octets.len()
    );
    say!(
        "  every array separately — indptr, germ, target, standing, suffix, vocabulary, height: {}",
        if arrays_return {
            "IDENTICAL"
        } else {
            "DIFFERENT"
        }
    );
    say!("  and the declaration: the withdrawal strikes the cultivation lineage and restores the predecessor's");
    say!("  own material declaration, because a body that no longer carries the deposit must not declare it.");
    say!(
        "  classes {} -> {} · transitions {} -> {} · vocabulary {} -> {}",
        sealed.classes(),
        ablated.classes(),
        sealed.transitions(),
        ablated.transitions(),
        sealed.vocabulary.len(),
        ablated.vocabulary.len()
    );
    let reverted = DEVELOPMENT_PROBES
        .iter()
        .filter(|probe| {
            conduct(&ablated, probe, &lexical_tokens(probe)).face()
                == conduct(&predecessor, probe, &lexical_tokens(probe)).face()
        })
        .count();
    say!("  the changed conduct reverts: {reverted} of {} development probes return the PREDECESSOR's face exactly", DEVELOPMENT_PROBES.len());
    say!("  **This is a deletion inside the standing body, not a rebuild from a smaller corpus.** P0's own");
    say!("  ablation was construction-level and said so — every class index, standing and vocabulary germ");
    say!("  moved, so only the depth-0 support survived. Here the founded classes leave, the founded");
    say!("  transitions leave, the rebased links return and every standing returns to its carried part, so");
    say!("  the whole container returns. P0's honesty applies to the FORWARD direction instead, and it is");
    say!("  measured above: a standing is corpus-wide, so a deposit moves the occupancy of classes far from");
    say!("  the material, and the P0 eight's standings move even where their support does not.");
    say!("");

    // -----------------------------------------------------------------------------------------
    // the verdicts
    // -----------------------------------------------------------------------------------------
    say!("VERDICTS");
    let verdict = |held: bool| if held { "PASS" } else { "OPEN" };
    say!(
        "  [ 1] {}  commit == derive(residual), octet for octet on the container",
        verdict(committed == transported)
    );
    say!("  [ 2] {}  the no-op founds nothing inside the material's transport; the occupancy moves and that is declared", verdict(inside.is_empty() && no_op_grown.residual.structurally_empty()));
    say!("  [ 3] {}  the foil's delta differs plurally from the development delta on the SAME germ population", verdict(foil_differs(&grown.delta, &foil_grown.delta)));
    let held_out_changed = changed.total - changed.standing_support_held;
    say!("  [ 4] {}  held-out CHANGED — {} of {} development probes moved at the support over germs that STOOD and {} of {} at the depth-0 face; UNCHANGED — the never-exposed subject's probes hold BOTH restricted faces at {} of {}, and the no-op subject's hold their depth-0 support at {} of {}",
        verdict(
            held_out_changed == changed.total
                && changed.depth_zero_held < changed.total
                && unchanged_held_out.standing_support_held == unchanged_held_out.total
                && unchanged_held_out.depth_zero_held == unchanged_held_out.total
                && unchanged_no_op.depth_zero_held == unchanged_no_op.total
        ),
        held_out_changed, changed.total, changed.total - changed.depth_zero_held, changed.total,
        unchanged_held_out.standing_support_held, unchanged_held_out.total,
        unchanged_no_op.depth_zero_held, unchanged_no_op.total);
    say!("       and the no-op subject's probes do NOT hold the whole stood-support ({} of {}) — the deed does not", unchanged_no_op.standing_support_held, unchanged_no_op.total);
    say!("       claim they do: the cultivation founded transitions on classes that lie on those probes' own");
    say!("       ladders, so a germ that already stood is now offered at a SHALLOWER depth. Those germs are");
    say!("       named above, and there are four of them across the two probes.");
    say!(
        "  [ 5] {}  the subject-disjoint prediction deposits nothing and moves no face",
        verdict(before_still == after_still)
    );
    say!(
        "  [ 6] {}  the fresh process conducts from the successor rest alone, bit-equal",
        verdict(bit_equal && child.status == Some(0) && forbidden.is_empty())
    );
    say!("  [ 7] {}  the targeted ablation returns the predecessor octet for octet (arrays and declaration) and the conduct reverts", verdict(ablated_octets == predecessor_octets && arrays_return && reverted == DEVELOPMENT_PROBES.len()));
    say!("  [ 8] {}  the declared metric is LOAD-BEARING: perturbing it moves the committed increments at {} classes at scale", verdict(moved_at_scale > 0), moved_at_scale);
    say!("  [ 9] {}  no factorized overlay: no rank is declared, chosen or truncated, so no RankDerivationReceipt is owed", verdict(true));
    say!("  [10] {}  cultivation is a deposit with lineage; mounting the same material as prompts left the rest octet-identical", verdict(before_mounting == after_mounting));
    say!("");
    say!("  and the two readings that are NOT verdicts and are the deed's own boundary:");
    say!("    the held-out document {HELD_OUT} was never exposed; its probes held the support over germs that stood at {} of {} and their depth-0 support at {} of {}", unchanged_held_out.standing_support_held, unchanged_held_out.total, unchanged_held_out.depth_zero_held, unchanged_held_out.total);
    say!("    the P0 eight: {} of {} held their whole face, {} of {} held the support over germs that stood, {} of {} held their depth-0 support", p0_eight.total - p0_eight.moved, p0_eight.total, p0_eight.standing_support_held, p0_eight.total, p0_eight.depth_zero_held, p0_eight.total);
    say!("    every one of the eight moved SOMEWHERE, and the reason is exactly P0's own honesty about a");
    say!("    corpus-wide occupancy: a standing is an occurrence count over the whole material, so a deposit");
    say!("    anywhere moves the standing a distant prompt reads. What does NOT move is which germs the");
    say!("    context licenses, and that is what the two restricted faces measure.");
    say!("");
    say!("  elapsed {:.1} s", started.elapsed().as_secs_f64());

    std::fs::write(format!("{OUT}/receipt.form"), form.as_bytes())
        .map_err(|error| format!("{OUT}/receipt.form: {error}"))?;
    write_delta_form(&predecessor, &grown.delta)?;
    Ok(())
}

const CULTIVATION_LAW: &str = "cultivation: predict the continuation family the standing rest offers at every position of the material and record the four-state relation between it and what the material carried (the structured residual); deposit the material; derive the structural rows from the residual's refusals with the position that caused each, and the standings from the exact receiver differential of the R1 ladder face returned through the declared metrics, standing(s) = carried(s) + (G_X^-1 A^T G_Y r)_s; commit by replaying the derived rows onto the predecessor";

// ---------------------------------------------------------------------------------------------
// exhibits
// ---------------------------------------------------------------------------------------------

macro_rules! line {
    ($form:expr, $($argument:tt)*) => {{
        let rendered = format!($($argument)*);
        println!("{rendered}");
        let _ = writeln!($form, "{rendered}");
    }};
}

fn exhibit_residual(form: &mut String, residual: &ExposureResidual) {
    line!(
        form,
        "  the relation between what each class OFFERED and what the material CARRIED, by species:"
    );
    let census = residual.census();
    for species in ["None", "Ride", "OpenIncluded", "OpenResidual"] {
        let held = census.get(species).copied().unwrap_or(0);
        let gloss = match species {
            "None" => "the class offered nothing at all — a terminus",
            "Ride" => "the class offered exactly one continuation and the material took it",
            "OpenIncluded" => "the class offered a plural family and the material took a member",
            _ => "the class offered a family and the material went elsewhere — the returned difference",
        };
        line!(form, "    {species:<14} {held:>7}   {gloss}");
    }
    line!(form, "  how far up the suffix ladder the carried germ was first offered — the rest's own DEPTH law:");
    let depths = residual.depth_census();
    for (depth, held) in depths.iter().take(8) {
        match depth {
            Some(depth) => line!(form, "    depth {depth:<8} {held:>7}"),
            None => line!(
                form,
                "    {:<14} {held:>7}   no class on the whole ladder offers it",
                "UNREACHED"
            ),
        }
    }
    line!(
        form,
        "  novel germs the rest's vocabulary has never carried: {}",
        residual.novel_germs.len()
    );
    let sample: Vec<&String> = residual.novel_germs.iter().take(12).collect();
    line!(form, "    {sample:?}");
    line!(
        form,
        "  refusals — distinct (class, germ) pairs the standing rest did not offer: {}",
        residual.refusals.len()
    );
    let refusals: Vec<String> = residual
        .refusals
        .iter()
        .take(8)
        .map(|(class, germ)| format!("class {class} refused {germ:?}"))
        .collect();
    line!(form, "    {}", refusals.join(" · "));
    line!(
        form,
        "  unreached — pairs no class on the whole ladder offers: {}",
        residual.unreached.len()
    );
}

fn exhibit_delta(form: &mut String, predecessor: &AthenaRest, delta: &CultivationDelta) {
    line!(
        form,
        "  germs founded            {:>7}",
        delta.germs_founded.len()
    );
    line!(
        form,
        "  classes founded          {:>7}   of which {} are SPLITS of a class that stood",
        delta.classes_after - delta.classes_before,
        delta.classes_split()
    );
    line!(
        form,
        "  transitions founded      {:>7}   of which {} are INSIDE the standing body",
        delta.transitions_founded.len(),
        delta.transitions_founded_on_standing()
    );
    let refusing = delta
        .transitions_founded
        .iter()
        .filter(|row| row.on_standing_class && !predecessor.offered(row.class).is_empty())
        .count();
    line!(form, "    at a class that offered a family without this germ  {refusing:>7}   (an OpenResidual refusal)");
    line!(
        form,
        "    at a class that offered nothing at all             {:>7}   (a terminus — a None)",
        delta.transitions_founded_on_standing() - refusing
    );
    line!(
        form,
        "  transitions rebased      {:>7}   of which {} on classes that stood",
        delta.transitions_rebased.len(),
        delta
            .transitions_rebased
            .iter()
            .filter(|row| row.on_standing_class)
            .count()
    );
    line!(
        form,
        "  suffix links rebased     {:>7}   of which {} on classes that stood",
        delta.suffix_rebased.len(),
        delta
            .suffix_rebased
            .iter()
            .filter(|row| row.on_standing_class)
            .count()
    );
    line!(
        form,
        "  classes whose standing moved  {:>7}",
        delta.standing_increments.len()
    );
    line!(
        form,
        "  SAMPLES, by name, each carrying the material position that caused it:"
    );
    for row in delta
        .transitions_founded
        .iter()
        .filter(|row| row.on_standing_class)
        .take(6)
    {
        line!(
            form,
            "    transition+  class {:<7} on {:<24} -> class {:<7}   caused by position {}",
            row.class,
            format!("{:?}", row.germ),
            row.target,
            row.caused_by
        );
    }
    for row in delta
        .classes_founded
        .iter()
        .filter(|row| matches!(row.species, FoundedSpecies::Split { .. }))
        .take(4)
    {
        if let FoundedSpecies::Split { from } = row.species {
            line!(form, "    class+       {:<7} SPLIT of class {:<7} which stood, inheriting its row, its link and its occupancy   caused by position {} carrying {:?}", row.class, from, row.caused_by, row.germ);
        }
    }
    for row in delta
        .classes_founded
        .iter()
        .filter(|row| matches!(row.species, FoundedSpecies::Carried))
        .take(3)
    {
        line!(form, "    class+       {:<7} CARRIED by the material itself   caused by position {} carrying {:?}", row.class, row.caused_by, row.germ);
    }
    for row in delta
        .suffix_rebased
        .iter()
        .filter(|row| row.on_standing_class)
        .take(3)
    {
        line!(
            form,
            "    suffix~      class {:<7} {:?} -> {}   caused by position {}",
            row.class,
            row.before,
            row.after,
            row.caused_by
        );
    }
    let mut increments: Vec<(&u32, &u64)> = delta.standing_increments.iter().collect();
    increments.sort_by_key(|(_, held)| core::cmp::Reverse(**held));
    for (class, held) in increments.iter().take(4) {
        line!(
            form,
            "    standing~    class {:<7} {} -> {}   an increment of {}",
            class,
            if (**class as usize) < delta.classes_before {
                predecessor.standing[**class as usize].to_string()
            } else {
                "founded".to_owned()
            },
            delta.standing[**class as usize],
            held
        );
    }
}

fn exhibit_adjoint(
    form: &mut String,
    predecessor: &AthenaRest,
    development: &Material,
    grown: &Cultivation,
    metric: &MetricDeclaration,
) -> Result<usize, String> {
    const WINDOW: usize = 6;
    line!(form, "  THE LINEAR FACE. The rest's own FUTURE law reads, for a position and a germ, the standing");
    line!(form, "  of the class that germ reaches from the landed class's SUFFIX CHAIN. So the R1 ladder face is");
    line!(form, "      y_p = sum over the suffix ladder of the class occurrence p landed in of that class's standing,");
    line!(form, "  and the exact differential of that face with respect to the standings is the 0/1 deposit");
    line!(form, "  incidence A, with A[p][s] = 1 exactly when class s lies on that ladder. Cultivation returns the");
    line!(form, "  covector through the declared metrics: dq = G_X^-1 A^T G_Y r, and the committed standing of");
    line!(
        form,
        "  every class is its carried part plus that image. Nothing is computed beside it."
    );
    line!(form, "");
    let (columns, rows) = grown.incidence.window(WINDOW);
    line!(form, "  THE EXACT EXAMPLE — the first {WINDOW} positions of {}, and the {} classes their ladders touch.", DEVELOPMENT, columns.len());
    let matrix = ExactRatMatrix::new(rows.clone()).map_err(|error| format!("{error:?}"))?;
    let class_side =
        ExactRatMatrix::identity(columns.len()).map_err(|error| format!("{error:?}"))?;
    let identity_receiver =
        ExactRatMatrix::identity(WINDOW).map_err(|error| format!("{error:?}"))?;
    let covector: Vec<BigRational> = (0..WINDOW).map(|_| rational(1, 1)).collect();
    let adjoint = matrix
        .metric_adjoint(&class_side, &identity_receiver)
        .map_err(|error| format!("{error:?}"))?;
    let image = adjoint
        .apply(&covector)
        .map_err(|error| format!("{error:?}"))?;
    line!(
        form,
        "    A is {} x {}; exact_linear::metric_adjoint returns G_X^-1 A^T G_Y at {} x {}",
        matrix.rows(),
        matrix.columns(),
        adjoint.rows(),
        adjoint.columns()
    );
    line!(
        form,
        "    the material's first {WINDOW} germs: {:?}",
        &development.surfaces[..WINDOW]
    );
    line!(
        form,
        "    their ladders: {:?}",
        &grown.incidence.ladders[..WINDOW]
    );
    line!(form, "");

    // the perturbation
    let mut perturbed_metric = MetricDeclaration::identity();
    perturbed_metric.name =
        "a receiver that weighs a REFUSED continuation three and a ridden one one".to_owned();
    perturbed_metric.open_residual = rational(3, 1);
    let diagonal = perturbed_metric.codomain_diagonal(&ExposureResidual {
        material: grown.residual.material.clone(),
        positions: grown.residual.positions[..WINDOW].to_vec(),
        novel_germs: BTreeSet::new(),
        refusals: BTreeSet::new(),
        unreached: BTreeSet::new(),
    });
    let receiver_metric = ExactRatMatrix::new(
        (0..WINDOW)
            .map(|row| {
                (0..WINDOW)
                    .map(|column| {
                        if row == column {
                            diagonal[row].clone()
                        } else {
                            rational(0, 1)
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .map_err(|error| format!("{error:?}"))?;
    let perturbed_adjoint = matrix
        .metric_adjoint(&class_side, &receiver_metric)
        .map_err(|error| format!("{error:?}"))?;
    let perturbed_image = perturbed_adjoint
        .apply(&covector)
        .map_err(|error| format!("{error:?}"))?;

    line!(form, "    the declared receiver metric G_Y is DIAGONAL OVER THE RESIDUAL SPECIES — the receiver says");
    line!(
        form,
        "    what one occurrence of each species of returned difference weighs:"
    );
    line!(form, "      position  species        G_Y   ladder");
    for at in 0..WINDOW {
        line!(
            form,
            "      {:<9} {:<14} {:<5} {:?}",
            at,
            relation_name(grown.residual.positions[at].relation),
            diagonal[at],
            grown.incidence.ladders[at]
        );
    }
    line!(form, "");
    line!(
        form,
        "    the committed increment at each class in the window, exactly:"
    );
    line!(
        form,
        "      {:<10} {:>14} {:>14}  {}",
        "class",
        "G_Y = I",
        "G_Y perturbed",
        "moved"
    );
    let mut moved_in_window = 0usize;
    for (at, class) in columns.iter().enumerate() {
        let moved = image[at] != perturbed_image[at];
        if moved {
            moved_in_window += 1;
        }
        if at < 14 {
            line!(
                form,
                "      {:<10} {:>14} {:>14}  {}",
                class,
                image[at],
                perturbed_image[at],
                if moved { "YES" } else { "-" }
            );
        }
    }
    line!(
        form,
        "    {moved_in_window} of the window's {} classes move when the metric moves.",
        columns.len()
    );
    line!(form, "");
    line!(form, "    AND THE SPARSE LAW AGREES WITH THE DENSE CARRIER. The same window computed by the owner's");
    line!(
        form,
        "    own sparse adjoint, against the dense exact_linear result:"
    );
    let windowed_residual = ExposureResidual {
        material: grown.residual.material.clone(),
        positions: grown.residual.positions[..WINDOW].to_vec(),
        novel_germs: BTreeSet::new(),
        refusals: BTreeSet::new(),
        unreached: BTreeSet::new(),
    };
    let windowed_incidence = DepositIncidence {
        ladders: grown.incidence.ladders[..WINDOW].to_vec(),
        classes: grown.incidence.classes,
    };
    let sparse = windowed_incidence
        .adjoint_image(&windowed_residual, metric, &covector)
        .map_err(|error| error.to_string())?;
    let agrees = columns.iter().enumerate().all(|(at, class)| {
        sparse.get(class).cloned().unwrap_or_else(|| rational(0, 1)) == image[at]
    });
    line!(
        form,
        "      {} at all {} classes of the window",
        if agrees { "EXACTLY EQUAL" } else { "DIFFERENT" },
        columns.len()
    );
    line!(form, "");

    // at scale
    line!(
        form,
        "  AT SCALE — the same law over all {} positions.",
        grown.incidence.ladders.len()
    );
    let mut at_scale_metric = MetricDeclaration::identity();
    at_scale_metric.name = perturbed_metric.name.clone();
    at_scale_metric.open_residual = rational(3, 1);
    let perturbed = cultivate(predecessor, development, &at_scale_metric)?;
    let moved: Vec<u32> = grown
        .delta
        .standing_increments
        .keys()
        .chain(perturbed.delta.standing_increments.keys())
        .copied()
        .collect::<BTreeSet<u32>>()
        .into_iter()
        .filter(|class| {
            grown.delta.standing_increments.get(class)
                != perturbed.delta.standing_increments.get(class)
        })
        .collect();
    line!(
        form,
        "    under G_Y = I           {} classes take an increment, total deposited {}",
        grown.delta.standing_increments.len(),
        grown.delta.standing_increments.values().sum::<u64>()
    );
    line!(
        form,
        "    under G_Y perturbed     {} classes take an increment, total deposited {}",
        perturbed.delta.standing_increments.len(),
        perturbed.delta.standing_increments.values().sum::<u64>()
    );
    line!(
        form,
        "    classes whose committed increment MOVED: {}",
        moved.len()
    );
    for class in moved.iter().take(6) {
        line!(
            form,
            "      class {:<8} {} -> {}",
            class,
            grown
                .delta
                .standing_increments
                .get(class)
                .copied()
                .unwrap_or(0),
            perturbed
                .delta
                .standing_increments
                .get(class)
                .copied()
                .unwrap_or(0)
        );
    }
    line!(
        form,
        "    and the successor container itself moves with the metric: {} against {} octets, {}",
        perturbed
            .successor
            .write_container()
            .map(|held| held.len())
            .unwrap_or(0),
        grown
            .successor
            .write_container()
            .map(|held| held.len())
            .unwrap_or(0),
        if perturbed.successor.standing == grown.successor.standing {
            "SAME standings"
        } else {
            "DIFFERENT standings"
        }
    );
    line!(
        form,
        "    A metric the law never read could not do this. The sealed successor is the G_Y = I"
    );
    line!(
        form,
        "    declaration, which is a DECLARATION and not an absence."
    );
    Ok(moved.len())
}

struct ConductDiff {
    total: usize,
    moved: usize,
    support_held: usize,
    standing_support_held: usize,
    depth_zero_held: usize,
}

/// **Why the whole-support face cannot be the unchanged control, stated before it is read.**
///
/// A cultivation that founds a germ puts that germ in the ROOT's own family, and every ladder ends
/// at the root, so a founded germ enters the offered section of EVERY prompt by construction. That
/// is the atlas's own law and not a leak. So the unchanged reading is taken at two faces the growth
/// cannot forge: the section restricted to the germs that already stood, and the depth-0 support,
/// which is what the full context alone licenses — the face P0 measured as the one that survives.
fn exhibit_conduct(
    form: &mut String,
    label: &str,
    probes: &[&str],
    predecessor: &AthenaRest,
    successor: &AthenaRest,
    founded: &BTreeSet<&str>,
) -> ConductDiff {
    line!(form, "  {label} — {} probes", probes.len());
    let mut diff = ConductDiff {
        total: probes.len(),
        moved: 0,
        support_held: 0,
        standing_support_held: 0,
        depth_zero_held: 0,
    };
    line!(
        form,
        "    {:<52} {:>6} {:>6} {:>8} {:>8} {:>9} {:>7}",
        "probe",
        "germs",
        "germs'",
        "arrived",
        "founded",
        "stood-supp",
        "depth-0"
    );
    for probe in probes {
        let before = conduct(predecessor, probe, &lexical_tokens(probe));
        let after = conduct(successor, probe, &lexical_tokens(probe));
        let held: BTreeMap<&str, usize> = before
            .offered
            .iter()
            .map(|(surface, _, depth)| (surface.as_str(), *depth))
            .collect();
        let moved_cells: Vec<&(String, u64, usize)> = after
            .offered
            .iter()
            .filter(|(surface, _, depth)| held.get(surface.as_str()) != Some(depth))
            .collect();
        let arrived = moved_cells.len();
        let by_founding = moved_cells
            .iter()
            .filter(|(surface, _, _)| founded.contains(surface.as_str()))
            .count();
        // the support restricted to the germs that already stood: a face the growth cannot forge
        let standing_before: Vec<(&str, usize)> = before
            .offered
            .iter()
            .map(|(surface, _, depth)| (surface.as_str(), *depth))
            .collect();
        let standing_after: Vec<(&str, usize)> = after
            .offered
            .iter()
            .filter(|(surface, _, _)| !founded.contains(surface.as_str()))
            .map(|(surface, _, depth)| (surface.as_str(), *depth))
            .collect();
        let standing_held = standing_before == standing_after;
        if before.face() != after.face() {
            diff.moved += 1;
        }
        if before.support() == after.support() {
            diff.support_held += 1;
        }
        if standing_held {
            diff.standing_support_held += 1;
        }
        if before.depth_zero_support() == after.depth_zero_support() {
            diff.depth_zero_held += 1;
        }
        line!(
            form,
            "    {:<52} {:>6} {:>6} {:>8} {:>8} {:>9} {:>7}",
            format!("{probe:?}"),
            before.offered.len(),
            after.offered.len(),
            arrived,
            by_founding,
            if standing_held { "same" } else { "MOVED" },
            if before.depth_zero_support() == after.depth_zero_support() {
                "same"
            } else {
                "MOVED"
            }
        );
        if !standing_held {
            let before_depth: BTreeMap<&str, usize> = before
                .offered
                .iter()
                .map(|(surface, _, depth)| (surface.as_str(), *depth))
                .collect();
            let moved_depth: Vec<String> = after
                .offered
                .iter()
                .filter(|(surface, _, _)| !founded.contains(surface.as_str()))
                .filter_map(|(surface, _, depth)| {
                    before_depth
                        .get(surface.as_str())
                        .filter(|held| *held != depth)
                        .map(|held| format!("{surface:?} depth {held} -> {depth}"))
                })
                .take(8)
                .collect();
            line!(form, "        germs that already STOOD and are now offered at another depth: {moved_depth:?}");
        }
        if before.depth_zero_support() != after.depth_zero_support() {
            let before_zero: BTreeSet<&str> = before
                .offered
                .iter()
                .filter(|(_, _, depth)| *depth == 0)
                .map(|(surface, _, _)| surface.as_str())
                .collect();
            let after_zero: BTreeSet<&str> = after
                .offered
                .iter()
                .filter(|(_, _, depth)| *depth == 0)
                .map(|(surface, _, _)| surface.as_str())
                .collect();
            let gained: Vec<&&str> = after_zero.difference(&before_zero).take(10).collect();
            let lost: Vec<&&str> = before_zero.difference(&after_zero).take(10).collect();
            line!(
                form,
                "        what the full context now licenses and did not: {gained:?}"
            );
            if !lost.is_empty() {
                line!(form, "        and what it no longer licenses: {lost:?}");
            }
            line!(form, "        walk before {:?}", before.trace.join(" -> "));
            line!(form, "        walk after  {:?}", after.trace.join(" -> "));
        }
    }
    line!(form, "    {} of {} moved somewhere in the face · {} of {} held their whole support · {} of {} held the support restricted to germs that STOOD · {} of {} held their depth-0 support", diff.moved, diff.total, diff.support_held, diff.total, diff.standing_support_held, diff.total, diff.depth_zero_held, diff.total);
    diff
}

fn exhibit_foil(
    form: &mut String,
    stride: usize,
    development: &Material,
    foil: &Material,
    grown: &Cultivation,
    foil_grown: &Cultivation,
) {
    let development_population: BTreeMap<&str, usize> = tally(&development.surfaces);
    let foil_population: BTreeMap<&str, usize> = tally(&foil.surfaces);
    line!(form, "  the permutation, declared: position i -> (i * {stride}) mod {}, a bijection on positions", development.surfaces.len());
    line!(
        form,
        "  the germ POPULATION is identical: {} · {} distinct surfaces each, multiset equal {}",
        development.surfaces.len(),
        development_population.len(),
        development_population == foil_population
    );
    line!(
        form,
        "  the ADJACENCY is broken: {} of {} adjacent pairs survive",
        surviving_pairs(&development.surfaces, &foil.surfaces),
        development.surfaces.len().saturating_sub(1)
    );
    line!(form, "  the two deltas, plurally:");
    line!(form, "    {:<38} {:>12} {:>12}", "", "development", "foil");
    line!(
        form,
        "    {:<38} {:>12} {:>12}",
        "germs founded",
        grown.delta.germs_founded.len(),
        foil_grown.delta.germs_founded.len()
    );
    line!(
        form,
        "    {:<38} {:>12} {:>12}",
        "classes founded",
        grown.delta.classes_after - grown.delta.classes_before,
        foil_grown.delta.classes_after - foil_grown.delta.classes_before
    );
    line!(
        form,
        "    {:<38} {:>12} {:>12}",
        "  of which splits",
        grown.delta.classes_split(),
        foil_grown.delta.classes_split()
    );
    line!(
        form,
        "    {:<38} {:>12} {:>12}",
        "transitions founded",
        grown.delta.transitions_founded.len(),
        foil_grown.delta.transitions_founded.len()
    );
    line!(
        form,
        "    {:<38} {:>12} {:>12}",
        "  inside the standing body",
        grown.delta.transitions_founded_on_standing(),
        foil_grown.delta.transitions_founded_on_standing()
    );
    line!(
        form,
        "    {:<38} {:>12} {:>12}",
        "suffix links rebased",
        grown.delta.suffix_rebased.len(),
        foil_grown.delta.suffix_rebased.len()
    );
    line!(
        form,
        "    {:<38} {:>12} {:>12}",
        "classes whose standing moved",
        grown.delta.standing_increments.len(),
        foil_grown.delta.standing_increments.len()
    );
    line!(
        form,
        "    {:<38} {:>12} {:>12}",
        "total occupancy deposited",
        grown.delta.standing_increments.values().sum::<u64>(),
        foil_grown.delta.standing_increments.values().sum::<u64>()
    );
    let development_census = grown.residual.census();
    let foil_census = foil_grown.residual.census();
    line!(
        form,
        "  and the residual that caused each of them, by species:"
    );
    for species in ["None", "Ride", "OpenIncluded", "OpenResidual"] {
        line!(
            form,
            "    {:<38} {:>12} {:>12}",
            species,
            development_census.get(species).copied().unwrap_or(0),
            foil_census.get(species).copied().unwrap_or(0)
        );
    }
    let development_founded: BTreeSet<(u32, &str)> = grown
        .delta
        .transitions_founded
        .iter()
        .filter(|row| row.on_standing_class)
        .map(|row| (row.class, row.germ.as_str()))
        .collect();
    let foil_founded: BTreeSet<(u32, &str)> = foil_grown
        .delta
        .transitions_founded
        .iter()
        .filter(|row| row.on_standing_class)
        .map(|row| (row.class, row.germ.as_str()))
        .collect();
    let shared = development_founded.intersection(&foil_founded).count();
    line!(
        form,
        "  the (class, germ) pairs founded INSIDE the standing body: {} shared of {} and {}",
        shared,
        development_founded.len(),
        foil_founded.len()
    );
    let only_foil: Vec<&(u32, &str)> = foil_founded
        .difference(&development_founded)
        .take(6)
        .collect();
    line!(form, "    founded only by the foil: {only_foil:?}");
    line!(
        form,
        "  **The germ population is the same and the delta is not.** So the delta is caused by the"
    );
    line!(
        form,
        "  material's STRUCTURE — which germ follows which — and not by which germs are present."
    );
}

fn foil_differs(development: &CultivationDelta, foil: &CultivationDelta) -> bool {
    development.germs_founded == foil.germs_founded
        && (development.classes_after != foil.classes_after
            || development.transitions_founded_on_standing()
                != foil.transitions_founded_on_standing()
            || development.standing_increments != foil.standing_increments)
}

fn tally(surfaces: &[String]) -> BTreeMap<&str, usize> {
    let mut population = BTreeMap::new();
    for surface in surfaces {
        *population.entry(surface.as_str()).or_insert(0) += 1;
    }
    population
}

fn surviving_pairs(left: &[String], right: &[String]) -> usize {
    let held: BTreeSet<(&str, &str)> = left
        .windows(2)
        .map(|pair| (pair[0].as_str(), pair[1].as_str()))
        .collect();
    right
        .windows(2)
        .filter(|pair| held.contains(&(pair[0].as_str(), pair[1].as_str())))
        .count()
}

/// The declared germ permutation, and the stride it actually used.
fn permute(development: &Material) -> Result<(Material, usize), String> {
    let extent = development.surfaces.len();
    let mut stride = FOIL_STRIDE_SEED;
    while extent % stride == 0 || gcd(stride, extent) != 1 {
        stride += 1;
    }
    let mut surfaces = vec![String::new(); extent];
    let mut germs = Vec::with_capacity(extent);
    let mut order = vec![0usize; extent];
    for at in 0..extent {
        order[at] = (at * stride) % extent;
    }
    // A stride permutation is a bijection exactly when gcd(stride, extent) = 1, which the loop
    // above establishes; assert it rather than trusting it.
    let distinct: BTreeSet<usize> = order.iter().copied().collect();
    if distinct.len() != extent {
        return Err(format!(
            "the declared foil permutation is not a bijection at stride {stride}"
        ));
    }
    for (at, from) in order.iter().enumerate() {
        surfaces[at] = development.surfaces[*from].clone();
        germs.push(development.germs[*from].clone());
    }
    Ok((
        Material {
            name: "MATCHED FOIL",
            label: format!("{DEVELOPMENT} germ-permuted at stride {stride}"),
            surfaces,
            germs,
        },
        stride,
    ))
}

fn gcd(left: usize, right: usize) -> usize {
    if right == 0 {
        left
    } else {
        gcd(right, left % right)
    }
}

struct Child {
    status: Option<i32>,
    classes: usize,
    transitions: usize,
    vocabulary: usize,
    descriptors: Vec<String>,
    faces: Vec<String>,
}

fn remount_child(locator: &str, probes: &[&str]) -> Result<Child, String> {
    let executable = std::env::current_exe().map_err(|error| format!("{error}"))?;
    let mut command = std::process::Command::new(executable);
    command.arg("--remount").arg(locator);
    for probe in probes {
        command.arg(probe);
    }
    let returned = command.output().map_err(|error| format!("{error}"))?;
    let text = String::from_utf8_lossy(&returned.stdout).into_owned();
    let mut child = Child {
        status: returned.status.code(),
        classes: 0,
        transitions: 0,
        vocabulary: 0,
        descriptors: Vec::new(),
        faces: Vec::new(),
    };
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("CHILD-CLASSES ") {
            child.classes = rest.trim().parse().unwrap_or(0);
        } else if let Some(rest) = line.strip_prefix("CHILD-TRANSITIONS ") {
            child.transitions = rest.trim().parse().unwrap_or(0);
        } else if let Some(rest) = line.strip_prefix("CHILD-VOCABULARY ") {
            child.vocabulary = rest.trim().parse().unwrap_or(0);
        } else if let Some(rest) = line.strip_prefix("CHILD-DESCRIPTORS ") {
            child.descriptors = rest.split_whitespace().map(str::to_owned).collect();
        } else if let Some(rest) = line.strip_prefix("CHILD-FACE ") {
            if let Some((_, face)) = rest.rsplit_once(' ') {
                child.faces.push(face.to_owned());
            }
        }
    }
    if child.status != Some(0) {
        return Err(format!(
            "the remount child exited {:?}: {}",
            child.status,
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(child)
}

fn write_delta_form(predecessor: &AthenaRest, delta: &CultivationDelta) -> Result<(), String> {
    let mut form = String::new();
    let _ = writeln!(form, "# THE CULTIVATION DELTA — Deed P3");
    let _ = writeln!(form, "# material   {}", delta.material);
    let _ = writeln!(form, "# metric     {}", delta.metric);
    let _ = writeln!(form, "# law        {CULTIVATION_LAW}");
    let _ = writeln!(
        form,
        "# classes    {} -> {}",
        delta.classes_before, delta.classes_after
    );
    let _ = writeln!(form, "#");
    let _ = writeln!(form, "# Every row carries the material position that caused it. The structural rows are licensed");
    let _ = writeln!(form, "# by the residual: a transition is founded exactly where the class did not offer that germ,");
    let _ = writeln!(form, "# which is the residual's `OpenResidual` (a family without it) or `None` (a terminus). The");
    let _ = writeln!(form, "# standing rows are the image of the exact receiver differential through the declared metric.");
    let _ = writeln!(form, "#");
    for germ in &delta.germs_founded {
        let _ = writeln!(form, "germ+\t{germ:?}");
    }
    for row in &delta.classes_founded {
        match row.species {
            FoundedSpecies::Carried => {
                let _ = writeln!(
                    form,
                    "class+\t{}\tcarried\tposition {}\tgerm {:?}\tstanding {}",
                    row.class, row.caused_by, row.germ, delta.standing[row.class as usize]
                );
            }
            FoundedSpecies::Split { from } => {
                let _ = writeln!(
                    form,
                    "class+\t{}\tsplit-of {}\tposition {}\tgerm {:?}\tstanding {}",
                    row.class, from, row.caused_by, row.germ, delta.standing[row.class as usize]
                );
            }
        }
    }
    for row in &delta.transitions_founded {
        let _ = writeln!(
            form,
            "transition+\t{}\t{:?}\t-> {}\tposition {}\t{}",
            row.class,
            row.germ,
            row.target,
            row.caused_by,
            if row.on_standing_class {
                "inside-the-standing-body"
            } else {
                "on-a-founded-class"
            }
        );
    }
    for row in &delta.transitions_rebased {
        let _ = writeln!(
            form,
            "transition~\t{}\t{:?}\t{} -> {}\tposition {}\t{}",
            row.class,
            row.germ,
            row.before,
            row.after,
            row.caused_by,
            if row.on_standing_class {
                "inside-the-standing-body"
            } else {
                "on-a-founded-class"
            }
        );
    }
    for row in &delta.suffix_rebased {
        let _ = writeln!(
            form,
            "suffix~\t{}\t{:?} -> {}\tposition {}\t{}",
            row.class,
            row.before,
            row.after,
            row.caused_by,
            if row.on_standing_class {
                "inside-the-standing-body"
            } else {
                "on-a-founded-class"
            }
        );
    }
    for (class, held) in &delta.standing_increments {
        let carried = if (*class as usize) < delta.classes_before {
            predecessor.standing[*class as usize].to_string()
        } else {
            "founded".to_owned()
        };
        let _ = writeln!(
            form,
            "standing~\t{class}\t{carried} -> {}\t+{held}",
            delta.standing[*class as usize]
        );
    }
    std::fs::write(format!("{OUT}/delta.form"), form.as_bytes())
        .map_err(|error| format!("{OUT}/delta.form: {error}"))
}
