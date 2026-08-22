//! **Deed P4: the application mounts a sealed native rest ALONE, conducts it, deposits into it, and
//! leaves it octet-identical — the corpus and the source absent from every path it takes.**
//!
//! Plan: `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md` §8 Deed
//! P4. Owners: `soma/life/src/phoenix_rest.rs` (the composition), `soma/life/src/bin/eros.rs`
//! (the station), `soma/life/src/atlas_cultivation.rs` (the law, P3's, unchanged),
//! `soma/life/src/suffix_ecology.rs` (the transport, plus the container's new return edge).
//!
//! # What this driver is, and what it is not
//!
//! **It is not the runtime.** The runtime is the built `eros` binary, and every control below runs
//! that binary in its own process and reads what it printed. The blueprint's *no example
//! subprocess* refuses a driver that shells out to do the deed; here the application IS the deed
//! and the controls are what a driver is for. The application's own code path shells out to
//! nothing, and control eight measures that on its source.
//!
//! **It is also the seal.** P4's first requirement is a seal, and a seal is a corpus-time act: this
//! driver conditions the eight declared canon documents once, emits the rest with its class
//! extents, and checks that stripping the extents reproduces the committed P0 artifact octet for
//! octet. After that point nothing in this deed reads a document, and the application never can.
//!
//! # The one thing P0's rest could not do, found by trying to do it
//!
//! The P0 container carries the transport, the standings, the suffix links and the vocabulary, and
//! all three of its declared laws read only those — so it **conducts** from itself perfectly, and
//! `eros phoenix infer` mounts the committed P0 artifact directly. It cannot be **deposited into**
//! from itself: a deposit finds the class the concatenation ends in as the unique class of greatest
//! extent, decides a split by comparing extents, and orders the occurrence fold by extent, and P0
//! emitted no extents. They are not derivable from what it did emit — 23 of its 59,698 classes are
//! not reachable from the root over the germ transport at all, being the classes whose longest
//! string crosses a path boundary. So the P4 seal carries one further region, `athena.class.extent`,
//! and a rest without it is refused **by name** rather than guessed at.
//!
//! ```text
//! cargo build --release -p life --bin eros
//! cargo run --release -q -p life --example the_application_infers_and_cultivates_from_the_rest_alone
//! ```

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::process::Command;

use life::atlas_cultivation::{conduct, AthenaRest, EXTENT_REGION};
use life::causal_language::{lexical_tokens, token_germs_public};
use life::phoenix_rest::{content_bar, loss_digest, mount_atlas, seal, FORBIDDEN_DESCRIPTORS};
use life::suffix_ecology::ExactSuffixEcology;

const P0_REST: &str = "output/the_native_baseline_conducts/rest.safetensors";
const OUT: &str = "output/the_application_infers";
const EROS: &str = "target/release/eros";

/// The eight documents the P0 rest declares, in the order its own metadata names them. They are
/// read **once**, here, to seal. Nothing below this point opens one.
const MATERIAL: &[&str] = &[
    "canon/THE_DOCUMENT_LAW.md",
    "canon/TABLET_THE_OPERATIONS.md",
    "canon/THE_RECOVERED_LAW.md",
    "canon/TABLET_THE_COMPRESSION.md",
    "canon/TABLET_THE_TURN.md",
    "canon/TABLET_THE_MANIFOLD.md",
    "canon/TABLET_THE_HEXIS.md",
    "canon/TABLET_THE_REASONING_CYCLE.md",
];

/// **The material the cultivation is handed, authored HERE and therefore unseen by construction.**
/// It is not any document, not a fixture on disk, and not a permutation of one; it is written into
/// this source and handed to the application through a file the run itself creates. Its subject is
/// deliberately outside the eight — `wobbleflux` is the surface P0's own receipt used as its
/// unseen-germ control, so the rest is known not to carry it.
const UNSEEN_MATERIAL: &str = "\
the wobbleflux ratchet turns one way and the wobbleflux is the residue a passage leaves behind it.
a ratchet that turns both ways deposits nothing, and a passage that deposits nothing taught the body
nothing whatever it returned. so the wobbleflux ratchet is a deposit and never a choice, and the
later current that rides the changed pathway is the whole of the conditioning.
the wobbleflux ratchet is therefore a passage and not a faculty.
";

/// The prompt the cultivation must move: its subject is the material's and nothing else's.
const MOVED_PROBE: &str = "the wobbleflux ratchet";
/// The prompt the cultivation must leave where it was: it is the P0 receipt's own first probe.
const STILL_PROBE: &str = "the receiver";
/// A prompt in no fixture anywhere, handed to the frozen runtime at run time.
const UNSEEN_PROBE: &str = "a coordinate system is a receiver and the turn is not deleted";

/// What the committed P0 receipt records the CARD returning for `the receiver`, quoted so this deed
/// states its reliance rather than re-measuring it. The agreement between the CPU conduct and the
/// card's is **Deed P3's measurement over all eight recorded prompts**, and nothing here regenerates
/// it; this row is the reliance made visible.
const P0_RECORDED_RECEIVER: (u32, u64, usize, usize) = (7812, 17, 12, 48);

/// The application's own code path, read as source and searched for a subprocess.
const APPLICATION_SOURCE: &[&str] = &[
    "soma/life/src/bin/eros.rs",
    "soma/life/src/phoenix_rest.rs",
    "soma/life/src/atlas_cultivation.rs",
];

fn main() {
    if let Err(reason) = run() {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

struct Run {
    status: Option<i32>,
    stdout: String,
    stderr: String,
}

fn eros(arguments: &[&str]) -> Result<Run, String> {
    let returned = Command::new(EROS)
        .args(arguments)
        .output()
        .map_err(|error| format!("{EROS} {arguments:?}: {error} (build the binary first)"))?;
    Ok(Run {
        status: returned.status.code(),
        stdout: String::from_utf8_lossy(&returned.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&returned.stderr).into_owned(),
    })
}

/// The conducted sections a run printed, with the process-local audit removed: a descriptor listing
/// carries this process's own pid, so comparing two runs' *surfaces* means comparing what they
/// conducted rather than which process conducted it.
fn surfaces(stdout: &str) -> String {
    let start = stdout.find("  PROMPT ").unwrap_or(0);
    let end = stdout
        .find("  THE FROZEN REST")
        .unwrap_or(stdout.len())
        .max(start);
    stdout[start..end].to_owned()
}

fn verdict(held: bool) -> &'static str {
    if held {
        "HELD"
    } else {
        "BROKEN"
    }
}

fn run() -> Result<(), String> {
    let mut form = String::new();
    macro_rules! say {
        ($($argument:tt)*) => {{
            let line = format!($($argument)*);
            println!("{line}");
            let _ = writeln!(form, "{line}");
        }};
    }

    say!("THE APPLICATION INFERS AND CULTIVATES FROM THE REST ALONE — Deed P4\n");

    std::fs::create_dir_all(OUT).map_err(|error| format!("{OUT}: {error}"))?;
    if !std::path::Path::new(EROS).exists() {
        return Err(format!(
            "{EROS} is not built. This deed's runtime IS that binary: \
             cargo build --release -p life --bin eros"
        ));
    }

    // -----------------------------------------------------------------------------------------
    // THE SEAL — the one corpus-time act, and the last time a document is opened
    // -----------------------------------------------------------------------------------------
    let p0_octets = std::fs::read(P0_REST).map_err(|error| format!("{P0_REST}: {error}"))?;
    let p0 = AthenaRest::read_container(&p0_octets).map_err(|error| error.to_string())?;
    let mut paths = Vec::new();
    for document in MATERIAL {
        let text =
            std::fs::read_to_string(document).map_err(|error| format!("{document}: {error}"))?;
        paths.push(
            token_germs_public(&lexical_tokens(&text))
                .map_err(|error| format!("{document}: {error:?}"))?,
        );
    }
    let atlas = ExactSuffixEcology::condition(&paths)
        .map_err(|error| format!("conditioning refused: {error:?}"))?;
    let sealed = seal(&atlas, p0.metadata.clone()).map_err(|error| error.to_string())?;
    let sealed_octets = sealed
        .write_container()
        .map_err(|error| error.to_string())?;
    let rest_path = format!("{OUT}/rest.safetensors");
    std::fs::write(&rest_path, &sealed_octets).map_err(|error| format!("{rest_path}: {error}"))?;

    let mut stripped = sealed.clone();
    stripped.extent = Vec::new();
    let stripped_octets = stripped
        .write_container()
        .map_err(|error| error.to_string())?;
    let seal_is_p0_plus_extents = stripped_octets == p0_octets;

    say!("THE SEAL — the eight declared documents conditioned once, and the last document opened");
    for document in MATERIAL {
        say!("    {document}");
    }
    say!(
        "  the sealed rest      {rest_path}\n    {} octets · {} classes · {} transitions · {} vocabulary · tree height {} · {} class extents",
        sealed_octets.len(),
        sealed.classes(),
        sealed.transitions(),
        sealed.vocabulary.len(),
        sealed.height,
        sealed.extent.len()
    );
    say!("    sha256               {}", loss_digest(&sealed_octets));
    say!(
        "  the same container with {EXTENT_REGION} STRIPPED, against the committed P0 artifact: {} ({} against {} octets)",
        if seal_is_p0_plus_extents { "OCTET-IDENTICAL" } else { "DIFFERENT" },
        stripped_octets.len(),
        p0_octets.len()
    );
    if !seal_is_p0_plus_extents {
        return Err(
            "the P4 seal is not the committed P0 rest plus its extents; nothing below would be \
             about that rest"
                .to_owned(),
        );
    }
    say!(
        "  and its declarations are P0's, unchanged: {} — the seal adds a REGION, not a law.",
        declarations_are_p0s(&p0.metadata, &sealed.metadata)
    );
    say!("  so the seal IS the P0 rest, plus exactly the one native region a deposit reads.");

    // The measurement that says the extents had to be carried rather than derived.
    let mut reachable = vec![false; sealed.classes()];
    reachable[0] = true;
    let mut stack = vec![0usize];
    while let Some(class) = stack.pop() {
        for slot in sealed.indptr[class] as usize..sealed.indptr[class + 1] as usize {
            let target = sealed.target[slot] as usize;
            if !reachable[target] {
                reachable[target] = true;
                stack.push(target);
            }
        }
    }
    let unreachable = reachable.iter().filter(|held| !**held).count();
    say!(
        "  and the extents are CARRIED rather than derived because they cannot be derived: {} of {} \
         classes are unreachable from the root over the germ transport alone — the classes whose \
         longest string crosses a path boundary, which the emission drops.",
        unreachable,
        sealed.classes()
    );
    say!("");

    // -----------------------------------------------------------------------------------------
    // 1 & 4 — seal -> separate-process mount -> seal byte identity, twice
    // -----------------------------------------------------------------------------------------
    let digest_before = loss_digest(&std::fs::read(&rest_path).map_err(|e| e.to_string())?);
    let first = eros(&[
        "phoenix",
        "infer",
        "--rest",
        &rest_path,
        "--text",
        STILL_PROBE,
        "--text",
        UNSEEN_PROBE,
    ])?;
    let digest_between = loss_digest(&std::fs::read(&rest_path).map_err(|e| e.to_string())?);
    let second = eros(&[
        "phoenix",
        "infer",
        "--rest",
        &rest_path,
        "--text",
        STILL_PROBE,
        "--text",
        UNSEEN_PROBE,
    ])?;
    let digest_after = loss_digest(&std::fs::read(&rest_path).map_err(|e| e.to_string())?);
    let frozen = digest_before == digest_between && digest_between == digest_after;
    let bit_equal =
        surfaces(&first.stdout) == surfaces(&second.stdout) && !surfaces(&first.stdout).is_empty();
    let both_returned = first.status == Some(0) && second.status == Some(0);

    say!(
        "[ 1] SEAL -> SEPARATE-PROCESS MOUNT -> SEAL BYTE IDENTITY   {}",
        verdict(frozen && bit_equal && both_returned)
    );
    say!(
        "  two processes, each handed one path and two prompts, each exiting {:?}/{:?}",
        first.status,
        second.status
    );
    say!("  the rest's sha256 before / between / after");
    say!("    {digest_before}");
    say!("    {digest_between}");
    say!("    {digest_after}");
    say!(
        "  the two runs' conducted surfaces: {} ({} octets each)",
        if bit_equal { "BIT-EQUAL" } else { "DIFFERENT" },
        surfaces(&first.stdout).len()
    );
    say!(
        "[ 4] FROZEN INFERENCE LEAVES THE REST BYTE-IDENTICAL         {}",
        verdict(frozen)
    );
    say!("  the same three digests; the application re-reads the file from the disk after conducting");
    say!("  and refuses its own run if it moved, so this is the runtime's own check as well as ours.");
    say!("");

    // A few verbatim faces, so the deed returns the ARTIFACT and not only its verdicts.
    say!("  THE RETURNED SURFACE, VERBATIM — the first process's own printing");
    for line in surfaces(&first.stdout).lines().take(14) {
        say!("  | {line}");
    }
    say!("");

    // -----------------------------------------------------------------------------------------
    // 2 & 7 — the source audit, printed by the application itself
    // -----------------------------------------------------------------------------------------
    let audited: Vec<&str> = first
        .stdout
        .lines()
        .skip_while(|line| !line.contains("THE SOURCE AUDIT"))
        .take_while(|line| !line.trim().is_empty())
        .collect();
    let forbidden_line = audited
        .iter()
        .find(|line| line.contains("forbidden targets open"))
        .copied()
        .unwrap_or("(the application printed no forbidden-target line)");
    let clean = forbidden_line.ends_with("none");
    // The descriptor TARGETS, not the printed page: the application prints the forbidden list
    // itself, so a search over the whole stdout would convict the audit of naming what it refuses.
    let targets: Vec<&str> = first
        .stdout
        .lines()
        .chain(second.stdout.lines())
        .skip_while(|line| !line.contains("THE SOURCE AUDIT"))
        .take_while(|line| !line.trim().is_empty())
        .filter(|line| line.starts_with("    ") && !line.contains("forbidden targets open"))
        .collect();
    let no_card = !targets.iter().any(|target| target.contains("/dev/nvidia"));
    say!(
        "[ 2] SOURCE MODEL AND DEVELOPMENT MATERIAL UNREACHABLE       {}",
        verdict(clean)
    );
    for line in &audited {
        say!("  |{line}");
    }
    say!(
        "  the audit is the process asking /proc/self/fd about ITSELF, printed by the application."
    );
    say!("  A rest is opened, read whole and closed, so what remains is this process's own stdio.");
    say!(
        "[ 7] THE CARD IS NEVER OPENED                                {}",
        verdict(no_card && clean)
    );
    say!(
        "  The blueprint's control is GPU hidden -> typed refusal. This application's inference is"
    );
    say!("  CPU-exact, so that control has no honest form here and this is the one it does have: the");
    say!(
        "  device is never opened at all. {:?} appear in no descriptor of either run, and `--card`",
        FORBIDDEN_DESCRIPTORS
    );
    let card_run = eros(&[
        "phoenix",
        "infer",
        "--rest",
        &rest_path,
        "--text",
        STILL_PROBE,
        "--card",
    ])?;
    let card_refused = card_run.status != Some(0) && card_run.stderr.contains("UNWIRED");
    say!(
        "  is NAMED UNWIRED rather than stubbed: {} exit {:?}",
        card_run.stderr.trim(),
        card_run.status
    );
    say!(
        "  the flag refuses instead of printing a plausible card face: {}",
        verdict(card_refused)
    );
    say!("");

    // -----------------------------------------------------------------------------------------
    // 3 — deleting the rest makes inference refuse
    // -----------------------------------------------------------------------------------------
    let missing = format!("{OUT}/there-is-no-rest-here.safetensors");
    let _ = std::fs::remove_file(&missing);
    let refused = eros(&[
        "phoenix",
        "infer",
        "--rest",
        &missing,
        "--text",
        STILL_PROBE,
    ])?;
    let names_it = refused.stderr.contains(&missing);
    let no_output = !refused.stdout.contains("PROMPT");
    let non_zero = refused.status.map(|code| code != 0).unwrap_or(true);
    say!(
        "[ 3] DELETING THE REST MAKES INFERENCE REFUSE                {}",
        verdict(names_it && no_output && non_zero)
    );
    say!(
        "  exit {:?}   the refusal names the rest: {names_it}   no plausible output: {no_output}",
        refused.status
    );
    say!("  | {}", refused.stderr.trim());
    say!("");

    // -----------------------------------------------------------------------------------------
    // 5 & 6 — cultivation founds a distinct successor, from material created at run time
    // -----------------------------------------------------------------------------------------
    let material_path = format!("{OUT}/material-written-at-run-time.txt");
    std::fs::write(&material_path, UNSEEN_MATERIAL)
        .map_err(|error| format!("{material_path}: {error}"))?;
    let unseen_germ_absent = !sealed
        .vocabulary
        .iter()
        .any(|surface| surface == "wobbleflux");
    let successor_path = format!("{OUT}/successor-rest.safetensors");
    let _ = std::fs::remove_file(&successor_path);
    let grown = eros(&[
        "phoenix",
        "cultivate",
        "--rest",
        &rest_path,
        "--material",
        &material_path,
        "--out",
        &successor_path,
    ])?;
    if grown.status != Some(0) {
        say!("{}", grown.stdout);
        return Err(format!("the cultivation refused: {}", grown.stderr.trim()));
    }
    let successor_octets =
        std::fs::read(&successor_path).map_err(|error| format!("{successor_path}: {error}"))?;
    let predecessor_after = loss_digest(&std::fs::read(&rest_path).map_err(|e| e.to_string())?);
    let successor_digest = loss_digest(&successor_octets);
    let distinct = successor_digest != digest_after && successor_path != rest_path;
    let predecessor_untouched = predecessor_after == digest_after;

    // the changed conduct, and the unchanged conduct, each taken in ITS OWN fresh process
    let moved_on_successor = eros(&[
        "phoenix",
        "infer",
        "--rest",
        &successor_path,
        "--text",
        MOVED_PROBE,
    ])?;
    let moved_on_predecessor = eros(&[
        "phoenix",
        "infer",
        "--rest",
        &rest_path,
        "--text",
        MOVED_PROBE,
    ])?;
    let still_on_successor = eros(&[
        "phoenix",
        "infer",
        "--rest",
        &successor_path,
        "--text",
        STILL_PROBE,
    ])?;
    let still_on_predecessor = eros(&[
        "phoenix",
        "infer",
        "--rest",
        &rest_path,
        "--text",
        STILL_PROBE,
    ])?;
    let printed_moved =
        surfaces(&moved_on_successor.stdout) != surfaces(&moved_on_predecessor.stdout);

    // **The face carries the standings and the support does not, and that distinction is P0's own
    // measurement rather than a convenience here**: a deposit re-folds the occurrence counts over
    // the whole suffix tree, so every probe's FACE moves after any cultivation whatever its
    // subject. The support — which germs at which depth — is the face that survives a corpus-wide
    // occupancy move, so it is the one a subject-disjoint control can be taken on.
    let successor_rest_read =
        AthenaRest::read_container(&std::fs::read(&successor_path).map_err(|e| e.to_string())?)
            .map_err(|error| error.to_string())?;
    let predecessor_rest_read =
        AthenaRest::read_container(&std::fs::read(&rest_path).map_err(|e| e.to_string())?)
            .map_err(|error| error.to_string())?;
    let three_faces = |probe: &str| -> (bool, bool, bool) {
        let before = conduct(&predecessor_rest_read, probe, &lexical_tokens(probe));
        let after = conduct(&successor_rest_read, probe, &lexical_tokens(probe));
        (
            before.depth_zero_support() != after.depth_zero_support(),
            before.support() != after.support(),
            before.face() != after.face(),
        )
    };
    let moved_faces = three_faces(MOVED_PROBE);
    let still_faces = three_faces(STILL_PROBE);
    let conduct_moved = printed_moved && moved_faces.0;
    let conduct_still = !still_faces.0
        && still_on_successor.status == Some(0)
        && still_on_predecessor.status == Some(0);

    say!(
        "[ 5] CULTIVATION FOUNDS A DISTINCT SUCCESSOR                 {}",
        verdict(distinct && predecessor_untouched && conduct_moved)
    );
    say!("  the predecessor  {rest_path}");
    say!("    sha256 before {digest_after}");
    say!("    sha256 after  {predecessor_after}   untouched: {predecessor_untouched}");
    say!("  the successor    {successor_path}");
    say!(
        "    sha256        {successor_digest}   {} octets   distinct: {distinct}",
        successor_octets.len()
    );
    say!("  THE DELTA, AS THE APPLICATION PRINTED IT");
    for line in grown
        .stdout
        .lines()
        .skip_while(|line| !line.contains("THE DELTA"))
        .take_while(|line| !line.trim().is_empty())
    {
        say!("  |{line}");
    }
    say!("  THE STRUCTURED RESIDUAL, AS THE APPLICATION PRINTED IT");
    for line in grown
        .stdout
        .lines()
        .skip_while(|line| !line.contains("THE STRUCTURED RESIDUAL"))
        .take_while(|line| !line.trim().is_empty())
    {
        say!("  |{line}");
    }
    say!("  THE SUCCESSOR'S DECLARED LINEAGE, AS THE APPLICATION PRINTED IT");
    let printed: Vec<&str> = grown.stdout.lines().collect();
    for (at, line) in printed.iter().enumerate() {
        if line.trim_start().starts_with("cultivation.") {
            say!("  |{line}");
            if let Some(value) = printed.get(at + 1) {
                say!("  |{value}");
            }
        }
    }
    say!("  THE CONDUCT, ON THREE FACES OF THE SAME SECTION, SUCCESSOR AGAINST PREDECESSOR");
    let moved_word = |moved: bool| if moved { "MOVED    " } else { "unchanged" };
    say!(
        "    {:<28} {:>10} {:>10} {:>10}",
        "probe",
        "depth-0",
        "support",
        "face"
    );
    say!(
        "    {:<28} {:>10} {:>10} {:>10}",
        format!("{MOVED_PROBE:?}"),
        moved_word(moved_faces.0),
        moved_word(moved_faces.1),
        moved_word(moved_faces.2)
    );
    say!(
        "    {:<28} {:>10} {:>10} {:>10}",
        format!("{STILL_PROBE:?}"),
        moved_word(still_faces.0),
        moved_word(still_faces.1),
        moved_word(still_faces.2)
    );
    say!("    and that table is the finding rather than a caveat. The FACE carries every offered");
    say!("    germ's standing, and a deposit re-folds the occurrence counts over the whole suffix");
    say!("    tree, so every probe's face moves after any cultivation whatever its subject. The");
    say!(
        "    SUPPORT drops the standings and keeps germ-and-depth, and it still moves for a probe"
    );
    say!(
        "    whose ladder reaches the root, because the vocabulary itself grew by three germs and"
    );
    say!("    the root offers them — that is the vocabulary growing, not the subject moving. The");
    say!(
        "    DEPTH-0 SUPPORT is what the full context alone licenses, and it is the face on which"
    );
    say!("    a subject-disjoint control can honestly be taken: it moves for the material's own");
    say!("    subject and does not move for a subject the material never touched.");
    let landed = |stdout: &str| -> String {
        stdout
            .lines()
            .find(|line| line.trim_start().starts_with("landed class"))
            .unwrap_or("")
            .trim()
            .to_owned()
    };
    say!(
        "    on the predecessor   {}",
        landed(&moved_on_predecessor.stdout)
    );
    say!(
        "    on the successor     {}",
        landed(&moved_on_successor.stdout)
    );
    // The seal is closed under its own law only if the successor can be cultivated in turn, so
    // the same material is exposed to it a second time: a re-exposure of standing material must
    // found nothing structurally and move only the occupancy.
    let second_path = format!("{OUT}/successor-rest-second-generation.safetensors");
    let _ = std::fs::remove_file(&second_path);
    let second = eros(&[
        "phoenix",
        "cultivate",
        "--rest",
        &successor_path,
        "--material",
        &material_path,
        "--out",
        &second_path,
    ])?;
    let second_delta: BTreeMap<&str, i64> = second
        .stdout
        .lines()
        .filter_map(|line| {
            let line = line.trim();
            for key in ["germs founded", "classes founded", "transitions founded"] {
                if let Some(tail) = line.strip_prefix(key) {
                    let value = tail.split_whitespace().next()?.parse::<i64>().ok()?;
                    return Some((key, value));
                }
            }
            None
        })
        .collect();
    let inside_line = second
        .stdout
        .lines()
        .find(|line| line.contains("already offered a nonempty family"))
        .unwrap_or("")
        .trim()
        .to_owned();
    let inside_zero = inside_line.contains("and 0 at a class");
    let second_rest = AthenaRest::read_container(
        &std::fs::read(&second_path).map_err(|e| format!("{second_path}: {e}"))?,
    )
    .map_err(|error| error.to_string())?;
    let lineage_chains = second_rest
        .metadata
        .get("cultivation.predecessor")
        .map(|named| named.contains(&successor_path))
        .unwrap_or(false)
        && second_rest.extent.len() == second_rest.classes();
    let chains = second.status == Some(0)
        && lineage_chains
        && second_delta.get("germs founded") == Some(&0)
        && inside_zero;
    say!("  THE SEAL IS CLOSED UNDER ITS OWN LAW — the successor is cultivated in turn");
    say!(
        "    the same material exposed to the SUCCESSOR: exit {:?}, {:?}",
        second.status,
        second_delta
    );
    say!("    | {inside_line}");
    say!(
        "    the second generation names the first as its predecessor and carries its own extents: {lineage_chains}"
    );
    say!("    -> {second_path}");
    say!("    AND THE NO-OP READING, STATED AS WHAT IT IS. The material is already in this rest");
    say!("    verbatim, so 0 germs are founded: the vocabulary is entirely standing. What it DOES");
    say!("    found is the seam — exposing a path a second time appends a second copy, and every");
    say!("    founded transition sits at a class that offered NOTHING, a terminus whose longest");
    say!("    string ends in the previous separator. 0 are founded at a class that could already");
    say!("    say something, so the material's own transport is untouched, which is the law's own");
    say!("    face and not an exception to it. Calling that whole delta empty would be false and");
    say!("    the first form of this control did.");
    say!(
        "[ 6] A FRESH RUNTIME ACCEPTS UNSEEN MATERIAL                 {}",
        verdict(
            unseen_germ_absent && conduct_moved && moved_on_successor.status == Some(0) && chains
        )
    );
    say!("  the material was WRITTEN AT RUN TIME to {material_path} from a paragraph authored in this");
    say!("  driver's source: it is no document, no fixture and no permutation of one. The surface");
    say!("  \"wobbleflux\" is absent from the sealed rest's {} germ vocabulary: {unseen_germ_absent}", sealed.vocabulary.len());
    say!("  and the prompt {UNSEEN_PROBE:?} is in no fixture either; it conducted in control 1.");
    say!("");

    // -----------------------------------------------------------------------------------------
    // 8 — no subprocess in the application's own code path
    // -----------------------------------------------------------------------------------------
    let mut shells: Vec<String> = Vec::new();
    for source in APPLICATION_SOURCE {
        let text = std::fs::read_to_string(source).map_err(|error| format!("{source}: {error}"))?;
        for (at, line) in text.lines().enumerate() {
            if line.contains("Command::new")
                || line.contains("std::process::Command")
                || line.contains("libc::fork")
                || line.contains("execve")
            {
                shells.push(format!("{source}:{}: {}", at + 1, line.trim()));
            }
        }
    }
    say!(
        "[ 8] THE APPLICATION SHELLS OUT TO NOTHING                   {}",
        verdict(shells.is_empty())
    );
    say!(
        "  searched Command::new / std::process::Command / libc::fork / execve over the whole code"
    );
    say!(
        "  path the station takes: {APPLICATION_SOURCE:?} — {} hit(s)",
        shells.len()
    );
    for hit in &shells {
        say!("    {hit}");
    }
    say!("  The subprocesses in this deed are THIS driver's, re-running the application to get a");
    say!("  second process; that is what a separate-process mount is and it is not the application's.");
    say!("");

    // -----------------------------------------------------------------------------------------
    // 9 — the export, the round trip, and the GGUF verdict
    // -----------------------------------------------------------------------------------------
    let manifest_run = eros(&[
        "phoenix",
        "infer",
        "--rest",
        &rest_path,
        "--text",
        STILL_PROBE,
        "--export-manifest",
    ])?;
    // the round trip, exactly: the octets a separate process mounted, mounted again and compared
    // class by class against the atlas the seal was taken from.
    let recovered_rest =
        AthenaRest::read_container(&std::fs::read(&rest_path).map_err(|e| e.to_string())?)
            .map_err(|error| error.to_string())?;
    let recovered = mount_atlas(&recovered_rest, &rest_path).map_err(|error| error.to_string())?;
    let mut moved_classes = 0usize;
    for class in 0..atlas.state_count() as u32 {
        if recovered.class_extent(class) != atlas.class_extent(class)
            || recovered.standing_at(class) != atlas.standing_at(class)
            || recovered.suffix_link(class) != atlas.suffix_link(class)
            || recovered.outgoing(class) != atlas.outgoing(class)
        {
            moved_classes += 1;
        }
    }
    let round_trip = moved_classes == 0 && recovered.state_count() == atlas.state_count();
    say!(
        "[ 9] EXPORT, AND THE ROUND TRIP THAT DECIDES WHETHER IT IS A MODEL   {}",
        verdict(round_trip && manifest_run.status == Some(0))
    );
    say!("  THE REALIZATION MANIFEST, AS THE APPLICATION PRINTED IT");
    for line in manifest_run
        .stdout
        .lines()
        .skip_while(|line| !line.contains("THE REALIZATION MANIFEST"))
        .take_while(|line| !line.trim().is_empty())
    {
        say!("  |{line}");
    }
    say!("  SAFETENSORS: LAWFUL, AND ALREADY DONE — the rest IS a safetensors container, so there is");
    say!("  no export step to perform and nothing to convert. The blueprint's criterion is the round");
    say!("  trip, native atlas -> serialized form -> separate-process remount -> recovered atlas:");
    say!("    the separate-process remount is control 1, twice, and the manifest run above;");
    say!(
        "    the recovered atlas is exact — {} of {} classes differ in extent, standing, suffix",
        moved_classes,
        atlas.state_count()
    );
    say!("    link or transport row after octets -> container -> transport;");
    say!("    and P3's own remount of a sealed successor stands beside it, unrerun.");
    say!("  GGUF: REFUSED, and here is the reason rather than the refusal.");
    say!(
        "    The payload is expressible — GGUF carries integer tensor types, so the CSR rows, the"
    );
    say!(
        "    standings, the suffix links and the extents would all fit as 1-D integer tensors, and"
    );
    say!(
        "    the vocabulary would fit as an array of strings. What has no lawful home is the LAW."
    );
    say!("    A GGUF file is read by dispatching on general.architecture and that architecture's");
    say!("    expected tensor names and hyperparameters; there is no architecture whose graph is");
    say!(
        "    `walk the transport row, fall along the suffix link, return the whole offered family"
    );
    say!("    with its depth`. So the file would be one of two things, and both are refused: it");
    say!(
        "    would name an architecture whose graph does not compute these three laws, which is a"
    );
    say!(
        "    false declaration inside the container; or it would name an architecture no consumer"
    );
    say!(
        "    knows, which every consumer refuses to load. Either way the atlas is not RECOVERABLE"
    );
    say!("    from it, and the blueprint's own criterion is exactly that — a parseable tensor file is");
    say!(
        "    not a model. Writing the tensors under a tokenizer key would be worse still: it would"
    );
    say!(
        "    assert a BPE/SPM decoder this body does not have. The lossy mapping is not invented."
    );
    say!("");

    // -----------------------------------------------------------------------------------------
    // 10 — the content bar
    // -----------------------------------------------------------------------------------------
    let bar = content_bar(&sealed_octets, &sealed);
    let bar_held = bar.iter().all(|row| row.held);
    say!(
        "[10] THE CONTENT BAR, MEASURED ON THE SEALED OCTETS          {}",
        verdict(bar_held)
    );
    say!("  AS THE APPLICATION PRINTED IT, in the same run that printed the manifest");
    let printed_bar: Vec<&str> = manifest_run
        .stdout
        .lines()
        .skip_while(|line| !line.contains("THE CONTENT BAR"))
        .take_while(|line| !line.trim().is_empty())
        .collect();
    for line in &printed_bar {
        say!("  |{line}");
    }
    let application_agrees = printed_bar.len() == 1 + 2 * bar.len()
        && !printed_bar.iter().any(|line| line.contains("[BROKEN]"));
    let successor_bar = content_bar(&successor_octets, &successor_rest_read);
    let successor_bar_held = successor_bar.iter().all(|row| row.held);
    say!(
        "  and the SUCCESSOR, which carries a cultivation lineage the predecessor does not: {}",
        verdict(successor_bar_held)
    );
    for row in &successor_bar {
        if !row.held {
            say!("      BROKEN {}: {}", row.claim, row.evidence);
        }
    }
    say!("  the routing search is the one the deed names — gemma / phoenix / q_proj and their");
    say!("  siblings — over region names and metadata values. Note what it does NOT claim: the");
    say!("  string `layer` occurs in the rest's own architecture declaration, inside the sentence");
    say!("  that says no layer, head, rank or latent width is declared. A negative declaration is");
    say!("  not a routing name, and a grep that could not tell them apart would be the defect.");
    say!("");

    // -----------------------------------------------------------------------------------------
    // the reliance, stated
    // -----------------------------------------------------------------------------------------
    let receiver_section = conduct(&sealed, STILL_PROBE, &lexical_tokens(STILL_PROBE));
    let depth_zero = receiver_section
        .offered
        .iter()
        .filter(|(_, _, depth)| *depth == 0)
        .count();
    let depth_one = receiver_section
        .offered
        .iter()
        .filter(|(_, _, depth)| *depth == 1)
        .count();
    let agrees = (
        receiver_section.class,
        receiver_section.standing,
        depth_zero,
        depth_one,
    ) == P0_RECORDED_RECEIVER;
    say!("THE SURFACE THIS CONDUCTS ON, STATED AS A RELIANCE");
    say!("  The application's inference is CPU-exact and integral throughout. That it is the same");
    say!("  reading the card returned is DEED P3'S MEASUREMENT over the committed P0 receipt's eight");
    say!("  recorded prompts, and nothing here regenerates it. The reliance made visible on one row:");
    say!(
        "    {STILL_PROBE:?}  landed {} standing {} depth-0 {} depth-1 {}   the P0 receipt records {:?}: {}",
        receiver_section.class, receiver_section.standing, depth_zero, depth_one, P0_RECORDED_RECEIVER,
        if agrees { "agrees" } else { "DOES NOT AGREE" }
    );
    say!("  `--card` is unwired, and the station refuses it rather than printing a card face.");
    say!("");

    // -----------------------------------------------------------------------------------------
    let held = [
        (
            "1 seal -> separate-process mount -> byte identity",
            frozen && bit_equal && both_returned,
        ),
        ("2 source and development material unreachable", clean),
        (
            "3 a missing rest refuses, typed, naming it",
            names_it && no_output && non_zero,
        ),
        ("4 frozen inference leaves the rest byte-identical", frozen),
        (
            "5 cultivation founds a distinct successor with changed conduct",
            distinct && predecessor_untouched && conduct_moved && conduct_still,
        ),
        (
            "6 a fresh runtime accepts unseen material, and the successor is cultivable in turn",
            unseen_germ_absent && conduct_moved && chains,
        ),
        (
            "7 the card is never opened, and --card is unwired",
            no_card && clean && card_refused,
        ),
        ("8 the application shells out to nothing", shells.is_empty()),
        ("9 the round trip recovers the atlas exactly", round_trip),
        (
            "10 the content bar, measured and printed by the application itself",
            bar_held && successor_bar_held && application_agrees,
        ),
    ];
    say!("THE TEN CONTROLS");
    for (name, stood) in &held {
        say!("  [{}] {name}", verdict(*stood));
    }
    let all = held.iter().all(|(_, stood)| *stood);
    say!("");
    say!(
        "  {} of {} stood. A deed that returned a plausible surface and could not say what it had",
        held.iter().filter(|(_, stood)| *stood).count(),
        held.len()
    );
    say!("  open would not be this deed.");

    let receipt = format!("{OUT}/receipt.form");
    std::fs::write(&receipt, &form).map_err(|error| format!("{receipt}: {error}"))?;
    println!("\n  -> {receipt}");
    if !all {
        return Err("a control did not stand".to_owned());
    }
    Ok(())
}

/// The declared laws the sealed rest carries forward from P0: the seal adds a region and changes no
/// declaration, and this is that sentence as a comparison rather than as a promise.
fn declarations_are_p0s(p0: &BTreeMap<String, String>, sealed: &BTreeMap<String, String>) -> bool {
    p0 == sealed
}
