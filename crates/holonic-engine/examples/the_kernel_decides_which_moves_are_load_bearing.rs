//! An independent instrument grades the move-species reading: **delete a move, ask the kernel.**
//!
//! `the_move_species_is_a_fiber` returns species over an arrival graph and reports that 45 of 78
//! moves in a real geometry file are *isolated* — founded and never used. That is a claim about
//! causal structure made by one instrument, and one instrument cannot audit itself.
//!
//! The kernel is a second instrument and it answers a question the species reading never consults:
//! **is this move load-bearing?** Remove its line, resubmit, and let Lean say whether the proof
//! still stands.
//!
//! # The declared prediction, stated before the run
//!
//! A move nothing arrives from should be **removable more often** than one a later move arrives
//! from. If the two rates agree, the arrival graph tracks nothing this instrument can see, and that
//! is a real negative about the reading rather than about the kernel.
//!
//! # Why the inconclusive arm exists and is not a hedge
//!
//! A `have` may span several lines. Deleting one line of a multi-line step leaves text that does not
//! parse, and a parse failure says nothing about whether the move carried weight. Those are
//! classified **inconclusive**, counted, and excluded from both rates — a refusal must be about the
//! mathematics to count as evidence of load. Collapsing them into "load-bearing" would manufacture
//! exactly the result the prediction wants.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_kernel_decides_which_moves_are_load_bearing
//! ```

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use holonic_engine::lean_development::{BinderGrain, DeclarationGrain, read_development_at};
use holonic_engine::move_species::{MoveComplex, MoveOccurrence};

const PROJECT: &str = "formal/rh-source-transport";
const CORPUS: &str = "SomaRHSourceTransport/FiniteTransport.lean";

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    /// The proof still stands without this move.
    Removable,
    /// The kernel refused on the mathematics: the move carried weight.
    LoadBearing,
    /// The remaining text does not parse. Says nothing either way.
    Inconclusive,
}

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate sits two levels under the repository root")
        .to_path_buf()
}

fn check(project: &Path, path: &Path) -> (bool, String) {
    let output = Command::new("lake")
        .arg("env")
        .arg("lean")
        .arg(path)
        .current_dir(project)
        .output()
        .expect("lake env lean runs");
    let mut diagnostic = String::from_utf8_lossy(&output.stdout).into_owned();
    diagnostic.push_str(&String::from_utf8_lossy(&output.stderr));
    (
        output.status.success() && diagnostic.trim().is_empty(),
        diagnostic,
    )
}

/// A refusal is inconclusive when the remaining text did not parse. Lean says so in its own words,
/// and this reads those words rather than guessing from the line that was cut.
fn verdict_of(clean: bool, diagnostic: &str) -> Verdict {
    if clean {
        return Verdict::Removable;
    }
    let syntactic = [
        "unexpected token",
        "expected term",
        "expected '",
        "unexpected identifier",
        "unexpected end of input",
        "expected command",
    ];
    if syntactic.iter().any(|marker| diagnostic.contains(marker)) {
        return Verdict::Inconclusive;
    }
    Verdict::LoadBearing
}

fn main() {
    let root = repository_root();
    let project = root.join(PROJECT);
    let corpus = project.join(CORPUS);
    println!("THE KERNEL DECIDES WHICH MOVES ARE LOAD-BEARING");
    println!("  project {}", project.display());
    println!("  corpus  {CORPUS}");
    if !corpus.is_file() {
        println!("  the corpus is absent");
        std::process::exit(2);
    }
    if !project.join(".lake/packages/mathlib").exists() {
        println!("  mathlib is not materialised for this project.");
        println!("  recover it with:  cd formal/elementary-holonics && lake exe cache get");
        std::process::exit(2);
    }

    let text = fs::read_to_string(&corpus).expect("the corpus reads");
    let lines: Vec<&str> = text.lines().collect();
    let reading = read_development_at(
        &text,
        DeclarationGrain::EveryTopLevelDeclaration,
        BinderGrain::EveryBinder,
    );
    let complex = MoveComplex::found(&reading.declarations);
    let connected: BTreeSet<MoveOccurrence> = complex.connected().into_iter().collect();
    let isolated: BTreeSet<MoveOccurrence> = complex.isolated().into_iter().collect();
    println!(
        "\n  declarations {}   moves {}   arrivals {}   connected {}   isolated {}",
        reading.declarations.len(),
        complex.moves(),
        complex.arrivals(),
        connected.len(),
        isolated.len()
    );
    if connected.is_empty() || isolated.is_empty() {
        println!("  one of the two populations is empty; there is no comparison to make");
        std::process::exit(2);
    }

    let scratch = root.join(".local/artifacts/the-kernel-decides-which-moves-are-load-bearing");
    fs::create_dir_all(&scratch).expect("the scratch root is writable");

    // The baseline. A file that does not check clean measures nothing when ablated.
    let baseline = scratch.join("baseline.lean");
    fs::write(&baseline, &text).expect("the baseline writes");
    let (baseline_clean, baseline_diagnostic) = check(&project, &baseline);
    println!(
        "  the unablated corpus checks {}",
        if baseline_clean { "CLEAN" } else { "NOT CLEAN" }
    );
    if !baseline_clean {
        println!(
            "{}",
            baseline_diagnostic
                .lines()
                .take(4)
                .collect::<Vec<_>>()
                .join("\n")
        );
        println!("  nothing below would mean anything; stopping");
        std::process::exit(1);
    }

    println!("\n  ablating one move at a time — its own line removed, everything else untouched");
    let mut rows: Vec<(MoveOccurrence, bool, usize, Verdict, String)> = Vec::new();
    for declaration in &reading.declarations {
        for (step_index, step) in declaration.steps.iter().enumerate() {
            let occurrence = MoveOccurrence {
                declaration: reading
                    .declarations
                    .iter()
                    .position(|form| std::ptr::eq(form, declaration))
                    .expect("the declaration is in the reading")
                    as u32,
                step: step_index as u32,
            };
            // Several binders of one destructuring share a line; ablating it once is enough.
            if rows.iter().any(|(_, _, line, _, _)| *line == step.line) {
                continue;
            }
            let ablated: String = lines
                .iter()
                .enumerate()
                .filter(|(index, _)| *index + 1 != step.line)
                .map(|(_, line)| *line)
                .collect::<Vec<_>>()
                .join("\n");
            let path = scratch.join(format!("without-line-{:04}.lean", step.line));
            fs::write(&path, &ablated).expect("the ablated file writes");
            let (clean, diagnostic) = check(&project, &path);
            let verdict = verdict_of(clean, &diagnostic);
            let is_connected = connected.contains(&occurrence);
            let head = diagnostic
                .lines()
                .find(|line| line.contains("error:"))
                .map(|line| {
                    let at = line.find("error:").unwrap_or(0);
                    line[at..].chars().take(64).collect::<String>()
                })
                .unwrap_or_default();
            println!(
                "    line {:4}  {:9}  {:?}  {}  {head}",
                step.line,
                if is_connected {
                    "connected"
                } else {
                    "isolated"
                },
                verdict,
                step.former
            );
            rows.push((occurrence, is_connected, step.line, verdict, head));
        }
    }

    // ---------------------------------------------------------------- the comparison
    let tally = |wanted_connected: bool| -> (usize, usize, usize) {
        let mut removable = 0;
        let mut load_bearing = 0;
        let mut inconclusive = 0;
        for (_, is_connected, _, verdict, _) in &rows {
            if *is_connected != wanted_connected {
                continue;
            }
            match verdict {
                Verdict::Removable => removable += 1,
                Verdict::LoadBearing => load_bearing += 1,
                Verdict::Inconclusive => inconclusive += 1,
            }
        }
        (removable, load_bearing, inconclusive)
    };
    let (connected_removable, connected_load, connected_unknown) = tally(true);
    let (isolated_removable, isolated_load, isolated_unknown) = tally(false);

    println!("\n  THE COMPARISON — exact counts, no rates presented as a single number");
    println!(
        "    connected   removable {connected_removable}   load-bearing {connected_load}   \
         inconclusive {connected_unknown}"
    );
    println!(
        "    isolated    removable {isolated_removable}   load-bearing {isolated_load}   \
         inconclusive {isolated_unknown}"
    );

    let connected_decided = connected_removable + connected_load;
    let isolated_decided = isolated_removable + isolated_load;
    println!("\n    removable, as a ratio over the DECIDED population only:");
    println!("      connected  {connected_removable}/{connected_decided}");
    println!("      isolated   {isolated_removable}/{isolated_decided}");

    if connected_decided == 0 || isolated_decided == 0 {
        println!(
            "\n  one population has no decided member, so the prediction cannot be tested here."
        );
        return;
    }
    println!(
        "\n  THE PREDICTION, declared before the run: an isolated move is removable more often."
    );

    // A comparison whose material cannot vary the property under test is the same defect as a check
    // that cannot fail — it just wears a verdict. If NOTHING is removable in either population the
    // question is undetermined here, and saying "the rates are equal" would dress a degenerate
    // material up as a finding.
    if connected_removable == 0 && isolated_removable == 0 {
        println!(
            "  UNDETERMINED — not one decided move in either population is removable, so this"
        );
        println!(
            "  material carries no variation in the property under test. The comparison has no"
        );
        println!("  resolving power here and no verdict is stated.");
    } else {
        // Cross-multiplied so the comparison stays in integers and no ratio is ever divided.
        let isolated_higher =
            isolated_removable * connected_decided > connected_removable * isolated_decided;
        let equal =
            isolated_removable * connected_decided == connected_removable * isolated_decided;
        println!(
            "  {}",
            if isolated_higher {
                "HELD — the kernel and the arrival graph agree about which moves carry weight."
            } else if equal {
                "DID NOT HOLD — the two rates are equal, so the arrival graph tracks nothing this \
                 instrument sees."
            } else {
                "REFUTED — connected moves are removable MORE often, which is the opposite of the \
                 reading's claim and is a finding about the reading."
            }
        );
    }

    // ---------------------------------------------------------------- why, measured directly
    //
    // The arrival graph tracks step -> step only. A declaration's CLOSING TERM is not a step, so a
    // `have` used only by the final `exact`/`linarith` line has no outgoing arrival and is called
    // isolated — while the kernel plainly needs it. Whether that is what happened here is not a
    // matter of argument: look at whether each isolated binder occurs again, later, in its own
    // declaration's text.
    println!("\n  WHY — is `isolated` the same population as `unused`?");
    let mut isolated_but_named_later = 0usize;
    let mut isolated_never_named_again = 0usize;
    for (index, declaration) in reading.declarations.iter().enumerate() {
        for (step_index, step) in declaration.steps.iter().enumerate() {
            let occurrence = MoveOccurrence {
                declaration: index as u32,
                step: step_index as u32,
            };
            if !isolated.contains(&occurrence) {
                continue;
            }
            let end =
                declaration.line + declaration.steps.iter().map(|s| s.line).max().unwrap_or(0);
            let named_later = lines
                .iter()
                .enumerate()
                .skip(step.line)
                .take_while(|(number, _)| *number + 1 <= end.max(step.line + 40))
                .any(|(_, line)| {
                    line.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
                        .any(|token| token == step.binder)
                });
            if named_later {
                isolated_but_named_later += 1;
            } else {
                isolated_never_named_again += 1;
            }
        }
    }
    println!(
        "    isolated moves whose binder IS named later in the same body   {isolated_but_named_later}"
    );
    println!(
        "    isolated moves whose binder is never named again              {isolated_never_named_again}"
    );
    if isolated_but_named_later > 0 {
        println!("    So `isolated` is NOT `unused`. The arrival graph joins step to step, and a");
        println!(
            "    declaration's closing term is not a step — a `have` consumed only by the final"
        );
        println!(
            "    tactic has no outgoing arrival and is called isolated while the kernel needs it."
        );
        println!(
            "    The repair is a terminal node for the closing term, so such a move is connected"
        );
        println!("    to it. Until that exists, `isolated` means *no later STEP arrives here* and");
        println!("    must not be read as *nothing uses this*.");
    }
}
