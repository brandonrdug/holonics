//! The extent of every link in a derivation's realized scaffold, computed from the incidence rather
//! than from a remembered multiplier — and conducted against the faces at every realized vertex.
//!
//! ```text
//! cargo run --release --example the_link_extent_is_read_off_the_incidence -- \
//!     standing/output \
//!     archive/reference/pureholonics-seed/src/pureholonics \
//!     archive/reference/holobrochos-a07ff376/src/soma
//! ```
//!
//! `crates/holonic-engine/src/derivation_curvature.rs` carried, until 2026-08-09, an authored level:
//! `SCAFFOLD_LINK_FOLD: usize = 3`, read at exactly two sites —
//! `FrameAgreement::fold_holds`, and one test. `docs/canon/THE_AUTHORED_LEVEL.md` §5.1 names its
//! replacement in four words: *the fold from the incidence*.
//!
//! **The three was a theorem, and the theorem is stated and kept.** For a site `v` of the layout,
//! the ribbon-graph scaffold puts in `v`'s link every neighbour of `v` (from the carry face of the
//! dart joining them), the rim vertex of every dart leaving `v` (from the corner face at that dart),
//! and the rim vertex of every dart entering `v` (from that dart's own carry face). The layout
//! refuses a self-incidence and a parallel incidence, so an incident edge contributes exactly one
//! dart out and one dart in, and rim vertices are one per dart and therefore all distinct:
//!
//! ```text
//!    extent(v) = |N(v)| + |out-darts(v)| + |in-darts(v)| = 3 * degree(v)
//! ```
//!
//! **What the constant could not do is leave the sites.** A realization of `|E|` incidences adds
//! `2|E|` rim vertices, and their links are not a multiple of anything the derivation carries: the
//! apex of each face walk has extent `span + 1`, the two darts adjacent to it have `4`, the rest
//! have `5`, and a walk of span two has `3` throughout because it founds no rim fan at all. Those
//! `2|E|` vertices carried no extent check before — only the classification that the link is a
//! cycle.
//!
//! This driver reports the population on both sides of that line. The run exits nonzero when any
//! declared control fails.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::conditioned_derivation::{
    ConditionedBody, ConditionedCircuit, DerivationQuery, Exposure, expose,
};
use holonic_engine::derivation_atlas::{CircuitAperture, ReachOrientation};
use holonic_engine::derivation_curvature::{
    DerivationCurvatureBody, ScaffoldLink, ScaffoldLinkLaw,
};

fn material(root: &Path, extension: &str) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(material(&path, extension));
        } else if path.extension().is_some_and(|carried| carried == extension) {
            found.push(path);
        }
    }
    found
}

fn read_deposit(root: &Path) -> Vec<(String, String)> {
    material(root, "lean")
        .into_iter()
        .filter_map(|path| {
            std::fs::read_to_string(&path)
                .ok()
                .map(|text| (path.display().to_string(), text))
        })
        .collect()
}

fn read_corpus(root: &Path) -> Vec<Exposure> {
    material(root, "md")
        .into_iter()
        .filter_map(|path| {
            std::fs::read_to_string(&path)
                .ok()
                .map(|text| expose(&path.display().to_string(), &text))
        })
        .collect()
}

/// The two declared fixtures, built the way the module's own tests build them.
fn declared(deposit: Vec<(String, String)>) -> ConditionedCircuit {
    ConditionedBody::mount(deposit)
        .expect("the deposit reads")
        .circuit(
            &DerivationQuery::reaching(": P"),
            CircuitAperture {
                identity: holonic_engine::derivation_atlas::DerivationIdentity::ByDeclaration,
                coefficient: holonic_engine::derivation_atlas::RecruitmentCoefficient::Incidence,
                reach: ReachOrientation::IntoDerivation,
                statements: holonic_engine::derivation_atlas::StatementIncidence::Withheld,
            },
        )
        .expect("the circuit founds")
}

fn four_cycle() -> ConditionedCircuit {
    declared(vec![
        (
            "alpha".to_owned(),
            "theorem alpha : P := by\n  have one := carryOne\n  have two := carryTwo\n".to_owned(),
        ),
        (
            "beta".to_owned(),
            "theorem beta : P := by\n  have one := carryOne\n  have two := carryTwo\n".to_owned(),
        ),
    ])
}

fn star() -> ConditionedCircuit {
    declared(vec![(
        "star".to_owned(),
        "theorem star : P := by\n  have one := carryOne\n  have two := carryTwo\n  have three := carryThree\n"
            .to_owned(),
    )])
}

fn population(law: &ScaffoldLinkLaw) -> BTreeMap<usize, usize> {
    law.extents.clone()
}

fn print_law(name: &str, body: &DerivationCurvatureBody, law: &ScaffoldLinkLaw) {
    println!(
        "\n  {name}: {} sites, {} incidences, {} face walks",
        body.layout.sites().len(),
        body.layout.incidences().len(),
        body.face_walks()
    );
    println!(
        "    realized vertices {:>6}      the excised constant covered {:>6} of them",
        law.pairs.len(),
        law.sites().len()
    );
    println!(
        "    rim vertices      {:>6}      2 * |incidences| = {}",
        law.rim().len(),
        2 * body.layout.incidences().len()
    );
    println!("    predicted extent -> how many vertices carry it");
    println!("      whole realization  {:?}", population(law));
    println!("      derivation sites   {:?}", law.site_extents);
    let rim_only: BTreeMap<usize, usize> = {
        let mut carried: BTreeMap<usize, usize> = BTreeMap::new();
        for pair in law.rim() {
            *carried.entry(pair.predicted_extent).or_default() += 1;
        }
        carried
    };
    println!("      rim                {rim_only:?}");
    let spans: BTreeMap<usize, usize> = {
        let mut carried: BTreeMap<usize, usize> = BTreeMap::new();
        for pair in law.rim() {
            if let ScaffoldLink::Rim { span, .. } = pair.predicted {
                *carried.entry(span).or_default() += 1;
            }
        }
        carried
    };
    println!("      face-walk span -> darts in a walk of that span   {spans:?}");
    println!(
        "    disagreements against local_star's face-derived link: {}",
        law.disagreements().len()
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();

    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!(
        "law=a scaffold link extent is counted from the darts, never multiplied by a constant"
    );
    println!("excised=SCAFFOLD_LINK_FOLD: usize = 3  (derivation_curvature.rs:208 at 085a9ab)");

    println!("\nWHAT DERIVES THE EXTENT NOW");
    println!("---------------------------");
    println!("  site  extent = |N(v)| + |out-darts(v)| + |in-darts(v)|");
    println!(
        "        Every neighbour enters the link from the carry face of the dart joining them;"
    );
    println!(
        "        every dart LEAVING v brings its rim vertex from the corner face at that dart;"
    );
    println!(
        "        every dart ENTERING v brings its rim vertex from that dart's own carry face."
    );
    println!(
        "        A self-incidence and a parallel incidence are refused, so an incident edge is"
    );
    println!(
        "        exactly one dart out and one dart in, and the three terms are each the degree."
    );
    println!("        The THREE is what that sum returns; it is not what the sum is told.");
    println!();
    println!("  rim   span = 2                 3       the walk founds no rim fan at all");
    println!(
        "        span >= 3, position 0     span+1  the apex of the fan, adjacent to every rim"
    );
    println!("                   1 or span-1    4       one fan each");
    println!("                   otherwise      5       two fans each");
    println!();
    println!("  The rim is where the constant could not go. It is `2 * |incidences|` vertices and");
    println!("  they carried no extent check before, only the classification that the link is a");
    println!("  cycle. Every figure below is a check that did not exist.");

    let mut holds: Vec<(&str, bool, String)> = Vec::new();
    let mut laws: Vec<(String, ScaffoldLinkLaw)> = Vec::new();

    println!("\nTHE DECLARED FIXTURES");
    println!("---------------------");
    for (name, circuit) in [("four_cycle", four_cycle()), ("star", star())] {
        let body = DerivationCurvatureBody::found(&circuit).expect("the layout realizes");
        let law = body.link_law().expect("the realization carries its links");
        print_law(name, &body, &law);

        // The theorem at the sites, returned rather than asserted.
        let folds: BTreeSet<usize> = law
            .sites()
            .iter()
            .filter(|pair| body.layout.coordination(pair.vertex) > 0)
            .map(|pair| pair.predicted_extent / body.layout.coordination(pair.vertex))
            .collect();
        println!("    the fold the site population RETURNED: {folds:?}");
        holds.push((
            "the site fold is three, as a returned count",
            folds == BTreeSet::from([3usize]),
            format!("{name}: {folds:?}"),
        ));
        laws.push((name.to_owned(), law));
    }

    println!("\nTHE CONDITIONED BODY");
    println!("--------------------");
    if arguments.len() < 2 {
        println!("  no material supplied; the declared fixtures above still stand");
    } else {
        let deposit = read_deposit(Path::new(&arguments[0]));
        let exposures: Vec<Exposure> = arguments[1..]
            .iter()
            .flat_map(|root| read_corpus(Path::new(root)))
            .collect();
        println!(
            "  mathematical {:<48} {} artifacts",
            arguments[0],
            deposit.len()
        );
        println!(
            "  linguistic   {} wholes over {} roots",
            exposures.len(),
            arguments.len() - 1
        );
        if deposit.is_empty() || exposures.is_empty() {
            println!("  the material is absent; the declared fixtures above still stand");
        } else {
            let mut body = ConditionedBody::mount(deposit).expect("the deposit reads");
            body.condition(&exposures);
            let circuit = body
                .circuit(
                    &DerivationQuery::reaching("(P : Prop) (h : P) : exactCarrier P"),
                    CircuitAperture::STATEMENT_INCIDENT,
                )
                .expect("the conditioned circuit founds");
            let realized = DerivationCurvatureBody::found(&circuit).expect("the layout realizes");
            let law = realized
                .link_law()
                .expect("the realization carries its links");
            print_law("conditioned production", &realized, &law);
            laws.push(("conditioned production".to_owned(), law));
        }
    }

    println!("\nCONTROLS");
    println!("--------");
    for (name, law) in &laws {
        holds.push((
            "the incidence's prediction agrees with local_star's face-derived link everywhere",
            law.disagreements().is_empty(),
            format!(
                "{name}: {} of {} vertices",
                law.pairs.len(),
                law.pairs.len()
            ),
        ));
        holds.push((
            "the law takes more than one value, so it is a law and not a constant",
            law.is_non_constant(),
            format!("{name}: extents {:?}", law.extents),
        ));
        holds.push((
            "the rim carries an extent no multiple of a derivation coordination produces",
            law.rim()
                .iter()
                .any(|pair| !law.site_extents.contains_key(&pair.predicted_extent)),
            format!(
                "{name}: {} rim vertices against site extents {:?}",
                law.rim().len(),
                law.site_extents.keys().collect::<Vec<_>>()
            ),
        ));
    }

    let mut failed = 0;
    for (claim, verdict, evidence) in &holds {
        println!(
            "  [{}] {claim}\n        {evidence}",
            if *verdict { "holds" } else { "FAILED" }
        );
        if !verdict {
            failed += 1;
        }
    }
    if failed > 0 {
        println!("\n{failed} declared control(s) failed");
        std::process::exit(1);
    }
    println!("\nevery declared control holds");
}
