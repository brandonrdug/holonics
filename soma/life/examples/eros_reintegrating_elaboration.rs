//! Re-integration over elaboration, run on the machine's own deposited derivations.
//!
//! `research/records/2026-08-08_FACES_GROW_FROM_COLLOCATION_AND_THE_ATOM_IS_NOT_EMPTY.md` §4(v):
//! *"`soma/life/src/decomposing_codec.rs` performs DECOMPOSE → RE-INTEGRATE and revises its grain at
//! the collapsed pair's own separating word. The elaboration decomposes and never recomposes, so it
//! never learns what its own decomposition collapsed. That is the lightning shape — the leader founds
//! the channel, the return stroke rides it — and the two organs have never met."*
//!
//! This driver runs the join and returns its artifacts: the channels, the collapse with every pair's
//! own separating passage, the founded boundaries with the pairs that founded them, the founded
//! roots, the retained obstructions, and what moved when the second pass rode the changed route.
//!
//! ```text
//! cargo run --release -p life --example eros_reintegrating_elaboration \
//!     -- standing/output routes 1 6 200 output/reintegrating-elaboration
//! ```
//!
//! Arguments, all with declared defaults: the deposit root; the root aperture (`routes`, one meaning
//! per deposited artifact, or `declarations`, one meaning per declared name, which is the union over
//! its artifacts); the elaboration depth aperture (`exhausted` or a number); the bound on turns; the
//! **exhibition aperture**; and where a population larger than that aperture is deposited.
//!
//! **Why a bounded depth aperture is the default.** A bounded aperture makes the first pass state, by
//! name, what it reached and did not carry — `Elaboration::unopened`. That population is what the
//! causal-parity control is measured against: a name the first pass *proved* it does not hold,
//! carried by the second pass because a boundary founded a root at it. At exhaustion `unopened` is
//! empty by construction and the control has to rest on the other witnesses instead.
//!
//! **Why an exhibition aperture, and what it is not.** `CLAUDE.md` §9 requires the artifact itself to
//! be returned, and the collapse on this deposit is twenty-one thousand pairs. Every one is written
//! out, with its own separating passage — to the terminal when it fits the declared aperture and to a
//! named artifact otherwise. Nothing is sampled and nothing is reduced to a figure on its way
//! anywhere; the aperture decides *where* the population is written, never *which of it*.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};

use holonic_engine::derivation_atlas::{read_derivation, Derivation};
use holonic_engine::name_elaboration::{ElaborationAperture, ElaborationDeposit};

use life::reintegrating_elaboration::{
    render_passage, CollapsedPlace, MeaningGrain, MeaningRevision, Movement, NameAlphabet,
    Reintegration, ReintegrationPass, RestReason,
};

/// Every `.lean` artifact under `root`, in a stable filename order.
fn artifact_paths(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(artifact_paths(&path));
        } else if path
            .extension()
            .is_some_and(|extension| extension == "lean")
        {
            found.push(path);
        }
    }
    found
}

fn read_deposit(root: &Path) -> Vec<Derivation> {
    artifact_paths(root)
        .iter()
        .filter_map(|path| std::fs::read_to_string(path).ok())
        .filter_map(|text| read_derivation(&text))
        .collect()
}

/// Write a population out in full, either here or to a named artifact. The return is the artifact
/// path when it went there, so the caller states where the population is rather than how big it was.
fn exhibit(
    label: &str,
    lines: &[String],
    aperture: usize,
    deposit_at: &Path,
    file: &str,
) -> Option<PathBuf> {
    let written: usize = lines.iter().map(|line| line.lines().count().max(1)).sum();
    println!("\n  {label}: {} members, written out in full", lines.len());
    if written <= aperture {
        for line in lines {
            println!("    {line}");
        }
        return None;
    }
    let path = deposit_at.join(file);
    if let Some(parent) = path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    match std::fs::File::create(&path) {
        Ok(mut sink) => {
            for line in lines {
                let _ = writeln!(sink, "{line}");
            }
            println!(
                "    past the declared exhibition aperture of {aperture}; the whole population is \
                 deposited at {} , one line per member",
                path.display()
            );
            Some(path)
        }
        Err(error) => {
            println!("    could not deposit the population: {error}");
            None
        }
    }
}

/// The names the recomposition cannot tell apart: collapsed pairs whose two places are rooted at
/// two different declared names.
fn indistinguishable_names(places: &[CollapsedPlace]) -> BTreeMap<(String, String), Vec<String>> {
    let mut carried: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();
    for place in places {
        let (Some(left), Some(right)) = (place.left_root.as_ref(), place.right_root.as_ref())
        else {
            continue;
        };
        if left == right {
            continue;
        }
        carried
            .entry((left.clone(), right.clone()))
            .or_default()
            .push(render_passage(&place.separating_word));
    }
    for words in carried.values_mut() {
        words.sort();
        words.dedup();
    }
    carried
}

fn exhibit_pass(label: &str, pass: &ReintegrationPass, alphabet: &NameAlphabet) {
    println!("\n== {label} ==");
    let cuts: Vec<String> = pass
        .grain
        .cuts()
        .iter()
        .map(|word| render_passage(&alphabet.passage(word)))
        .collect();
    if cuts.is_empty() {
        println!("  grain        the origin: no boundary anywhere, one part per channel");
    } else {
        println!("  grain        {} boundaries", cuts.len());
    }
    println!(
        "  roots        {} declared, {} elaborated, {} refused",
        pass.roots.len(),
        pass.meanings.len(),
        pass.refused_roots.len()
    );
    for (root, refusal) in &pass.refused_roots {
        println!("               refused {root}: {refusal}");
    }
    println!(
        "  reading      one-shot {} blocks -> conduct {} blocks in {} rounds over {} places",
        pass.compression.one_shot.len(),
        pass.compression.conduct.len(),
        pass.compression.rounds,
        pass.system.prefixes().len(),
    );
    let failures = pass.reintegration_failures();
    println!(
        "  re-integrate {} channels rebuilt from their parts, {} refused",
        pass.meanings.len() - failures.len(),
        failures.len()
    );
    for failed in &failures {
        println!("               {} does not rebuild", failed.root);
    }
    let unopened = pass.unopened();
    println!(
        "  unopened     {:?} -- reached, named, and not carried by the meanings that named them",
        unopened.keys().collect::<Vec<_>>()
    );
}

fn main() {
    let mut argv = std::env::args().skip(1);
    let root = argv.next().unwrap_or_else(|| "standing/output".to_owned());
    let root_aperture = argv.next().unwrap_or_else(|| "routes".to_owned());
    let aperture = match argv.next().as_deref() {
        None | Some("1") => ElaborationAperture::ToDepth(1),
        Some("exhausted") => ElaborationAperture::Exhausted,
        Some(depth) => ElaborationAperture::ToDepth(depth.parse().expect("a depth")),
    };
    let bound: usize = argv
        .next()
        .map_or(6, |bound| bound.parse().expect("a bound"));
    let exhibition: usize = argv
        .next()
        .map_or(200, |aperture| aperture.parse().expect("an aperture"));
    let deposit_at = PathBuf::from(
        argv.next()
            .unwrap_or_else(|| "output/reintegrating-elaboration".to_owned()),
    );

    let population = read_deposit(Path::new(&root));
    let deposit = ElaborationDeposit::read(&population);
    let alphabet =
        NameAlphabet::over_deposit(&deposit).expect("the deposit fits the octet carrier");
    let roots: Vec<String> = match root_aperture.as_str() {
        "declarations" => deposit.declarations().keys().cloned().collect(),
        _ => deposit.route_keys().to_vec(),
    };

    println!("== THE DEPOSIT ==");
    println!("  root          {root}");
    println!("  artifacts     {}", population.len());
    println!(
        "  declared      {:?}",
        deposit.declarations().keys().collect::<Vec<_>>()
    );
    println!(
        "  alphabet      {} names over the octet carrier",
        alphabet.len()
    );
    println!(
        "  apertures     roots={root_aperture} ({} roots), depth={aperture:?}, turns<={bound}, \
         exhibition={exhibition}",
        roots.len()
    );

    let run = Reintegration::run(&deposit, &alphabet, &roots, aperture, bound)
        .expect("the deposit elaborates");

    // ------------------------------------------------------------------ turn zero: the leader
    let leader = &run.turns[0];
    exhibit_pass(
        "TURN 0 -- THE LEADER: a name, elaborated, then re-integrated",
        &leader.pass,
        &alphabet,
    );
    let channels: Vec<String> = leader
        .pass
        .meanings
        .iter()
        .map(|meaning| render_passage(&alphabet.passage(&meaning.channel)))
        .collect();
    exhibit(
        "CHANNELS -- the leader's steps, in walk order",
        &channels,
        exhibition,
        &deposit_at,
        "channels.txt",
    );

    let leader_places = leader
        .pass
        .collapsed_places(&alphabet)
        .expect("names for every place");
    let collapse: Vec<String> = leader_places.iter().map(CollapsedPlace::exhibit).collect();
    let collapse_artifact = exhibit(
        "THE COLLAPSE -- every pair the re-integration merged, with its own separating passage",
        &collapse,
        exhibition,
        &deposit_at,
        "collapsed-turn-0.txt",
    );

    let indistinguishable = indistinguishable_names(&leader_places);
    let names: Vec<String> = indistinguishable
        .iter()
        .map(|((left, right), words)| format!("{left} | {right}   separated by {words:?}"))
        .collect();
    exhibit(
        "THE NAMES THE RECOMPOSITION CANNOT TELL APART",
        &names,
        exhibition,
        &deposit_at,
        "indistinguishable-names-turn-0.txt",
    );

    // ------------------------------------------------------------------------- the revision
    let mut controls: Vec<(&str, bool, String)> = Vec::new();

    let Some(revision) = leader.revision.as_ref() else {
        println!(
            "\n== THE REVISION ==\n  none: the re-integration was exact and nothing was founded"
        );
        report(&run, &controls);
        return;
    };

    println!("\n== THE REVISION -- boundaries founded by the collapse ==");
    println!(
        "  {} boundaries founded, one per collapsed pair, factoring through {} distinct passages \
         ({} new to the grain, {} it already held)",
        revision.founded.len(),
        revision.added.len() + revision.already_carried.len(),
        revision.added.len(),
        revision.already_carried.len()
    );
    let boundaries: Vec<String> = revision
        .added
        .iter()
        .map(|word| {
            let names = render_passage(&alphabet.passage(word));
            let cause = revision.cause_of(word).expect("a founded boundary");
            format!("cut at '{names}'  founded by  {}", cause.place.exhibit())
        })
        .collect();
    exhibit(
        "EVERY DISTINCT BOUNDARY, WITH THE PAIR THAT FOUNDED IT",
        &boundaries,
        exhibition,
        &deposit_at,
        "boundaries-turn-0.txt",
    );

    println!("\n  founded roots -- a boundary opened a part at a name the deposit CAN open:");
    if revision.founded_roots.is_empty() {
        println!("    none");
    }
    for founded in &revision.founded_roots {
        println!(
            "    {}  opened by '{}'  inside {} channels",
            founded.name,
            render_passage(&alphabet.passage(&founded.word)),
            founded.inside.len()
        );
    }
    println!("\n  retained obstructions -- a boundary at a name the deposit CANNOT open:");
    if revision.unopenable.is_empty() {
        println!("    none");
    }
    for obstruction in &revision.unopenable {
        println!(
            "    {}  opened by '{}'  inside {} channels",
            obstruction.name,
            render_passage(&alphabet.passage(&obstruction.word)),
            obstruction.inside.len()
        );
    }

    // ------------------------------------------------------- turn one: the return stroke
    let Some(movement) = leader.movement.as_ref() else {
        println!(
            "\n== TURN 1 ==\n  none: the run rested at turn {} ({:?})",
            run.rested_at, run.rest
        );
        report(&run, &controls);
        return;
    };
    let rider = &run.turns[1];
    exhibit_pass(
        "TURN 1 -- THE RETURN STROKE: later current on the route the first pass changed",
        &rider.pass,
        &alphabet,
    );

    println!("\n== WHAT MOVED, AND WHAT CAUSED IT ==");
    println!(
        "  {} meanings moved, {} stood still",
        movement.changed.len(),
        movement.unchanged.len()
    );
    let moved: Vec<String> = movement
        .changed
        .iter()
        .map(|moved| {
            let causes: Vec<String> = moved
                .caused_by
                .iter()
                .map(|cause| {
                    format!(
                        "cut '{}' <- pair ('{}' | '{}') separated by '{}'",
                        render_passage(&cause.names),
                        render_passage(&cause.place.left),
                        render_passage(&cause.place.right),
                        render_passage(&cause.place.separating_word),
                    )
                })
                .collect();
            format!(
                "{}\n        before  {:?}\n        after   {:?}\n        caused by  {}",
                moved.root,
                moved
                    .before
                    .iter()
                    .map(|part| render_passage(part))
                    .collect::<Vec<_>>(),
                moved
                    .after
                    .iter()
                    .map(|part| render_passage(part))
                    .collect::<Vec<_>>(),
                causes.join("\n                   "),
            )
        })
        .collect();
    exhibit(
        "EVERY MEANING THAT MOVED, WITH THE PAIR THAT MOVED IT",
        &moved,
        exhibition,
        &deposit_at,
        "moved-turn-0-to-1.txt",
    );

    println!("\n== WHAT THE SECOND PASS REACHED AND THE FIRST COULD NOT ==");
    let new_places: Vec<String> = movement
        .new_places
        .iter()
        .map(|place| render_passage(place))
        .collect();
    exhibit(
        "NEW PLACES -- a place with no rooted prefix; the first pass had no item for it at all",
        &new_places,
        exhibition,
        &deposit_at,
        "new-places-turn-1.txt",
    );
    println!("\n  new roots         {:?}", movement.new_roots);
    println!(
        "  new constituents  {:?}",
        movement.new_constituents.iter().collect::<Vec<_>>()
    );
    println!("\n  reached past the first aperture -- a name the first pass returned as UNOPENED:");
    if movement.reached_past_the_first_aperture.is_empty() {
        println!("    none");
    }
    for reached in &movement.reached_past_the_first_aperture {
        println!(
            "    {}  was unopened from {} of the first pass's meanings, now carried by {}{}",
            reached.name,
            reached.was_unopened_from.len(),
            reached.now_reached_from,
            if reached.absent_from_the_first_pass {
                "  [and no first-pass meaning carried it at all]"
            } else {
                "  [some other first-pass meaning already carried it]"
            }
        );
    }
    let new_collapses: Vec<String> = movement
        .new_collapses
        .iter()
        .map(CollapsedPlace::exhibit)
        .collect();
    exhibit(
        "NEW COLLAPSES -- pairs at places the first pass did not have",
        &new_collapses,
        exhibition,
        &deposit_at,
        "new-collapses-turn-1.txt",
    );

    // ------------------------------------------------------------------------------ controls
    controls.push((
        "1. the second pass differs from the first, and every difference names its cause",
        !movement.is_still()
            && !movement.changed.is_empty()
            && movement
                .changed
                .iter()
                .all(|moved| !moved.caused_by.is_empty() && moved.before != moved.after),
        format!(
            "{} of {} meanings moved; every one names the collapsed pair and the separating passage \
             that cut it",
            movement.changed.len(),
            movement.changed.len() + movement.unchanged.len(),
        ),
    ));

    controls.push(no_op_control());

    let reached_something = !movement.new_places.is_empty()
        || !movement.new_collapses.is_empty()
        || !movement.reached_past_the_first_aperture.is_empty()
        || !movement.new_constituents.is_empty();
    controls.push((
        "3. it is not a replay: the second pass reaches what the first could not",
        reached_something,
        format!(
            "{} places with no rooted prefix, {} collapses at those places, {} aperture crossings \
             ({} of them onto material no first-pass meaning carried), {} new constituents",
            movement.new_places.len(),
            movement.new_collapses.len(),
            movement.reached_past_the_first_aperture.len(),
            movement
                .reached_past_the_first_aperture
                .iter()
                .filter(|reached| reached.absent_from_the_first_pass)
                .count(),
            movement.new_constituents.len(),
        ),
    ));

    let exhibited = leader_places.len() == leader.pass.collapsed().len()
        && leader_places
            .iter()
            .all(|place| !place.separating_word.is_empty());
    controls.push((
        "4. the collapse is exhibited, never counted",
        exhibited,
        format!(
            "{} collapsed pairs, {} written out in full{}, every one carrying a non-empty separating \
             passage and the receiver that saw the difference",
            leader.pass.collapsed().len(),
            leader_places.len(),
            collapse_artifact
                .as_ref()
                .map_or_else(String::new, |path| format!(" at {}", path.display())),
        ),
    ));

    controls.push((
        "5. it terminates, and the turn and the reason are reported",
        run.rest != RestReason::BoundReached,
        format!(
            "rested at turn {} because {:?}; {} turns taken against a declared bound of {bound}",
            run.rested_at,
            run.rest,
            run.turns.len()
        ),
    ));

    controls.push(foil_control(
        &deposit, &alphabet, &roots, aperture, revision,
    ));

    report(&run, &controls);
}

/// **The no-op control.** A re-integration that collapses nothing must found no boundary and leave
/// the next pass bit-identical. If any revision always moved something, the revision would be noise
/// rather than conduct.
///
/// The material is declared here rather than taken from the deposit, because a deposit that
/// collapses nothing is exactly what this deposit is not — and a control needs material that can
/// exercise it. The channel below has a distinct successor name at every position, so the one-shot
/// partition is already discrete and nothing can be collapsed.
fn no_op_control() -> (&'static str, bool, String) {
    let population = vec![Derivation {
        name: "only".to_owned(),
        statement: "S".to_owned(),
        recruited: [("aaa", 1u32), ("bbb", 1), ("ccc", 1), ("ddd", 1)]
            .into_iter()
            .map(|(symbol, count)| (symbol.to_owned(), count))
            .collect(),
    }];
    let deposit = ElaborationDeposit::read(&population);
    let alphabet = NameAlphabet::over_deposit(&deposit).expect("a small alphabet");
    let roots = vec!["only#0".to_owned()];
    let first = ReintegrationPass::read(
        &deposit,
        &alphabet,
        &roots,
        ElaborationAperture::Exhausted,
        &MeaningGrain::origin(),
    )
    .expect("the route is in the deposit");
    let revision = MeaningRevision::revise(&first, &alphabet, &deposit).expect("a revision");
    let again = ReintegrationPass::read(
        &deposit,
        &alphabet,
        &roots,
        ElaborationAperture::Exhausted,
        &revision.grain,
    )
    .expect("the route is in the deposit");
    let movement = Movement::read(&first, &again, &revision, &alphabet).expect("a movement");
    let held = first.is_exact()
        && revision.founded.is_empty()
        && revision.added.is_empty()
        && revision.founded_roots.is_empty()
        && again == first
        && movement.is_still();
    (
        "2. a re-integration that collapses nothing leaves the second pass bit-identical",
        held,
        format!(
            "declared control channel 'only#0\u{b7}aaa\u{b7}bbb\u{b7}ccc\u{b7}ddd': collapsed {} \
             pairs, founded {} boundaries, {} founded roots; second pass == first pass is {}",
            first.collapsed().len(),
            revision.founded.len(),
            revision.founded_roots.len(),
            again == first
        ),
    )
}

/// **The foil**, carried over from `decomposing_codec`'s own falsifier: cut at a word of the same
/// length the compression did *not* return. If any cut whatsoever moved the reading the same way,
/// the derivation would be decorative and the crossing would be "cutting more is better" wearing a
/// lineage.
fn foil_control(
    deposit: &ElaborationDeposit,
    alphabet: &NameAlphabet,
    roots: &[String],
    aperture: ElaborationAperture,
    revision: &MeaningRevision,
) -> (&'static str, bool, String) {
    // A root key occurs at position zero of exactly one channel and nowhere else, so cutting after
    // it is a boundary no collapse asked for and no channel is split by it in the interior.
    let foil_name = roots.first().expect("a root").clone();
    let foil_word = vec![alphabet.symbol(&foil_name).expect("declared")];
    if revision.added.contains(&foil_word) {
        return (
            "foil. a boundary the collapse did not return is not interchangeable with one it did",
            false,
            "the declared foil word was itself returned by the collapse".to_owned(),
        );
    }
    let foil = MeaningGrain::origin().with(foil_word).expect("a boundary");
    let foil_pass = ReintegrationPass::read(deposit, alphabet, roots, aperture, &foil)
        .expect("the deposit elaborates");
    let derived_pass = ReintegrationPass::read(deposit, alphabet, roots, aperture, &revision.grain)
        .expect("the deposit elaborates");
    (
        "foil. a boundary the collapse did not return is not interchangeable with one it did",
        foil_pass.system != derived_pass.system,
        format!(
            "cutting after '{foil_name}' leaves {} places and {} collapsed pairs; cutting where the \
             reading's own loss asked, over the same roots, leaves {} places and {} collapsed pairs",
            foil_pass.system.prefixes().len(),
            foil_pass.collapsed().len(),
            derived_pass.system.prefixes().len(),
            derived_pass.collapsed().len(),
        ),
    )
}

fn report(run: &Reintegration, controls: &[(&str, bool, String)]) {
    println!("\n== TERMINATION ==");
    println!(
        "  rested at turn {} of {} because {:?}",
        run.rested_at,
        run.turns.len(),
        run.rest
    );
    match run.rest {
        RestReason::ReintegrationIsExact => println!(
            "  the one-shot re-integration lost nothing later conduct through the channel can see, \
             so there is no boundary left to found"
        ),
        RestReason::GrainDidNotGrow => println!(
            "  the collapse demands only boundaries the grain already carries: a fixed point. The \
             remainder is irreducible under this revision rule and is retained above."
        ),
        RestReason::BoundReached => println!(
            "  the declared bound was reached with the collapse still growing the grain. The state \
             is returned rather than the run being called a failure."
        ),
    }
    let grains: Vec<usize> = run
        .turns
        .iter()
        .map(|turn| turn.pass.grain.cuts().len())
        .collect();
    let collapses: Vec<usize> = run
        .turns
        .iter()
        .map(|turn| turn.pass.collapsed().len())
        .collect();
    let places: Vec<usize> = run
        .turns
        .iter()
        .map(|turn| turn.pass.system.prefixes().len())
        .collect();
    println!("  boundaries per turn       {grains:?}");
    println!("  places per turn           {places:?}");
    println!("  collapsed pairs per turn  {collapses:?}");

    println!("\n== CONTROLS ==");
    let mut failed = 0usize;
    for (name, held, evidence) in controls {
        println!("  [{}] {name}", if *held { "holds" } else { "FAILS" });
        println!("        {evidence}");
        if !held {
            failed += 1;
        }
    }
    if failed > 0 {
        println!("\n{failed} declared control(s) failed.");
        std::process::exit(1);
    }
}
