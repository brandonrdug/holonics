//! DECOMPOSE → RE-INTEGRATE, run on material and made to return its artifacts.
//!
//! `blueprint/THE_ASSEMBLY.md` loop (a). A decomposer runs as a codec; its own byte-level reading of
//! the parts it produced over-collapses; every collapsed pair founds a parented codec version
//! cutting at that pair's shortest distinguishing word; the next batch is read under their join.
//!
//! This driver returns the **artifacts** — the parts, the collapsed pairs with their words and the
//! receiver that saw each difference, the founded lineage, and the re-integrated wholes. The counts
//! it prints are captions on artifacts that are printed beside them, never the return.

use std::collections::BTreeSet;

use life::decomposing_codec::{
    decompose, read, render_word, DecomposingBody, DecompositionGrain, DecompositionPass,
    DecompositionProgram, Symbol,
};

/// Every collapsed pair of a pass, written out: the two places the byte-level reading merged and
/// the shortest word that shows they are not the same place. This is what the falsifier and the
/// foil are compared on — the populations themselves, with their sizes as captions beside them.
fn population(pass: &DecompositionPass) -> Vec<String> {
    pass.collapsed()
        .iter()
        .map(|pair| {
            format!(
                "'{}'|'{}' by '{}'",
                render_word(pass.system.prefix_of(pair.left).expect("an item")),
                render_word(pass.system.prefix_of(pair.right).expect("an item")),
                render_word(
                    &pass
                        .system
                        .word_symbols(&pair.distinguishing_word)
                        .expect("a word over the alphabet")
                ),
            )
        })
        .collect()
}

const BATCH_A: &[&str] = &["abx.aby.cbx.cbz.", "dby.dbz.ebx.eby.ebz.", "prsx.qrsy."];
const BATCH_C: &[&str] = &[
    "abz.abw.cby.cbw.",
    "dbx.dbw.ebz.ebw.eby.",
    "fbx.fbw.gbz.gby.",
    "prsw.qrsz.",
    "mkx.mky.nkx.nkz.",
];
const BATCH_D: &[&str] = &["abx.cbw.gby.prsz.", "mkw.nky.fbz.dbw."];

fn word(text: &str) -> Vec<Symbol> {
    text.bytes().map(Symbol).collect()
}

fn batch(wholes: &[&str]) -> Vec<Vec<Symbol>> {
    wholes.iter().map(|whole| word(whole)).collect()
}

fn exhibit(label: &str, pass: &DecompositionPass) {
    println!("\n== {label} ==");
    println!(
        "  grain      {:?}",
        pass.grain
            .cuts()
            .iter()
            .map(|cut| render_word(cut))
            .collect::<Vec<_>>()
    );
    println!(
        "  parts      {:?}",
        pass.parts()
            .iter()
            .map(|part| render_word(part))
            .collect::<Vec<_>>()
    );
    println!(
        "  reading    one-shot {} blocks -> conduct {} blocks in {} rounds",
        pass.compression.one_shot.len(),
        pass.compression.conduct.len(),
        pass.compression.rounds
    );
    if pass.compression.is_exact() {
        println!("  collapsed  none: the byte-level reading is already receiver-exact here");
    }
    for pair in pass.collapsed() {
        let walk = pass
            .system
            .word_symbols(&pair.distinguishing_word)
            .expect("a word over the alphabet");
        let witness = match pair.witness {
            Some((receiver, left, right)) => format!(
                "receiver '{}' returned {} against {}",
                u8::try_from(receiver.0).map_or('?', char::from),
                left.0,
                right.0
            ),
            None => "a terminus, with no receiver naming it".to_owned(),
        };
        println!(
            "  collapsed  '{}' | '{}'  separated by '{}'  ({witness})",
            render_word(pass.system.prefix_of(pair.left).expect("an item")),
            render_word(pass.system.prefix_of(pair.right).expect("an item")),
            render_word(&walk),
        );
    }
    let rebuilt = pass.reintegration();
    let sources: Vec<Vec<Symbol>> = pass
        .decomposed
        .iter()
        .map(|whole| whole.source.clone())
        .collect();
    println!(
        "  reintegrate {:?}",
        rebuilt.iter().map(|whole| render_word(whole)).collect::<Vec<_>>()
    );
    println!(
        "  refused    {:?}",
        pass.reintegration_failures()
            .iter()
            .map(|(at, source, back)| format!(
                "whole {at}: '{}' came back as '{}'",
                render_word(source),
                render_word(back)
            ))
            .collect::<Vec<_>>()
    );
    assert_eq!(rebuilt, sources, "re-integration must return the wholes");
}

fn main() {
    let origin = DecompositionGrain::declare([word(".")]).expect("one non-empty cut word");

    // --- the crossing --------------------------------------------------------------------------
    let mut body = DecomposingBody::mount(origin.clone()).expect("a declared grain");
    body.receive(batch(BATCH_A)).expect("readable");
    exhibit("pass one, under the declared origin grain", &body.passes()[0]);
    let first = body.revise().expect("a collapsed population revises");
    println!(
        "\n  revision one founds {} parented codec versions over {} distinct words {:?}",
        first.founded.len(),
        first.words.len(),
        first.words.iter().map(|w| render_word(w)).collect::<Vec<_>>()
    );
    for founded in &first.founded {
        let version = body.runtime().codec(founded.codec).expect("it stands");
        let DecompositionProgram::CutAtDistinguishingWord { grain, word, pair } = &version.program
        else {
            panic!("a per-pair version cuts at its pair's word");
        };
        // The word printed is RECOMPUTED from the pair this version retained, not read off the
        // same binding twice, so the line below cannot say `cuts at 'b' because 'p' | 'q' were
        // merged`. And the grain is the parent's grain plus exactly this one word.
        let derived = body.passes()[0]
            .system
            .word_symbols(&pair.distinguishing_word)
            .expect("a word over the alphabet");
        assert_eq!(word, &derived, "a version must cut at its own pair's word");
        assert_eq!(&founded.word, &derived);
        assert_eq!(
            grain,
            &origin.with(derived.clone()).expect("a non-empty word"),
            "a per-pair grain is the parent's grain plus exactly this pair's word"
        );
        println!(
            "    codec {:?} parents {:?} cuts at '{}' because '{}' | '{}' were merged",
            founded.codec.0,
            version.parents.iter().map(|p| p.0).collect::<Vec<_>>(),
            render_word(&derived),
            render_word(
                body.passes()[0]
                    .system
                    .prefix_of(pair.left)
                    .expect("an item")
            ),
            render_word(
                body.passes()[0]
                    .system
                    .prefix_of(pair.right)
                    .expect("an item")
            ),
        );
    }

    body.receive(batch(BATCH_C)).expect("readable");
    exhibit("pass two, under the joined revision", &body.passes()[1]);
    let second = body.revise().expect("a collapsed population revises");
    println!(
        "\n  revision two founds {} version(s) over {:?}, parented on the first revision's join",
        second.founded.len(),
        second.words.iter().map(|w| render_word(w)).collect::<Vec<_>>()
    );

    let third = body.receive(batch(BATCH_D)).expect("readable");
    exhibit("pass three, under the twice-revised grain", &body.passes()[2]);
    println!(
        "\n  the reading rested rather than reflecting: {:?}, reflection {:?}",
        third.state, third.reflection
    );

    // --- the same material, decomposed before and after ------------------------------------------
    let unseen = &batch(BATCH_C)[0];
    println!("\n== the same unseen whole, cut by parent and by child ==");
    println!("  whole   '{}'", render_word(unseen));
    println!(
        "  parent  {:?}",
        decompose(&origin, unseen)
            .iter()
            .map(|p| render_word(p))
            .collect::<Vec<_>>()
    );
    println!(
        "  child   {:?}",
        decompose(&first.grain, unseen)
            .iter()
            .map(|p| render_word(p))
            .collect::<Vec<_>>()
    );

    // --- the falsifier, run --------------------------------------------------------------------
    let mut ablated = DecomposingBody::mount(origin.clone()).expect("a declared grain");
    ablated.receive(batch(BATCH_A)).expect("readable");
    ablated.resume_unrevised().expect("an open reflection");
    ablated.receive(batch(BATCH_C)).expect("readable");
    ablated.resume_unrevised().expect("an open reflection");
    ablated.receive(batch(BATCH_D)).expect("readable");

    println!("\n== the falsifier ==");
    for (label, run) in [("revised", &body), ("ablated", &ablated)] {
        for (at, pass) in run.passes().iter().enumerate() {
            let left = population(pass);
            println!("  {label} pass {at}: {} pair(s) {left:?}", left.len());
        }
    }
    // The lineages themselves, not their sizes: what each body founded, in words.
    for (label, run) in [("revised", &body), ("ablated", &ablated)] {
        println!(
            "  {label} lineage {:?}",
            run.runtime()
                .codecs()
                .map(|version| match &version.program {
                    DecompositionProgram::Origin(grain) => format!(
                        "codec {} origin {:?}",
                        version.id.0,
                        grain.cuts().iter().map(|cut| render_word(cut)).collect::<Vec<_>>()
                    ),
                    DecompositionProgram::CutAtDistinguishingWord { word, .. } =>
                        format!("codec {} cuts '{}'", version.id.0, render_word(word)),
                    DecompositionProgram::JoinedRevision { words, .. } => format!(
                        "codec {} joins {:?}",
                        version.id.0,
                        words.iter().map(|w| render_word(w)).collect::<Vec<_>>()
                    ),
                })
                .collect::<Vec<_>>()
        );
    }

    // The foil: cuts of the same shape that the compression never returned.
    let foils: Vec<(&str, Vec<Vec<Symbol>>)> = vec![
        ("derived   ", first.words.iter().cloned().collect()),
        ("absent    ", vec![word("W"), word("Z"), word("AB")]),
        ("present   ", vec![word("x"), word("z"), word("ab")]),
        (
            "five cuts ",
            vec![word("x"), word("y"), word("z"), word("w"), word("k")],
        ),
    ];
    println!("\n== the foil, on the batch pass two reads ==");
    for (name, words) in foils {
        let grain = origin.with_all(words.clone()).expect("non-empty words");
        let pass = read(&grain, &batch(BATCH_C)).expect("readable");
        let left = population(&pass);
        println!(
            "  {name} {:?} -> {} pair(s) over {} parts, and the pairs are {left:?}",
            words.iter().map(|w| render_word(w)).collect::<Vec<_>>(),
            left.len(),
            pass.parts().len(),
        );
    }

    let words: BTreeSet<String> = first
        .words
        .union(&second.words)
        .map(|word| render_word(word))
        .collect();
    println!(
        "\nthe lineage's whole answer, in words rather than in a figure: {words:?}\nfrom {} codec \
         versions across two revisions, every one of them parented.",
        body.codec_population()
    );
}
