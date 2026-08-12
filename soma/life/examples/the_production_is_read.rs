//! **Read the production. Not its census — the text it emitted.**
//!
//! `CLAUDE.md` §9: *"A generated proof, text, image, classification, or obstruction must itself be
//! returned and inspected. Counts, morphology totals, atlases, and diagnostics are supporting
//! receipts and never substitutes."*
//!
//! `the_deposit_licenses_the_re_emission` establishes that the conducted population is strictly
//! smaller than the complete fiber, that each attached continuation names its licensing deposits,
//! and that ablation removes exactly what a deposit solely licensed. Every one of those is a
//! **count**. It deposits no emitted surface anywhere, and two readers verified its figures twice
//! without once asking what the machine said. This driver asks.
//!
//! It re-runs both arms on the same declared family and prints, verbatim:
//!
//! 1. the complete continuation fiber's emissions, to the declared depth;
//! 2. the conducted emissions, each with the distinct-source count its support carries;
//! 3. the population the deposits **withheld** — retained standing, never emitted;
//! 4. the obstructions, with their addresses.
//!
//! It asserts nothing. It is a reading, and its whole purpose is that a person can look at what
//! this body produces and judge it.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::BufReader,
    path::PathBuf,
};

use body::num::Cog;
use holonic_engine::hardware_cover::HardwareCover;
use life::{
    morphological_language::{
        CudaMorphologicalConductExecutor, MorphologicalConductPlurality, MorphologicalConductState,
        MorphologicalGenerationSpec, MorphologicalLanguageConductState,
        MorphologicalLanguageEcology, MorphologicalLanguagePassage, MorphologicalSupportConduct,
    },
    text_material::{ExactTextMaterialAtlas, TextMaterialRole},
};
use soma_abi::active::ActionCurrent;

const DECLARED_FAMILY: &[&str] = &[
    "papers/source/mathematics/definitions/receiver-indexed-holonic-system.typ",
    "papers/source/mathematics/definitions/holonic-process-double-category.typ",
    "papers/source/mathematics/definitions/receiver-configuration-calculus.typ",
    "papers/source/mathematics/definitions/contextual-tangle-compression.typ",
];

const DECLARED_PROMPT: &str =
    "How does training condition morphology while unresolved uncertainty remains open?";

/// How many emissions of the complete fiber to print. The complete fiber is a real object and is
/// often large; this bounds the **printing**, is stated as a caller's declaration, and is reported
/// beside the population so a reader always knows what was elided.
const PRINTED_COMPLETE_EMISSIONS: usize = 12;

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut corpus_form: Option<PathBuf> = None;
    let mut prompt = DECLARED_PROMPT.to_owned();
    let mut arguments = std::env::args().skip(1);
    while let Some(flag) = arguments.next() {
        let value = arguments
            .next()
            .ok_or_else(|| format!("{flag} carries no value"))?;
        match flag.as_str() {
            "--corpus-form" => corpus_form = Some(PathBuf::from(value)),
            "--prompt" => prompt = value,
            other => return Err(format!("unknown argument {other}")),
        }
    }
    let corpus_form =
        corpus_form.ok_or_else(|| "--corpus-form <sealed corpus rest> is required".to_owned())?;

    let corpus_file = File::open(&corpus_form).map_err(|error| format!("open corpus: {error}"))?;
    let atlas = ExactTextMaterialAtlas::from_native_reader(BufReader::new(corpus_file))
        .map_err(|error| format!("mount corpus: {error:?}"))?;

    let mut passages = Vec::new();
    for occurrence in atlas.corpus().occurrences() {
        if occurrence.role != TextMaterialRole::Document {
            continue;
        }
        let Some(declared) = DECLARED_FAMILY.iter().find(|declared| {
            occurrence.witnesses.iter().any(|witness| {
                witness.container == **declared
                    || witness.container.ends_with(&format!("/{declared}"))
            })
        }) else {
            continue;
        };
        passages.push(MorphologicalLanguagePassage::new(
            format!("{declared}#{}", occurrence.ordinal),
            (*declared).to_owned(),
            occurrence.receiver(),
            occurrence.text.clone(),
        ));
    }
    drop(atlas);
    if passages.is_empty() {
        return Err("the sealed corpus carries no occurrence of the declared family".to_owned());
    }

    let action =
        ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "action current is dark".to_owned())?;
    let workers = std::thread::available_parallelism()
        .map(|workers| workers.get())
        .unwrap_or(1);
    let ecology = MorphologicalLanguageEcology::condition(&passages, action, workers)
        .map_err(|error| format!("condition: {error:?}"))?;

    let spec = MorphologicalGenerationSpec {
        maximum_observed_tokens: 2,
    };
    let cover = HardwareCover::host_only();

    println!("PROMPT");
    println!("  {prompt}");
    println!();

    // --- the complete fiber, as text ------------------------------------------------------------
    let complete = ecology
        .generate_currents_over(&prompt, spec, &cover)
        .map_err(|error| format!("enumerate the complete fiber: {error:?}"))?;
    println!(
        "THE COMPLETE CONTINUATION FIBER — {} emissions, printing {}",
        complete.outputs.len(),
        PRINTED_COMPLETE_EMISSIONS.min(complete.outputs.len())
    );
    println!("  (this is what the body returned before a deposit decided anything)");
    for (at, output) in complete
        .outputs
        .iter()
        .take(PRINTED_COMPLETE_EMISSIONS)
        .enumerate()
    {
        println!("  [{at:>3}] {:?}", output.text);
    }
    if complete.outputs.len() > PRINTED_COMPLETE_EMISSIONS {
        println!(
            "  … {} further emissions not printed",
            complete.outputs.len() - PRINTED_COMPLETE_EMISSIONS
        );
    }
    println!();

    // --- the deposits -----------------------------------------------------------------------
    let atlas = ecology
        .conduct_atlas()
        .map_err(|error| format!("found the conduct atlas: {error:?}"))?;
    let plurality = MorphologicalConductPlurality::recurrence_across_two_distinct_wholes();
    let MorphologicalConductState::Conducting(morphology) = atlas
        .into_state(&plurality)
        .map_err(|error| format!("condense: {error}"))?
    else {
        return Err("no transport in this family returned through two distinct sources".to_owned());
    };
    let deposits = morphology.deposit_count();

    let MorphologicalLanguageConductState::Conducting(conducting) =
        ecology.receive_conduct(MorphologicalConductState::Conducting(morphology))
    else {
        return Err("a conducting morphology did not produce a conducting ecology".to_owned());
    };
    let mut executor = CudaMorphologicalConductExecutor::new(0)
        .map_err(|error| format!("mount the card: {error}"))?;
    let conducted = conducting
        .generate_currents_over(&prompt, spec, &cover, &mut executor)
        .map_err(|error| format!("conduct the generation: {error:?}"))?;

    println!(
        "WHAT THE DEPOSITS CONDUCT — {} emissions from {deposits} deposits, on {}",
        conducted.generation.outputs.len(),
        executor.device_name()
    );
    println!("  (a continuation is emitted only where its support recurred across distinct wholes)");
    let mut by_breadth: BTreeMap<usize, Vec<&str>> = BTreeMap::new();
    for output in &conducted.generation.outputs {
        by_breadth
            .entry(output.supporting_sources)
            .or_default()
            .push(output.text.as_str());
    }
    for (at, output) in conducted.generation.outputs.iter().enumerate() {
        let conduct = match output.support_conduct {
            MorphologicalSupportConduct::Recurred => "recurred",
            _ => "open",
        };
        println!(
            "  [{at:>3}] sources {:>2} · {conduct:<8} {:?}",
            output.supporting_sources, output.text
        );
    }
    println!();
    println!("  by distinct-source breadth:");
    for (breadth, texts) in &by_breadth {
        println!("    {breadth:>2} sources · {} emissions", texts.len());
    }
    println!();

    // --- what was withheld ----------------------------------------------------------------------
    let emitted = conducted
        .generation
        .outputs
        .iter()
        .map(|output| output.text.as_str())
        .collect::<BTreeSet<_>>();
    let withheld = complete
        .outputs
        .iter()
        .filter(|output| !emitted.contains(output.text.as_str()))
        .collect::<Vec<_>>();
    println!(
        "WHAT THE DEPOSITS WITHHELD — {} emissions retained as standing, never emitted",
        withheld.len()
    );
    println!("  (retained fiber: reachable terrain that no deposit licensed)");
    for output in withheld.iter().take(PRINTED_COMPLETE_EMISSIONS) {
        println!("    {:?}", output.text);
    }
    if withheld.len() > PRINTED_COMPLETE_EMISSIONS {
        println!(
            "    … {} further withheld emissions not printed",
            withheld.len() - PRINTED_COMPLETE_EMISSIONS
        );
    }

    Ok(())
}
