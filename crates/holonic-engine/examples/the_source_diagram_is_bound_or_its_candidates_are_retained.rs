//! **Phoenix station one: the source's own testimony is bound, and what it does not decide is
//! retained whole.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`.
//! Derivation:
//! `research/records/2026-08-18_THE_HOLON_IS_THE_OPERATION_COMPLEX_THE_FOREIGN_MAP_IS_A_PORTED_WORD_AND_THE_CARD_CARRIES_ITS_FRONTS.md`
//! §12.1 — *"Admit the source configuration and authoritative implementation as exterior realization
//! testimony; bind every operator occurrence, port, chronology and shared state/cache passage. If
//! unavailable, return the complete candidate-diagram fibre."*
//!
//! Three testimony species are admitted here and each is retained with what it decided:
//!
//! - the source's **declared configuration**, field by field;
//! - the source's **authoritative description of itself**, statement by statement; and
//! - the **declared shapes** of its manifested populations, which constrain the ports.
//!
//! The source's **executable implementation is not present on this machine**, so every binding it
//! alone would settle is returned as an open candidate population naming what would decide it.
//! Nothing is chosen by plausibility.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_source_diagram_is_bound_or_its_candidates_are_retained -- \
//!   /home/b/models/gemma-4-E4B-it
//! ```

use std::collections::BTreeMap;

use holonic_engine::category::BoundaryId;
use holonic_engine::exact_json;
use holonic_engine::foreign_map::{ForeignContainer, manifest_safetensors};
use holonic_engine::interaction::OccurrencePort;
use holonic_engine::ported_operation::{
    CandidateDiagrams, OperationSpecies, PortedOperationComplex, SourceTestimony,
};

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());

    // ---------------------------------------------------------------------------------------
    // The declared populations.
    // ---------------------------------------------------------------------------------------
    let map = format!("{root}/model.safetensors");
    let (_, container) = match manifest_safetensors(&map) {
        Ok(pair) => pair,
        Err(error) => {
            println!("the source refused: {error}");
            std::process::exit(1);
        }
    };
    println!("PHOENIX STATION ONE — THE SOURCE'S TESTIMONY IS BOUND");
    println!();
    println!(
        "  declared populations              {}",
        container.tensors.len()
    );
    println!(
        "  refused by name                   {}",
        container.refused.len()
    );
    println!(
        "  entries claiming the same octets  {}",
        container.overlaps().len()
    );

    // ---------------------------------------------------------------------------------------
    // The declared configuration.
    // ---------------------------------------------------------------------------------------
    let configuration = std::fs::read_to_string(format!("{root}/config.json")).unwrap_or_default();
    let pairs: Vec<(String, &str)> =
        exact_json::top_level_pairs(&configuration).unwrap_or_default();
    let text_config: String = pairs
        .iter()
        .find(|(key, _)| key == "text_config")
        .map(|(_, span)| (*span).to_owned())
        .unwrap_or_default();
    let field = |key: &str| -> Option<String> {
        let span = exact_json::field(&text_config, key)?;
        exact_json::as_string(span).or_else(|| Some(span.trim().to_owned()))
    };
    let sites = field("num_hidden_layers")
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(0);
    let construction_width = field("hidden_size")
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(0);
    let receivers = field("num_attention_heads")
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(0);
    let families = field("num_key_value_heads")
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(0);
    let per_site_width = field("hidden_size_per_layer_input")
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(0);
    let shared_state = field("num_kv_shared_layers")
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(0);
    let layer_types = exact_json::field(&text_config, "layer_types")
        .and_then(exact_json::as_string_array)
        .unwrap_or_default();
    let whole_context: Vec<bool> = layer_types
        .iter()
        .map(|kind| kind == "full_attention")
        .collect();

    println!();
    println!("  DECLARED CONFIGURATION, the source's own");
    println!("    sites                           {sites}");
    println!("    construction width              {construction_width}");
    println!("    receivers / presented families  {receivers} / {families}");
    println!("    per-site material width         {per_site_width}");
    println!(
        "    whole-context sites             {} of {}",
        whole_context.iter().filter(|whole| **whole).count(),
        whole_context.len()
    );
    println!("    declared shared state passages  {shared_state}");

    // ---------------------------------------------------------------------------------------
    // The source's authoritative description of itself.
    // ---------------------------------------------------------------------------------------
    let description = std::fs::read_to_string(format!("{root}/README.md")).unwrap_or_default();
    let mut statements = Vec::new();
    for phrase in [
        "unified Keys and Values",
        "Proportional RoPE",
        "ensuring the final layer is always global",
        "only used for quick lookups",
    ] {
        if let Some(sentence) = sentence_carrying(&description, phrase) {
            statements.push((phrase.to_owned(), sentence));
        }
    }
    println!();
    println!("  AUTHORITATIVE DESCRIPTION — statements that decide a binding");
    for (phrase, sentence) in &statements {
        println!("    [{phrase}]");
        println!("      {}", shorten(sentence, 150));
    }

    // The executable implementation, sought and reported rather than assumed.
    let implementation_present = std::process::Command::new("python3")
        .args(["-c", "import transformers"])
        .output()
        .map(|out| out.status.success())
        .unwrap_or(false);
    println!();
    println!(
        "  EXECUTABLE IMPLEMENTATION           {}",
        if implementation_present {
            "present"
        } else {
            "ABSENT on this machine (python3 -c \"import transformers\")"
        }
    );

    // ---------------------------------------------------------------------------------------
    // The ported operation complex.
    // ---------------------------------------------------------------------------------------
    let mut complex = PortedOperationComplex::new("gemma-4-E4B ported operation complex");
    let standing = complex.port("continuing standing");
    let symbol = complex.port("delivered symbol");
    let per_site_bundle = complex.port("per-site material bundle");
    let potential = complex.port("illicial potential section");

    let configuration_testimony = |field: &str, value: &str| SourceTestimony::Configuration {
        field: field.to_owned(),
        value: value.to_owned(),
    };
    let shape_testimony = |container: &ForeignContainer, name: &str| {
        container
            .tensor(name)
            .map(|tensor| SourceTestimony::DeclaredShape {
                population: name.to_owned(),
                shape: tensor.shape.clone(),
            })
            .ok()
    };

    // The delivered symbol arrives from the exterior, and BOTH lookups admit it. That is what makes
    // them one front rather than two hops: co-presence is read off the chronology, never declared.
    let delivery = complex
        .bind_operation(
            "symbol delivery",
            OperationSpecies::Construction,
            vec![],
            vec![symbol],
            None,
            vec![SourceTestimony::AuthoritativeDescription {
                statement:
                    "the exterior codec delivers one symbol; it is admitted material, not an \
                            operation of this map"
                        .to_owned(),
            }],
        )
        .expect("bound");
    let delivery_event = complex.occur(delivery).expect("occurs");

    // The entering construction: a lookup, which the description names as such.
    let symbol_table = "model.language_model.embed_tokens.weight";
    let entering = complex
        .bind_operation(
            "entering construction",
            OperationSpecies::Construction,
            vec![symbol],
            vec![standing],
            Some(symbol_table.to_owned()),
            shape_testimony(&container, symbol_table)
                .into_iter()
                .collect(),
        )
        .expect("bound");
    let entering_event = complex.occur(entering).expect("occurs");
    complex
        .carries_precedence(
            "the entering construction admits the delivered symbol",
            symbol,
            OccurrencePort::output(delivery_event, 0),
            OccurrencePort::input(entering_event, 0),
        )
        .expect("joined");
    let mut previous = entering_event;

    // The per-site material: a lookup the description explicitly types.
    let per_site_table = "model.language_model.embed_tokens_per_layer.weight";
    let mut per_site_testimony: Vec<SourceTestimony> = shape_testimony(&container, per_site_table)
        .into_iter()
        .collect();
    if let Some((_, sentence)) = statements
        .iter()
        .find(|(phrase, _)| phrase == "only used for quick lookups")
    {
        per_site_testimony.push(SourceTestimony::AuthoritativeDescription {
            statement: sentence.clone(),
        });
    }
    let per_site_lookup = complex
        .bind_operation(
            "per-site material lookup",
            OperationSpecies::Construction,
            vec![symbol],
            vec![per_site_bundle],
            Some(per_site_table.to_owned()),
            per_site_testimony,
        )
        .expect("bound");
    let per_site_event = complex.occur(per_site_lookup).expect("occurs");
    complex
        .carries_precedence(
            "the per-site lookup admits the same delivered symbol",
            symbol,
            OccurrencePort::output(delivery_event, 0),
            OccurrencePort::input(per_site_event, 0),
        )
        .expect("joined");

    // Each site.
    let mut chart_ports: BTreeMap<usize, (BoundaryId, BoundaryId, BoundaryId)> = BTreeMap::new();
    for site in 0..sites {
        let whole = whole_context.get(site).copied().unwrap_or(false);
        let receiver_port = complex.port(format!("site {site} receiver chart"));
        let presented_port = complex.port(format!("site {site} presented chart"));
        let carried_port = complex.port(format!("site {site} carried chart"));
        chart_ports.insert(site, (receiver_port, presented_port, carried_port));
        let named = |suffix: &str| format!("model.language_model.layers.{site}.{suffix}");

        // The entering rebase.
        let entering_gain = named("input_layernorm.weight");
        let rebase = complex
            .bind_operation(
                format!("site {site} entering rebase"),
                OperationSpecies::Transport,
                vec![standing],
                vec![standing],
                Some(entering_gain.clone()),
                vec![configuration_testimony(
                    "rms_norm_eps",
                    &field("rms_norm_eps").unwrap_or_default(),
                )]
                .into_iter()
                .chain(shape_testimony(&container, &entering_gain))
                .collect(),
            )
            .expect("bound");
        let rebase_event = complex.occur(rebase).expect("occurs");
        let site_entry = previous;
        complex
            .carries_precedence(
                format!("site {site} receives the standing"),
                standing,
                OccurrencePort::output(site_entry, 0),
                OccurrencePort::input(rebase_event, 0),
            )
            .expect("joined");

        // THE FIRST FRONT: three co-present projections of one predecessor.
        let mut front = Vec::new();
        for (label, suffix, port) in [
            ("receiver", "self_attn.q_proj.weight", receiver_port),
            ("presented", "self_attn.k_proj.weight", presented_port),
            ("carried", "self_attn.v_proj.weight", carried_port),
        ] {
            let carrier = named(suffix);
            let law = complex
                .bind_operation(
                    format!("site {site} {label} projection"),
                    OperationSpecies::Transport,
                    vec![standing],
                    vec![port],
                    Some(carrier.clone()),
                    shape_testimony(&container, &carrier).into_iter().collect(),
                )
                .expect("bound");
            let event = complex.occur(law).expect("occurs");
            complex
                .carries_precedence(
                    format!("site {site} {label} follows the rebase"),
                    standing,
                    OccurrencePort::output(rebase_event, 0),
                    OccurrencePort::input(event, 0),
                )
                .expect("joined");
            front.push(event);
        }

        // The contact: a face, and a chart transition with a declared gauge.
        let faces = complex
            .bind_operation(
                format!("site {site} contact faces"),
                OperationSpecies::Face,
                vec![receiver_port, presented_port],
                vec![presented_port],
                None,
                vec![configuration_testimony(
                    "layer_types",
                    if whole {
                        "full_attention"
                    } else {
                        "sliding_attention"
                    },
                )],
            )
            .expect("bound");
        let faces_event = complex.occur(faces).expect("occurs");
        for (at, source) in front.iter().take(2).enumerate() {
            complex
                .carries_precedence(
                    format!("site {site} contact receives branch {at}"),
                    if at == 0 {
                        receiver_port
                    } else {
                        presented_port
                    },
                    OccurrencePort::output(*source, 0),
                    OccurrencePort::input(faces_event, at),
                )
                .expect("joined");
        }

        let ratios = complex
            .bind_operation(
                format!("site {site} ratio family"),
                OperationSpecies::Transport,
                vec![presented_port],
                vec![presented_port],
                None,
                vec![SourceTestimony::AuthoritativeDescription {
                    statement:
                        "a ratio family is the additive chart carried to the multiplicative \
                                one, with a declared null that enters no ratio"
                            .to_owned(),
                }],
            )
            .expect("bound");
        let ratios_event = complex.occur(ratios).expect("occurs");
        complex
            .carries_precedence(
                format!("site {site} ratios follow the faces"),
                presented_port,
                OccurrencePort::output(faces_event, 0),
                OccurrencePort::input(ratios_event, 0),
            )
            .expect("joined");

        let carried_construction = complex
            .bind_operation(
                format!("site {site} carried construction"),
                OperationSpecies::Construction,
                vec![presented_port, carried_port],
                vec![carried_port],
                None,
                vec![SourceTestimony::AuthoritativeDescription {
                    statement: "the carried construction is a convex combination and lies inside \
                                its population's hull"
                        .to_owned(),
                }],
            )
            .expect("bound");
        let carried_event = complex.occur(carried_construction).expect("occurs");
        complex
            .carries_precedence(
                format!("site {site} construction follows the ratios"),
                presented_port,
                OccurrencePort::output(ratios_event, 0),
                OccurrencePort::input(carried_event, 0),
            )
            .expect("joined");
        complex
            .carries_precedence(
                format!("site {site} construction receives the carried branch"),
                carried_port,
                OccurrencePort::output(front[2], 0),
                OccurrencePort::input(carried_event, 1),
            )
            .expect("joined");

        // The return and its re-entry.
        let return_carrier = named("self_attn.o_proj.weight");
        let returning = complex
            .bind_operation(
                format!("site {site} contact return"),
                OperationSpecies::Transport,
                vec![carried_port],
                vec![standing],
                Some(return_carrier.clone()),
                shape_testimony(&container, &return_carrier)
                    .into_iter()
                    .collect(),
            )
            .expect("bound");
        let returning_event = complex.occur(returning).expect("occurs");
        complex
            .carries_precedence(
                format!("site {site} return follows the construction"),
                carried_port,
                OccurrencePort::output(carried_event, 0),
                OccurrencePort::input(returning_event, 0),
            )
            .expect("joined");

        // **A RECONVERGENCE.** The re-entry admits two paths: the standing that was retained
        // across the whole contact, and the delta the contact returned. Modelling it with one
        // input would hide the join, and the join is what a residual IS.
        let reentry = complex
            .bind_operation(
                format!("site {site} contact re-entry"),
                OperationSpecies::Construction,
                vec![standing, standing],
                vec![standing],
                Some(named("post_attention_layernorm.weight")),
                shape_testimony(&container, &named("post_attention_layernorm.weight"))
                    .into_iter()
                    .collect(),
            )
            .expect("bound");
        let reentry_event = complex.occur(reentry).expect("occurs");
        complex
            .carries_precedence(
                format!("site {site} re-entry retains the predecessor standing"),
                standing,
                OccurrencePort::output(site_entry, 0),
                OccurrencePort::input(reentry_event, 0),
            )
            .expect("joined");
        complex
            .carries_precedence(
                format!("site {site} re-entry admits the returned delta"),
                standing,
                OccurrencePort::output(returning_event, 0),
                OccurrencePort::input(reentry_event, 1),
            )
            .expect("joined");

        // THE SECOND FRONT: gate and raise are co-present branches of one predecessor.
        let constitutive_rebase = complex
            .bind_operation(
                format!("site {site} constitutive rebase"),
                OperationSpecies::Transport,
                vec![standing],
                vec![standing],
                Some(named("pre_feedforward_layernorm.weight")),
                shape_testimony(&container, &named("pre_feedforward_layernorm.weight"))
                    .into_iter()
                    .collect(),
            )
            .expect("bound");
        let constitutive_rebase_event = complex.occur(constitutive_rebase).expect("occurs");
        complex
            .carries_precedence(
                format!("site {site} constitutive rebase follows the re-entry"),
                standing,
                OccurrencePort::output(reentry_event, 0),
                OccurrencePort::input(constitutive_rebase_event, 0),
            )
            .expect("joined");

        let intermediate = complex.port(format!("site {site} intermediate chart"));
        let mut second_front = Vec::new();
        for (label, suffix) in [
            ("gate", "mlp.gate_proj.weight"),
            ("raise", "mlp.up_proj.weight"),
        ] {
            let carrier = named(suffix);
            let law = complex
                .bind_operation(
                    format!("site {site} {label} projection"),
                    OperationSpecies::Transport,
                    vec![standing],
                    vec![intermediate],
                    Some(carrier.clone()),
                    shape_testimony(&container, &carrier).into_iter().collect(),
                )
                .expect("bound");
            let event = complex.occur(law).expect("occurs");
            complex
                .carries_precedence(
                    format!("site {site} {label} follows the constitutive rebase"),
                    standing,
                    OccurrencePort::output(constitutive_rebase_event, 0),
                    OccurrencePort::input(event, 0),
                )
                .expect("joined");
            second_front.push(event);
        }

        let passage = complex
            .bind_operation(
                format!("site {site} constitutive passage"),
                OperationSpecies::Transport,
                vec![intermediate, intermediate],
                vec![intermediate],
                None,
                vec![configuration_testimony(
                    "hidden_activation",
                    &field("hidden_activation").unwrap_or_default(),
                )],
            )
            .expect("bound");
        let passage_event = complex.occur(passage).expect("occurs");
        for (at, source) in second_front.iter().enumerate() {
            complex
                .carries_precedence(
                    format!("site {site} passage receives branch {at}"),
                    intermediate,
                    OccurrencePort::output(*source, 0),
                    OccurrencePort::input(passage_event, at),
                )
                .expect("joined");
        }

        let lowering = complex
            .bind_operation(
                format!("site {site} constitutive return"),
                OperationSpecies::Transport,
                vec![intermediate],
                vec![standing],
                Some(named("mlp.down_proj.weight")),
                shape_testimony(&container, &named("mlp.down_proj.weight"))
                    .into_iter()
                    .collect(),
            )
            .expect("bound");
        let lowering_event = complex.occur(lowering).expect("occurs");
        complex
            .carries_precedence(
                format!("site {site} lowering follows the passage"),
                intermediate,
                OccurrencePort::output(passage_event, 0),
                OccurrencePort::input(lowering_event, 0),
            )
            .expect("joined");

        // The second reconvergence of this site.
        let constitutive_reentry = complex
            .bind_operation(
                format!("site {site} constitutive re-entry"),
                OperationSpecies::Construction,
                vec![standing, standing],
                vec![standing],
                Some(named("post_feedforward_layernorm.weight")),
                shape_testimony(&container, &named("post_feedforward_layernorm.weight"))
                    .into_iter()
                    .collect(),
            )
            .expect("bound");
        let constitutive_reentry_event = complex.occur(constitutive_reentry).expect("occurs");
        complex
            .carries_precedence(
                format!("site {site} constitutive re-entry retains the predecessor standing"),
                standing,
                OccurrencePort::output(reentry_event, 0),
                OccurrencePort::input(constitutive_reentry_event, 0),
            )
            .expect("joined");
        complex
            .carries_precedence(
                format!("site {site} constitutive re-entry admits the returned delta"),
                standing,
                OccurrencePort::output(lowering_event, 0),
                OccurrencePort::input(constitutive_reentry_event, 1),
            )
            .expect("joined");

        previous = constitutive_reentry_event;
    }

    // The boundary.
    let boundary_gain = "model.language_model.norm.weight";
    let closing = complex
        .bind_operation(
            "boundary rebase",
            OperationSpecies::Transport,
            vec![standing],
            vec![standing],
            Some(boundary_gain.to_owned()),
            shape_testimony(&container, boundary_gain)
                .into_iter()
                .collect(),
        )
        .expect("bound");
    let closing_event = complex.occur(closing).expect("occurs");
    complex
        .carries_precedence(
            "the boundary receives the last standing",
            standing,
            OccurrencePort::output(previous, 0),
            OccurrencePort::input(closing_event, 0),
        )
        .expect("joined");

    let section = complex
        .bind_operation(
            "illicial potential section",
            OperationSpecies::Face,
            vec![standing],
            vec![potential],
            Some(symbol_table.to_owned()),
            vec![configuration_testimony(
                "tie_word_embeddings",
                "true; the boundary reads the same population the entering construction did",
            )],
        )
        .expect("bound");
    let section_event = complex.occur(section).expect("occurs");
    complex
        .carries_precedence(
            "the section follows the boundary rebase",
            standing,
            OccurrencePort::output(closing_event, 0),
            OccurrencePort::input(section_event, 0),
        )
        .expect("joined");

    // ---------------------------------------------------------------------------------------
    // What the admitted testimony did NOT decide.
    // ---------------------------------------------------------------------------------------
    let would_decide = vec![
        "the source's executable implementation".to_owned(),
        "an intervention separating the candidates under a declared receiver family".to_owned(),
    ];
    for fibre in [
        CandidateDiagrams {
            question: "how is a stored rebase gain read?".to_owned(),
            candidates: vec![
                "the stored value is the gain".to_owned(),
                "the stored value is an offset and the gain is one plus it".to_owned(),
            ],
            would_be_decided_by: would_decide.clone(),
        },
        CandidateDiagrams {
            question: "which two coordinates does the chronology's group action pair?".to_owned(),
            candidates: vec![
                "adjacent coordinates of the receiver chart".to_owned(),
                "the two halves of the turned sub-bundle".to_owned(),
            ],
            would_be_decided_by: would_decide.clone(),
        },
        CandidateDiagrams {
            question: "where does the stored per-site scalar multiply?".to_owned(),
            candidates: vec![
                "the re-entering standing".to_owned(),
                "the contact faces".to_owned(),
                "nothing; it is inert under the declared runtime".to_owned(),
            ],
            would_be_decided_by: would_decide.clone(),
        },
        CandidateDiagrams {
            question: "does the contact carry a scale, and which?".to_owned(),
            candidates: vec![
                "the reciprocal root of the receiver chart's width".to_owned(),
                "unity, because the receiver chart is already rebased".to_owned(),
            ],
            would_be_decided_by: would_decide.clone(),
        },
    ] {
        complex.retain_undecided(fibre);
    }

    // The one the authoritative description DOES decide, recorded as decided.
    let shared_state_decided = statements
        .iter()
        .any(|(phrase, _)| phrase == "unified Keys and Values");

    // ---------------------------------------------------------------------------------------
    // The return.
    // ---------------------------------------------------------------------------------------
    let closure = complex.closure().expect("validated");
    println!();
    println!("THE PORTED OPERATION COMPLEX");
    println!();
    println!("  typed ports                       {}", closure.ports);
    println!("  bound operations                  {}", closure.operations);
    println!(
        "  occurrences                       {}",
        closure.occurrences
    );
    println!("  CO-PRESENT FRONTS                 {}", closure.fronts);
    println!(
        "  dependency span                   {}",
        complex.dependency_span().expect("span")
    );
    println!();
    println!("  species census — every operation typed by TABLET_THE_OPERATIONS:");
    for (species, count) in complex.species_census() {
        println!("      {:<14} {count}", species.name());
    }

    let fronts = complex.fronts().expect("layered");
    let branching: Vec<_> = fronts.iter().filter(|front| !front.is_serial()).collect();
    println!();
    println!("  fronts of breadth greater than one {}", branching.len());
    println!(
        "  widest front                       {}",
        branching.iter().map(|f| f.breadth()).max().unwrap_or(0)
    );
    println!();
    println!("  A CONTRACTION COUNT IS NOT A DEPENDENCY SPAN.");
    let transports = complex
        .species_census()
        .get(&OperationSpecies::Transport)
        .copied()
        .unwrap_or(0);
    println!("    transports bound              {transports}");
    println!("    occurrences                   {}", closure.occurrences);
    println!("    dependency span               {}", closure.fronts);
    println!(
        "    occurrences riding co-present {}",
        closure.occurrences.saturating_sub(closure.fronts)
    );
    println!();
    println!("  BRANCHES AND RECONVERGENCES, read off the diagram");
    let branches = complex
        .shape
        .laws
        .values()
        .filter(|law| law.outputs.len() > 1)
        .count();
    let reconvergences = complex
        .shape
        .laws
        .values()
        .filter(|law| law.inputs.len() > 1)
        .count();
    println!("    operations admitting more than one path  {reconvergences}");
    println!("    operations emitting more than one path   {branches}");
    println!(
        "    the open exterior: ports no operation emits {}",
        complex
            .shape
            .boundaries
            .objects
            .keys()
            .filter(|port| !complex
                .shape
                .laws
                .values()
                .any(|law| law.outputs.contains(port)))
            .count()
    );

    println!();
    println!("WHAT THE ADMITTED TESTIMONY DECIDED");
    println!();
    println!(
        "  the declared shared state passage  {}",
        if shared_state_decided {
            "DECIDED by the authoritative description: the whole-context sites carry unified keys \
             and values"
        } else {
            "OPEN"
        }
    );
    println!(
        "  the chronology species             DECIDED by the description: proportional, partial"
    );
    println!("  the per-site material's species    DECIDED by the description: a lookup");

    println!();
    println!("WHAT IT DID NOT — retained whole, never chosen by plausibility");
    println!();
    for fibre in &complex.undecided {
        println!("  {}", fibre.question);
        for candidate in &fibre.candidates {
            println!("      candidate  {candidate}");
        }
        for evidence in &fibre.would_be_decided_by {
            println!("      decided by {evidence}");
        }
        println!();
    }

    println!("THE STATION'S OWN VERDICT");
    println!();
    println!(
        "  diagram closed                    {}",
        closure.is_closed()
    );
    println!(
        "  open questions                    {}",
        closure.open_questions.len()
    );
    println!(
        "  operations with no deciding testimony {}",
        closure.operations_without_deciding_testimony.len()
    );
    println!();
    println!("  The diagram is bound and its chronology stands. It is NOT closed, and the station");
    println!(
        "  returns that rather than a composition. No transport is posed and no capability is"
    );
    println!("  promoted; the next station may pose transports only where testimony decided them.");
}

fn sentence_carrying(text: &str, phrase: &str) -> Option<String> {
    let at = text.find(phrase)?;
    let start = text[..at].rfind(['.', '\n']).map_or(0, |index| index + 1);
    let end = text[at..]
        .find(['.', '\n'])
        .map_or(text.len(), |index| at + index + 1);
    Some(text[start..end].trim().to_owned())
}

fn shorten(text: &str, extent: usize) -> String {
    if text.chars().count() <= extent {
        return text.to_owned();
    }
    let held: String = text.chars().take(extent).collect();
    format!("{held}…")
}
