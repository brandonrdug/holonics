//! Drive `codec_system`: recover an opaque tokenizer from testimony, read it as an
//! `ObservedSystem`, and cross-check the two independent routes to *the shortest input separating
//! two codecs* — against each other, and against three readings that are wrong on purpose.
//!
//! Nothing here is a hand-written table. The material is an [`OpaqueSymbolCodec`], a boxed
//! `dyn Fn(&str) -> Vec<String>` the driver can only call, and every codec below comes back out of
//! `codec_recovery::recover` from testimony over a declared query family.
//!
//! What is returned, in order:
//!
//! 1. the recovered structure — classes, emission, the boundary table, the gauge freedom;
//! 2. the reachable conduct states, each with the word that reaches it and what `segment` returns
//!    there, so the state population is exhibited and not counted;
//! 3. the Nerode congruence of that machine: one-shot blocks, conduct blocks, and every collapsed
//!    pair with the shortest word that separates it;
//! 4. the production cross-check on two really inequivalent codecs — both routes, both words, both
//!    segmentations, and a disagreement population that is **empty**;
//! 5. three declared wrong readings through the same shape, each returning a **non-empty**
//!    disagreement population with its species named and its word exhibited;
//! 6. the same return written out to octets and read back.
//!
//! `CLAUDE.md` §8 — *a law that returns zero proves nothing about itself*. Steps 4 and 5 are the
//! zero and the non-zero return of one law, on one material. §9 — *return the artifact*: counts
//! appear only beside the populations they count.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;

use holonic_engine::codec_recovery::{
    recover, Boundary, CodecRecovery, Obstruction, OpaqueSymbolCodec, RecoveredCodec, SymbolClass,
};
use holonic_engine::codec_system::{
    cross_check, cross_check_over, CodecIndexReceiver, CodecSystem, JointCarrier, JointReading,
    PushEventSystem, ReversedInputOrder, SeparationCrossCheck, StepReturn, ThePushEventAutomaton,
    TheJointAutomaton, CROSS_CHECK_SCHEMA,
};
use holonic_engine::receiver_exact_compression::{compress, InputId, ItemId, ObservedSystem};

/// The opaque target. A character-class state machine written as a state machine, never as a table:
/// word characters agglutinate, digits agglutinate only with each other, whitespace is dropped and
/// flushes, `.`/`-` are a run class, `,`/`;` are a solo class. The recovery is told the alphabet and
/// nothing else.
fn tokenizer() -> OpaqueSymbolCodec {
    OpaqueSymbolCodec::new(|input: &str| {
        #[derive(Clone, Copy, PartialEq)]
        enum Kind {
            Word,
            Digit,
            Space,
            Run,
            Solo,
        }
        fn kind(symbol: char) -> Kind {
            match symbol {
                'a' | 'b' | 'q' => Kind::Word,
                '0' | '1' => Kind::Digit,
                ' ' | '\t' => Kind::Space,
                '.' | '-' => Kind::Run,
                _ => Kind::Solo,
            }
        }
        let mut tokens = Vec::new();
        let mut current = String::new();
        let mut previous: Option<Kind> = None;
        for symbol in input.chars() {
            let here = kind(symbol);
            let cut = match previous {
                None => true,
                Some(before) => {
                    before != here || !matches!(here, Kind::Word | Kind::Digit | Kind::Run)
                }
            };
            if cut && !current.is_empty() {
                tokens.push(std::mem::take(&mut current));
            }
            if here != Kind::Space {
                current.push(symbol);
            }
            previous = Some(here);
        }
        if !current.is_empty() {
            tokens.push(current);
        }
        tokens
    })
}

const TOKENIZER_ALPHABET: [char; 11] = ['a', 'b', 'q', '0', '1', ' ', '\t', '.', '-', ',', ';'];

/// A second opaque target whose dropped symbol **joins**: `"a_b"` is one token. At radius two the
/// declared family provably cannot see through it, and the recovery returns two genuinely
/// inequivalent codecs together with the word it was not allowed to ask.
fn soft_join() -> OpaqueSymbolCodec {
    OpaqueSymbolCodec::new(|input: &str| {
        let token: String = input.chars().filter(|symbol| *symbol != '_').collect();
        if token.is_empty() {
            Vec::new()
        } else {
            vec![token]
        }
    })
}

/// Flip one boundary entry. Every codec compared below is either recovered or one recovered codec
/// with named entries flipped, so the population stays material rather than becoming a fixture.
fn flipped(codec: &RecoveredCodec, left: usize, right: usize) -> RecoveredCodec {
    let mut variant = codec.clone();
    variant.boundary[left][right] = match variant.boundary[left][right] {
        Boundary::Join => Boundary::Cut,
        Boundary::Cut => Boundary::Join,
    };
    variant
}

fn spell(symbol: char) -> String {
    match symbol {
        ' ' => "␠".to_owned(),
        '\t' => "␉".to_owned(),
        other => other.to_string(),
    }
}

fn spell_word(word: &str) -> String {
    word.chars().map(spell).collect()
}

fn spell_class(codec: &RecoveredCodec, class: SymbolClass) -> String {
    codec.classes[class.0 as usize]
        .iter()
        .map(|symbol| spell(*symbol))
        .collect::<Vec<String>>()
        .join("")
}

fn show_recovery(recovery: &CodecRecovery, label: &str) {
    let codec = recovery.codec.as_ref().expect("the codec is recovered");
    println!("== the recovered structure: {label} ==");
    println!(
        "  alphabet {}  radius {}  family {} words  target calls {}",
        spell_word(&recovery.alphabet.iter().collect::<String>()),
        recovery.radius,
        recovery.work.declared_family_words,
        recovery.work.target_calls,
    );
    for (index, block) in codec.classes.iter().enumerate() {
        println!(
            "  class {index}: {{{}}}  {:?}",
            block
                .iter()
                .map(|symbol| spell(*symbol))
                .collect::<Vec<String>>()
                .join(" "),
            codec.emission[index],
        );
    }
    println!("  boundary (rows = previous class, columns = this class)");
    for (left, row) in codec.boundary.iter().enumerate() {
        let cells: Vec<&str> = row
            .iter()
            .map(|entry| match entry {
                Boundary::Join => "join",
                Boundary::Cut => "cut ",
            })
            .collect();
        println!("    {left} | {}", cells.join(" "));
    }
    if recovery.gauge_freedom.is_empty() {
        println!("  gauge freedom: none — every entry is determined by the family");
    } else {
        let free: Vec<String> = recovery
            .gauge_freedom
            .iter()
            .map(|(left, right)| format!("({}->{})", left.0, right.0))
            .collect();
        println!(
            "  gauge freedom: {} entries, {} retained tables, all one codec — {}",
            recovery.gauge_freedom.len(),
            recovery.retained_tables,
            free.join(" "),
        );
    }
}

/// The shortest word over the class representatives that reaches each item, breadth-first from rest.
fn reaching_words(system: &CodecSystem<'_>) -> BTreeMap<ItemId, String> {
    let mut found: BTreeMap<ItemId, String> = BTreeMap::new();
    let rest = system.rest_state(0).expect("a system rests");
    let mut frontier = std::collections::VecDeque::from([(rest, Vec::<InputId>::new())]);
    found.insert(rest, String::new());
    while let Some((item, word)) = frontier.pop_front() {
        for input in system.inputs() {
            if let Some(next) = system.successor(item, input)
                && !found.contains_key(&next)
            {
                let mut extended = word.clone();
                extended.push(input);
                found.insert(
                    next,
                    system.word_string(&extended).expect("over the alphabet"),
                );
                frontier.push_back((next, extended));
            }
        }
    }
    found
}

/// The state population, exhibited: every reachable state with the word that reaches it, what the
/// codec's own `segment` returns there, and what each declared receiver sees.
fn show_states(codec: &RecoveredCodec, system: &CodecSystem<'_>) {
    println!("== the reachable conduct states ==");
    println!(
        "  {} states over {} symbol classes — the design's state space would have to hold them",
        system.states().len(),
        codec.classes.len(),
    );
    let words = reaching_words(system);
    println!("  item | reached by | previous class | open | returned | segment(word)");
    for (position, state) in system.states().iter().enumerate() {
        let item = ItemId(position as u64);
        let word = words.get(&item).expect("every state is reachable");
        let previous = match state.previous {
            None => "-".to_owned(),
            Some(class) => format!("{} {{{}}}", class.0, spell_class(codec, class)),
        };
        println!(
            "  {position:>4} | {:>10} | {previous:>14} | {:>4} | {:>8} | {:?}",
            if word.is_empty() {
                "(rest)".to_owned()
            } else {
                spell_word(word)
            },
            state.token_open,
            match state.last {
                StepReturn::Silent => "silent",
                StepReturn::OpenedToken => "opened",
                StepReturn::ExtendedToken => "extended",
            },
            codec.segment(word).expect("declared symbols only"),
        );
    }
}

/// The congruence, exhibited: both partitions and every collapsed pair with its word and witness.
fn show_congruence(codec: &RecoveredCodec, system: &CodecSystem<'_>) {
    let compression = compress(system);
    let words = reaching_words(system);
    let name = |item: ItemId| -> String {
        let word = words.get(&item).expect("every state is reachable");
        if word.is_empty() {
            "(rest)".to_owned()
        } else {
            spell_word(word)
        }
    };
    println!("== the Nerode congruence of that machine ==");
    println!(
        "  {} rounds to the fixed point; the one-shot reading over-collapses by {} blocks",
        compression.rounds,
        compression.refinement(),
    );
    println!("  one-shot blocks — what the receivers alone cannot tell apart");
    for block in &compression.one_shot.blocks {
        let members: Vec<String> = block.iter().map(|item| name(*item)).collect();
        println!("    {{{}}}", members.join(" "));
    }
    println!("  conduct blocks — what survives stepping");
    for block in &compression.conduct.blocks {
        let members: Vec<String> = block.iter().map(|item| name(*item)).collect();
        println!("    {{{}}}", members.join(" "));
    }
    println!(
        "  the exact loss — {} pairs the one-shot reading merged and conduct separates",
        compression.collapsed.len(),
    );
    if compression.collapsed.is_empty() {
        println!("    (EMPTY — the one-shot reading was already receiver-exact)");
    }
    for pair in &compression.collapsed {
        let word = system
            .word_string(&pair.distinguishing_word)
            .expect("over the alphabet");
        let how = match pair.witness {
            None => "a terminus one reaches and the other does not".to_owned(),
            Some((receiver, here, there)) => {
                format!("receiver {} returns {} against {}", receiver.0, here.0, there.0)
            }
        };
        println!(
            "    {:>10} | {:<10} after {:<6} — {how}",
            name(pair.left),
            name(pair.right),
            spell_word(&word),
        );
        // The artifact the pair is about, taken from `segment` and not from the adapter.
        let (here, there) = (name(pair.left), name(pair.right));
        for reached in [&here, &there] {
            if *reached == "(rest)" {
                continue;
            }
            let plain: String = words
                .values()
                .find(|candidate| spell_word(candidate) == *reached)
                .cloned()
                .unwrap_or_default();
            println!(
                "        segment({}{}) = {:?}",
                spell_word(&plain),
                spell_word(&word),
                codec
                    .segment(&format!("{plain}{word}"))
                    .expect("declared symbols only"),
            );
        }
    }
}

/// One cross-check, exhibited whole: which two readings ran, both words, both segmentations, and
/// the disagreement population — empty or not — with every species named.
fn show_cross_check(label: &str, check: &SeparationCrossCheck) {
    println!("-- {label}");
    println!(
        "     {} against {}",
        check.nerode_reading, check.joint_reading
    );
    let word = |named: &Option<String>| match named {
        None => "NONE — no input of any length separates them".to_owned(),
        Some(input) => format!("{:?} ({} symbols)", spell_word(input), input.chars().count()),
    };
    println!(
        "     congruence: {}",
        word(&check.nerode.as_ref().map(|(_, written)| written.clone())),
    );
    println!("     other route: {}", word(&check.joint_automaton));
    println!(
        "     rest states {:?} separated by the refinement: {}",
        (check.rest_states.0.0, check.rest_states.1.0),
        check.rest_states_separated,
    );
    for (source, returns) in [
        ("congruence", &check.nerode_returns),
        ("other route", &check.joint_automaton_returns),
    ] {
        if let Some((left, right)) = returns {
            println!(
                "     {source}'s word segments as {left:?} against {right:?} — {}",
                if left == right {
                    "IDENTICAL, so the word does not separate them"
                } else {
                    "different, so the word really separates them"
                },
            );
        }
    }
    if check.disagreements.is_empty() {
        println!("     disagreements: EMPTY");
    } else {
        println!("     disagreements: {} species", check.disagreements.len());
        for species in &check.disagreements {
            println!("       {species:?}");
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let target = tokenizer();
    let recovery = recover(&target, &TOKENIZER_ALPHABET, 3)?;
    show_recovery(&recovery, "an opaque tokenizer, from testimony alone");
    let codec = recovery.codec.as_ref().expect("the codec is recovered");

    println!();
    let system = CodecSystem::new(codec)?;
    show_states(codec, &system);

    println!();
    show_congruence(codec, &system);

    // The second target, at the radius that leaves it undetermined: two codecs a real recovery
    // retained and could not choose between, and the word it was not allowed to ask.
    println!();
    let blind = recover(&soft_join(), &['a', 'b', '_'], 2)?;
    let Some(Obstruction::UndeterminedCodec {
        left,
        right,
        separating_input,
        left_return,
        right_return,
    }) = blind.obstructions.first()
    else {
        return Err("radius two must leave the soft-join codec undetermined".into());
    };
    println!("== two codecs a real recovery could not choose between ==");
    println!(
        "  the family reached {} symbols; the word that would have decided is {:?} at {} symbols",
        blind.radius,
        spell_word(separating_input),
        separating_input.chars().count(),
    );
    println!("  left  returns {left_return:?}");
    println!("  right returns {right_return:?}");

    println!();
    println!("== the production cross-check: two routes, one quantity ==");
    show_cross_check(
        "the two inequivalent codecs the recovery exhibited",
        &cross_check(left, right)?,
    );

    let word = codec.class_of('a').ok_or("the word class is recovered")?;
    let digit = codec.class_of('0').ok_or("the digit class is recovered")?;
    let space = codec.class_of(' ').ok_or("the space class is recovered")?;
    let gauge = flipped(codec, word.0 as usize, space.0 as usize);
    let mut across = flipped(codec, word.0 as usize, space.0 as usize);
    across = flipped(&across, space.0 as usize, word.0 as usize);
    let mut twice = flipped(codec, word.0 as usize, word.0 as usize);
    twice = flipped(&twice, digit.0 as usize, digit.0 as usize);

    show_cross_check(
        "the tokenizer against a single gauge flip — observationally identical",
        &cross_check(codec, &gauge)?,
    );
    show_cross_check(
        "the tokenizer against a table that holds a token across a dropped symbol",
        &cross_check(codec, &across)?,
    );
    show_cross_check(
        "the tokenizer against two flipped determined entries",
        &cross_check(codec, &twice)?,
    );

    println!();
    println!("== the declared wrong readings — the non-zero return of the same law ==");
    println!(
        "  the two production routes are specification-equivalent, so the population above is\n  \
         empty for every well-formed input. These are wrong on purpose, each in one named way,\n  \
         and each runs through the same cross-check shape."
    );

    let mut produced: BTreeSet<String> = BTreeSet::new();
    let mut take = |label: &str, check: SeparationCrossCheck| -> Result<(), Box<dyn Error>> {
        show_cross_check(label, &check);
        if check.disagreements.is_empty() {
            return Err(format!("the control {label} returned nothing").into());
        }
        for species in &check.disagreements {
            produced.insert(format!("{species:?}"));
        }
        Ok(())
    };

    let shadow_gauge = PushEventSystem::joint(&[codec, &gauge])?;
    take(
        "PUSH-EVENT SHADOW on the congruence side, against a pair with no separator at all",
        cross_check_over(&shadow_gauge, &TheJointAutomaton, codec, &gauge)?,
    )?;
    let shadow_across = PushEventSystem::joint(&[codec, &across])?;
    take(
        "PUSH-EVENT SHADOW on the congruence side, against a pair that separates at three",
        cross_check_over(&shadow_across, &TheJointAutomaton, codec, &across)?,
    )?;
    let real_gauge = CodecSystem::joint(&[codec, &gauge])?;
    take(
        "PUSH-EVENT SHADOW in the other plug point, as the automaton",
        cross_check_over(&real_gauge, &ThePushEventAutomaton, codec, &gauge)?,
    )?;
    let real_twice = CodecSystem::joint(&[codec, &twice])?;
    take(
        "REVERSED INPUT ORDER — right about the quantity, different about the word",
        cross_check_over(
            &ReversedInputOrder {
                inner: &real_twice,
            },
            &TheJointAutomaton,
            codec,
            &twice,
        )?,
    )?;
    let real_self = CodecSystem::joint(&[codec, codec])?;
    take(
        "CODEC-INDEX RECEIVER — an absolute frame, against a codec and itself",
        cross_check_over(
            &CodecIndexReceiver { inner: &real_self },
            &TheJointAutomaton,
            codec,
            codec,
        )?,
    )?;

    println!();
    println!("  species produced by a declared control:");
    for species in &produced {
        println!("    {species}");
    }
    if produced.len() != 6 {
        return Err(format!(
            "six species are declared and {} were produced: {produced:?}",
            produced.len()
        )
        .into());
    }

    // The wrong readings must refuse exactly what the organ refuses, or a control could be
    // exercised on material the organ itself would not accept.
    let malformed = RecoveredCodec {
        schema: codec.schema.clone(),
        classes: codec.classes.clone(),
        emission: codec.emission.clone(),
        boundary: vec![vec![Boundary::Join]],
    };
    println!();
    println!("== what every reading refuses, on one malformed value ==");
    println!("  CodecSystem::joint      {:?}", CodecSystem::joint(&[&malformed]).err());
    println!("  PushEventSystem::joint  {:?}", PushEventSystem::joint(&[&malformed]).err());
    println!(
        "  joint automaton         {:?}",
        TheJointAutomaton
            .shortest_separating_input(codec, &malformed)
            .err()
    );
    println!(
        "  push-event automaton    {:?}",
        ThePushEventAutomaton
            .shortest_separating_input(codec, &malformed)
            .err()
    );
    println!(
        "  segment                 {:?}",
        malformed.segment("a").err()
    );
    let single = CodecSystem::new(codec)?;
    println!(
        "  a one-codec carrier     {:?}  (rest pair {:?})",
        cross_check_over(&single, &TheJointAutomaton, codec, codec)
            .map(|_| ())
            .err(),
        single.rest_pair(),
    );

    // The octets. A derived `Serialize` is a claim about a round trip and this is the material that
    // tests it.
    let check = cross_check(left, right)?;
    if check.schema != CROSS_CHECK_SCHEMA {
        return Err(format!("the return names {:?}", check.schema).into());
    }
    let written = ron::ser::to_string(&check)?;
    let read_back: SeparationCrossCheck = ron::from_str(&written)?;
    if read_back != check {
        return Err("the cross-check did not survive its own octets".into());
    }
    println!();
    println!("== the octets ==");
    println!("  schema {}", check.schema);
    println!(
        "  {} octets written and read back exactly, carrying {} collapsed pairs and the word {:?}",
        written.len(),
        read_back.compression.collapsed.len(),
        read_back
            .nerode
            .as_ref()
            .map(|(_, written)| spell_word(written)),
    );

    Ok(())
}
