//! Continuing physical reception on the notebook's already admitted KnownTruth chart.
//!
//! `executed physical-receive <A|B|one> <count> <aperture> <out> <pin> <terrain>=<seed>…`
//! is a prequential law diagnostic, with no unseen or useful-language claim. Each blind damaged
//! section is received on the contemporary material and preceding physical carry. Its whole
//! receipt is published before a comparison observes only its intact stations. The next section
//! consumes the successor. No pair location, authored relation, reference repair or erased target
//! enters the receiver. The identity chart is the terrain owner's KnownTruth chart; arbitrary
//! external bytes still require their founded encoding and admitted clock/decoder join.
//!
//! The source frame is the same declared station origin for each separate section. The physical
//! field's pump clock continues through ReceptionCarry; this is not a claim that arbitrary erased
//! selective advances have been inferred. The command requires its own measured, committed pin;
//! no historical physical-repair pin licenses this changed law.

use super::*;
use holonics::hnn::physical::{PhysicalLearning, PhysicalObservation, PhysicalResident};
use holonics::hnn::prediction::DamagedSection;
use holonics::hnn::word::WordOpening;
use holonics::holarchy::terrain::{CyclicLaw, KnownTruth};
use std::io::Write;

pub(super) fn run(
    damage_name: &str,
    count: usize,
    aperture: usize,
    out: &str,
    terrains: &[String],
    pin: &exterior::Pin,
) {
    let bound = pin
        .unit_bound_ms()
        .expect("physical-receive requires a measured reception bound");
    let erased = if damage_name == "one" {
        vec![1]
    } else {
        repair_loop::damage(damage_name)
    };
    let declared = Declared {
        alphabet: repair_loop::CLASSES,
        ..order_declared()
    };
    let field = declare(&declared);
    let shape = Declared {
        // terrain_truth's exterior declaration reserves its last class for termination.
        // The physical chart has four actual classes and no termination row.
        alphabet: repair_loop::CLASSES + 1,
        request: repair_loop::OPENING,
        stations: repair_loop::STATIONS,
        ..declared
    };
    let current = Current::at_rest(&field);
    let material = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).expect("declared material");
    let mut resident = PhysicalResident::new(&field, material, current, WordOpening::Rest);
    let receiver = ReceiverDeclaration {
        ring: 0,
        aperture,
        ..field.receivers()[0].clone()
    };
    // This comparison is a whole declared section, so its native receiving clock must read it all.
    assert_eq!(
        aperture,
        shape.request + shape.stations,
        "comparison needs the whole section"
    );
    #[allow(clippy::disallowed_methods)] // exterior output, never the retained machine state
    let mut output = std::fs::File::create(out).expect("the requested output file");
    for spec in terrains {
        let (terrain, seed) = spec.split_once('=').expect("<terrain>=<seed>");
        let seed = seed.parse().expect("a seed");
        let encoded = executed_loop::terrain_encoded(terrain, &shape, &field, seed, count);
        for (index, observed) in encoded.into_iter().enumerate() {
            let started = Instant::now();
            let damaged = DamagedSection::damage(&observed, &erased).expect("declared damage");
            let compared = damaged.placed().iter().map(Option::is_some).collect();
            let received = resident
                .receive(&damaged, &receiver, |blind| {
                    // All classes at erased stations are absent from the blind forward constructor.
                    // The same whole blind output is shown and flushed before this observation.
                    let whole = format!("{terrain}/{seed} section {index}: blind {blind:?}\n");
                    print!("{whole}");
                    std::io::stdout().flush().expect("publish blind output");
                    output
                        .write_all(whole.as_bytes())
                        .expect("write whole blind output");
                    output.flush().expect("publish whole blind output");
                    Some(PhysicalObservation {
                        observed,
                        compared,
                        learning: PhysicalLearning::Receiving,
                    })
                })
                .expect("the admitted physical reception");
            let receipt = format!(
                "comparison on intact stations only: {:?}; contemporary commit {}; physical carry at {}; elapsed {} ms\n",
                received.comparison,
                resident.constitution().commit(),
                received.prediction.carry.ticks,
                started.elapsed().as_millis(),
            );
            print!("{receipt}");
            output
                .write_all(receipt.as_bytes())
                .expect("write comparison receipt");
            output.flush().expect("publish comparison receipt");
            if started.elapsed().as_millis() > bound {
                println!(
                    "INCOMPLETE: reception exceeded measured fixed bound {bound} ms; no later section read"
                );
                return;
            }
        }
    }
}

/// [agent-inferred] A bounded acquisition read on the existing cyclic producers. Four stations
/// are the shortest passage containing both order-two continuations and neighbours on both sides
/// of the predeclared missing station 2. The physical period is the least quarter-turn period
/// containing this section; the pair family includes *every* separation in it, independent of
/// the terrain. This is a short-section law read, not a reproduction of U6's 40+8 bank consumer.
///
/// `measure` probes development material; `held` probes seeds/counts sealed before execution and
/// never deposits a probe. `coverage` is development only: one seeded KnownTruth class orbit,
/// Receiving at all four sections, fixed before probing. Its training passages share one source
/// representative, and the continuing probe readings are not independent observations. Fresh
/// seeds do not make the finite Line/Alternation pattern family new. No U6 count is presumed.
/// In `measure` and `held`, the resident alternates Receiving and PairOutputs observations. A target is
/// absent from its source and is observed only after the blind cells have been flushed. Each
/// step's eta and the *applied* logit movement are read separately. No charted substitution occurs.
pub(super) fn learn(
    role: &str,
    teaching_count: usize,
    probe_count: usize,
    out: &str,
    terrains: &[String],
    pin: &exterior::Pin,
) {
    use holonics::hnn::field::FieldMaterial;
    use holonics::hnn::prediction::{RepairedCell, repair_by_field};
    use holonics::hnn::receiving::ReceivingPhases;
    use num_bigint::BigInt;
    use num_traits::{Signed, Zero};
    assert!(matches!(role, "measure" | "held" | "coverage"), "a declared probe role");
    assert!(teaching_count > 0 && probe_count >= 2);
    let bound = pin.unit_bound_ms().expect("a measured whole-unit bound");
    let target = 2;
    let length = 4;
    let classes = repair_loop::CLASSES;
    if role == "coverage" {
        assert_eq!(teaching_count, classes, "one Receiving observation per class-translation, no repetition");
        assert_eq!(probe_count, classes, "one blind probe per class-translation, fixed coverage read");
    }
    let physical_shape = Declared {
        period: length as u64,
        alphabet: classes,
        request: 2,
        stations: 2,
        ..order_declared()
    };
    // The old notebook's producer declaration includes a termination class. Encoded::identity
    // nevertheless carries only the producer's actual four residues, matching the physical D=I.
    let truth_shape = Declared { alphabet: classes + 1, ..physical_shape };
    let field = declare_with_offsets(&physical_shape, (1..length).collect());
    let current = Current::at_rest(&field);
    let receiver = ReceiverDeclaration { ring: 0, aperture: length, ..field.receivers()[0].clone() };
    #[allow(clippy::disallowed_methods)]
    let mut output = std::fs::File::create(out).expect("the requested output file");
    publish(&mut output, format!(
        "role={role}; exact physical section length={length}; classes={classes}; target={target}; period={}; all source offsets={:?}; teaching_count={teaching_count}; probe_count={probe_count}; probe truth is never deposited\n",
        field.ring(0).period(), field.offsets(),
    ));
    let mut seeds = std::collections::BTreeSet::new();
    for spec in terrains {
        let (terrain, split) = spec.split_once('=').expect("terrain=teaching-seed:probe-seed");
        let (teaching_seed, probe_seed) = split.split_once(':').expect("disjoint seed roles");
        let teaching_seed: u64 = teaching_seed.parse().expect("a teaching seed");
        let probe_seed: u64 = probe_seed.parse().expect("a probe seed");
        assert!(seeds.insert(teaching_seed) && seeds.insert(probe_seed), "seed reuse across roles");
        let initial = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).expect("declared material");
        let mut resident = PhysicalResident::new(&field, initial.clone(), current.clone(), WordOpening::Rest);
        let teaching = if role == "coverage" {
            let law = match terrain {
                "order2" => CyclicLaw::OrderTwo { opening: physical_shape.request },
                "alternation" => CyclicLaw::Alternation,
                "line" => CyclicLaw::Line,
                _ => panic!("a terrain: order2 | alternation | line"),
            };
            let source = KnownTruth::cyclic_class_orbit(law, classes, teaching_seed, length)
                .expect("the producer's complete class orbit");
            publish(&mut output, format!("{terrain} coverage_rule=complete_source_class_translation_orbit; shifts=0..{classes}; one_seeded_source_representative; all_teaching_Receiving; fixed_before_probes; no_independence_or_held_claim\n"));
            Encoded::identity(&source, &field).expect("the same complete four-class producing chart")
        } else {
            executed_loop::terrain_encoded(terrain, &truth_shape, &field, teaching_seed, teaching_count)
        };
        let mut intended_targets = std::collections::BTreeSet::new();
        let mut published_targets = std::collections::BTreeSet::new();
        for (index, observed) in teaching.into_iter().enumerate() {
            let started = Instant::now();
            let damaged = DamagedSection::damage(&observed, &[target]).expect("declared withheld cell");
            let entered = resident.opening().clone();
            let before_material = resident.constitution().clone();
            let learning = if role == "coverage" || index % 2 == 0 { PhysicalLearning::Receiving } else { PhysicalLearning::PairOutputs };
            let phases = ReceivingPhases::declare(&field, &before_material, &current, &receiver).expect("the receiving clock");
            // Exterior timing separates existing physical work from receipt costs. It does
            // not profile arithmetic inside a law or grant a new scientific acceptance.
            let mut blind_forward_done_ns = 0;
            let mut blind_publication_done_ns = 0;
            let received = resident.receive(&damaged, &receiver, |blind| {
                blind_forward_done_ns = started.elapsed().as_nanos();
                publish(&mut output, format!("{terrain}/{teaching_seed} teaching {index}; input={:?}; blind cells={:?}; read={:?}; grain={}\n", damaged.placed(), blind.cells, blind.reads[target], phases.grain()));
                blind_publication_done_ns = started.elapsed().as_nanos();
                let mut compared = vec![false; length];
                compared[target] = true;
                Some(PhysicalObservation { observed: observed.clone(), compared, learning })
            }).expect("admitted blind physical reception");
            let receiving_done_ns = started.elapsed().as_nanos();
            // Exterior matched-material control, never retained by the machine: both Words have
            // this section, producing source frame, receiver and identical *entered* carry.
            let next_phases = ReceivingPhases::declare(&field, resident.constitution(), &current, &receiver).expect("contemporary receiving clock");
            let applied = repair_by_field(&field, resident.constitution(), &current, &damaged, &entered, &next_phases).expect("matched applied read");
            let matched_forward_done_ns = started.elapsed().as_nanos();
            let old = &received.prediction.reads[target].read.logits;
            let new = &applied.reads[target].read.logits;
            let movement: Vec<_> = new.iter().zip(old).map(|(new, old)| new-old).collect();
            let real_move = movement.iter().step_by(2).map(|value| value.abs()).max().unwrap();
            let phase_move = movement.iter().skip(1).step_by(2).map(|value| value.abs() / Rat::from_integer(2.into())).max().unwrap();
            let truth = observed.classes_read().nth(target).expect("the post-blind observation");
            if role == "coverage" {
                intended_targets.insert(truth);
                if matches!(&received.comparison, Ok(Some(_))) {
                    published_targets.insert(truth);
                }
            }
            publish(&mut output, format!(
                "teaching result; learning={learning:?}; observed={truth}; publication={:?}; applied_logit_movement={movement:?}; largest_real_move={real_move}; largest_real_move_in_grain_cells={}; largest_phase_move_turns={phase_move}; target_margin_before={}; target_margin_after={}; applied_cells={:?}; entered={:?}; retained_tick={}; material_commit={}; receiving_changed={}; source_changed={}; pair_changed={}; balances_close={}; elapsed_ms={}\n",
                received.comparison, &real_move * Rat::from_integer(BigInt::from(phases.grain())), margin(old, truth), margin(new, truth), applied.reads[target].read.cells,
                entered, received.prediction.carry.ticks, resident.constitution().commit(),
                holonics::hnn::ConstitutionRead::receiving_map(&before_material, 0) != holonics::hnn::ConstitutionRead::receiving_map(resident.constitution(), 0),
                holonics::hnn::ConstitutionRead::source_port(&before_material, 0) != holonics::hnn::ConstitutionRead::source_port(resident.constitution(), 0),
                field.offsets().iter().any(|&offset| holonics::hnn::ConstitutionRead::pair_port(&before_material, 0,offset) != holonics::hnn::ConstitutionRead::pair_port(resident.constitution(), 0,offset)),
                closed(&received.prediction) && closed(&applied), started.elapsed().as_millis(),
            ));
            let receipt_done_ns = started.elapsed().as_nanos();
            publish(&mut output, format!("{terrain} teaching {index} timings; setup_and_blind_forward_ns={blind_forward_done_ns}; blind_publication_ns={}; same_word_comparison_and_deposition_ns={}; matched_applied_control_ns={}; movement_and_receipt_ns={}; whole_unit_ns={receipt_done_ns}; wall_categories_are_exterior_not_an_arithmetic_or_certification_profile\n",
                blind_publication_done_ns-blind_forward_done_ns,
                receiving_done_ns-blind_publication_done_ns,
                matched_forward_done_ns-receiving_done_ns,
                receipt_done_ns-matched_forward_done_ns,
            ));
            assert!(closed(&received.prediction) && closed(&applied), "the measured physical balances must close");
            if started.elapsed().as_millis() > bound {
                publish(&mut output, format!("INCOMPLETE: teaching whole-unit exceeded measured bound {bound} ms; no subsequent unit\n"));
                return;
            }
        }
        if role == "coverage" {
            let expected: std::collections::BTreeSet<_> = (0..classes).collect();
            assert_eq!(intended_targets, expected, "the source orbit covers the declared target classes");
            let equal = receiving_rows_equal(resident.constitution(), receiver.ring, 0, 1);
            publish(&mut output, format!("{terrain} coverage_result; intended_targets={intended_targets:?}; published_targets={published_targets:?}; complete_complex_rows_0_1_equal={equal}; source_coverage_is_not_a_relation_fidelity_certificate\n"));
            if published_targets != expected || equal {
                publish(&mut output, "INCOMPLETE: declared coverage did not publish all Receiving observations or break the actual 0/1 row symmetry; no probes\n".into());
                return;
            }
        }
        let probes = if role == "coverage" {
            let law = match terrain {
                "order2" => CyclicLaw::OrderTwo { opening: physical_shape.request },
                "alternation" => CyclicLaw::Alternation,
                "line" => CyclicLaw::Line,
                _ => panic!("a terrain: order2 | alternation | line"),
            };
            let source = KnownTruth::cyclic_class_orbit(law, classes, probe_seed, length)
                .expect("the independently seeded probe representative's complete class orbit");
            Encoded::identity(&source, &field).expect("the same complete four-class producing chart")
        } else {
            executed_loop::terrain_encoded(terrain, &truth_shape, &field, probe_seed, probe_count)
        };
        let frozen_commit = resident.constitution().commit();
        let frozen_material = resident.constitution().clone();
        // Exterior material/source controls all enter the same actual post-teaching carry. The
        // resident itself continues between probes; its evolving interior must not be mistaken
        // for acquired source-context sensitivity in the centered comparison below.
        let controlled_opening = resident.opening().clone();
        let mut contexts = std::collections::BTreeSet::new();
        let mut rows = Vec::new();
        let (mut released_right, mut released_wrong, mut held, mut point_right) = (0,0,0,0);
        let (mut majority_right, mut left_right, mut right_right) = (0,0,0);
        for (index, observed) in probes.into_iter().enumerate() {
            let started = Instant::now();
            let damaged = DamagedSection::damage(&observed, &[target]).expect("declared withheld cell");
            let entered = resident.opening().clone();
            let pre_phases = ReceivingPhases::declare(&field, &initial, &current, &receiver).expect("initial receiving clock");
            let before = repair_by_field(&field, &initial, &current, &damaged, &controlled_opening, &pre_phases).expect("initial-material matched control");
            let initial_control_done_ns = started.elapsed().as_nanos();
            let post_phases = ReceivingPhases::declare(&field, &frozen_material, &current, &receiver).expect("learned receiving clock");
            // The first continuing read has exactly this learned control's operands. Execute
            // that Word once and use its result for both exterior observations. Subsequent
            // resident carries differ, so their common-carry controls still execute separately.
            let controlled_after = if index == 0 {
                assert_eq!(entered, controlled_opening);
                assert_eq!(resident.current(), &current);
                assert_eq!(resident.constitution(), &frozen_material);
                None
            } else {
                Some(repair_by_field(&field, &frozen_material, &current, &damaged, &controlled_opening, &post_phases).expect("same-carry learned-material control"))
            };
            let learned_control_done_ns = started.elapsed().as_nanos();
            // This is the actual continuing resident; the held truth cannot reach its read API.
            let after = resident.read(&damaged, &receiver).expect("the blind contemporary probe");
            let continuing_done_ns = started.elapsed().as_nanos();
            let controlled_after = controlled_after.as_ref().unwrap_or(&after);
            publish(&mut output, format!("{terrain}/{probe_seed} {role} probe {index}; input={:?}; before cells={:?}; matched learned cells={:?}; continuing cells={:?}; before read={:?}; matched learned read={:?}; continuing read={:?}; matched_entered={:?}; continuing_entered={:?}; carried_tick={}; balances_close={}\n", damaged.placed(), before.cells, controlled_after.cells, after.cells, before.reads[target], controlled_after.reads[target], after.reads[target], controlled_opening, entered, after.carry.ticks, closed(&before) && closed(&controlled_after) && closed(&after)));
            assert_eq!(resident.constitution(), &frozen_material, "no probe deposition");
            assert!(closed(&before) && closed(&controlled_after) && closed(&after), "the measured physical balances must close");
            assert_eq!(resident.constitution().commit(), frozen_commit);
            // Only after publishing blind output is the exterior truth used to score.
            let truth = observed.classes_read().nth(target).expect("exterior scoring truth");
            match &after.cells[target] {
                RepairedCell::Released(class) if *class == truth => released_right += 1,
                RepairedCell::Released(_) => released_wrong += 1,
                RepairedCell::Held { .. } => held += 1,
                RepairedCell::Intact(_) => panic!("the target was withheld"),
            }
            point_right += usize::from(after.reads[target].leaders() == vec![truth]);
            let placed = damaged.placed();
            contexts.insert(placed.clone());
            let mut counts = vec![0usize; classes];
            for class in placed.iter().flatten() { counts[*class] += 1; }
            // Deterministic baseline tie rule: least class at maximum intact count.
            let majority = (0..classes).max_by_key(|&class| (counts[class], std::cmp::Reverse(class))).unwrap();
            let left = placed[..target].iter().rev().flatten().next().copied();
            let right = placed[target+1..].iter().flatten().next().copied();
            majority_right += usize::from(majority == truth);
            left_right += usize::from(left == Some(truth));
            right_right += usize::from(right == Some(truth));
            let grain = pre_phases.grain();
            let pre = before.reads[target].read.logits.clone();
            let post = controlled_after.reads[target].read.logits.clone();
            let pre_cells: Vec<_> = before.reads[target].read.cells.iter().map(|cell| cell.representative(grain)).collect();
            let post_cells: Vec<_> = controlled_after.reads[target].read.cells.iter().map(|cell| cell.representative(grain)).collect();
            publish(&mut output, format!("scoring only; truth={truth}; majority={majority}; copy_left={left:?}; copy_right={right:?}; target_margin_before={}; target_margin_after={}; grain={grain}\n", margin(&pre,truth), margin(&post,truth)));
            rows.push((pre,post,pre_cells,post_cells));
            let scoring_done_ns = started.elapsed().as_nanos();
            publish(&mut output, format!("{terrain} probe {index} timings; initial_control_ns={initial_control_done_ns}; learned_control_ns={}; actual_continuing_forward_ns={}; publication_and_exterior_scoring_ns={}; whole_unit_ns={scoring_done_ns}; learned_control_reuses_identical_continuing_word={}; no_observation_or_deposition\n",
                learned_control_done_ns-initial_control_done_ns,
                continuing_done_ns-learned_control_done_ns,
                scoring_done_ns-continuing_done_ns,
                index == 0,
            ));
            if started.elapsed().as_millis() > bound {
                publish(&mut output, format!("INCOMPLETE: probe whole-unit exceeded measured bound {bound} ms; no subsequent unit\n"));
                return;
            }
        }
        publish(&mut output, format!("{terrain} counts; whole_passages={probe_count}; released_right={released_right}; released_wrong={released_wrong}; held={held}; point_singleton_right={point_right}; majority_right={majority_right}; copy_left_right={left_right}; copy_right_right={right_right}; no_probe_deposition_commit={frozen_commit}\n"));
        let context_started = Instant::now();
        // Remove each context's common real class shift before centering across contexts. Raw
        // imaginary coordinates retain their declared phase chart. The grain part uses the
        // actual representative, so a subcell raw change cannot masquerade as an amplitude face.
        let relative = |values: &[Rat]| -> Vec<Rat> { values.iter().enumerate().map(|(i,value)| if i%2==0 { value-&values[0] } else { value.clone() }).collect() };
        let pairs: Vec<_> = rows.iter().map(|(pre,post,_,_)| (relative(pre),relative(post))).collect();
        let mean = |which: bool| -> Vec<Rat> {
            (0..2*classes).map(|i| pairs.iter().map(|(pre,post)| if which { post[i].clone() } else { pre[i].clone() }).sum::<Rat>() / Rat::from_integer(BigInt::from(probe_count))).collect()
        };
        let pre_mean = mean(false);
        let post_mean = mean(true);
        let shared_change: Vec<_> = post_mean.iter().zip(&pre_mean).map(|(post,pre)| post-pre).collect();
        publish(&mut output, format!("{terrain} relative_shared_bias_before={pre_mean:?}; relative_shared_bias_after={post_mean:?}; relative_shared_bias_change={shared_change:?}\n"));
        let mut heard = false;
        let grain_differences: Vec<Vec<Rat>> = rows.iter().map(|(_,_,pre,post)| pre.iter().zip(post).map(|(a,b)| (b-&post[0])-(a-&pre[0])).collect()).collect();
        let grain_mean: Vec<Rat> = (0..classes).map(|k| grain_differences.iter().map(|row| row[k].clone()).sum::<Rat>() / Rat::from_integer(BigInt::from(probe_count))).collect();
        for (index,((pre,post),grain_delta)) in pairs.iter().zip(&grain_differences).enumerate() {
            let pre_existing: Vec<_> = pre.iter().zip(&pre_mean).map(|(value,mean)| value-mean).collect();
            let acquired: Vec<_> = post.iter().zip(pre).zip(&shared_change).map(|((post,pre),shared)| post-pre-shared).collect();
            let grain_acquired: Vec<_> = grain_delta.iter().zip(&grain_mean).map(|(value,mean)| value-mean).collect();
            let acquired_phase_turns: Vec<_> = acquired.iter().skip(1).step_by(2).map(|value| value / Rat::from_integer(2.into())).collect();
            heard |= grain_acquired.iter().any(|value| !value.is_zero());
            publish(&mut output, format!("{terrain} probe {index}; pre_existing_relative_context={pre_existing:?}; acquired_relative_context={acquired:?}; acquired_phase_turns={acquired_phase_turns:?}; acquired_real_grain_context={grain_acquired:?}\n"));
        }
        publish(&mut output, format!("{terrain} distinct_source_contexts={}; acquired_context_changes_real_amplitude_face={heard}; all_context_controls_share_one_exact_entered_carry; scope=short_section_physical_acquisition; U6_bank_counts_are_a_different_consumer\n", contexts.len()));
        publish(&mut output, format!("{terrain} final_context_summary_ns={}; this_cost_is_outside_the_individual_teaching_and_probe_units\n", context_started.elapsed().as_nanos()));
    }
}

fn receiving_rows_equal(material: &Constitution, ring: usize, left: usize, right: usize) -> bool {
    let map = holonics::hnn::ConstitutionRead::receiving_map(material, ring)
        .expect("the admitted receiving map");
    let width = map.columns();
    let entries = map.entries();
    entries[2*left*width..2*(left+1)*width] == entries[2*right*width..2*(right+1)*width]
}

fn margin(logits: &[Rat], target: usize) -> Rat {
    let rival = logits.chunks_exact(2).enumerate().filter(|(class,_)| *class != target).map(|(_,pair)| &pair[0]).max().expect("another class");
    &logits[2*target]-rival
}

fn closed(prediction: &holonics::hnn::prediction::PhysicalRepair) -> bool {
    prediction.opening.closes() && prediction.word.closes() && prediction.balances.iter().all(|balance| balance.closes())
}

#[allow(clippy::disallowed_types, clippy::disallowed_methods)] // exterior output, no native state
fn publish(output: &mut std::fs::File, text: String) {
    print!("{text}");
    std::io::stdout().flush().expect("publish whole output");
    output.write_all(text.as_bytes()).expect("write whole output");
    output.flush().expect("flush before observing/scoring");
}
