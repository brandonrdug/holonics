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
use holonics::receiver::face::GrainCell;
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
    #[allow(clippy::disallowed_types, clippy::disallowed_methods)] // exterior output, never the retained machine state
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
/// `attribution` preserves the historical four alternating updates and four Alternation probes.
/// It adds three intermediate material controls at each of the fixed probe positions zero and
/// three, all at one entered carry. These exterior controls neither observe nor deposit truth.
/// In `measure`, `held` and `attribution`, the resident alternates Receiving and PairOutputs observations. A target is
/// absent from its source and is observed only after the blind cells have been flushed. Each
/// step's eta and the *applied* logit movement are read separately. These routes stay exact.
/// `charted-compare` separately declares four Receiving observations and four blind probes on
/// the spent OrderTwo class orbit, with one-grain numerical component tolerance fixed first.
/// Each charted reception is paired with the same exact sparse Word on the contemporary
/// material and a continuing exact reference carry. Erasures remain Held in both sparse routes.
pub(super) fn learn(
    role: &str,
    teaching_count: usize,
    probe_count: usize,
    out: &str,
    terrains: &[String],
    pin: &exterior::Pin,
) {
    if role == "charted-compare" {
        charted_compare(teaching_count, probe_count, out, terrains, pin);
        return;
    }
    use holonics::hnn::field::FieldMaterial;
    use holonics::hnn::prediction::{RepairedCell, repair_by_field};
    use holonics::hnn::receiving::ReceivingPhases;
    use num_bigint::BigInt;
    use num_traits::{Signed, Zero};
    assert!(matches!(role, "measure" | "held" | "coverage" | "attribution"), "a declared probe role");
    assert!(teaching_count > 0 && probe_count >= 2);
    let bound = pin.unit_bound_ms().expect("a measured whole-unit bound");
    let target = 2;
    let length = 4;
    let classes = repair_loop::CLASSES;
    if role == "coverage" {
        assert_eq!(teaching_count, classes, "one Receiving observation per class-translation, no repetition");
        assert_eq!(probe_count, classes, "one blind probe per class-translation, fixed coverage read");
    }
    if role == "attribution" {
        assert_eq!((teaching_count, probe_count), (4, 4), "historical diagnostic partition");
        assert_eq!(terrains, ["alternation=20261006003:20261006013".to_owned()], "spent development operands fixed before output");
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
    #[allow(clippy::disallowed_types, clippy::disallowed_methods)]
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
        // Exterior finite measurement controls only. No Word, trajectory, teacher or response
        // column is retained by the HNN. Each prefix is an actually published constitution.
        let mut material_controls = if role == "attribution" { vec![initial.clone()] } else { Vec::new() };
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
            let publication = if role == "attribution" {
                causal_publication(&received.comparison, phases.grain())
            } else {
                format!("{:?}", received.comparison)
            };
            if role == "attribution" {
                let before = receiving_contrast(&before_material, receiver.ring);
                let after = receiving_contrast(resident.constitution(), receiver.ring);
                if matches!(learning, PhysicalLearning::PairOutputs) {
                    assert_eq!(holonics::hnn::ConstitutionRead::receiving_map(&before_material, receiver.ring), holonics::hnn::ConstitutionRead::receiving_map(resident.constitution(), receiver.ring), "PairOutputs leaves the whole R map unchanged");
                }
                let delta: Vec<_> = after.iter().zip(&before).map(|(a,b)| [ &a[0]-&b[0], &a[1]-&b[1] ]).collect();
                publish(&mut output, format!("attribution publication {index}; actual_R2_minus_R3_delta_real_imag={delta:?}; no_proposed_map_or_Gram_dump\n"));
                material_controls.push(resident.constitution().clone());
            }
            publish(&mut output, format!(
                "teaching result; learning={learning:?}; observed={truth}; publication={publication}; applied_logit_movement={movement:?}; largest_real_move={real_move}; largest_real_move_in_grain_cells={}; largest_phase_move_turns={phase_move}; target_margin_before={}; target_margin_after={}; applied_cells={:?}; entered={:?}; retained_tick={}; material_commit={}; receiving_changed={}; source_changed={}; pair_changed={}; balances_close={}; elapsed_ms={}\n",
                &real_move * Rat::from_integer(BigInt::from(phases.grain())), margin(old, truth), margin(new, truth), applied.reads[target].read.cells,
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
        let mut causal_controls = Vec::new();
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
            if role == "attribution" && matches!(index, 0 | 3) {
                let opened_at = match &controlled_opening {
                    WordOpening::Rest => 0,
                    WordOpening::Received { carry, .. } => carry.ticks,
                };
                let before_read = causal_read(&before, target, pre_phases.grain(), opened_at);
                let after_read = causal_read(controlled_after, target, post_phases.grain(), opened_at);
                assert_eq!(before_read.tick, after_read.tick, "same absolute receiving tick");
                causal_controls.push((index, damaged.clone(), before_read, after_read));
            }
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
        if role == "attribution" && !causal_attribution(&mut output, &field, &current, &receiver, &controlled_opening, &material_controls, &causal_controls, target, bound) {
            return;
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

/// Matched sparse engineering read, declared before execution. The exact baseline excludes
/// its otherwise additional completion work. This role never supplies an E/pair publication.
fn charted_compare(teaching_count: usize, probe_count: usize, out: &str, terrains: &[String], pin: &exterior::Pin) {
    use holonics::hnn::prediction::{charted::{ChartedPhysicalResident, ChartedTolerance}, predict_sparse_by_field};
    use holonics::hnn::receiving::ReceivingPhases;
    use holonics::hnn::word::{Absorption, EndChange};
    use num_traits::Signed;
    assert_eq!((teaching_count,probe_count),(4,4),"matched fixed complete class orbits");
    assert_eq!(terrains.len(),1);
    assert_eq!(terrains[0],"order2=20261006001:20261006011","spent coverage baseline operands");
    let bound=pin.unit_bound_ms().expect("matched whole-unit measured projection");
    let shape=Declared {period:4,alphabet:repair_loop::CLASSES,request:2,stations:2,..order_declared()};
    let field=declare_with_offsets(&shape,(1..4).collect());
    let current=Current::at_rest(&field);
    let receiver=ReceiverDeclaration {ring:0,aperture:4,..field.receivers()[0].clone()};
    let theta=Constitution::initial(&field,CAMPAIGN_ONE_BUDGET).expect("same baseline material");
    let grain=ReceivingPhases::declare(&field,&theta,&current,&receiver).unwrap().grain();
    // The accepted fixture's one-grain component bounds, fixed without consulting output.
    // These are numerical component tolerances; missing-source release still has no certificate.
    let one_grain=Rat::new(1.into(),grain.into());
    let tolerance=ChartedTolerance {logits:one_grain.clone(),receiving_covector:one_grain.clone(),source_covector:one_grain};
    let mut resident=ChartedPhysicalResident::new(&field,theta,current.clone(),WordOpening::Rest,tolerance.clone()).expect("declared charted material");
    let mut reference_opening=WordOpening::Rest;
    #[allow(clippy::disallowed_types, clippy::disallowed_methods)]
    let mut output=std::fs::File::create(out).expect("requested output");
    publish(&mut output,format!("charted-compare; exact_sparse_baseline; R_only; source_family=complete_order2_class_orbit; seeds=20261006001:20261006011; grain={grain}; fixed_tolerance={tolerance:?}; same_contemporary_charted_material; exact_reference_carry_continues; no_completion_or_speedup_claim\n"));
    let coordinates=|e: &EndChange| -> Vec<Rat> { e.storage.iter().flatten().chain(e.arrivals.iter().flatten().flatten()).chain(e.states.iter().flatten().flatten()).chain(e.resonators.iter().flatten().flatten().flatten()).cloned().collect() };
    for (teaching,seed) in [(true,20261006001),(false,20261006011)] {
        let truth=KnownTruth::cyclic_class_orbit(CyclicLaw::OrderTwo {opening:2},shape.alphabet,seed,4).expect("same predeclared source orbit");
        for (index,observed) in Encoded::identity(&truth,&field).unwrap().into_iter().enumerate() {
            let whole=Instant::now();
            // Exterior receipt cost is charged to this same whole unit. Retained charts still
            // travel through the existing key/shape/certificate/refinement owner; no shortcut.
            let route_receipt_started=Instant::now();
            let previous_routes:Vec<_>=resident.charts().keys().map(|key| {
                let chart=resident.charts().get(key).expect("a retained key's chart");
                (key.clone(),chart.rows(),chart.columns(),chart.exponent())
            }).collect();
            let route_receipt_ns=route_receipt_started.elapsed().as_nanos();
            let damaged=DamagedSection::damage(&observed,&[2]).unwrap();
            let material=resident.constitution().clone();
            let exact_started=Instant::now();
            let phases=ReceivingPhases::declare(&field,&material,&current,&receiver).unwrap();
            let exact=match predict_sparse_by_field(&field,&material,&current,&damaged,&reference_opening,&phases) {Ok(v)=>v,Err(e)=>{publish(&mut output,format!("INCOMPLETE: exact sparse forward refused {e:?}\n"));return;}};
            let exact_forward_ns=exact_started.elapsed().as_nanos();
            let exact_prediction=exact.prediction().clone();
            let charted_started=Instant::now();let mut charted_forward_ns=0;let mut blind_publication_done_ns=0;
            let charted=match resident.receive(&damaged,&receiver,|blind| {
                charted_forward_ns=charted_started.elapsed().as_nanos();
                publish(&mut output,format!("matched {teaching} section {index}; input={:?}; exact sparse blind cells={:?}; charted blind cells={:?}; exact tick={}; charted tick={}; producing_commit={}\n",damaged.placed(),exact_prediction.cells,blind.cells,exact_prediction.carry.ticks,blind.carry.ticks,material.commit()));
                blind_publication_done_ns=charted_started.elapsed().as_nanos();
                teaching.then(||(observed.clone(),vec![false,false,true,false]))
            }) {Ok(v)=>v,Err(e)=>{publish(&mut output,format!("INCOMPLETE: charted forward refused {e:?}\n"));return;}};
            let charted_whole_ns=charted_started.elapsed().as_nanos();
            let readings=&charted.prediction.error.charts;
            let chart_exponent=field.word_lattice().expect("declared chart lattice").chart_exponent();
            let candidate=|reading:&holonics::hnn::chart::ChartReading| {
                previous_routes.iter().find(|(key,..)|*key==reading.key)
            };
            let compatible=|reading:&holonics::hnn::chart::ChartReading| {
                candidate(reading).is_some_and(|(_,rows,columns,exponent)|
                    *rows==reading.width && *columns==reading.width && *exponent==chart_exponent)
            };
            // Every Newton-Schulz step re-certifies; warm admission, cold seed and exact
            // fallback each have their actual certificate calls. Count from producing starts
            // and retained shapes, rather than treating a warm key as an accepted certificate.
            let certificate_calls:u64=readings.iter().map(|r|1+u64::from(r.steps)
                +u64::from(compatible(r) && r.start!=holonics::hnn::chart::ChartStart::Warm)
                +u64::from(r.start==holonics::hnn::chart::ChartStart::Exact)).sum();
            let admitted_tolerance_checks=match &charted.comparison {
                Ok(Some(publication))=>Some((3usize, // the three nonnegative tolerance declarations
                    1usize, // one compared station's supremum against the logit tolerance
                    publication.error.logit_covectors[2].len(), // components read by that supremum
                    publication.error.receiving_covector.entries().len(),
                    publication.error.source_covectors.iter().map(Vec::len).sum::<usize>())),
                _=>None, // no invented visited-check count for an early refusal or blind probe
            };
            publish(&mut output,format!("matched producing chart work; selected_routes={}; retained_candidates={}; shape_checks={}; compatible_candidates={}; certificate_evaluations={certificate_calls}; final_target_admissions={}; refinement_steps={}; route_receipt_ns={route_receipt_ns}; admitted_tolerance_checks=(declaration,logit_order,logit_components,receiving_orders,source_orders)={admitted_tolerance_checks:?}; chart_readings={readings:?}; setup_selection_refinement_and_error_transport_wall_costs_unseparated
",
                readings.len(),readings.iter().filter(|r|candidate(r).is_some()).count(),
                readings.iter().filter(|r|candidate(r).is_some()).count(),
                readings.iter().filter(|r|compatible(r)).count(),readings.len(),
                readings.iter().map(|r|u64::from(r.steps)).sum::<u64>()));
            assert_eq!(charted.prediction.physical.carry.ticks,exact_prediction.carry.ticks);
            assert_eq!(charted.prediction.physical.carry.change.resonator_phases,exact_prediction.carry.change.resonator_phases);
            assert_eq!(charted.prediction.physical.carry.conductances,exact_prediction.carry.conductances);
            let exact_opening_residual = &exact_prediction.opening.after - &exact_prediction.opening.before
                - &exact_prediction.opening.imposed + &exact_prediction.opening.absorbed;
            let charted_opening_residual = &charted.prediction.physical.opening.after
                - &charted.prediction.physical.opening.before - &charted.prediction.physical.opening.imposed
                + &charted.prediction.physical.opening.absorbed;
            let charted_opening_work = &charted_opening_residual + &charted.prediction.error.opening.split;
            publish(&mut output,format!("matched balances; exact_opening_residual={exact_opening_residual}; exact_word_closes={}; exact_failed_tick={:?}; charted_opening_residual={charted_opening_residual}; charted_opening_split={}; charted_charged_opening_residual={charted_opening_work}; charted_source_receipts_match={}; charted_word_closes={}; charted_failed_tick={:?}; charted_balance_closes={}\n",
                exact_prediction.word.closes(),exact_prediction.balances.iter().position(|balance|!balance.closes()),
                charted.prediction.error.opening.split,
                charted.prediction.physical.opening==charted.prediction.error.opening.source,
                charted.prediction.physical.word.closes(),charted.prediction.physical.balances.iter().position(|balance|!balance.closes()),
                charted.prediction.closes()));
            assert!(closed(&exact_prediction) && charted.prediction.closes(),
                "the exact balance and charted balance with its actual opening split must close");
            let actual=coordinates(&charted.prediction.physical.carry.change);let reference=coordinates(&exact_prediction.carry.change);let radius=coordinates(&charted.prediction.error.end);
            assert_eq!(actual.len(),reference.len());assert_eq!(actual.len(),radius.len());
            let differences:Vec<_>=actual.iter().zip(&reference).map(|(a,b)|(a-b).abs()).collect();
            assert!(differences.iter().zip(&radius).all(|(d,r)|d<=r),"actual continued carry error lies in its native box");
            assert_eq!(charted.prediction.physical.reads.len(),exact_prediction.reads.len());
            assert_eq!(charted.prediction.physical.reads.len(),charted.prediction.error.stations.len());
            let logit_max=charted.prediction.physical.reads.iter().zip(&exact_prediction.reads).zip(&charted.prediction.error.stations).map(|((a,b),r)| {
                assert_eq!((a.station,a.crossing,a.tick),(b.station,b.crossing,b.tick));
                assert_eq!((r.station,r.tick),(a.station,a.tick));
                assert_eq!(a.read.logits.len(),b.read.logits.len());
                assert_eq!(a.read.logits.len(),r.logits.len());
                let differences:Vec<_>=a.read.logits.iter().zip(&b.read.logits).map(|(a,b)|(a-b).abs()).collect();
                assert!(differences.iter().zip(&r.logits).all(|(d,r)|d<=r),"same producing receiver error");
                differences.into_iter().max().unwrap()
            }).max().unwrap();
            let exact_compare_started=Instant::now();
            let mut stop_reason=None;
            if teaching {
                match (exact.observe(&material,&observed,&[false,false,true,false]),charted.comparison) {
                    (Ok(exact),Ok(Some(comparison))) => {
                        let a=&comparison.teaching.pullback.receiving.1;let b=&exact.pullback.receiving.1;let error=&comparison.error.receiving_covector;
                        assert_eq!((a.rows(),a.columns()),(b.rows(),b.columns()));
                        assert_eq!((a.rows(),a.columns()),(error.rows(),error.columns()));
                        let gradient_delta:Vec<_>=a.entries().iter().zip(b.entries()).map(|(a,b)|(a-b).abs()).collect();
                        assert!(gradient_delta.iter().zip(error.entries()).all(|(d,r)|d<=r),"actual receiving gradient error");
                        let changed=holonics::hnn::ConstitutionRead::receiving_map(&material,0)!=holonics::hnn::ConstitutionRead::receiving_map(resident.constitution(),0);
                        publish(&mut output,format!("matched publication; R_only; R_changed={changed}; exact_commit={}; charted_commit={}; actual_receiving_covector_error_max={}; receiving_bound_max={}; source_covector_bound={:?}; charged_applied={:?}\n",exact.publication.commit,comparison.teaching.publication.commit,gradient_delta.iter().max().unwrap(),error.entries().iter().max().unwrap(),comparison.error.source_covectors,comparison.error.applied));
                    }
                    (exact,charted) => stop_reason=Some(format!("observed comparison refused; exact={:?}; charted={charted:?}; numerical tolerance unchanged",exact.err().map(|e|e.error))),
                }
            } else {drop(exact);assert_eq!(resident.constitution(),&material,"no probe deposition");}
            let exact_comparison_ns=exact_compare_started.elapsed().as_nanos();
            reference_opening=WordOpening::Received {carry:exact_prediction.carry,absorption:Absorption::Nothing};
            publish(&mut output,format!("matched costs; teaching={teaching}; section={index}; cold_charts={}; exact_sparse_forward_with_receiving_declaration_ns={exact_forward_ns}; charted_forward_with_receiving_declaration_and_error_ns={charted_forward_ns}; signed_saved_forward_ns={}; blind_publication_ns={}; charted_comparison_and_deposition_ns={}; charted_receive_ns={charted_whole_ns}; exact_comparison_and_exterior_checks_ns={exact_comparison_ns}; largest_actual_logit_error={logit_max}; largest_actual_carry_error={}; largest_carry_bound={}; balances_close=true; whole_unit_ns={}; no_completion_cost_removed_from_grade\n",teaching && index==0,exact_forward_ns as i128-charted_forward_ns as i128,blind_publication_done_ns-charted_forward_ns,charted_whole_ns-blind_publication_done_ns,differences.iter().max().unwrap(),radius.iter().max().unwrap(),whole.elapsed().as_nanos()));
            if let Some(reason)=stop_reason {publish(&mut output,format!("INCOMPLETE: {reason}; measured forward and carry errors above; no subsequent unit\n"));return;}
            if whole.elapsed().as_millis()>bound {publish(&mut output,format!("INCOMPLETE: matched unit exceeded fixed {bound}ms; no subsequent unit\n"));return;}
        }
    }
}

// The fixed class contrast is the logged wrong release (two against true three), not a
// task decoder. Full native leader unions still include every class, including zero and one.
fn contrast(logits: &[Rat]) -> [Rat; 2] {
    [ &logits[4]-&logits[6], (&logits[5]-&logits[7]) / Rat::from_integer(2.into()) ]
}

fn receiving_contrast(material: &Constitution, ring: usize) -> Vec<[Rat; 2]> {
    let map = holonics::hnn::ConstitutionRead::receiving_map(material, ring).expect("actual R");
    let width = map.columns();
    (0..width).map(|j| [ &map.entries()[4*width+j]-&map.entries()[6*width+j], &map.entries()[5*width+j]-&map.entries()[7*width+j] ]).collect()
}

fn causal_publication(comparison: &Result<Option<holonics::hnn::physical::PhysicalPublication>, holonics::hnn::HnnError>, grain: u64) -> String {
    match comparison {
        Ok(Some(result)) => {
            let steps: Vec<_> = result.publication.steps.iter().map(|(locus, read)| (locus, &read.step.step)).collect();
            let phases: Vec<_> = result.ratio.phases().iter().map(|p| (p.target, GrainCell::of(&p.target_phase, grain), GrainCell::of(&p.produced_phase, grain), p.winding(), GrainCell::of(&p.gap.turns(), grain))).collect();
            format!("published commit={}; loci={:?}; eta={steps:?}; target_produced_gap_phase_cells_and_winding={phases:?}; reached_feature_energy={:?}; source_certificate={}; source_pairing={}", result.publication.commit, result.publication.loci, result.feature_energy, result.source_certificate.is_some(), result.source_pairing.is_some())
        }
        Ok(None) => "no comparison".into(),
        Err(error) => format!("refused {error:?}"),
    }
}

#[derive(Clone, Debug)]
struct CausalRead {
    tick: usize,
    grain: u64,
    sparse: [Rat; 2],
    fixed: [Rat; 2],
    columns: Vec<[Rat; 2]>,
    real_cells: Vec<[GrainCell; 2]>,
    phase_cells: Vec<GrainCell>,
    leaders: Vec<usize>,
}

fn causal_read(prediction: &holonics::hnn::prediction::PhysicalRepair, target: usize, grain: u64, opened_at: usize) -> CausalRead {
    let station = &prediction.reads[target];
    assert_eq!(station.station, target);
    assert_eq!(station.tick, opened_at + station.crossing, "native source/absolute receiving clock join");
    let domain = prediction.domains[target].as_ref().expect("admitted completed source domain");
    let completion = domain.completion.as_ref().expect("existing exact signed completion columns");
    assert_eq!(completion.station, target);
    let mut leaders = std::collections::BTreeSet::new();
    let mut real_cells = Vec::new();
    let mut phase_cells = Vec::new();
    for column in &completion.label_logits {
        let image = completion.fixed_logits.iter().zip(column).map(|(a,b)| a+b).collect();
        let read = holonics::hnn::receiving::ReceivingRead::of_logits(image, grain);
        let completed = holonics::hnn::prediction::StationRead { station: target, crossing: station.crossing, tick: station.tick, read };
        leaders.extend(completed.leaders());
        let read = &completed.read;
        real_cells.push([read.cells[2].clone(), read.cells[3].clone()]);
        phase_cells.push(GrainCell::of(&(&read.phases[2]-&read.phases[3]), grain));
    }
    let leaders: Vec<_> = leaders.into_iter().collect();
    assert_eq!(leaders, domain.classes, "full native completed-source union, not sparse leaders");
    CausalRead { tick: station.tick, grain, sparse: contrast(&station.read.logits), fixed: contrast(&completion.fixed_logits), columns: completion.label_logits.iter().map(|column| contrast(column)).collect(), real_cells, phase_cells, leaders }
}

// a_i(x,c)=m_i(x,c)-m_(i-1)(x,c), with every operand at the same actual carry.
// These controls exclude carry-mediated effects and allocate ordered interactions to the
// later actual publication. They do not construct reordered or hypothetical deposit materials.
#[allow(clippy::too_many_arguments)]
#[allow(clippy::disallowed_types)] // exterior receipt writer; never a native state or input
fn causal_attribution(output: &mut std::fs::File, field: &Field, current: &Current, receiver: &ReceiverDeclaration, opening: &WordOpening, materials: &[Constitution], controls: &[(usize, DamagedSection, CausalRead, CausalRead)], target: usize, bound: u128) -> bool {
    use holonics::hnn::{prediction::repair_by_field, receiving::ReceivingPhases};
    assert_eq!(materials.len(), 5);
    assert_eq!(controls.iter().map(|c| c.0).collect::<Vec<_>>(), vec![0,3]);
    let opened_at = match opening { WordOpening::Rest => 0, WordOpening::Received { carry, .. } => carry.ticks };
    let mut effects = Vec::new();
    for (index, damaged, before, after) in controls {
        let mut readings = vec![before.clone()];
        for (prefix, material) in materials.iter().enumerate().take(4).skip(1) {
            let started = Instant::now();
            let phases = ReceivingPhases::declare(field, material, current, receiver).expect("same producing receiver declaration");
            let prediction = repair_by_field(field, material, current, damaged, opening, &phases).expect("actual prefix material completion");
            assert!(closed(&prediction));
            let read = causal_read(&prediction, target, phases.grain(), opened_at);
            assert_eq!((read.tick,read.grain), (before.tick,before.grain));
            readings.push(read);
            let elapsed = started.elapsed();
            publish(output, format!("attribution probe {index} prefix {prefix}; elapsed_ns={}; elapsed_ms={}; balances_close=true; no_observation_or_deposition\n", elapsed.as_nanos(), elapsed.as_millis()));
            if started.elapsed().as_millis() > bound {
                publish(output, format!("INCOMPLETE: attribution control exceeded measured unit bound {bound} ms; no subsequent control\n"));
                return false;
            }
        }
        readings.push(after.clone());
        for (prefix, read) in readings.iter().enumerate() {
            publish(output, format!("attribution probe {index} prefix {prefix}; tick={}; grain={}; sparse_2_minus_3_real_phase={:?}; fixed_2_minus_3_real_phase={:?}; label_columns_2_minus_3_real_phase={:?}; absolute_real_cells_2_3_per_completion={:?}; phase_contrast_cells_per_completion={:?}; full_native_leader_union={:?}\n", read.tick,read.grain,read.sparse,read.fixed,read.columns,read.real_cells,read.phase_cells,read.leaders));
        }
        let mut per_update = Vec::new();
        for update in 1..readings.len() {
            let pre = &readings[update-1];
            let post = &readings[update];
            assert_eq!(pre.columns.len(), post.columns.len());
            let delta: Vec<_> = pre.columns.iter().zip(&post.columns).map(|(a,b)| [(&post.fixed[0]+&b[0])-(&pre.fixed[0]+&a[0]), (&post.fixed[1]+&b[1])-(&pre.fixed[1]+&a[1])]).collect();
            let fixed = [ &post.fixed[0]-&pre.fixed[0], &post.fixed[1]-&pre.fixed[1] ];
            publish(output, format!("attribution probe {index} update {update}; completed_margin_delta_real_phase={delta:?}; fixed_margin_delta_real_phase={fixed:?}; phase_is_separate_from_real_grain_release\n"));
            per_update.push(delta);
        }
        for c in 0..before.columns.len() {
            for channel in 0..2 {
                let sum: Rat = per_update.iter().map(|delta| delta[c][channel].clone()).sum();
                assert_eq!(sum, (&after.fixed[channel]+&after.columns[c][channel])-(&before.fixed[channel]+&before.columns[c][channel]), "exact chronological telescope");
            }
        }
        effects.push(per_update);
    }
    for update in 0..4 {
        let centered: Vec<_> = effects[0][update].iter().zip(&effects[1][update]).map(|(a,b)| [ &b[0]-&a[0], &b[1]-&a[1] ]).collect();
        publish(output, format!("attribution update {}; probe3_minus_probe0_completed_margin_effect_real_phase={centered:?}; pair_specific_distractor_contrast_not_population; exact_telescope=true; direct_material_at_fixed_actual_carry_only\n", update+1));
    }
    true
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
