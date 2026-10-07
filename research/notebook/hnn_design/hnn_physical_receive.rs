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
/// `exact-relation` separately consumes the native exact sparse owner under a measured role
/// projection. Its expected margins and centered R response are development point readings;
/// the zero initial pair-output law is unchanged, so this does not identify a pair mechanism.
/// `pair-relation` appends one fresh PairOutputs observation of the already seen last section.
/// Contemporary no-deposit and source-translation controls isolate its later material effect;
/// bias and the unchanged useful signal gate are separate from the applied descent certificate.
pub(super) fn learn(
    role: &str,
    teaching_count: usize,
    probe_count: usize,
    out: &str,
    terrains: &[String],
    pin: &exterior::Pin,
) {
    if matches!(role, "exact-relation" | "pair-relation") {
        exact_relation(teaching_count, probe_count, out, terrains, pin, role == "pair-relation");
        return;
    }
    if role == "charted-compare" {
        charted_compare(teaching_count, probe_count, out, terrains, pin);
        return;
    }
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

/// The exact physical receiving relation is an existing-owner scientific read. At one actual
/// carried end c, delta_i = f(Theta_4, c, u_i) - f(Theta_0, c, u_i); delta_i minus its orbit mean
/// removes a source-independent receiving bias. The native consumer is still the same sparse
/// source -> Word -> receiving face -> observed ratio -> that Word's pullback -> R normal law.
/// Whole-job admission is separate from the charted comparison's disproved unit projection.
fn exact_relation(teaching_count: usize, probe_count: usize, out: &str, terrains: &[String], pin: &exterior::Pin, pair_role: bool) {
    use holonics::hnn::prediction::predict_sparse_by_field;
    use holonics::hnn::receiving::ReceivingPhases;
    use num_traits::Signed;
    assert_eq!((teaching_count,probe_count),(4,4),"same fixed complete class orbits");
    assert_eq!(terrains,["order2=20261006001:20261006011".to_owned()]);
    let role_bound=pin.unit_bound_ms().expect("a separately measured exact-role projection");
    let all_started=Instant::now();
    let all_work=holonics::hnn::word::work::read();
    let shape=Declared {period:4,alphabet:repair_loop::CLASSES,request:2,stations:2,..order_declared()};
    let field=declare_with_offsets(&shape,(1..4).collect());
    let current=Current::at_rest(&field);
    let receiver=ReceiverDeclaration {ring:0,aperture:4,..field.receivers()[0].clone()};
    let initial=Constitution::initial(&field,CAMPAIGN_ONE_BUDGET).expect("same initial material");
    let grain=ReceivingPhases::declare(&field,&initial,&current,&receiver).unwrap().grain();
    let tolerance=Rat::new(1.into(),grain.into());
    let mut resident=PhysicalResident::new(&field,initial.clone(),current.clone(),WordOpening::Rest);
    let mut declaration=DeclarationWork::default();
    let mut completed=0;
    let mut common=None;
    let mut common_phases=None;
    let mut pair_baseline=None;
    let mut pairs=Vec::new();
    let mut initial_passes=true;
    let mut learned_passes=true;
    #[allow(clippy::disallowed_types, clippy::disallowed_methods)]
    let mut output=std::fs::File::create(out).expect("requested output");
    if pair_role {
        publish(&mut output,format!("pair-relation; fresh native coordinate Words; same four R observations then one PairOutputs observation of the already seen final teaching section; same four blind source translations; unchanged OrderTwo seeds20261006001:20261006011 and withheld station2; grain={grain}; tolerance={tolerance}; blind receipt precedes repeated teacher; actual carry and pair material retained; no probe deposition; whole_job_deadline_ms={}; measured_role_bound_ms={role_bound}\n",pin.deadline_ms()));
        publish(&mut output,format!("fixed pair receiving gate: complete4R+1Pair+4probes; own pair comparison first-order descent<0; all learned common and continuing margins>{tolerance}; no-pair contemporary material fails some; centered real pair effect>{tolerance}; report bias, material effect and useful gate separately; this delayed-one-class relation cannot establish pair necessity or order-two key discovery; finite spent correlated orbits are not untouched holdout; a weak last-context pair step does not refute pair necessity\n"));
    } else {
    publish(&mut output,format!("exact-relation; actual PhysicalResident sparse R-only reception; four teachings then four blind probes; OrderTwo seeds20261006001:20261006011; x_t=x_(t-2)+1 mod4; station2 withheld; grain={grain}; tolerance={tolerance}; actual carry continues; expected target read only after blind publication; no probe deposition; source/clock/chart/decoder and physical balance contracts unchanged; declaration reuse is a work receipt, not acceptance; every setup/control/Word charged; whole_job_deadline_ms={}; new_exact_role_bound_ms={role_bound}; inherited composite unit latency is not acceptance; no charted speedup/equivalence or source-domain release claim\n",pin.deadline_ms()));
    publish(&mut output,format!("fixed receiving gate: complete4+4; all learned common-carry and actual continuing expected-target margins>{tolerance}; initial common-carry material fails some expected margin; centered acquired real source response>{tolerance}; comparison refusal means incomplete; no independent/general-language/order-two-key/full-teaching-retention claim; sources are spent correlated orbits; controls use actual exact post-teaching carry and never deposit; initial E is the declared dense sign map/2; pair-output factors are zero and unchanged by R-only deposition, so no learned pair-mechanism claim\n"));
    }
    if !exact_role(&mut output,"setup",all_started,role_bound,None,&initial) {
        interaction_work(&mut output,all_work,&declaration,completed,false);return;
    }
    for (teaching,seed) in [(true,20261006001),(false,20261006011)] {
        let truth=KnownTruth::cyclic_class_orbit(CyclicLaw::OrderTwo {opening:2},shape.alphabet,seed,4).unwrap();
        for (index,observed) in Encoded::identity(&truth,&field).unwrap().into_iter().enumerate() {
            let started=Instant::now();
            let before_work=holonics::hnn::word::work::read();
            let entered=resident.opening().clone();
            if !teaching && index==0 {common=Some(entered.clone());}
            let material=resident.constitution().clone();
            if pair_role && (resident.current()!=&current ||
                pair_baseline.as_ref().is_some_and(|baseline| !same_declaring_medium(&field,baseline,&material))) {
                publish(&mut output,"INCOMPLETE: common-control source frame/lift or actual declaring coefficient key differs; no further Word\n".into());
                interaction_work(&mut output,all_work,&declaration,completed,false);return;
            }
            let damaged=DamagedSection::damage(&observed,&[2]).unwrap();
            let mut producing_phases=None;
            let mut forward_ns=0;
            let mut publication_ns=0;
            let received=match resident.receive_sparse_with_receiving_diagnostic(&damaged,&receiver,|blind,phases| {
                forward_ns=started.elapsed().as_nanos();
                assert_eq!(grain,phases.grain());
                if pair_role && !teaching && index==0 {producing_phases=Some(phases.clone());}
                publish(&mut output,format!("exact blind; teaching={teaching}; section={index}; input={:?}; whole_cells={:?}; reads={:?}; carry_tick={}; producing_commit={}\n",damaged.placed(),blind.cells,blind.reads,blind.carry.ticks,material.commit()));
                publication_ns=started.elapsed().as_nanos();
                teaching.then(||PhysicalObservation {observed:observed.clone(),compared:vec![false,false,true,false],learning:PhysicalLearning::Receiving})
            }) {
                Ok(v)=>v,
                Err(e)=>{publish(&mut output,format!("INCOMPLETE: exact native forward refused {e:?}\n"));interaction_work(&mut output,all_work,&declaration,completed,false);return;}
            };
            let receive_ns=started.elapsed().as_nanos();
            if pair_role && producing_phases.as_ref().is_some_and(|p|
                p.ring()!=receiver.ring || p.aperture()!=receiver.aperture ||
                p.tolerance()!=&receiver.tolerance || p.depth()!=receiver.depth) {
                publish(&mut output,format!("INCOMPLETE: actual common-control producing phases do not match receiver {receiver:?}; phases={producing_phases:?}\n"));
                interaction_work(&mut output,all_work,&declaration,completed,false);return;
            }
            declaration.selected(received.declaring_face_reused);
            assert!(closed(&received.prediction),"actual exact source/Word/tick balances close");
            publish(&mut output,format!("exact native work; teaching={teaching}; section={index}; declaration={declaration:?}; receive_owner_calls={:?}; forward_ns={forward_ns}; blind_publication_ns={}; comparison_deposition_and_return_ns={}; whole_receive_ns={receive_ns}; balances_close=true; retained_tick={}\n",holonics::hnn::word::work::read().since(before_work),publication_ns-forward_ns,receive_ns-publication_ns,received.prediction.carry.ticks));
            let control_started=Instant::now();
            if teaching {
                match received.comparison {
                    Ok(Some(publication))=>{
                        let changed=holonics::hnn::ConstitutionRead::receiving_map(&material,0)!=holonics::hnn::ConstitutionRead::receiving_map(resident.constitution(),0);
                        publish(&mut output,format!("exact observed R publication; section={index}; R_changed={changed}; commit={}; loci={:?}; source_certificate={}; source_pairing={}; comparison follows whole blind output\n",publication.publication.commit,publication.publication.loci,publication.source_certificate.is_some(),publication.source_pairing.is_some()));
                        publish_receiving_operands(&mut output,index,&publication,&received.prediction);
                    }
                    refusal=>{publish(&mut output,format!("INCOMPLETE: exact comparison refused {refusal:?}; actual blind carry retained\n"));interaction_work(&mut output,all_work,&declaration,completed,false);return;}
                }
            } else {
                assert!(matches!(received.comparison,Ok(None)),"blind probe has no comparison");
                assert_eq!(resident.constitution(),&material,"no probe changes material");
            }
            if !exact_role(&mut output,"primary sparse reception",started,role_bound,Some(&received.prediction.carry),resident.constitution()) {
                interaction_work(&mut output,all_work,&declaration,completed,false);return;
            }
            if !teaching {
                let fixed=common.as_ref().expect("actual post-teaching carry");
                let initial_control_started=Instant::now();
                if pair_role && index==0 {common_phases=producing_phases;}
                let baseline=pair_baseline.as_ref().unwrap_or(&initial);
                // Equal producing source frame/receiver/interior at this common opening. Actual
                // continuing Words still ask the resident's declaring owner on each new lift.
                let before_phases=if pair_role {
                    common_phases.as_ref().expect("actual common-carry producing phases").clone()
                } else {ReceivingPhases::declare(&field,&initial,&current,&receiver).unwrap()};
                let before=match predict_sparse_by_field(&field,baseline,&current,&damaged,fixed,&before_phases) {
                    Ok(v)=>v,
                    Err(e)=>{publish(&mut output,format!("INCOMPLETE: exact initial control refused {e:?}\n"));interaction_work(&mut output,all_work,&declaration,completed,false);return;}
                };
                let before_feature=before.receiving_feature(2)
                    .expect("the existing common-carry Word's actual receiving anchor");
                if !exact_role(&mut output,if pair_role {"no-pair fixed-carry control"} else {"initial fixed-carry control"},initial_control_started,role_bound,Some(&before.prediction().carry),baseline) {
                    interaction_work(&mut output,all_work,&declaration,completed,false);return;
                }
                let matched=if index==0 {
                    assert_eq!(&entered,fixed);
                    None
                } else {
                    let learned_control_started=Instant::now();
                    let phases=if pair_role {common_phases.as_ref().unwrap().clone()} else {ReceivingPhases::declare(&field,&material,&current,&receiver).unwrap()};
                    match predict_sparse_by_field(&field,&material,&current,&damaged,fixed,&phases) {
                        Ok(v)=>{
                            if !exact_role(&mut output,"learned fixed-carry control",learned_control_started,role_bound,Some(&v.prediction().carry),&material) {
                                interaction_work(&mut output,all_work,&declaration,completed,false);return;
                            }
                            Some(v)
                        },
                        Err(e)=>{publish(&mut output,format!("INCOMPLETE: exact learned control refused {e:?}\n"));interaction_work(&mut output,all_work,&declaration,completed,false);return;}
                    }
                };
                let after=matched.as_ref().map(|x|x.prediction()).unwrap_or(&received.prediction);
                let after_feature=matched.as_ref().map(|x|x.receiving_feature(2)
                    .expect("the existing learned common-carry Word's actual receiving anchor"))
                    .unwrap_or_else(||received.receiving_features.as_ref()
                        .expect("the actual first probe exposes its reached forward features")[2].clone());
                assert!(closed(before.prediction()) && closed(after));
                publish(&mut output,format!("matched common-carry receiving features; probe={index}; no_pair_feature={before_feature:?}; learned_feature={after_feature:?}; receiver_lift={:?}; common_entered_tick={}; producing_no_pair_commit={}; producing_learned_commit={}; no extra Word/comparison/deposit\n",current.lift(),if let WordOpening::Received {carry,..}=fixed {carry.ticks} else {0},baseline.commit(),material.commit()));
                if pair_role {publish(&mut output,format!("pair fixed-carry material controls; probe={index}; no_pair_commit={}; no_pair={:?}; pair_commit={}; learned={:?}; actual_continuing={:?}; no observation or deposit\n",baseline.commit(),before.prediction().reads[2],material.commit(),after.reads[2],received.prediction.reads[2]));}
                else {
                publish(&mut output,format!("exact fixed-carry controls; probe={index}; initial={:?}; learned={:?}; actual_continuing={:?}; no observation or deposit\n",before.prediction().reads[2],after.reads[2],received.prediction.reads[2]));
                }
                let target=observed.classes_read().nth(2).expect("exterior expected relation");
                let pre=before.prediction().reads[2].read.logits.clone();
                let post=after.reads[2].read.logits.clone();
                let actual=&received.prediction.reads[2].read.logits;
                initial_passes &= margin(&pre,target)>tolerance;
                learned_passes &= margin(&post,target)>tolerance && margin(actual,target)>tolerance;
                if pair_role {publish(&mut output,format!("pair relation comparison after blind publication; probe={index}; truth={target}; no_pair_margin={}; learned_common_margin={}; continuing_margin={}; required={tolerance}\n",margin(&pre,target),margin(&post,target),margin(actual,target)));}
                else {
                publish(&mut output,format!("exact relation comparison after publication; probe={index}; truth={target}; initial_margin={}; learned_common_margin={}; continuing_margin={}; required={tolerance}\n",margin(&pre,target),margin(&post,target),margin(actual,target)));
                }
                pairs.push((pre,post));
            }
            completed+=1;
            publish(&mut output,format!("exact whole unit; teaching={teaching}; section={index}; controls_receipts_and_grading_ns={}; whole_unit_ns={}; all_owner_calls={:?}; unit_cost_is_telemetry; whole_job_admission_unchanged\n",control_started.elapsed().as_nanos(),started.elapsed().as_nanos(),holonics::hnn::word::work::read().since(before_work)));
            if pair_role && teaching && index==teaching_count-1 {
                pair_baseline=exact_pair_observation(&mut resident,&field,&current,&receiver,&observed,&mut output,role_bound,&mut declaration);
                if pair_baseline.is_none() {interaction_work(&mut output,all_work,&declaration,completed,false);return;}
                completed+=1;
            }
        }
    }
    let mut acquired=false;
    if let Some((pre,_))=pairs.first() {
        let count=Rat::from_integer(pairs.len().into());
        let mean:Vec<Rat>=(0..pre.len()).map(|j|pairs.iter().map(|(a,b)|&b[j]-&a[j]).sum::<Rat>()/&count).collect();
        acquired=pairs.iter().any(|(a,b)|a.iter().zip(b).zip(&mean).enumerate().any(|(j,((a,b),m))|j%2==0 && (b-a-m).abs()>tolerance));
        if pair_role {
            let post_mean:Vec<Rat>=(0..pre.len()).map(|j|pairs.iter().map(|(_,b)|b[j].clone()).sum::<Rat>()/&count).collect();
            let centered:Vec<Vec<Rat>>=pairs.iter().map(|(a,b)|a.iter().zip(b).zip(&mean).map(|((a,b),m)|b-a-m).collect()).collect();
            publish(&mut output,format!("pair orbit decomposition; mean_pair_effect={mean:?}; centered_pair_effect={centered:?}; post_pair_mean_logits={post_mean:?}; no individual R-delta projection or recency-cause proof\n"));
        }
    }
    let complete=completed==teaching_count+probe_count+usize::from(pair_role) && pairs.len()==probe_count;
    if pair_role {publish(&mut output,format!("bounded pair material consequence; complete_interaction={complete}; baseline_no_pair_relation_already_passes={initial_passes}; centered_real_pair_effect_above_tolerance={acquired}; every_expected_common_and_continuing_margin_passes={learned_passes}; useful_pair_relation_gate={}; whole_interaction_ns={}; own negative pairing alone does not establish subsequent useful response or missing-pair causality\n",complete && !initial_passes && acquired && learned_passes,all_started.elapsed().as_nanos()));}
    else {
    publish(&mut output,format!("bounded exact receiving relation; complete_interaction={complete}; initial_relation_already_passes={initial_passes}; centered_acquired_real_source_response_above_tolerance={acquired}; every_expected_common_and_continuing_margin_passes={learned_passes}; bounded_relation_gate={}; whole_interaction_ns={}; no charted/performance/product/generalization/order-two-key/full-teaching-retention claim\n",complete && !initial_passes && acquired && learned_passes,all_started.elapsed().as_nanos()));
    }
    interaction_work(&mut output,all_work,&declaration,completed,complete);
}

/// The actual reached R operands, read only AFTER the unchanged blind/comparison/publication.
/// A port's linear read at its already reached feature costs no additional Word. Its arithmetic
/// and full receipt publication are still charged in the existing whole unit/job measurement.
fn publish_receiving_operands(output:&mut std::fs::File,index:usize,
    publication:&holonics::hnn::physical::PhysicalPublication,
    blind:&holonics::hnn::prediction::PhysicalRepair,
) {
    use holonics::hnn::constitution::{prequential_terms,receiving_class_metric};
    let diagnostic=publication.receiving_diagnostic.as_ref()
        .expect("the exact receiving publication exposes its already reached operands");
    assert_eq!(diagnostic.crossings.len(),diagnostic.samples.len());
    let metric=receiving_class_metric(&diagnostic.samples);
    let terms=prequential_terms(&diagnostic.samples,diagnostic.before.map());
    let mut applied=Vec::new();
    for (crossing,sample) in diagnostic.crossings.iter().zip(&diagnostic.samples) {
        let before=diagnostic.before.map().apply(&sample.feature).unwrap();
        let after=diagnostic.after.map().apply(&sample.feature).unwrap();
        assert_eq!(before,blind.reads[crossing.station].read.logits,
            "the sample is the exact producing receiving chart's feature");
        let delta:Vec<Rat>=after.iter().zip(&before).map(|(a,b)|a-b).collect();
        let class:Rat=sample.covector.iter().zip(&delta).step_by(2).map(|(g,d)|g*d).sum();
        let phase:Rat=sample.covector.iter().zip(&delta).skip(1).step_by(2).map(|(g,d)|g*d).sum();
        applied.push((crossing.station,before,after,delta,
            &sample.weight*class,&sample.weight*phase));
    }
    publish(output,format!("actual R producing operands; section={index}; diagnostic={diagnostic:?}; class_metric_even_only={metric:?}; actual_predeposit_prior_terms={terms:?}; actual_publication={:?}; applied_same_feature_reads_and_descent_class_phase={applied:?}; no additional Word, return or deposit; snapshots are exterior receipts, not retained state\n",publication.publication));
}

/// One lawful coordinate consumer, on a fresh contemporary Word after the R publications.
/// The returned Theta is an exterior no-deposit control, never the resident's retained state.
/// Same-context first-order descent is a mechanical reading, not a finite score or useful gate.
fn exact_pair_observation(
    resident:&mut PhysicalResident<'_>,field:&Field,current:&Current,
    receiver:&ReceiverDeclaration,observed:&Encoded,output:&mut std::fs::File,
    bound:u128,declaration:&mut DeclarationWork,
) -> Option<Constitution> {
    use holonics::hnn::ConstitutionRead;
    use holonics::hnn::prediction::predict_sparse_by_field;
    let producing=resident.constitution().clone();
    if resident.current()!=current {
        publish(output,format!("INCOMPLETE: pair consumer has foreign source frame/lift; actual={:?}; requested={current:?}\n",resident.current()));
        return None;
    }
    let entered=resident.opening().clone();
    let damaged=DamagedSection::damage(observed,&[2]).unwrap();
    let mut phases=None;
    let started=Instant::now();
    let before_work=holonics::hnn::word::work::read();
    let received=match resident.receive_sparse(&damaged,receiver,|blind,declared| {
        phases=Some(declared.clone());
        publish(output,format!("pair coordinate blind; source={:?}; producing_commit={}; whole_receipt={blind:?}; fresh Word on actual entered carry; repeated teacher still absent from forward source\n",damaged.placed(),producing.commit()));
        Some(PhysicalObservation {observed:observed.clone(),compared:vec![false,false,true,false],learning:PhysicalLearning::PairOutputs})
    }) {
        Ok(v)=>v,
        Err(e)=>{publish(output,format!("INCOMPLETE: pair coordinate forward refused {e:?}\n"));return None;}
    };
    declaration.selected(received.declaring_face_reused);
    if !closed(&received.prediction) {
        publish(output,format!("INCOMPLETE: pair blind physical balances do not close; receipt={:?}\n",received.prediction));return None;
    }
    let publication=match &received.comparison {
        Ok(Some(v))=>v,
        refusal=>{publish(output,format!("INCOMPLETE: pair observation refused {refusal:?}; blind carry retained\n"));return None;}
    };
    let (Some(paired),Some(certificate))=(&publication.source_pairing,&publication.source_certificate) else {
        publish(output,format!("INCOMPLETE: pair publication lacks applied certificates; publication={publication:?}\n"));return None;
    };
    if !certificate.joint.holds() || !paired.defect.is_zero() || !paired.composition_defect.is_zero()
        || paired.receiving!=paired.opening || paired.opening!=paired.deposition
        || paired.return_remainders.entries!=0 || paired.producing_commit!=producing.commit()
        || paired.source_lift.as_slice()!=current.lift() {
        publish(output,format!("INCOMPLETE: pair applied joint/pairing/commit/source-frame contract failed; certificate={certificate:?}; pairing={paired:?}; requested_commit={}; requested_frame={current:?}\n",producing.commit()));return None;
    }
    let after=resident.constitution();
    let ports_equal=(0..field.rings().len()).all(|ring|
        producing.source_port(ring)==after.source_port(ring) && producing.receiving_map(ring)==after.receiving_map(ring));
    if !ports_equal || !same_declaring_medium(field,&producing,after) {
        publish(output,format!("INCOMPLETE: pair changed E/R or actual declaring-medium inputs; R_E_equal={ports_equal}; producing={producing:?}; after={after:?}\n"));return None;
    }
    let outputs_changed=field.sources().iter().any(|&ring|field.offsets().iter().any(|&offset|
        producing.pair_port(ring,offset).unwrap().outputs()!=after.pair_port(ring,offset).unwrap().outputs()));
    let descent=paired.receiving<Rat::zero();
    publish(output,format!("pair coordinate publication; commit={}; output_changed={outputs_changed}; R_E_fixed=true; applied_certificate={certificate:?}; applied_pairing={paired:?}; own_realized_first_order_descent={descent}; same blind carry retained; all signed response ticks charged in whole role; owner_calls={:?}\n",after.commit(),holonics::hnn::word::work::read().since(before_work)));
    if !exact_role(output,"fresh PairOutputs observation",started,bound,Some(&received.prediction.carry),after) {return None;}
    let no_deposit_started=Instant::now();
    let no_deposit=match predict_sparse_by_field(field,&producing,current,&damaged,&entered,phases.as_ref().unwrap()) {
        Ok(v)=>v.finish(),
        Err(e)=>{publish(output,format!("INCOMPLETE: pair no-deposit control refused {e:?}\n"));return None;}
    };
    if no_deposit!=received.prediction {
        publish(output,format!("INCOMPLETE: whole no-deposit blind/carry mismatch; no_deposit={no_deposit:?}; actual={:?}\n",received.prediction));return None;
    }
    publish(output,format!("pair no-deposit control; complete_receipt_and_carry_equal=true; producing_commit={}; same source/frame/receiver/phases/entered carry; fresh native Word; no observation or deposition\n",producing.commit()));
    if !exact_role(output,"pair matched no-deposit Word",no_deposit_started,bound,Some(&no_deposit.carry),&producing) {return None;}
    if !descent || !outputs_changed || paired.source_move_squared.is_zero() {
        publish(output,"INCOMPLETE: pair coordinate has no nonzero first-order descending material consequence; no later probe; no useful or missing-pair-cause claim\n".into());
        return None;
    }
    Some(producing)
}

/// Exact inputs of receiving::declaration::DeclaringMaterial, compared at this consumer.
/// Source E, pair ports, R, transport and statistics are absent from that producer's key.
fn same_declaring_medium(field:&Field,a:&Constitution,b:&Constitution) -> bool {
    use holonics::hnn::ConstitutionRead;
    (0..field.rings().len()).all(|g|
        a.standing(g)==b.standing(g) && a.passive_factor(g)==b.passive_factor(g)
        && a.contrast_port(g)==b.contrast_port(g) && a.slices(g)==b.slices(g)
        && a.ring_resonator(g)==b.ring_resonator(g))
    && (0..field.contacts().len()).all(|j|
        a.contact_storage(j)==b.contact_storage(j) && a.contact_stiffness(j)==b.contact_stiffness(j)
        && a.contact_dissipation(j)==b.contact_dissipation(j)
        && a.contact_stiffness_signature(j)==b.contact_stiffness_signature(j)
        && a.contact_surface_storage(j)==b.contact_surface_storage(j))
}

fn exact_role(output:&mut std::fs::File,name:&str,started:Instant,bound_ms:u128,
    carry:Option<&holonics::hnn::word::ReceptionCarry>,material:&Constitution,
) -> bool {
    let carry_denominator_bits=carry.map(|c|c.change.storage.iter().flatten()
        .chain(c.change.arrivals.iter().flatten().flatten())
        .chain(c.change.states.iter().flatten().flatten())
        .chain(c.change.resonators.iter().flatten().flatten().flatten())
        .chain(c.conductances.iter()).chain(c.momenta.iter().flatten())
        .chain(c.resonator_momenta.iter().flatten().flatten())
        .map(|v|v.denom().bits()).max().unwrap_or(0)).unwrap_or(0);
    let receiving_denominator_bits=holonics::hnn::ConstitutionRead::receiving_map(material,0)
        .map(|r|r.entries().iter().map(|v|v.denom().bits()).max().unwrap_or(0)).unwrap_or(0);
    let elapsed=started.elapsed().as_nanos();
    publish(output,format!("exact execution role={name}; elapsed_ns={elapsed}; projected_upper_ms={bound_ms}; largest_actual_carry_denominator_bits={carry_denominator_bits}; largest_receiving_map_denominator_bits={receiving_denominator_bits}; timing does not prove a cause from bit length\n"));
    if elapsed>bound_ms*1_000_000 {
        publish(output,format!("INCOMPLETE: changed exact role exceeded its fixed measured projection; no further role; whole resource envelope unchanged\n"));
        false
    } else {true}
}

/// Matched sparse engineering read, declared before execution. The exact baseline excludes
/// its otherwise additional completion work. This role never supplies an E/pair publication.
fn charted_compare(teaching_count: usize, probe_count: usize, out: &str, terrains: &[String], pin: &exterior::Pin) {
    use holonics::hnn::prediction::{charted::{ChartedPhysicalResident, ChartedTolerance}, predict_sparse_by_field};
    use holonics::hnn::receiving::ReceivingPhases;
    use holonics::hnn::word::{Absorption, EndChange};
    use num_traits::Signed;
    let total_work_before=holonics::hnn::word::work::read();
    let mut declaration_work=DeclarationWork::default();
    let mut completed_units=0usize;
    let mut relation_rows=Vec::new();
    let mut common_probe_opening=None;
    let mut relation_complete=true;
    let mut initial_relation_complete=true;
    assert_eq!((teaching_count,probe_count),(4,4),"matched fixed complete class orbits");
    assert_eq!(terrains.len(),1);
    assert_eq!(terrains[0],"order2=20261006001:20261006011","spent coverage baseline operands");
    let bound=pin.unit_bound_ms().expect("matched whole-unit measured projection");
    let shape=Declared {period:4,alphabet:repair_loop::CLASSES,request:2,stations:2,..order_declared()};
    let field=declare_with_offsets(&shape,(1..4).collect());
    let current=Current::at_rest(&field);
    let receiver=ReceiverDeclaration {ring:0,aperture:4,..field.receivers()[0].clone()};
    let theta=Constitution::initial(&field,CAMPAIGN_ONE_BUDGET).expect("same baseline material");
    let initial=theta.clone();
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
    publish(&mut output,format!("declared interaction: four Receiving teachings then four unobserved probes, in producer class-translation order; terrain x_t=x_(t-2)+1 modulo4 after opening2; station2 absent from every blind source; expected relation is the terrain's class at station2; compare only after publication; probe truth never deposits; all probes additionally compare initial/learned material under one fixed actual post-teaching carry; initial control is exterior, not retained by HNN; complete bounded relation requires all common-carry learned and actual continuing target margins>{}; initial common-carry material must fail at least one expected margin; acquired centered real source response must exceed the same grain tolerance; unchanged material during probes; actual error and work balances close; spent source families are not independent or unseen; no admission or timing budget is raised\n",Rat::new(1.into(),grain.into())));
    let coordinates=|e: &EndChange| -> Vec<Rat> { e.storage.iter().flatten().chain(e.arrivals.iter().flatten().flatten()).chain(e.states.iter().flatten().flatten()).chain(e.resonators.iter().flatten().flatten().flatten()).cloned().collect() };
    for (teaching,seed) in [(true,20261006001),(false,20261006011)] {
        let truth=KnownTruth::cyclic_class_orbit(CyclicLaw::OrderTwo {opening:2},shape.alphabet,seed,4).expect("same predeclared source orbit");
        for (index,observed) in Encoded::identity(&truth,&field).unwrap().into_iter().enumerate() {
            let whole=Instant::now();
            let unit_work_before=holonics::hnn::word::work::read();
            if !teaching && index==0 {common_probe_opening=Some(reference_opening.clone());}
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
            let exact=match predict_sparse_by_field(&field,&material,&current,&damaged,&reference_opening,&phases) {Ok(v)=>v,Err(e)=>{publish(&mut output,format!("INCOMPLETE: exact sparse forward refused {e:?}\n"));interaction_work(&mut output,total_work_before,&declaration_work,completed_units,false);return;}};
            let exact_forward_ns=exact_started.elapsed().as_nanos();
            let exact_prediction=exact.prediction().clone();
            let charted_started=Instant::now();let mut charted_forward_ns=0;let mut blind_publication_done_ns=0;
            let charted=match resident.receive(&damaged,&receiver,|blind| {
                charted_forward_ns=charted_started.elapsed().as_nanos();
                publish(&mut output,format!("matched {teaching} section {index}; input={:?}; exact sparse blind cells={:?}; charted blind cells={:?}; exact tick={}; charted tick={}; producing_commit={}\n",damaged.placed(),exact_prediction.cells,blind.cells,exact_prediction.carry.ticks,blind.carry.ticks,material.commit()));
                blind_publication_done_ns=charted_started.elapsed().as_nanos();
                teaching.then(||(observed.clone(),vec![false,false,true,false]))
            }) {Ok(v)=>v,Err(e)=>{publish(&mut output,format!("INCOMPLETE: charted forward refused {e:?}\n"));interaction_work(&mut output,total_work_before,&declaration_work,completed_units,false);return;}};
            declaration_work.selected(charted.declaring_face_reused);
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
            let source_control_started=Instant::now();
            if !teaching {
                // These fixed exterior controls never enter the resident or observe a target.
                // All four source variations meet exactly the same actual post-teaching carry.
                let common=common_probe_opening.as_ref().expect("fixed post-teaching carry");
                let before_phases=ReceivingPhases::declare(&field,&initial,&current,&receiver).unwrap();
                let before=match predict_sparse_by_field(&field,&initial,&current,&damaged,common,&before_phases) {Ok(v)=>v,Err(e)=>{publish(&mut output,format!("INCOMPLETE: initial common-carry control refused {e:?}\n"));interaction_work(&mut output,total_work_before,&declaration_work,completed_units,false);return;}};
                let matched=if index==0 {
                    assert_eq!(&reference_opening,common);
                    None // the identical actual exact Word has already executed
                } else {
                    match predict_sparse_by_field(&field,&material,&current,&damaged,common,&phases) {Ok(v)=>Some(v),Err(e)=>{publish(&mut output,format!("INCOMPLETE: learned common-carry control refused {e:?}\n"));interaction_work(&mut output,total_work_before,&declaration_work,completed_units,false);return;}}
                };
                let after=matched.as_ref().map(|v|v.prediction()).unwrap_or(&exact_prediction);
                assert!(closed(before.prediction()) && closed(after));
                // Producer truth is read only after both native outputs have been published.
                publish(&mut output,format!("fixed common-carry probe {index}; initial={:?}; learned={:?}; actual_continuing={:?}; common_opening={common:?}; controls never deposit\n",before.prediction().reads[2],after.reads[2],charted.prediction.physical.reads[2]));
                let target=observed.classes_read().nth(2).expect("exterior relation truth");
                let pre=before.prediction().reads[2].read.logits.clone();
                let post=after.reads[2].read.logits.clone();
                let actual=&charted.prediction.physical.reads[2].read.logits;
                let minimum=Rat::new(1.into(),grain.into());
                initial_relation_complete &= margin(&pre,target)>minimum;
                relation_complete &= margin(&post,target)>minimum && margin(actual,target)>minimum;
                publish(&mut output,format!("predeclared relation probe {index}; truth={target}; common_initial_margin={}; common_learned_margin={}; actual_continuing_margin={}; minimum={minimum}; no point selected by output\n",margin(&pre,target),margin(&post,target),margin(actual,target)));
                relation_rows.push((pre,post));
            }
            let common_carry_controls_ns=source_control_started.elapsed().as_nanos();
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
            completed_units+=1;
            publish(&mut output,format!("matched owner work; teaching={teaching}; section={index}; declaration={declaration_work:?}; native_calls_this_whole_unit={:?}; counts_include_all_actual_declaration_and_control_Words; returned native motion/error/covectors unchanged; arithmetic and energy are separate axes\n",holonics::hnn::word::work::read().since(unit_work_before)));
            publish(&mut output,format!("matched costs; teaching={teaching}; section={index}; cold_charts={}; exact_sparse_forward_with_receiving_declaration_ns={exact_forward_ns}; charted_forward_with_receiving_declaration_and_error_ns={charted_forward_ns}; signed_saved_forward_ns={}; blind_publication_ns={}; charted_comparison_and_deposition_ns={}; charted_receive_ns={charted_whole_ns}; fixed_common_carry_controls_and_receipt_ns={common_carry_controls_ns}; exact_comparison_and_exterior_checks_ns={exact_comparison_ns}; largest_actual_logit_error={logit_max}; largest_actual_carry_error={}; largest_carry_bound={}; balances_close=true; whole_unit_ns={}; no_completion_cost_removed_from_grade\n",teaching && index==0,exact_forward_ns as i128-charted_forward_ns as i128,blind_publication_done_ns-charted_forward_ns,charted_whole_ns-blind_publication_done_ns,differences.iter().max().unwrap(),radius.iter().max().unwrap(),whole.elapsed().as_nanos()));
            if let Some(reason)=stop_reason {publish(&mut output,format!("INCOMPLETE: {reason}; measured forward and carry errors above; no subsequent unit\n"));interaction_work(&mut output,total_work_before,&declaration_work,completed_units,false);return;}
            if whole.elapsed().as_millis()>bound {publish(&mut output,format!("INCOMPLETE: matched unit exceeded fixed {bound}ms; no subsequent unit\n"));interaction_work(&mut output,total_work_before,&declaration_work,completed_units,false);return;}
        }
    }
    let mut acquired_source_response=false;
    if let Some((pre,_))=relation_rows.first() {
        let count=Rat::from_integer(relation_rows.len().into());
        let mean:Vec<Rat>=(0..pre.len()).map(|j|relation_rows.iter().map(|(a,b)|&b[j]-&a[j]).sum::<Rat>()/&count).collect();
        let minimum=Rat::new(1.into(),grain.into());
        acquired_source_response=relation_rows.iter().any(|(a,b)|a.iter().zip(b).zip(&mean).enumerate().any(|(j,((a,b),mean))|j%2==0 && (b-a-mean).abs()>minimum));
    }
    let complete=completed_units==teaching_count+probe_count && relation_rows.len()==probe_count;
    publish(&mut output,format!("bounded continuing relation; complete_interaction={complete}; initial_common_carry_relation_already_passes={initial_relation_complete}; fixed_common_carry_acquired_real_source_response_above_tolerance={acquired_source_response}; every_common_and_continuing_expected_margin_at_declared_grain={relation_complete}; bounded_relation_gate={}; no independent/general-language/product claim\n",complete && !initial_relation_complete && acquired_source_response && relation_complete));
    interaction_work(&mut output,total_work_before,&declaration_work,completed_units,complete);
}

#[derive(Debug,Default)]
struct DeclarationWork { selections:u64, constructions:u64, reuses:u64, invalidations:u64 }
impl DeclarationWork {
    fn selected(&mut self,reused:bool) {
        self.selections+=1;
        if reused {self.reuses+=1;} else {
            self.invalidations+=u64::from(self.constructions>0);
            self.constructions+=1;
        }
    }
}
fn interaction_work(output:&mut std::fs::File,before:holonics::hnn::word::work::WorkRead,
    declaration:&DeclarationWork,completed:usize,complete:bool,
) {
    publish(output,format!("interaction work receipt; completed_units={completed}; complete={complete}; declaration={declaration:?}; native_owner_calls={:?}; includes_setup_declarations_all_basis_Words_exact_reference_charted_and_exterior_controls; partial_attempts_retained; thread_scope=one_calling_thread; no FLOP_energy_or_speedup_conversion; whole_resource_time_in_outer_queue_receipt\n",holonics::hnn::word::work::read().since(before)));
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
