//! One continuing native receiver through observation, delayed contact credit and publication.
//! Refs #73 #62 #148. The run is `hnn_prediction executed continuing-behavior <out> <pin>`.
//!
//! [agent-inferred] The acceptance is the whole seven-passage interaction below: two actual
//! Receiving comparisons locate R from its zero opening; a prospective contact future then
//! carries a blind passage, three later comparisons, at least two actual C/K/D factor movements,
//! and a blind consequence. Every blind boundary is flushed before its observation is read.
//! One PhysicalReceiver retains the same Resident, its actual momentum, pump phase and material.
//! The native owner alone stages, certifies, deposits and rebases the reached total covector.
//!
//! This is the existing correlated KnownTruth alternation orbit through Encoded::identity.
//! Its generator belongs to the terrain, never the HNN. No expected string, answer routine,
//! authored readout, source reinjection at deposition, independent learner or retained Word is
//! added. The sparse boundary's actual Held decision is output; point leaders are not release.
//! The decoder is that Encoded chart's D and fibre. A foreign byte passage would require the
//! existing located encoding squares, not this known-truth identity chart.
//!
//! The computational object is the helical pair interaction: the source/receiver phase faces,
//! pair contact and loaded parametron on a continuing tube. Helix, pair, faces and placement,
//! and tube are touched; declared cell holonomy and tower restrictions remain attached.
//! Lessons 3/6/7/9 are consumers here: unrepaired owner refusal ends the whole run, deposition
//! must be the native certified return, actual output decides behavior, and no budget is raised.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::time::Instant;

use holonics::compression::landmark::context::{BaseMeasure, StopPrior};
use holonics::geometry::RatVec3;
use holonics::geometry::screw::ScrewGenerator;
use holonics::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution};
use holonics::hnn::encoding::Encoded;
use holonics::hnn::field::{
    ConstitutionRead, ContactDeclaration, CribDeclaration, Current, Field, FieldDeclaration,
    ReceiverDeclaration, RingDeclaration,
};
use holonics::hnn::physical::communication::PhysicalBoundary;
use holonics::hnn::physical::contact::ContactObservation;
use holonics::hnn::physical::{PhysicalLearning, PhysicalObservation, PhysicalReceiver};
use holonics::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
use holonics::hnn::word::variation::{ContactVariationAction, VariationBudget};
use holonics::hnn::word::{Absorption, WordOpening};
use holonics::holarchy::terrain::{CyclicLaw, KnownTruth};
use holonics::holon::parametron::Carrier;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{Rat, integer, rat};
use num_traits::Zero;

use super::exterior;

const CLASSES: usize = 2;
const PREFIX: usize = 2;
const APERTURE: usize = PREFIX + 1;
const RECEIVING_OBSERVATIONS: usize = CLASSES;
const CONTACT_OBSERVATIONS: usize = 3;
const CONTACT_WORDS: usize = 1 + CONTACT_OBSERVATIONS + 1;
const WHOLE_PASSAGES: usize = RECEIVING_OBSERVATIONS + CONTACT_WORDS;
const SOURCE_SEED: u64 = 20_261_008_001;
const CONSEQUENCE_SEED: u64 = 20_261_008_011;
// Fixed exact admission of this prospective future, inherited from the existing variation
// owner control's bit domain. This is a resource bound, not precision or a machinery literal.
const VARIATION_BITS: u64 = 1 << 20;

fn publish(output: &mut impl Write, line: impl AsRef<str>) {
    let line = line.as_ref();
    output
        .write_all(line.as_bytes())
        .expect("the whole actual receipt is writable");
    output
        .flush()
        .expect("publish before obtaining a later observation");
    print!("{line}");
    std::io::stdout()
        .flush()
        .expect("the actual boundary reaches stdout");
}

fn ratios(values: &[Rat]) -> Vec<String> {
    values.iter().map(exterior::ratio).collect()
}

fn opening_tick(opening: &WordOpening) -> usize {
    match opening {
        WordOpening::Rest => 0,
        WordOpening::Received { carry, .. } => carry.ticks,
    }
}

fn continued(opening: &WordOpening) -> bool {
    matches!(
        opening,
        WordOpening::Received {
            absorption: Absorption::Nothing,
            ..
        }
    )
}

fn ring(period: u64, lock: Vec<u64>) -> RingDeclaration {
    RingDeclaration {
        period,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..period)
            .map(|node| FieldDeclaration::quarter_turn(node, period))
            .collect(),
        lock,
        reflector: (0..period)
            .map(|port| ((period - port) % period) as usize)
            .collect(),
        admittance: integer(2),
        initial: 0,
    }
}

fn declare() -> Result<(Field, ReceiverDeclaration), holonics::hnn::HnnError> {
    let receiver = ReceiverDeclaration {
        ring: 0,
        aperture: APERTURE,
        tolerance: rat(1, 16),
        depth: 1,
        prior: StopPrior::half(),
        mass: 1,
        base: BaseMeasure::Even,
        receiving_prior: 0,
    };
    // Source period four holds both classes at distinct phase addresses and exceeds aperture
    // three. The interior's width-two loaded component keeps the actual Half pump clock.
    let field = Field::declare(
        FieldDeclaration {
            rings: vec![ring(4, (0..4).collect()), ring(1, Vec::new())],
            contacts: vec![ContactDeclaration {
                from: 0,
                to: 1,
                channel: vec![(0, 0)],
                admittance: integer(2),
                exponent: integer(0),
            }],
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: CLASSES,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver.clone()],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )?;
    Ok((field, receiver))
}

fn material(field: &Field) -> Result<Constitution, holonics::hnn::HnnError> {
    let theta = Constitution::initial(field, CAMPAIGN_ONE_BUDGET)?;
    let width = field.ring(1).width();
    let factor = ExactRatMatrix::identity(width)?;
    let pump = PumpDeclaration::new(
        rat(1, 16),
        Carrier::new(integer(1), integer(0))?,
        PumpStep::Half,
    )?;
    // Existing loaded storage/pump law, declared independently of every observed class.
    theta.with_ring_resonator(
        field,
        1,
        ResonatorMaterial::new(factor.clone(), factor.clone(), factor, Some(pump))?,
    )
}

fn boundary(output: &mut impl Write, role: &str, blind: &PhysicalBoundary) {
    publish(
        output,
        format!(
            "BLIND OUTPUT BEGIN; role={role}; first_station={}; grain={}\n",
            blind.first_station(),
            blind.grain()
        ),
    );
    publish(
        output,
        format!(
            "producing decoder D={:?}; encoding fibre={:?}; classes={}; sources={:?}; located={:?}\n",
            blind.chart().decoder(),
            blind.chart().fibre(),
            blind.chart().classes(),
            blind.chart().sources(),
            blind.chart().located()
        ),
    );
    for (index, read) in blind.readings().iter().enumerate() {
        publish(
            output,
            format!(
                "station={}; crossing={}; absolute_tick={}; complete_complex_logits={:?}; phase_turns={:?}; grain_cells={:?}; point_leaders={:?}; actual_decision={:?}; actual_domain={:?}\n",
                read.station,
                read.crossing,
                read.tick,
                ratios(&read.read.logits),
                ratios(&read.read.phases),
                read.read.cells,
                read.leaders(),
                blind.decisions()[index],
                blind.domains()[index]
            ),
        );
    }
    publish(
        output,
        format!(
            "BLIND OUTPUT END; role={role}; no observation has entered this forward constructor\n"
        ),
    );
}

fn point(output: &mut impl Write, role: &str, receiver: &PhysicalReceiver<'_>) {
    let opening = receiver.opening();
    publish(
        output,
        format!(
            "retained point; role={role}; material_commit={}; source_Current={:?}; absolute_next_tick={}; continued_without_absorption={}; actual_opening={opening:?}\n",
            receiver.constitution().commit(),
            receiver.current(),
            opening_tick(&opening),
            continued(&opening)
        ),
    );
    publish(
        output,
        format!(
            "actual retained future; role={role}; state_bits={}; sensitivity={:?}\n",
            receiver.resident().state_bits(),
            receiver
                .resident()
                .held_contact_variation()
                .map(|h| h.reading())
        ),
    );
    publish(
        output,
        format!(
            "actual action/current clock binding; role={role}; action={:?}; clock_matches={:?}\n",
            receiver
                .resident()
                .held_contact_variation()
                .map(|h| h.action()),
            receiver
                .resident()
                .held_contact_variation()
                .zip(receiver.resident().carried())
                .map(|(h, carry)| h.reading().next_tick == carry.ticks)
        ),
    );
}

fn elapsed(output: &mut impl Write, role: &str, start: Instant, pin: &exterior::Pin) -> bool {
    let ns = start.elapsed().as_nanos();
    let valid = pin
        .unit_bound_ms()
        .is_none_or(|bound| ns <= bound * 1_000_000);
    publish(
        output,
        format!(
            "passage complete; role={role}; elapsed_ns={ns}; elapsed_ms={}; measured_unit_bound_ms={:?}; within_declared_unit={valid}; resident_bytes={:?}\n",
            ns / 1_000_000,
            pin.unit_bound_ms(),
            exterior::resident_set()
        ),
    );
    if !valid {
        publish(
            output,
            "INCOMPLETE: this whole passage exceeded the fixed measured unit projection; no later passage or larger limit\n",
        );
    }
    valid
}

/// No program-selected answer gates the output. Acceptance requires the actual continuing
/// native operations, actual material movement and complete declared observations to occur.
pub(super) fn run(out: &str, pin: &exterior::Pin) {
    std::fs::create_dir_all(out).expect("the output receipt directory");
    let mut output =
        BufWriter::new(File::create(format!("{out}/ACTUAL_OUTPUT.txt")).expect("actual output"));
    let all = Instant::now();
    let before_work = holonics::hnn::word::work::read();
    let accepted = exercise(&mut output, pin);
    publish(
        &mut output,
        format!(
            "WHOLE RUN RECEIPT; integrated_operation_acceptance={accepted}; measured_wall_ns={}; owner_calls={:?}; resident_bytes={:?}; declared_wall_guard_ms={}; measured_unit_bound_ms={:?}; threads={}; no limit changed\n",
            all.elapsed().as_nanos(),
            holonics::hnn::word::work::read().since(before_work),
            exterior::resident_set(),
            pin.deadline_ms(),
            pin.unit_bound_ms(),
            pin.threads()
        ),
    );
    if !accepted {
        // The complete receipt was flushed; a refused native operation is not process success.
        std::process::exit(2);
    }
}

fn exercise(mut output: &mut impl Write, pin: &exterior::Pin) -> bool {
    let all = Instant::now();
    let before_work = holonics::hnn::word::work::read();
    publish(
        &mut output,
        format!(
            "continuing-behavior-v1; correlated native terrain; source_seed={SOURCE_SEED}; consequence_seed={CONSEQUENCE_SEED}; classes={CLASSES}; prefix={PREFIX}; aperture={APERTURE}; receiving_observations={RECEIVING_OBSERVATIONS}; blind_contact=1; observed_contact={CONTACT_OBSERVATIONS}; blind_consequence=1; whole_passages={WHOLE_PASSAGES}; pin_wall_guard_ms={}; threads={}\n",
            pin.deadline_ms(),
            pin.threads()
        ),
    );
    publish(
        &mut output,
        "fixed whole acceptance: all seven native passages and later observations; at least two actual C/K/D factor movements; carried delayed credit reaches a later comparison; source entrance/work and canonical momentum close; actual pump/current/receiver clocks and held future continue; final blind output precedes any observation. Actual sparse Held/fibre output remains visible. No target-string, unseen, language, generalization, completed repair or useful-product claim.\n",
    );
    let (field, declared) = match declare() {
        Ok(v) => v,
        Err(error) => {
            publish(
                &mut output,
                format!("INCOMPLETE: declared native field refused {error:?}\n"),
            );
            return false;
        }
    };
    let theta = match material(&field) {
        Ok(v) => v,
        Err(error) => {
            publish(
                &mut output,
                format!("INCOMPLETE: native material/mount refused {error:?}\n"),
            );
            return false;
        }
    };
    let current = Current::at_rest(&field);
    let truth =
        KnownTruth::cyclic_class_orbit(CyclicLaw::Alternation, CLASSES, SOURCE_SEED, APERTURE)
            .expect("the existing correlated terrain declaration");
    let encoded = Encoded::identity(&truth, &field).expect("actual known-truth identity admission");
    let consequence =
        KnownTruth::cyclic_class_orbit(CyclicLaw::Alternation, CLASSES, CONSEQUENCE_SEED, APERTURE)
            .expect("the blind source terrain");
    let consequence = Encoded::identity(&consequence, &field).expect("the same admitted chart");
    let mut receiver = match PhysicalReceiver::new(&field, theta, current, WordOpening::Rest) {
        Ok(v) => v,
        Err(error) => {
            publish(
                &mut output,
                format!("INCOMPLETE: common native Resident mount refused {error:?}\n"),
            );
            return false;
        }
    };
    publish(
        &mut output,
        format!("declared Field={field:?}; receiving section={declared:?}\n"),
    );
    point(&mut output, "initial", &receiver);
    let compared: Vec<bool> = (0..APERTURE).map(|station| station >= PREFIX).collect();
    let mut completed = 0;
    let mut receiving_changed = 0;
    for observed in &encoded {
        let role = format!("receiving observation {completed}");
        let start = Instant::now();
        let work = holonics::hnn::word::work::read();
        let before_tick = opening_tick(&receiver.opening());
        let before = receiver.constitution().clone();
        let source = observed.part(0..PREFIX).expect("actual source prefix only");
        publish(
            &mut output,
            format!(
                "source admission; role={role}; encoded_prefix={:?}; prior_next_tick={before_tick}; source is supplied once to this native section query\n",
                source.cells()
            ),
        );
        let receipt = match receiver.communicate(&source, &declared, |blind| {
            boundary(&mut output, &role, blind);
            // Reading/printing the later observation happens only here, after the entire blind
            // receipt has reached both outputs. It supplies the existing declared comparison.
            publish(
                &mut output,
                format!(
                    "LATER OBSERVATION; role={role}; actual_section={:?}; compared={compared:?}\n",
                    observed.cells()
                ),
            );
            Some(PhysicalObservation {
                observed: observed.clone(),
                compared: compared.clone(),
                learning: PhysicalLearning::Receiving,
            })
        }) {
            Ok(v) => v,
            Err(error) => {
                publish(
                    &mut output,
                    format!("INCOMPLETE: {role} native forward refused {error:?}\n"),
                );
                point(&mut output, "after receiving refusal", &receiver);
                return false;
            }
        };
        publish(
            &mut output,
            format!(
                "source/physical work; role={role}; closes={}; opening={:?}; Word={:?}; per_tick={:?}; owner_calls={:?}\n",
                receipt.closes(),
                receipt.opening,
                receipt.word,
                receipt.balances,
                holonics::hnn::word::work::read().since(work)
            ),
        );
        let closed = receipt.closes();
        match receipt.comparison {
            Ok(Some(publication)) => {
                let changed = before.receiving_map(declared.ring)
                    != receiver.constitution().receiving_map(declared.ring);
                receiving_changed += usize::from(changed);
                publish(
                    &mut output,
                    format!(
                        "actual Receiving publication; role={role}; map_changed={changed}; ratio={:?}; publication={:?}\n",
                        publication.ratio, publication.publication
                    ),
                );
            }
            other => {
                publish(
                    &mut output,
                    format!("INCOMPLETE: {role} comparison/publication is {other:?}\n"),
                );
                point(&mut output, "after receiving comparison refusal", &receiver);
                return false;
            }
        }
        point(&mut output, &role, &receiver);
        if !closed
            || opening_tick(&receiver.opening()) <= before_tick
            || !continued(&receiver.opening())
        {
            publish(
                &mut output,
                "INCOMPLETE: the actual source/work/continuing-clock receipt did not close\n",
            );
            return false;
        }
        completed += 1;
        if !elapsed(&mut output, &role, start, pin) {
            return false;
        }
    }
    if receiving_changed == 0 {
        publish(
            &mut output,
            "INCOMPLETE: actual Receiving comparisons acquired no readout movement; no authored map substitutes\n",
        );
        return false;
    }
    // Derive the fixed numerical domain from the actual full-state shape and factor coordinates.
    // This native cut is charged by the work owner; it neither executes a second passage nor
    // changes the common material/carry. Its loaded slots are part of the retained differential.
    let ops = match holonics::hnn::propagation::Operands::exact_at_cut(
        &field,
        receiver.constitution(),
        receiver.current(),
    ) {
        Ok(v) => v,
        Err(error) => {
            publish(
                &mut output,
                format!("INCOMPLETE: prospective native operand admission refused {error:?}\n"),
            );
            return false;
        }
    };
    let shape = holonics::hnn::word::EndChange::rest(&field, &ops);
    let state_coordinates = shape
        .storage
        .iter()
        .chain(shape.arrivals.iter().flatten())
        .chain(shape.states.iter().flatten())
        .chain(shape.resonators.iter().flatten().flatten())
        .map(Vec::len)
        .sum::<usize>();
    let parameters = (0..field.contacts().len())
        .map(|a| {
            [
                receiver.constitution().contact_storage(a),
                receiver.constitution().contact_stiffness(a),
                receiver.constitution().contact_dissipation(a),
            ]
            .iter()
            .map(|f| f.rows() * f.columns())
            .sum::<usize>()
        })
        .sum::<usize>();
    let budget = VariationBudget {
        ratios: parameters * state_coordinates,
        bits: VARIATION_BITS,
        column_ticks: parameters * APERTURE * CONTACT_WORDS,
    };
    drop(shape);
    drop(ops);
    let admission = match receiver.begin_continuing_contact_variation(budget) {
        Ok(v) => v,
        Err(error) => {
            publish(
                &mut output,
                format!(
                    "INCOMPLETE: current held-material future refused {error:?}; no derivative reset or bypass\n"
                ),
            );
            point(&mut output, "after prospective future refusal", &receiver);
            return false;
        }
    };
    publish(
        &mut output,
        format!(
            "actual prospective held future; budget={budget:?}; admitted={admission:?}; earlier readout-acquisition derivatives are not claimed\n"
        ),
    );
    publish(
        &mut output,
        "Declared continuing action: RealizedFactorTranslation, applied native factor increments held as controls, explicit P=I. The learner/rounding/observation-selection policy is not differentiated. The native current-Word ray/joint/storage checks admit the supplied reached direction; they do not certify historical-response score decrease. Source station entrance remains tau_g+1+j at its fixed Current lift; the independent carried hop/pump clock advances.\n",
    );
    let mut moved_publications = 0;
    let mut delayed_comparisons = 0;
    for passage in 0..CONTACT_WORDS {
        let observes = (1..=CONTACT_OBSERVATIONS).contains(&passage);
        let role = if passage == 0 {
            "blind contact".to_string()
        } else if observes {
            format!("contact observation {passage}")
        } else {
            "blind consequence".to_string()
        };
        let observed = if passage == CONTACT_WORDS - 1 {
            &consequence[0]
        } else {
            &encoded[passage % encoded.len()]
        };
        let source = observed
            .part(0..PREFIX)
            .expect("actual source only, never future target");
        let start = Instant::now();
        let work = holonics::hnn::word::work::read();
        let before_tick = opening_tick(&receiver.opening());
        let before_commit = receiver.constitution().commit();
        publish(
            &mut output,
            format!(
                "source admission; role={role}; encoded_prefix={:?}; prior_next_tick={before_tick}; producing_commit={before_commit}\n",
                source.cells()
            ),
        );
        let receipt = match receiver.communicate_contact(&source, &declared, |blind| {
            boundary(&mut output, &role, blind);
            observes.then(|| {
                publish(&mut output, format!("LATER OBSERVATION; role={role}; actual_section={:?}; compared={compared:?}\n", observed.cells()));
                ContactObservation { observed: observed.clone(), compared: compared.clone() }
            })
        }) {
            Ok(v) => v,
            Err(error) => { publish(&mut output, format!("INCOMPLETE: {role} native forward/held future refused {error:?}; no reset/skip/restart\n")); point(&mut output, "after contact forward refusal", &receiver);
                return false; }
        };
        let closed = receipt.closes();
        publish(
            &mut output,
            format!(
                "source/physical work; role={role}; closes={closed}; opening={:?}; Word={:?}; per_tick={:?}; owner_calls={:?}\n",
                receipt.opening,
                receipt.word,
                receipt.balances,
                holonics::hnn::word::work::read().since(work)
            ),
        );
        match receipt.held_comparison {
            Ok(Some(credit)) if observes => {
                let has_delayed = credit.carried.iter().any(|x| !x.is_zero());
                delayed_comparisons += usize::from(has_delayed);
                let sum_closes = credit
                    .total
                    .iter()
                    .zip(&credit.within_word)
                    .zip(&credit.carried)
                    .all(|((total, direct), carried)| total == &(direct + carried));
                publish(
                    &mut output,
                    format!(
                        "actual full contact credit; role={role}; producing_commit={}; coordinates={:?}; within_word={:?}; carried={:?}; total={:?}; sum_closes={sum_closes}; delayed_nonzero={has_delayed}; opening_costate={:?}; reached_metric={:?}; retained_reading={:?}\n",
                        credit.producing_commit,
                        credit.coordinates,
                        ratios(&credit.within_word),
                        ratios(&credit.carried),
                        ratios(&credit.total),
                        credit.opening,
                        credit.metric,
                        credit.reading
                    ),
                );
                if !sum_closes || credit.producing_commit != before_commit {
                    publish(
                        &mut output,
                        "INCOMPLETE: the actual delayed covector/material pairing did not close\n",
                    );
                    return false;
                }
            }
            Ok(None) if !observes => {}
            other => {
                publish(
                    &mut output,
                    format!("INCOMPLETE: {role} held comparison is {other:?}\n"),
                );
                point(&mut output, "after held comparison refusal", &receiver);
                return false;
            }
        }
        if !matches!(receipt.comparison.as_ref(), Ok(None)) {
            publish(
                &mut output,
                format!(
                    "INCOMPLETE: continuing contact unexpectedly used an ordinary local publication {:?}\n",
                    receipt.comparison
                ),
            );
            return false;
        }
        match receipt.held_publication {
            Ok(Some(publication)) if observes => {
                let moved = publication
                    .continuation
                    .material
                    .iter()
                    .any(|m| m.factor.entries().iter().any(|x| !x.is_zero()));
                moved_publications += usize::from(moved);
                let parameters = receiver
                    .resident()
                    .held_contact_variation()
                    .map_or(0, |h| h.reading().parameters);
                let identity = ExactRatMatrix::identity(parameters)
                    .expect("the declared finite parameter identity");
                let actual_rebase = receiver
                    .resident()
                    .held_contact_variation()
                    .map(|h| h.reading());
                let rebase_closes = publication.parameter_transport == identity
                    && Some(&publication.rebase) == actual_rebase
                    && publication.rebase.next_tick == receipt.carry.ticks;
                publish(
                    &mut output,
                    format!(
                        "actual native contact publication; role={role}; factor_moved={moved}; actual_material_commit={}; admitted_publication={:?}; canonical_held_continuation={:?}; declared_parameter_transport={:?}; successor_sensitivity={:?}; rebase_closes={rebase_closes}\n",
                        receiver.constitution().commit(),
                        publication.publication,
                        publication.continuation,
                        publication.parameter_transport,
                        publication.rebase
                    ),
                );
                if !rebase_closes {
                    publish(
                        &mut output,
                        "INCOMPLETE: the actual canonical sensitivity rebase did not match the declared action/material/clock\n",
                    );
                    return false;
                }
            }
            Ok(None) if !observes => {
                if receiver.constitution().commit() != before_commit {
                    publish(
                        &mut output,
                        "INCOMPLETE: a blind passage unexpectedly published material\n",
                    );
                    return false;
                }
            }
            other => {
                publish(
                    &mut output,
                    format!(
                        "INCOMPLETE: {role} native material publication/rebase is {other:?}; the held gradient is not a finite Deposit by itself\n"
                    ),
                );
                point(&mut output, "after material/rebase refusal", &receiver);
                return false;
            }
        }
        point(&mut output, &role, &receiver);
        if !closed
            || receipt.carry
                != match receiver.opening() {
                    WordOpening::Received { carry, .. } => carry,
                    WordOpening::Rest => receipt.blind_carry.clone(),
                }
            || opening_tick(&receiver.opening()) <= before_tick
            || !continued(&receiver.opening())
        {
            publish(
                &mut output,
                "INCOMPLETE: actual source/work/canonical carry/continuing clock did not close\n",
            );
            return false;
        }
        completed += 1;
        if !elapsed(&mut output, &role, start, pin) {
            return false;
        }
    }
    // Move the same Resident out only at the end. Reconstructing the receiver merely to inspect
    // it between inputs would throw away its declaring-face cache and obscure real whole costs.
    let resident = receiver.into_resident();
    let held = resident.held_contact_variation();
    let held_complete = held.is_some_and(|h| {
        h.action() == ContactVariationAction::RealizedFactorTranslation
            && h.reading().words == CONTACT_WORDS
            && h.reading().next_tick == resident.carried().map_or(0, |c| c.ticks)
    });
    let accepted = completed == WHOLE_PASSAGES
        && moved_publications >= 2
        && delayed_comparisons > 0
        && held_complete;
    publish(
        &mut output,
        format!(
            "whole actual interaction; complete_passages={completed}/{WHOLE_PASSAGES}; actual_receiving_movements={receiving_changed}; actual_contact_factor_publications={moved_publications}; nonzero_delayed_comparisons={delayed_comparisons}; held_future_matches_actual_clock={held_complete}; retained_state_bits={}; final_held_reading={:?}; final_material_commit={}; source_Current={:?}; owner_calls={:?}; wall_ns={}; resident_bytes={:?}; integrated_operation_acceptance={accepted}\n",
            resident.state_bits(),
            held.map(|h| h.reading()),
            resident.constitution().commit(),
            resident.current(),
            holonics::hnn::word::work::read().since(before_work),
            all.elapsed().as_nanos(),
            exterior::resident_set()
        ),
    );
    if !accepted {
        publish(
            &mut output,
            "INCOMPLETE: the whole continuing-operation acceptance did not pass; actual output above remains the receipt\n",
        );
    }
    publish(
        &mut output,
        "Scope: section-source clock and absolute carried pump clock are separately printed. This run adds no unsupported ingest, save/cold/device continuation, policy derivative, foreign codec or completion-domain release. No useful-language/product conclusion follows from the operation acceptance.\n",
    );
    accepted
}
