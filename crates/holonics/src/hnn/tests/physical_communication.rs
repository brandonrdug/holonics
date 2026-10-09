//! Bounded law controls of the production complex communication boundary, not task accuracy.

use super::support::{contact, encoded, ring};
use crate::compression::landmark::context::{BaseMeasure, StopPrior};
use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution};
use crate::hnn::field::{
    CribDeclaration, Current, Field, FieldDeclaration, FieldMaterial, ReceiverDeclaration,
};
use crate::hnn::physical::{PhysicalLearning, PhysicalObservation, PhysicalReceiver};
use crate::hnn::prediction::{DamagedSection, RepairedCell, Unresolved, repair_by_field};
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::WordOpening;
use crate::ratio::{integer, rat};
use num_traits::Zero;

fn receiver() -> ReceiverDeclaration {
    ReceiverDeclaration {
        ring: 0,
        aperture: 3,
        tolerance: rat(1, 16),
        depth: 1,
        prior: StopPrior::half(),
        mass: 1,
        base: BaseMeasure::Even,
        receiving_prior: 0,
    }
}

fn field() -> Field {
    Field::declare(
        FieldDeclaration {
            rings: vec![ring(4, (0..4).collect()), ring(3, Vec::new())],
            contacts: vec![contact(0, 1, 3, 0)],
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: 4,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver()],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

fn material(field: &Field) -> Constitution {
    let theta = Constitution::initial(field, CAMPAIGN_ONE_BUDGET).unwrap();
    // The existing non-dyadic source fixture, declared independently of the later observation.
    let source = theta.source_port(0).unwrap().scaled(&rat(1, 3));
    theta.with_ports(0, None, Some(source), None).unwrap()
}

/// One fixed mechanical fixture, with the existing native contact grain. It is not a sampled
/// curriculum or an output accuracy gate; targets arrive only in the comparison callback.
fn contact_material(field: &Field) -> Constitution {
    use crate::hnn::constitution::Locus;
    let reads = crate::hnn::retention::loci(field).into_iter().collect();
    super::learning::generic(field, 81).rebased(Locus::Channel(0), 7, &reads).unwrap()
}

// Two legal period-two rings have widths 4+4: storage and arrivals each have eight
// coordinates, the width-two contact has four, and the loaded ring has eight.
const HELD_FIXTURE_PARAMETERS: usize = 3 * 2 * 2;
const HELD_FIXTURE_STATE_COORDINATES: usize = 2 * (4 + 4) + 2 * 2 + 2 * 4;
const HELD_FIXTURE_RATIOS: usize = HELD_FIXTURE_PARAMETERS * HELD_FIXTURE_STATE_COORDINATES;

/// Small fixed physical law fixture: twelve contact-factor coordinates, twenty-eight full-state
/// coordinates. Its maps/material are declared before either observation; no output is authored.
fn held_variation_fixture() -> (Field,Constitution,WordOpening,ReceiverDeclaration) {
    use crate::hnn::propagation::Operands;
    use crate::hnn::ring::{PumpDeclaration,PumpStep,ResonatorMaterial};
    use crate::hnn::word::{EndChange,Word};
    use crate::holon::parametron::Carrier as ParametronCarrier;
    use crate::ratio::linear::ExactRatMatrix;
    let declared = receiver();
    let field = Field::declare(FieldDeclaration {
        rings:vec![ring(2,vec![0,1]),ring(2,vec![])], contacts:vec![contact(0,1,1,0)],
        loops:vec![],sources:vec![0],offsets:vec![],alphabet:2,step:integer(1),exponent_grain:1,
        receivers:vec![declared.clone()],crib:CribDeclaration { window:16,offset:1 },
        population:1<<16,lattice:Default::default(),
    }.by_lattice_rule()).unwrap();
    let mut theta = Constitution::initial(&field,CAMPAIGN_ONE_BUDGET).unwrap();
    for g in 0..2 {
        let n = field.ring(g).width();
        let zero = ExactRatMatrix::zero(n,n).unwrap();
        theta = theta.with_element(g,zero.clone(),zero,
            vec![(vec![integer(0);n],vec![integer(0);n]);n]).unwrap();
    }
    let contact_factor = ExactRatMatrix::identity(2).unwrap();
    theta = theta.with_channel(0,contact_factor.clone(),contact_factor.clone(),contact_factor).unwrap();
    // Fixed two-class complex contrast R(z_0,z_1)=(z_0-z_1,z_1-z_0), packed
    // [Re_0,Im_0,Re_1,Im_1]. Both classes exist before any observed comparison.
    let map = ExactRatMatrix::new(vec![vec![integer(1),integer(0),integer(-1),integer(0)],
        vec![integer(0),integer(1),integer(0),integer(-1)],
        vec![integer(-1),integer(0),integer(1),integer(0)],
        vec![integer(0),integer(-1),integer(0),integer(1)]]).unwrap();
    theta = theta.with_ports(0,None,None,Some(map)).unwrap();
    let ring_factor = ExactRatMatrix::identity(field.ring(1).width()).unwrap();
    let pump = PumpDeclaration::new(rat(1,16),
        ParametronCarrier::new(integer(1),integer(0)).unwrap(),PumpStep::Half).unwrap();
    theta = theta.with_ring_resonator(&field,1,ResonatorMaterial::new(ring_factor.clone(),
        ring_factor.clone(),ring_factor,Some(pump)).unwrap()).unwrap();
    let ops = Operands::exact_at_cut(&field,&theta,&Current::at_rest(&field)).unwrap();
    let mut seed = EndChange::rest(&field,&ops);
    for x in seed.storage.iter_mut().chain(seed.arrivals.iter_mut().flatten())
        .chain(seed.states.iter_mut().flatten())
        .chain(seed.resonators.iter_mut().flatten().flatten()).flatten() { *x=rat(1,3); }
    let nothing = seed.storage.iter().map(|s| vec![integer(0);s.len()]).collect::<Vec<_>>();
    // Fixed initial motion at crossing 1: this is not a fitted prior or a material history.
    let carry = Word::continuing(&field,ops,&seed,&nothing,1).unwrap().reception_end().unwrap();
    (field,theta,WordOpening::Received { carry,absorption:crate::hnn::word::Absorption::Nothing },declared)
}

#[test]
fn held_contact_variation_returns_the_delayed_full_state_credit() {
    use crate::hnn::physical::contact::ContactObservation;
    use crate::hnn::moment::SourceMoment;
    use crate::hnn::retention::Diamond;
    use crate::hnn::word::{Absorption,Word};
    use crate::hnn::word::variation::VariationBudget;
    use crate::ratio::linear::vector::dot;
    use std::sync::Arc;
    let (field,theta,opening,declared) = held_variation_fixture();
    let current = Current::at_rest(&field);
    let mut actual = PhysicalReceiver::new(&field,theta.clone(),current.clone(),opening.clone()).unwrap();
    let budget = VariationBudget { ratios:HELD_FIXTURE_RATIOS,bits:1<<20,column_ticks:72 };
    let before = actual.opening();
    let admitted = actual.begin_held_contact_variation(budget).unwrap();
    assert_eq!(format!("{:?}",actual.opening()),format!("{before:?}"),"admission resets no primal coordinate");
    assert_eq!((admitted.parameters,admitted.state_coordinates,admitted.retained_ratios),
        (HELD_FIXTURE_PARAMETERS,HELD_FIXTURE_STATE_COORDINATES,HELD_FIXTURE_RATIOS));
    let first_source = encoded(&field,&[0]);
    let first = actual.communicate_contact(&first_source,&declared,|_| None).unwrap();
    assert!(first.closes());
    assert!(first.comparison.unwrap().is_none());
    assert!(first.held_comparison.unwrap().is_none());
    let resident = actual.into_resident();
    let columns = resident.held_contact_variation().unwrap().columns().to_vec();
    assert!(columns.iter().any(|chi| chi.arrivals.iter().flatten().flatten().any(|x| !x.is_zero())));
    assert!(columns.iter().any(|chi| chi.states.iter().flatten().flatten().any(|x| !x.is_zero())));
    assert!(columns.iter().any(|chi| chi.resonators.iter().flatten().flatten().flatten().any(|x| !x.is_zero())));
    let mut actual = PhysicalReceiver::from_resident(&field,resident).unwrap();
    let second = actual.communicate_contact(&encoded(&field,&[1]),&declared,|blind| {
        assert!(!blind.readings().is_empty());
        Some(ContactObservation { observed:encoded(&field,&[1,0,1]),compared:vec![false,true,true] })
    }).unwrap();
    assert!(second.closes());
    assert!(second.comparison.as_ref().unwrap().is_none(),"a differential is not a certified Deposit");
    let credit = second.held_comparison.as_ref().unwrap().as_ref().unwrap();
    assert!(credit.carried.iter().any(|x| !x.is_zero()),"the later observed ratio reaches earlier material motion");
    assert_eq!(actual.constitution(),&theta);
    assert_eq!(second.carry,second.blind_carry);
    assert_eq!(credit.reading.words,2);
    assert_eq!(credit.reading.column_ticks,72);
    assert_eq!(credit.reading.next_tick,7);
    assert_eq!(second.carry.change.resonator_phases[1],Some(0));
    // Full dual versus storage-only: the prior source storage is replaced, while arrival,
    // contact and loaded coordinates still contribute to this observed comparison.
    let storage_only:Vec<_> = columns.iter().map(|chi| credit.opening.storage.iter()
        .zip(&chi.storage).enumerate().filter(|(g,_)| !field.sources().contains(g))
        .map(|(_, (a,b))| dot(a,b)).sum::<crate::ratio::Rat>()).collect();
    assert_ne!(credit.carried,storage_only);
    for (index,chi) in columns.iter().enumerate() {
        let mut opened = chi.clone();
        for &g in field.sources() { opened.storage[g].fill(integer(0)); }
        assert_eq!(credit.carried[index],credit.opening.pairing(&opened));
    }
    // Independent two-Word reverse-chain oracle. Only this finite control temporarily
    // reconstructs the first Word; no production history/Word is retained or replayed.
    let section = DamagedSection::of_runs(3,&first_source,vec![(0,first_source.clone())]).unwrap();
    let mut source = SourceMoment::open_with(&field,&current,&theta).unwrap();
    for &g in field.sources() {
        source = source.station_section(&field,&current,g,&section.placed()).unwrap();
    }
    let (mut prior,source_receipt) = Word::open_source_exact_received(&field,&theta,&current,Arc::new(source),&opening).unwrap();
    prior.run(3).unwrap();
    assert!(source_receipt.closes());
    assert_eq!(prior.reception_end().unwrap(),first.carry);
    let mut end_dual = credit.opening.clone();
    for &g in field.sources() { end_dual.storage[g].fill(integer(0)); }
    let (prior_back,_) = prior.pull_back_continuing(vec![None;3],0,Some(&end_dual)).unwrap();
    let phases = ReceivingPhases::declare(&field,&theta,&current,&declared).unwrap();
    let diamond = Diamond::opened(&field,&phases,&opening.support(&field));
    let (_,prior_pull) = crate::hnn::reference::compose_contact(&field,&theta,&prior_back,&diamond,
        &|_| false,current.lift(),field.step(),0).unwrap();
    for (i,coordinate) in credit.coordinates.iter().enumerate() {
        let form = [&prior_pull.storage,&prior_pull.stiffness,&prior_pull.dissipation][coordinate.family];
        assert_eq!(credit.carried[i],*form.get(coordinate.row,coordinate.column).unwrap());
        assert_eq!(credit.total[i],&credit.within_word[i]+&credit.carried[i]);
    }
    let resident = actual.into_resident();
    // Derived canonical momentum tangents introduce no independent state or double count.
    let c = crate::hnn::field::ConstitutionRead::contact_storage(&theta,0);
    let capacity = c.multiply(&c.transpose().unwrap()).unwrap();
    assert_eq!(capacity.apply(&second.carry.change.states[0][1]).unwrap(),second.carry.momenta[0]);
    assert!(resident.state_bits() >= credit.reading.retained_bits);
    assert_eq!(resident.held_contact_variation().unwrap().reading(),&credit.reading);
    assert!(matches!(resident.reception_opening(),WordOpening::Received { absorption:Absorption::Nothing,.. }));
    let before_bits = resident.state_bits();
    let before_carry = resident.carried().cloned();
    let mut actual = PhysicalReceiver::from_resident(&field,resident).unwrap();
    let mut observed = false;
    assert!(actual.communicate_contact(&encoded(&field,&[0]),&declared,|_| { observed=true;None }).is_err());
    assert!(!observed);
    let resident = actual.into_resident();
    assert_eq!(resident.state_bits(),before_bits);
    assert_eq!(resident.carried(),before_carry.as_ref());
    assert_eq!(resident.held_contact_variation().unwrap().reading().words,2);
    println!("held two-Word actual differential: {:?}",credit.reading);
}

#[test]
fn held_contact_variation_refuses_untransported_future_without_clearing_it() {
    use crate::hnn::word::variation::VariationBudget;
    let (field,theta,opening,declared) = held_variation_fixture();
    let mut incorrect = opening.clone();
    if let WordOpening::Received { carry,.. } = &mut incorrect { carry.momenta[0][0] += integer(1); }
    let mut refused = PhysicalReceiver::new(&field,theta.clone(),Current::at_rest(&field),incorrect).unwrap();
    assert!(refused.begin_held_contact_variation(VariationBudget { ratios:HELD_FIXTURE_RATIOS,bits:1<<20,column_ticks:72 }).is_err());
    assert!(refused.into_resident().held_contact_variation().is_none());
    let mut incorrect_phase = opening.clone();
    if let WordOpening::Received { carry,.. } = &mut incorrect_phase { carry.change.resonator_phases[1] = Some(1); }
    let mut refused = PhysicalReceiver::new(&field,theta.clone(),Current::at_rest(&field),incorrect_phase).unwrap();
    assert!(refused.begin_held_contact_variation(VariationBudget { ratios:HELD_FIXTURE_RATIOS,bits:1<<20,column_ticks:72 }).is_err());
    let mut actual = PhysicalReceiver::new(&field,theta,Current::at_rest(&field),opening).unwrap();
    actual.begin_held_contact_variation(VariationBudget { ratios:HELD_FIXTURE_RATIOS,bits:1<<20,column_ticks:0 }).unwrap();
    let mut resident = actual.into_resident();
    let carry = resident.carried().cloned();
    let bits = resident.state_bits();
    let factor = crate::ratio::linear::ExactRatMatrix::identity(2).unwrap();
    let foreign = resident.constitution().clone().with_channel(0,
        factor.scaled(&integer(2)),factor.clone(),factor).unwrap();
    assert_eq!(foreign.commit(),resident.constitution().commit(),"commit alone does not stamp the material point");
    assert!(!resident.held_contact_variation().unwrap().matches(&foreign,resident.carried().unwrap()));
    assert!(resident.refine_contact_grain(1).is_err());
    assert!(resident.continuing_state(0).is_err());
    assert_eq!(resident.carried(),carry.as_ref());
    assert_eq!(resident.state_bits(),bits);
    assert!(resident.held_contact_variation().is_some());
    let mut actual = PhysicalReceiver::from_resident(&field,resident).unwrap();
    let mut called = false;
    assert!(actual.communicate_contact(&encoded(&field,&[0]),&declared,|_| { called=true;None }).is_err());
    assert!(!called,"the fixed column-tick budget refuses before the blind passage/observation");
    let mut resident = actual.into_resident();
    assert_eq!(resident.carried(),carry.as_ref());
    assert_eq!(resident.state_bits(),bits);
    let ended = resident.end_held_contact_variation().unwrap();
    assert_eq!(ended.words,0);
    assert_eq!(resident.carried(),carry.as_ref(),"explicit derivative-future retirement keeps the physical point");
}

/// A mechanical integration control of the existing consumer, not scientific acquisition.
/// It crosses three real Constitution publications without ending/restarting the derivative.
/// Actual coarse factor movement is read separately from normalization and unresolved material.
#[test]
fn continuing_contact_comparison_deposits_and_rebases_without_resetting_delayed_credit() {
    use crate::hnn::constitution::{FactorGradient,Family};
    use crate::hnn::physical::contact::ContactObservation;
    use crate::hnn::word::variation::{ContactVariationAction,VariationBudget};
    use crate::ratio::linear::ExactRatMatrix;
    let (field,theta,opening,declared) = held_variation_fixture();
    let current = Current::at_rest(&field);
    let mut actual = PhysicalReceiver::new(&field,theta,current.clone(),opening).unwrap();
    // Five full three-tick passages, twelve columns each; no admission changes mid-run.
    actual.begin_continuing_contact_variation(VariationBudget {
        ratios:HELD_FIXTURE_RATIOS,bits:1<<20,column_ticks:180,
    }).unwrap();
    let blind = actual.communicate_contact(&encoded(&field,&[0]),&declared,|_|None).unwrap();
    assert!(blind.closes());
    assert!(blind.held_publication.unwrap().is_none());
    let mut actual_factor_moves = 0usize;
    for passage in 0..3 {
        let before_material = actual.constitution().clone();
        let class = (passage+1)%2;
        let source = encoded(&field,&[class]);
        let observed = encoded(&field,&[class,1-class,class]);
        let mut saw_blind = false;
        let result = actual.communicate_contact(&source,&declared,|boundary| {
            saw_blind = true;
            assert!(!boundary.readings().is_empty());
            Some(ContactObservation { observed,compared:vec![false,true,true] })
        }).unwrap();
        assert!(saw_blind);
        assert!(result.closes());
        let credit = result.held_comparison.as_ref().unwrap().as_ref().unwrap();
        let publication = result.held_publication.as_ref().unwrap().as_ref().unwrap();
        assert_eq!(credit.producing_commit,before_material.commit());
        assert_eq!(credit.action,ContactVariationAction::RealizedFactorTranslation);
        assert!(credit.carried.iter().any(|x| !x.is_zero()));
        for (i,coordinate) in credit.coordinates.iter().enumerate() {
            assert_eq!(credit.total[i],&credit.within_word[i]+&credit.carried[i]);
            if let Some(step) = publication.comparison_return.factors().iter().find(|s|
                s.gradient.locus()==crate::hnn::constitution::Locus::Channel(coordinate.contact)
                    && s.gradient.family()==Family::Factor(coordinate.family)) {
                let gradient = match &step.gradient {
                    FactorGradient::Storage { gradient,.. } |
                    FactorGradient::Stiffness { gradient,.. } |
                    FactorGradient::Dissipation { gradient,.. } => gradient,
                    _ => unreachable!(),
                };
                assert_eq!(gradient.get(coordinate.row,coordinate.column).unwrap(),&-credit.total[i].clone());
                let metric = credit.metric.iter().find(|m|
                    m.contact==coordinate.contact && m.family==Family::Factor(coordinate.family)).unwrap();
                assert_eq!(step.energy,&metric.within_word_energy+&metric.opening_column_power);
                assert_eq!(step.covector,&metric.within_word_covector+&metric.opening_dual_bound);
            }
        }
        assert_eq!(publication.parameter_transport,ExactRatMatrix::identity(12).unwrap());
        assert_eq!(publication.rebase.words,passage+2);
        assert_eq!(publication.rebase.column_ticks,(passage+2)*36);
        assert_eq!(result.carry.ticks,1+(passage+2)*3);
        assert_eq!(result.carry.momenta,result.blind_carry.momenta);
        assert_eq!(result.carry.change.resonator_phases,result.blind_carry.change.resonator_phases);
        assert_ne!(actual.constitution(),&before_material,"the actual reached normalization/carry/material is published");
        actual_factor_moves += publication.continuation.material.iter()
            .filter(|m| m.factor.entries().iter().any(|x| !x.is_zero())).count();
        let resident = actual.into_resident();
        assert_eq!(resident.current(),&current,"the declared station-section source lift is a distinct clock");
        assert_eq!(resident.carried(),Some(&result.carry));
        let retained = resident.held_contact_variation().unwrap();
        assert!(retained.matches(resident.constitution(),&result.carry));
        assert_eq!(retained.reading(),&publication.rebase);
        assert!(retained.columns().iter().any(|chi|
            chi.states.iter().flatten().flatten().any(|x| !x.is_zero())));
        actual = PhysicalReceiver::from_resident(&field,resident).unwrap();
    }
    let final_blind = actual.communicate_contact(&encoded(&field,&[1]),&declared,|_|None).unwrap();
    assert!(final_blind.closes());
    assert!(final_blind.held_comparison.unwrap().is_none());
    assert!(final_blind.held_publication.unwrap().is_none());
    let resident = actual.into_resident();
    assert_eq!(resident.held_contact_variation().unwrap().reading().words,5);
    assert_eq!(resident.held_contact_variation().unwrap().reading().column_ticks,180);
    assert_eq!(resident.carried().unwrap().ticks,16);
    // Read the actual coarse reaction; no relation-level output claim from a statistic move.
    println!("continuing physical publications=3 actual_factor_families_moved={actual_factor_moves}");
}

/// Mechanical finite variations use the actual contact decoder and complete loaded Word.
/// The fixed samples challenge the certificate; its uniform ray argument is the factor
/// triangle/Gram law, not an empirical claim inferred from these samples.
#[test]
fn finite_loaded_span_carries_the_actual_contact_response_at_its_clock() {
    use crate::hnn::constitution::Reach;
    use crate::hnn::propagation::{Operands, participation, transit};
    use crate::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
    use crate::hnn::word::{EndChange, Word};
    use crate::hnn::word::finite_gain::FiniteContactSpans;
    use crate::holon::parametron::Carrier as ParametronCarrier;
    use crate::ratio::linear::ExactRatMatrix;
    use crate::ratio::linear::vector::{dot, scale, sub};
    let field = field();
    let current = Current::at_rest(&field);
    let width = field.contact(0).width();
    let factor = ExactRatMatrix::identity(width).unwrap();
    let ring_factor = ExactRatMatrix::identity(field.ring(0).width()).unwrap();
    let pump = PumpDeclaration::new(rat(1,16),
        ParametronCarrier::new(integer(1),integer(0)).unwrap(),PumpStep::Half).unwrap();
    let zeros=vec![integer(0);field.ring(0).width()];
    let base = material(&field).with_element(0,ExactRatMatrix::zero(zeros.len(),zeros.len()).unwrap(),
        ring_factor.scaled(&rat(1,3)),vec![(zeros.clone(),zeros);field.ring(0).width()]).unwrap()
        .with_channel(0,factor.clone(),factor.clone(),factor.clone()).unwrap()
        .with_ring_resonator(&field,0,ResonatorMaterial::new(ring_factor.clone(),ring_factor.clone(),
            ring_factor,Some(pump)).unwrap()).unwrap();
    let old = Operands::exact_at_cut(&field,&base,&current).unwrap();
    let moved = base.clone().with_channel(0,factor.scaled(&integer(2)),factor.clone(),factor.clone()).unwrap();
    let new = Operands::exact_at_cut(&field,&moved,&current).unwrap();
    let outgoing_g = vec![rat(1,3);field.ring(0).width()];
    let outgoing_h = vec![rat(-1,5);field.ring(1).width()];
    let u = vec![rat(1,7);width];
    let w = vec![rat(-1,11);width];
    let before = transit(&old.contacts()[0],field.step(),&outgoing_g,&outgoing_h,&u,&w).unwrap();
    let after = transit(&new.contacts()[0],field.step(),&outgoing_g,&outgoing_h,&u,&w).unwrap();
    let eta = sub(&after.midpoint,&before.midpoint);
    let delta_c = new.contacts()[0].forms().0.subtract(old.contacts()[0].forms().0).unwrap();
    let forcing = scale(&integer(2),&delta_c.apply(&sub(&w,&before.midpoint)).unwrap());
    let g = old.contacts()[0].conductance();
    // Geometry equation (13), in the native normalized operator m=(G/2h) M.
    assert_eq!(scale(&(integer(2)*field.step()/g),&new.contacts()[0].operator().apply(&eta).unwrap()),forcing);
    assert_eq!(sub(&after.displacement,&before.displacement),scale(field.step(),&eta));
    assert_eq!(sub(&after.rate,&before.rate),scale(&integer(2),&eta));
    assert!(eta.iter().any(|x| !x.is_zero()));
    let mut response = EndChange::rest(&field,&new);
    response.arrivals[0] = [sub(&after.arrive_from,&before.arrive_from),sub(&after.arrive_to,&before.arrive_to)];
    response.states[0] = [sub(&after.displacement,&before.displacement),sub(&after.rate,&before.rate)];
    // This is a test of one produced response, not a replacement for retained material.
    let reach = Reach { receiver:0,stations:vec![1,2,3],entries:vec![0],phases:1,
        loci:crate::hnn::retention::loci(&field).into_iter().collect() };
    let spans = FiniteContactSpans::of(&new,0,&reach).unwrap();
    let reading = spans.read(&[(integer(4),integer(1))]).unwrap();
    assert_eq!(reading.station_sum,integer(3)+integer(2)*&reading.gamma[1]
        + &reading.gamma[1]*&reading.gamma[2]);
    let zeta = scale(&(integer(2)*field.step()/g),&eta);
    let input = dot(&forcing,&forcing);
    assert!(dot(&zeta,&zeta)<=input,"the actual successor normalized resolvent is contractive");
    let nothing: Vec<_> = response.storage.iter().map(|s| vec![integer(0);s.len()]).collect();
    let mut word = Word::continuing(&field,new.clone(),&response,&nothing,1).unwrap();
    let mut product = integer(1);
    let mut actual_directional = integer(0);
    for j in 1..=3 {
        let state = word.change().unwrap();
        let arrivals: Vec<&[crate::ratio::Rat]> = new.incident(0).iter()
            .map(|&a| state.arrivals[a][new.end_slot(a,0)].as_slice()).collect();
        let anchor = participation(new.weights(0),&state.storage[0],&arrivals).unwrap();
        let actual = dot(&anchor,&anchor);
        assert!(actual <= &reading.receiving_projection*&reading.contact_injection[0]*&product*&input);
        actual_directional += actual;
        if j<3 { assert!(word.tick().unwrap().closes()); product *= &reading.gamma[j]; }
    }
    assert!(actual_directional < &reading.receiving_projection*&reading.contact_injection[0]*&reading.station_sum*&input,
        "the actual directional read can be tighter than the uniform product; neither is an eta improvement claim");
    // A nontrivial simultaneous factor ray: C/K rise, D falls but remains Gram-positive.
    // The whole-state stage includes nonzero waves, contact state and loaded state.
    for lambda in [integer(0),rat(1,2),integer(1)] {
        let ray = base.clone().with_channel(0,factor.scaled(&(integer(1)+&lambda)),
            factor.scaled(&(integer(1)+&lambda)),factor.scaled(&(integer(1)-&lambda/integer(2)))).unwrap();
        let operands = Operands::exact_at_cut(&field,&ray,&current).unwrap();
        for opened_at in [0,1] {
            let witness = FiniteContactSpans::of(&operands,opened_at,&reach).unwrap()
                .read(&[(integer(4),integer(4))]).unwrap();
            let mut state = EndChange::rest(&field,&operands);
            for x in state.storage.iter_mut().flatten()
                .chain(state.arrivals.iter_mut().flatten().flatten())
                .chain(state.states.iter_mut().flatten().flatten())
                .chain(state.resonators.iter_mut().flatten().flatten().flatten()) { *x=rat(1,3); }
            let norm = |state:&EndChange| {
                let mut sum:crate::ratio::Rat = state.storage.iter().flatten()
                    .chain(state.arrivals.iter().flatten().flatten()).map(|x|x*x).sum();
                for (xs,(u,w)) in state.states.iter().zip(&witness.contact_coordinates) {
                    sum += xs[0].iter().map(|x|(x/u)*(x/u)).sum::<crate::ratio::Rat>();
                    sum += xs[1].iter().map(|x|(x/w)*(x/w)).sum::<crate::ratio::Rat>();
                }
                for (xs,scales) in state.resonators.iter().zip(&witness.ring_coordinates) {
                    if let (Some(xs),Some((u,w)))=(xs,scales) {
                        sum += xs[0].iter().map(|x|(x/u)*(x/u)).sum::<crate::ratio::Rat>();
                        sum += xs[1].iter().map(|x|(x/w)*(x/w)).sum::<crate::ratio::Rat>();
                    }
                }
                sum
            };
            let before = norm(&state);
            let mut word = Word::continuing(&field,operands.clone(),&state,&nothing,opened_at).unwrap();
            assert!(word.tick().unwrap().closes());
            assert!(norm(&word.change().unwrap()) <= &witness.gamma[0]*before);
        }
    }
}

#[test]
fn native_contact_step_consumes_the_finite_loaded_span_witness() {
    use crate::hnn::constitution::Locus;
    use crate::hnn::physical::contact::ContactObservation;
    let field=field();
    let mut actual=PhysicalReceiver::new(&field,contact_material(&field),
        Current::at_rest(&field),WordOpening::Rest).unwrap();
    let receipt=actual.communicate_contact(&encoded(&field,&[0,1]),&receiver(), |_| {
        Some(ContactObservation { observed:encoded(&field,&[0,1,3]),compared:vec![false,false,true] })
    }).unwrap();
    assert!(receipt.closes());
    let publication=&receipt.comparison.as_ref().unwrap().as_ref().unwrap().publication;
    let witness=publication.loaded.as_ref().expect("actual contact selector consumes its finite witness");
    assert!(publication.pumped.is_none());
    assert_eq!(witness.opened_at,0);
    assert_eq!(witness.stations,vec![2]);
    assert_eq!(witness.station_sum,integer(1)+&witness.gamma[1]);
    for (locus,step) in &publication.steps {
        let Locus::Channel(a)=*locus else { panic!("native contact-only comparison"); };
        assert_eq!(step.gain,witness.gain(a,&step.readout));
    }
}

/// Trace the fixed v79 observation through its actual return, two carry resolutions and
/// producer/current publication. It changes no acceptance, fixture, material or future read.
fn contact_causal_receipt(before: &Constitution, after: &Constitution,
    publication: &crate::hnn::physical::contact::ContactPublication) {
    use crate::hnn::constitution::{Carrier, FactorGradient, Family, Locus, gamma_length};
    use crate::ratio::Rat;
    use num_traits::Signed;
    let locus = Locus::Channel(0);
    assert_eq!(publication.comparison_return.commit(), before.commit());
    assert_eq!(publication.publication.commit, after.commit());
    let movement = publication.continuation.material.iter()
        .find(|m| m.contact == 0 && m.family == Family::Factor(0)).unwrap();
    assert_eq!(before.contact_storage(0).add(&movement.factor).unwrap(),
        *after.contact_storage(0), "the producer's actual factor reaches the resident unchanged");
    let old_capacity = before.contact_storage(0).multiply(&before.contact_storage(0).transpose().unwrap()).unwrap();
    let new_capacity = after.contact_storage(0).multiply(&after.contact_storage(0).transpose().unwrap()).unwrap();
    assert_eq!(new_capacity.subtract(&old_capacity).unwrap(), movement.form);
    let steps = publication.comparison_return.factors().iter().filter(|s| {
        matches!(s.gradient, FactorGradient::Storage { contact: 0, .. })
    }).collect::<Vec<_>>();
    assert_eq!(steps.len(), 1, "compose_contact emits one complete Storage return per contact");
    let step = steps[0];
    let FactorGradient::Storage { gradient, .. } = &step.gradient else { unreachable!() };
    let eta = publication.publication.family_step(locus, Family::Factor(0));
    let statistic = &after.contact_scales(0)[0];
    let proposed = gradient.scaled(&(&eta / statistic));
    let prior = before.carried_remainders();
    let next = after.carried_remainders();
    let carried = |xs: &[(Locus, Carrier, usize, Rat)], carrier, entry| {
        xs.iter().filter(|(l,c,i,_)| *l==locus && *c==carrier && *i==entry)
            .map(|(_,_,_,r)| r.clone()).sum::<Rat>()
    };
    let scale_release = publication.publication.released.iter()
        .filter(|(l,c,i,_)| *l==locus && *c==Carrier::FactorScale(0) && *i==0)
        .map(|(_,_,_,r)| r.clone()).sum::<Rat>();
    assert_eq!(&step.energy + carried(&prior,Carrier::FactorScale(0),0),
        statistic - &before.contact_scales(0)[0] + carried(&next,Carrier::FactorScale(0),0) + scale_release,
        "the reached energy splits into applied statistic, retained and released parts");
    let half_unit = before.lattice(locus).unwrap().unit() / integer(2);
    for (i, (delta, applied)) in proposed.entries().iter().zip(movement.factor.entries()).enumerate() {
        let released = publication.publication.released.iter()
            .filter(|(l,c,j,_)| *l==locus && *c==Carrier::Factor(0) && *j==i)
            .map(|(_,_,_,r)| r.clone()).sum::<Rat>();
        assert_eq!(delta + carried(&prior,Carrier::Factor(0),i), applied + carried(&next,Carrier::Factor(0),i) + released,
            "the actual proposed factor displacement splits into applied, retained and released parts");
        let remainder = carried(&next,Carrier::Factor(0),i);
        assert!(-&half_unit <= remainder && remainder < half_unit,
            "the coarse remainder uses the half-open cell with ties upward");
    }
    let largest = proposed.entries().iter().map(Signed::abs).max().unwrap_or_else(Rat::zero);
    let largest_with_prior = proposed.entries().iter().enumerate()
        .map(|(i,d)| (d + carried(&prior,Carrier::Factor(0),i)).abs()).max().unwrap_or_else(Rat::zero);
    println!("v79 fixed causal receipt: before_commit={} after_commit={} aggregate_stepped={} unit={} clock_before={} clock_after={} precision={} eta={} gradient_squared={} reached_energy={} reached_covector={} scale_before={} scale_after={} largest_proposed={} largest_with_prior={} joint={:?} family_steps={:?} pumped={:?} vanished={:?} released={:?} carried_before={:?} carried_after={:?} actual_storage={:?} work={}",
        before.commit(), after.commit(), publication.publication.stepped, before.lattice(locus).unwrap().unit(),
        before.clock(locus), after.clock(locus), gamma_length(before.clock(locus)+1), eta,
        gradient.entries().iter().map(|x| x*x).sum::<Rat>(), step.energy, step.covector,
        before.contact_scales(0)[0], statistic, largest, largest_with_prior, publication.publication.joint,
        publication.publication.steps.iter().filter(|(l,_)| *l==locus).collect::<Vec<_>>(),
        publication.publication.pumped,
        publication.publication.vanished,
        publication.publication.released.iter().filter(|(l,_,_,_)| *l==locus).collect::<Vec<_>>(),
        prior.iter().filter(|(l,_,_,_)| *l==locus).collect::<Vec<_>>(),
        next.iter().filter(|(l,_,_,_)| *l==locus).collect::<Vec<_>>(), movement,
        publication.continuation.deposition_work);
}

#[test]
fn all_reached_contact_families_return_through_the_same_continuing_field() {
    use crate::hnn::constitution::{Carrier, FactorGradient, Family, Locus};
    use crate::hnn::physical::contact::ContactObservation;
    use crate::ratio::Rat;
    use crate::ratio::linear::vector::dot;
    let field = field();
    let mut actual = PhysicalReceiver::new(&field, contact_material(&field),
        Current::at_rest(&field), WordOpening::Rest).unwrap();
    for (source, target) in [([0,1], [0,1,3]), ([1,0], [1,0,2])] {
        let before = actual.constitution().clone();
        let entered = actual.opening();
        let receipt = actual.communicate_contact(&encoded(&field, &source), &receiver(), |_| {
            Some(ContactObservation { observed: encoded(&field, &target), compared: vec![false,false,true] })
        }).unwrap();
        assert!(receipt.closes());
        let publication = receipt.comparison.as_ref().unwrap().as_ref().unwrap();
        let after = actual.constitution();
        assert_eq!(publication.comparison_return.commit(), before.commit());
        assert_eq!(publication.publication.commit, after.commit());
        assert_eq!(publication.comparison_return.factors().len(), 3);
        assert_eq!(publication.continuation.material.len(), 3);
        let prior = before.carried_remainders();
        let next = after.carried_remainders();
        let carry = |xs: &[(Locus, Carrier, usize, Rat)], carrier, entry| xs.iter()
            .filter(|(l,c,i,_)| *l == Locus::Channel(0) && *c == carrier && *i == entry)
            .map(|(_,_,_,r)| r.clone()).sum::<Rat>();
        let released = |carrier, entry| publication.publication.released.iter()
            .filter(|(l,c,i,_)| *l == Locus::Channel(0) && *c == carrier && *i == entry)
            .map(|(_,_,_,r)| r.clone()).sum::<Rat>();
        for family in 0..3 {
            let step = &publication.comparison_return.factors()[family];
            assert_eq!(step.gradient.family(), Family::Factor(family));
            let (FactorGradient::Storage { gradient, .. }
                | FactorGradient::Stiffness { gradient, .. }
                | FactorGradient::Dissipation { gradient, .. }) = &step.gradient else {
                panic!("the actual comparison returns C/K/D factors");
            };
            assert!(gradient.entries().iter().any(|x| !x.is_zero()),
                "this fixed observation must actually reach each returned family");
            let movement = &publication.continuation.material[family];
            assert_eq!(movement.contact, 0);
            assert_eq!(movement.family, Family::Factor(family));
            assert_eq!(movement.linear.add(&movement.quadratic).unwrap(), movement.form);
            let h = &after.contact_scales(0)[family];
            let eta = publication.publication.family_step(Locus::Channel(0), Family::Factor(family));
            let proposed = gradient.scaled(&(&eta / h)); // this fixture's signature is identity
            for (i, (delta, applied)) in proposed.entries().iter().zip(movement.factor.entries()).enumerate() {
                assert_eq!(delta + carry(&prior, Carrier::Factor(family), i),
                    applied + carry(&next, Carrier::Factor(family), i) + released(Carrier::Factor(family), i));
            }
            assert_eq!(&step.energy + carry(&prior, Carrier::FactorScale(family), 0),
                h - &before.contact_scales(0)[family] + carry(&next, Carrier::FactorScale(family), 0)
                    + released(Carrier::FactorScale(family), 0));
        }
        // This is the producing Word's actual physical dissipation, before this observation.
        // The next loop uses the already published material and current on a different source.
        let d = before.contact_dissipation(0);
        let dissipation = d.multiply(&d.transpose().unwrap()).unwrap();
        assert_eq!(publication.pullback.transits[0].len(), receipt.balances.len());
        for (index, (tick, balance)) in publication.pullback.transits[0].iter().zip(&receipt.balances).enumerate() {
            assert_eq!(tick.tick, index, "the adjoint and Diamond use this Word's local crossing");
            assert_eq!(balance.dissipation,
                field.step() * dot(&tick.midpoint, &dissipation.apply(&tick.midpoint).unwrap()));
        }
        let entering_tick = match entered { WordOpening::Rest => 0,
            WordOpening::Received { carry, .. } => carry.ticks };
        for reading in receipt.boundary.readings() {
            assert_eq!(reading.tick, entering_tick + reading.crossing,
                "the receiving boundary places this local crossing on the actual carried clock");
        }
        assert_eq!(receipt.carry.ticks, entering_tick + 3);
        assert_eq!(receipt.carry.momenta, receipt.blind_carry.momenta);
        assert!(after.exact_bits() <= after.budget());
        println!("whole C/K/D blind boundary: {:?}", receipt.boundary);
        println!("actual C/K/D applied material and held work: {:?}", publication.continuation);
        println!("actual C/K/D unresolved material: {:?}", publication.publication.unresolved_contact_material);
    }
    // Conservation and passage coupling do not establish a material/output gain. The spent
    // original seven-selector gate and its nonzero-C/output assertions remain unchanged.
}

#[test]
fn finite_signed_contact_reaction_holds_momentum_and_reaches_the_next_tick() {
    use crate::hnn::constitution::Family;
    use crate::hnn::propagation::Operands;
    use crate::hnn::word::{PowerForm, Word};
    use crate::hnn::word::continuation::ContactMaterialMove;
    use crate::ratio::linear::ExactRatMatrix;
    use crate::ratio::linear::vector::{add, dot, scale};
    let field = field();
    let current = Current::at_rest(&field);
    let width = field.contact(0).width();
    let identity = ExactRatMatrix::identity(width).unwrap();
    // A mechanical finite-action control, not a learning curriculum or a tuned output gate.
    // C and D are positive Gram forms; K has alternating positive/negative columns. Their
    // combined contact operator is admitted at the same h/G by the existing boost owner.
    let signs: Vec<_> = (0..width).map(|j| j % 2 == 0).collect();
    let before = material(&field).with_channel(0, identity.clone(), identity.clone(), identity.clone())
        .unwrap().with_contact_signature(&field, 0, signs.clone()).unwrap();
    let moved = identity.scaled(&integer(2));
    let after = before.clone().with_channel(0, moved.clone(), moved.clone(), moved.clone())
        .unwrap().with_contact_signature(&field, 0, signs).unwrap();
    let old_operands = Operands::exact_at_cut(&field, &before, &current).unwrap();
    let new_operands = Operands::exact_at_cut(&field, &after, &current).unwrap();
    let movements: Vec<_> = (0..3).map(|family| ContactMaterialMove::between(&before, &after,
        &old_operands, &new_operands, 0, Family::Factor(family)).unwrap()).collect();
    for movement in &movements {
        assert_eq!(movement.factor, identity);
        assert_eq!(movement.linear, movement.quadratic.scaled(&integer(2)));
        assert_eq!(movement.form, movement.quadratic.scaled(&integer(3)));
    }
    assert!(movements[1].form.get(1,1).unwrap() < &integer(0),
        "the full K reaction consumes the producing negative column");
    let mut source = PhysicalReceiver::new(&field, before.clone(), current.clone(), WordOpening::Rest).unwrap();
    let blind = source.communicate_contact(&encoded(&field, &[0,1]), &receiver(), |_| None).unwrap();
    assert!(blind.closes());
    let old = PowerForm::read(&field, &before, &current).unwrap();
    let new = PowerForm::read(&field, &after, &current).unwrap();
    let held = old.held(&new, &blind.carry.change).unwrap();
    let u = &blind.carry.change.states[0][0];
    let w = &blind.carry.change.states[0][1];
    let pi = &blind.carry.momenta[0];
    let wp = &held.change.states[0][1];
    assert_eq!(held.change.states[0][0], *u);
    assert_eq!(new_operands.contacts()[0].forms().0.apply(wp).unwrap(), *pi);
    let expected_work = (dot(pi, wp) - dot(pi, w)
        + dot(u, &movements[1].form.apply(u).unwrap())) / integer(2);
    assert_eq!(held.deposition, expected_work);
    assert_eq!(new.power(&held.change).unwrap() - old.power(&blind.carry.change).unwrap(), expected_work);
    let d_only = before.clone().with_channel(0, identity.clone(), identity, moved).unwrap();
    assert_eq!(old.held(&PowerForm::read(&field, &d_only, &current).unwrap(), &blind.carry.change)
        .unwrap().deposition, integer(0), "D is dissipative, not stored energy at this cut");
    let nothing: Vec<_> = held.change.storage.iter().map(|wave| vec![integer(0); wave.len()]).collect();
    let mut old_word = Word::continuing(&field, old_operands, &blind.carry.change, &nothing, blind.carry.ticks).unwrap();
    let mut new_word = Word::continuing(&field, new_operands, &held.change, &nothing, blind.carry.ticks).unwrap();
    let mut d_word = Word::continuing(&field, Operands::exact_at_cut(&field, &d_only, &current).unwrap(),
        &blind.carry.change, &nothing, blind.carry.ticks).unwrap();
    for word in [&mut old_word, &mut new_word, &mut d_word] {
        let entering = word.change().unwrap();
        let balance = word.tick().unwrap();
        let end = word.change().unwrap();
        let omega = scale(&rat(1,2), &add(&entering.states[0][1], &end.states[0][1]));
        assert_eq!(balance.dissipation,
            field.step() * dot(&omega, &word.operands().contacts()[0].forms().2.apply(&omega).unwrap()));
        assert!(balance.closes());
        assert_eq!(word.opened_at(), blind.carry.ticks);
    }
    assert_ne!(old_word.change().unwrap(), new_word.change().unwrap(),
        "the finite material reaction reaches a later actual field tick");
    assert_ne!(old_word.field_balances()[0].dissipation, d_word.field_balances()[0].dissipation,
        "D alone changes the subsequent actual dissipative work at matched entering state/time");
    println!("finite signed C/K/D reaction: {movements:?} held_work={expected_work}");
    println!("actual old/new/D-only next-tick balances: {:?} / {:?} / {:?}",
        old_word.field_balances(), new_word.field_balances(), d_word.field_balances());
}

#[test]
fn the_fixed_v79_contact_observation_accounts_for_its_actual_material_and_remainders() {
    use crate::hnn::physical::contact::ContactObservation;
    let field = field();
    let initial = contact_material(&field);
    let mut actual = PhysicalReceiver::new(&field, initial.clone(), Current::at_rest(&field), WordOpening::Rest).unwrap();
    let taught = actual.communicate_contact(&encoded(&field,&[0,1]), &receiver(), |_| {
        Some(ContactObservation { observed: encoded(&field,&[0,1,3]), compared: vec![false,false,true] })
    }).unwrap();
    assert!(taught.closes());
    contact_causal_receipt(&initial, actual.constitution(), taught.comparison.as_ref().unwrap().as_ref().unwrap());
    // This diagnostic proves the actual publication/split account, not the failed nonzero-C or
    // later-output gate. The original seven-selector acceptance remains failed and unchanged.
}

#[test]
fn the_actual_unresolved_contact_return_survives_a_different_physical_passage() {
    use crate::hnn::constitution::{Carrier, Family, Locus};
    use crate::hnn::physical::contact::ContactObservation;
    let field=field();
    let initial=contact_material(&field);
    let mut actual=PhysicalReceiver::new(&field,initial.clone(),Current::at_rest(&field),WordOpening::Rest).unwrap();
    let taught=actual.communicate_contact(&encoded(&field,&[0,1]),&receiver(), |_| {
        Some(ContactObservation { observed:encoded(&field,&[0,1,3]),compared:vec![false,false,true] })
    }).unwrap();
    assert!(taught.closes());
    let publication=taught.comparison.as_ref().unwrap().as_ref().unwrap();
    contact_causal_receipt(&initial,actual.constitution(),publication);
    let learned=actual.constitution().clone();
    let pending:Vec<_>=learned.carried_remainders().into_iter().filter(|(l,c,_,_)|
        *l==Locus::Channel(0) && matches!(c,Carrier::Factor(_) | Carrier::FactorScale(_))).collect();
    assert_eq!(pending,publication.publication.unresolved_contact_material);
    assert!(publication.publication.released.iter().all(|(_,c,_,_)|
        !matches!(c,Carrier::Factor(_) | Carrier::FactorScale(_))));
    // Conditioned on the actual sub-cell displacement (Epime's review, October 8): the storage
    // family's move stays below its cell exactly when the publication reads it as vanished, and
    // only then is the exact unresolved direction not an immediate physical storage move, with
    // every storage entry pending. complete_contact_return_publishes_held_point_before_existing_
    // communication demands that move on these same operands and stays the failed acceptance while
    // it vanishes; a move that leaves its cell is a physical storage move here too.
    if publication.publication.vanished.contains(&(Locus::Channel(0), Family::Factor(0))) {
        assert_eq!(pending.iter().filter(|(_,c,_,_)| *c==Carrier::Factor(0)).count(),
            initial.contact_storage(0).entries().len());
        assert_eq!(learned.contact_storage(0),initial.contact_storage(0),
            "exact unresolved direction is not an immediate physical storage move");
    } else {
        assert_ne!(learned.contact_storage(0),initial.contact_storage(0),
            "a storage move that left its cell is an immediate physical storage move");
    }
    assert!(learned.exact_bits() <= learned.budget());
    let ordinary=actual.communicate(&encoded(&field,&[1,0]),&receiver(), |_| None).unwrap();
    assert!(ordinary.closes());
    assert_eq!(actual.constitution(),&learned);
    let prior=actual.constitution().clone();
    let next=actual.communicate_contact(&encoded(&field,&[1,0]),&receiver(), |_| {
        Some(ContactObservation { observed:encoded(&field,&[1,0,2]),compared:vec![false,false,true] })
    }).unwrap();
    assert!(next.closes());
    let publication=next.comparison.as_ref().unwrap().as_ref().unwrap();
    contact_causal_receipt(&prior,actual.constitution(),publication);
    assert!(publication.publication.released.iter().all(|(_,c,_,_)|
        !matches!(c,Carrier::Factor(_) | Carrier::FactorScale(_))));
    println!("whole ordinary boundary carrying unresolved contact material: {:?}",ordinary.boundary);
    println!("whole next blind boundary with a different source: {:?}",next.boundary);
    println!("exact successor unresolved contact material: {:?}",publication.publication.unresolved_contact_material);
    println!("actual successor carrier costs: {:?}",actual.constitution().carrier_bits());
    // The second declared comparison consumes its own source and the same retained material;
    // contact_causal_receipt proves delta+r_old=dF+r_new exactly, including its normalization.
    // No changed grain/step, repeated teacher, storage-gain or useful-output assertion.
}

#[test]
fn complete_contact_return_publishes_held_point_before_existing_communication() {
    use crate::hnn::constitution::{Family, Locus};
    use crate::hnn::physical::contact::ContactObservation;
    let field = field();
    let initial = contact_material(&field);
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let mut actual = PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).unwrap();
    let mut untouched = PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).unwrap();
    let blind = untouched.communicate_contact(&source, &receiver(), |_| None).unwrap();
    let taught = actual.communicate_contact(&source, &receiver(), |boundary| {
        assert_eq!(boundary, &blind.boundary, "observation cannot enter its earlier forward");
        println!("whole complete blind contact boundary: {boundary:?}");
        Some(ContactObservation { observed: encoded(&field, &[0, 1, 3]), compared: vec![false, false, true] })
    }).unwrap();
    assert!(blind.closes() && taught.closes());
    assert_eq!(taught.boundary, blind.boundary);
    assert_eq!(taught.blind_carry, blind.carry);
    assert_eq!(taught.carry.ticks, 3, "full ticks keep their actual complete crossing");
    let publication = taught.comparison.as_ref().unwrap().as_ref().unwrap();
    contact_causal_receipt(&initial, actual.constitution(), publication);
    assert!(publication.publication.stepped > 0);
    // The first step's contract at the declared grain, corrected on October 8 (Epime's review;
    // the failed receipts of v85, v90 and v116-v118 are kept): a reached, certified form moves its
    // representative only when its move leaves its cell. Here the reached storage move is about
    // 2^-38 against the half-unit 2^-16 (the pin-2 owner diagnostic), so the publication reads
    // C, K and D as vanished and carries them exactly; the former `C_after != C_before` was a
    // false expectation at this grain. The stronger behaviour, material that moved felt by a later
    // output, is asserted below wherever the forms actually moved.
    let vanished = |family| publication.publication.vanished.contains(&(Locus::Channel(0), family));
    let formed = [
        (Family::Factor(0), actual.constitution().contact_storage(0) != initial.contact_storage(0)),
        (Family::Factor(1), actual.constitution().contact_stiffness(0) != initial.contact_stiffness(0)),
        (Family::Factor(2), actual.constitution().contact_dissipation(0) != initial.contact_dissipation(0)),
    ];
    for (family, moved) in formed {
        if vanished(family) {
            assert!(!moved, "a form whose reached move stays in its cell keeps its representative");
        }
    }
    let material_moved = formed.iter().any(|(_, moved)| *moved);
    println!("first-step forms moved: {formed:?}; vanished: {:?}", publication.publication.vanished);
    assert_eq!(taught.carry.momenta, taught.blind_carry.momenta);
    assert_eq!(taught.carry.change.states[0][0], taught.blind_carry.change.states[0][0]);
    assert_eq!(&publication.continuation.committed - &publication.continuation.before,
        publication.continuation.deposition_work);
    let material = actual.constitution().clone();
    let opening = actual.opening();
    let common = actual.into_resident();
    assert_eq!(common.constitution(), &material);
    assert_eq!(common.current(), &current);
    assert_eq!(common.carried(), Some(&taught.carry));
    assert!(common.carry_error().is_none());
    let mut actual = PhysicalReceiver::from_resident(&field, common).unwrap();
    // The actual production boundary consumes this current on a different source, without a
    // new contact comparison, expected target or retained Word. Controls share its entering end.
    let other_source = encoded(&field, &[2, 1]);
    let mut prior = PhysicalReceiver::new(&field, initial, current.clone(), opening.clone()).unwrap();
    let mut other = PhysicalReceiver::new(&field, material, current, opening).unwrap();
    let next = actual.communicate(&other_source, &receiver(), |_| None).unwrap();
    let old_material = prior.communicate(&other_source, &receiver(), |_| None).unwrap();
    let old_source = other.communicate(&source, &receiver(), |_| None).unwrap();
    assert!(next.closes() && old_material.closes() && old_source.closes());
    assert_eq!(next.carry.ticks, taught.carry.ticks + 2);
    // Material that moved is felt by the later output on the same entering end. While every
    // reached form stays in its cell, this is the declared unfinished capability (#73): landing a
    // reached contact move at this grain on the charted word (a law, representation or coupling
    // change), and the acceptance holds unasserted rather than claimed.
    if material_moved {
        assert_ne!(next.boundary.readings(), old_material.boundary.readings());
    }
    println!("later output equals the unmoved-material control: {}",
        next.boundary.readings() == old_material.boundary.readings());
    assert_ne!(next.boundary.readings(), old_source.boundary.readings());
    println!("whole carried existing communication boundary: {:?}", next.boundary);
}

// The held twin of 0279 on its own operands. Declared once, from the field, and never raised after a
// run: a refusal at them is the next loop's subject, not a larger limit. The width-six contact
// carries three raw 6 x 6 Gram factors (C, K, D): 3 * 6 * 6 = 108 = 2^2 * 3^3 parameters.
const LANDING_TANGENT_PARAMETERS: usize = 3 * 6 * 6;
// One Word's full state: storage (8 + 6), arriving waves (8 + 6) and the contact's (u, w) (6 + 6),
// with no loaded resonator: 40 = 2^3 * 5 coordinates, so 108 * 40 = 4320 = 2^5 * 3^3 * 5 retained
// ratios.
const LANDING_TANGENT_STATE_COORDINATES: usize = (8 + 6) + (8 + 6) + (6 + 6);
const LANDING_TANGENT_RATIOS: usize =
    LANDING_TANGENT_PARAMETERS * LANDING_TANGENT_STATE_COORDINATES;
// 0279's one Word executes three ticks (`taught.carry.ticks == 3`) and every tick moves every
// column: 108 * 3 = 324 = 2^2 * 3^4 column-ticks.
const LANDING_TANGENT_TICKS: usize = 3;
const LANDING_TANGENT_COLUMN_TICKS: usize = LANDING_TANGENT_PARAMETERS * LANDING_TANGENT_TICKS;

/// [agent-inferred, October 8; the medium-of-joints record, section 7] **The landing tangent read
/// beside the uniform certificate** on 0279's own operands. A CONDITIONAL DIAGNOSTIC, NEVER A
/// CERTIFIED LANDING: L1' is a candidate closer, `eps_ray` is uncertified, and a point tangent
/// cannot authorize a finite deposit. It changes no law and admits no step.
///
/// Per family `f` (C, K, D) the numerator is the certificate's own `kb_f = kappa^2 b` (the deposit's
/// `StepReading::gain * moves`; the step's curvature is `s kb_f` with `s = 1/2`) and the denominator
/// is `|A d_f|^2`, the squared response at the compared station to the deposit's unit step
/// `d_f = G_f / h'_f` (so `a_f = |G_f|^2 / h'_f` at the certificate's face). `A` is the held twin's
/// exact station response at the same producing material, current and Word; `G_f` and `h'_f` are the
/// actual deposit's descent direction and published statistic. The two are read in different charts
/// (kappa maps the contact right-hand-side streams; `A` maps raw factors to realified logits at
/// identity metrics), so the quotient reads whether the uniform certificate could be loose, and is
/// not a like-for-like bound. With `s = 1/2` and `eps_ray = 0` an own-certificate L1' admits
/// `eta = 2^-10` exactly when `|A d_f|^2 <= T_f = 2^11 a_f` (jointly, `|A (d_C + d_K + d_D)|^2 <=
/// 2^11 sum a_f`). A zero `|A d_f|^2` is a kernel or singular case, never a ratio.
///
/// The readings print first; the assertions that let them be trusted follow, so a failed assertion
/// leaves the readings visible but unverified.
fn landing_tangent_reading(
    before: &Constitution,
    after: &Constitution,
    actual: &crate::hnn::physical::contact::ContactPublication,
    twin: &crate::hnn::physical::contact::ContactCommunication,
    admitted: &crate::hnn::word::variation::VariationReading,
    compared: &[bool],
) {
    use crate::hnn::constitution::{FactorGradient, Family, Locus};
    use crate::holon::deposition::dyadic;
    use crate::ratio::Rat;
    use crate::ratio::disk::floor_log2;
    use crate::ratio::linear::vector::{add, dot};
    use num_traits::Signed;
    let locus = Locus::Channel(0);
    let names = ["C", "K", "D"];
    // The actual deposit: its certified steps, its descent directions and its published statistics.
    assert_eq!(actual.comparison_return.commit(), before.commit());
    assert_eq!(actual.publication.commit, after.commit());
    let scales = after.contact_scales(0);
    let steps: Vec<_> = (0..3)
        .map(|f| {
            actual
                .publication
                .steps
                .iter()
                .find(|(at, reading)| *at == locus && reading.family == Family::Factor(f))
                .map(|(_, reading)| reading)
                .unwrap_or_else(|| panic!("the actual deposit certified no family-{f} step"))
        })
        .collect();
    let gradients: Vec<_> = (0..3)
        .map(|f| {
            let step = actual
                .comparison_return
                .factors()
                .iter()
                .find(|s| s.gradient.locus() == locus && s.gradient.family() == Family::Factor(f))
                .unwrap_or_else(|| panic!("the actual deposit returned no family-{f} gradient"));
            match &step.gradient {
                FactorGradient::Storage { gradient, .. }
                | FactorGradient::Stiffness { gradient, .. }
                | FactorGradient::Dissipation { gradient, .. } => gradient,
                _ => unreachable!("a contact family returns a Gram-factor gradient"),
            }
        })
        .collect();
    // The held twin: its complete station response, and the rows of it at the compared stations.
    let response = twin
        .station_response
        .as_ref()
        .expect("the held twin returns its complete station response");
    assert_eq!(response.producing_commit, before.commit());
    let fallback;
    let selected = match &twin.compared_response {
        Some(selected) => selected,
        None => {
            fallback = response
                .select(compared)
                .expect("the compared stations select from the complete response");
            &fallback
        }
    };
    // The actual comparison's covector at the compared stations.
    let covector = actual
        .ratio
        .covector()
        .expect("the actual comparison's covector");
    let g: Vec<Rat> = compared
        .iter()
        .enumerate()
        .filter(|(_, picked)| **picked)
        .flat_map(|(station, _)| covector.logits()[station].iter().cloned())
        .collect();
    assert_eq!(
        g.len(),
        selected.matrix.rows(),
        "the covector and the selected rows share the compared stations"
    );
    // The family directions d_f = G_f / h'_f, in the response's own coordinate order.
    let directions: Vec<Vec<Rat>> = (0..3)
        .map(|f| {
            response
                .coordinates
                .iter()
                .map(|c| {
                    if c.contact == 0 && c.family == f {
                        gradients[f]
                            .get(c.row, c.column)
                            .expect("a returned gradient entry")
                            / &scales[f]
                    } else {
                        Rat::zero()
                    }
                })
                .collect()
        })
        .collect();
    // The owner's transpose identity A^T g = total, re-read against the actual descent direction
    // -G: how many coordinates of each family differ (none when the readings are sound).
    let transposed = match response.pullback(&covector) {
        Ok(pulled) => {
            let mut differing = [0usize; 3];
            for (c, got) in response.coordinates.iter().zip(&pulled) {
                let descent = gradients[c.family]
                    .get(c.row, c.column)
                    .expect("a returned gradient entry");
                if *got != -descent {
                    differing[c.family] += 1;
                }
            }
            format!(
                "A^T g differs from -G at {differing:?} coordinates of C, K, D (of {} each)",
                response.coordinates.len() / 3
            )
        }
        Err(refusal) => format!("A^T g was refused: {refusal:?}"),
    };
    let tangents: Vec<_> = directions
        .iter()
        .enumerate()
        .map(|(f, d)| {
            selected.directional(d).unwrap_or_else(|refusal| {
                panic!("family {f}: the directional response was refused: {refusal:?}")
            })
        })
        .collect();
    let sum_direction = add(&add(&directions[0], &directions[1]), &directions[2]);
    let joint = selected
        .directional(&sum_direction)
        .unwrap_or_else(|refusal| {
            panic!("the summed direction's response was refused: {refusal:?}")
        });
    // The certificate's numerator kb_f, |G_f|^2, and the threshold T_f = a_f / (s eta) = 2^11 a_f of
    // an own-certificate L1' with s = 1/2 and eps_ray = 0 at eta = 2^-10 (the record's landing step).
    assert_eq!(dyadic(11), integer(1) / (rat(1, 2) * dyadic(-10)));
    let numerators: Vec<Rat> = steps.iter().map(|step| &step.gain * &step.moves).collect();
    let gradient_squared: Vec<Rat> = gradients
        .iter()
        .map(|gradient| gradient.entries().iter().map(|x| x * x).sum::<Rat>())
        .collect();
    let thresholds: Vec<Rat> = steps
        .iter()
        .map(|step| dyadic(11) * &step.step.alignment)
        .collect();
    let sum_alignment: Rat = steps.iter().map(|step| step.step.alignment.clone()).sum();
    let joint_threshold = dyadic(11) * &sum_alignment;
    // The first dyadic step at which this family's largest entry move reaches the half-unit.
    let half_unit = before.lattice(locus).expect("the contact's lattice").unit() / integer(2);
    let widest: Vec<Rat> = directions
        .iter()
        .map(|d| {
            d.iter()
                .map(Signed::abs)
                .max()
                .expect("a direction has entries")
        })
        .collect();
    let first_reach: Vec<i64> = widest
        .iter()
        .map(|w| {
            assert!(w.is_positive(), "a certified step has a nonzero direction");
            let needed = &half_unit / w;
            let k = floor_log2(&needed);
            if dyadic(k) == needed { k } else { k + 1 }
        })
        .collect();
    let binary = |x: &Rat| -> String {
        if x.is_positive() {
            format!("{x} [floor_log2={}]", floor_log2(x))
        } else {
            format!("{x} [no binary exponent]")
        }
    };
    let credit = match &twin.held_comparison {
        Ok(Some(credit)) => Some(credit),
        _ => None,
    };
    let status = match &twin.held_comparison {
        Ok(Some(_)) => "returned (the owner checked A^T g = total)".to_string(),
        Ok(None) => "none".to_string(),
        Err(refusal) => format!("REFUSED, the readings below are UNVERIFIED: {refusal:?}"),
    };
    println!(
        "landing tangent CONDITIONAL DIAGNOSTIC, NOT A LANDING: L1' is a candidate closer, eps_ray is \
         uncertified, a point tangent cannot authorize a finite deposit, and no certified landing \
         exists. kb = kappa^2 b is the certificate's own numerator (contact right-hand-side streams); \
         |A d|^2 is the held twin's exact station response in identity raw-factor and realified-logit \
         charts: a reading beside it, never a like-for-like bound."
    );
    println!(
        "landing tangent twin: admitted={admitted:?} run={:?} compared_stations={:?} A_rows={} \
         A_columns={} |A|^2_enclosure=[{}, {}] held_comparison={status} transpose_identity: {transposed}",
        credit.map(|c| &c.reading),
        selected.station_ticks,
        selected.matrix.rows(),
        selected.matrix.columns(),
        selected.lower_squared,
        selected.upper_squared
    );
    for (f, step) in steps.iter().enumerate() {
        let kb = &numerators[f];
        let ad2 = &tangents[f].receiving_squared;
        let order = crate::ratio::compare(ad2, &thresholds[f]);
        let quotient = if ad2.is_zero() {
            "kernel/singular (|A d|^2 = 0): no ratio".to_string()
        } else if !kb.is_positive() {
            "numerator kb = 0: no ratio".to_string()
        } else {
            let rho = kb / ad2;
            let k = floor_log2(&rho);
            format!("rho={rho} floor_log2={k} remainder={}", &rho - dyadic(k))
        };
        println!(
            "landing tangent f={f} [{}] certificate: eta=2^{} a={} h'={} |G|^2={} max|d|={} \
             first_reach_eta=2^{} kb=kappa^2*b={}",
            names[f],
            step.step.exponent,
            binary(&step.step.alignment),
            scales[f],
            gradient_squared[f],
            binary(&widest[f]),
            first_reach[f],
            binary(kb)
        );
        println!(
            "landing tangent f={f} [{}] tangent: |A d|^2={} |d|^2={} kb/|A d|^2: {quotient}",
            names[f],
            binary(ad2),
            tangents[f].parameter_squared
        );
        println!(
            "landing tangent f={f} [{}] threshold: T=2^11*a={} needed kb/T={} |A d|^2<=T: {} (exact order {order:?}{})",
            names[f],
            binary(&thresholds[f]),
            binary(&(kb / &thresholds[f])),
            order.is_le(),
            if ad2.is_zero() {
                "; kernel/singular is not a favourable quotient"
            } else {
                ""
            }
        );
    }
    let joint_order = crate::ratio::compare(&joint.receiving_squared, &joint_threshold);
    println!(
        "landing tangent joint: |A(d_C+d_K+d_D)|^2={} |d_C+d_K+d_D|^2={} 2^11*sum(a)={} \
         |A d|^2<=T: {} (exact order {joint_order:?}{}) declared_landing_eta=2^-10 first_reach_eta=2^{}",
        binary(&joint.receiving_squared),
        joint.parameter_squared,
        binary(&joint_threshold),
        joint_order.is_le(),
        if joint.receiving_squared.is_zero() {
            "; kernel/singular is not a favourable quotient"
        } else {
            ""
        },
        first_reach.iter().max().expect("three families")
    );
    // The assertions that let the readings above be trusted.
    let credit = credit.unwrap_or_else(|| {
        panic!(
            "the held twin returned no comparison: {:?}",
            twin.held_comparison.as_ref().err()
        )
    });
    // The twin is the actual run's comparison on its own Word: the same coordinates and covector,
    // and a first Word from rest, which carries no earlier column.
    assert_eq!(credit.coordinates, response.coordinates);
    assert_eq!(credit.total.len(), response.coordinates.len());
    assert_eq!(
        credit.ratio.covector().expect("the twin's covector"),
        covector,
        "the twin compares what the actual run compared"
    );
    assert!(
        credit.carried.iter().all(Zero::is_zero),
        "a first Word from rest carries no earlier column"
    );
    response
        .check_pullback(&covector, &credit.total)
        .expect("A^T g = total, checked again on the actual covector");
    // The held total is -(d h') entrywise: the descent direction is -total and d_f = G_f / h'_f.
    for (i, c) in response.coordinates.iter().enumerate() {
        assert_eq!(
            credit.total[i],
            -(&directions[c.family][i] * &scales[c.family]),
            "coordinate {i} {c:?}"
        );
    }
    let mut sum_pairing = Rat::zero();
    for (f, step) in steps.iter().enumerate() {
        // The certificate's curvature is s kb with s = 1/2, so kb is the deposit's printed kappa^2 b.
        assert_eq!(
            &step.step.curvature * integer(2),
            numerators[f],
            "family {f}"
        );
        // sum_j g_j (A d_f)_j = total . d_f = -|G_f|^2 / h'_f, exactly.
        let pairing = &gradient_squared[f] / &scales[f];
        assert_eq!(dot(&g, &tangents[f].response), -&pairing, "family {f}");
        // a_f is that same |G_f|^2 / h'_f at the certificate's floor.
        assert!(
            crate::ratio::compare(&step.step.alignment, &pairing).is_le(),
            "family {f}"
        );
        sum_pairing += pairing;
    }
    assert_eq!(dot(&g, &joint.response), -sum_pairing);
    // The declared budget, derived once and never raised, against what the run reports.
    assert_eq!(
        (
            admitted.parameters,
            admitted.state_coordinates,
            admitted.retained_ratios
        ),
        (
            LANDING_TANGENT_PARAMETERS,
            LANDING_TANGENT_STATE_COORDINATES,
            LANDING_TANGENT_RATIOS
        )
    );
    assert_eq!(credit.reading.column_ticks, LANDING_TANGENT_COLUMN_TICKS);
    assert_eq!(
        (credit.reading.words, credit.reading.next_tick),
        (1, LANDING_TANGENT_TICKS)
    );
    assert!(credit.reading.retained_ratios <= LANDING_TANGENT_RATIOS);
    assert!(credit.reading.retained_bits <= CAMPAIGN_ONE_BUDGET);
    assert!(response.matrix.rows() * response.matrix.columns() <= LANDING_TANGENT_RATIOS);
    assert!(response.matrix_bits <= CAMPAIGN_ONE_BUDGET);
    println!(
        "landing tangent: every trust assertion passed; the readings above remain a conditional diagnostic"
    );
}

#[test]
fn the_landing_tangent_is_read_beside_the_uniform_certificate_on_the_complete_contact_return() {
    use crate::hnn::physical::contact::ContactObservation;
    use crate::hnn::word::variation::VariationBudget;
    let field = field();
    let initial = contact_material(&field);
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let compared = vec![false, false, true];
    let observation = || ContactObservation {
        observed: encoded(&field, &[0, 1, 3]),
        compared: compared.clone(),
    };
    // 0279's own runs: the blind forward, then the same Word with its comparison and deposit.
    let mut untouched =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).unwrap();
    let blind = untouched
        .communicate_contact(&source, &receiver(), |_| None)
        .unwrap();
    let started = std::time::Instant::now();
    let mut actual =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).unwrap();
    let taught = actual
        .communicate_contact(&source, &receiver(), |_| Some(observation()))
        .unwrap();
    let actual_ns = started.elapsed().as_nanos();
    // The held twin: the same operands and observation, with the exact station response.
    let started = std::time::Instant::now();
    let mut twin =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).unwrap();
    let admitted = twin
        .begin_held_contact_variation(VariationBudget {
            ratios: LANDING_TANGENT_RATIOS,
            bits: CAMPAIGN_ONE_BUDGET,
            column_ticks: LANDING_TANGENT_COLUMN_TICKS,
        })
        .expect("the held twin is admitted within its declared budget");
    let held = twin
        .communicate_contact(&source, &receiver(), |_| Some(observation()))
        .unwrap();
    let twin_ns = started.elapsed().as_nanos();
    assert!(blind.closes() && taught.closes() && held.closes());
    assert_eq!(
        taught.boundary, blind.boundary,
        "observation cannot enter its earlier forward"
    );
    assert_eq!(
        held.boundary, blind.boundary,
        "the held twin's boundary is the blind run's"
    );
    assert_eq!(held.blind_carry, blind.carry);
    assert_eq!(
        held.carry, held.blind_carry,
        "a fixed-material twin deposits nothing"
    );
    let publication = taught.comparison.as_ref().unwrap().as_ref().unwrap();
    landing_tangent_reading(
        &initial,
        actual.constitution(),
        publication,
        &held,
        &admitted,
        &compared,
    );
    println!(
        "landing tangent timing: actual_ns={actual_ns} twin_ns={twin_ns} \
         column_ticks={LANDING_TANGENT_COLUMN_TICKS}"
    );
}

// The learned-change acceptance, READ on 0279's own task (issue #73's gate; the medium-of-joints
// record, section 7). A reading, never an acceptance: it prints what the machine does and asserts
// only what makes its readings trustworthy.

/// An exact value beside its binary exponent: never a decimal or a float.
fn acceptance_exact(x: &crate::ratio::Rat) -> String {
    use num_traits::Signed;
    if x.is_zero() {
        "0".to_string()
    } else if x.is_positive() {
        format!("{x} [floor_log2={}]", crate::ratio::disk::floor_log2(x))
    } else {
        format!(
            "{x} [floor_log2 of the magnitude={}]",
            crate::ratio::disk::floor_log2(&-x)
        )
    }
}

fn acceptance_verdict(met: bool) -> &'static str {
    if met { "PASS" } else { "NOT-MET" }
}

/// One word's world accounting, from its own receipts and every term exact. The opening is
/// `E_after - E_before = imposed - absorbed`; the defects are the owner's executed residuals, each
/// within its certified bound.
struct AcceptanceWorld {
    moved: crate::ratio::Rat,
    supplied: crate::ratio::Rat,
    opening_gap: crate::ratio::Rat,
    ticks: usize,
    tick_defects: crate::ratio::Rat,
    tick_bound: crate::ratio::Rat,
    word_defects: crate::ratio::Rat,
    word_bound: crate::ratio::Rat,
    closes: bool,
}

fn acceptance_world(
    opening: &crate::hnn::word::SourceOpeningReceipt,
    balances: &[crate::hnn::word::FieldBalance],
    word: &crate::hnn::word::WordBalance,
) -> AcceptanceWorld {
    use crate::ratio::Rat;
    let moved = &opening.after - &opening.before;
    let supplied = &opening.imposed - &opening.absorbed;
    AcceptanceWorld {
        opening_gap: &moved - &supplied,
        moved,
        supplied,
        ticks: balances.len(),
        tick_defects: balances
            .iter()
            .map(|b| b.residual() + &b.resonator_chart + &b.resonator_split)
            .sum::<Rat>(),
        tick_bound: balances
            .iter()
            .map(|b| &b.bound + &b.resonator_bound)
            .sum::<Rat>(),
        word_defects: word.residual(),
        word_bound: word.bound.clone(),
        closes: opening.closes()
            && balances.iter().all(crate::hnn::word::FieldBalance::closes)
            && word.closes(),
    }
}

/// The later response's exact difference from a control's, station by station:
/// `learned.logits - control.logits`, over the same stations, crossings and ticks.
fn acceptance_difference(
    learned: &[crate::hnn::prediction::StationRead],
    control: &[crate::hnn::prediction::StationRead],
) -> Vec<(usize, Vec<crate::ratio::Rat>)> {
    assert_eq!(
        learned.len(),
        control.len(),
        "the learned and control boundaries read the same stations"
    );
    learned
        .iter()
        .zip(control)
        .map(|(l, c)| {
            assert_eq!(
                (l.station, l.crossing, l.tick),
                (c.station, c.crossing, c.tick)
            );
            assert_eq!(l.read.logits.len(), c.read.logits.len());
            let delta = l
                .read
                .logits
                .iter()
                .zip(&c.read.logits)
                .map(|(a, b)| a - b)
                .collect::<Vec<_>>();
            (l.station, delta)
        })
        .collect()
}

/// The later communication of a physical point restored cold from exact text.
struct AcceptanceCold {
    text_bytes: usize,
    same_material: bool,
    same_carry: bool,
    same_current: bool,
    later: crate::hnn::physical::communication::PhysicalCommunication,
}

/// Save a receiver's physical point as exact text and mount it on a fresh founding, then run the
/// later communication on the mounted point. This is the narrower material-and-carry remount the
/// owner declares for a constitution-only save (`Reference::mount_continued`): the whole-passage
/// save `Resident::continuing_state` refuses a receiving resident (`reference/passage.rs`, its
/// receiving chart), so this is the only cold path a `PhysicalReceiver` has. The mount reads only
/// the immutable field, a fresh founding constitution at the declared budget, the declared source
/// frame at rest and the saved text: no predecessor material, carry, chart or current is borrowed.
fn acceptance_cold(
    field: &Field,
    live: &PhysicalReceiver<'_>,
    source: &crate::hnn::encoding::Encoded,
    receiver: &ReceiverDeclaration,
) -> Result<AcceptanceCold, crate::hnn::HnnError> {
    use crate::hnn::constitution::ContinuingState;
    use crate::hnn::reference::Reference;
    let resident = live.resident();
    let saved = resident
        .constitution()
        .continuing_state(field.sources()[0])?
        .with_carry(resident.carried().cloned());
    let text = saved.to_text();
    let state = ContinuingState::from_text(&text)?;
    let founding = Constitution::initial(field, resident.constitution().budget())?;
    let restored = Reference::campaign_one().mount_continued(
        field,
        &Current::at_rest(field),
        founding,
        &state,
    )?;
    let same_material = restored.constitution() == resident.constitution();
    let same_carry = restored.carried() == resident.carried();
    let same_current = restored.current() == resident.current();
    let mut cold = PhysicalReceiver::from_resident(field, restored)?;
    let later = cold.communicate(source, receiver, |_| None)?;
    Ok(AcceptanceCold {
        text_bytes: text.len(),
        same_material,
        same_carry,
        same_current,
        later,
    })
}

/// [agent-inferred, October 8; the medium-of-joints record, section 7; issue #73's gate] **The
/// learned-change acceptance, READ on 0279's own task, family, material, receivers and observation**
/// (`complete_contact_return_publishes_held_point_before_existing_communication`: source `[0, 1]`,
/// observed `[0, 1, 3]`, station 2 compared, then the existing communication on source `[2, 1]` at
/// the same entering end). A READING, NEVER AN ACCEPTANCE: the criteria below were fixed before any
/// law change, this test asserts none of them and prints a label for each, and it is renamed into an
/// asserting acceptance only when a certified landing makes all four hold.
///
/// 1. **Committed change.** A reached C/K/D deposit commits a nonzero lattice coordinate `q != 0`
///    under its certified step: the family is not in `publication.publication.vanished`, its
///    material moved, and every applied entry lies on the family's lattice (a movement off the
///    lattice has no lattice coordinate, so it is refused as a reading and asserted against).
///    [agent-inferred] The criterion is met when at least one reached family commits;
///    each family's label is printed beside it, so a stricter all-three reading is visible.
/// 2. **Later response.** The later response at the declared compared station (mask
///    `[false, false, true]`, station 2) differs from the unmoved-material control by an exact
///    nonzero amount, with station, crossing and tick identity checked. The whole field's
///    difference is printed as a diagnostic only; a change at another station never passes the
///    criterion.
/// 3. **Energy accounting.** The world and material energy balance closes exactly: the opening
///    receipt `E_after - E_before = imposed - absorbed` of the deposit's word and of the later word,
///    the executed defects within their certified bounds, and the continuation's
///    `committed - before = deposition_work` (its `opening_difference` is read, not checked: the
///    owner defines it as `opening - committed`). [agent-inferred] The chain link joins the two
///    balances: the later word opens on exactly the energy the deposit opened
///    (`next.opening.before = continuation.opening`, both the power of the held change under the
///    successor material at the same lift). The owners refuse a receipt that does not close, so
///    the opening and held-work identities are zero on any receipt returned, and are asserted;
///    the chain link is the one independent link, derived here rather than guaranteed by an owner,
///    so it is printed and counted but not asserted. A closure over a deposit that committed
///    nothing accounts for no learned change, so the criterion is met only when criterion 1 is (a
///    no-change pass is never reported as learning).
/// 4. **Cold continuation.** The same later-response difference survives a cold restore from exact
///    text. It is met only when the restore reproduced the live material, carry and current, the
///    cold word closes, the restored later response equals the live one, their differences from
///    the control are equal, and that difference is nonzero (criterion 2). Equal output alone is
///    not evidence that the saved point was restored.
///    `PhysicalReceiver` has no whole-passage cold path (`Resident::continuing_state` refuses its
///    receiving chart), so the restore is the narrower material-and-carry remount, and this test
///    prints that refusal beside it.
///
/// The assertions are trust invariants only: the observation never enters its earlier forward;
/// identical operands give identical boundaries (twice live, and across a cold restore of the
/// unmoved control and of the learned point whenever the restore reproduces the live operands);
/// the control is truly unmoved, at the learned point's entering end; the later response is
/// source-sensitive (so equality with the control is not an insensitive output); the exact
/// remainder, statistic and lineage identities of the deposit; and the energy identities wherever
/// the owner guarantees them.
///
/// Recorded failures this reading refuses to repeat: a no-change pass reported as learning
/// (criteria 3 and 4 need a committed change and a nonzero difference); an authored outcome (the
/// only input is 0279's own observation, and every printed value is the machine's); a raised limit
/// (every budget is the one the live material declares); a scalar or bit count read as progress (the
/// count below counts named criteria, and says it is not an acceptance); cold continuation faked by
/// reusing live state (the restored point is read back from exact text onto a fresh founding).
#[test]
fn the_learned_change_acceptance_is_read_on_the_complete_contact_return() {
    use crate::hnn::constitution::{Carrier, FactorGradient, Family, Locus};
    use crate::hnn::physical::contact::ContactObservation;
    use crate::ratio::Rat;
    use num_traits::Signed;
    let started = std::time::Instant::now();
    // 0279's own task, family, material, receivers and observation, unchanged.
    let field = field();
    let initial = contact_material(&field);
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let compared = vec![false, false, true];
    let observation = || ContactObservation {
        observed: encoded(&field, &[0, 1, 3]),
        compared: compared.clone(),
    };
    let mut actual =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).unwrap();
    let mut untouched =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).unwrap();
    let blind = untouched
        .communicate_contact(&source, &receiver(), |_| None)
        .unwrap();
    let taught = actual
        .communicate_contact(&source, &receiver(), |boundary| {
            assert_eq!(
                boundary, &blind.boundary,
                "observation cannot enter its earlier forward"
            );
            Some(observation())
        })
        .unwrap();
    assert!(blind.closes() && taught.closes());
    assert_eq!(taught.boundary, blind.boundary);
    assert_eq!(taught.blind_carry, blind.carry);
    assert_eq!(
        taught.carry.ticks, 3,
        "full ticks keep their actual complete crossing"
    );
    let publication = taught.comparison.as_ref().unwrap().as_ref().unwrap();
    let material = actual.constitution().clone();
    let entering = actual.opening();
    // 0279's resident hand-off, then its controls on the learned point's entering end.
    let common = actual.into_resident();
    assert_eq!(common.constitution(), &material);
    assert_eq!(common.current(), &current);
    assert_eq!(common.carried(), Some(&taught.carry));
    assert!(common.carry_error().is_none());
    let mut actual = PhysicalReceiver::from_resident(&field, common).unwrap();
    let other_source = encoded(&field, &[2, 1]);
    let mut prior =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), entering.clone()).unwrap();
    // A determinism control on identical operands, never a selection among releases.
    let mut again =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), entering.clone()).unwrap();
    let mut other =
        PhysicalReceiver::new(&field, material.clone(), current.clone(), entering.clone()).unwrap();
    assert_eq!(
        prior.opening(),
        entering,
        "the control shares the learned point's entering end"
    );
    // The cold save is taken from the post-deposit point, before that point communicates again.
    let passage = actual.resident().continuing_state(field.sources()[0]);
    let cold = acceptance_cold(&field, &actual, &other_source, &receiver());
    // The same cold mechanism on the unmoved control, which isolates it from any learned change.
    let cold_control = acceptance_cold(&field, &prior, &other_source, &receiver());
    let next = actual
        .communicate(&other_source, &receiver(), |_| None)
        .unwrap();
    let old_material = prior
        .communicate(&other_source, &receiver(), |_| None)
        .unwrap();
    let old_again = again
        .communicate(&other_source, &receiver(), |_| None)
        .unwrap();
    let old_source = other.communicate(&source, &receiver(), |_| None).unwrap();

    println!(
        "learned-change acceptance READING on 0279's own task: source [0, 1], observed [0, 1, 3], \
         compared {compared:?} (the producing chart and the source prefix stay intact: the owner \
         admitted the comparison), then the existing communication on source [2, 1] at the same \
         entering end. The criteria were fixed before any law change: (1) a reached C/K/D deposit \
         commits q != 0 under its certified step; (2) the later response differs from the \
         unmoved-material control by an exact nonzero amount; (3) the world and material energy \
         balance closes exactly on a committed change; (4) that difference survives a cold restore. \
         The three families deposit together and the owner offers no single-family control, so \
         criterion 1 is read per family (C, K, D) and criteria 2 to 4 jointly."
    );

    // Criterion 1: a reached C/K/D deposit commits q != 0 under its certified step.
    let locus = Locus::Channel(0);
    let lattice = initial.lattice(locus).expect("the contact's lattice");
    let half_unit = lattice.unit() / integer(2);
    let half_reading = acceptance_exact(&half_unit);
    let prior_remainders = initial.carried_remainders();
    let next_remainders = material.carried_remainders();
    let carried = |xs: &[(Locus, Carrier, usize, Rat)], carrier: Carrier, entry: usize| -> Rat {
        xs.iter()
            .filter(|(l, c, i, _)| *l == locus && *c == carrier && *i == entry)
            .map(|(_, _, _, r)| r.clone())
            .sum::<Rat>()
    };
    let released = |carrier: Carrier, entry: usize| -> Rat {
        publication
            .publication
            .released
            .iter()
            .filter(|(l, c, i, _)| *l == locus && *c == carrier && *i == entry)
            .map(|(_, _, _, r)| r.clone())
            .sum::<Rat>()
    };
    let mut committed_families = 0usize;
    let mut lineage = true;
    let mut remainder_split = true;
    let mut statistic_split = true;
    let mut on_lattice = true;
    for (f, name) in ["C", "K", "D"].into_iter().enumerate() {
        let family = Family::Factor(f);
        let eta = publication.publication.family_step(locus, family);
        let vanished = publication.publication.vanished.contains(&(locus, family));
        let (before_factor, after_factor) = match f {
            0 => (initial.contact_storage(0), material.contact_storage(0)),
            1 => (initial.contact_stiffness(0), material.contact_stiffness(0)),
            _ => (
                initial.contact_dissipation(0),
                material.contact_dissipation(0),
            ),
        };
        let moved = after_factor != before_factor;
        let movement = publication
            .continuation
            .material
            .iter()
            .find(|m| m.contact == 0 && m.family == family)
            .unwrap_or_else(|| panic!("the actual deposit applied no family-{f} movement"));
        let reached = publication
            .comparison_return
            .factors()
            .iter()
            .find(|s| s.gradient.locus() == locus && s.gradient.family() == family)
            .unwrap_or_else(|| panic!("the actual deposit returned no family-{f} gradient"));
        let gradient = match &reached.gradient {
            FactorGradient::Storage { gradient, .. }
            | FactorGradient::Stiffness { gradient, .. }
            | FactorGradient::Dissipation { gradient, .. } => gradient,
            _ => unreachable!("a contact family returns a Gram-factor gradient"),
        };
        let statistic = &material.contact_scales(0)[f];
        // This fixture's stiffness signature is the identity, as in the neighbouring controls.
        let proposed = gradient.scaled(&(&eta / statistic));
        // The applied lattice coordinates q of the movement the deposit actually committed.
        let coordinates: Vec<_> = movement
            .factor
            .entries()
            .iter()
            .map(|entry| lattice.div_rem(entry))
            .collect();
        let entries = coordinates.len();
        let off_lattice = coordinates.iter().filter(|(_, r)| !r.is_zero()).count();
        on_lattice &= off_lattice == 0;
        let q_nonzero = coordinates.iter().filter(|(q, _)| !q.is_zero()).count();
        let q_largest = coordinates
            .iter()
            .map(|(q, _)| q.abs())
            .max()
            .unwrap_or_default();
        // How far the proposed move (with the prior remainder it meets) is from the half-unit.
        let largest_with_prior = proposed
            .entries()
            .iter()
            .enumerate()
            .map(|(i, d)| (d + carried(&prior_remainders, Carrier::Factor(f), i)).abs())
            .max()
            .unwrap_or_else(Rat::zero);
        let shortfall = largest_with_prior
            .is_positive()
            .then(|| &half_unit / &largest_with_prior);
        // The exact remainder split of the deposit, entry by entry: delta + r_prior = applied +
        // r_next + released, and the applied factor reaches the resident unchanged.
        for (i, (delta, applied)) in proposed
            .entries()
            .iter()
            .zip(movement.factor.entries())
            .enumerate()
        {
            remainder_split &= delta + carried(&prior_remainders, Carrier::Factor(f), i)
                == applied
                    + carried(&next_remainders, Carrier::Factor(f), i)
                    + released(Carrier::Factor(f), i);
        }
        lineage &= before_factor.add(&movement.factor).unwrap() == *after_factor;
        statistic_split &= &reached.energy + carried(&prior_remainders, Carrier::FactorScale(f), 0)
            == statistic - &initial.contact_scales(0)[f]
                + carried(&next_remainders, Carrier::FactorScale(f), 0)
                + released(Carrier::FactorScale(f), 0);
        let unresolved: Vec<Rat> = next_remainders
            .iter()
            .filter(|(l, c, _, _)| *l == locus && *c == Carrier::Factor(f))
            .map(|(_, _, _, r)| r.clone())
            .collect();
        let unresolved_entries = unresolved.len();
        let unresolved_nonzero = unresolved.iter().filter(|r| !r.is_zero()).count();
        let unresolved_largest = unresolved
            .iter()
            .map(Signed::abs)
            .max()
            .unwrap_or_else(Rat::zero);
        let committed =
            !vanished && moved && off_lattice == 0 && q_nonzero > 0 && eta.is_positive();
        committed_families += usize::from(committed);
        let eta_reading = acceptance_exact(&eta);
        let largest_reading = acceptance_exact(&largest_with_prior);
        let shortfall_reading = shortfall
            .as_ref()
            .map_or("no positive proposed move".to_string(), acceptance_exact);
        let unresolved_reading = acceptance_exact(&unresolved_largest);
        let verdict = acceptance_verdict(committed);
        println!(
            "learned-change acceptance criterion 1 family {name}: certified eta={eta_reading} \
             vanished={vanished} material_moved={moved}; applied lattice coordinates q != 0 at \
             {q_nonzero} of {entries} entries (largest |q|={q_largest}, entries off the lattice=\
             {off_lattice}); half_unit={half_reading}; largest |proposed + prior remainder|=\
             {largest_reading}; half_unit/largest={shortfall_reading} (above 1 is the factor by \
             which the move falls short of its cell); unresolved after the deposit: \
             {unresolved_nonzero} of {unresolved_entries} entries nonzero, largest |r|=\
             {unresolved_reading} => {verdict}"
        );
    }
    let met1 = committed_families > 0;
    println!(
        "learned-change acceptance criterion 1 (a reached C/K/D deposit commits q != 0): \
         {committed_families} of 3 families committed => {}",
        acceptance_verdict(met1)
    );

    // Criterion 2: the later compared-station response against the unmoved-material control.
    let difference =
        acceptance_difference(next.boundary.readings(), old_material.boundary.readings());
    let total_coordinates: usize = difference.iter().map(|(_, d)| d.len()).sum();
    let changed_coordinates: usize = difference
        .iter()
        .map(|(_, d)| d.iter().filter(|x| !x.is_zero()).count())
        .sum();
    let squared: Rat = difference
        .iter()
        .flat_map(|(_, d)| d.iter())
        .map(|x| x * x)
        .sum();
    // The criterion reads the declared compared station only; the field difference is diagnostic.
    let compared_stations: Vec<usize> = compared
        .iter()
        .enumerate()
        .filter(|(_, c)| **c)
        .map(|(station, _)| station)
        .collect();
    let compared_present = difference
        .iter()
        .any(|(station, _)| compared_stations.contains(station));
    let compared_changed: usize = difference
        .iter()
        .filter(|(station, _)| compared_stations.contains(station))
        .map(|(_, d)| d.iter().filter(|x| !x.is_zero()).count())
        .sum();
    let met2 = compared_present && compared_changed > 0;
    let cells_equal = next
        .boundary
        .readings()
        .iter()
        .zip(old_material.boundary.readings())
        .all(|(a, b)| a.read.cells == b.read.cells);
    let leaders_learned: Vec<_> = next
        .boundary
        .readings()
        .iter()
        .map(|r| r.leaders())
        .collect();
    let leaders_control: Vec<_> = old_material
        .boundary
        .readings()
        .iter()
        .map(|r| r.leaders())
        .collect();
    let difference_reading = if met2 {
        difference
            .iter()
            .map(|(station, d)| {
                let entries = d.iter().map(acceptance_exact).collect::<Vec<_>>();
                format!("station {station}: [{}]", entries.join(", "))
            })
            .collect::<Vec<_>>()
            .join("; ")
    } else {
        format!("all {total_coordinates} logit coordinates are equal")
    };
    let squared_reading = acceptance_exact(&squared);
    // The cells that respond: a class is realified as its (Re, Im) logits, so class c is
    // coordinates 2c and 2c + 1.
    let distinguishing: Vec<(usize, Vec<usize>)> = difference
        .iter()
        .map(|(station, d)| {
            let classes = (0..d.len() / 2)
                .filter(|&c| !d[2 * c].is_zero() || !d[2 * c + 1].is_zero())
                .collect::<Vec<_>>();
            (*station, classes)
        })
        .collect();
    let attribution = if met2 && !met1 {
        " (no family committed, so this difference is not attributed to a landing)"
    } else {
        ""
    };
    println!(
        "learned-change acceptance criterion 2 (the later response differs from the unmoved-material \
         control): at the compared station(s) {compared_stations:?} (present={compared_present}), \
         {compared_changed} coordinates differ; diagnostic over the whole field: \
         {changed_coordinates} of {total_coordinates} realified logit coordinates differ; \
         difference (learned - control) = {difference_reading}; |difference|^2={squared_reading}; \
         distinguishing classes by station={distinguishing:?}; grain cells equal={cells_equal}; \
         leaders learned={leaders_learned:?} control={leaders_control:?}{attribution} => {}",
        acceptance_verdict(met2)
    );

    // Criterion 3: the world and material energy balance.
    let continuation = &publication.continuation;
    let deposit_world = acceptance_world(&taught.opening, &taught.balances, &taught.word);
    let later_world = acceptance_world(&next.opening, &next.balances, &next.word);
    let held_work_gap =
        (&continuation.committed - &continuation.before) - &continuation.deposition_work;
    // The chain link between the two balances: the deposit hands the later word the energy it
    // opened (both are the power of the held change under the successor material, at the same
    // lift), so the later opening starts exactly where the deposit left the energy.
    let chain_gap = &next.opening.before - &continuation.opening;
    let identities_exact = deposit_world.closes
        && later_world.closes
        && deposit_world.opening_gap.is_zero()
        && later_world.opening_gap.is_zero()
        && held_work_gap.is_zero()
        && chain_gap.is_zero();
    let identity_residual: Rat = [
        &deposit_world.opening_gap,
        &later_world.opening_gap,
        &held_work_gap,
        &chain_gap,
    ]
    .into_iter()
    .map(|gap| gap.abs())
    .sum();
    let met3 = identities_exact && met1;
    for (what, world) in [
        ("deposit word", &deposit_world),
        ("later word", &later_world),
    ] {
        let moved = acceptance_exact(&world.moved);
        let supplied = acceptance_exact(&world.supplied);
        let gap = acceptance_exact(&world.opening_gap);
        let ticks = world.ticks;
        let tick_defects = acceptance_exact(&world.tick_defects);
        let tick_bound = acceptance_exact(&world.tick_bound);
        let word_defects = acceptance_exact(&world.word_defects);
        let word_bound = acceptance_exact(&world.word_bound);
        let closes = world.closes;
        println!(
            "learned-change acceptance criterion 3 {what}: opening E_after - E_before={moved} \
             imposed - absorbed={supplied} residual={gap}; executed defects over {ticks} ticks=\
             {tick_defects} within bound {tick_bound}; whole-word defects={word_defects} within \
             bound {word_bound}; the owner's receipts close={closes}"
        );
    }
    let held_before = acceptance_exact(&continuation.before);
    let held_committed = acceptance_exact(&continuation.committed);
    let held_work = acceptance_exact(&continuation.deposition_work);
    let held_gap = acceptance_exact(&held_work_gap);
    let opened_difference = acceptance_exact(&continuation.opening_difference);
    let chain_residual = acceptance_exact(&chain_gap);
    let storage_growth = acceptance_exact(&publication.publication.storage_growth);
    let storage_product = acceptance_exact(&publication.publication.storage_product);
    let momentum_growth = continuation
        .held_momentum_growth
        .as_ref()
        .map_or("none (no uniform bound)".to_string(), acceptance_exact);
    println!(
        "learned-change acceptance criterion 3 material: before={held_before} \
         committed={held_committed} deposition_work={held_work} (committed - before - work \
         residual={held_gap}); the owner's opening difference (opening - committed, its own \
         definition)={opened_difference}; chain link (the later word's opening E_before - the \
         deposit's opened energy)={chain_residual}; certified storage_growth={storage_growth} \
         storage_product={storage_product} held_momentum_growth={momentum_growth}"
    );
    let vacuity = if identities_exact && !met1 {
        " (the identities close exactly over a deposit that committed nothing: a no-change \
         closure, not reported as learning)"
    } else {
        ""
    };
    let identity_residual_reading = acceptance_exact(&identity_residual);
    println!(
        "learned-change acceptance criterion 3 (the world and material energy balance closes \
         exactly on a committed change): identities close exactly={identities_exact} (sum of the \
         absolute opening, held-work and chain residuals={identity_residual_reading}) \
         committed change present={met1}{vacuity} => {}",
        acceptance_verdict(met3)
    );

    // Criterion 4: the same later-response difference survives a cold restore.
    // Whether the fresh founding shares the live material's declared identity, which the owner's
    // `Constitution::continued` requires of the opening a state is restored onto.
    let founding_matches = Constitution::initial(&field, material.budget())
        .map(|founding| founding.material_identity() == material.material_identity());
    let passage_reading = match &passage {
        Ok(_) => "admitted (the whole passage was saved)".to_string(),
        Err(refusal) => format!("REFUSED {refusal:?}"),
    };
    let (survives, cold_reading) = match &cold {
        Err(refusal) => (
            false,
            format!("the narrower material-and-carry cold remount was REFUSED {refusal:?}"),
        ),
        Ok(restored) => {
            // The cold difference is comparable only when the restored carry reproduces the
            // entering end, so that the stations, crossings and ticks are the same.
            let same_difference = restored.same_carry
                && acceptance_difference(
                    restored.later.boundary.readings(),
                    old_material.boundary.readings(),
                ) == difference;
            let same_response = restored.later.boundary.readings() == next.boundary.readings();
            let bytes = restored.text_bytes;
            let (material_back, carry_back, current_back) = (
                restored.same_material,
                restored.same_carry,
                restored.same_current,
            );
            let closes = restored.later.closes();
            (
                material_back
                    && carry_back
                    && current_back
                    && closes
                    && same_response
                    && same_difference
                    && met2,
                format!(
                    "the narrower material-and-carry cold remount ({bytes} bytes of exact text, a \
                     fresh founding at the declared budget): restored material == live \
                     {material_back}, carry == live {carry_back}, current == live \
                     {current_back}; cold later response == live later response \
                     {same_response}; cold difference == live difference {same_difference}; the \
                     cold word closes={closes}"
                ),
            )
        }
    };
    let cold_control_reading = match &cold_control {
        Err(refusal) => format!("REFUSED {refusal:?}"),
        Ok(restored) => {
            let reproduced = restored.same_material && restored.same_carry && restored.same_current;
            let same_boundary = restored.later.boundary == old_material.boundary;
            format!(
                "operands reproduced={reproduced}, later boundary equals the live control's=\
                 {same_boundary}"
            )
        }
    };
    let met4 = survives;
    println!(
        "learned-change acceptance criterion 4 (the same later-response difference survives a \
         cold restore): whole-passage Resident::continuing_state on this physical resident: \
         {passage_reading}; fresh founding shares the live material's declared identity=\
         {founding_matches:?}; {cold_reading}; the same cold mechanism on the unmoved control: \
         {cold_control_reading}; difference nonzero={met2} => {}",
        acceptance_verdict(met4)
    );

    // The assertions that let the readings above be trusted. None asserts that a criterion is met.
    assert_eq!(publication.comparison_return.commit(), initial.commit());
    assert_eq!(publication.publication.commit, material.commit());
    assert!(
        lineage,
        "each family's applied factor reaches the resident unchanged"
    );
    assert!(
        on_lattice,
        "every applied movement lies on its family's lattice, so q reads a lattice coordinate"
    );
    assert!(
        remainder_split,
        "delta + r_prior = applied + r_next + released, exactly, entry by entry"
    );
    assert!(
        statistic_split,
        "the reached energy splits into applied statistic, retained and released parts"
    );
    assert!(
        deposit_world.closes && later_world.closes,
        "the owner's world receipts close"
    );
    assert!(
        deposit_world.opening_gap.is_zero()
            && later_world.opening_gap.is_zero()
            && held_work_gap.is_zero(),
        "the owner's energy identities have no residual"
    );
    assert!(next.closes() && old_material.closes() && old_again.closes() && old_source.closes());
    assert_eq!(next.carry.ticks, taught.carry.ticks + 2);
    assert_eq!(old_material.carry.ticks, next.carry.ticks);
    assert_eq!(
        prior.constitution(),
        &initial,
        "the control is truly unmoved"
    );
    assert_eq!(again.constitution(), &initial);
    assert_eq!(
        old_again.boundary, old_material.boundary,
        "identical operands give identical boundaries"
    );
    assert_eq!(old_again.carry, old_material.carry);
    assert_ne!(
        next.boundary.readings(),
        old_source.boundary.readings(),
        "the later response is source-sensitive, so equality with the control is not an \
         insensitive output"
    );
    if let Ok(restored) = &cold {
        let reproduced = restored.same_material && restored.same_carry && restored.same_current;
        if reproduced {
            assert_eq!(
                restored.later.boundary, next.boundary,
                "identical operands give identical boundaries across a cold restore"
            );
            assert_eq!(restored.later.carry, next.carry);
        }
    }
    if let Ok(restored) = &cold_control {
        let reproduced = restored.same_material && restored.same_carry && restored.same_current;
        if reproduced {
            assert_eq!(
                restored.later.boundary, old_material.boundary,
                "identical operands give identical boundaries across a cold restore of the control"
            );
            assert_eq!(restored.later.carry, old_material.carry);
        }
    }
    println!(
        "learned-change acceptance: every trust assertion passed; the readings above are verified"
    );
    println!(
        "learned-change acceptance timing: elapsed_ns={}",
        started.elapsed().as_nanos()
    );
    let met = [met1, met2, met3, met4];
    let count = met.iter().filter(|m| **m).count();
    println!(
        "learned-change acceptance: {count} of 4 criteria met (NOT accepted until 4 of 4 under a \
         certified step)"
    );
}

#[test]
fn a_shared_execution_clock_reanchors_the_next_section_without_resetting_its_carry() {
    use crate::hnn::port::ExecutionPort;
    use crate::hnn::reference::Reference;
    let field = field();
    let mut view = PhysicalReceiver::new(&field, material(&field), Current::at_rest(&field), WordOpening::Rest).unwrap();
    let source = encoded(&field, &[0, 1]);
    let first = view.communicate(&source, &receiver(), |_| None).unwrap();
    let mut common = view.into_resident();
    let previous = common.current().clone();
    Reference::campaign_one().ingest(&mut common, None, &encoded(&field, &[2])).unwrap();
    assert_ne!(common.current(), &previous);
    assert_eq!(common.carried(), Some(&first.carry), "ingest advances source time, not this wave current");
    let live = common.current().clone();
    let theta = common.constitution().clone();
    let entering = common.reception_opening();
    let chart = source.part(0..0).unwrap();
    let section = DamagedSection::of_runs(3, &chart, vec![(0, source.clone())]).unwrap();
    let phases = ReceivingPhases::declare(&field, &theta, &live, &receiver()).unwrap();
    let matched = crate::hnn::prediction::predict_sparse_by_field(&field, &theta, &live, &section, &entering, &phases).unwrap().finish();
    let mut view = PhysicalReceiver::from_resident(&field, common).unwrap();
    let next = view.communicate(&source, &receiver(), |_| None).unwrap();
    assert!(next.closes());
    assert_eq!(next.boundary.readings(), &matched.reads[2..]);
    assert_eq!(next.carry, matched.carry);
    assert_eq!(view.current(), &live, "section entrance does not secretly advance Current");
    assert_eq!(next.carry.ticks, first.carry.ticks + 2);
}

#[test]
fn communication_deposits_after_the_whole_boundary_and_reuses_material_source_and_carry() {
    let started = std::time::Instant::now();
    let field = field();
    let initial = material(&field);
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let mut resident =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).expect("admitted common resident");
    let taught = resident
        .communicate(&source, &receiver(), |boundary| {
            println!("whole blind communication boundary: {boundary:?}");
            assert_eq!(boundary.chart(), &source.part(0..0).unwrap());
            assert_eq!(boundary.first_station(), 2);
            assert_eq!(boundary.readings().len(), 1);
            assert_eq!(boundary.readings()[0].station, 2);
            assert_eq!(boundary.readings()[0].read.cells.len(), field.alphabet());
            assert_eq!(boundary.readings()[0].read.phases.len(), field.alphabet());
            assert_eq!(
                boundary.decisions(),
                &[RepairedCell::Held {
                    fibre: (0..field.alphabet()).collect(),
                    unresolved: Unresolved::UncertifiedDomain,
                }]
            );
            assert_eq!(boundary.domains(), &[None]);
            assert!(boundary.faces().is_ok());
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 3]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    assert!(taught.closes());
    assert!(!taught.declaring_face_reused);
    assert_eq!(taught.carry.ticks, 2);
    assert!(taught.comparison.unwrap().unwrap().publication.stepped > 0);
    assert_ne!(
        resident.constitution().receiving_map(0),
        initial.receiving_map(0)
    );
    assert_eq!(
        resident.constitution().source_port(0),
        initial.source_port(0)
    );
    let theta = resident.constitution().clone();
    let entered = resident.opening().clone();
    let commit = theta.commit();

    // Same actual entering carry and source, with the earlier material: isolate learned R.
    let mut unlearned = PhysicalReceiver::new(&field, initial, current.clone(), entered.clone()).expect("admitted common resident");
    let prior = unlearned
        .communicate(&source, &receiver(), |_| None)
        .unwrap();
    let next = resident
        .communicate(&source, &receiver(), |_| None)
        .unwrap();
    assert!(prior.closes() && next.closes());
    assert!(!prior.declaring_face_reused);
    assert!(next.declaring_face_reused, "R changed; the actual rank producer is independent of R");
    assert_ne!(
        next.boundary.readings()[0].read.logits,
        prior.boundary.readings()[0].read.logits
    );
    assert_eq!(next.carry.ticks, taught.carry.ticks + 2);
    assert_eq!(
        resident.constitution().commit(),
        commit,
        "unobserved communication does not deposit"
    );
    let WordOpening::Received { carry, .. } = resident.opening() else {
        panic!("actual carried end")
    };
    assert_eq!(carry, next.carry);

    // Same learned material, clock and entering carry, changing only an admitted source class.
    // This is a source-sensitivity falsifier, not a favourable answer selected by a grader.
    let mut changed_source = PhysicalReceiver::new(&field, theta, current, entered).expect("admitted common resident");
    let changed = changed_source
        .communicate(&encoded(&field, &[2, 1]), &receiver(), |_| None)
        .unwrap();
    assert!(changed.closes());
    assert!(!changed.declaring_face_reused);
    assert_ne!(
        next.boundary.readings()[0].read.logits,
        changed.boundary.readings()[0].read.logits
    );
    println!(
        "whole unobserved carried communication boundary: {:?}",
        next.boundary
    );
    println!(
        "unit communication material/source/carry elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn communication_observations_cannot_change_the_earlier_boundary() {
    let started = std::time::Instant::now();
    let field = field();
    let initial = material(&field);
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let mut left =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).expect("admitted common resident");
    let mut right = PhysicalReceiver::new(&field, initial, current, WordOpening::Rest).expect("admitted common resident");
    let a = left
        .communicate(&source, &receiver(), |_| {
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 3]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    let b = right
        .communicate(&source, &receiver(), |_| {
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 2]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    assert!(a.closes() && b.closes());
    assert_eq!(a.boundary, b.boundary);
    assert_eq!(a.carry, b.carry);
    assert_eq!(a.opening, b.opening);
    assert!(a.comparison.unwrap().unwrap().publication.stepped > 0);
    assert!(b.comparison.unwrap().unwrap().publication.stepped > 0);
    assert_ne!(
        left.constitution().receiving_map(0),
        right.constitution().receiving_map(0)
    );
    let a_next = left.communicate(&source, &receiver(), |_| None).unwrap();
    let b_next = right.communicate(&source, &receiver(), |_| None).unwrap();
    assert!(a_next.closes() && b_next.closes());
    assert_ne!(
        a_next.boundary.readings()[0].read.logits,
        b_next.boundary.readings()[0].read.logits
    );
    println!(
        "unit communication post-blind independence elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn communication_refuses_changed_source_or_partition_without_deposition_and_keeps_the_blind_end() {
    let started = std::time::Instant::now();
    let field = field();
    let initial = material(&field);
    let source = encoded(&field, &[0, 1]);
    let mut resident = PhysicalReceiver::new(
        &field,
        initial.clone(),
        Current::at_rest(&field),
        WordOpening::Rest,
    ).expect("admitted common resident");
    for (cells, compared) in [
        ([1, 1, 3], vec![false, false, true]),
        ([0, 1, 3], vec![true, false, true]),
    ] {
        let entered = match resident.opening() {
            WordOpening::Rest => 0,
            WordOpening::Received { carry, .. } => carry.ticks,
        };
        let receipt = resident
            .communicate(&source, &receiver(), |_| {
                Some(PhysicalObservation {
                    observed: encoded(&field, &cells),
                    compared,
                    learning: PhysicalLearning::Receiving,
                })
            })
            .unwrap();
        assert!(receipt.comparison.is_err());
        assert!(receipt.closes());
        assert_eq!(receipt.carry.ticks, entered + 2);
        assert_eq!(resident.constitution(), &initial);
        let WordOpening::Received { carry, .. } = resident.opening() else {
            panic!("blind carried end")
        };
        assert_eq!(carry, receipt.carry);
    }
    let before = resident.opening().clone();
    assert!(
        resident
            .communicate(&encoded(&field, &[0, 1, 2]), &receiver(), |_| {
                panic!("no future section must refuse before reception")
            })
            .is_err()
    );
    assert_eq!(resident.opening(), before);
    assert_eq!(resident.constitution(), &initial);
    let mut over_period = receiver();
    over_period.aperture = 5; // the producing source phase period is four
    assert!(
        resident
            .communicate(&source, &over_period, |_| {
                panic!("a unit-source phase wrap must refuse before opening a Word")
            })
            .is_err()
    );
    assert_eq!(resident.opening(), before);
    assert_eq!(resident.constitution(), &initial);
    println!(
        "unit communication source/partition refusal elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn communication_returns_actual_multistation_held_receipts_without_a_joint_certificate() {
    let started = std::time::Instant::now();
    let field = field();
    let initial = material(&field);
    let mut resident = PhysicalReceiver::new(
        &field,
        initial.clone(),
        Current::at_rest(&field),
        WordOpening::Rest,
    ).expect("admitted common resident");
    let output = resident
        .communicate(&encoded(&field, &[0]), &receiver(), |boundary| {
            assert_eq!(boundary.first_station(), 1);
            assert_eq!(boundary.readings().len(), 2);
            assert_eq!(boundary.readings()[0].station, 1);
            assert_eq!(boundary.readings()[1].station, 2);
            assert_eq!(boundary.readings()[0].tick, 1);
            assert_eq!(boundary.readings()[1].tick, 2);
            assert_eq!(boundary.decisions().len(), 2);
            for decision in boundary.decisions() {
                assert_eq!(
                    decision,
                    &RepairedCell::Held {
                        fibre: (0..field.alphabet()).collect(),
                        unresolved: Unresolved::UncertifiedDomain,
                    }
                );
            }
            assert_eq!(
                boundary.domains(),
                &[None, None],
                "sparse forward supplies no completion certificate; a point face is insufficient"
            );
            println!("whole multi-station blind communication receipt: {boundary:?}");
            None
        })
        .unwrap();
    assert!(output.closes());
    assert!(output.comparison.unwrap().is_none());
    assert_eq!(output.carry.ticks, 2);
    assert_eq!(resident.constitution(), &initial);
    println!(
        "unit communication actual held/domain receipts elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn one_future_communication_carries_one_actual_source_label_through_the_whole_receiving_image() {
    let started = std::time::Instant::now();
    let field = field();
    let initial = material(&field);
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let mut resident =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).expect("admitted common resident");
    let taught = resident
        .communicate_one_future(&source, &receiver(), |boundary| {
            println!("whole one-future boundary before observation: {boundary:?}");
            let domain = boundary.domains()[0].as_ref().unwrap();
            let response = domain.completion.as_ref().unwrap();
            assert_eq!(boundary.completion_consistency(), Some(response));
            assert_eq!(response.station, 2);
            assert_eq!(response.label_logits.len(), 4);
            assert_eq!(domain.classes, vec![0, 1, 2, 3]); // initial R is zero
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 3]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    assert!(taught.closes());
    assert!(taught.comparison.unwrap().unwrap().publication.stepped > 0);
    assert_ne!(
        resident.constitution().receiving_map(0),
        initial.receiving_map(0)
    );
    let producing = resident.constitution().clone();
    let entered = resident.opening().clone();
    let next = resident
        .communicate_one_future(&source, &receiver(), |_| None)
        .unwrap();
    assert!(next.closes());
    assert_eq!(next.carry.ticks, 4);
    assert!(next.comparison.unwrap().is_none());
    assert_eq!(resident.constitution(), &producing);
    let domain = next.boundary.domains()[0].as_ref().unwrap();
    let response = domain.completion.as_ref().unwrap();
    assert_eq!(next.boundary.completion_consistency(), Some(response));
    let mut communicated = domain.classes.clone();
    communicated.extend(next.boundary.readings()[0].leaders());
    communicated.sort_unstable();
    communicated.dedup();
    match &next.boundary.decisions()[0] {
        RepairedCell::Released(class) => assert_eq!(communicated, vec![*class]),
        RepairedCell::Held { fibre, .. } => assert_eq!(fibre, &communicated),
        RepairedCell::Intact(_) => panic!("a requested future class was never imposed"),
    }
    assert_eq!(response.station, 2);
    assert_eq!(response.fixed_logits.len(), 8);
    assert_eq!(response.label_logits.len(), 4);
    let phases = ReceivingPhases::declare(&field, &producing, &current, &receiver()).unwrap();
    // Exterior falsifiers only: every complete label runs an independent native Word at the
    // same producing material/source frame/entering carry. Production carries signed columns,
    // not these completed Words or a table of answers.
    for class in 0..4 {
        let complete = encoded(&field, &[0, 1, class]);
        let section = DamagedSection::of_runs(3, &complete, vec![(0, complete.clone())]).unwrap();
        let actual =
            repair_by_field(&field, &producing, &current, &section, &entered, &phases).unwrap();
        let image = response
            .fixed_logits
            .iter()
            .zip(&response.label_logits[class])
            .map(|(fixed, label)| fixed + label)
            .collect::<Vec<_>>();
        assert_eq!(image, actual.reads[2].read.logits);
        assert!(actual.opening.closes() && actual.word.closes());
        assert!(actual.balances.iter().all(|balance| balance.closes()));
        for (value, interval) in image.iter().zip(&domain.logits) {
            assert!(interval.lower <= *value && *value <= interval.upper);
        }
    }
    println!("whole carried one-future boundary: {:?}", next.boundary);
    println!(
        "unit one-future common-label image elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn one_future_source_publication_reaches_the_next_contemporary_communication_opening() {
    let started = std::time::Instant::now();
    let field = field();
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let mut resident =
        PhysicalReceiver::new(&field, material(&field), current.clone(), WordOpening::Rest).expect("admitted common resident");
    let received = resident
        .communicate_one_future(&source, &receiver(), |_| {
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 3]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    assert!(received.closes());
    assert!(!received.declaring_face_reused);
    assert!(received.comparison.unwrap().unwrap().publication.stepped > 0);
    let producing = resident.constitution().clone();
    let mut emitted = None;
    let taught = resident
        .communicate_one_future(&source, &receiver(), |boundary| {
            emitted = Some(boundary.clone());
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 2]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::SourcePorts,
            })
        })
        .unwrap();
    assert!(taught.closes());
    assert!(taught.declaring_face_reused);
    assert_eq!(taught.boundary, emitted.unwrap());
    let publication = taught.comparison.unwrap().unwrap();
    assert!(publication.publication.stepped > 0);
    let paired = publication.source_pairing.as_ref().unwrap();
    assert_eq!(paired.producing_commit, producing.commit());
    assert!(paired.source_move_squared > integer(0));
    assert!(!paired.receiving.is_zero());
    assert_eq!(paired.receiving, paired.opening);
    assert_eq!(paired.opening, paired.deposition);
    assert!(paired.defect.is_zero() && paired.composition_defect.is_zero());
    assert_eq!(
        resident.constitution().receiving_map(0),
        producing.receiving_map(0)
    );
    assert_ne!(
        resident.constitution().source_port(0),
        producing.source_port(0)
    );
    let entered = resident.opening().clone();
    let WordOpening::Received { carry, .. } = &entered else {
        panic!("actual blind end")
    };
    assert_eq!(carry, &taught.carry);
    let mut prior = PhysicalReceiver::new(&field, producing, current, entered).expect("admitted common resident");
    // A separately fixed prefix; no later observation is supplied to either native read.
    let later_source = encoded(&field, &[2, 1]);
    let before = prior
        .communicate_one_future(&later_source, &receiver(), |_| None)
        .unwrap();
    let commit = resident.constitution().commit();
    let after = resident
        .communicate_one_future(&later_source, &receiver(), |_| None)
        .unwrap();
    assert!(before.closes() && after.closes());
    assert!(!before.declaring_face_reused);
    assert!(after.declaring_face_reused, "new E and a different source still execute under the same declaring medium");
    assert_eq!(after.carry.ticks, taught.carry.ticks + 2);
    assert_ne!(
        before.boundary.readings()[0].read.logits,
        after.boundary.readings()[0].read.logits
    );
    assert_eq!(resident.constitution().commit(), commit);
    // A changed imposition need not change its scalar energy. Each actual work receipt must
    // close; differing energy is not a condition for learning a physical source relation.
    println!(
        "later source openings before={:?} after={:?}",
        before.opening, after.opening
    );
    println!("actual one-future source return: {paired:?}");
    println!(
        "whole later source-conditioned boundary: {:?}",
        after.boundary
    );
    println!(
        "unit one-future source publication elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn one_future_communication_keeps_refusal_and_multi_future_admission_honest() {
    let field = field();
    let initial = material(&field);
    let source = encoded(&field, &[0, 1]);
    let mut resident = PhysicalReceiver::new(
        &field,
        initial.clone(),
        Current::at_rest(&field),
        WordOpening::Rest,
    ).expect("admitted common resident");
    let refused = resident
        .communicate_one_future(&source, &receiver(), |_| {
            Some(PhysicalObservation {
                observed: encoded(&field, &[1, 1, 3]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    assert!(refused.closes());
    assert!(refused.comparison.is_err());
    assert_eq!(resident.constitution(), &initial);
    let entered = resident.opening().clone();
    assert!(
        resident
            .communicate_one_future(&encoded(&field, &[0]), &receiver(), |_| {
                panic!("two future stations need their joint certificate before Word")
            })
            .is_err()
    );
    let mut wrapped = receiver();
    wrapped.aperture = 5;
    assert!(
        resident
            .communicate_one_future(&encoded(&field, &[0, 1, 2, 3]), &wrapped, |_| {
                panic!("unit source period admission precedes Word")
            })
            .is_err()
    );
    assert_eq!(resident.opening(), entered);
    assert_eq!(resident.constitution(), &initial);
    let WordOpening::Received { carry, .. } = &entered else {
        panic!("blind end retained")
    };
    assert_eq!(carry, &refused.carry);
}

/// [agent-inferred, October 9; the medium-of-joints record, section 7] **The finite-decrease
/// landing, READ on 0279's own flow** (source `[0, 1]`, observed `[0, 1, 3]`, station 2 compared,
/// then the existing communication on source `[2, 1]` at the same entering end). The W0 flow now
/// issues ONE declared candidate on its Rest-opened comparison: each reached family at its first
/// reach, re-read on a transient Word of the same declared passage, admitted only on an exact,
/// strict improvement (`upper(L′) < lower(L)` with `X′ ≤ X`, or the reading-identity witness with
/// `X′ < X`); a typed refusal continues on the certified step exactly as before. The outcome,
/// admitted or refused, is a measurement and is never forced.
///
/// It prints `L`, `L′`, `X`, `X′`, the declared exponents, the committed `q` per family and `e`, all
/// exact, and the four learned-change criteria as the acceptance reader reads them (PASS or
/// NOT-MET). It asserts only the admission's own laws and trust invariants, never a criterion: the
/// admission re-reads from its two ratios; the published material, publication and committed reach
/// are the admitted candidate's (or, refused, the certified successor's); `e` sits at the cut's
/// absolute tick; the carry identity, lineage and lattice of the applied movement; and the energy
/// identities the owners guarantee. The admission certifies only that `θ′` reads the declared
/// same-Rest comparison no worse classically and strictly better in one part; criteria 2 to 4 stay
/// measured outcomes.
#[test]
fn the_finite_decrease_landing_is_read_on_the_complete_contact_return() {
    use crate::hnn::constitution::{Carrier, FactorGradient, Family, Locus};
    use crate::hnn::physical::contact::ContactObservation;
    use crate::hnn::word::continuation::admit;
    use crate::ratio::Rat;
    use num_traits::Signed;
    let started = std::time::Instant::now();
    let field = field();
    let initial = contact_material(&field);
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let compared = vec![false, false, true];
    let observation = || ContactObservation {
        observed: encoded(&field, &[0, 1, 3]),
        compared: compared.clone(),
    };
    let mut actual =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).unwrap();
    let mut untouched =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).unwrap();
    let blind = untouched
        .communicate_contact(&source, &receiver(), |_| None)
        .unwrap();
    let taught = actual
        .communicate_contact(&source, &receiver(), |boundary| {
            assert_eq!(
                boundary, &blind.boundary,
                "observation cannot enter its earlier forward"
            );
            Some(observation())
        })
        .unwrap();
    let taught_ns = started.elapsed().as_nanos();
    assert!(blind.closes() && taught.closes());
    assert_eq!(taught.boundary, blind.boundary);
    assert_eq!(taught.blind_carry, blind.carry);
    assert_eq!(
        taught.carry.ticks, 3,
        "full ticks keep their actual complete crossing"
    );
    let publication = taught.comparison.as_ref().unwrap().as_ref().unwrap();
    let landing = &publication.landing;
    let material = actual.constitution().clone();
    let locus = Locus::Channel(0);

    // The landing's exact readings: L and X of the producing comparison, L′ and X′ of the
    // candidate's re-read, the declared exponents, the committed q, the outcome and e.
    let code = publication.ratio.code_length().unwrap();
    let excess = publication.ratio.excess();
    println!(
        "finite-decrease landing READING on 0279's own task: L=[{}, {}] X={}",
        acceptance_exact(&code.lower),
        acceptance_exact(&code.upper),
        acceptance_exact(&excess)
    );
    match &landing.candidate {
        Some(candidate) => {
            let candidate_code = candidate.ratio().code_length().unwrap();
            println!(
                "finite-decrease landing candidate: L′=[{}, {}] X′={} support={:?} tick={}",
                acceptance_exact(&candidate_code.lower),
                acceptance_exact(&candidate_code.upper),
                acceptance_exact(&candidate.ratio().excess()),
                candidate.support(),
                candidate.tick()
            );
            for (key, moved) in &candidate.committed().families {
                println!("finite-decrease landing committed {key:?}: (entry, q) = {moved:?}");
            }
        }
        None => println!("finite-decrease landing candidate: not read"),
    }
    match &landing.declared {
        Some(declared) => {
            for (key, step) in declared.families_with_steps() {
                let reach = step.reach.as_ref();
                println!(
                    "finite-decrease landing declared {key:?}: k_f={} k_cert={:?} endpoint={:?} \
                     proposed (entry, q)={:?}",
                    step.exponent,
                    reach.map(|r| r.certified),
                    reach.map(|r| r.endpoint),
                    reach.map(|r| &r.reached)
                );
            }
        }
        None => println!("finite-decrease landing declared exponents: not read"),
    }
    match &landing.outcome {
        Ok(admission) => println!(
            "finite-decrease landing: ADMITTED ({:?})",
            admission.admitted()
        ),
        Err(refusal) => println!("finite-decrease landing: REFUSED {refusal:?}"),
    }
    match &publication.continuation.landing {
        Some(e) => {
            let coordinates: Vec<&Rat> = e
                .difference
                .storage
                .iter()
                .flatten()
                .chain(e.difference.arrivals.iter().flatten().flatten())
                .chain(e.difference.states.iter().flatten().flatten())
                .chain(e.difference.resonators.iter().flatten().flatten().flatten())
                .collect();
            let nonzero: Vec<String> = coordinates
                .iter()
                .filter(|x| !x.is_zero())
                .map(|x| acceptance_exact(x))
                .collect();
            println!(
                "finite-decrease landing e = candidate_end - held at tick {}: {} of {} coordinates \
                 nonzero: [{}]",
                e.tick,
                nonzero.len(),
                coordinates.len(),
                nonzero.join(", ")
            );
        }
        None => println!("finite-decrease landing e: none (no admitted continuation)"),
    }

    // Criterion 1, read as the acceptance reader reads it.
    let lattice = initial.lattice(locus).expect("the contact's lattice");
    let carried = |xs: &[(Locus, Carrier, usize, Rat)], carrier: Carrier, entry: usize| -> Rat {
        xs.iter()
            .filter(|(l, c, i, _)| *l == locus && *c == carrier && *i == entry)
            .map(|(_, _, _, r)| r.clone())
            .sum::<Rat>()
    };
    let prior_remainders = initial.carried_remainders();
    let next_remainders = material.carried_remainders();
    let mut committed_families = 0usize;
    let (mut lineage, mut on_lattice, mut remainder_split) = (true, true, true);
    for (f, name) in ["C", "K", "D"].into_iter().enumerate() {
        let family = Family::Factor(f);
        let eta = publication.publication.family_step(locus, family);
        let vanished = publication.publication.vanished.contains(&(locus, family));
        let (before_factor, after_factor) = match f {
            0 => (initial.contact_storage(0), material.contact_storage(0)),
            1 => (initial.contact_stiffness(0), material.contact_stiffness(0)),
            _ => (
                initial.contact_dissipation(0),
                material.contact_dissipation(0),
            ),
        };
        let moved = after_factor != before_factor;
        let movement = publication
            .continuation
            .material
            .iter()
            .find(|m| m.contact == 0 && m.family == family)
            .unwrap_or_else(|| panic!("the actual deposit applied no family-{f} movement"));
        let reached = publication
            .comparison_return
            .factors()
            .iter()
            .find(|s| s.gradient.locus() == locus && s.gradient.family() == family)
            .unwrap_or_else(|| panic!("the actual deposit returned no family-{f} gradient"));
        let gradient = match &reached.gradient {
            FactorGradient::Storage { gradient, .. }
            | FactorGradient::Stiffness { gradient, .. }
            | FactorGradient::Dissipation { gradient, .. } => gradient,
            _ => unreachable!("a contact family returns a Gram-factor gradient"),
        };
        let statistic = &material.contact_scales(0)[f];
        let proposed = gradient.scaled(&(&eta / statistic));
        let coordinates: Vec<_> = movement
            .factor
            .entries()
            .iter()
            .map(|entry| lattice.div_rem(entry))
            .collect();
        let off_lattice = coordinates.iter().filter(|(_, r)| !r.is_zero()).count();
        on_lattice &= off_lattice == 0;
        let q_nonzero = coordinates.iter().filter(|(q, _)| !q.is_zero()).count();
        let q_largest = coordinates
            .iter()
            .map(|(q, _)| q.abs())
            .max()
            .unwrap_or_default();
        for (i, (delta, applied)) in proposed
            .entries()
            .iter()
            .zip(movement.factor.entries())
            .enumerate()
        {
            let released = publication
                .publication
                .released
                .iter()
                .filter(|(l, c, j, _)| *l == locus && *c == Carrier::Factor(f) && *j == i)
                .map(|(_, _, _, r)| r.clone())
                .sum::<Rat>();
            remainder_split &= delta + carried(&prior_remainders, Carrier::Factor(f), i)
                == applied + carried(&next_remainders, Carrier::Factor(f), i) + released;
        }
        lineage &= before_factor.add(&movement.factor).unwrap() == *after_factor;
        let committed =
            !vanished && moved && off_lattice == 0 && q_nonzero > 0 && eta.is_positive();
        committed_families += usize::from(committed);
        println!(
            "finite-decrease landing criterion 1 family {name}: published eta={} vanished={vanished} \
             material_moved={moved}; applied q != 0 at {q_nonzero} of {} entries (largest |q|=\
             {q_largest}) => {}",
            acceptance_exact(&eta),
            coordinates.len(),
            acceptance_verdict(committed)
        );
    }
    let met1 = committed_families > 0;

    // Criteria 2 to 4: the later communication against the unmoved control at the same entering
    // end, the energy accounting, and the cold restore.
    let entering = actual.opening();
    let common = actual.into_resident();
    let mut actual = PhysicalReceiver::from_resident(&field, common).unwrap();
    let other_source = encoded(&field, &[2, 1]);
    let mut prior =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), entering.clone()).unwrap();
    assert_eq!(prior.opening(), entering, "the control shares the learned point's entering end");
    let cold = acceptance_cold(&field, &actual, &other_source, &receiver());
    let next = actual
        .communicate(&other_source, &receiver(), |_| None)
        .unwrap();
    let old_material = prior
        .communicate(&other_source, &receiver(), |_| None)
        .unwrap();
    let difference =
        acceptance_difference(next.boundary.readings(), old_material.boundary.readings());
    let compared_stations: Vec<usize> = compared
        .iter()
        .enumerate()
        .filter(|(_, c)| **c)
        .map(|(station, _)| station)
        .collect();
    let compared_present = difference
        .iter()
        .any(|(station, _)| compared_stations.contains(station));
    let compared_changed: usize = difference
        .iter()
        .filter(|(station, _)| compared_stations.contains(station))
        .map(|(_, d)| d.iter().filter(|x| !x.is_zero()).count())
        .sum();
    let met2 = compared_present && compared_changed > 0;
    let continuation = &publication.continuation;
    let deposit_world = acceptance_world(&taught.opening, &taught.balances, &taught.word);
    let later_world = acceptance_world(&next.opening, &next.balances, &next.word);
    let held_work_gap =
        (&continuation.committed - &continuation.before) - &continuation.deposition_work;
    let chain_gap = &next.opening.before - &continuation.opening;
    let identities_exact = deposit_world.closes
        && later_world.closes
        && deposit_world.opening_gap.is_zero()
        && later_world.opening_gap.is_zero()
        && held_work_gap.is_zero()
        && chain_gap.is_zero();
    let met3 = identities_exact && met1;
    let met4 = match &cold {
        Ok(restored) => {
            restored.same_material
                && restored.same_carry
                && restored.same_current
                && restored.later.closes()
                && restored.later.boundary.readings() == next.boundary.readings()
                && acceptance_difference(
                    restored.later.boundary.readings(),
                    old_material.boundary.readings(),
                ) == difference
                && met2
        }
        Err(_) => false,
    };
    println!(
        "finite-decrease landing criterion 1 (a reached C/K/D deposit commits q != 0): \
         {committed_families} of 3 families => {}",
        acceptance_verdict(met1)
    );
    println!(
        "finite-decrease landing criterion 2 (the later compared-station response differs from the \
         unmoved-material control): {compared_changed} coordinates differ at {compared_stations:?} \
         => {}",
        acceptance_verdict(met2)
    );
    println!(
        "finite-decrease landing criterion 3 (the world and material energy balance closes exactly \
         on a committed change): identities exact={identities_exact}, chain residual={} => {}",
        acceptance_exact(&chain_gap),
        acceptance_verdict(met3)
    );
    println!(
        "finite-decrease landing criterion 4 (the same difference survives a cold restore): \
         restore={} => {}",
        match &cold {
            Ok(restored) => format!(
                "material={} carry={} current={}",
                restored.same_material, restored.same_carry, restored.same_current
            ),
            Err(refusal) => format!("REFUSED {refusal:?}"),
        },
        acceptance_verdict(met4)
    );

    // The admission's own laws and the trust invariants. None asserts a criterion.
    if let Some(declared) = &landing.declared {
        for ((at, _), step) in declared.families_with_steps() {
            let reach = step.reach.as_ref().expect("the first-reach read claims its families");
            assert_eq!(*at, locus);
            assert_eq!(step.exponent, reach.exponent);
            assert!(reach.certified <= reach.exponent && reach.exponent <= reach.endpoint);
            assert!(!reach.reached.is_empty() && reach.reached.iter().all(|(_, q)| !q.is_zero()));
        }
    }
    match &landing.outcome {
        Ok(admission) => {
            let candidate = landing
                .candidate
                .as_ref()
                .expect("an admitted candidate was read");
            assert_eq!(candidate, admission.candidate());
            assert_eq!(admission.ratio(), &publication.ratio);
            assert_eq!(
                admit(&publication.ratio, candidate.ratio()),
                Ok(admission.admitted()),
                "the admission re-reads from its two ratios"
            );
            assert_eq!(&material, candidate.theta(), "the published material is the candidate");
            assert_eq!(&publication.publication, candidate.publication());
            for (key, step) in candidate.declared().families_with_steps() {
                assert_eq!(
                    candidate.committed().families.get(key),
                    step.reach.as_ref().map(|reach| &reach.reached),
                    "the committed reach is the proposed reach"
                );
            }
            let e = continuation
                .landing
                .as_ref()
                .expect("the admitted continuation reads e");
            assert_eq!(e.tick, taught.carry.ticks, "e sits at the cut's absolute tick");
        }
        Err(_) => {
            assert!(continuation.landing.is_none());
            let operands =
                crate::hnn::propagation::Operands::exact_at_cut(&field, &initial, &current).unwrap();
            let spans = crate::hnn::word::finite_gain::FiniteContactSpans::of(
                &operands,
                0,
                publication.comparison_return.reach().unwrap(),
            )
            .unwrap();
            let (native, reading) = initial
                .deposited_with_contact_spans(&publication.comparison_return, &spans)
                .unwrap();
            assert_eq!(material, native, "a refused landing continues on the certified step");
            assert_eq!(publication.publication, reading);
        }
    }
    assert!(lineage, "each family's applied factor reaches the resident unchanged");
    assert!(on_lattice, "every applied movement lies on its family's lattice");
    assert!(
        remainder_split,
        "delta + r_prior = applied + r_next + released, exactly, entry by entry"
    );
    assert!(
        deposit_world.closes && later_world.closes,
        "the owner's world receipts close"
    );
    assert!(
        deposit_world.opening_gap.is_zero()
            && later_world.opening_gap.is_zero()
            && held_work_gap.is_zero(),
        "the owner's energy identities have no residual"
    );
    assert!(next.closes() && old_material.closes());
    assert_eq!(next.carry.ticks, taught.carry.ticks + 2);
    assert_eq!(prior.constitution(), &initial, "the control is truly unmoved");
    println!("finite-decrease landing: every trust assertion passed; the readings above are verified");
    let met = [met1, met2, met3, met4];
    println!(
        "finite-decrease landing: {} of 4 criteria met (a reading, not an acceptance); timing: \
         taught_ns={taught_ns} elapsed_ns={}",
        met.iter().filter(|m| **m).count(),
        started.elapsed().as_nanos()
    );
}

/// [agent-inferred, October 9; the medium-of-joints record §7; #73] **The second learned publication,
/// READ on 0279's own task.** Call 1 is L's first landing at Rest (source `[0, 1]`, observed
/// `[0, 1, 3]`, station 2 compared). Call 2 repeats that observation on the published material, at the
/// received opening call 1 left: its landing re-reads the Word's own received opening through `θ′` at
/// held momentum. The existing communication on source `[2, 1]` then reads the later response, beside a
/// control holding call 1's material at the same entering end.
///
/// A READING, never an acceptance. The four criteria of
/// `the_learned_change_acceptance_is_read_on_the_complete_contact_return`, applied to the SECOND
/// publication (its committed change measured against call 1's material), are printed PASS or
/// NOT-MET, and none is asserted: (1) a reached C/K/D deposit commits `q != 0` at call 2; (2) the later
/// compared-station response differs from the control; (3) the world and material energy balance
/// closes exactly over that committed change; (4) the same difference survives a cold restore. The
/// assertions are trust invariants only: the opening call 2 entered, each applied movement's lineage
/// and lattice, the owner's energy identities, and the control's material.
#[test]
fn a_second_learned_publication_is_read_at_its_received_opening() {
    use crate::hnn::constitution::{Family, Locus};
    use crate::hnn::physical::contact::ContactObservation;
    use crate::hnn::word::continuation::FiniteDecrease;
    use crate::ratio::Rat;
    use num_traits::Signed;
    let field = field();
    let initial = contact_material(&field);
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let compared = vec![false, false, true];
    let observation = || ContactObservation {
        observed: encoded(&field, &[0, 1, 3]),
        compared: compared.clone(),
    };
    let mut actual =
        PhysicalReceiver::new(&field, initial.clone(), current.clone(), WordOpening::Rest).unwrap();
    let first = actual
        .communicate_contact(&source, &receiver(), |_| Some(observation()))
        .unwrap();
    assert!(first.closes());
    let first_outcome = first
        .comparison
        .as_ref()
        .unwrap()
        .as_ref()
        .unwrap()
        .landing
        .outcome
        .as_ref()
        .map(FiniteDecrease::admitted)
        .map_err(|refusal| format!("{refusal:?}"));
    let after_first = actual.constitution().clone();
    assert!(
        matches!(actual.opening(), WordOpening::Received { .. }),
        "call 2 opens on the carry call 1 published"
    );
    let second = actual
        .communicate_contact(&source, &receiver(), |_| Some(observation()))
        .unwrap();
    assert!(second.closes());
    let publication = second.comparison.as_ref().unwrap().as_ref().unwrap();
    let after_second = actual.constitution().clone();
    let landing = &publication.landing;
    println!(
        "second publication READING on 0279's own task: call 1 at Rest landed {first_outcome:?}; \
         call 2 at the received opening: declared {:?}, outcome {:?}",
        landing.declared,
        landing
            .outcome
            .as_ref()
            .map(FiniteDecrease::admitted)
            .map_err(|refusal| format!("{refusal:?}"))
    );
    match &publication.continuation.landing {
        Some(e) => {
            let coordinates: Vec<&Rat> = e
                .difference
                .storage
                .iter()
                .flatten()
                .chain(e.difference.arrivals.iter().flatten().flatten())
                .chain(e.difference.states.iter().flatten().flatten())
                .chain(e.difference.resonators.iter().flatten().flatten().flatten())
                .collect();
            let nonzero = coordinates.iter().filter(|x| !x.is_zero()).count();
            println!(
                "second publication e = candidate_end - held at tick {}: {nonzero} of {} coordinates \
                 nonzero",
                e.tick,
                coordinates.len()
            );
        }
        None => println!("second publication e: none (no admitted continuation at call 2)"),
    }

    // Criterion 1 at call 2: the committed change against call 1's material.
    let locus = Locus::Channel(0);
    let lattice = initial.lattice(locus).expect("the contact's lattice");
    let mut committed_families = 0usize;
    let (mut lineage, mut on_lattice) = (true, true);
    for (f, name) in ["C", "K", "D"].into_iter().enumerate() {
        let family = Family::Factor(f);
        let eta = publication.publication.family_step(locus, family);
        let vanished = publication.publication.vanished.contains(&(locus, family));
        let (before, after) = match f {
            0 => (after_first.contact_storage(0), after_second.contact_storage(0)),
            1 => (after_first.contact_stiffness(0), after_second.contact_stiffness(0)),
            _ => (
                after_first.contact_dissipation(0),
                after_second.contact_dissipation(0),
            ),
        };
        let moved = after != before;
        let movement = publication
            .continuation
            .material
            .iter()
            .find(|m| m.contact == 0 && m.family == family)
            .unwrap_or_else(|| panic!("the second deposit applied no family-{f} movement"));
        let coordinates: Vec<_> = movement
            .factor
            .entries()
            .iter()
            .map(|entry| lattice.div_rem(entry))
            .collect();
        let off_lattice = coordinates.iter().filter(|(_, r)| !r.is_zero()).count();
        on_lattice &= off_lattice == 0;
        let q_nonzero = coordinates.iter().filter(|(q, _)| !q.is_zero()).count();
        lineage &= before.add(&movement.factor).unwrap() == *after;
        let committed =
            !vanished && moved && off_lattice == 0 && q_nonzero > 0 && eta.is_positive();
        committed_families += usize::from(committed);
        println!(
            "second publication criterion 1 family {name}: eta={} vanished={vanished} \
             material_moved={moved}; applied q != 0 at {q_nonzero} of {} entries => {}",
            acceptance_exact(&eta),
            coordinates.len(),
            acceptance_verdict(committed)
        );
    }
    let met1 = committed_families > 0;

    // Criterion 2: the later response against call 1's material at the same entering end.
    let entering = actual.opening();
    let mut control =
        PhysicalReceiver::new(&field, after_first.clone(), current.clone(), entering).unwrap();
    let other_source = encoded(&field, &[2, 1]);
    let cold = acceptance_cold(&field, &actual, &other_source, &receiver());
    let next = actual
        .communicate(&other_source, &receiver(), |_| None)
        .unwrap();
    let old = control
        .communicate(&other_source, &receiver(), |_| None)
        .unwrap();
    let difference = acceptance_difference(next.boundary.readings(), old.boundary.readings());
    let is_compared = |station: usize| compared.get(station).copied().unwrap_or(false);
    let compared_present = difference.iter().any(|(station, _)| is_compared(*station));
    let compared_changed: usize = difference
        .iter()
        .filter(|(station, _)| is_compared(*station))
        .map(|(_, d)| d.iter().filter(|x| !x.is_zero()).count())
        .sum();
    let met2 = compared_present && compared_changed > 0;
    println!(
        "second publication criterion 2: {compared_changed} compared-station coordinates differ \
         from call 1's material (present={compared_present}) => {}",
        acceptance_verdict(met2)
    );

    // Criterion 3: the world and material energy balance over the second committed change.
    let continuation = &publication.continuation;
    let deposit_world = acceptance_world(&second.opening, &second.balances, &second.word);
    let later_world = acceptance_world(&next.opening, &next.balances, &next.word);
    let held_work_gap =
        (&continuation.committed - &continuation.before) - &continuation.deposition_work;
    let chain_gap = &next.opening.before - &continuation.opening;
    let identities = deposit_world.closes
        && later_world.closes
        && deposit_world.opening_gap.is_zero()
        && later_world.opening_gap.is_zero()
        && held_work_gap.is_zero()
        && chain_gap.is_zero();
    let met3 = identities && met1;
    println!(
        "second publication criterion 3: identities close exactly={identities} (held work \
         residual {}, chain residual {}) committed change present={met1} => {}",
        acceptance_exact(&held_work_gap),
        acceptance_exact(&chain_gap),
        acceptance_verdict(met3)
    );

    // Criterion 4: the same difference survives a cold restore of the post-call-2 point.
    let (met4, cold_reading) = match &cold {
        Err(refusal) => (false, format!("cold remount REFUSED {refusal:?}")),
        Ok(restored) => {
            let same_difference = restored.same_carry
                && acceptance_difference(restored.later.boundary.readings(), old.boundary.readings())
                    == difference;
            let same_response = restored.later.boundary.readings() == next.boundary.readings();
            let closes = restored.later.closes();
            (
                restored.same_material
                    && restored.same_carry
                    && restored.same_current
                    && closes
                    && same_response
                    && same_difference
                    && met2,
                format!(
                    "restored material/carry/current == live: {}/{}/{}; cold later response == \
                     live {same_response}; cold difference == live {same_difference}; closes \
                     {closes}",
                    restored.same_material, restored.same_carry, restored.same_current
                ),
            )
        }
    };
    println!(
        "second publication criterion 4: {cold_reading} => {}",
        acceptance_verdict(met4)
    );
    let met = [met1, met2, met3, met4].iter().filter(|m| **m).count();
    println!("second publication READING: {met} of 4 criteria met (a reading, not an acceptance)");

    // Trust invariants only; no criterion is asserted.
    assert!(lineage, "each family's applied factor reaches the resident unchanged");
    assert!(on_lattice, "every applied movement lies on its family's lattice");
    assert!(deposit_world.closes && later_world.closes, "the owner's world receipts close");
    assert!(
        deposit_world.opening_gap.is_zero()
            && later_world.opening_gap.is_zero()
            && held_work_gap.is_zero(),
        "the owner's energy identities have no residual"
    );
    assert!(next.closes() && old.closes());
    assert_eq!(control.constitution(), &after_first, "the control holds call 1's material");
    assert_eq!(old.carry.ticks, next.carry.ticks);
}
