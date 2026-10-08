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
    use crate::hnn::constitution::{Carrier, Locus};
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
    assert_eq!(pending.iter().filter(|(_,c,_,_)| *c==Carrier::Factor(0)).count(),
        initial.contact_storage(0).entries().len());
    assert!(publication.publication.released.iter().all(|(_,c,_,_)|
        !matches!(c,Carrier::Factor(_) | Carrier::FactorScale(_))));
    assert_eq!(learned.contact_storage(0),initial.contact_storage(0),
        "exact unresolved direction is not an immediate physical storage move");
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
    assert!(publication.publication.stepped > 0, "this fixed native control remains unaccepted until an actual move");
    assert_ne!(actual.constitution().contact_storage(0), initial.contact_storage(0));
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
    assert_ne!(next.boundary.readings(), old_material.boundary.readings());
    assert_ne!(next.boundary.readings(), old_source.boundary.readings());
    println!("whole carried existing communication boundary: {:?}", next.boundary);
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
