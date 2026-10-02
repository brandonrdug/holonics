//! A native channel re-base at a continuing helical pair (Refs #62 #73).
//!
//! [definition; agent-inferred] Re-basing preserves factor-plus-carry, not the applied material.
//! At the same carried z=(u,w), W=1/2(w^T ΔC w+u^T ΔK u) is the material work. The stationary
//! chart changes with the material: r'=r-(K_chart'-K_chart)x. The accepted ContactCut consumer
//! reads the actual next junction and transit; no propagation or receiving owner is duplicated.
//! Pair, helix, faces and tube are read here; cell holonomy and tower restrictions stay attached.
//! The recorded omitted-work and located-cause failures are avoided by carrying the same state,
//! clock and pump phase and by checking the native committed balance before any aggregate code.

use num_traits::{One, Zero};

use super::contact_residual::{ContactCut, Read, Refusal};
use super::learning::{OPEN_BUDGET, chain, chain_reach};
use super::support::Draw;
use crate::hnn::constitution::{
    BudgetedCarry, Carrier, ChartRule, Constitution, FactorGradient, FactorStep, Lattice, Locus,
    NormalLaw, Sample, receiving_class_metric,
};
use crate::hnn::field::{ConstitutionRead, Current};
use crate::hnn::port::Deposit;
use crate::hnn::propagation::Operands;
use crate::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
use crate::hnn::word::{PowerForm, Word, WordBalance};
use crate::holon::parametron::Carrier as PumpCarrier;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{dot, scale, sub};
use crate::ratio::{Rat, integer, rat};

/// These are declared factor covectors, not a claimed learned comparison. One contemporary native
/// return builds genuine carried remainders; the tested consumer is the subsequent native re-base.
fn stage(theta: &Constitution, width: usize) -> Deposit {
    let gradient = ExactRatMatrix::identity(width).unwrap();
    Deposit::new(
        theta.commit(),
        Vec::new(),
        vec![
            FactorStep {
                gradient: FactorGradient::Storage {
                    contact: 0,
                    gradient: gradient.clone(),
                },
                energy: integer(2),
                covector: Rat::one(),
            },
            FactorStep {
                gradient: FactorGradient::Stiffness {
                    contact: 0,
                    gradient,
                },
                energy: integer(2),
                covector: Rat::one(),
            },
        ],
        vec![Locus::Channel(0)],
    )
    .with_reach(chain_reach())
}

fn channel_entries(theta: &Constitution, carrier: Carrier) -> Vec<Rat> {
    match carrier {
        Carrier::Factor(0) => theta.contact_storage(0).entries().to_vec(),
        Carrier::Factor(1) => theta.contact_stiffness(0).entries().to_vec(),
        Carrier::Factor(2) => theta.contact_dissipation(0).entries().to_vec(),
        Carrier::FactorScale(i) => vec![theta.contact_scales(0)[i].clone()],
        _ => unreachable!("six native channel carriers"),
    }
}

#[test]
fn native_rebase_moves_material_at_the_same_carried_boundary_with_work() {
    // Exact elapsed milliseconds belong only to this exterior diagnostic receipt.
    let started = std::time::Instant::now();
    macro_rules! mark {
        ($stage:expr) => {
            eprintln!(
                "stage={} elapsed_ms={}",
                $stage,
                started.elapsed().as_millis()
            );
        };
    }
    mark!("field:begin");
    let field = chain().with_exact_word();
    mark!("field:done");
    let current = Current::at_rest(&field);
    let pump =
        PumpDeclaration::new(rat(1, 16), PumpCarrier::at(&rat(1, 2)), PumpStep::Half).unwrap();
    mark!("resonator-material:begin");
    let resonator =
        ResonatorMaterial::of_parametron(field.ring(0).parametron(), &rat(1, 8), Some(pump))
            .unwrap();
    mark!("resonator-material:done");
    mark!("constitution-passive-initial:begin");
    let mut theta = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    mark!("constitution-passive-initial:done");
    // [agent-inferred] Carry formation is a declared native material fixture, not a learned
    // comparison through the pumped medium. The pump is founded before either word opens.
    for n in 0..1 {
        let deposit = stage(&theta, field.contact(0).width());
        mark!(format!("native-deposit-{n}:begin"));
        let (next, reading) = theta.deposited(&deposit).unwrap();
        mark!(format!("native-deposit-{n}:done"));
        assert!(reading.stepped > 0);
        theta = next;
    }
    mark!("passive-native-carries:check");
    for carrier in [Carrier::Factor(0), Carrier::Factor(1)] {
        assert!(
            theta
                .carried_remainders()
                .iter()
                .any(|(l, c, _, r)| (*l, *c) == (Locus::Channel(0), carrier) && !r.is_zero()),
            "both C and K require genuine nonzero native factor carry"
        );
    }
    mark!("declare-pump-before-word:begin");
    theta = theta.with_ring_resonator(&field, 0, resonator).unwrap();
    mark!("declare-pump-before-word:done");
    let locus = Locus::Channel(0);
    assert!(
        theta
            .carried_remainders()
            .iter()
            .any(|(l, _, _, r)| *l == locus && !r.is_zero())
    );
    let stale = stage(&theta, field.contact(0).width());
    mark!("native-rebase:begin");
    let successor = theta.rebased(locus, 3).unwrap();
    mark!("native-rebase:done");
    assert_eq!(theta.rebased(locus, 0).unwrap(), theta);
    assert_eq!(successor.commit(), theta.commit() + 1);
    assert_eq!(successor.clock(locus), theta.clock(locus));
    let finer = successor.lattice(locus).unwrap();
    assert_eq!(
        finer.exponent(),
        theta.lattice(locus).unwrap().exponent() + 3
    );
    assert!(successor.on_lattice());
    assert!(successor.storage_product() >= theta.storage_product());
    assert!(matches!(
        successor.deposited(&stale),
        Err(crate::hnn::HnnError::StaleDeposit { .. })
    ));
    for carrier in [
        Carrier::Factor(0),
        Carrier::Factor(1),
        Carrier::Factor(2),
        Carrier::FactorScale(0),
        Carrier::FactorScale(1),
        Carrier::FactorScale(2),
    ] {
        let total = |t: &Constitution| {
            let mut entries = channel_entries(t, carrier);
            for (l, c, i, r) in t.carried_remainders() {
                if (l, c) == (locus, carrier) {
                    entries[i] += r;
                }
            }
            entries
        };
        assert_eq!(total(&successor), total(&theta));
        let half = finer.unit() / integer(2);
        for (l, c, _, r) in successor.carried_remainders() {
            if (l, c) == (locus, carrier) {
                assert!(-&half <= r && r < half);
            }
        }
    }
    let unaffected = |t: &Constitution| {
        t.carried_remainders()
            .into_iter()
            .filter(|(l, ..)| *l != locus)
            .collect::<Vec<_>>()
    };
    assert_eq!(unaffected(&successor), unaffected(&theta));
    for a in 1..field.contacts().len() {
        assert_eq!(successor.contact_storage(a), theta.contact_storage(a));
        assert_eq!(successor.contact_stiffness(a), theta.contact_stiffness(a));
        assert_eq!(
            successor.contact_dissipation(a),
            theta.contact_dissipation(a)
        );
        assert_eq!(
            successor.clock(Locus::Channel(a)),
            theta.clock(Locus::Channel(a))
        );
    }
    for g in 0..field.rings().len() {
        assert_eq!(successor.source_law(g), theta.source_law(g));
        assert_eq!(successor.receiving_map(g), theta.receiving_map(g));
        assert_eq!(successor.resonator(g), theta.resonator(g));
    }

    mark!("rebase-invariants:done");
    mark!("old-operands:begin");
    let old_operands = Operands::exact_at_cut(&field, &theta, &current).unwrap();
    mark!("old-operands:done");
    mark!("new-operands:begin");
    let new_operands = Operands::exact_at_cut(&field, &successor, &current).unwrap();
    mark!("new-operands:done");
    let (old_c, old_k, _) = old_operands.contacts()[0].forms();
    let (new_c, new_k, _) = new_operands.contacts()[0].forms();
    assert_ne!(old_c, new_c, "applied C must actually move");
    assert_ne!(old_k, new_k, "applied K must actually move");
    assert_eq!(old_operands.rings(), new_operands.rings());
    assert_eq!(old_operands.resonators(), new_operands.resonators());
    let mut draw = Draw::new(74);
    let injected = field
        .rings()
        .iter()
        .map(|r| draw.half_vector(r.width()))
        .collect();
    mark!("C-K-movement-and-unchanged-ring-pump:passed");
    mark!("first-word:begin");
    let mut first = Word::on_operands(&field, old_operands.clone(), injected).unwrap();
    first.run(2).unwrap();
    mark!("first-word:done");
    mark!("cut-and-power-forms:begin");
    let cut = ContactCut::read(&first, &theta, &current).unwrap();
    let nothing: Vec<_> = cut
        .change
        .storage
        .iter()
        .map(|v| vec![Rat::zero(); v.len()])
        .collect();
    let (old_power, new_power) = (
        PowerForm::read(&field, &theta, &current).unwrap(),
        PowerForm::read(&field, &successor, &current).unwrap(),
    );
    mark!("cut-and-power-forms:done");
    mark!("exact-material-work:begin");
    let work = old_power.deposition_work(&new_power, &cut.change).unwrap();
    let z = &cut.change.states[0];
    let explicit_work = (dot(&z[1], &new_c.subtract(old_c).unwrap().apply(&z[1]).unwrap())
        + dot(&z[0], &new_k.subtract(old_k).unwrap().apply(&z[0]).unwrap()))
        / integer(2);
    assert!(!work.is_zero());
    assert_eq!(work, explicit_work);
    assert_eq!(
        new_power.power(&cut.change).unwrap() - old_power.power(&cut.change).unwrap(),
        work
    );
    let resonator_open = old_power.resonator_power(&cut.change).unwrap();
    assert!(!resonator_open.is_zero());
    assert_eq!(
        new_power.resonator_power(&cut.change).unwrap(),
        resonator_open
    );

    mark!("exact-material-work-and-resonator-opening:passed");
    mark!("continuation-opening:begin");
    assert!(matches!(
        cut.continuing(&field, &successor, &current, &nothing, 3),
        Err(Refusal::Clock)
    ));
    let mut before = cut
        .continuing(&field, &theta, &current, &nothing, 2)
        .unwrap();
    let mut after = cut
        .continuing(&field, &successor, &current, &nothing, 2)
        .unwrap();
    assert_eq!(before.change().unwrap(), cut.change);
    assert_eq!(after.change().unwrap(), cut.change);
    assert_eq!(before.clock(), after.clock());
    let (old_cut, new_cut) = (
        ContactCut::read(&before, &theta, &current).unwrap(),
        ContactCut::read(&after, &successor, &current).unwrap(),
    );
    mark!("same-state-clock-pump-continuation-opening:passed");
    mark!("continuation-old-two-ticks:begin");
    before.run(2).unwrap();
    mark!("continuation-old-two-ticks:done");
    mark!("continuation-new-two-ticks:begin");
    after.run(2).unwrap();
    mark!("continuation-new-two-ticks:done");
    mark!("first-transit-and-reflected-residual:begin");
    let old_step = old_cut.first_step(&before, &theta, &current, 0).unwrap();
    let new_step = new_cut.first_step(&after, &successor, &current, 0).unwrap();
    for step in [&old_step, &new_step] {
        assert!(step.boundary_advanced);
        assert!(step.remainder.as_ref().unwrap().iter().all(Zero::is_zero));
    }
    let (Read::Unique(old), Read::Unique(new)) = (&old_step.before, &new_step.before) else {
        panic!(
            "this fixture declares nonsingular stiffness; no inverse is claimed for other fibres"
        )
    };
    assert_eq!(old.interior, new.interior);
    assert_eq!(old.boundary, new.boundary);
    assert!(old.closes() && new.closes());
    assert_eq!(&new.energy - &old.energy, work);
    let chart_change = new.chart.subtract(&old.chart).unwrap();
    assert!(chart_change.entries().iter().any(|x| !x.is_zero()));
    assert_eq!(
        sub(&new.residual, &old.residual),
        scale(&-Rat::one(), &chart_change.apply(&old.boundary).unwrap())
    );
    mark!("exact-transit-and-reflected-residual:passed");
    mark!("word-balances-and-commit:begin");
    for word in [before, after] {
        for tick in word.field_balances() {
            assert!(tick.closes());
        }
        let balance = WordBalance::of(&word.release().unwrap());
        assert_eq!(balance.resonator_open, resonator_open);
        assert!(balance.closes());
    }
    // The terminal junction changes waves, but keeps the same contact interior and pump phase.
    // Its committed balance therefore reads the same material work as the earlier full-tick cut.
    let mut balance = WordBalance::of(&first.release().unwrap());
    assert_eq!(balance.change.states, cut.change.states);
    assert_eq!(balance.change.resonator_phases, cut.change.resonator_phases);
    assert!(balance.closes());
    balance.commit(&old_power, &new_power).unwrap();
    assert_eq!(balance.commit.as_ref().unwrap().deposition, work);
    assert!(balance.closes());
    mark!("word-balances-and-commit:passed");
    println!(
        "native rebase: C/K moved; unchanged factor+carry, clock/state/phase; W={work}; reflected chart and committed balance close"
    );
}

/// Standalone direction diagnostic. It reads the normal-law consumer, not the receiving
/// certificate that another worker owns: the original comparison covector pairs with the
/// scaled direction. Scaling the covector again gives a different quantity, not that comparison.
#[test]
fn class_metric_direction_pairs_with_the_original_comparison_covector() {
    let original = Sample {
        weight: Rat::one(),
        feature: vec![Rat::one()],
        covector: vec![rat(1, 2), Rat::zero(), rat(-1, 2), Rat::zero()],
    };
    let metric = receiving_class_metric(std::slice::from_ref(&original)).unwrap();
    assert_eq!(metric, integer(2));
    let mut scaled = original.clone();
    for (i, g) in scaled.covector.iter_mut().enumerate() {
        if i % 2 == 0 {
            *g *= &metric;
        }
    }
    let law = NormalLaw::with_prior(ExactRatMatrix::zero(4, 1).unwrap());
    let rule = ChartRule::new(Lattice::new(9), 16);
    let mut carry = BudgetedCarry::new(Lattice::new(9), 1);
    let (next, _) = law
        .deposited(
            std::slice::from_ref(&scaled),
            &Rat::one(),
            &rule,
            &mut carry,
        )
        .unwrap();
    let direction = next.map().apply(&original.feature).unwrap();
    assert_eq!(
        next.gram(),
        ExactRatMatrix::new(vec![vec![integer(2)]]).unwrap()
    );
    assert_eq!(
        next.solved(),
        ExactRatMatrix::new(vec![vec![rat(1, 2)]]).unwrap()
    );
    assert_eq!(direction, original.covector);
    let original_alignment = dot(&original.covector, &direction);
    let scaled_alignment = dot(&scaled.covector, &direction);
    assert_eq!(original_alignment, rat(1, 2));
    assert_eq!(scaled_alignment, Rat::one());
    // Smooth decrease log_2(4/3) is strictly below 1/2: (4/3)^2=16/9<2.
    // This exact ordering claims no strict decrease for the quantized receiver score.
    assert!(rat(4, 3) * rat(4, 3) < integer(2));
    println!(
        "native direction: class metric={metric}; original pairing={original_alignment}; scaled pairing={scaled_alignment}; (4/3)^2<2"
    );
}
