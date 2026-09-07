//! A measured conditional phase action using the public native field and local relation.
//! The driver controls source/condition ports and observes returns; all learning is in the
//! standing engine owner. The reported local family is not a text/audio model artifact.

use holonic_engine::{
    dimensional_wave::ExactComplexWaveCurrent,
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, ConditionPreimageReading, ConstitutiveFibreError,
        ConstitutiveReading, NativeConstitutiveField, NativeFieldOccurrence, NativeJunctionSeed,
        NativePhaseCurrent, ResidentConstitutiveCurrent, ResidentConstitutiveFibre,
        ResidentConstitutiveReturn,
    },
    resident_section::{
        ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface, TransferCensus,
    },
};
use serde_json::{Value, json};
use std::{error::Error, fs::OpenOptions, io::Write, path::PathBuf, time::Instant};

fn phase(r: i64, i: i64, d: i64) -> Result<NativePhaseCurrent, ConstitutiveFibreError> {
    NativePhaseCurrent::new(r, i, d)
}
fn mount<'c>(
    surface: &'c ResidentSurface<'c>,
    values: &[i64],
) -> Result<ResidentSection<'c>, Box<dyn Error>> {
    Ok(surface.mount_section_rest(&ResidentSectionRest::found(
        1,
        values.len(),
        ResidentGrain(0),
        64,
        values.iter().map(|v| (*v, *v)).collect(),
    )?)?)
}
fn rational<'a, 'c>(
    section: &'a ResidentSection<'c>,
) -> Result<ResidentConstitutiveCurrent<'a, 'c>, ConstitutiveFibreError> {
    ResidentConstitutiveCurrent::rational(section)
}
fn returned(
    result: &ResidentConstitutiveReturn<'_>,
) -> Result<ExactComplexWaveCurrent, Box<dyn Error>> {
    match result.inspect()?.predecessor_reading {
        ConstitutiveReading::Unique { current } => Ok(ExactComplexWaveCurrent::new(
            current[0].clone(),
            current[1].clone(),
        )),
        other => Err(format!("conditional phase receiver remains {other:?}").into()),
    }
}
fn face(current: &ExactComplexWaveCurrent) -> Value {
    json!({"real":current.real.to_string(),"imaginary":current.imaginary.to_string(),
        "norm_square":current.norm_square().to_string()})
}
fn delta(before: TransferCensus, after: TransferCensus) -> Value {
    json!({"deeds":after.deed_launches-before.deed_launches,
        "section_readouts":after.section_read_outs-before.section_read_outs,
        "ingress_octets":after.ingress_octets-before.ingress_octets,
        "numerical_egress_octets":after.egress_section_octets-before.egress_section_octets,
        "receipt_egress_octets":after.egress_receipt_octets-before.egress_receipt_octets})
}
fn observe(
    field: &mut NativeConstitutiveField<'_>,
    source: NativePhaseCurrent,
    condition: NativePhaseCurrent,
) -> Result<ExactComplexWaveCurrent, ConstitutiveFibreError> {
    field.replace_incoming_transport(0, condition)?;
    let actual = field.advance_status(&mut NativeFieldOccurrence::entering(vec![source]))?;
    Ok(actual.held_successor[0].clone())
}
fn main() -> Result<(), Box<dyn Error>> {
    let path = PathBuf::from(
        std::env::args()
            .nth(1)
            .ok_or("usage: native_conditioned_phase NEW.json")?,
    );
    if path.exists() {
        return Err("report already exists".into());
    }
    let start = Instant::now();
    let readout = ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    let mut world = NativeConstitutiveField::found(
        &surface,
        vec![NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        }],
    )?;
    let mut learner = ResidentConstitutiveFibre::found_bilinear_contact(&surface, 1, 1, 1)?;
    let mut observations = Vec::new();
    let development_start = Instant::now();
    for (x, c) in [
        ([0, 0], [1, 0]),
        ([0, 0], [0, 1]),
        ([1, 0], [1, 0]),
        ([0, 1], [1, 0]),
        ([1, 0], [-1, 0]),
        ([0, 1], [-1, 0]),
    ] {
        let x = phase(x[0], x[1], 1)?;
        let c = phase(c[0], c[1], 1)?;
        let measured = observe(&mut world, x, c)?;
        let xs = mount(&surface, &x.words())?;
        let cs = mount(&surface, &c.words())?;
        let ys = mount(
            &surface,
            &NativePhaseCurrent::from_current(&measured)?.words(),
        )?;
        let before = learner.census();
        let result = learner.advance_bilinear_contact(
            rational(&xs)?,
            rational(&cs)?,
            Some(rational(&ys)?),
        )?;
        let work = delta(before, learner.census());
        observations.push(json!({"source":x,"condition":c,"measured":face(&measured),
            "learner_work":work,"return":result.inspect()?}));
    }
    let development_seconds = development_start.elapsed().as_secs_f64();
    let x = phase(2, 3, 1)?;
    let c = phase(3, 4, 5)?;
    let xs = mount(&surface, &x.words())?;
    let cs = mount(&surface, &c.words())?;
    let before = learner.census();
    let predicted = learner.advance_bilinear_contact(rational(&xs)?, rational(&cs)?, None)?;
    let prediction_work = delta(before, learner.census());
    // This previously unseen physical condition is executed only after prediction.
    let actual = observe(&mut world, x, c)?;
    let predicted = returned(&predicted)?;
    // This phase is controlled by the world but never supplied to the learner. Only the actual
    // source and its later native return enter the condition Preimage Fibre.
    let hidden_condition = phase(-5, 12, 13)?;
    let identifying_source = phase(1, -2, 1)?;
    let identifying_return = observe(&mut world, identifying_source, hidden_condition)?;
    let identifying_x = mount(&surface, &identifying_source.words())?;
    let identifying_y = mount(
        &surface,
        &NativePhaseCurrent::from_current(&identifying_return)?.words(),
    )?;
    let before = learner.census();
    let preimage =
        learner.read_condition_preimage(rational(&identifying_x)?, rational(&identifying_y)?)?;
    let preimage_work = delta(before, learner.census());
    let later_source = phase(4, 1, 1)?;
    let later_x = mount(&surface, &later_source.words())?;
    let before = learner.census();
    let inferred_prediction =
        learner.advance_bilinear_contact(rational(&later_x)?, preimage.current(), None)?;
    let inferred_work = delta(before, learner.census());
    let later_actual = observe(&mut world, later_source, hidden_condition)?;
    let inferred_prediction = returned(&inferred_prediction)?;
    let condition_reading = match preimage.inspect()? {
        ConditionPreimageReading::Compatible {
            particular,
            directions,
        } => json!({"kind":"compatible",
            "particular":particular.iter().map(ToString::to_string).collect::<Vec<_>>(),
            "directions":directions.iter().map(|row|row.iter().map(ToString::to_string).collect::<Vec<_>>()).collect::<Vec<_>>()}),
        other => return Err(format!("condition preimage remains {other:?}").into()),
    };
    let (constraint, rhs) = preimage.inspect_constraints()?;
    let condition_inference = json!({"source":identifying_source,"actual_return":face(&identifying_return),
        "hidden_condition_for_observer_only":hidden_condition,"preimage":condition_reading,
        "relation_cut":preimage.relation_cut(),"work":preimage_work,
        "constraint_graph":{"rows":constraint.rows,"width":constraint.width,"intervals":constraint.intervals},
        "constraint_rhs":{"width":rhs.width,"intervals":rhs.intervals},
        "later_source":later_source,"later_prediction":face(&inferred_prediction),
        "later_actual":face(&later_actual),"later_equal":inferred_prediction==later_actual,"later_work":inferred_work});
    let one = mount(&surface, &[1, 0, 1])?;
    // Begin with a whole free condition family. Its image can conduct a fixed output even
    // before a condition is known; a later actual observation refines the same joint family.
    let zero = mount(&surface, &[0, 0, 1])?;
    let family = learner.read_condition_preimage(rational(&zero)?, rational(&zero)?)?;
    let silent = learner.read_condition_image(rational(&zero)?, &family)?;
    let before = learner.census();
    let silent_carried =
        learner.advance_bilinear_contact(silent.current(), rational(&one)?, None)?;
    let silent_work = delta(before, learner.census());
    let cycle_source = phase(2, 1, 1)?;
    let cycle_x = mount(&surface, &cycle_source.words())?;
    let before = learner.census();
    let expectation = learner.read_condition_image(rational(&cycle_x)?, &family)?;
    let image_work = delta(before, learner.census());
    // Actual model standing is generated by the learned action. Free evidence does not prevent
    // it from conducting a nonzero current before the world's unknown condition is observed.
    let before = learner.census();
    let initial = learner.advance_bilinear_contact(rational(&one)?, rational(&cs)?, None)?;
    let mut held = learner.retain_condition_current(
        initial.current(),
        ConditionContactMetric::UnitAdmittanceRealification,
    )?;
    let free_contact = held.contact(&family)?;
    let anticipated =
        learner.advance_bilinear_contact(rational(&cycle_x)?, held.current(), None)?;
    let generative_work = delta(before, learner.census());
    let cycle_hidden = phase(-7, 24, 25)?;
    let cycle_observed = observe(&mut world, cycle_source, cycle_hidden)?;
    let cycle_y = mount(
        &surface,
        &NativePhaseCurrent::from_current(&cycle_observed)?.words(),
    )?;
    let before = learner.census();
    let refined = expectation.receive(rational(&cycle_y)?)?;
    let refinement_work = delta(before, learner.census());
    let before = learner.census();
    let actual_contact = held.contact(&refined)?;
    let contact_work = delta(before, learner.census());
    let future_source = phase(3, -2, 1)?;
    let future_x = mount(&surface, &future_source.words())?;
    let before = learner.census();
    let future = learner.read_condition_image(rational(&future_x)?, &refined)?;
    let carried = learner.advance_bilinear_contact(future.current(), rational(&one)?, None)?;
    let generated_future =
        learner.advance_bilinear_contact(rational(&future_x)?, held.current(), None)?;
    let future_work = delta(before, learner.census());
    let future_actual = observe(&mut world, future_source, cycle_hidden)?;
    let future_predicted = returned(&carried)?;
    let cycle_equal = future_actual == future_predicted;
    let generated_prediction = returned(&generated_future)?;
    let generated_equal = generated_prediction == future_actual;
    // Generated current now reaches the ordinary paired field recurrence, including its internal
    // contact and successor, without decoding/remounting it as an exterior vector.
    let mut recipient = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        vec![NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        }],
        ResidentGrain(72),
    )?;
    let before = recipient.census();
    let first_received = recipient.advance_current_resident(
        &mut NativeFieldOccurrence::entering(vec![]),
        anticipated.current(),
    )?;
    let second_received = recipient.advance_current_resident(
        &mut NativeFieldOccurrence::through(first_received.source, vec![]),
        generated_future.current(),
    )?;
    let third_received = recipient.advance_current_resident(
        &mut NativeFieldOccurrence::through(second_received.source, vec![]),
        held.current(),
    )?;
    let field_work = delta(before, recipient.census());
    let resident_field_cycle = json!({"work":field_work,"final_lineage":third_received.lineage,
        "actual_inputs":(0..3).map(|at|recipient.inspect_incoming(at)).collect::<Result<Vec<_>,_>>()?,
        "first_junction":recipient.inspect_exact_junction(0)?,"last_junction":recipient.inspect_exact_junction(2)?,
        "internal_currents":recipient.inspect_internal_currents()?,"occurrences":recipient.occurrence_count()});
    let actual_current_cycle = json!({"initial_native_current":face(&returned(&initial)?),
        "free_contact":free_contact.inspect()?,"generation_before_observation":face(&returned(&anticipated)?),
        "generative_work":generative_work,"contact_after_observation":actual_contact.inspect()?,
        "contact_work":contact_work,"future_generation":face(&generated_prediction),
        "future_actual":face(&future_actual),"future_equal":generated_equal,
        "contacts":held.contacts(),"condition_family_is_not_actual_cause":true});
    let family_cycle = json!({"initial_condition":family.inspect()?,"silent_image":silent.inspect()?,
        "silent_carried":face(&returned(&silent_carried)?),"silent_work":silent_work,
        "source":cycle_source,"joint_before_return":expectation.inspect()?,"image_work":image_work,
        "actual_return":face(&cycle_observed),"hidden_condition_for_observer_only":cycle_hidden,
        "refined_condition":refined.inspect()?,"refinement_work":refinement_work,
        "future_source":future_source,"future_image":future.inspect()?,
        "future_prediction":face(&future_predicted),"future_actual":face(&future_actual),
        "future_equal":cycle_equal,"future_work":future_work});
    let before = learner.census();
    let first = learner.advance_bilinear_contact(rational(&one)?, rational(&cs)?, None)?;
    let second = learner.advance_bilinear_contact(first.current(), rational(&cs)?, None)?;
    let third = learner.advance_bilinear_contact(second.current(), rational(&cs)?, None)?;
    let continuation_work = delta(before, learner.census());
    let continuation = [returned(&first)?, returned(&second)?, returned(&third)?];
    let agreement = predicted == actual
        && inferred_prediction == later_actual
        && cycle_equal
        && generated_equal;
    let relation = learner.inspect_relation()?;
    // Cold receiver of the inferred operator, after every productive operation: the six source
    // pivots span the declared chart, and each row maps its mixed complex pair to the target.
    let multiplication_graph_exact = relation.rows == 8
        && relation.width == 8
        && relation.intervals.iter().all(|(lo, hi)| lo == hi)
        && (0..6).all(|p| relation.intervals[8 * p + p].0 > 0)
        && relation
            .intervals
            .chunks_exact(8)
            .all(|row| row[6].0 == row[4].0 && row[7].0 == row[5].0);
    let relation = json!({"rows":relation.rows,"width":relation.width,"grain":relation.grain.0,
        "bound_octaves":relation.bound_octaves,"intervals":relation.intervals});
    let report = json!({"schema":"holonics.native-conditional-phase.v1",
        "truth_status":"established-bounded","evidence_tags":["measured"],
        "source_chart":learner.source_chart(),"receiver":"one complex held phase current",
        "multiplication_graph_exact":multiplication_graph_exact,
        "condition_inference":condition_inference,
        "condition_family_cycle":family_cycle,
        "actual_condition_current_cycle":actual_current_cycle,
        "resident_field_cycle":resident_field_cycle,
        "observations":observations,"withheld":{"source":x,"condition":c,
            "prediction":face(&predicted),"actual_native_return":face(&actual),"equal":agreement,"work":prediction_work},
        "continuation":continuation.iter().map(face).collect::<Vec<_>>(),"continuation_work":continuation_work,
        "learner_occurrences":learner.occurrences(),"relation":relation,
        "development_and_observation_seconds":development_seconds,"whole_seconds":start.elapsed().as_secs_f64(),
        "apparatus_census_including_world_and_diagnostics":surface.census(),
        "model_persisted":false,"conversation_quality_established":false,"acoustic_model_established":false});
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options.open(&path)?;
    serde_json::to_writer_pretty(&mut file, &report)?;
    file.write_all(b"\n")?;
    file.sync_all()?;
    println!(
        "{}",
        json!({"report":path,"withheld_equal":agreement,"learner_occurrences":learner.occurrences()})
    );
    if !agreement || !multiplication_graph_exact {
        return Err(
            "native conditional prediction disagrees with the withheld field return".into(),
        );
    }
    Ok(())
}
