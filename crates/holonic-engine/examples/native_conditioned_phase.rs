//! A measured conditional phase action using the public native field and local relation.
//! The driver controls source/condition ports and observes returns; all learning is in the
//! standing engine owner. The reported local family is not a text/audio model artifact.

use holonic_engine::{
    dimensional_wave::ExactComplexWaveCurrent,
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConstitutiveFibreError, ConstitutiveReading, NativeConstitutiveField,
        NativeFieldOccurrence, NativeJunctionSeed, NativePhaseCurrent, ResidentConstitutiveCurrent,
        ResidentConstitutiveFibre, ResidentConstitutiveReturn,
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
    let one = mount(&surface, &[1, 0, 1])?;
    let before = learner.census();
    let first = learner.advance_bilinear_contact(rational(&one)?, rational(&cs)?, None)?;
    let second = learner.advance_bilinear_contact(first.current(), rational(&cs)?, None)?;
    let third = learner.advance_bilinear_contact(second.current(), rational(&cs)?, None)?;
    let continuation_work = delta(before, learner.census());
    let continuation = [returned(&first)?, returned(&second)?, returned(&third)?];
    let agreement = predicted == actual;
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
