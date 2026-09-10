//! Bounded phase-generator construction through public native owners, without a text codec.
//! `learn NEW.law` measures an existing native source apparatus; `resume FILE.law` needs only
//! the compact learned law. Neither mode contains a local learner or stored observation list.
use holonic_engine::{
    embedding_fiber::{AlignedMaterial, ResidentReadout},
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, ConstitutiveFibreRest, ConstitutiveReading,
        NativeConstitutiveField, NativeFieldOccurrence, NativeJunctionSeed, NativePhaseCurrent,
        ResidentConstitutiveCurrent, ResidentConstitutiveFibre,
    },
    resident_section::{ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface},
};
use std::{
    error::Error,
    fs::{File, OpenOptions},
    io::BufReader,
    path::Path,
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;
fn point<'c>(s: &'c ResidentSurface<'c>, values: &[i64]) -> Result<ResidentSection<'c>> {
    Ok(s.mount_section_rest(&ResidentSectionRest::found(
        1,
        values.len(),
        ResidentGrain(0),
        64,
        values.iter().map(|v| (*v, *v)).collect(),
    )?)?)
}
fn current<'a, 'c>(s: &'a ResidentSection<'c>) -> Result<ResidentConstitutiveCurrent<'a, 'c>> {
    Ok(ResidentConstitutiveCurrent::integers(s)?)
}
fn learn<'c>(s: &'c ResidentSurface<'c>) -> Result<ResidentConstitutiveFibre<'c>> {
    // Declared local hypothesis: one complex source and one complex condition, including their
    // mixed contact. These are source-interface dimensions, not capacities derived from a codec.
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(s, 1, 1, 1)?;
    let mut source = NativeConstitutiveField::found(
        s,
        vec![NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        }],
    )?;
    for (x, c) in [
        ([0, 0], [1, 0]),
        ([0, 0], [0, 1]),
        ([1, 0], [1, 0]),
        ([0, 1], [1, 0]),
        ([1, 0], [-1, 0]),
        ([0, 1], [-1, 0]),
    ] {
        source.replace_incoming_transport(0, NativePhaseCurrent::new(c[0], c[1], 1)?)?;
        let measurement = source.advance_status(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::new(x[0], x[1], 1)?,
        ]))?;
        // This exterior source observation is measured through the existing field law. Its
        // generating coefficients are never supplied to the learner as a target operator.
        let measured = NativePhaseCurrent::from_current(&measurement.held_successor[0])?.words();
        let xs = point(s, &x)?;
        let cs = point(s, &c)?;
        let ys = point(s, &measured)?;
        law.advance_bilinear_contact(
            current(&xs)?,
            current(&cs)?,
            Some(ResidentConstitutiveCurrent::rational(&ys)?),
        )?;
    }
    // The source apparatus and its finite diagnostic history leave scope here.
    Ok(law)
}
fn family(reading: &ConstitutiveReading) -> serde_json::Value {
    let values =
        |v: &[num_rational::BigRational]| v.iter().map(ToString::to_string).collect::<Vec<_>>();
    match reading {
        ConstitutiveReading::Unique { current } => {
            serde_json::json!({"kind":"unique","current":values(current)})
        }
        ConstitutiveReading::Plural {
            particular,
            directions,
        } => serde_json::json!({"kind":"plural","particular":values(particular),
            "directions":directions.iter().map(|d|values(d)).collect::<Vec<_>>()}),
        ConstitutiveReading::OutsideDomain { source_remainder } => {
            serde_json::json!({"kind":"outside-domain","source_remainder":values(source_remainder)})
        }
    }
}

fn compose<'c>(
    readout: &'c ResidentReadout,
    s: &'c ResidentSurface<'c>,
    law: &ResidentConstitutiveFibre<'c>,
) -> Result<()> {
    // A declared real-component receiver is calibrated through actual native contractions.
    // This is a sensor chart, not a manually installed learned phase operator.
    let detector = readout.mount(
        &AlignedMaterial {
            entries: vec![1, 0],
            exponent: 0,
            entry_octaves: 1,
            negatives: 0,
        },
        2,
    )?;
    let mut receiver = ResidentConstitutiveFibre::found(s, 2, 1)?;
    for v in [[1, 0], [0, 1]] {
        let input = point(s, &v)?;
        let output = s.fresh_section(1, 1, ResidentGrain(0))?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_contract(&lane, &input, &detector, &output)?;
        }
        passage.close(0, &output, 64)?;
        if !passage.finish()?.launch()?.obstruction.is_empty() {
            return Err("component receiver refused".into());
        }
        receiver.advance_resident(current(&input)?, Some(current(&output)?))?;
    }
    drop(detector);
    let zero = point(s, &[0, 0])?;
    let observed_component = point(s, &[1])?; // This experiment's supplied exterior observation.
    let p = point(s, &[3, 4, 5])?;
    let inverse = point(s, &[3, -4, 5])?;
    let left = law.contextual_section(ResidentConstitutiveCurrent::rational(&p)?)?;
    let right = law.contextual_section(ResidentConstitutiveCurrent::rational(&inverse)?)?;
    let initial_condition = point(s, &[0, 4, 5])?;
    let actual_input = point(s, &[2, 3])?;
    let mut standing = law.retain_condition_current(
        ResidentConstitutiveCurrent::rational(&initial_condition)?,
        ConditionContactMetric::UnitAdmittanceRealification,
    )?;
    let output_generator = law.contextual_section(current(&actual_input)?)?;
    let before = law.rest()?;
    let hot = s.census();
    let prior_output = output_generator.read_change(standing.current())?;
    // Zero source and zero return leave the condition unresolved in this learned local law.
    let unknown = law.read_condition_preimage(current(&zero)?, current(&zero)?)?;
    let measured = receiver.read_image(unknown.family())?;
    let restriction = measured.receive(current(&observed_component)?)?;
    let restricted = unknown.refined_by(restriction)?;
    let phase_image = left.read_change_image(restricted.family())?;
    let roundtrip = right.read_change_image(phase_image.output())?;
    let contact = standing.contact(&restricted)?;
    let subsequent_output = output_generator.read_change(standing.current())?;
    let after = s.census();
    let source = restricted.family().inspect()?.predecessor_reading;
    let contact_reading = contact.inspect()?;
    let rotated = phase_image.inspect()?;
    let returned = roundtrip.inspect()?;
    if returned.output != source || law.rest()?.relation() != before.relation() {
        return Err("composed family or learned material changed unexpectedly".into());
    }
    println!(
        "{}",
        serde_json::json!({"scope":"native joint-family composition and received source refinement; not a language model",
        "mode":"compose","external_received_real_component":"1","source_family":family(&source),
        "rotated_family":family(&rotated.output),"returned_family":family(&returned.output),
        "joint_rotated_family":family(&rotated.joint),"first_coverage":rotated.coverage,"second_coverage":returned.coverage,
        "law_unchanged":true,
        "actual_condition_before":contact_reading.predecessor.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "actual_condition_after":contact_reading.successor.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "prior_output":family(&prior_output.inspect()?.predecessor_reading),
        "subsequent_output":family(&subsequent_output.inspect()?.predecessor_reading),
        "condition_contacts":standing.contacts(),
        "numerical_section_readouts_during_composition":after.section_read_outs-hot.section_read_outs,
        "native_ingress_octets_during_composition":after.ingress_octets-hot.ingress_octets})
    );
    Ok(())
}

fn main() -> Result<()> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() != 2 || !matches!(args[0].as_str(), "learn" | "resume" | "compose") {
        return Err(
            "usage: native_generator learn NEW.law | resume SAVED.law | compose SAVED.law".into(),
        );
    }
    let readout = ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    let mut law = if args[0] == "learn" {
        let law = learn(&surface)?;
        let rest = law.rest()?;
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options.mode(0o600);
        }
        rest.write(&mut options.open(Path::new(&args[1]))?)?;
        law
    } else {
        let file = File::open(&args[1])?;
        let n = file.metadata()?.len();
        ConstitutiveFibreRest::read(&mut BufReader::new(file), n)?.remount(&surface)?
    };
    if args[0] == "compose" {
        return compose(&readout, &surface, &law);
    }
    let before = law.rest()?;
    let input = point(&surface, &[2, 3])?;
    let condition = point(&surface, &[3, 4, 5])?;
    let quarter = point(&surface, &[0, 1])?;
    let before_operation = law.census();
    let mut output = law.advance_bilinear_contact(
        current(&input)?,
        ResidentConstitutiveCurrent::rational(&condition)?,
        None,
    )?;
    let resident = law.census().resident_octets_now;
    // This run's declared work extent. The generator remains the learned relation at every step.
    let turns = 64usize;
    for _ in 0..turns * 4 {
        output = law.advance_bilinear_contact(output.current(), current(&quarter)?, None)?;
        if law.census().resident_octets_now != resident {
            return Err("generator retained additional resident material".into());
        }
    }
    let after_operation = law.census();
    let reading = output.inspect()?;
    let after = law.rest()?;
    if before.relation() != after.relation() {
        return Err("source-only continuation changed the learned law".into());
    }
    let ConstitutiveReading::Unique { current } = reading.predecessor_reading else {
        return Err("declared continuation left the supported point chart".into());
    };
    println!(
        "{}",
        serde_json::json!({"scope":"measured local bilinear phase generator; not a language model",
        "mode":args[0],"source_chart":before.source_chart(),"learned_rank":before.rank(),
        "basis_words":before.relation().intervals.len(),"law_file_octets":std::fs::metadata(&args[1])?.len(),
        "law_unchanged":true,"composed_operations":1+turns*4,"current":current.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "resident_octets_during_continuation":resident,
        "numerical_section_readouts_during_continuation":after_operation.section_read_outs-before_operation.section_read_outs,
        "native_ingress_octets_during_continuation":after_operation.ingress_octets-before_operation.ingress_octets,
        "retained_observation_population":0})
    );
    Ok(())
}
