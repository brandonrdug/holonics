//! Bounded phase-generator construction through public native owners, without a text codec.
//! `learn NEW.law` measures an existing native source apparatus; `resume FILE.law` needs only
//! the compact learned law. Neither mode contains a local learner or stored observation list.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConstitutiveFibreRest, ConstitutiveReading, NativeConstitutiveField, NativeFieldOccurrence,
        NativeJunctionSeed, NativePhaseCurrent, ResidentConstitutiveCurrent,
        ResidentConstitutiveFibre,
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
fn main() -> Result<()> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() != 2 || !matches!(args[0].as_str(), "learn" | "resume") {
        return Err("usage: native_generator learn NEW.law | resume SAVED.law".into());
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
