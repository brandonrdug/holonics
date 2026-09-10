//! Public construction probe for a shared condition field and its local learned generators.
//! `learn NEW` saves after the first received occurrence; `resume SAVED NEW` continues with
//! the second; `full NEW` performs both uninterrupted. No source archive enters the saved body.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, ConstitutiveReading, GeneratorNeighborhoodRest,
        NativeConstitutiveField, NativeFieldOccurrence, NativeJunctionSeed, NativePhaseCurrent,
        ResidentConstitutiveCurrent, ResidentConstitutiveFibre, ResidentGeneratorNeighborhood,
    },
    resident_section::{ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface},
};
use std::{error::Error, fs::File, io::BufReader, path::Path};
type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn point<'c>(s: &'c ResidentSurface<'c>, words: &[i64]) -> Result<ResidentSection<'c>> {
    Ok(s.mount_section_rest(&ResidentSectionRest::found(
        1,
        words.len(),
        ResidentGrain(0),
        i64::BITS,
        words.iter().map(|v| (*v, *v)).collect(),
    )?)?)
}
fn current<'a, 'c>(s: &'a ResidentSection<'c>) -> Result<ResidentConstitutiveCurrent<'a, 'c>> {
    Ok(ResidentConstitutiveCurrent::integers(s)?)
}
fn apparatus<'c>(s: &'c ResidentSurface<'c>) -> Result<NativeConstitutiveField<'c>> {
    Ok(NativeConstitutiveField::found(
        s,
        vec![NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        }],
    )?)
}
fn observe(
    source: &mut NativeConstitutiveField<'_>,
    excitation: NativePhaseCurrent,
    transport: NativePhaseCurrent,
) -> Result<[i64; 3]> {
    source.replace_incoming_transport(0, transport)?;
    let result = source.advance_status(&mut NativeFieldOccurrence::entering(vec![excitation]))?;
    Ok(NativePhaseCurrent::from_current(&result.held_successor[0])?.words())
}
fn learn<'c>(s: &'c ResidentSurface<'c>) -> Result<ResidentGeneratorNeighborhood<'c>> {
    // Declared apparatus: one complex source, two shared complex condition components,
    // one complex output per local law. Unit phases span the admitted bilinear source chart.
    const UNIT: [i64; 2] = [1, 0];
    const QUARTER: [i64; 2] = [0, 1];
    const HALF: [i64; 2] = [-1, 0];
    let controls = [
        ([0, 0], UNIT, UNIT),
        ([0, 0], HALF, UNIT),
        ([0, 0], QUARTER, UNIT),
        ([0, 0], UNIT, QUARTER),
        (UNIT, UNIT, UNIT),
        (UNIT, HALF, UNIT),
        (UNIT, QUARTER, UNIT),
        (UNIT, UNIT, QUARTER),
        (UNIT, HALF, HALF),
        (QUARTER, UNIT, UNIT),
    ];
    let mut sources = [apparatus(s)?, apparatus(s)?];
    let mut laws = (0..sources.len())
        .map(|_| ResidentConstitutiveFibre::found_bilinear_contact(s, 1, sources.len(), 1))
        .collect::<std::result::Result<Vec<_>, _>>()?;
    for (x, a, b) in controls {
        let xs = point(s, &x)?;
        let cs = point(s, &[a[0], a[1], b[0], b[1]])?;
        for (member, c) in [a, b].into_iter().enumerate() {
            let measured = observe(
                &mut sources[member],
                NativePhaseCurrent::new(x[0], x[1], 1)?,
                NativePhaseCurrent::new(c[0], c[1], 1)?,
            )?;
            let ys = point(s, &measured)?;
            laws[member].advance_bilinear_contact(
                current(&xs)?,
                current(&cs)?,
                Some(ResidentConstitutiveCurrent::rational(&ys)?),
            )?;
        }
    }
    // The two apparatus bodies are exterior. Only the learned local relations move into HNN.
    let initial = point(s, &[0, 4, 3, 0, 5])?;
    Ok(ResidentGeneratorNeighborhood::with_shared_condition(
        laws,
        ResidentConstitutiveCurrent::rational(&initial)?,
        ConditionContactMetric::UnitAdmittanceRealification,
    )?)
}
fn receive<'c>(
    s: &'c ResidentSurface<'c>,
    body: &mut ResidentGeneratorNeighborhood<'c>,
    member: usize,
) -> Result<serde_json::Value> {
    // The two test transports are rational unit phases from the 3-4-5 triangle and a
    // quarter-turn thereof. They specify exterior interventions, never learner coefficients.
    let transport = match member {
        0 => NativePhaseCurrent::new(3, 4, 5)?,
        1 => NativePhaseCurrent::new(-4, 3, 5)?,
        _ => return Err("this apparatus has two measured branches".into()),
    };
    let mut source = apparatus(s)?;
    let measured = observe(&mut source, NativePhaseCurrent::unit(), transport)?;
    drop(source);
    let excitation = point(s, &[1, 0])?;
    let observed = point(s, &measured)?;
    let before = s.census();
    let step = body.advance(
        member,
        current(&excitation)?,
        Some(ResidentConstitutiveCurrent::rational(&observed)?),
    )?;
    let after = s.census();
    let contact = step.contact.as_ref().ok_or("missing contact")?.inspect()?;
    Ok(serde_json::json!({
        "member":member, "predecessor_epoch":step.predecessor_epoch,
        "successor_epoch":step.successor_epoch,
        "condition_before":contact.predecessor.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "condition_after":contact.successor.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "section_readouts_during_return":after.section_read_outs-before.section_read_outs,
        "ingress_octets_during_return":after.ingress_octets-before.ingress_octets,
    }))
}
fn main() -> Result<()> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let (mode, input, output) = match args.as_slice() {
        [mode, output] if mode == "learn" || mode == "full" => {
            (mode.as_str(), None, output.as_str())
        }
        [mode, input, output] if mode == "resume" => {
            (mode.as_str(), Some(input.as_str()), output.as_str())
        }
        _ => {
            return Err("usage: native_neighborhood learn NEW | full NEW | resume SAVED NEW".into())
        }
    };
    if Path::new(output).exists() {
        return Err("output already exists".into());
    }
    let readout = ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    let mut body = if let Some(input) = input {
        let file = File::open(input)?;
        let bytes = file.metadata()?.len();
        GeneratorNeighborhoodRest::read(&mut BufReader::new(file), bytes)?.remount(&surface)?
    } else {
        learn(&surface)?
    };
    let mut returns = Vec::new();
    if mode != "resume" {
        returns.push(receive(&surface, &mut body, 0)?);
    }
    if mode != "learn" {
        returns.push(receive(&surface, &mut body, 1)?);
    }
    let probe = point(&surface, &[2, 3])?;
    let outputs = (0..body.members())
        .map(|member| -> Result<_> {
            Ok(
                match body
                    .read(member, current(&probe)?)?
                    .inspect()?
                    .predecessor_reading
                {
                    ConstitutiveReading::Unique { current } => {
                        current.iter().map(ToString::to_string).collect::<Vec<_>>()
                    }
                    _ => {
                        return Err(
                            "probe did not return a unique current in its calibrated domain".into(),
                        )
                    }
                },
            )
        })
        .collect::<Result<Vec<_>>>()?;
    let rest = body.rest()?;
    holonics_hna::publish_new(output, |file| {
        rest.write(file).map_err(std::io::Error::other)
    })?;
    println!(
        "{}",
        serde_json::json!({
            "scope":"two learned local relations sharing one declared condition field",
            "mode":mode,"epoch":body.epoch(),"members":body.members(),
            "source_archive_in_model":false,"latest_received_fibre_count":usize::from(rest.last_received_evidence().is_some()),
            "ranks":rest.laws().iter().map(|law|law.rank()).collect::<Vec<_>>(),
            "law_observations":rest.laws().iter().map(|law|law.occurrences()).collect::<Vec<_>>(),
            "condition_words":rest.condition().current_words(),
            "rest_octets":std::fs::metadata(output)?.len(),"probe_source":[2,3],"probe_outputs":outputs,
            "returns":returns,
        })
    );
    Ok(())
}
