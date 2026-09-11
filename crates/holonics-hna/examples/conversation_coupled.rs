//! Prepared conversation source meets the public coupled owner. This driver supplies source
//! charts and reads results; local formation, conditional transport and rest stay native.
use holonic_engine::{
    codec_recovery::SymbolAlphabet,
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, NormalWaveRest, ResidentConstitutiveCurrent,
        ResidentConstitutiveFibre, ResidentConstitutiveSection, ResidentGeneratorNeighborhood,
        WaveSourceReceiver,
    },
    resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface},
};
use holonics_hna::{
    alpha::exposure::{ExposureCursor, ExposurePartition, ExposureReader},
    native::section_input::SymbolCurrentChart,
    publish_new,
};
use std::{
    error::Error,
    fs::{self, File},
    io,
    path::Path,
    time::Instant,
};
type Result<T> = std::result::Result<T, Box<dyn Error>>;
fn json(path: impl AsRef<Path>, value: &impl serde::Serialize) -> Result<()> {
    publish_new(path, |f| {
        serde_json::to_writer(f, value).map_err(io::Error::other)
    })?;
    Ok(())
}
fn inspect(model: &str, output: &str) -> Result<()> {
    use num_traits::One;
    let model = Path::new(model);
    let output = Path::new(output);
    fs::create_dir(output)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(output, fs::Permissions::from_mode(0o700))?;
    }
    let mut f = File::open(model.join("model.wave"))?;
    let size = f.metadata()?.len();
    eprintln!("validating complete coupled source");
    let rest = NormalWaveRest::read(&mut f, size)?;
    let ro = ResidentReadout::new()?;
    let s = ResidentSurface::on(&ro)?;
    let wave = rest.remount_coupled(&s, |n| eprintln!("source word {n}"))?;
    let anchor = wave.current().anchor().inspect()?;
    let n = anchor.center.len() / 2;
    let zero = &anchor.radius - &anchor.radius;
    let mut one = zero.clone();
    one.set_one();
    let count = (0..n).fold(zero.clone(), |a, _| a + &one);
    let p = anchor.center[..n]
        .iter()
        .fold(zero.clone(), |a, v| a + &v.real);
    let c = anchor.center[n..]
        .iter()
        .fold(zero.clone(), |a, v| a + &v.real);
    let radius_square = &anchor.radius * &anchor.radius;
    json(
        output.join("source.json"),
        &serde_json::json!({"epoch":wave.epoch(),"anchor":anchor,
        "previous_real_sum":p.to_string(),"current_real_sum":c.to_string(),"radius_squared":radius_square.to_string(),
        "unit_previous_real_sum_excluded":(&p-&one)*(&p-&one)>&count*&radius_square,
        "unit_current_real_sum_excluded":(&c-&one)*(&c-&one)>&count*&radius_square}),
    )?;
    for id in wave.contact_ids() {
        eprintln!("reading candidate for admitted contact {id}");
        let h = wave.contact(id)?;
        let candidate = wave.read_contact(&h)?;
        publish_new(output.join(format!("candidate-{id}.family")), |f| {
            candidate
                .rest()
                .and_then(|r| r.write(f))
                .map_err(io::Error::other)
        })?;
        json(
            output.join(format!("candidate-{id}.affine.json")),
            &candidate.affine_relation().inspect()?,
        )?;
        let view = match candidate.read_receiver().and_then(|r| r.inspect()) {
            Ok(view) => view,
            Err(error) => {
                json(
                    output.join(format!("candidate-{id}.json")),
                    &serde_json::json!({
                    "contact":id,"member":h.member(),"receiver_error":error.to_string()}),
                )?;
                continue;
            }
        };
        let distance = view
            .anchor_difference
            .as_ref()
            .map(|v| v.iter().fold(zero.clone(), |a, x| a + x * x));
        let sums = view.nearest_anchor.as_ref().map(|v| {
            [
                (0..2 * n).step_by(2).fold(zero.clone(), |a, i| a + &v[i]),
                (2 * n..4 * n)
                    .step_by(2)
                    .fold(zero.clone(), |a, i| a + &v[i]),
            ]
        });
        json(
            output.join(format!("candidate-{id}.json")),
            &serde_json::json!({"contact":id,"member":h.member(),"receiver":view,
            "distance_squared":distance.as_ref().map(ToString::to_string),"nearest_real_sums":sums.map(|v|v.map(|x|x.to_string()))}),
        )?;
    }
    Ok(())
}
fn main() -> Result<()> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if let [mode, model, output] = args.as_slice() {
        if mode == "inspect" {
            return inspect(model, output);
        }
    }
    let (receiver, operands) = if args.first().is_some_and(|v| v == "unit-real-sum") {
        (WaveSourceReceiver::UnitRealSum, &args[1..])
    } else {
        (WaveSourceReceiver::Direct, args.as_slice())
    };
    let [model, take, steps, output] = operands else {
        return Err(
            "usage: conversation_coupled [unit-real-sum] MODEL_DIRECTORY TAKE_FRAMES GENERATE_STEPS NEW_DIRECTORY"
                .into(),
        );
    };
    let take = take.parse::<u64>()?;
    let steps = steps.parse::<u64>()?;
    if take == 0 {
        return Err("declare a nonempty source aperture".into());
    }
    let model = Path::new(model);
    let output = Path::new(output);
    fs::create_dir(output)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(output, fs::Permissions::from_mode(0o700))?;
    }
    let chart = SymbolCurrentChart::declared(serde_json::from_reader::<_, SymbolAlphabet>(
        File::open(model.join("exterior-chart.json"))?,
    )?);
    let cursor: ExposureCursor =
        serde_json::from_reader(File::open(model.join("source-cursor.json"))?)?;
    let mut reader = ExposureReader::resume(cursor)?;
    eprintln!("validating source model");
    let mut file = File::open(model.join("model.wave"))?;
    let size = file.metadata()?.len();
    let rest = NormalWaveRest::read(&mut file, size)?;
    if rest.is_coupled() || rest.material().roots() != chart.alphabet().len() {
        return Err("expected normal model in the supplied source chart".into());
    }
    let ro = ResidentReadout::new()?;
    let s = ResidentSurface::on(&ro)?;
    eprintln!(
        "mounting normal bank: {} complex coordinates",
        chart.alphabet().len()
    );
    let bank = rest.remount(&s, |step| eprintln!("source word {step}"))?;
    let n = chart.alphabet().len();
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(&s, 3 * n, 1, n)?;
    // One declared complex condition chart for this source assay, initialized at its unit.
    // This is not a semantic capacity, source ordinal amplitude or expected-answer route.
    let h = s.mount_section_rest(&ResidentSectionRest::found(
        1,
        2,
        ResidentGrain(0),
        64,
        vec![(1, 1), (0, 0)],
    )?)?;
    let condition = ResidentConstitutiveCurrent::integers(&h)?;
    let mut fields = Vec::new();
    let mut stage = "calibration";
    let mut position = serde_json::json!(null);
    let started = Instant::now();
    let mut frames = 0;
    let mut observations = 0;
    let calibration: Result<()> = (|| {
        while frames < take {
            let Some(frame) = reader.peek()? else { break };
            if frame.partition == ExposurePartition::Development {
                for part in frame.development_parts()? {
                    let Some(text) = &part.text else { continue };
                    let symbols = chart.decode_text(text)?;
                    if symbols.len() < 3 {
                        continue;
                    }
                    let source = chart.mount(&s, &symbols)?;
                    let differences =
                        ResidentConstitutiveSection::integers(&source)?.differences(&s)?;
                    let before = s.census();
                    let clock = Instant::now();
                    for row in 0..differences.source().rows() {
                        position = serde_json::json!({"sequence":frame.sequence,"part":part.ordinal,"row":row,"source_scalars":symbols.len()});
                        law.advance_bilinear_contact(
                            differences.source().row(row)?,
                            condition,
                            Some(differences.observed().row(row)?),
                        )?;
                        observations += 1;
                    }
                    let after = s.census();
                    fields.push(serde_json::json!({"sequence":frame.sequence,"part":part.ordinal,"scalars":symbols.len(),"octets":text.len(),
                        "observations":differences.source().rows(),"milliseconds":clock.elapsed().as_millis(),
                        "numerical_readouts":after.section_read_outs-before.section_read_outs,"ingress_octets":after.ingress_octets-before.ingress_octets}));
                    eprintln!(
                        "source {} part {}: {} observed passages",
                        frame.sequence,
                        part.ordinal,
                        differences.source().rows()
                    );
                }
            }
            let sequence = frame.sequence;
            reader.acknowledge(sequence)?;
            frames += 1;
        }
        Ok(())
    })();
    json(
        output.join("source-return.json"),
        &serde_json::json!({"stage":stage,"source_receiver":receiver,"position":position,"frames":frames,"observations":observations,"fields":fields,"milliseconds":started.elapsed().as_millis(),"device":{"name":s.declaration().name,"max_shared_bytes":s.declaration().max_sectiond_bytes,"multiprocessors":s.declaration().multiprocessors}}),
    )?;
    let saved_law = publish_new(output.join("local-law.fibre"), |f| {
        law.rest()
            .and_then(|v| v.write(f))
            .map_err(io::Error::other)
    });
    if let Err(error) = calibration {
        json(
            output.join("failure.json"),
            &serde_json::json!({"stage":stage,"error":error.to_string(),"position":position,"checkpoint_error":saved_law.err().map(|e|e.to_string())}),
        )?;
        return Err(error);
    }
    saved_law?;
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law],
        condition,
        ConditionContactMetric::UnitAdmittanceRealification,
    )?;
    stage = "attach";
    eprintln!("attaching observed local material");
    let mut wave = bank.with_neighborhood(neighborhood).map_err(|r| r.reason)?;
    let mut returned = Vec::new();
    let operation: Result<()> = (|| {
        for _ in 0..steps {
            stage = "contact admission";
            eprintln!("admitting at epoch {}", wave.epoch());
            let h = wave.admit_contact_in_chart(0, receiver)?;
            stage = "conditional passage";
            eprintln!("continuing at epoch {}", wave.epoch());
            let before = s.census();
            let clock = Instant::now();
            let step = wave.advance_contact(&h)?;
            let after = s.census();
            stage = "receiver";
            let view = step.successor().read_receiver()?.inspect()?;
            returned.push(serde_json::json!({"epoch":wave.epoch(),"milliseconds":clock.elapsed().as_millis(),"receiver":view,
                "numerical_readouts":after.section_read_outs-before.section_read_outs,"ingress_octets":after.ingress_octets-before.ingress_octets}));
        }
        Ok(())
    })();
    eprintln!("saving complete coupled rest at epoch {}", wave.epoch());
    publish_new(output.join("model.wave"), |f| {
        wave.rest()
            .and_then(|r| r.write(f))
            .map_err(io::Error::other)
    })?;
    json(output.join("exterior-chart.json"), chart.alphabet())?;
    json(output.join("source-cursor.json"), &reader.cursor())?;
    json(
        output.join("summary.json"),
        &serde_json::json!({"schema":"holonics.conversation-coupled-source.v1","stage":stage,"source_receiver":receiver,
        "error":operation.as_ref().err().map(ToString::to_string),"frames":frames,"observations":observations,"fields":fields,"returned":returned,
        "epoch":wave.epoch(),"normal_observations":wave.normal_material().observations(),"resident":s.census(),"milliseconds":started.elapsed().as_millis()}),
    )?;
    operation
}
