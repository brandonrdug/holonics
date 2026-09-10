//! Public normal material import and generator-word continuation. Source data stays exterior;
//! the wave runs only from its learned material, exact initial currents and retained word.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        NormalMaterialRest, NormalWaveRest, ResidentConstitutiveCurrent,
    },
    resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface},
};
use holonics_hna::publish_new;
use std::{
    error::Error,
    fs::File,
    io::{self, BufReader},
    path::{Path, PathBuf},
    time::Instant,
};
type Result<T> = std::result::Result<T, Box<dyn Error>>;

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct StateData {
    schema: String,
    rows: usize,
    width: usize,
    grain: u32,
    bound_octaves: u32,
    intervals: Vec<(i64, i64)>,
}
fn read_material(path: &Path) -> Result<NormalMaterialRest> {
    let file = File::open(path)?;
    let length = file.metadata()?.len();
    Ok(NormalMaterialRest::read(&mut BufReader::new(file), length)?)
}
fn main() -> Result<()> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if let [mode, input, grain, output] = args.as_slice() {
        if mode == "refine" {
            let rest = read_material(Path::new(input))?;
            let readout = ResidentReadout::new()?;
            let surface = ResidentSurface::on(&readout)?;
            let mut material = rest.remount(&surface)?;
            let returned = material.refine_realization(ResidentGrain(grain.parse::<u32>()?))?;
            let before = returned.inspect_before()?;
            let after = returned.inspect_after()?;
            if before.source_normal != after.source_normal
                || before.cross_source != after.cross_source
                || before.source_normal_error != after.source_normal_error
                || before.cross_source_error != after.cross_source_error
                || before.target_energy != after.target_energy
                || before.target_energy_error != after.target_energy_error
            {
                return Err("refinement changed source geometry".into());
            }
            let rest = material.rest()?;
            publish_new(output, |file| rest.write(file).map_err(io::Error::other))?;
            println!(
                "{}",
                serde_json::json!({"mode":"refine","before_grain":returned.before_grain.0,
                "after_grain":returned.after_grain.0,"observations":returned.observations,
                "source_geometry_unchanged":true,"coefficient_error_before":before.material.radius.to_string(),
                "coefficient_error_after":after.material.radius.to_string()})
            );
            return Ok(());
        }
    }
    if let [mode, directory, output] = args.as_slice() {
        if mode != "import" {
            return Err("expected import SOURCE_RUN NEW.normal".into());
        }
        let started = Instant::now();
        let directory = Path::new(directory);
        let summary: serde_json::Value =
            serde_json::from_reader(File::open(directory.join("summary.json"))?)?;
        if summary["schema"] != "holonics.conversation-difference-field.v1"
            || summary["observed_receiver"] != "next-minus-current"
            || summary["source_ports"]
                != serde_json::json!(["current-minus-previous", "current", "previous"])
        {
            return Err("incompatible recorded source/receiver chart".into());
        }
        let n = summary["alphabet_coordinates"]
            .as_u64()
            .ok_or("missing source extent")? as usize;
        let grain = summary["grain"].as_u64().ok_or("missing grain")? as u32;
        let observations = summary["observed_local_comparisons"]
            .as_u64()
            .ok_or("missing observation cut")?;
        let data: StateData = serde_json::from_reader(BufReader::new(File::open(
            directory.join("native-state.json"),
        )?))?;
        if data.schema != "holonics.normal-state-data.v1" {
            return Err("unsupported state data".into());
        }
        let state = ResidentSectionRest::found(
            data.rows,
            data.width,
            ResidentGrain(data.grain),
            data.bound_octaves,
            data.intervals,
        )?;
        let rest =
            NormalMaterialRest::from_state_data(n, n, ResidentGrain(grain), observations, state)?;
        publish_new(output, |file| rest.write(file).map_err(io::Error::other))?;
        println!(
            "{}",
            serde_json::json!({"mode":"import","roots":n,"observations":observations,"seconds":started.elapsed().as_secs_f64()})
        );
        return Ok(());
    }
    let (mode,input,steps,coordinate,output)=match args.as_slice(){
        [mode,input,steps,coordinate,output] if mode=="start"=>(mode.as_str(),input,steps.parse::<u64>()?,Some(coordinate.parse::<usize>()?),output),
        [mode,input,steps,output] if mode=="resume"=>(mode.as_str(),input,steps.parse::<u64>()?,None,output),
        _=>return Err("usage: normal_wave import SOURCE_RUN NEW.normal | refine MODEL.normal GRAIN NEW.normal | start MODEL.normal STEPS COORDINATE NEW.wave | resume SAVED.wave EXTRA_STEPS NEW.wave".into()),
    };
    let output = PathBuf::from(output);
    let report = output.with_extension("json");
    if output.exists() || report.exists() {
        return Err("output already exists".into());
    }
    let started = Instant::now();
    let readout = ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    let mut wave = if mode == "start" {
        let rest = read_material(Path::new(input))?;
        let n = rest.roots();
        let coordinate = coordinate.unwrap();
        if coordinate >= n {
            return Err("excitation outside the declared current chart".into());
        }
        let mut values = vec![(0, 0); 2 * n];
        let previous = surface.mount_section_rest(&ResidentSectionRest::found(
            1,
            2 * n,
            ResidentGrain(0),
            64,
            values.clone(),
        )?)?;
        values[2 * coordinate] = (1, 1);
        let current = surface.mount_section_rest(&ResidentSectionRest::found(
            1,
            2 * n,
            ResidentGrain(0),
            64,
            values,
        )?)?;
        rest.remount(&surface)?
            .into_difference_wave(
                ResidentConstitutiveCurrent::integers(&previous)?,
                ResidentConstitutiveCurrent::integers(&current)?,
            )
            .map_err(|r| r.reason)?
    } else {
        let file = File::open(input)?;
        let length = file.metadata()?.len();
        let rest = NormalWaveRest::read(&mut BufReader::new(file), length)?;
        rest.remount(&surface, |step| eprintln!("decoded generator word {step}"))?
    };
    let first = wave.steps();
    let standing = surface.census().resident_octets_now;
    let mut trajectory = Vec::new();
    for _ in 0..steps {
        let before = surface.census();
        let clock = Instant::now();
        let returned = wave.advance()?;
        let after = surface.census();
        let seconds = clock.elapsed().as_secs_f64();
        let reading = returned.inspect()?;
        trajectory.push(serde_json::json!({"reading":reading,"seconds":seconds,
            "numerical_readouts_during_passage":after.section_read_outs-before.section_read_outs,
            "ingress_octets_during_passage":after.ingress_octets-before.ingress_octets}));
        eprintln!(
            "generator word {} returned in {:.3}s",
            wave.steps(),
            seconds
        );
        drop(returned);
        if surface.census().resident_octets_now != standing {
            return Err("wave retained an earlier current or workspace".into());
        }
    }
    let rest = wave.rest()?;
    publish_new(&output, |file| rest.write(file).map_err(io::Error::other))?;
    let result = serde_json::json!({"scope":"fixed learned normal generator and bounded joint current; not language attainment",
        "mode":mode,"first_word":first,"last_word":wave.steps(),"coordinate":coordinate,
        "resident_octets":standing,"rest_octets":std::fs::metadata(&output)?.len(),
        "process_seconds":started.elapsed().as_secs_f64(),"trajectory":trajectory});
    publish_new(&report, |file| {
        serde_json::to_writer(file, &result).map_err(io::Error::other)
    })?;
    println!(
        "{}",
        serde_json::json!({"mode":mode,"first_word":first,"last_word":wave.steps(),
        "resident_octets":standing,"rest_octets":std::fs::metadata(&output)?.len()})
    );
    Ok(())
}
