//! Public constituted-field model: local reaction learning, whole-section generation, actual
//! output-target updates, held-out phase fields and native rest. The driver supplies data only.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, NativeConstitutiveField, NativeFieldOccurrence, NativeJunctionSeed,
        NativePhaseCurrent, ResidentConstitutiveCurrent, ResidentConstitutiveFibre,
        ResidentGeneratorNeighborhood, ResidentNormalMaterial,
    },
    resident_section::{ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface},
};
use holonics_hna::native::{NativeCoupledBody, SavedCoupledBody};
use num_rational::BigRational as Rat;
use num_traits::Zero;
use serde_json::{Value, json};
use std::{fs, path::PathBuf, time::Instant};
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn point<'c>(s: &'c ResidentSurface<'c>, v: &[i64]) -> Result<ResidentSection<'c>> {
    Ok(s.mount_section_rest(&ResidentSectionRest::found(
        1,
        v.len(),
        ResidentGrain(0),
        64,
        v.iter().map(|x| (*x, *x)).collect(),
    )?)?)
}
fn current<'a, 'c>(s: &'a ResidentSection<'c>) -> Result<ResidentConstitutiveCurrent<'a, 'c>> {
    Ok(ResidentConstitutiveCurrent::integers(s)?)
}
fn input(h: [i64; 2]) -> [i64; 6] {
    let [a, b] = h;
    [a, b, -b, a, a + b, b - a]
}
fn target(h: [i64; 2]) -> [i64; 6] {
    let v = input(h);
    [-v[1], v[0], -v[3], v[2], -v[5], v[4]]
}
fn error(
    read: &holonic_engine::native_ecology::constitutive_fibre::NativeFieldCurrentBall,
    target: &[i64],
) -> Rat {
    read.center
        .iter()
        .zip(target.chunks_exact(2))
        .fold(Rat::zero(), |s, (x, t)| {
            let re = &x.real - Rat::from_integer(t[0].into());
            let im = &x.imaginary - Rat::from_integer(t[1].into());
            s + &re * &re + &im * &im
        })
}
fn evaluation<'c>(body: &mut NativeCoupledBody<'c>, s: &'c ResidentSurface<'c>) -> Result<Value> {
    let mut rows = Vec::new();
    let mut total = Rat::zero();
    for h in [[3, 1], [-2, 3], [1, -3], [-3, -2]] {
        let x = input(h);
        let t = target(h);
        let input = point(s, &x)?;
        let condition = point(s, &h)?;
        let clock = Instant::now();
        let generated = body.preview_field(current(&input)?.into(), current(&condition)?)?;
        let micros = clock.elapsed().as_micros();
        let reading = generated.output().inspect()?;
        let squared = error(&reading, &t);
        total += &squared;
        rows.push(json!({"condition":h,"input":x,"target":t,"output":reading,
            "center_error_squared":squared.to_string(),"generation_us":micros}));
    }
    Ok(
        json!({"cases":rows,"center_error_squared_sum":total.to_string(),"receiver":"exact squared error of the output centre, with its source radius reported separately"}),
    )
}
fn main() -> Result<()> {
    let mut args = std::env::args().skip(1);
    let directory = PathBuf::from(
        args.next()
            .ok_or("supply output directory, and optionally training iterations")?,
    );
    // One pass over the eight declared training conditions is the first local model task.
    let iterations: usize = args.next().as_deref().unwrap_or("8").parse()?;
    fs::create_dir_all(&directory)?;
    let start = Instant::now();
    let readout = ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    let seed = NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: NativePhaseCurrent::zero(),
    };
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        vec![seed],
        ResidentGrain(48),
    )?;
    let first = field.advance_resident(&mut NativeFieldOccurrence::entering(vec![
        NativePhaseCurrent::new(1, 0, 1)?,
    ]))?;
    field.advance_resident(&mut NativeFieldOccurrence::through(
        first.source,
        vec![NativePhaseCurrent::new(0, 1, 1)?],
    ))?;
    let law = ResidentConstitutiveFibre::found_bilinear_contact(&surface, 3, 1, 3)?;
    let material = ResidentNormalMaterial::found_features(&surface, 7, 3, ResidentGrain(48))?;
    let h = point(&surface, &[1, 0])?;
    let mut neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law],
        current(&h)?,
        ConditionContactMetric::UnitAdmittanceRealification,
    )?;
    neighborhood
        .attach_normal_prediction(0, material)
        .map_err(|(_, e)| e)?;
    let mut body = NativeCoupledBody::from_field(field, neighborhood, 0).map_err(|r| r.reason)?;
    let setup_us = start.elapsed().as_micros();
    let before = evaluation(&mut body, &surface)?;
    fs::write(
        directory.join("before.json"),
        serde_json::to_vec_pretty(&before)?,
    )?;
    // Actual local supervision teaches the conditional reaction a nonzero phase correction;
    // source basis examples vary independently of h. The normal learner lives in the library.
    let local_clock = Instant::now();
    let mut local_examples = 0;
    for basis in 0..7 {
        let mut source = [0; 6];
        if basis > 0 {
            source[basis - 1] = 1;
        }
        for h in [[0, 0], [1, 0], [0, 1]] {
            let x = input(h);
            let y = target(h);
            let correction: Vec<_> = y.iter().zip(x).map(|(a, b)| a - b).collect();
            let source = point(&surface, &source)?;
            let h = point(&surface, &h)?;
            let t = point(&surface, &correction)?;
            body.train_field_reaction(current(&source)?.into(), current(&h)?, current(&t)?.into())?;
            local_examples += 1;
        }
    }
    let local_training_us = local_clock.elapsed().as_micros();
    let after_local = evaluation(&mut body, &surface)?;
    fs::write(
        directory.join("after-local.json"),
        serde_json::to_vec_pretty(&after_local)?,
    )?;
    let mut returns = Vec::new();
    let training = Instant::now();
    let training_conditions = [
        [1, 0],
        [0, 1],
        [-1, 0],
        [0, -1],
        [2, 0],
        [0, 2],
        [-2, 0],
        [0, -2],
    ];
    for step in 0..iterations {
        let h = training_conditions[step % training_conditions.len()];
        let x = input(h);
        let t = target(h);
        let x = point(&surface, &x)?;
        let h = point(&surface, &h)?;
        let target = point(&surface, &t)?;
        let preview = body.preview_field(current(&x)?.into(), current(&h)?)?;
        let generated = body.generate_field(current(&x)?.into(), current(&h)?, true)?;
        assert_eq!(
            preview.output().inspect()?,
            generated.output().inspect()?,
            "preview and commit must evaluate the same source operation"
        );
        let id = generated
            .comparison_id()
            .ok_or("missing producing comparison")?;
        let returned = match body.observe_field(id, current(&target)?.into(), 3) {
            Ok(returned) => returned,
            Err(error) => {
                fs::write(directory.join("training-obstruction.json"), serde_json::to_vec_pretty(
                    &json!({"completed_targets":step,"pending_comparison":id,"error":error.to_string(),
                        "generated":generated.inspect()?,"target":t,"state":body.inspect_current()?,
                        "completed_returns":returns}))?)?;
                return Err(error.into());
            }
        };
        assert!(
            body.observe_field(id, current(&target)?.into(), 3).is_err(),
            "one actual target is incorporated once"
        );
        returns.push(returned);
        if step % 8 == 7 {
            eprintln!("trained {} complete field targets", step + 1);
        }
    }
    let training_us = training.elapsed().as_micros();
    let after = evaluation(&mut body, &surface)?;
    let state = body.inspect_current()?;
    let rest = body.rest()?;
    let mut bytes = Vec::new();
    rest.write(&mut bytes)?;
    fs::write(directory.join("athena-field.rest"), &bytes)?;
    // The live owner is dropped before remount; preview did not change its continuing state.
    drop(body);
    drop(rest);
    let saved = fs::read(directory.join("athena-field.rest"))?;
    let rest = SavedCoupledBody::read(&mut saved.as_slice(), saved.len() as u64)?;
    let mut resumed = rest.remount(&surface)?;
    let resumed_output = evaluation(&mut resumed, &surface)?;
    for (a, b) in after["cases"]
        .as_array()
        .unwrap()
        .iter()
        .zip(resumed_output["cases"].as_array().unwrap())
    {
        assert_eq!(
            a["output"], b["output"],
            "native rest must preserve the learned operation"
        );
    }
    let result = json!({"schema":"holonics.athena.constituted-field.v1","task":"joint quarter-turn of three complex boundary coordinates",
        "supplied":"one-node initial contact geometry; explicit scalar complex boundary condition; fixed source/receiver restrictions and target transformation",
        "learned":"local conditional reaction from native normal material and direct operative D/M responses to actual model output targets",
        "refinement":"one declared reaction-before-scattering step per generated whole section; no per-coordinate prediction clock",
        "local_examples":local_examples,"actual_model_targets":iterations,"setup_us":setup_us,
        "fractional_bits":48,"surface_transfer_census":surface.census(),
        "local_training_us":local_training_us,"model_training_us":training_us,"before":before,"after_local_training":after_local,
        "after_model_training":after,"observed_returns":returns,"model_state":state,"rest_octets":bytes.len(),"rest_receiver_match":true,
        "hardware_scope":"CUDA resident exact arithmetic; host source data, target error receivers and durable I/O"});
    fs::write(
        directory.join("return.json"),
        serde_json::to_vec_pretty(&result)?,
    )?;
    println!(
        "{}",
        json!({"output":directory,"actual_model_targets":iterations,"rest_octets":bytes.len(),"rest_receiver_match":true})
    );
    Ok(())
}
