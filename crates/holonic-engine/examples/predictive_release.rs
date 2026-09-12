//! Exact release synthesis and deterministic transport of unresolved source conditions.
//! Units: m, s, kg; a declared constant downward acceleration 10 m/s^2, not an Earth calibration.
use holonic_engine::exact_linear::{ConstantAccelerationRelease, ReceiverFactorization};
use holonic_engine::surprisal::SymbolicSurprisal;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde_json::json;
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn strings(v: &[Rat]) -> Vec<String> {
    v.iter().map(ToString::to_string).collect()
}
fn main() -> Result<()> {
    let motion = ConstantAccelerationRelease::new(2, q(2, 1))?;
    let t = q(1, 1);
    let initial = vec![q(0, 1), q(1, 1), q(0, 1), q(0, 1), q(0, 1), q(-10, 1)];
    let target = vec![q(4, 1), q(1, 1)];
    let coast = motion
        .position_receiver()?
        .multiply(&motion.flow(&t)?)?
        .apply(&initial)?;
    let residual: Vec<_> = target
        .iter()
        .zip(coast)
        .map(|(target, held)| target - held)
        .collect();
    let (impulse, kernel) = motion
        .impulse_receiver(&t)?
        .preimage_fibre(&residual)?
        .ok_or("requested landing is not in the impulse image")?;
    assert!(kernel.is_empty());
    assert_eq!(impulse, vec![q(8, 1), q(10, 1)]);
    let mut release_source = initial;
    release_source.extend(impulse.clone());
    let released = motion.release()?.apply(&release_source)?;
    assert_eq!(motion.endpoint(&t)?.apply(&release_source)?, target);
    let mut cuts = Vec::new();
    for time in [q(0, 1), q(1, 2), q(1, 1)] {
        let current = motion.flow(&time)?.apply(&released)?;
        let kinetic = &current[2] * &current[2] + &current[3] * &current[3];
        let potential = q(20, 1) * &current[1];
        assert_eq!(&kinetic + &potential, q(61, 1));
        cuts.push(
            json!({"time_seconds":time.to_string(),"state":strings(&current),
            "kinetic_joules":kinetic.to_string(),"potential_joules":potential.to_string()}),
        );
    }
    // Eight seconds of motion can be conducted as one exact operator, or rebased at any cut.
    assert_eq!(
        motion.flow(&q(3, 1))?.multiply(&motion.flow(&q(5, 1))?)?,
        motion.flow(&q(8, 1))?
    );
    // A present position does not fix a later position when velocity remains unresolved.
    let future = motion.position_receiver()?.multiply(&motion.flow(&t)?)?;
    let ReceiverFactorization::Obstructed {
        source_null,
        returned,
    } = motion.position_receiver()?.factor_receiver(&future)?
    else {
        return Err("the present position must not determine this complete future".into());
    };
    // The physical law is deterministic for each source. These weights describe unresolved
    // impulse deviations; no randomness is sampled and no probability changes the flow law.
    let population = [
        (q(-1, 5), q(1, 4)),
        (Rat::zero(), q(1, 2)),
        (q(1, 5), q(1, 4)),
    ];
    let mut mean_x = Rat::zero();
    let mut success = Rat::zero();
    let mut mean_energy = Rat::zero();
    let mut entropy = SymbolicSurprisal::zero();
    let mut outcomes = Vec::new();
    for (deviation, mass) in population {
        let mut source = release_source.clone(); // Independent declared experimental source, not a continuing body.
        source[6] += &deviation;
        let endpoint = motion.endpoint(&t)?.apply(&source)?;
        let state = motion.release()?.apply(&source)?;
        let kinetic = &state[2] * &state[2] + &state[3] * &state[3];
        let inside = (&endpoint[0] - q(4, 1)).abs() <= q(1, 20);
        mean_x += &mass * &endpoint[0];
        mean_energy += &mass * &kinetic;
        if inside {
            success += &mass;
        }
        entropy = entropy.plus(&SymbolicSurprisal::of_probability(&mass)?.scaled(&mass));
        outcomes.push(
            json!({"impulse_deviation":deviation.to_string(),"mass":mass.to_string(),
            "endpoint":strings(&endpoint),"within_declared_tolerance":inside}),
        );
    }
    assert_eq!(mean_x, q(4, 1));
    assert_eq!(success, q(1, 2));
    assert_eq!(mean_energy, q(8201, 200));
    assert_eq!(entropy, SymbolicSurprisal::term(2, q(3, 2))?);
    let report = json!({"schema":"holonics.predictive-release.v1",
        "chart":{"length":"metre","time":"second","mass":"kilogram","mass_value":"2",
            "acceleration":["0","-10"],"scope":"uniform weak-field acceleration; no air drag, spin, articulated preparation or GR field solve"},
        "requested_endpoint":strings(&target),"release_impulse":strings(&impulse),"released_state":strings(&released),
        "release_kinetic_work_joules":"41","cuts":cuts,
        "source_fibre_separator":{"source_null":strings(&source_null),"future_difference":strings(&returned)},
        "uncertain_sources":outcomes,"mean_endpoint_x":mean_x.to_string(),
        "success_mass_at_tolerance_1_over_20":success.to_string(),"expected_launch_energy_joules":mean_energy.to_string(),
        "source_entropy_bits":entropy.named(),"source_sampling":false,"native_ecology_changed":false});
    let text = serde_json::to_string_pretty(&report)?;
    if let Some(path) = std::env::args().nth(1) {
        std::fs::write(path, format!("{text}\n"))?;
    }
    println!("{text}");
    Ok(())
}
