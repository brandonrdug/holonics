//! Exact release synthesis and deterministic transport of unresolved source conditions.
//! Units: m, s, kg; a declared constant downward acceleration 10 m/s^2, not an Earth calibration.
use holonics::exact_linear::{
    ConstantAccelerationRelease, ExactRatMatrix, ReceiverFactorization,
};
use holonics::ratio::surprisal::SymbolicSurprisal;
use num_traits::{Signed, Zero};
use holonics::geometry::Rat;
use serde_json::json;
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn strings(v: &[Rat]) -> Vec<String> {
    v.iter().map(ToString::to_string).collect()
}
fn main() -> Result<()> {
    if std::env::args().nth(1).as_deref() == Some("--native-requests") {
        return native_requests();
    }
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
            "acceleration":["0","-10"],"scope":"GR-derived weak-field motion simulation; prescribed uniform acceleration and point-body release"},
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

// Compile this same physical chart into caller-controlled public HNN requests. This
// branch supplies laws and a landing constraint; it does not solve the impulse on the
// host or supply expected intermediate predictions to the native session.
fn native_requests() -> Result<()> {
    let args: Vec<_> = std::env::args().skip(2).collect();
    if ![0, 2].contains(&args.len()) {
        return Err("usage: predictive_release --native-requests [target-x target-y]".into());
    }
    let target = if args.is_empty() {
        vec![q(4, 1), q(1, 1)]
    } else {
        args.iter()
            .map(|s| s.parse::<Rat>())
            .collect::<std::result::Result<Vec<_>, _>>()?
    };
    let wire = |v: &[Rat]| {
        v.iter()
            .map(|r| {
                json!({"numerator":r.numer().to_string(),
        "denominator":r.denom().to_string()})
            })
            .collect::<Vec<_>>()
    };
    let matrix = |m: &ExactRatMatrix| m.to_rows().iter().map(|row| wire(row)).collect::<Vec<_>>();
    let emit = |request: serde_json::Value| -> Result<()> {
        println!(
            "{}",
            json!({"schema":"org.holonics.hna.stream-request.v1",
            "command":{"action":"mathematical-request","request":request}})
        );
        Ok(())
    };
    // The exact complex dot-product chart reads components of h=(x,v,g,J).
    // Its calibration is supplied action material; h is inferred by native images.
    let mut calibration = Vec::new();
    for axis in 0..8 {
        let mut basis = vec![q(0, 1); 8];
        basis[axis] = q(1, 1);
        calibration.push(json!({"source":wire(&vec![q(0,1);8]),"condition":wire(&basis),"observed":wire(&[q(0,1),q(0,1)])}));
        calibration.push(json!({"source":wire(&basis),"condition":wire(&vec![q(0,1);8]),"observed":wire(&[q(0,1),q(0,1)])}));
    }
    for i in 0..4 {
        for j in 0..4 {
            for phase in 0..2 {
                let mut source = vec![q(0, 1); 8];
                source[2 * i + phase] = q(1, 1);
                let mut condition = vec![q(0, 1); 8];
                condition[2 * j] = q(1, 1);
                let mut observed = vec![q(0, 1); 2];
                if i == j {
                    observed[phase] = q(1, 1);
                }
                calibration.push(json!({"source":wire(&source),"condition":wire(&condition),"observed":wire(&observed)}));
            }
        }
    }
    emit(
        json!({"operation":"construct-relation","source_complex":4,"condition_complex":4,"target_complex":1,
        "calibration":calibration,"initial_source":wire(&[q(1,1),q(0,1),q(0,1),q(0,1),q(0,1),q(0,1),q(0,1),q(0,1)]),
        "initial_observed":wire(&[q(0,1),q(1,1)])}),
    )?;
    for (prediction, axis, value) in [(0, 1, [0, 0]), (1, 2, [0, -10])] {
        let mut source = vec![q(0, 1); 8];
        source[2 * axis] = q(1, 1);
        emit(
            json!({"operation":"predict-relation","relation":0,"source":{"kind":"values","values":wire(&source)},"retain_prediction":true}),
        )?;
        emit(
            json!({"operation":"observe-relation","relation":0,"prediction":prediction,"observed":wire(&value.map(|v|q(v,1)))}),
        )?;
    }
    let motion = ConstantAccelerationRelease::new(2, q(2, 1))?;
    emit(json!({"operation":"construct-linear","coefficients":matrix(&motion.release()?)}))?; // operator 0
    for (time, flow) in [(q(1, 2), 1), (q(1, 1), 3)] {
        emit(json!({"operation":"construct-linear","coefficients":matrix(&motion.flow(&time)?)}))?;
        emit(json!({"operation":"compose","operator":0,"following":flow}))?; // 2, 4
    }
    emit(json!({"operation":"join-receivers","operators":[2,4]}))?; // 5
    emit(json!({"operation":"predict-condition","relation":0,"operator":5}))?;
    let mut comparison = vec![vec![q(0, 1); 12]; 2];
    for i in 0..2 {
        comparison[i][i] = q(-2, 1);
        comparison[i][6 + i] = q(1, 1);
    }
    emit(
        json!({"operation":"compose-receiver","operator":5,"matrix":matrix(&ExactRatMatrix::new(comparison)?)}),
    )?; // 6
    emit(json!({"operation":"predict-condition","relation":0,"operator":6}))?;
    let mut landing = vec![vec![q(0, 1); 12]; 2];
    for i in 0..2 {
        landing[i][6 + i] = q(1, 1);
    }
    emit(
        json!({"operation":"compose-receiver","operator":5,"matrix":matrix(&ExactRatMatrix::new(landing)?)}),
    )?; // 7
    emit(
        json!({"operation":"predict-condition","relation":0,"operator":7,"retain_prediction":true}),
    )?;
    emit(
        json!({"operation":"observe-relation","relation":0,"prediction":2,"observed":wire(&target)}),
    )?;
    emit(json!({"operation":"predict-condition","relation":0,"operator":5}))?;
    println!(
        "{}",
        json!({"schema":"org.holonics.hna.stream-request.v1","command":{"action":"close"}})
    );
    Ok(())
}
