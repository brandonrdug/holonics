//! Exact relativistic composition, recoil, electromagnetic energy flux and observer changes.
use holonics::exact_linear::{EnergyMomentum, MaxwellEnergyFace, VacuumEnergyChart};
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde_json::{Value, json};
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn v(x: i64, y: i64, z: i64) -> [Rat; 3] {
    [q(x, 1), q(y, 1), q(z, 1)]
}
fn face(p: &EnergyMomentum) -> Value {
    json!({"energy":p.energy.to_string(),
    "c_momentum":p.c_momentum.iter().map(ToString::to_string).collect::<Vec<_>>(),
    "mass_squared_c_fourth":p.invariant_square().to_string(),"future_causal":p.is_future_causal()})
}
fn field(f: &MaxwellEnergyFace) -> Value {
    json!({"energy_density":f.energy_density.to_string(),
    "poynting":f.poynting.iter().map(ToString::to_string).collect::<Vec<_>>(),
    "cone_residual":f.cone_residual.to_string(),"E_squared_minus_c_squared_B_squared":f.electric_minus_magnetic.to_string(),
    "E_dot_B":f.electric_dot_magnetic.to_string()})
}
fn main() -> Result<()> {
    let right = EnergyMomentum::photon(q(1, 1), v(1, 0, 0))?;
    let left = EnergyMomentum::photon(q(1, 1), v(-1, 0, 0))?;
    let opposite = right.add(&left);
    let parallel = right.add(&right);
    assert_eq!(opposite.invariant_square(), q(4, 1));
    assert!(parallel.invariant_square().is_zero());
    let boosted = opposite.boost_x(&q(4, 5), &q(5, 3))?;
    assert_eq!(boosted.invariant_square(), q(4, 1));
    assert_eq!(boosted.energy, q(10, 3));
    let body = EnergyMomentum::new(q(3, 1), v(0, 0, 0));
    let confined = body.add(&opposite);
    assert_eq!(confined.invariant_square(), q(25, 1));
    let absorbed = body.add(&right);
    assert_eq!(absorbed.invariant_square(), q(15, 1));
    // Two-body radiative transition: parent rest energy 5, daughter rest energy 3.
    let parent = EnergyMomentum::new(q(5, 1), v(0, 0, 0));
    let emitted = EnergyMomentum::photon(q(8, 5), v(1, 0, 0))?;
    let daughter = parent.subtract(&emitted);
    assert_eq!(daughter.invariant_square(), q(9, 1));
    assert_eq!(daughter.add(&emitted), parent);
    let recoil_kinetic = &daughter.energy - q(3, 1);
    assert_eq!(&recoil_kinetic + &emitted.energy, q(2, 1));
    // Elastic reflection conserves the body's invariant mass and transfers energy into recoil.
    let reflected = EnergyMomentum::photon(q(3, 5), v(-1, 0, 0))?;
    let recoiled = body.add(&right).subtract(&reflected);
    assert_eq!(recoiled.invariant_square(), body.invariant_square());
    assert_eq!(recoiled.add(&reflected), body.add(&right));
    let vacuum = VacuumEnergyChart::new(q(1, 1), q(1, 1), q(1, 1))?;
    let null = vacuum.read(&v(1, 0, 0), &v(0, 1, 0));
    let standing = vacuum.read(&v(1, 0, 0), &v(1, 0, 0));
    assert!(null.cone_residual.is_zero());
    assert_eq!(standing.cone_residual, q(1, 1));
    let (e, b) = vacuum.boost_fields_x(&v(1, 0, 0), &v(0, 1, 0), &q(4, 5), &q(5, 3))?;
    let boosted_field = vacuum.read(&e, &b);
    assert_eq!(boosted_field.energy_density, q(25, 9));
    assert!(boosted_field.cone_residual.is_zero());
    assert!(!boosted_field.energy_density.is_negative());
    // A constitutive rechart with c=1/2 and epsilon=mu=2 has impedance 1 and the same null law.
    let slower_chart = VacuumEnergyChart::new(q(1, 2), q(2, 1), q(2, 1))?;
    assert_eq!(slower_chart.impedance_squared(), q(1, 1));
    let scaled_null = slower_chart.read(&v(1, 0, 0), &v(0, 2, 0));
    assert!(scaled_null.cone_residual.is_zero());
    let c_si = q(299_792_458, 1);
    let retained_heat_mass = q(41, 1) / (&c_si * &c_si);
    let report = json!({"schema":"holonics.mass-energy-transport.v1",
        "chart":"c=1, epsilon=mu=1 unless the separate constitutive chart or SI heat conversion is stated; momentum stored as c*p",
        "opposite_photons":face(&opposite),"parallel_photons":face(&parallel),
        "boost_beta":"4/5","boost_gamma":"5/3","boosted_pair":face(&boosted),
        "body_with_balanced_retained_radiation":face(&confined),"photon_absorption":face(&absorbed),
        "radiative_transition":{"parent":face(&parent),"daughter":face(&daughter),"emission":face(&emitted),
            "recoil_kinetic":recoil_kinetic.to_string(),"rest_energy_difference":"2"},
        "reflection":{"reflected":face(&reflected),"recoiled_body":face(&recoiled)},
        "null_field":field(&null),"standing_field":field(&standing),"boosted_null_field":field(&boosted_field),
        "other_constitutive_chart":{"speed":"1/2","epsilon":"2","mu":"2","impedance_squared":"1","field":field(&scaled_null)},
        "41_joule_retained_heat_mass_kg":retained_heat_mass.to_string(),
        "heat_scope":"41 J retained as internal rest-frame energy; a 41 J translational kinetic increment is a different receiver",
        "native_operation_changed":false});
    let text = serde_json::to_string_pretty(&report)?;
    if let Some(path) = std::env::args().nth(1) {
        std::fs::write(path, format!("{text}\n"))?;
    }
    println!("{text}");
    Ok(())
}
