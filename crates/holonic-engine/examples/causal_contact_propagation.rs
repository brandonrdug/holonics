//! Cold exact composition on a stored native operator. No model execution, learner or replay.
use holonic_engine::native_ecology::constitutive_fibre::{
    CausalContactPropagation, NativeFieldCurrentBall, NativeOperativeContactBirth,
};
use holonic_engine::ExactComplexWaveCurrent as Wave;
use num_traits::Zero;
use relational_geometry::Rat;
use serde::Deserialize;
use serde_json::json;
use std::{
    error::Error,
    fs,
    io::{BufReader, Write},
    time::Instant,
};

#[derive(Deserialize)]
struct InputBall {
    center: Vec<Wave>,
    radius: Rat,
}
#[derive(Deserialize)]
struct Operator {
    field_cut: usize,
    fractional_bits: u32,
    births: Vec<NativeOperativeContactBirth>,
    contacts: Vec<Vec<Wave>>,
    contacts_radius: Rat,
    internal: InputBall,
    numerical_contact_norm_upper: Rat,
}
fn norm(v: &[Wave]) -> Rat {
    v.iter().map(Wave::norm_square).sum()
}
fn aggregate(contacts: &[Vec<Wave>], current: &[Wave]) -> Vec<Wave> {
    let mut value = vec![Wave::zero(); contacts.first().map_or(0, Vec::len)];
    for (d, b) in contacts.iter().zip(current) {
        for (out, d) in value.iter_mut().zip(d) {
            *out = out.add(&d.multiply(b));
        }
    }
    value
}
fn separator(left: &[Wave], right: &[Wave], radius: &Rat) -> Option<serde_json::Value> {
    left.iter().zip(right).enumerate().find_map(|(coordinate,(a,b))| {
        let square = a.subtract(b).norm_square();
        (square > radius*radius).then(||json!({"coordinate":coordinate,
            "squared_center_distance":square.to_string(),"squared_sum_of_radii":(radius*radius).to_string()}))
    })
}
fn main() -> Result<(), Box<dyn Error>> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if !(args.len() == 2 || (args.len() == 3 && args[2] == "--enclosed")) {
        return Err(
            "usage: causal_contact_propagation PRIVATE_REPORT.json NEW_RECEIPT.json [--enclosed]"
                .into(),
        );
    }
    let mut document: serde_json::Value =
        serde_json::from_reader(BufReader::new(fs::File::open(&args[0])?))?;
    let operator: Operator = serde_json::from_value(document["body"]["operative_contacts"].take())?;
    let start = Instant::now();
    let (family, joined, rounding_radius) = if args.len() == 3 {
        let result = CausalContactPropagation::at_enclosed(
            &operator.births,
            &operator.contacts,
            &operator.contacts_radius,
            &NativeFieldCurrentBall {
                center: operator.internal.center.clone(),
                radius: operator.internal.radius.clone(),
            },
            operator.fractional_bits,
        )?;
        (result.internal, result.joins, Some(result.rounding_radius))
    } else {
        let path = CausalContactPropagation::at(
            &operator.births,
            operator.contacts.clone(),
            &operator.internal.center,
        )?;
        (
            path.enclosed_internal(&operator.contacts_radius, &operator.internal.radius)?,
            path.joins().collect(),
            None,
        )
    };
    let incoming_norm = norm(&operator.internal.center);
    if rounding_radius.is_none() {
        assert_eq!(incoming_norm, norm(&family.center));
    }
    let internal_separator = separator(
        &operator.internal.center,
        &family.center,
        &(&operator.internal.radius + &family.radius),
    );
    // With an exact producing map, D maps each complete current ball with this retained norm bound.
    // A nonzero map radius needs its additional mixed terms before comparing these boundary balls.
    let boundary_separator = if operator.contacts_radius.is_zero() {
        let before = aggregate(&operator.contacts, &operator.internal.center);
        let after = aggregate(&operator.contacts, &family.center);
        separator(
            &before,
            &after,
            &((&operator.internal.radius + &family.radius)
                * &operator.numerical_contact_norm_upper),
        )
    } else {
        None
    };
    let receipt = json!({"grade":"established-bounded","evidence":["implemented-exact","computational-witness"],
        "scope":"Cold exact causal-join composition on a complete stored operator cut. Current/contact uncertainty retained. No native propagation update or text-quality claim.",
        "source_report":args[0],"field_cut":operator.field_cut,"contacts":operator.contacts.len(),
        "joins":joined,"current_norm_preserved":rounding_radius.is_none().then_some(true),"incoming_squared_norm":incoming_norm.to_string(),
        "enclosed_fractional_bits":rounding_radius.as_ref().map(|_|operator.fractional_bits),
        "rounding_radius":rounding_radius.as_ref().map(ToString::to_string),
        "contacts_radius":operator.contacts_radius.to_string(),"incoming_radius":operator.internal.radius.to_string(),
        "propagated_radius":family.radius.to_string(),"internal_separator":internal_separator,
        "boundary_separator_with_exact_map":boundary_separator,"reference_seconds":start.elapsed().as_secs_f64()});
    let mut output = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&args[1])?;
    output.write_all(serde_json::to_string_pretty(&receipt)?.as_bytes())?;
    output.write_all(b"\n")?;
    println!(
        "{} contacts, {} actual joins; retained propagation family returned",
        operator.contacts.len(),
        joined.len()
    );
    Ok(())
}
