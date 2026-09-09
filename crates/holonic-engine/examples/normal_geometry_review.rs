//! Exterior exact witnesses for normal-response reuse and complete versus open reflection.
//! Uses the standing matrix and paired-producer owners. No native learning law is changed.
use holonic_engine::exact_linear::ExactRatMatrix as Matrix;
use holonic_engine::native_ecology::constitutive_fibre::PairedJunctionLinearization;
use holonic_engine::ExactComplexWaveCurrent as Wave;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde_json::json;
use std::{error::Error, fs};

type Result<T> = std::result::Result<T, Box<dyn Error>>;
fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn column(v: &[i64]) -> Result<Matrix> {
    Ok(Matrix::new(v.iter().map(|n| vec![q(*n, 1)]).collect())?)
}
fn squared(m: &Matrix) -> Rat {
    m.entries().iter().map(|x| x * x).sum()
}
fn trace(m: &Matrix) -> Result<Rat> {
    if m.rows() != m.columns() {
        return Err("trace requires square matrix".into());
    }
    Ok((0..m.rows()).map(|i| m.get(i, i).unwrap().clone()).sum())
}
fn residual(m: &Matrix, h: &Matrix, b: &Matrix) -> Result<Matrix> {
    Ok(m.multiply(h)?.subtract(b)?)
}
fn potential(m: &Matrix, h: &Matrix, b: &Matrix, c: &Rat) -> Result<Rat> {
    Ok((trace(&m.multiply(h)?.multiply(&m.transpose()?)?)?
        - q(2, 1) * trace(&m.multiply(&b.transpose()?)?)?
        + c)
        / q(2, 1))
}
fn display(m: &Matrix) -> Vec<Vec<String>> {
    m.to_rows()
        .iter()
        .map(|r| r.iter().map(ToString::to_string).collect())
        .collect()
}

fn normal_witnesses() -> Result<serde_json::Value> {
    let events = [
        (column(&[1, 0])?, column(&[1, 0])?),
        (column(&[0, 1])?, column(&[0, 1])?),
        (column(&[1, 1])?, column(&[1, -1])?),
        (column(&[1, 0])?, column(&[0, 1])?),
    ];
    let mut h = Matrix::identity(2)?;
    let mut b = Matrix::zero(2, 2)?;
    let mut c = Rat::zero();
    // Deliberately start away from a normal solution. The residual law must still hold.
    let mut m = Matrix::new(vec![vec![q(1, 7), q(-1, 11)], vec![q(0, 1), q(1, 13)]])?;
    let mut returns = vec![];
    for (ordinal, (x, y)) in events.iter().enumerate() {
        let old_residual = residual(&m, &h, &b)?;
        assert!(!old_residual.entries().iter().all(Zero::is_zero));
        let z = h.inverse()?.multiply(x)?;
        let denominator = Rat::one() + x.transpose()?.multiply(&z)?.get(0, 0)?;
        assert!(denominator > Rat::zero());
        let gain = z.scaled(&(Rat::one() / denominator));
        let next_h = h.add(&x.multiply(&x.transpose()?)?)?;
        let next_b = b.add(&y.multiply(&x.transpose()?)?)?;
        let e = y.subtract(&m.multiply(x)?)?;
        assert_eq!(gain.transpose()?.multiply(&next_h)?, x.transpose()?);
        let next_m = m.add(&e.multiply(&gain.transpose()?)?)?;
        let next_residual = residual(&next_m, &next_h, &next_b)?;
        assert_eq!(next_residual, old_residual);

        // A numerical gain and deposit must carry both errors through the NEW metric.
        let gain_error = Matrix::new(vec![vec![q(1, 16)], vec![q(-1, 32)]])?;
        let deposit_error = Matrix::new(vec![vec![q(1, 64), q(0, 1)], vec![q(0, 1), q(-1, 128)]])?;
        let approximate_gain = gain.add(&gain_error)?;
        let approximate_m = m
            .add(&e.multiply(&approximate_gain.transpose()?)?)?
            .add(&deposit_error)?;
        let gain_defect = approximate_gain
            .transpose()?
            .multiply(&next_h)?
            .subtract(&x.transpose()?)?;
        let predicted_residual = old_residual
            .add(&e.multiply(&gain_defect)?)?
            .add(&deposit_error.multiply(&next_h)?)?;
        assert_eq!(
            residual(&approximate_m, &next_h, &next_b)?,
            predicted_residual
        );
        assert_ne!(predicted_residual, old_residual);

        c += squared(y);
        h = next_h;
        b = next_b;
        m = next_m;
        let inverse = h.inverse()?;
        let stationary = b.multiply(&inverse)?;
        let optimum = potential(&stationary, &h, &b, &c)?;
        let attained = potential(&m, &h, &b, &c)?;
        let gap = trace(
            &next_residual
                .multiply(&inverse)?
                .multiply(&next_residual.transpose()?)?,
        )? / q(2, 1);
        assert_eq!(&attained - &optimum, gap);
        assert_eq!(
            optimum,
            (&c - trace(&b.multiply(&inverse)?.multiply(&b.transpose()?)?)?) / q(2, 1)
        );
        let direct_data: Rat = events[..=ordinal]
            .iter()
            .map(|(x, y)| squared(&m.multiply(x).unwrap().subtract(y).unwrap()))
            .sum();
        assert_eq!(attained, (squared(&m) + direct_data) / q(2, 1));
        returns.push(
            json!({"ordinal": ordinal, "H": display(&h), "B": display(&b),
            "C": c.to_string(), "retained_normal_residual": display(&next_residual),
            "attained_regularized_potential": attained.to_string(),
            "best_regularized_potential": optimum.to_string(), "solve_gap": gap.to_string(),
            "gain_and_deposit_defect_return": display(&predicted_residual)}),
        );
    }

    // A conflicting receiver fibre cannot be repaired by a more accurate solve in this chart.
    let x = column(&[1, 0])?;
    let first = column(&[1, 0])?;
    let second = column(&[0, 1])?;
    let collision_h = Matrix::identity(2)?.add(&x.multiply(&x.transpose()?)?.scaled(&q(2, 1)))?;
    let collision_b = first.add(&second)?.multiply(&x.transpose()?)?;
    let best = collision_b.multiply(&collision_h.inverse()?)?;
    let best_phi = potential(&best, &collision_h, &collision_b, &q(2, 1))?;
    let data_error = (squared(&best.multiply(&x)?.subtract(&first)?)
        + squared(&best.multiply(&x)?.subtract(&second)?))
        / q(2, 1);
    assert_eq!(best_phi, q(2, 3));
    assert_eq!(data_error, q(5, 9));
    assert_eq!(squared(&best) / q(2, 1), q(1, 9));

    // Recharting transports the existing prior as well as observations. The live normal owner
    // already consumes root currents; this is a future chart-transfer control, not a bug claim.
    let chart = Matrix::new(vec![vec![q(0, 1), q(-1, 1)], vec![q(1, 1), q(0, 1)]])?;
    let moved_h = chart.multiply(&h)?.multiply(&chart.transpose()?)?;
    let moved_b = b.multiply(&chart.transpose()?)?;
    let moved_m = m.multiply(&chart.transpose()?)?;
    assert_eq!(
        potential(&moved_m, &moved_h, &moved_b, &c)?,
        potential(&m, &h, &b, &c)?
    );
    Ok(
        json!({"events": returns, "source_rotation_preserves_potential": true,
        "conflicting_source_control": {"same_source": display(&x), "targets": [display(&first), display(&second)],
            "best_regularized_potential": best_phi.to_string(), "data_term": data_error.to_string(),
            "prior_term": (squared(&best) / q(2, 1)).to_string(),
            "scope": "constructed collision; no claim that these are the Athena model's actual sources"}}),
    )
}

fn wave(n: i64, d: i64) -> Wave {
    Wave::new(q(n, d), Rat::zero())
}
fn waves(v: &[Wave]) -> Vec<[String; 2]> {
    v.iter()
        .map(|w| [w.real.to_string(), w.imaginary.to_string()])
        .collect()
}
fn norm(v: &[Wave]) -> Rat {
    v.iter().map(Wave::norm_square).sum()
}

fn reflection_witnesses() -> Result<serde_json::Value> {
    let contacts = vec![vec![Wave::new(q(2, 1), q(1, 1))]];
    let u = vec![Wave::new(q(3, 1), q(-1, 2))];
    let b = vec![Wave::new(q(5, 1), q(2, 3))];
    let forward = PairedJunctionLinearization::at(contacts.clone(), &u, &b)?;
    let returned =
        PairedJunctionLinearization::at(contacts, forward.outgoing(), forward.internal())?;
    assert_eq!(returned.outgoing(), u);
    assert_eq!(returned.internal(), b);
    assert_eq!(
        norm(forward.outgoing()) + norm(forward.internal()),
        norm(&u) + norm(&b)
    );

    let contacts = vec![vec![wave(2, 1)]];
    let zero = vec![Wave::zero()];
    let first = PairedJunctionLinearization::at(contacts.clone(), &zero, &[wave(1, 1)])?;
    let second = PairedJunctionLinearization::at(contacts, &zero, first.internal())?;
    assert_eq!(first.internal(), [wave(3, 5)]);
    assert_eq!(second.internal(), [wave(9, 25)]);
    assert_eq!(first.outgoing(), [wave(4, 5)]);
    assert_eq!(second.outgoing(), [wave(12, 25)]);
    assert_eq!(norm(first.outgoing()) + norm(first.internal()), Rat::one());

    let hidden = vec![wave(1, 1), wave(-1, 1)];
    let blind =
        PairedJunctionLinearization::at(vec![vec![wave(1, 1)], vec![wave(1, 1)]], &zero, &hidden)?;
    assert_eq!(blind.outgoing(), zero);
    assert_eq!(blind.internal(), [wave(-1, 1), wave(1, 1)]);
    let reopened =
        PairedJunctionLinearization::at(vec![vec![wave(1, 1)], vec![wave(2, 1)]], &zero, &hidden)?;
    assert_eq!(reopened.outgoing(), [wave(-1, 3)]);
    Ok(json!({"complete_complex_reflection_returns_source": true,
        "open_zero_input_steps": [{"outgoing": waves(first.outgoing()), "internal": waves(first.internal())},
            {"outgoing": waves(second.outgoing()), "internal": waves(second.internal())}],
        "joint_current_energy_exact": true, "blind_internal_successor": waves(blind.internal()),
        "changed_contact_separates": waves(reopened.outgoing()),
        "scope": "existing exact passive producer; no closed timelike spacetime or periodic whole Athena ecology is assumed"}))
}

fn main() -> Result<()> {
    let path = std::env::args()
        .nth(1)
        .ok_or("usage: normal_geometry_review NEW_RECEIPT.json")?;
    let receipt = json!({"grade": "established-bounded", "evidence": ["implemented-exact", "computational-witness"],
        "scope": "exterior exact architecture controls; no model training or production semantic readout",
        "normal": normal_witnesses()?, "reflection": reflection_witnesses()?});
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)?;
    use std::io::Write;
    file.write_all(serde_json::to_string_pretty(&receipt)?.as_bytes())?;
    file.write_all(b"\n")?;
    println!("normal residual reuse, potential separation, chart transport and complete/open reflection: exact");
    Ok(())
}
