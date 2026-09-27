//! An independent scalar-coordinate witness for the loaded storage port (Decision 38).

use num_traits::Zero;

use crate::hnn::ring::{ResonatorMaterial, ResonatorOperands, ResonatorRemainders};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};

#[test]
fn the_loaded_port_returns_three_fifths_and_accounts_for_the_rest() {
    // One active real coordinate in the smallest complex carrier. At h=1, Y=2,
    // C=I, K=D=0 and zero state, M=(5/2)I. This gives independently known
    // rate=2/5, displacement=2/5, velocity=4/5 and returned wave=3/5.
    let identity = ExactRatMatrix::identity(2).unwrap();
    let zero = ExactRatMatrix::zero(2, 2).unwrap();
    let material = ResonatorMaterial::new(identity, zero.clone(), zero, None).unwrap();
    let operands = ResonatorOperands::at_cut(0, &material, &integer(2), &integer(1), None).unwrap();
    let quiet = vec![Rat::zero(); 2];
    let drive = vec![integer(1), Rat::zero()];
    let step = operands
        .step(
            0,
            &drive,
            [&quiet, &quiet],
            &ResonatorRemainders::default(),
            None,
        )
        .unwrap();

    assert_eq!(step.rate, vec![rat(2, 5), Rat::zero()]);
    assert_eq!(step.state[0], vec![rat(2, 5), Rat::zero()]);
    assert_eq!(step.state[1], vec![rat(4, 5), Rat::zero()]);
    assert_eq!(step.output, vec![rat(3, 5), Rat::zero()]);
    assert_eq!(step.after, rat(8, 25));
    assert_eq!(step.port, rat(8, 25));
    assert!(step.closes());
    // Wave energy 9/50 and mode energy 16/50 sum to the incoming 1/2.
    assert_eq!(
        rat(1, 2) * &step.output[0] * &step.output[0] + &step.after,
        rat(1, 2)
    );

    // Independent capacity-gain tangent at g_C=1: ds'/dg_C = 16/25.
    // Pull the output covector through the owner's transposed solve and
    // contract with 2 dC (w−ω), dC/dg_C=2I.
    let solved = operands
        .solve_transpose(0, &[-integer(1), Rat::zero()])
        .unwrap();
    let capacity_gain = -integer(4) * &solved[0] * &step.rate[0];
    assert_eq!(capacity_gain, rat(16, 25));
}
