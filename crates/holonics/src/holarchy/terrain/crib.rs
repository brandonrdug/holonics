//! **Rotor cribs: a declared field's ring as a true reflector machine behind a plugboard.**
//!
//! [definition] The HNN's key location (`hnn::keys`) reads a crib the true machine produces on ring
//! `g`: `x_(k+1) = S⁻¹ W_(key + steps_g(k)) S x_k`, with `W_m = ρ^(−m) F ρ^m` the ring's stage at
//! rotor position `m` (`compression::ReflectorMachine::stage`), `S` the plugboard, and
//! `steps_g(k)` ring `g`'s ticks on the cells before `k` under the declared configurations of the
//! earlier rings, stepped by the field's selective law on the cells as they are produced
//! (`hnn::field::Field::selective_step`; Lean `HNN/Moment.selective_position`). Codes are ports,
//! below the ring's period.
//!
//! [definition; agent-inferred] **The truth** ([`CribTruth`]): the key and the plugboard, the
//! configurations and the start the crib was produced under, and the description of a drawn key
//! and plugboard, `⌈log₂(d · d!)⌉` bits (a key uniform on `ℤ/d`, a plugboard uniform among the
//! `d!` permutations by a Fisher–Yates shuffle, [`RotorCrib::draw`]). The key is located only up to
//! the ring's rotor gauge (Lean `HNN/Keys.rotorGauge`): the truth is one member of the located
//! orbit, published when the plugboard fixes the least menu port (`gauge_fix_unique`).

use num_bigint::{BigInt, BigUint};

use super::{Draw, TerrainError, refuse};
use crate::compression::cost::ceil_log2;
use crate::hnn::field::Field;
use crate::holon::contact::menu::PortPermutation;

/// [definition] **A rotor crib's truth** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CribTruth {
    pub ring: usize,
    pub key: u64,
    pub board: PortPermutation,
    pub configurations: Vec<u64>,
    pub start: usize,
    pub key_bits: u64,
}

/// [definition] **A rotor crib with its truth** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RotorCrib {
    pub cells: Vec<usize>,
    pub truth: CribTruth,
}

/// **The crib a true machine produces on ring `ring`** (module header): `length ≥ 1` cells from
/// `start`, each the machine's image of the one before at the ring's position `key + steps`.
pub fn rotor_crib(
    field: &Field,
    ring: usize,
    key: u64,
    board: &PortPermutation,
    configurations: &[u64],
    length: usize,
    start: usize,
) -> Result<Vec<usize>, TerrainError> {
    if length == 0 {
        return Err(refuse("a rotor crib", "it holds at least one cell"));
    }
    let machine = field.ring(ring).machine()?;
    let mut lift: Vec<BigInt> = configurations.iter().map(|c| BigInt::from(*c)).collect();
    let mut taken = 0u64;
    let mut crib = Vec::with_capacity(length);
    crib.push(start);
    for k in 0..length - 1 {
        let stage = machine.stage(&BigUint::from(key + taken))?;
        let image = stage.apply(board.apply(crib[k])?)?;
        crib.push(board.inverse().apply(image)?);
        taken += u64::from(field.selective_step(&mut lift, crib[k])?.ticks[ring]);
    }
    Ok(crib)
}

impl RotorCrib {
    /// **A crib under a drawn key and plugboard** (module header), from a drawn start port, under the
    /// declared configurations.
    pub fn draw(
        field: &Field,
        ring: usize,
        configurations: &[u64],
        length: usize,
        draw: &mut Draw,
    ) -> Result<Self, TerrainError> {
        let period = field.ring(ring).period();
        let ports = usize::try_from(period)
            .map_err(|_| refuse("a rotor crib", "the ring's period exceeds the address space"))?;
        let key = draw.below(ports) as u64;
        let mut images: Vec<usize> = (0..ports).collect();
        for i in (1..ports).rev() {
            images.swap(i, draw.below(i + 1));
        }
        let board = PortPermutation::new(images)?;
        let start = draw.below(ports);
        let cells = rotor_crib(field, ring, key, &board, configurations, length, start)?;
        let boards: BigUint = (1..=ports).map(BigUint::from).product();
        Ok(Self {
            cells,
            truth: CribTruth {
                ring,
                key,
                board,
                configurations: configurations.to_vec(),
                start,
                key_bits: ceil_log2(&(BigUint::from(period) * boards)),
            },
        })
    }
}
