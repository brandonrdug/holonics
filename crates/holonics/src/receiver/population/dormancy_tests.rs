//! Tests for **the executed chart's counted roundings** (module header, "The executed chart"): the
//! counter `roundings` covers every rounding factor Lean `Dormancy.dormant_executed_code` takes.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::*;
use crate::holarchy::terrain::{Grating, Moire, MoireClass, MoireFamily};
use crate::receiver::population::GratingParity;

/// An exact dyadic `m · 2^e`: the executed weights and the exact step from them.
#[derive(Clone)]
struct Dyadic(BigInt, i64);

impl Dyadic {
    fn zero() -> Self {
        Self(BigInt::zero(), 0)
    }

    fn of(weight: Weight) -> Self {
        Self(BigInt::from(weight.mantissa), weight.exponent)
    }

    fn plus(&self, other: &Self) -> Self {
        let floor = self.1.min(other.1);
        Self(
            (&self.0 << (self.1 - floor) as usize) + (&other.0 << (other.1 - floor) as usize),
            floor,
        )
    }

    fn times(&self, other: &Self) -> Self {
        Self(&self.0 * &other.0, self.1 + other.1)
    }

    fn le(&self, other: &Self) -> bool {
        let floor = self.1.min(other.1);
        (&self.0 << (self.1 - floor) as usize) <= (&other.0 << (other.1 - floor) as usize)
    }

    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

/// [proved-derived; formal-checked] **The roundings counted cover every factor the Lean takes**
/// (Lean `Dormancy.dormant_executed_code`'s `hround`). On a parity of two rings over `q ≤ 7`
/// (`8,100 = 2²·3⁴·5²` keys, so the first cells read past one chunk and its joins), ring 0 silent
/// over cells `[8, 16)`, each executed quantity is checked against the exact step from the executed
/// weights, with `ε = 2^(−62)` and every rounding chain read at its own length:
///
/// * the opening: `(1 − #a ε) π_A(a) ≤ W_0(k, a) ≤ π_A(a)` (Lean `hopen` with `ρ₀ ≥ 1 − L ε`
///   and `c = |K|`, and `hZ`), and the opening's count is at least `L`;
/// * each cell `t`, `E_(t+1) = Σ W_t f(t) K` the exact kernel of the executed weights:
///   `(1 − L ε) E_(t+1) ≤ W_(t+1) ≤ E_(t+1)` (Lean `hup` with `ρ_t ≥ 1 − L ε`, and `hdown`; one
///   share rounding a layer), the survivors exactly the keys `E_(t+1)` keeps; the scored class's
///   rounded sum `S̃_x ≥ (1 − m ε) Σ W_t f(t)`, `m` its chain (the weights it adds and the chunk
///   pieces it joins), and `Σ S̃ ≤ Σ W_t`, so `q̂_t = S̃_x/Σ S̃` gives Lean `hq` with
///   `μ_t ≥ 1 − m ε`; and the cell's count is at least `m + L`.
///
/// Since `1 − k ε ≥ (1 − ε)^k`, the factors multiply to at least `(1 − ε)^r`, `r` the counter's
/// total: Lean `hround` at `j = 62`, read from the executed chart rather than from the code.
#[test]
fn the_roundings_counted_cover_every_factor_the_lean_takes() {
    let rung = 3u32;
    let n = 20;
    let moire = Moire::new(
        vec![
            Grating::new(1, 3, 1).unwrap(),
            Grating::new(2, 7, 3).unwrap(),
        ],
        MoireClass::Parity,
    )
    .unwrap();
    let every = moire.emit(n);
    let quiet = moire.emit_active(n, &[false, true]);
    let cells: Vec<usize> = (0..n)
        .map(|t| {
            if (8..16).contains(&t) {
                quiet[t]
            } else {
                every[t]
            }
        })
        .collect();
    let family = MoireFamily {
        rings: 2,
        denominator: 7,
    };
    let mut filter = Dormancy::new(
        Box::new(GratingParity::new(&family).unwrap()),
        rung,
        1 << 16,
        "",
    )
    .unwrap();
    assert_eq!(filter.keys(), 8100);
    let (layers, masks) = (filter.layers(), filter.masks);
    let lowered = |chain: u128| Dyadic(BigInt::from((1u128 << 62) - chain), -62);
    let stay = Dyadic(BigInt::from((1u32 << rung) - 1), -i64::from(rung));
    let switch = Dyadic(BigInt::one(), -i64::from(rung));

    // The opening: at most the prior share, within its own chain of it, and counted.
    for (mask, &weight) in filter.opening.iter().enumerate() {
        let prior = Dyadic(
            BigInt::from((1u32 << rung) - 1).pow(mask.count_ones()),
            -i64::from(rung) * layers as i64,
        );
        let weight = Dyadic::of(weight);
        assert!(weight.le(&prior), "opening {mask}");
        let chain = u128::from(mask.count_ones());
        assert!(lowered(chain).times(&prior).le(&weight), "opening {mask}");
    }
    assert!(filter.roundings >= layers as u128);

    let mut chunked = false;
    for (t, &cell) in cells.iter().enumerate() {
        // The exact step from the executed weights: the whole, the emitting mass and its chain, and
        // the kernel.
        let (mut whole, mut emitted) = (Dyadic::zero(), Dyadic::zero());
        let mut chain = 0u128;
        let mut stepped: Vec<(u64, Vec<Dyadic>)> = Vec::new();
        let rows: Vec<(u64, Vec<Weight>)> = filter
            .rows()
            .map(|(key, row)| (key, row.to_vec()))
            .collect();
        chunked |= rows.len() > CHUNK;
        for part in rows.chunks(CHUNK) {
            let mut joined = false;
            for (key, row) in part {
                let sounding = filter.emitters.sounding(*key);
                let mut moved = Vec::with_capacity(masks);
                for (mask, &weight) in row.iter().enumerate() {
                    let weight = Dyadic::of(weight);
                    whole = whole.plus(&weight);
                    if filter.emitters.class(sounding, mask) == cell {
                        if !weight.is_zero() {
                            chain += 1;
                            joined = true;
                        }
                        emitted = emitted.plus(&weight);
                        moved.push(weight);
                    } else {
                        moved.push(Dyadic::zero());
                    }
                }
                for layer in 0..layers {
                    let bit = 1 << layer;
                    for mask in (0..masks).filter(|mask| mask & bit == 0) {
                        let (dormant, active) = (moved[mask].clone(), moved[mask | bit].clone());
                        moved[mask] = stay.times(&dormant).plus(&switch.times(&active));
                        moved[mask | bit] = switch.times(&dormant).plus(&stay.times(&active));
                    }
                }
                if moved.iter().any(|weight| !weight.is_zero()) {
                    stepped.push((*key, moved));
                }
            }
            chain += u128::from(joined);
        }

        let before = filter.roundings;
        let pending = filter.read(cell);
        let scored = Dyadic::of(pending.sums[cell]);
        let sums = pending
            .sums
            .iter()
            .fold(Dyadic::zero(), |sum, &weight| sum.plus(&Dyadic::of(weight)));
        assert!(sums.le(&whole), "cell {t}");
        assert!(scored.le(&emitted), "cell {t}");
        assert!(lowered(chain).times(&emitted).le(&scored), "cell {t}");
        filter.commit(pending, cell).unwrap();
        assert!(
            filter.roundings - before >= chain + layers as u128,
            "cell {t}"
        );

        let after: Vec<(u64, Vec<Weight>)> = filter
            .rows()
            .map(|(key, row)| (key, row.to_vec()))
            .collect();
        assert_eq!(after.len(), stepped.len(), "cell {t}");
        let kernel = lowered(layers as u128);
        for ((key, exact), (kept, row)) in stepped.iter().zip(&after) {
            assert_eq!(key, kept, "cell {t}");
            for (mask, (exact, &weight)) in exact.iter().zip(row).enumerate() {
                let weight = Dyadic::of(weight);
                assert!(weight.le(exact), "cell {t}, key {key}, activity {mask}");
                assert!(
                    kernel.times(exact).le(&weight),
                    "cell {t}, key {key}, activity {mask}"
                );
            }
        }
    }
    assert!(chunked, "a cell reads past one chunk");
}
