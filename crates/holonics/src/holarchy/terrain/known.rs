//! **Known truth: the passages a terrain's generator emits, and nothing else** (THE_MACHINE guard 9,
//! "One source type"; THE_REBUILD U6, lane E; #73, #148, #63).
//!
//! [definition; agent-inferred, October 5] **A known truth** ([`KnownTruth`]) is a read set of
//! passages on the classes `ℤ/|A|` that a terrain's generator emitted by its exact routine, with the
//! class count. Its fields are private and it has no public constructor: it is built only here, by
//! the library's terrain generators, so a cut file, a byte passage or a harness's vector is never a
//! known truth. It is what `hnn::encoding::Encoded::identity` reads, and the identity is refused
//! unless `|A| ≤ d_g` on every source ring (no fold).
//!
//! The generators:
//! - [`KnownTruth::cyclic`]: the cyclic terrains on `ℤ/|A|` the step-1 harness reads
//!   ([`CyclicLaw`]): **order-2**, `x_t` drawn uniformly for `t < o`, then `x_t = x_(t−2) + 1
//!   (mod |A|)`; the **alternation**, two drawn classes alternating, `x_t = x_(t−2)`; the **line**, a
//!   drawn start and step, `x_t = x_0 + s t (mod |A|)`. Moved from the notebook (`terrain_pairs`,
//!   `order_pairs`) unchanged in law and in the draw's order, so every receipt they wrote reads the
//!   same passages.
//! - [`KnownTruth::uniform`]: drawn cells on `ℤ/|A|` with no source structure, the synthetic
//!   fields' passages (the moment's, the port's and the card's parity reads).
//! - [`KnownTruth::interrupted`]: the period-four word `0, 1, 2, 1` interrupted by drawn cells,
//!   the port's and the card's parity source.
//! - [`KnownTruth::stepped`]: the located transport's terrain
//!   (`compression::keys::transport::SteppedTerrain`), `u_k = λ(c(ℓ(k)))`, `ℓ(k+1) = ℓ(k) + A(u_k)`,
//!   one passage per declared key.
//!
//! [definition] The computational object is the helical pair interaction, here as the terrain it
//! meets. Of the winding guide's six objects this owner touches the **helix** (the line's step and
//! the order-2 law's half-period carry on `ℤ/|A|`; the stepped terrain's lift on the carry helix) and
//! the **pair** (order-2 and the alternation are pair laws at distance 2, `x_t` against `x_(t−2)`);
//! faces and placement, the cell holonomy, the tube and the tower thread stay attached through the
//! encoding that reads it.

use crate::compression::keys::transport::SteppedTerrain;

use super::{Draw, TerrainError};

/// [definition] **A cyclic terrain's law on `ℤ/|A|`** (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CyclicLaw {
    /// `x_t` drawn uniformly for `t < opening`, then `x_t = x_(t−2) + 1 (mod |A|)`.
    OrderTwo { opening: usize },
    /// Two drawn classes `a, b` alternating: `x_t = a` at even `t`, `b` at odd.
    Alternation,
    /// A drawn start and step: `x_t = x_0 + s t (mod |A|)`.
    Line,
}

/// [definition] **A known truth** (module header): the class count `|A|` and the passages a
/// terrain's generator emitted, each a word on `ℤ/|A|`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KnownTruth {
    classes: usize,
    passages: Vec<Vec<usize>>,
}

impl KnownTruth {
    /// The one constructor, private to the generators below.
    fn emitted(classes: usize, passages: Vec<Vec<usize>>) -> Self {
        debug_assert!(passages.iter().flatten().all(|&class| class < classes));
        Self { classes, passages }
    }

    /// **A cyclic terrain** (module header): `count` passages of `length` cells on `ℤ/classes`, from
    /// `Draw::new(seed)`, each passage's draws in order (order-2: its opening's cells; the
    /// alternation: `a` then `b`; the line: `x_0` then `s`). Refused when the classes are empty, or
    /// order-2's opening holds fewer than the law's two antecedents or more cells than the passage.
    pub fn cyclic(
        law: CyclicLaw,
        classes: usize,
        seed: u64,
        count: usize,
        length: usize,
    ) -> Result<Self, TerrainError> {
        if classes == 0 {
            return Err(TerrainError::Declaration {
                what: "a cyclic terrain",
                reason: "it declares at least one class",
            });
        }
        if let CyclicLaw::OrderTwo { opening } = law
            && (opening < 2 || opening > length)
        {
            return Err(TerrainError::Declaration {
                what: "the order-2 terrain",
                reason: "its drawn opening holds the law's two antecedents and lies in the passage",
            });
        }
        let mut draw = Draw::new(seed);
        let passages = (0..count)
            .map(|_| match law {
                CyclicLaw::OrderTwo { opening } => {
                    let mut passage: Vec<usize> =
                        (0..opening).map(|_| draw.below(classes)).collect();
                    for t in opening..length {
                        passage.push((passage[t - 2] + 1) % classes);
                    }
                    passage
                }
                CyclicLaw::Alternation => {
                    let (a, b) = (draw.below(classes), draw.below(classes));
                    (0..length)
                        .map(|t| if t % 2 == 0 { a } else { b })
                        .collect()
                }
                CyclicLaw::Line => {
                    let (start, step) = (draw.below(classes), draw.below(classes));
                    (0..length).map(|t| (start + step * t) % classes).collect()
                }
            })
            .collect();
        Ok(Self::emitted(classes, passages))
    }

    /// **The uniform terrain** (the synthetic fields' drawn cells, no source structure): `count`
    /// passages of `length` cells, each drawn uniformly on `ℤ/classes` from `Draw::new(seed)` in
    /// order. Refused when the classes are empty.
    pub fn uniform(
        classes: usize,
        seed: u64,
        count: usize,
        length: usize,
    ) -> Result<Self, TerrainError> {
        if classes == 0 {
            return Err(TerrainError::Declaration {
                what: "the uniform terrain",
                reason: "it declares at least one class",
            });
        }
        let mut draw = Draw::new(seed);
        let passages = (0..count)
            .map(|_| (0..length).map(|_| draw.below(classes)).collect())
            .collect();
        Ok(Self::emitted(classes, passages))
    }

    /// **The interrupted cycle** (the moment's, the port's and the card's parity source): `count`
    /// passages of `length` cells from `Draw::new(seed)`, cell `k` a uniform class of `ℤ/classes`
    /// where a draw below 8 reads 0 (one cell in eight), else the period-four word `0, 1, 2, 1` at
    /// `k mod 4`, read on `ℤ/classes`. Refused when the classes are empty.
    pub fn interrupted(
        classes: usize,
        seed: u64,
        count: usize,
        length: usize,
    ) -> Result<Self, TerrainError> {
        if classes == 0 {
            return Err(TerrainError::Declaration {
                what: "the interrupted cycle",
                reason: "it declares at least one class",
            });
        }
        let mut draw = Draw::new(seed);
        let passages = (0..count)
            .map(|_| {
                (0..length)
                    .map(|k| {
                        if draw.below(8) == 0 {
                            draw.below(classes)
                        } else {
                            [0, 1, 2, 1][k % 4] % classes
                        }
                    })
                    .collect()
            })
            .collect();
        Ok(Self::emitted(classes, passages))
    }

    /// [definition; agent-inferred, October 5] **A test's declared words** (in-crate tests only:
    /// this exists in no build of the library, so no harness or file reaches it). The field's laws
    /// are tested on declared words (`[1, 3, 2]`, a run of zeros); a word outside `ℤ/classes` is a
    /// test defect and panics.
    #[cfg(test)]
    pub(crate) fn declared(classes: usize, passages: Vec<Vec<usize>>) -> Self {
        assert!(
            passages.iter().flatten().all(|&class| class < classes),
            "a declared word lies on its classes"
        );
        Self::emitted(classes, passages)
    }

    /// **The stepped terrain's passages** (`SteppedTerrain::passage`), one of `length` cells from
    /// each key; its classes are the receiving ring's cells, which its labels biject.
    pub fn stepped(terrain: &SteppedTerrain, keys: &[u64], length: usize) -> Self {
        let classes = usize::try_from(terrain.helix().cells()).expect("a cell count fits");
        Self::emitted(
            classes,
            keys.iter()
                .map(|&key| terrain.passage(key, length))
                .collect(),
        )
    }

    /// `|A|`, the terrain's class count.
    pub fn classes(&self) -> usize {
        self.classes
    }

    /// The emitted passages, each a word on `ℤ/|A|` (read to declare a request and to score; the
    /// field reads them only through `hnn::encoding::Encoded::identity`).
    pub fn passages(&self) -> &[Vec<usize>] {
        &self.passages
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// [implemented-exact] **The cyclic laws, in the harness's draw order**: each passage obeys its
    /// law on `ℤ/4`, and its draws are the harness's (`terrain_pairs` before October 5): order-2's
    /// opening cells in order, the alternation's `a` then `b`, the line's `x_0` then `s`, one draw
    /// for all passages.
    #[test]
    fn the_cyclic_terrains_obey_their_laws_in_the_harness_draw_order() {
        let (classes, seed, count, length) = (4, 2_026_100_973, 6, 48);
        let order = KnownTruth::cyclic(
            CyclicLaw::OrderTwo { opening: 40 },
            classes,
            seed,
            count,
            length,
        )
        .unwrap();
        let mut draw = Draw::new(seed);
        for passage in order.passages() {
            assert_eq!(passage.len(), length);
            for &cell in &passage[..40] {
                assert_eq!(cell, draw.below(classes));
            }
            for t in 40..length {
                assert_eq!(passage[t], (passage[t - 2] + 1) % classes);
            }
        }
        let alternation =
            KnownTruth::cyclic(CyclicLaw::Alternation, classes, seed, count, length).unwrap();
        let line = KnownTruth::cyclic(CyclicLaw::Line, classes, seed, count, length).unwrap();
        let mut draw = Draw::new(seed);
        for passage in alternation.passages() {
            let (a, b) = (draw.below(classes), draw.below(classes));
            assert!(
                passage
                    .iter()
                    .enumerate()
                    .all(|(t, &x)| x == if t % 2 == 0 { a } else { b })
            );
        }
        let mut draw = Draw::new(seed);
        for passage in line.passages() {
            let (start, step) = (draw.below(classes), draw.below(classes));
            assert!(
                passage
                    .iter()
                    .enumerate()
                    .all(|(t, &x)| x == (start + step * t) % classes)
            );
        }
        assert_eq!(line.classes(), classes);
        assert!(KnownTruth::cyclic(CyclicLaw::Line, 0, seed, 1, 8).is_err());
        assert!(KnownTruth::cyclic(CyclicLaw::OrderTwo { opening: 1 }, 4, seed, 1, 8).is_err());
        assert!(KnownTruth::cyclic(CyclicLaw::OrderTwo { opening: 9 }, 4, seed, 1, 8).is_err());
    }
}
