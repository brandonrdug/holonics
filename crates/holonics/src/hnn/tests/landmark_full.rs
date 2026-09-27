//! **Decision 28's tree of one node a depth, the tests' independent reference** (Lean
//! `HNN/LandmarkTree.{stopWeight, landmark_step}`): the ideal tree weighting in ℚ with every node of
//! an opened path founded at its first arrival, one node a depth, at its depth's
//! `β₀ = 2^(j_d) − 1`. The library stores the tree at the faces where paths part (Decision 37,
//! `hnn::landmark`), whose code is this tree's exactly in ℚ
//! (`HNN/LandmarkCompaction.compacted_is_decision_28`); the retired realization of this arena
//! (`Storage::Full`) is at commit `89460425`. Its nodes are keyed by their tree and the address
//! prefix that reaches them, so it shares no topology with the owner it checks.
//!
//! - a path: the founded nodes at the prefixes `a_1 … a_d`, `d = 0, …, D`; a leaf at `D` reads its
//!   KT face `k`, the first unfounded depth the prior `½`, a forced depth its child, and a mixing
//!   depth `(β k + q')/(1 + β)`;
//! - an enlarged tree joins its two branches at each dyadic cell, `(β_h q_cells + q_bundles)/(1 + β_h)`;
//! - a deposit steps each mixing depth `β' = β k(b)/q'(b)` and the join
//!   `β'_h = β_h q_cells(b)/q_bundles(b)`, founds the path's missing depths, then counts the digit
//!   at every depth past the forced ones.

use std::collections::HashMap;

use num_bigint::BigInt;
use num_traits::One;

use crate::hnn::landmark::{LandmarkDeclaration, Letter, odometer_digits};
use crate::ratio::{Rat, rat};

/// One founded node: its two counts and its `β`.
#[derive(Clone, Debug)]
struct Node {
    counts: [i64; 2],
    beta: Rat,
}

/// One branch's read of one digit: its founded nodes' keys and its faces of the digit's symbol,
/// `faces[top]` the leaf's or the prior's.
struct Read {
    keys: Vec<(usize, Vec<u32>)>,
    faces: Vec<Rat>,
}

/// **Decision 28's full tree in ℚ** (module header).
pub(super) struct FullTree {
    declaration: LandmarkDeclaration,
    digits: u64,
    nodes: HashMap<(usize, Vec<u32>), Node>,
    joins: Vec<Rat>,
}

impl FullTree {
    /// Decision 28's tree of a declaration, empty.
    pub(super) fn new(declaration: LandmarkDeclaration) -> Self {
        let digits = odometer_digits(declaration.alphabet);
        let joins = vec![Rat::one(); 1usize << digits];
        Self {
            declaration,
            digits,
            nodes: HashMap::new(),
            joins,
        }
    }

    /// The founded nodes, one a depth of every opened path.
    pub(super) fn nodes(&self) -> usize {
        self.nodes.len()
    }

    fn forced(&self, branch: usize) -> usize {
        if branch == 0 {
            self.declaration.forced
        } else {
            0
        }
    }

    fn kt(node: &Node, symbol: usize) -> Rat {
        rat(
            2 * node.counts[symbol] + 1,
            2 * (node.counts[0] + node.counts[1]) + 2,
        )
    }

    fn read(&self, branch: usize, dyadic: usize, symbol: usize, letters: &[u32]) -> Read {
        let tree = branch * (1usize << self.digits) + dyadic;
        let depth = letters.len();
        let keys: Vec<(usize, Vec<u32>)> = (0..=depth)
            .map(|d| (tree, letters[..d].to_vec()))
            .take_while(|key| self.nodes.contains_key(key))
            .collect();
        let top = keys.len().min(depth);
        let mut faces = vec![rat(1, 2); top + 1];
        if keys.len() == depth + 1 {
            faces[top] = Self::kt(&self.nodes[&keys[depth]], symbol);
        }
        for d in (0..top).rev() {
            faces[d] = if d < self.forced(branch) {
                faces[d + 1].clone()
            } else {
                let node = &self.nodes[&keys[d]];
                (&node.beta * Self::kt(node, symbol) + &faces[d + 1]) / (Rat::one() + &node.beta)
            };
        }
        Read { keys, faces }
    }

    /// Each opened digit's dyadic cell, symbol, reads and joined face.
    fn digits(&self, address: &[Letter], class: usize) -> Vec<(usize, usize, Vec<Read>, Rat)> {
        let letters = self.declaration.letters(address);
        self.declaration
            .emitted(class)
            .into_iter()
            .map(|(dyadic, symbol)| {
                let reads: Vec<Read> = letters
                    .iter()
                    .enumerate()
                    .map(|(branch, flat)| self.read(branch, dyadic, symbol, flat))
                    .collect();
                let face = if reads.len() > 1 {
                    let beta = &self.joins[dyadic];
                    (beta * &reads[0].faces[0] + &reads[1].faces[0]) / (Rat::one() + beta)
                } else {
                    reads[0].faces[0].clone()
                };
                (dyadic, symbol, reads, face)
            })
            .collect()
    }

    /// **The face of one class** at an address, exact.
    pub(super) fn probability(&self, address: &[Letter], class: usize) -> Rat {
        self.digits(address, class)
            .into_iter()
            .map(|(.., face)| face)
            .product()
    }

    /// **Receive one cell**: its face at the current standing, then its deposit.
    pub(super) fn receive(&mut self, address: &[Letter], class: usize) -> Rat {
        let digits = self.digits(address, class);
        let letters = self.declaration.letters(address);
        let depths = self.declaration.branch_depths();
        let face = digits.iter().map(|(.., face)| face.clone()).product();
        for (dyadic, symbol, reads, _) in digits {
            if reads.len() > 1 {
                self.joins[dyadic] =
                    &self.joins[dyadic] * &reads[0].faces[0] / &reads[1].faces[0];
            }
            for (branch, read) in reads.into_iter().enumerate() {
                let forced = self.forced(branch);
                let top = read.faces.len() - 1;
                for d in forced..read.keys.len().min(top) {
                    let node = self.nodes.get_mut(&read.keys[d]).expect("a founded node");
                    node.beta = &node.beta * Self::kt(node, symbol) / &read.faces[d + 1];
                }
                let tree = branch * (1usize << self.digits) + dyadic;
                for d in read.keys.len()..=depths[branch] {
                    let founding = self.declaration.prior.founding(d);
                    self.nodes.insert(
                        (tree, letters[branch][..d].to_vec()),
                        Node {
                            counts: [0, 0],
                            beta: Rat::from_integer(BigInt::from(founding)),
                        },
                    );
                }
                for d in forced..=depths[branch] {
                    let key = (tree, letters[branch][..d].to_vec());
                    self.nodes.get_mut(&key).expect("a path node").counts[symbol] += 1;
                }
            }
        }
        face
    }
}
