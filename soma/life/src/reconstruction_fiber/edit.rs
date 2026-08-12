//! The exact local re-expression face carried beside a ReconstructionFiber.
//!
//! The minimum grade never governs candidate admission. The returned DAG factorizes every minimal
//! route under this declared Unicode-scalar operation family.

use std::collections::BTreeSet;

use num_bigint::BigUint;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EditNode {
    /// Prefix length in the candidate surface.
    pub candidate_prefix: usize,
    /// Prefix length in the observed surface.
    pub observed_prefix: usize,
}

/// One primitive re-expression edge. These are presentation operations, not semantic relations.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EditOperation {
    Retain(char),
    Insert { observed: char },
    Delete { candidate: char },
    Substitute { candidate: char, observed: char },
    AdjacentTranspose { left: char, right: char },
    CaseRebase { candidate: char, observed: char },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EditEdge {
    pub from: EditNode,
    pub to: EditNode,
    pub operation: EditOperation,
}

/// Every minimal local path, factorized as one DAG. `minimum_operations` is a face of this complex
/// and is never consulted by reconstruction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EditComplex {
    pub candidate: String,
    pub observed: String,
    pub minimum_operations: usize,
    pub minimal_path_count: BigUint,
    pub nodes: BTreeSet<EditNode>,
    pub edges: BTreeSet<EditEdge>,
}

/// Build the complete minimal-path DAG under this module's declared local operation family.
pub fn edit_complex(candidate: &str, observed: &str) -> EditComplex {
    let candidate_chars = candidate.chars().collect::<Vec<_>>();
    let observed_chars = observed.chars().collect::<Vec<_>>();
    let rows = candidate_chars.len() + 1;
    let columns = observed_chars.len() + 1;
    let mut distance = vec![vec![usize::MAX; columns]; rows];
    let mut ways = vec![vec![BigUint::from(0u8); columns]; rows];
    let mut predecessors = vec![vec![Vec::<(usize, usize, EditOperation)>::new(); columns]; rows];
    distance[0][0] = 0;
    ways[0][0] = BigUint::from(1u8);

    for i in 0..rows {
        for j in 0..columns {
            if i == 0 && j == 0 {
                continue;
            }
            let mut alternatives = Vec::new();
            if i > 0 {
                alternatives.push((
                    distance[i - 1][j] + 1,
                    i - 1,
                    j,
                    EditOperation::Delete {
                        candidate: candidate_chars[i - 1],
                    },
                ));
            }
            if j > 0 {
                alternatives.push((
                    distance[i][j - 1] + 1,
                    i,
                    j - 1,
                    EditOperation::Insert {
                        observed: observed_chars[j - 1],
                    },
                ));
            }
            if i > 0 && j > 0 {
                let from = candidate_chars[i - 1];
                let to = observed_chars[j - 1];
                let (cost, operation) = if from == to {
                    (0, EditOperation::Retain(from))
                } else if case_equivalent(from, to) {
                    (
                        1,
                        EditOperation::CaseRebase {
                            candidate: from,
                            observed: to,
                        },
                    )
                } else {
                    (
                        1,
                        EditOperation::Substitute {
                            candidate: from,
                            observed: to,
                        },
                    )
                };
                alternatives.push((distance[i - 1][j - 1] + cost, i - 1, j - 1, operation));
            }
            if i > 1
                && j > 1
                && candidate_chars[i - 2] == observed_chars[j - 1]
                && candidate_chars[i - 1] == observed_chars[j - 2]
            {
                alternatives.push((
                    distance[i - 2][j - 2] + 1,
                    i - 2,
                    j - 2,
                    EditOperation::AdjacentTranspose {
                        left: candidate_chars[i - 2],
                        right: candidate_chars[i - 1],
                    },
                ));
            }
            let best = alternatives
                .iter()
                .map(|alternative| alternative.0)
                .min()
                .expect("every non-origin edit cell has a predecessor");
            distance[i][j] = best;
            for (cost, predecessor_i, predecessor_j, operation) in alternatives {
                if cost == best {
                    let inherited = ways[predecessor_i][predecessor_j].clone();
                    ways[i][j] += inherited;
                    predecessors[i][j].push((predecessor_i, predecessor_j, operation));
                }
            }
        }
    }

    let mut nodes = BTreeSet::new();
    let mut edges = BTreeSet::new();
    let mut frontier = vec![(candidate_chars.len(), observed_chars.len())];
    while let Some((i, j)) = frontier.pop() {
        if !nodes.insert(EditNode {
            candidate_prefix: i,
            observed_prefix: j,
        }) {
            continue;
        }
        for (predecessor_i, predecessor_j, operation) in &predecessors[i][j] {
            let from = EditNode {
                candidate_prefix: *predecessor_i,
                observed_prefix: *predecessor_j,
            };
            let to = EditNode {
                candidate_prefix: i,
                observed_prefix: j,
            };
            edges.insert(EditEdge {
                from,
                to,
                operation: operation.clone(),
            });
            frontier.push((*predecessor_i, *predecessor_j));
        }
    }

    EditComplex {
        candidate: candidate.to_owned(),
        observed: observed.to_owned(),
        minimum_operations: distance[candidate_chars.len()][observed_chars.len()],
        minimal_path_count: ways[candidate_chars.len()][observed_chars.len()].clone(),
        nodes,
        edges,
    }
}

fn case_equivalent(left: char, right: char) -> bool {
    left.to_lowercase().collect::<String>() == right.to_lowercase().collect::<String>()
}
