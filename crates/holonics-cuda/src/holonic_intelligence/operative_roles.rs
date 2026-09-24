//! The declared withdrawals at the role grain: SKE4's founding material for cones.
//!
//! A family declares the withdrawals it exposes its occurrences to.  Here the declaration is
//! derived from the ecology's own structure and nothing outside it, at a grain the family
//! declares: every contraction population a role (`Population`); the query population of a
//! contact one role per head (`Head`); or every block of contractions that flow into one
//! another through non-contraction operations within one layer without crossing a residual sum
//! one role (`LayerBlock`, the grain of the SKE4 deed; keys and values another layer reads belong
//! to the layer that computes them).  A role is a population of output sites of one
//! or more contraction populations; withdrawing it zeroes those contractions' outputs at those
//! sites at every position, the SKE2 intervention.  The tied population is the receiver's own
//! and is not a role.
//!
//! An order over the roles is declared from the excitation: the first-order contribution of a
//! role is the sum over its sites, and roles are ordered by their share of each exposure's
//! total, greatest share over the exposures first.  The order founds nothing; the withdrawals
//! do.  This owner is host arithmetic over the ecology and the contributions the card returned,
//! and the octet forms that carry them between bounded processes.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{BufReader, BufWriter, Read, Write},
    path::Path,
};

use serde::{Deserialize, Serialize};

use super::{
    NativeCarrierOrdinal, NativeFullOperatorEcology, NativeOperationPrimitive, NativeSiteBitmask,
    NativeSiteSelection, NativeTensorOrdinal,
};

/// One span of output sites of one contraction population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeRoleSpan {
    pub population: u32,
    pub operation: u32,
    pub first: usize,
    pub sites: usize,
}

/// One declared role: spans of output sites, all in one layer (or the prologue).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeRole {
    pub ordinal: u32,
    pub layer: Option<u16>,
    /// The head this role is, when the grain is `Head`; `None` otherwise.
    pub head: Option<usize>,
    pub members: Vec<NativeRoleSpan>,
}

impl NativeRole {
    pub fn sites(&self) -> usize {
        self.members.iter().map(|m| m.sites).sum()
    }
}

/// The grain the family declares its withdrawals at.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeRoleGrain {
    Population,
    Head,
    LayerBlock,
}

#[derive(Debug, thiserror::Error)]
pub enum NativeRoleError {
    #[error("I/O: {0}")]
    Io(String),
    #[error("the octets are malformed: {0}")]
    Malformed(String),
    #[error("population {0} is not a contraction population with a site count")]
    Population(u32),
    #[error("the exposures disagree on the roles")]
    Roles,
}

fn io(error: std::io::Error) -> NativeRoleError {
    NativeRoleError::Io(error.to_string())
}

/// The roles the ecology declares at a grain, in operation order; the tied population (the
/// receiver's own, the final contraction's) is excluded.
pub fn declared_roles(ecology: &NativeFullOperatorEcology, grain: NativeRoleGrain) -> Result<Vec<NativeRole>, NativeRoleError> {
    let operations = &ecology.operations;
    let terminal_start = operations.len().saturating_sub(5);
    let mut producer: BTreeMap<NativeCarrierOrdinal, usize> = BTreeMap::new();
    for (index, operation) in operations.iter().enumerate() {
        producer.insert(operation.output, index);
    }
    let site_count = |population: u32| -> Result<usize, NativeRoleError> {
        ecology
            .coefficient_populations
            .get(population as usize)
            .and_then(|descriptor| descriptor.shape.first().copied())
            .ok_or(NativeRoleError::Population(population))
    };
    // The body's contractions, in order, once per population.
    let mut contractions: Vec<(usize, u32)> = Vec::new();
    let mut seen: BTreeSet<u32> = BTreeSet::new();
    for (index, operation) in operations.iter().enumerate() {
        if index >= terminal_start || !matches!(operation.primitive, NativeOperationPrimitive::Contract) {
            continue;
        }
        if let Some(population) = operation.coefficients.first() {
            if seen.insert(population.0) {
                contractions.push((index, population.0));
            }
        }
    }
    let span_of = |index: usize, population: u32| -> Result<NativeRoleSpan, NativeRoleError> {
        Ok(NativeRoleSpan {
            population,
            operation: operations[index].ordinal,
            first: 0,
            sites: site_count(population)?,
        })
    };
    let mut roles = Vec::new();
    match grain {
        NativeRoleGrain::Population => {
            for (index, population) in contractions {
                roles.push(NativeRole {
                    ordinal: roles.len() as u32,
                    layer: operations[index].layer,
                    head: None,
                    members: vec![span_of(index, population)?],
                });
            }
        }
        NativeRoleGrain::Head => {
            // The query populations: the contraction whose output reaches a contact's first
            // input through non-contraction operations.
            let mut query_heads: BTreeMap<u32, (usize, usize)> = BTreeMap::new();
            for operation in operations {
                let NativeOperationPrimitive::CausalContact { heads, head_width, .. } = &operation.primitive else {
                    continue;
                };
                let mut cursor = operation.inputs.first().copied();
                for _ in 0..16 {
                    let Some(carrier) = cursor else { break };
                    let Some(index) = producer.get(&carrier).copied() else { break };
                    let source = &operations[index];
                    if matches!(source.primitive, NativeOperationPrimitive::Contract) {
                        if let Some(population) = source.coefficients.first() {
                            query_heads.insert(population.0, (*heads, *head_width));
                        }
                        break;
                    }
                    cursor = source.inputs.first().copied();
                }
            }
            for (index, population) in contractions {
                let sites = site_count(population)?;
                match query_heads.get(&population) {
                    Some((heads, head_width)) if heads * head_width == sites => {
                        for head in 0..*heads {
                            roles.push(NativeRole {
                                ordinal: roles.len() as u32,
                                layer: operations[index].layer,
                                head: Some(head),
                                members: vec![NativeRoleSpan {
                                    population,
                                    operation: operations[index].ordinal,
                                    first: head * head_width,
                                    sites: *head_width,
                                }],
                            });
                        }
                    }
                    _ => roles.push(NativeRole {
                        ordinal: roles.len() as u32,
                        layer: operations[index].layer,
                        head: None,
                        members: vec![span_of(index, population)?],
                    }),
                }
            }
        }
        NativeRoleGrain::LayerBlock => {
            // Union-find over contractions: a contraction's output flowing forward through
            // operations that are neither contractions nor residual sums to another contraction
            // joins their block.
            let by_index: BTreeMap<usize, usize> = contractions.iter().enumerate().map(|(at, (index, _))| (*index, at)).collect();
            let mut parent: Vec<usize> = (0..contractions.len()).collect();
            fn find(parent: &mut [usize], x: usize) -> usize {
                let mut root = x;
                while parent[root] != root {
                    root = parent[root];
                }
                let mut cursor = x;
                while parent[cursor] != root {
                    let next = parent[cursor];
                    parent[cursor] = root;
                    cursor = next;
                }
                root
            }
            // consumers of each carrier
            let mut consumers: BTreeMap<NativeCarrierOrdinal, Vec<usize>> = BTreeMap::new();
            for (index, operation) in operations.iter().enumerate() {
                for input in &operation.inputs {
                    consumers.entry(*input).or_default().push(index);
                }
            }
            for (at, (index, _)) in contractions.iter().enumerate() {
                // forward flood from this contraction's output
                let mut stack = vec![operations[*index].output];
                let mut visited: BTreeSet<usize> = BTreeSet::new();
                while let Some(carrier) = stack.pop() {
                    for consumer in consumers.get(&carrier).cloned().unwrap_or_default() {
                        if consumer >= terminal_start || !visited.insert(consumer) {
                            continue;
                        }
                        let operation = &operations[consumer];
                        match operation.primitive {
                            NativeOperationPrimitive::Contract => {
                                // Blocks stay within one layer: a contraction another layer
                                // reads (shared keys and values) belongs to the layer that
                                // computes it, and the sharing stays in the ecology.
                                if let Some(other) = by_index.get(&consumer) {
                                    if operations[*index].layer == operation.layer {
                                        let a = find(&mut parent, at);
                                        let b = find(&mut parent, *other);
                                        parent[a.max(b)] = a.min(b);
                                    }
                                }
                            }
                            NativeOperationPrimitive::Add => {}
                            _ => stack.push(operation.output),
                        }
                    }
                }
            }
            let mut blocks: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
            for at in 0..contractions.len() {
                let root = find(&mut parent, at);
                blocks.entry(root).or_default().push(at);
            }
            for (_, members) in blocks {
                let first = contractions[members[0]].0;
                roles.push(NativeRole {
                    ordinal: roles.len() as u32,
                    layer: operations[first].layer,
                    head: None,
                    members: members
                        .iter()
                        .map(|at| span_of(contractions[*at].0, contractions[*at].1))
                        .collect::<Result<Vec<_>, _>>()?,
                });
            }
        }
    }
    Ok(roles)
}

/// The site count of every population the roles cover.
pub fn role_sizes(roles: &[NativeRole]) -> BTreeMap<NativeTensorOrdinal, usize> {
    let mut sizes = BTreeMap::new();
    for role in roles {
        for member in &role.members {
            let entry = sizes.entry(NativeTensorOrdinal(member.population)).or_insert(0usize);
            *entry = (*entry).max(member.first + member.sites);
        }
    }
    sizes
}

/// The selection withdrawing exactly the given roles.
pub fn selection_of_roles(roles: &[NativeRole], sizes: &BTreeMap<NativeTensorOrdinal, usize>, which: impl Iterator<Item = u32>) -> NativeSiteSelection {
    let mut selection = NativeSiteSelection::founded(sizes);
    for ordinal in which {
        if let Some(role) = roles.get(ordinal as usize) {
            for member in &role.members {
                for site in member.first..member.first + member.sites {
                    selection.withdraw(NativeTensorOrdinal(member.population), site);
                }
            }
        }
    }
    selection
}

/// The given roles as a cone per population, a bitmask over its sites.
pub fn cone_of_roles(roles: &[NativeRole], sizes: &BTreeMap<NativeTensorOrdinal, usize>, which: impl Iterator<Item = u32>) -> BTreeMap<u32, NativeSiteBitmask> {
    let selection = selection_of_roles(roles, sizes, which);
    sizes
        .iter()
        .map(|(population, count)| {
            let sites = selection
                .withdrawn_of(*population)
                .map(<[bool]>::to_vec)
                .unwrap_or_else(|| vec![false; *count]);
            (population.0, NativeSiteBitmask::from_sites(&sites))
        })
        .collect()
}

/// The first-order contributions of one exposure per site of every contraction population.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeSiteContributions {
    pub populations: Vec<(u32, Vec<u128>)>,
}

impl NativeSiteContributions {
    pub fn from_map(contributions: &BTreeMap<NativeTensorOrdinal, Vec<u128>>) -> Self {
        Self {
            populations: contributions
                .iter()
                .map(|(population, sites)| (population.0, sites.clone()))
                .collect(),
        }
    }

    pub fn sizes(&self) -> BTreeMap<NativeTensorOrdinal, usize> {
        self.populations
            .iter()
            .map(|(population, sites)| (NativeTensorOrdinal(*population), sites.len()))
            .collect()
    }

    /// The contribution of every role: the sum over its sites.
    pub fn per_role(&self, roles: &[NativeRole]) -> Result<Vec<u128>, NativeRoleError> {
        let by_population: BTreeMap<u32, &Vec<u128>> = self
            .populations
            .iter()
            .map(|(population, sites)| (*population, sites))
            .collect();
        roles
            .iter()
            .map(|role| {
                let mut sum = 0u128;
                for member in &role.members {
                    let sites = by_population
                        .get(&member.population)
                        .ok_or(NativeRoleError::Population(member.population))?;
                    let span = sites
                        .get(member.first..member.first + member.sites)
                        .ok_or(NativeRoleError::Population(member.population))?;
                    sum = span.iter().fold(sum, |acc, c| acc.saturating_add(*c));
                }
                Ok(sum)
            })
            .collect()
    }

    pub fn write(&self, path: &Path) -> Result<(), NativeRoleError> {
        let mut out = BufWriter::new(File::create(path).map_err(io)?);
        out.write_all(&(self.populations.len() as u64).to_le_bytes()).map_err(io)?;
        for (population, sites) in &self.populations {
            out.write_all(&population.to_le_bytes()).map_err(io)?;
            out.write_all(&(sites.len() as u64).to_le_bytes()).map_err(io)?;
            for site in sites {
                out.write_all(&site.to_le_bytes()).map_err(io)?;
            }
        }
        out.flush().map_err(io)
    }

    pub fn read(path: &Path) -> Result<Self, NativeRoleError> {
        let mut input = BufReader::with_capacity(1 << 20, File::open(path).map_err(io)?);
        let mut word8 = [0u8; 8];
        let mut word4 = [0u8; 4];
        let mut word16 = [0u8; 16];
        input.read_exact(&mut word8).map_err(io)?;
        let count = u64::from_le_bytes(word8) as usize;
        let mut populations = Vec::with_capacity(count);
        for _ in 0..count {
            input.read_exact(&mut word4).map_err(io)?;
            let population = u32::from_le_bytes(word4);
            input.read_exact(&mut word8).map_err(io)?;
            let sites = u64::from_le_bytes(word8) as usize;
            if sites > 1 << 26 {
                return Err(NativeRoleError::Malformed("site count".to_owned()));
            }
            let mut contributions = Vec::with_capacity(sites);
            for _ in 0..sites {
                input.read_exact(&mut word16).map_err(io)?;
                contributions.push(u128::from_le_bytes(word16));
            }
            populations.push((population, contributions));
        }
        Ok(Self { populations })
    }
}

/// The share of one exposure's total contribution each role carries, as a fixed-point fraction
/// with 64 fractional bits; the frame that lets exposures of different magnitude be compared.
pub fn role_shares(per_role: &[u128]) -> Vec<u128> {
    let total: u128 = per_role.iter().fold(0u128, |sum, c| sum.saturating_add(*c));
    if total == 0 {
        return vec![0; per_role.len()];
    }
    // Bring the total under 2^63 so `c << 64` fits: the same shift on every contribution keeps
    // the ratios, to within the last bit, which orders nothing here.
    let shift = (128 - total.leading_zeros()).saturating_sub(63);
    let total = (total >> shift).max(1);
    per_role
        .iter()
        .map(|c| ((c >> shift) << 64) / total)
        .collect()
}

/// A declared order over the roles: the roles in descending greatest share over the exposures,
/// ties by role ordinal.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeRoleOrder {
    pub roles: Vec<NativeRole>,
    /// Role ordinals, most excited first.
    pub order: Vec<u32>,
    /// The greatest share (64 fractional bits) each role had over the exposures, in `order`.
    pub greatest_share: Vec<u128>,
}

impl NativeRoleOrder {
    pub fn found(roles: &[NativeRole], exposures: &[Vec<u128>]) -> Result<Self, NativeRoleError> {
        if exposures.iter().any(|shares| shares.len() != roles.len()) {
            return Err(NativeRoleError::Roles);
        }
        let mut greatest = vec![0u128; roles.len()];
        for shares in exposures {
            for (role, share) in shares.iter().enumerate() {
                greatest[role] = greatest[role].max(*share);
            }
        }
        let mut order: Vec<u32> = (0..roles.len() as u32).collect();
        order.sort_by(|a, b| greatest[*b as usize].cmp(&greatest[*a as usize]).then(a.cmp(b)));
        let greatest_share = order.iter().map(|role| greatest[*role as usize]).collect();
        Ok(Self {
            roles: roles.to_vec(),
            order,
            greatest_share,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn role(ordinal: u32, first: usize) -> NativeRole {
        NativeRole {
            ordinal,
            layer: None,
            head: None,
            members: vec![NativeRoleSpan {
                population: 0,
                operation: 0,
                first,
                sites: 2,
            }],
        }
    }

    #[test]
    fn shares_sum_to_one_within_the_frame() {
        let shares = role_shares(&[1, 1, 2]);
        let total: u128 = shares.iter().sum();
        assert!(total <= 1u128 << 64 && total >= (1u128 << 64) - 3);
        assert_eq!(shares[2], shares[0] * 2);
    }

    #[test]
    fn the_order_is_by_greatest_share_then_ordinal_and_roles_select_their_sites() {
        let roles: Vec<NativeRole> = (0..3).map(|o| role(o, o as usize * 2)).collect();
        let order = NativeRoleOrder::found(&roles, &[vec![1, 5, 5], vec![9, 0, 0]]).unwrap();
        assert_eq!(order.order, vec![0, 1, 2]);
        let sizes = role_sizes(&roles);
        assert_eq!(sizes[&NativeTensorOrdinal(0)], 6);
        assert_eq!(selection_of_roles(&roles, &sizes, [1u32, 2].into_iter()).withdrawn_population(), 4);
        let cone = cone_of_roles(&roles, &sizes, [0u32].into_iter());
        assert_eq!(cone[&0].population(), 2);
    }
}
