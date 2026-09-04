//! Receiver-local sections, overlap transport, and bounded assembly.
//!
//! An assembled region is a compatible family of local sections over a named
//! boundary. It is never a scene standing outside its receiver fibers.

use std::collections::{BTreeMap, BTreeSet};

use relational_geometry::ReceiverId;
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct RegionId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound(
    serialize = "K: Ord + Serialize, V: Serialize",
    deserialize = "K: Ord + Deserialize<'de>, V: Deserialize<'de>"
))]
pub struct LocalSection<K, V> {
    pub region: RegionId,
    pub values: BTreeMap<K, V>,
}

impl<K: Ord + Clone, V: Clone> LocalSection<K, V> {
    pub fn restrict(
        &self,
        region: RegionId,
        addresses: impl IntoIterator<Item = K>,
    ) -> Result<Self, AtlasError<K>> {
        let mut values = BTreeMap::new();
        for address in addresses {
            let value = self
                .values
                .get(&address)
                .ok_or_else(|| AtlasError::MissingAddress {
                    region: self.region,
                    address: address.clone(),
                })?;
            values.insert(address, value.clone());
        }
        Ok(Self { region, values })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound(
    serialize = "K: Ord + Serialize, V: Serialize",
    deserialize = "K: Ord + Deserialize<'de>, V: Deserialize<'de>"
))]
pub struct ReceiverFiber<K, V> {
    pub receiver: ReceiverId,
    pub section: LocalSection<K, V>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SectionMember {
    pub receiver: ReceiverId,
    pub region: RegionId,
}

impl<K, V> From<&ReceiverFiber<K, V>> for SectionMember {
    fn from(fiber: &ReceiverFiber<K, V>) -> Self {
        Self {
            receiver: fiber.receiver,
            region: fiber.section.region,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OverlapCorrespondence<K> {
    pub name: String,
    pub left: SectionMember,
    pub right: SectionMember,
    pub pairs: Vec<(K, K)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportedAgreement<K, V> {
    pub left: SectionMember,
    pub right: SectionMember,
    pub left_address: K,
    pub right_address: K,
    pub common_face: V,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrientedResidual<K, V> {
    pub left: SectionMember,
    pub right: SectionMember,
    pub left_address: K,
    pub right_address: K,
    pub left_face: V,
    pub right_face: V,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddressHolonomy<K> {
    pub member: SectionMember,
    /// One overlap component returned to these distinct local addresses.
    pub addresses: Vec<K>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SectionResidual<K, V> {
    Face(OrientedResidual<K, V>),
    AddressHolonomy(AddressHolonomy<K>),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundedAssembly<K, V> {
    pub schema: String,
    pub boundary_name: String,
    pub members: Vec<SectionMember>,
    pub agreements: Vec<TransportedAgreement<K, V>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GluingObstruction<K, V> {
    pub schema: String,
    pub boundary_name: String,
    pub members: Vec<SectionMember>,
    pub agreements: Vec<TransportedAgreement<K, V>>,
    pub residuals: Vec<SectionResidual<K, V>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GluingOutcome<K, V> {
    Assembled(BoundedAssembly<K, V>),
    Obstructed(GluingObstruction<K, V>),
}

impl<K, V> GluingOutcome<K, V> {
    pub fn is_assembled(&self) -> bool {
        matches!(self, Self::Assembled(_))
    }

    pub fn is_obstructed(&self) -> bool {
        matches!(self, Self::Obstructed(_))
    }
}

/// Assemble one finite cover of discrete local sections only after every
/// overlap member has been transported into the declared common face and
/// every overlap cycle returns to the same local address.
pub fn assemble_cover<K, V, W>(
    boundary_name: impl Into<String>,
    fibers: &[ReceiverFiber<K, V>],
    overlaps: &[OverlapCorrespondence<K>],
    transport: impl Fn(SectionMember, &V) -> W,
) -> Result<GluingOutcome<K, W>, AtlasError<K>>
where
    K: Ord + Clone,
    W: Clone + Eq,
{
    if fibers.is_empty() {
        return Err(AtlasError::EmptyCover);
    }
    let boundary_name = boundary_name.into();
    let members = fibers.iter().map(SectionMember::from).collect::<Vec<_>>();
    let mut indexed = BTreeMap::new();
    for fiber in fibers {
        let member = SectionMember::from(fiber);
        if indexed.insert(member, fiber).is_some() {
            return Err(AtlasError::DuplicateMember(member));
        }
    }
    let mut adjacency = members
        .iter()
        .copied()
        .map(|member| (member, Vec::new()))
        .collect::<BTreeMap<_, Vec<SectionMember>>>();
    let mut address_graph = BTreeMap::<(SectionMember, K), Vec<(SectionMember, K)>>::new();
    let mut agreements = Vec::new();
    let mut residuals = Vec::new();
    for overlap in overlaps {
        if overlap.pairs.is_empty() {
            return Err(AtlasError::EmptyOverlap(overlap.name.clone()));
        }
        let left = indexed
            .get(&overlap.left)
            .ok_or(AtlasError::MissingMember(overlap.left))?;
        let right = indexed
            .get(&overlap.right)
            .ok_or(AtlasError::MissingMember(overlap.right))?;
        adjacency
            .get_mut(&overlap.left)
            .expect("overlap member presence was checked")
            .push(overlap.right);
        adjacency
            .get_mut(&overlap.right)
            .expect("overlap member presence was checked")
            .push(overlap.left);
        for (left_address, right_address) in &overlap.pairs {
            let left_node = (overlap.left, left_address.clone());
            let right_node = (overlap.right, right_address.clone());
            address_graph
                .entry(left_node.clone())
                .or_default()
                .push(right_node.clone());
            address_graph.entry(right_node).or_default().push(left_node);
            let left_value = left.section.values.get(left_address).ok_or_else(|| {
                AtlasError::MissingAddress {
                    region: left.section.region,
                    address: left_address.clone(),
                }
            })?;
            let right_value = right.section.values.get(right_address).ok_or_else(|| {
                AtlasError::MissingAddress {
                    region: right.section.region,
                    address: right_address.clone(),
                }
            })?;
            let left_face = transport(overlap.left, left_value);
            let right_face = transport(overlap.right, right_value);
            if left_face == right_face {
                agreements.push(TransportedAgreement {
                    left: overlap.left,
                    right: overlap.right,
                    left_address: left_address.clone(),
                    right_address: right_address.clone(),
                    common_face: left_face,
                });
            } else {
                residuals.push(SectionResidual::Face(OrientedResidual {
                    left: overlap.left,
                    right: overlap.right,
                    left_address: left_address.clone(),
                    right_address: right_address.clone(),
                    left_face,
                    right_face,
                }));
            }
        }
    }
    let mut visited = BTreeMap::from([(members[0], ())]);
    let mut frontier = vec![members[0]];
    while let Some(member) = frontier.pop() {
        for neighbor in &adjacency[&member] {
            if visited.insert(*neighbor, ()).is_none() {
                frontier.push(*neighbor);
            }
        }
    }
    if visited.len() != members.len() {
        return Err(AtlasError::DisconnectedCover);
    }
    let mut visited_addresses = BTreeSet::new();
    for seed in address_graph.keys() {
        if visited_addresses.contains(seed) {
            continue;
        }
        let mut component = BTreeMap::<SectionMember, BTreeSet<K>>::new();
        let mut address_frontier = vec![seed.clone()];
        while let Some(node) = address_frontier.pop() {
            if !visited_addresses.insert(node.clone()) {
                continue;
            }
            component.entry(node.0).or_default().insert(node.1.clone());
            for neighbor in &address_graph[&node] {
                if !visited_addresses.contains(neighbor) {
                    address_frontier.push(neighbor.clone());
                }
            }
        }
        for (member, addresses) in component {
            if addresses.len() > 1 {
                residuals.push(SectionResidual::AddressHolonomy(AddressHolonomy {
                    member,
                    addresses: addresses.into_iter().collect(),
                }));
            }
        }
    }
    if residuals.is_empty() {
        Ok(GluingOutcome::Assembled(BoundedAssembly {
            schema: "holonic-engine.bounded-assembly.v1".to_owned(),
            boundary_name,
            members,
            agreements,
        }))
    } else {
        Ok(GluingOutcome::Obstructed(GluingObstruction {
            schema: "holonic-engine.gluing-obstruction.v1".to_owned(),
            boundary_name,
            members,
            agreements,
            residuals,
        }))
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum AtlasError<K> {
    #[error("region {region:?} has no value at the requested local address")]
    MissingAddress { region: RegionId, address: K },
    #[error("a bounded assembly requires at least one local section")]
    EmptyCover,
    #[error("the local-section member {0:?} occurs more than once")]
    DuplicateMember(SectionMember),
    #[error("an overlap names absent local-section member {0:?}")]
    MissingMember(SectionMember),
    #[error("the declared overlap {0} contains no address correspondence")]
    EmptyOverlap(String),
    #[error("the declared local sections do not form one connected cover")]
    DisconnectedCover,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compatibility_assembles_and_difference_returns_an_oriented_residual() {
        let left = ReceiverFiber {
            receiver: ReceiverId(1),
            section: LocalSection {
                region: RegionId(1),
                values: BTreeMap::from([(0_u8, 3_i64), (1, 5)]),
            },
        };
        let right = ReceiverFiber {
            receiver: ReceiverId(2),
            section: LocalSection {
                region: RegionId(2),
                values: BTreeMap::from([(8_u8, 3_i64), (9, 7)]),
            },
        };
        let left_member = SectionMember::from(&left);
        let right_member = SectionMember::from(&right);
        let compatible = assemble_cover(
            "one covered point",
            &[left.clone(), right.clone()],
            &[OverlapCorrespondence {
                name: "compatible".to_owned(),
                left: left_member,
                right: right_member,
                pairs: vec![(0, 8)],
            }],
            |_member, value| *value,
        )
        .unwrap();
        assert!(compatible.is_assembled());

        let obstructed = assemble_cover(
            "one covered point",
            &[left, right],
            &[OverlapCorrespondence {
                name: "incompatible".to_owned(),
                left: left_member,
                right: right_member,
                pairs: vec![(1, 9)],
            }],
            |_member, value| *value,
        )
        .unwrap();
        assert!(obstructed.is_obstructed());
    }

    #[test]
    fn pairwise_equal_faces_can_still_carry_nontrivial_cycle_holonomy() {
        let first = ReceiverFiber {
            receiver: ReceiverId(1),
            section: LocalSection {
                region: RegionId(1),
                values: BTreeMap::from([(0_u8, 3_i64), (1, 3)]),
            },
        };
        let second = ReceiverFiber {
            receiver: ReceiverId(2),
            section: LocalSection {
                region: RegionId(2),
                values: BTreeMap::from([(8_u8, 3_i64)]),
            },
        };
        let third = ReceiverFiber {
            receiver: ReceiverId(3),
            section: LocalSection {
                region: RegionId(3),
                values: BTreeMap::from([(4_u8, 3_i64)]),
            },
        };
        let first_member = SectionMember::from(&first);
        let second_member = SectionMember::from(&second);
        let third_member = SectionMember::from(&third);
        let outcome = assemble_cover(
            "three-member cycle",
            &[first, second, third],
            &[
                OverlapCorrespondence {
                    name: "first-second".to_owned(),
                    left: first_member,
                    right: second_member,
                    pairs: vec![(0, 8)],
                },
                OverlapCorrespondence {
                    name: "second-third".to_owned(),
                    left: second_member,
                    right: third_member,
                    pairs: vec![(8, 4)],
                },
                OverlapCorrespondence {
                    name: "third-first return".to_owned(),
                    left: third_member,
                    right: first_member,
                    pairs: vec![(4, 1)],
                },
            ],
            |_member, value| *value,
        )
        .unwrap();
        let GluingOutcome::Obstructed(obstruction) = outcome else {
            panic!("the nontrivial return must not assemble");
        };
        assert!(obstruction.residuals.iter().any(|residual| matches!(
            residual,
            SectionResidual::AddressHolonomy(AddressHolonomy { member, .. })
                if *member == first_member
        )));
    }
}
