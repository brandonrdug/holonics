//! How far a local agreement spreads by contact, and what stops it.
//!
//! Brandon: *"localized truth is real, and that is the entire point of communication and adaptation
//! within ecosystems"*; *"information transport is the main job, which is why **local navigation and
//! transport (communication)** is key"*; *"Is it more likely that the Riemann Hypothesis is trivially
//! provable on a local scale that can then grow? In the same way we are attempting to localize and
//! grow P=NP?"*
//!
//! And the form of a proof, from day one: *"You cannot prove that you own two sheep to an external
//! observer unless you have them count your two sheep, or unless you show them analogous logic about
//! the nature of owning two sheep."* No absolute frame — a transport between two receivers who share
//! an overlap.
//!
//! `gluing` decides that for **two** receivers. This iterates it along contact. A receiver reaches
//! its neighbour when their sections overlap and nothing obstructs on the overlap; the neighbourhood
//! grows hop by hop; and the **degrees of separation at which growth stops, together with the
//! obstruction that stopped it, is the return.** There is no global controller and no global
//! section is ever assembled — only neighbours, which is how a flock navigates.
//!
//! ## What the two failure modes mean, and why they are different
//!
//! ```text
//!   no overlap       -> no contact. Not a disagreement. Nothing to communicate through.
//!   overlap, delta=0 -> the local truths agree and the frontier advances.
//!   overlap, delta≠0 -> a real obstruction. Growth stops HERE and the obstruction is retained.
//! ```
//!
//! Collapsing the first two would make silence look like assent; collapsing the last two would make
//! disagreement look like distance. Both are recorded separately.
//!
//! ## The measurement this exists for
//!
//! A local truth that cannot glue globally still glues on its own neighbourhood. That is not a
//! weaker result — it is the whole claim. The reach is the size of the region over which a claim
//! holds without any appeal outside it, and the obstruction at the frontier is where the next
//! founding is owed.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};

use crate::algebraic::{CausalCellId, GradedCausalComplex};
use crate::gluing::{Cover, GluingRefusal, read_cover};
use crate::rebase_invariants::PivotRule;

/// One receiver's section. Communication happens only where sections meet.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Neighbourhood {
    pub sections: Vec<BTreeSet<CausalCellId>>,
}

impl Neighbourhood {
    pub fn extent(&self) -> usize {
        self.sections.len()
    }
}

/// Why growth stopped at a particular contact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Frontier {
    pub from: usize,
    pub to: usize,
    /// The overlap they share. Non-empty by construction — no contact is not a frontier.
    pub overlap_extent: usize,
    /// Per grade, the rank of the connecting map. Nonzero somewhere, or this would not be a
    /// frontier at all.
    pub obstruction: Vec<i64>,
}

/// How far a local agreement spread from one origin.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Spread {
    pub schema: String,
    pub origin: usize,
    /// Receiver -> degrees of separation from the origin, for every receiver the agreement reached.
    pub degrees: BTreeMap<usize, usize>,
    /// Contacts where the sections meet and the local truths do not agree.
    pub frontier: Vec<Frontier>,
    /// Receivers that share no contact path at all. Silence, not disagreement.
    pub out_of_contact: Vec<usize>,
}

impl Spread {
    /// How many receivers the local truth reached, the origin included.
    pub fn reach(&self) -> usize {
        self.degrees.len()
    }

    /// The greatest degrees of separation the agreement survived.
    pub fn radius(&self) -> usize {
        self.degrees.values().copied().max().unwrap_or(0)
    }

    /// The agreement reached every receiver that is in contact at all. Note this is **not** a claim
    /// that a global section exists — only that nothing obstructed along the way.
    pub fn unobstructed(&self) -> bool {
        self.frontier.is_empty()
    }
}

/// Grow a local agreement outward from one receiver by contact alone.
///
/// Breadth-first over contacts, so `degrees` really is degrees of separation and not the length of
/// whatever path the walk happened to take. A neighbour is admitted when the sections overlap and
/// `gluing` returns no obstruction on that pair; when they overlap and it does obstruct, the contact
/// becomes a frontier and the walk does not cross it.
pub fn spread(
    complex: &GradedCausalComplex,
    neighbourhood: &Neighbourhood,
    origin: usize,
    rule: PivotRule,
) -> Result<Spread, GluingRefusal> {
    let extent = neighbourhood.extent();
    let mut degrees = BTreeMap::from([(origin, 0usize)]);
    let mut frontier = Vec::new();
    let mut pending = VecDeque::from([origin]);

    while let Some(here) = pending.pop_front() {
        let step = degrees[&here];
        for there in 0..extent {
            if there == here || degrees.contains_key(&there) {
                continue;
            }
            let cover = Cover {
                left: neighbourhood.sections[here].clone(),
                right: neighbourhood.sections[there].clone(),
            };
            let overlap = cover.overlap();
            if overlap.is_empty() {
                // No contact. Silence is not assent and it is not disagreement either.
                continue;
            }
            let reading = read_cover(complex, &cover, rule)?;
            if reading.exhibits_obstruction() {
                frontier.push(Frontier {
                    from: here,
                    to: there,
                    overlap_extent: overlap.len(),
                    obstruction: reading.obstruction.clone(),
                });
                continue;
            }
            degrees.insert(there, step + 1);
            pending.push_back(there);
        }
    }

    // A receiver may appear on the frontier from one side and still be reached from another; only
    // those reached by nothing are genuinely out of contact.
    let out_of_contact: Vec<usize> = (0..extent)
        .filter(|receiver| !degrees.contains_key(receiver))
        .filter(|receiver| {
            !frontier
                .iter()
                .any(|contact| contact.to == *receiver || contact.from == *receiver)
        })
        .collect();

    let reached: BTreeSet<usize> = degrees.keys().copied().collect();
    frontier.retain(|contact| reached.contains(&contact.from) && !reached.contains(&contact.to));

    Ok(Spread {
        schema: "holonic-engine.communication.v1".to_owned(),
        origin,
        degrees,
        frontier,
        out_of_contact,
    })
}

/// Spread from every origin. The reach is a property of where you start, which is the point.
pub fn spread_from_each(
    complex: &GradedCausalComplex,
    neighbourhood: &Neighbourhood,
    rule: PivotRule,
) -> Result<Vec<Spread>, GluingRefusal> {
    (0..neighbourhood.extent())
        .map(|origin| spread(complex, neighbourhood, origin, rule))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebraic::{CausalChain, ComparativeMultiplicity};
    use crate::causal::EventId;

    fn source() -> BTreeSet<EventId> {
        BTreeSet::from([EventId(1)])
    }

    /// A path of `n` vertices with `n-1` edges, which is the simplest terrain where contact is
    /// genuinely local: a receiver holding one stretch meets only the stretches beside it.
    fn path(length: usize) -> (GradedCausalComplex, Vec<CausalCellId>, Vec<CausalCellId>) {
        let mut complex = GradedCausalComplex::default();
        let mut vertices = Vec::new();
        let mut edges = Vec::new();
        for index in 0..length {
            vertices.push(
                complex
                    .found_cell(format!("v{index}"), source(), 0, CausalChain::default())
                    .expect("a vertex has no boundary"),
            );
        }
        for index in 1..length {
            let mut boundary = CausalChain::default();
            boundary.add_term(vertices[index], ComparativeMultiplicity::positive(1u32));
            boundary.add_term(vertices[index - 1], ComparativeMultiplicity::negative(1u32));
            edges.push(
                complex
                    .found_cell(format!("e{index}"), source(), 1, boundary)
                    .expect("an edge closes"),
            );
        }
        (complex, vertices, edges)
    }

    /// Overlapping stretches along a path: receiver `k` holds vertices `k..k+width` and every edge
    /// between them. Consecutive receivers share a vertex, so contact is local and a receiver at one
    /// end reaches the other only by passing through everyone in between.
    fn stretches(
        complex: &GradedCausalComplex,
        vertices: &[CausalCellId],
        width: usize,
        count: usize,
    ) -> Neighbourhood {
        let sections = (0..count)
            .map(|start| {
                let held: BTreeSet<CausalCellId> = vertices
                    [start..(start + width).min(vertices.len())]
                    .iter()
                    .copied()
                    .collect();
                complex
                    .cells()
                    .values()
                    .filter(|cell| cell.grade > 0 && cell.boundary.support().is_subset(&held))
                    .map(|cell| cell.id)
                    .chain(held.iter().copied())
                    .collect()
            })
            .collect();
        Neighbourhood { sections }
    }

    #[test]
    fn agreement_spreads_by_contact_and_degrees_are_hop_counts() {
        let (complex, vertices, _) = path(8);
        let neighbourhood = stretches(&complex, &vertices, 3, 6);
        let reading = spread(&complex, &neighbourhood, 0, PivotRule::FirstNonzero).unwrap();

        assert_eq!(
            reading.reach(),
            6,
            "every stretch is reachable along the path"
        );
        assert!(reading.unobstructed());
        assert_eq!(reading.degrees[&0], 0);
        // Stretches 0..2 all share vertices with stretch 0, so they are one hop; further ones take
        // more. What matters is that the far end is NOT one hop.
        assert!(
            reading.degrees[&5] > 1,
            "the far stretch must be reached through the ones between it: {:?}",
            reading.degrees
        );
        assert_eq!(reading.radius(), *reading.degrees.values().max().unwrap());
    }

    /// Silence is not assent. A receiver holding a disjoint region is out of contact, and that is
    /// reported as its own species rather than as a disagreement.
    #[test]
    fn a_receiver_out_of_contact_is_not_an_obstruction() {
        let (complex, vertices, _) = path(9);
        let mut neighbourhood = stretches(&complex, &vertices, 2, 2);
        // A third receiver far down the path, touching neither of the first two.
        let far: BTreeSet<CausalCellId> = vertices[6..9].iter().copied().collect();
        let far_section: BTreeSet<CausalCellId> = complex
            .cells()
            .values()
            .filter(|cell| cell.grade > 0 && cell.boundary.support().is_subset(&far))
            .map(|cell| cell.id)
            .chain(far.iter().copied())
            .collect();
        neighbourhood.sections.push(far_section);

        let reading = spread(&complex, &neighbourhood, 0, PivotRule::FirstNonzero).unwrap();
        assert_eq!(reading.out_of_contact, vec![2]);
        assert!(
            reading.unobstructed(),
            "no contact means nothing disagreed: {:?}",
            reading.frontier
        );
        assert_eq!(reading.reach(), 2);
    }

    /// The measurement this module exists for. Two stretches of a **rim** overlap at both ends, so
    /// their union carries a loop neither holds — the connecting map is nonzero and growth stops at
    /// that contact. The local truth is still real on its own neighbourhood.
    #[test]
    fn growth_stops_at_a_real_obstruction_and_the_local_truth_still_stands() {
        let mut complex = GradedCausalComplex::default();
        let length = 10usize;
        let mut vertices = Vec::new();
        for index in 0..length {
            vertices.push(
                complex
                    .found_cell(format!("v{index}"), source(), 0, CausalChain::default())
                    .unwrap(),
            );
        }
        for index in 0..length {
            let mut boundary = CausalChain::default();
            boundary.add_term(
                vertices[(index + 1) % length],
                ComparativeMultiplicity::positive(1u32),
            );
            boundary.add_term(vertices[index], ComparativeMultiplicity::negative(1u32));
            complex
                .found_cell(format!("e{index}"), source(), 1, boundary)
                .unwrap();
        }

        let arc = |from: usize, to: usize| -> BTreeSet<CausalCellId> {
            let held: BTreeSet<CausalCellId> =
                (from..=to).map(|index| vertices[index % length]).collect();
            complex
                .cells()
                .values()
                .filter(|cell| cell.grade > 0 && cell.boundary.support().is_subset(&held))
                .map(|cell| cell.id)
                .chain(held.iter().copied())
                .collect()
        };

        // Two arcs whose union is the whole rim and whose overlap is disconnected.
        let neighbourhood = Neighbourhood {
            sections: vec![arc(0, 5), arc(5, 10)],
        };
        let reading = spread(&complex, &neighbourhood, 0, PivotRule::FirstNonzero).unwrap();

        assert!(
            !reading.unobstructed(),
            "the rim's loop lives in neither arc; the contact must obstruct"
        );
        assert_eq!(reading.frontier.len(), 1);
        assert_eq!(reading.frontier[0].from, 0);
        assert_eq!(reading.frontier[0].to, 1);
        assert!(
            reading.frontier[0].overlap_extent > 0,
            "they are in contact"
        );
        assert!(
            reading.frontier[0]
                .obstruction
                .iter()
                .any(|rank| *rank != 0),
            "and the contact carries a real connecting map"
        );
        assert_eq!(
            reading.reach(),
            1,
            "growth stopped, and the origin's own local truth still stands"
        );
        assert!(
            reading.out_of_contact.is_empty(),
            "this is disagreement, not silence"
        );
    }

    /// Reach depends on where you start. If it did not, the construction would be measuring a
    /// global property and the whole local premise would be false.
    #[test]
    fn reach_is_a_property_of_the_origin() {
        let (complex, vertices, _) = path(10);
        let mut neighbourhood = stretches(&complex, &vertices, 2, 4);
        let far: BTreeSet<CausalCellId> = vertices[8..10].iter().copied().collect();
        neighbourhood.sections.push(
            complex
                .cells()
                .values()
                .filter(|cell| cell.grade > 0 && cell.boundary.support().is_subset(&far))
                .map(|cell| cell.id)
                .chain(far.iter().copied())
                .collect(),
        );

        let readings = spread_from_each(&complex, &neighbourhood, PivotRule::FirstNonzero).unwrap();
        let radii: Vec<usize> = readings.iter().map(Spread::radius).collect();
        assert!(
            radii.iter().any(|radius| *radius != radii[0]),
            "every origin returned the same radius {radii:?}, so this is not a local measurement"
        );
        // And the isolated receiver reaches only itself.
        assert_eq!(readings[4].reach(), 1);
    }

    /// A single receiver communicates with nobody and still holds its own local truth. Without this
    /// the reach could be reporting the size of the family rather than what was reached.
    #[test]
    fn one_receiver_reaches_itself_and_no_further() {
        let (complex, vertices, _) = path(4);
        let neighbourhood = stretches(&complex, &vertices, 3, 1);
        let reading = spread(&complex, &neighbourhood, 0, PivotRule::FirstNonzero).unwrap();
        assert_eq!(reading.reach(), 1);
        assert_eq!(reading.radius(), 0);
        assert!(reading.unobstructed());
        assert!(reading.out_of_contact.is_empty());
    }
}
