use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct CorrespondenceCandidate {
    pub left: String,
    pub right: String,
}

/// Complete correspondence/reconstruction fibre for two declared charts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CoTestimonyFiber {
    pub left_artifact: ArtifactIdentity,
    pub right_artifact: ArtifactIdentity,
    pub left_extent: ExactExtent,
    pub right_extent: ExactExtent,
    pub candidates: Vec<CorrespondenceCandidate>,
    pub left_candidates: BTreeMap<String, BTreeSet<String>>,
    pub right_candidates: BTreeMap<String, BTreeSet<String>>,
    pub unmatched_left: BTreeSet<String>,
    pub unmatched_right: BTreeSet<String>,
    pub work: SourceLayoutWorkDemand,
    pub actual_pair_visits: u128,
    pub outside_declared_charts_open: bool,
}

pub fn correspondence_demand(
    left: &SourceLayoutTestimony,
    right: &SourceLayoutTestimony,
) -> Result<SourceLayoutWorkDemand, SourceLayoutError> {
    let left_population =
        u128::try_from(left.occurrences.len()).map_err(|_| SourceLayoutError::Extent)?;
    let right_population =
        u128::try_from(right.occurrences.len()).map_err(|_| SourceLayoutError::Extent)?;
    Ok(SourceLayoutWorkDemand {
        pair_visits: left_population
            .checked_mul(right_population)
            .ok_or(SourceLayoutError::Extent)?,
        sample_visits: 0,
        carried_octets: 0,
    })
}

pub fn correspond(
    left: &SourceLayoutTestimony,
    right: &SourceLayoutTestimony,
    cover: &SourceLayoutWorkCover,
) -> Result<CoTestimonyFiber, SourceLayoutError> {
    let work = correspondence_demand(left, right)?;
    if !cover.admits(&work) {
        return Err(SourceLayoutError::WorkCoverInsufficient {
            demand: work,
            cover: cover.clone(),
        });
    }
    let mut candidates = Vec::new();
    let mut left_candidates = BTreeMap::<String, BTreeSet<String>>::new();
    let mut right_candidates = BTreeMap::<String, BTreeSet<String>>::new();
    // Chart division is exact but expensive. Take it once per occurrence, never once per pair.
    let normalized_left = left
        .occurrences
        .iter()
        .map(|occurrence| occurrence.bounds.normalized(&left.extent))
        .collect::<Vec<_>>();
    let normalized_right = right
        .occurrences
        .iter()
        .map(|occurrence| occurrence.bounds.normalized(&right.extent))
        .collect::<Vec<_>>();
    // Exact rectangle intersection by an x-sweep. End events precede starts at equal x because
    // boxes are half-open. The active population is precisely the possible x-overlap fibre; y is
    // then the shortest separating receiver. This returns the same complete pair population as the
    // Cartesian product while refusing to replay pairs whose x projections are disjoint.
    // Event tuple: (x, end-before-start, left-before-right, local ordinal).
    let mut events = Vec::<(Rat, u8, u8, usize)>::new();
    for (at, bounds) in normalized_left.iter().enumerate() {
        if bounds.left < bounds.right && bounds.top < bounds.bottom {
            events.push((bounds.right.clone(), 0, 0, at));
            events.push((bounds.left.clone(), 1, 0, at));
        }
    }
    for (at, bounds) in normalized_right.iter().enumerate() {
        if bounds.left < bounds.right && bounds.top < bounds.bottom {
            events.push((bounds.right.clone(), 0, 1, at));
            events.push((bounds.left.clone(), 1, 1, at));
        }
    }
    events.sort();
    let mut active_left = BTreeSet::new();
    let mut active_right = BTreeSet::new();
    let mut actual_pair_visits = 0_u128;
    let mut admit_pair = |left_at: usize, right_at: usize| -> Result<(), SourceLayoutError> {
        actual_pair_visits = actual_pair_visits
            .checked_add(1)
            .ok_or(SourceLayoutError::Extent)?;
        if normalized_left[left_at].overlaps(&normalized_right[right_at]) {
            let left_occurrence = &left.occurrences[left_at];
            let right_occurrence = &right.occurrences[right_at];
            candidates.push(CorrespondenceCandidate {
                left: left_occurrence.address.clone(),
                right: right_occurrence.address.clone(),
            });
            left_candidates
                .entry(left_occurrence.address.clone())
                .or_default()
                .insert(right_occurrence.address.clone());
            right_candidates
                .entry(right_occurrence.address.clone())
                .or_default()
                .insert(left_occurrence.address.clone());
        }
        Ok(())
    };
    for (_, phase, side, at) in events {
        match (phase, side) {
            (0, 0) => {
                active_left.remove(&at);
            }
            (0, 1) => {
                active_right.remove(&at);
            }
            (1, 0) => {
                for right_at in active_right.iter().copied() {
                    admit_pair(at, right_at)?;
                }
                active_left.insert(at);
            }
            (1, 1) => {
                for left_at in active_left.iter().copied() {
                    admit_pair(left_at, at)?;
                }
                active_right.insert(at);
            }
            _ => unreachable!("the event phases and sides are constructed above"),
        }
    }
    let unmatched_left = left
        .occurrences
        .iter()
        .map(|occurrence| occurrence.address.clone())
        .filter(|address| !left_candidates.contains_key(address))
        .collect();
    let unmatched_right = right
        .occurrences
        .iter()
        .map(|occurrence| occurrence.address.clone())
        .filter(|address| !right_candidates.contains_key(address))
        .collect();
    Ok(CoTestimonyFiber {
        left_artifact: left.artifact.clone(),
        right_artifact: right.artifact.clone(),
        left_extent: left.extent.clone(),
        right_extent: right.extent.clone(),
        candidates,
        left_candidates,
        right_candidates,
        unmatched_left,
        unmatched_right,
        work,
        actual_pair_visits,
        outside_declared_charts_open: true,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ComparedContact {
    pub from_serial: u64,
    pub to_serial: u64,
    pub relation: LayoutRelation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PresentationComparison {
    pub serial_payload_face_equal: bool,
    pub retained_contacts: Vec<ComparedContact>,
    pub departed_contacts: Vec<ComparedContact>,
    pub arrived_contacts: Vec<ComparedContact>,
    pub before_contacts_outside_serial_receiver: Vec<LayoutContact>,
    pub after_contacts_outside_serial_receiver: Vec<LayoutContact>,
    pub first_payload_separator: Option<(usize, String, String)>,
}

/// Compare two presentations at two separately named receivers: serial payload order may remain
/// invariant while exact layout incidence moves. The function calls neither movement semantic.
pub fn compare_presentations(
    before: &SourceLayoutTestimony,
    after: &SourceLayoutTestimony,
) -> PresentationComparison {
    let serial = |testimony: &SourceLayoutTestimony| {
        let mut population = testimony
            .occurrences
            .iter()
            .filter_map(|occurrence| {
                occurrence
                    .serial_ordinal
                    .map(|ordinal| (ordinal, occurrence.payload_sha256.clone()))
            })
            .collect::<Vec<_>>();
        population.sort();
        population
    };
    let before_serial = serial(before);
    let after_serial = serial(after);
    let first_payload_separator = before_serial
        .iter()
        .zip(&after_serial)
        .enumerate()
        .find_map(|(at, (left, right))| {
            (left != right).then(|| {
                (
                    at,
                    format!("{}:{}", left.0, left.1),
                    format!("{}:{}", right.0, right.1),
                )
            })
        })
        .or_else(|| {
            (before_serial.len() != after_serial.len()).then(|| {
                (
                    before_serial.len().min(after_serial.len()),
                    before_serial
                        .get(after_serial.len())
                        .map(|entry| entry.1.clone())
                        .unwrap_or_default(),
                    after_serial
                        .get(before_serial.len())
                        .map(|entry| entry.1.clone())
                        .unwrap_or_default(),
                )
            })
        });
    let keyed = |testimony: &SourceLayoutTestimony| {
        let mut carried = BTreeSet::new();
        let mut outside = Vec::new();
        for contact in &testimony.contacts {
            let from = testimony
                .occurrences
                .get(contact.from)
                .and_then(|occurrence| occurrence.serial_ordinal);
            let to = testimony
                .occurrences
                .get(contact.to)
                .and_then(|occurrence| occurrence.serial_ordinal);
            match (from, to) {
                (Some(from_serial), Some(to_serial)) => {
                    carried.insert((from_serial, to_serial, contact.relation));
                }
                _ => outside.push(contact.clone()),
            }
        }
        (carried, outside)
    };
    let (before_contacts, before_outside) = keyed(before);
    let (after_contacts, after_outside) = keyed(after);
    let present = |(from_serial, to_serial, relation)| ComparedContact {
        from_serial,
        to_serial,
        relation,
    };
    PresentationComparison {
        serial_payload_face_equal: before_serial == after_serial,
        retained_contacts: before_contacts
            .intersection(&after_contacts)
            .cloned()
            .map(present)
            .collect(),
        departed_contacts: before_contacts
            .difference(&after_contacts)
            .cloned()
            .map(present)
            .collect(),
        arrived_contacts: after_contacts
            .difference(&before_contacts)
            .cloned()
            .map(present)
            .collect(),
        before_contacts_outside_serial_receiver: before_outside,
        after_contacts_outside_serial_receiver: after_outside,
        first_payload_separator,
    }
}
