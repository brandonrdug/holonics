use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::receiver_exact_compression::{Observation, ReceiverId};
use crate::receiver_history_compression::NativeStateId;

/// An exterior contact schedule chart. It observes a founded native population and never becomes
/// the identity or topology of that population.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ContactScheduleChart {
    ForeignAutoregressiveKv { retained: usize },
    FixedWindow { radius: usize },
    PeriodicHybrid { radius: usize, period: usize },
    RecurrentLinear,
    CurrentFounded,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ContactEdge {
    pub from: NativeStateId,
    pub to: NativeStateId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContactChartReturn {
    pub chart: ContactScheduleChart,
    pub contacts: Vec<ContactEdge>,
    pub active_causal_extent: usize,
    pub exact_pair_tests: u64,
    pub retained_receiver_classes: usize,
    pub reconstruction_fibres: Vec<Vec<NativeStateId>>,
}

/// One comparison over a common native population and receiver family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContactChartComparison {
    pub states: Vec<NativeStateId>,
    pub receiver: ReceiverId,
    pub returns: Vec<ContactChartReturn>,
    pub richer_receiver_reopenings: Vec<(NativeStateId, NativeStateId)>,
    pub schedules_are_receiver_charts: bool,
}

pub fn compare_contact_charts(
    states: &[NativeStateId],
    recurrent: &[ContactEdge],
    current_founded: &[ContactEdge],
    receiver: ReceiverId,
    coarse_faces: &[(NativeStateId, Observation)],
    rich_faces: &[(NativeStateId, Observation)],
) -> Result<ContactChartComparison, ContactChartError> {
    let state_set = states.iter().copied().collect::<BTreeSet<_>>();
    if states.is_empty()
        || state_set.len() != states.len()
        || !all_total_faces(&state_set, coarse_faces)
        || !all_total_faces(&state_set, rich_faces)
        || recurrent
            .iter()
            .chain(current_founded)
            .any(|edge| !state_set.contains(&edge.from) || !state_set.contains(&edge.to))
    {
        return Err(ContactChartError::Malformed);
    }
    let charts = [
        ContactScheduleChart::ForeignAutoregressiveKv {
            retained: states.len(),
        },
        ContactScheduleChart::FixedWindow { radius: 1 },
        ContactScheduleChart::PeriodicHybrid {
            radius: 1,
            period: 3,
        },
        ContactScheduleChart::RecurrentLinear,
        ContactScheduleChart::CurrentFounded,
    ];
    let mut returns = Vec::with_capacity(charts.len());
    for chart in charts {
        let contacts = match chart {
            ContactScheduleChart::ForeignAutoregressiveKv { retained } => {
                causal_prefix(states, retained)
            }
            ContactScheduleChart::FixedWindow { radius } => window(states, radius, None),
            ContactScheduleChart::PeriodicHybrid { radius, period } => {
                window(states, radius, Some(period))
            }
            ContactScheduleChart::RecurrentLinear => ordered_unique(recurrent),
            ContactScheduleChart::CurrentFounded => ordered_unique(current_founded),
        };
        let fibres = receiver_fibres(states, coarse_faces);
        returns.push(ContactChartReturn {
            chart,
            active_causal_extent: contacts.len(),
            exact_pair_tests: match chart {
                ContactScheduleChart::ForeignAutoregressiveKv { .. } => {
                    u64::try_from(states.len().saturating_mul(states.len().saturating_add(1)) / 2)
                        .map_err(|_| ContactChartError::Extent)?
                }
                ContactScheduleChart::FixedWindow { .. }
                | ContactScheduleChart::PeriodicHybrid { .. } => {
                    u64::try_from(states.len().saturating_mul(states.len()))
                        .map_err(|_| ContactChartError::Extent)?
                }
                ContactScheduleChart::RecurrentLinear => recurrent.len() as u64,
                ContactScheduleChart::CurrentFounded => current_founded.len() as u64,
            },
            retained_receiver_classes: fibres.len(),
            reconstruction_fibres: fibres,
            contacts,
        });
    }
    let coarse = face_map(coarse_faces);
    let rich = face_map(rich_faces);
    let mut reopenings = Vec::new();
    for (at, left) in states.iter().enumerate() {
        for right in &states[at + 1..] {
            if coarse[left] == coarse[right] && rich[left] != rich[right] {
                reopenings.push((*left, *right));
            }
        }
    }
    Ok(ContactChartComparison {
        states: states.to_vec(),
        receiver,
        returns,
        richer_receiver_reopenings: reopenings,
        schedules_are_receiver_charts: true,
    })
}

fn causal_prefix(states: &[NativeStateId], retained: usize) -> Vec<ContactEdge> {
    let mut contacts = Vec::new();
    for (to_at, to) in states.iter().enumerate() {
        let from_at = to_at.saturating_add(1).saturating_sub(retained);
        contacts.extend(states[from_at..=to_at].iter().map(|from| ContactEdge {
            from: *from,
            to: *to,
        }));
    }
    contacts
}

fn window(
    states: &[NativeStateId],
    radius: usize,
    periodic_reopening: Option<usize>,
) -> Vec<ContactEdge> {
    let mut contacts = BTreeSet::new();
    for (from_at, from) in states.iter().enumerate() {
        for (to_at, to) in states.iter().enumerate() {
            let local = from_at.abs_diff(to_at) <= radius;
            let reopened = periodic_reopening.is_some_and(|period| {
                period != 0 && (from_at % period == 0 || to_at % period == 0)
            });
            if local || reopened {
                contacts.insert(ContactEdge {
                    from: *from,
                    to: *to,
                });
            }
        }
    }
    contacts.into_iter().collect()
}

fn ordered_unique(edges: &[ContactEdge]) -> Vec<ContactEdge> {
    edges
        .iter()
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn face_map(faces: &[(NativeStateId, Observation)]) -> BTreeMap<NativeStateId, Observation> {
    faces.iter().copied().collect()
}

fn all_total_faces(
    states: &BTreeSet<NativeStateId>,
    faces: &[(NativeStateId, Observation)],
) -> bool {
    let map = face_map(faces);
    map.len() == faces.len() && map.keys().copied().collect::<BTreeSet<_>>() == *states
}

fn receiver_fibres(
    states: &[NativeStateId],
    faces: &[(NativeStateId, Observation)],
) -> Vec<Vec<NativeStateId>> {
    let map = face_map(faces);
    let mut fibres = BTreeMap::<Observation, Vec<NativeStateId>>::new();
    for state in states {
        fibres.entry(map[state]).or_default().push(*state);
    }
    fibres.into_values().collect()
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ContactChartError {
    #[error("contact-chart population is malformed")]
    Malformed,
    #[error("contact-chart exact-work extent overflowed")]
    Extent,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schedules_change_contact_without_becoming_native_identity() {
        let states = (0..5).map(NativeStateId).collect::<Vec<_>>();
        let recurrent = (0..5)
            .map(|at| ContactEdge {
                from: NativeStateId(at),
                to: NativeStateId((at + 1) % 5),
            })
            .collect::<Vec<_>>();
        let current = vec![
            ContactEdge {
                from: NativeStateId(0),
                to: NativeStateId(2),
            },
            ContactEdge {
                from: NativeStateId(2),
                to: NativeStateId(4),
            },
        ];
        let coarse = states
            .iter()
            .map(|state| (*state, Observation(state.0 % 2)))
            .collect::<Vec<_>>();
        let rich = states
            .iter()
            .map(|state| (*state, Observation(state.0)))
            .collect::<Vec<_>>();
        let returned =
            compare_contact_charts(&states, &recurrent, &current, ReceiverId(0), &coarse, &rich)
                .expect("comparison");
        let extents = returned
            .returns
            .iter()
            .map(|returned| returned.active_causal_extent)
            .collect::<BTreeSet<_>>();
        assert!(extents.len() > 1);
        assert!(!returned.richer_receiver_reopenings.is_empty());
        assert!(returned.schedules_are_receiver_charts);
    }
}
