//! Exterior presentation contact and its descent to proposal-relative factor current.

use super::*;

#[derive(Default)]
pub(super) struct PhaseFaceContactCurrent {
    pub(super) current: BTreeMap<(u32, u32), BigUint>,
    pub(super) query_sections: BTreeMap<(u32, u32), BTreeSet<usize>>,
}

fn contact_port_fold(port: u16) -> u16 {
    if (u16::from(b'A') + 1..=u16::from(b'Z') + 1).contains(&port) {
        port + u16::from(b'a' - b'A')
    } else {
        port
    }
}

fn contact_sections(
    ports: &[u16],
) -> Result<Vec<BTreeMap<(u16, u16), u64>>, SourceNeutralRelationalError> {
    let mut sections = Vec::new();
    let mut section = Vec::<u16>::new();
    let flush = |section: &mut Vec<u16>, sections: &mut Vec<BTreeMap<(u16, u16), u64>>| {
        if section.is_empty() {
            return;
        }
        let ports = std::iter::once(0_u16)
            .chain(section.drain(..))
            .chain(std::iter::once(257_u16))
            .collect::<Vec<_>>();
        let mut current = BTreeMap::new();
        for pair in ports.windows(2) {
            *current.entry((pair[0], pair[1])).or_default() += 1;
        }
        sections.push(current);
    };
    for port in ports.iter().copied() {
        let octet = port
            .checked_sub(1)
            .and_then(|value| u8::try_from(value).ok())
            .ok_or(SourceNeutralRelationalError::Quotient)?;
        if octet.is_ascii_alphanumeric() {
            section.push(contact_port_fold(port));
        } else {
            flush(&mut section, &mut sections);
        }
    }
    flush(&mut section, &mut sections);
    Ok(sections)
}

impl SourceNeutralExteriorRealizationMorphology {
    /// Project one exterior occurrence onto anonymous realization faces through shared local port
    /// incidence. Every returned current retains which boundary-founded query section caused it.
    pub(super) fn phase_face_contact_current(
        &self,
        relational: &SourceNeutralRelationalMorphology,
        ingress_ports: &[u16],
        phase: u8,
    ) -> Result<PhaseFaceContactCurrent, SourceNeutralRelationalError> {
        if ingress_ports.is_empty() {
            return Ok(PhaseFaceContactCurrent::default());
        }
        let query_sections = contact_sections(ingress_ports)?;
        if query_sections.is_empty() {
            return Ok(PhaseFaceContactCurrent::default());
        }
        if phase > 1 {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        let counterpart = 1_u8 - phase;
        let counterpart_factors = relational
            .cells
            .iter()
            .flat_map(|cell| &cell.phase_population)
            .filter(|population| population.phase == counterpart)
            .map(|population| population.factor)
            .collect::<BTreeSet<_>>();
        let mut presentations = Vec::<((u32, u32), Vec<BTreeMap<(u16, u16), u64>>)>::new();
        for (face, root) in &self.presentation_roots {
            let admitted = relational
                .faces
                .get(*face as usize)
                .ok_or(SourceNeutralRelationalError::Quotient)?
                .phase_population
                .iter()
                .any(|population| {
                    population.phase == phase && counterpart_factors.contains(&population.factor)
                });
            if !admitted {
                continue;
            }
            let mut state = *root;
            let mut source = 0_u16;
            let mut visited = BTreeSet::new();
            let mut surface_ports = Vec::new();
            loop {
                if !visited.insert((state, source)) {
                    return Err(SourceNeutralRelationalError::Quotient);
                }
                let transitions = self
                    .state_source_transitions(state, source)
                    .iter()
                    .filter(|transition| transition.face == *face)
                    .collect::<Vec<_>>();
                let [transition] = transitions.as_slice() else {
                    return Err(SourceNeutralRelationalError::Quotient);
                };
                if transition.target == 257 {
                    break;
                }
                surface_ports.push(transition.target);
                source = transition.target;
                state = transition
                    .target_state
                    .ok_or(SourceNeutralRelationalError::Quotient)?;
            }
            let sections = contact_sections(&surface_ports)?;
            if !sections.is_empty() {
                presentations.push(((*face, *root), sections));
            }
        }
        if presentations.is_empty() {
            return Ok(PhaseFaceContactCurrent::default());
        }
        let mut edge_presentations = BTreeMap::<(u16, u16), BTreeSet<(u32, u32)>>::new();
        for (presentation, sections) in &presentations {
            for section in sections {
                for edge in section.keys() {
                    edge_presentations
                        .entry(*edge)
                        .or_default()
                        .insert(*presentation);
                }
            }
        }
        let presentation_extent = u64::try_from(presentations.len())
            .map_err(|_| SourceNeutralRelationalError::Extent)?
            .checked_add(1)
            .ok_or(SourceNeutralRelationalError::Extent)?;
        let rarity = edge_presentations
            .iter()
            .map(|(edge, members)| {
                let population = u64::try_from(members.len())
                    .map_err(|_| SourceNeutralRelationalError::Extent)?;
                let current = presentation_extent
                    .checked_sub(population)
                    .and_then(|value| value.checked_add(1))
                    .ok_or(SourceNeutralRelationalError::Extent)?;
                Ok((*edge, current))
            })
            .collect::<Result<BTreeMap<_, _>, SourceNeutralRelationalError>>()?;
        let mut contact = BTreeMap::<(u32, u32), BigUint>::new();
        let mut contact_sections = BTreeMap::<(u32, u32), BTreeSet<usize>>::new();
        for (query_section, query) in query_sections.into_iter().enumerate() {
            let query_total = query
                .iter()
                .fold(BigUint::zero(), |total, (edge, population)| {
                    let weight = rarity.get(edge).copied().unwrap_or(presentation_extent);
                    total + BigUint::from(*population) * BigUint::from(weight)
                });
            let mut candidates = Vec::new();
            for (presentation, sections) in &presentations {
                let mut presentation_contact = None;
                for edges in sections {
                    let mut total = BigUint::zero();
                    let mut common = BigUint::zero();
                    for (edge, population) in edges {
                        let weight = rarity[edge];
                        total += BigUint::from(*population) * BigUint::from(weight);
                        if let Some(query_population) = query.get(edge).copied() {
                            common += BigUint::from(query_population.min(*population))
                                * BigUint::from(weight);
                        }
                    }
                    if !common.is_zero() {
                        let union = &query_total + total - &common;
                        if union.is_zero() {
                            return Err(SourceNeutralRelationalError::Quotient);
                        }
                        let quotient = Ratio::new(common, union);
                        if presentation_contact
                            .as_ref()
                            .is_none_or(|held| &quotient > held)
                        {
                            presentation_contact = Some(quotient);
                        }
                    }
                }
                if let Some(quotient) = presentation_contact {
                    candidates.push((*presentation, quotient));
                }
            }
            let Some(greatest) = candidates
                .iter()
                .map(|(_, quotient)| quotient)
                .max()
                .cloned()
            else {
                continue;
            };
            for (presentation, quotient) in candidates {
                if quotient == greatest {
                    *contact.entry(presentation).or_default() += BigUint::from(1_u8);
                    contact_sections
                        .entry(presentation)
                        .or_default()
                        .insert(query_section);
                }
            }
        }
        if contact.is_empty() {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "oriented-realization-contact-presentations={:?}",
                contact.keys().collect::<Vec<_>>()
            );
        }
        Ok(PhaseFaceContactCurrent {
            current: contact,
            query_sections: contact_sections,
        })
    }

    pub(super) fn join_ingress_face_factor_current(
        &self,
        relational: &SourceNeutralRelationalMorphology,
        native: Vec<SourceNeutralExteriorRealizationOrientedFactorCurrent>,
        ingress_faces: &BTreeMap<(u32, u32), BigUint>,
        response_faces: &BTreeMap<(u32, u32), BigUint>,
        entering: &ExactComplexWaveCurrent,
    ) -> Result<
        Vec<SourceNeutralExteriorRealizationOrientedFactorCurrent>,
        SourceNeutralRelationalError,
    > {
        let mut joined = native
            .into_iter()
            .map(|factor| {
                (
                    factor.factor,
                    (
                        factor.current,
                        factor.pair_currents,
                        factor.ingress_face_currents,
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let ingress_factors = relational
            .cells
            .iter()
            .flat_map(|cell| &cell.phase_population)
            .filter(|population| population.phase == 0)
            .map(|population| population.factor)
            .collect::<BTreeSet<_>>();
        let emanation_factors = relational
            .cells
            .iter()
            .flat_map(|cell| &cell.phase_population)
            .filter(|population| population.phase == 1)
            .map(|population| population.factor)
            .collect::<BTreeSet<_>>();
        let paired_factors = ingress_factors
            .intersection(&emanation_factors)
            .copied()
            .collect::<BTreeSet<_>>();
        let mut contact_incidence = BTreeMap::<(u32, u32, u8, u32), BigUint>::new();
        for (faces, phase) in [(ingress_faces, 0_u8), (response_faces, 1_u8)] {
            for ((face, realization_state), contact) in faces {
                let relational_face = relational
                    .faces
                    .get(*face as usize)
                    .ok_or(SourceNeutralRelationalError::Quotient)?;
                for population in &relational_face.phase_population {
                    if population.phase != phase || !paired_factors.contains(&population.factor) {
                        continue;
                    }
                    let key = (*face, *realization_state, phase, population.factor);
                    *contact_incidence.entry(key).or_default() +=
                        contact * BigUint::from(population.occurrence_population);
                }
            }
        }
        let response_factor_contact = contact_incidence.iter().fold(
            BTreeMap::<u32, BigUint>::new(),
            |mut totals, ((_, _, phase, factor), current)| {
                if *phase == 1 {
                    *totals.entry(*factor).or_default() += current;
                }
                totals
            },
        );
        let greatest_factor_contact = response_factor_contact
            .values()
            .max()
            .cloned()
            .ok_or(SourceNeutralRelationalError::Quotient)?;
        let admitted_factors = response_factor_contact
            .into_iter()
            .filter_map(|(factor, current)| (current == greatest_factor_contact).then_some(factor))
            .collect::<BTreeSet<_>>();
        contact_incidence.retain(|(_, _, _, factor), _| admitted_factors.contains(factor));
        for ((face, realization_state, phase, factor), contact_incidence) in contact_incidence {
            if contact_incidence.is_zero() || factor >= self.factor_population {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            let current = entering.scaled(&Ratio::from_integer(BigInt::from(
                contact_incidence.clone(),
            )));
            if current.is_zero() {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            let entry = joined
                .entry(factor)
                .or_insert_with(|| (ExactComplexWaveCurrent::zero(), Vec::new(), Vec::new()));
            entry.0 = entry.0.add(&current);
            entry.2.push(SourceNeutralIngressFaceFactorCurrent {
                face,
                realization_state,
                phase,
                factor,
                contact_incidence,
                current,
            });
        }
        joined.retain(|factor, (current, _, _)| {
            admitted_factors.contains(factor) && !current.is_zero()
        });
        let joined = joined
            .into_iter()
            .map(
                |(factor, (current, pair_currents, mut ingress_face_currents))| {
                    ingress_face_currents.sort();
                    SourceNeutralExteriorRealizationOrientedFactorCurrent {
                        factor,
                        current,
                        pair_currents,
                        ingress_face_currents,
                    }
                },
            )
            .collect::<Vec<_>>();
        if joined.is_empty() {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        Ok(joined)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn phase(factor: u32, phase: u8) -> SourceNeutralPhasePopulation {
        SourceNeutralPhasePopulation {
            factor,
            phase,
            occurrence_population: 1,
        }
    }

    fn install_surface(
        transitions: &mut Vec<SourceNeutralExteriorRealizationTransition>,
        next_state: &mut u32,
        face: u32,
        root: u32,
        surface: &[u8],
    ) {
        let mut state = root;
        let mut source = 0_u16;
        for target in surface
            .iter()
            .copied()
            .map(|octet| u16::from(octet) + 1)
            .chain(std::iter::once(257_u16))
        {
            let target_state = (target != 257).then(|| {
                let target_state = *next_state;
                *next_state += 1;
                target_state
            });
            transitions.push(SourceNeutralExteriorRealizationTransition {
                face,
                state,
                source,
                target,
                target_state,
                occurrence_population: 1,
            });
            let Some(target_state) = target_state else {
                break;
            };
            state = target_state;
            source = target;
        }
    }

    #[test]
    fn query_section_lineage_separates_relation_from_entity_across_phases() {
        let relational = SourceNeutralRelationalMorphology {
            schema: String::new(),
            factor_population: 1,
            factor_adjacency: Vec::new(),
            faces: vec![
                SourceNeutralRelationalFace {
                    address: String::new(),
                    factor_support: vec![0],
                    phase_population: vec![phase(0, 0)],
                    cell_incidence: vec![SourceNeutralRelationalIncidence {
                        cell: 0,
                        boundary_position: 0,
                        incidence_population: 1,
                    }],
                },
                SourceNeutralRelationalFace {
                    address: String::new(),
                    factor_support: vec![0],
                    phase_population: vec![phase(0, 1)],
                    cell_incidence: vec![SourceNeutralRelationalIncidence {
                        cell: 0,
                        boundary_position: 3,
                        incidence_population: 1,
                    }],
                },
            ],
            cells: vec![SourceNeutralRelationalCell {
                address: String::new(),
                oriented_boundary: vec![0, 0, 1],
                factor_support: vec![0],
                phase_population: vec![phase(0, 0), phase(0, 1)],
            }],
            obstructed_delivery_population: 0,
            identity_sha256: String::new(),
        };
        let mut transitions = Vec::new();
        let mut next_state = 2;
        install_surface(&mut transitions, &mut next_state, 0, 0, b"Brandon");
        install_surface(&mut transitions, &mut next_state, 1, 1, b"Brandon");
        transitions.sort_by_key(|transition| {
            (
                transition.source,
                transition.state,
                transition.face,
                transition.target,
            )
        });
        let morphology = SourceNeutralExteriorRealizationMorphology {
            schema: String::new(),
            relational_identity_sha256: String::new(),
            face_population: 2,
            cell_population: 1,
            sites: Vec::new(),
            factor_population: 1,
            face_root_states: vec![0, 1],
            presentation_roots: vec![(0, 0), (1, 1)],
            realization_state_population: next_state,
            transitions,
            developmental_transition_population: 16,
            identity_sha256: String::new(),
        };
        let query = "Describe Brandon"
            .bytes()
            .map(|octet| u16::from(octet) + 1)
            .collect::<Vec<_>>();
        let ingress = morphology
            .phase_face_contact_current(&relational, &query, 0)
            .expect("ingress contact");
        let response = morphology
            .phase_face_contact_current(&relational, &query, 1)
            .expect("response contact");
        assert_eq!(
            ingress.current.keys().copied().collect::<Vec<_>>(),
            vec![(0, 0)]
        );
        assert_eq!(
            response.current.keys().copied().collect::<Vec<_>>(),
            vec![(1, 1)]
        );
        assert_eq!(ingress.query_sections[&(0, 0)], BTreeSet::from([1]));
        assert_eq!(response.query_sections[&(1, 1)], BTreeSet::from([1]));
    }
}
