use super::*;

/// Exact oriented basis current retained once per native factor. The complete addressed pair
/// population remains beside the joined current as its reconstruction fibre.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralExteriorRealizationOrientedFactorCurrent {
    pub factor: u32,
    pub current: ExactComplexWaveCurrent,
    pub pair_currents: Vec<SourceNeutralAddressedResponsePairCurrent>,
}

/// One response-face current before response faces join on their dependent factor line.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralAddressedResponsePairCurrent {
    pub response_face: u32,
    pub native_port: u32,
    pub native_generator: u32,
    pub source_section: u32,
    pub selected_slot: u32,
    pub target_section: u32,
    pub factor: u32,
    pub current: ExactComplexWaveCurrent,
}

/// One exact current occurrence after a response face meets an addressed realization-site
/// transport. Both endpoint maps and the original response occurrence remain present until the
/// target and port junctions consume this population. Absence from this complete sparse list is
/// the zero-support complement; no dense zero entries are materialized.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralAddressedRealizationPairCurrent {
    pub response: SourceNeutralAddressedResponsePairCurrent,
    pub source_carrier: u32,
    pub source_site: u32,
    pub source_local_port: u16,
    pub target_carrier: u32,
    pub target_site: u32,
    pub target_local_port: u16,
    pub exterior_target_port: u16,
    pub factor: u32,
    pub phase: u8,
    pub current: ExactComplexWaveCurrent,
}

pub(super) fn join_response_pair_currents(
    pairs: &[SourceNeutralAddressedResponsePairCurrent],
) -> Result<Vec<SourceNeutralExteriorRealizationOrientedFactorCurrent>, SourceNeutralRelationalError>
{
    if pairs.is_empty() || pairs.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(SourceNeutralRelationalError::Quotient);
    }
    let mut joined = BTreeMap::<u32, ExactComplexWaveCurrent>::new();
    for pair in pairs {
        if pair.current.is_zero() {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        let entry = joined.entry(pair.factor).or_default();
        *entry = entry.add(&pair.current);
    }
    joined.retain(|_, current| !current.is_zero());
    Ok(joined
        .into_iter()
        .map(
            |(factor, current)| SourceNeutralExteriorRealizationOrientedFactorCurrent {
                factor,
                current,
                pair_currents: pairs
                    .iter()
                    .filter(|pair| pair.factor == factor)
                    .cloned()
                    .collect(),
            },
        )
        .collect())
}

pub(super) fn validate_oriented_factor_currents(
    factors: &[SourceNeutralExteriorRealizationOrientedFactorCurrent],
    faces: &[SourceNeutralNativeOrientedFace],
) -> Result<(), SourceNeutralRelationalError> {
    for factor in factors {
        if factor.pair_currents.is_empty()
            || factor
                .pair_currents
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        let mut joined = ExactComplexWaveCurrent::zero();
        for pair in &factor.pair_currents {
            let retained = faces.iter().any(|face| {
                face.mode == pair.response_face
                    && face.native_port == pair.native_port
                    && face.native_generator == pair.native_generator
                    && face.local_currents.iter().any(|local| {
                        local.source_section == pair.source_section
                            && local.selected_slot == pair.selected_slot
                            && local.target_section == pair.target_section
                            && local
                                .factor_current
                                .iter()
                                .any(|(held, _)| *held == pair.factor)
                    })
            });
            if pair.factor != factor.factor || pair.current.is_zero() || !retained {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            joined = joined.add(&pair.current);
        }
        if joined != factor.current {
            return Err(SourceNeutralRelationalError::Quotient);
        }
    }
    Ok(())
}

impl SourceNeutralExteriorRealizationMorphology {
    /// Join the exact pre-locking response faces through the device-enacted local-current rows
    /// which precede their target-state junction.  The resident row supplies the factor
    /// coefficient and the response face supplies the complex orientation.  Their mode axis
    /// remains in `native_oriented_faces` as the complete reconstruction fibre; it may condense
    /// here only because the subsequent realization incidence acts factorwise and independently
    /// of that mode.
    pub(super) fn native_complex_factor_current(
        &self,
        native_sections: &[AddressedCurrentSection],
        native_oriented_faces: &[SourceNeutralNativeOrientedFace],
    ) -> Result<
        Vec<SourceNeutralExteriorRealizationOrientedFactorCurrent>,
        SourceNeutralRelationalError,
    > {
        if native_oriented_faces
            .windows(2)
            .any(|pair| pair[0].mode >= pair[1].mode)
            || native_oriented_faces.iter().any(|face| {
                face.target_states.is_empty()
                    || face.target_states.windows(2).any(|pair| pair[0] >= pair[1])
            })
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        let mut unique_local_currents = BTreeMap::<(u32, u32, u32), Vec<(u32, BigUint)>>::new();
        let mut pair_currents = Vec::<SourceNeutralAddressedResponsePairCurrent>::new();
        for face in native_oriented_faces {
            if face.local_currents.is_empty() {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            for local in &face.local_currents {
                let target = native_sections
                    .get(local.target_section as usize)
                    .ok_or(SourceNeutralRelationalError::Quotient)?;
                let target_state = target
                    .boundary_state
                    .ok_or(SourceNeutralRelationalError::Quotient)?;
                if local.source_section as usize >= native_sections.len()
                    || face.target_states.binary_search(&target_state).is_err()
                    || local.factor_current.is_empty()
                    || local
                        .factor_current
                        .windows(2)
                        .any(|pair| pair[0].0 >= pair[1].0)
                    || local.factor_current.iter().any(|(factor, coefficient)| {
                        *factor >= self.factor_population || coefficient.is_zero()
                    })
                {
                    return Err(SourceNeutralRelationalError::Quotient);
                }
                match unique_local_currents.insert(
                    (
                        local.source_section,
                        local.selected_slot,
                        local.target_section,
                    ),
                    local.factor_current.clone(),
                ) {
                    Some(existing) if existing != local.factor_current => {
                        return Err(SourceNeutralRelationalError::Quotient);
                    }
                    _ => {}
                }
                if face.oriented_current.is_zero() {
                    continue;
                }
                for (factor, coefficient) in &local.factor_current {
                    let contribution = face
                        .oriented_current
                        .scaled(&Ratio::from_integer(BigInt::from(coefficient.clone())));
                    pair_currents.push(SourceNeutralAddressedResponsePairCurrent {
                        response_face: face.mode,
                        native_port: face.native_port,
                        native_generator: face.native_generator,
                        source_section: local.source_section,
                        selected_slot: local.selected_slot,
                        target_section: local.target_section,
                        factor: *factor,
                        current: contribution,
                    });
                }
            }
        }
        pair_currents.sort();
        if pair_currents.is_empty() || pair_currents.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        let joined_factor_currents = join_response_pair_currents(&pair_currents)?;
        let mut reconstructed_targets =
            vec![BTreeMap::<u32, BigUint>::new(); native_sections.len()];
        for ((_, _, target_section), factor_current) in unique_local_currents {
            let target = reconstructed_targets
                .get_mut(target_section as usize)
                .ok_or(SourceNeutralRelationalError::Quotient)?;
            for (factor, coefficient) in factor_current {
                *target.entry(factor).or_default() += coefficient;
            }
        }
        if native_sections
            .iter()
            .zip(reconstructed_targets)
            .any(|(expected, returned)| {
                expected.factor_current
                    != returned
                        .into_iter()
                        .filter(|(_, coefficient)| !coefficient.is_zero())
                        .collect::<Vec<_>>()
            })
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        if joined_factor_currents.is_empty() {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        Ok(joined_factor_currents)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn current(real: i64, imaginary: i64) -> ExactComplexWaveCurrent {
        ExactComplexWaveCurrent::new(
            Ratio::from_integer(BigInt::from(real)),
            Ratio::from_integer(BigInt::from(imaginary)),
        )
    }

    #[test]
    fn addressed_response_pairs_join_without_losing_either_boundary_map() {
        let pairs = vec![
            SourceNeutralAddressedResponsePairCurrent {
                response_face: 3,
                native_port: 5,
                native_generator: 7,
                source_section: 11,
                selected_slot: 13,
                target_section: 17,
                factor: 19,
                current: current(2, 1),
            },
            SourceNeutralAddressedResponsePairCurrent {
                response_face: 4,
                native_port: 5,
                native_generator: 7,
                source_section: 12,
                selected_slot: 14,
                target_section: 17,
                factor: 19,
                current: current(-1, 3),
            },
        ];
        let joined = join_response_pair_currents(&pairs).expect("the addressed junction returns");
        assert_eq!(joined.len(), 1);
        assert_eq!(joined[0].factor, 19);
        assert_eq!(joined[0].current, current(1, 4));
        assert_eq!(joined[0].pair_currents, pairs);
    }
}
