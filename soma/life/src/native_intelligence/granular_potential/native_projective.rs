impl NativeGranularPotential {
    /// Read the granular organ from the rejected pre-UAR0 wrapper and immediately quotient away
    /// its developmental occurrence/action identities. This reader is reachable only from the
    /// cold severing passage; the returned value validates under the source-neutral schema.
    pub(super) fn read_developmental_predecessor(
        value: serde_json::Value,
    ) -> Result<Self, NativeGranularPotentialError> {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct DevelopmentalPortState {
            #[serde(rename = "port")]
            _port: Option<GranularExteriorPort>,
            #[serde(rename = "restriction")]
            _restriction: Option<u32>,
            recurrence_multiplicity: u64,
            support: u32,
            transitions: Vec<GranularPortTransition>,
        }

        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct DevelopmentalWire {
            schema: String,
            supports: Vec<Vec<u32>>,
            states: Vec<DevelopmentalPortState>,
            factor_faces: Vec<GranularFactorFace>,
            factor_generators: Vec<GranularFactorGenerator>,
            #[serde(rename = "source_action_identity_sha256")]
            _action_lineage: String,
            #[serde(rename = "exposure_lineage")]
            occurrence_lineage: Vec<GranularExposureLineage>,
            #[serde(rename = "material_octet_population")]
            _material_octet_population: u64,
            #[serde(rename = "material_port_population")]
            _material_port_population: u64,
            identity_sha256: String,
        }

        let DevelopmentalWire {
            schema,
            supports: developmental_supports,
            states,
            mut factor_faces,
            factor_generators,
            _action_lineage: _,
            occurrence_lineage,
            _material_octet_population: _,
            _material_port_population: _,
            identity_sha256,
        } = serde_json::from_value(value).map_err(|_| NativeGranularPotentialError::Wire)?;
        if !schema.starts_with("soma-life.native-causal-boundary-potential.")
            || occurrence_lineage.is_empty()
            || !is_digest(&identity_sha256)
        {
            return Err(NativeGranularPotentialError::Wire);
        }
        for face in &mut factor_faces {
            face.factor_address =
                native_factor_address(face.factor, face.native, &face.receiver_factors);
            let identity = factor_identity(&face.factor_address);
            face.receiver_schema = identity.schema();
            face.receiver_words = identity.words().to_vec();
        }
        let mut supports = Vec::<Vec<u32>>::new();
        let mut support_lookup = BTreeMap::<Vec<u32>, u32>::new();
        let state_population = states.len();
        if state_population == 0 || state_population > u32::MAX as usize {
            return Err(NativeGranularPotentialError::Wire);
        }
        // Preserve the complete causal-state incidence while severing the developmental state
        // labels.  A state's predecessor port and restriction were source-chart coordinates;
        // its support, multiplicity, outgoing addressed spans, and target joins are the native
        // future-consequence structure required by later successor words.
        let states = states
            .into_iter()
            .map(|state| {
                let state_factors = developmental_supports
                    .get(state.support as usize)
                    .cloned()
                    .ok_or(NativeGranularPotentialError::Wire)?;
                let support = intern_support(state_factors, &mut supports, &mut support_lookup)?;
                let transitions = state
                    .transitions
                    .into_iter()
                    .map(|transition| {
                        if transition.target as usize >= state_population {
                            return Err(NativeGranularPotentialError::Wire);
                        }
                        let factors = developmental_supports
                            .get(transition.support as usize)
                            .cloned()
                            .ok_or(NativeGranularPotentialError::Wire)?;
                        let transition_support =
                            intern_support(factors, &mut supports, &mut support_lookup)?;
                        Ok(GranularPortTransition {
                            port: transition.port,
                            target: transition.target,
                            recurrence_multiplicity: transition.recurrence_multiplicity,
                            support: transition_support,
                            factor_current: transition.factor_current,
                        })
                    })
                    .collect::<Result<Vec<_>, NativeGranularPotentialError>>()?;
                Ok(NativeGranularState {
                    recurrence_multiplicity: state.recurrence_multiplicity,
                    support,
                    transitions,
                })
            })
            .collect::<Result<Vec<_>, NativeGranularPotentialError>>()?;
        let factor_generators = factor_generators
            .into_iter()
            .map(|generator| NativeGranularFactorGenerator {
                generator: generator.generator,
                targets: generator.targets,
            })
            .collect();
        let mut potential = Self {
            schema: NATIVE_GRANULAR_POTENTIAL_SCHEMA.to_owned(),
            supports,
            states,
            factor_faces,
            factor_generators,
            identity_sha256: String::new(),
        };
        potential.identity_sha256 = potential.rederived_identity();
        potential.validate()?;
        Ok(potential)
    }

    pub fn boundary_port_population(&self) -> usize {
        self.states.first().map_or(0, |root| root.transitions.len())
    }

    pub fn causal_grain_population(&self) -> usize {
        self.factor_faces.len()
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeGranularPotentialError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|_| NativeGranularPotentialError::Wire)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, NativeGranularPotentialError> {
        let potential: Self =
            serde_json::from_slice(bytes).map_err(|_| NativeGranularPotentialError::Wire)?;
        potential.validate()?;
        Ok(potential)
    }

    pub fn validate(&self) -> Result<(), NativeGranularPotentialError> {
        if self.schema != NATIVE_GRANULAR_POTENTIAL_SCHEMA
            || self.supports.is_empty()
            || self.states.is_empty()
            || self.factor_faces.is_empty()
            || self.factor_generators.is_empty()
            || self.identity_sha256 != self.rederived_identity()
            || self.factor_faces.iter().enumerate().any(|(at, face)| {
                face.factor != u32::try_from(at).unwrap_or(u32::MAX)
                    || !factor_face_is_native(face)
                    || face.receiver_factors.is_empty()
                    || face
                        .receiver_factors
                        .windows(2)
                        .any(|pair| pair[0] >= pair[1])
                    || face_identity(face) != factor_identity(&face.factor_address)
            })
        {
            return Err(NativeGranularPotentialError::Wire);
        }
        if !native_factor_action_is_total(&self.factor_faces, &self.factor_generators) {
            return Err(NativeGranularPotentialError::Wire);
        }
        if self.states.len() > u32::MAX as usize
            || self
                .states
                .iter()
                .any(|state| state.recurrence_multiplicity == 0 || state.transitions.is_empty())
        {
            return Err(NativeGranularPotentialError::Wire);
        }
        for support in &self.supports {
            if support.is_empty()
                || support.windows(2).any(|pair| pair[0] >= pair[1])
                || support
                    .iter()
                    .any(|factor| *factor as usize >= self.factor_faces.len())
            {
                return Err(NativeGranularPotentialError::Wire);
            }
        }
        for state in &self.states {
            if state.support as usize >= self.supports.len()
                || state
                    .transitions
                    .windows(2)
                    .any(|pair| pair[0].port >= pair[1].port)
                || state.transitions.iter().any(|transition| {
                    transition.target as usize >= self.states.len()
                        || transition.support as usize >= self.supports.len()
                        || transition.recurrence_multiplicity == 0
                        || !self
                            .supports
                            .get(transition.support as usize)
                            .is_some_and(|support| {
                                factor_current_matches(
                                    &transition.factor_current,
                                    support,
                                    transition.recurrence_multiplicity,
                                    self.factor_faces.len(),
                                )
                            })
                })
            {
                return Err(NativeGranularPotentialError::Wire);
            }
        }
        Ok(())
    }

    pub fn mount(
        &self,
    ) -> Result<MountedNativeGranularPotential<'_>, NativeGranularPotentialError> {
        self.validate()?;
        Ok(MountedNativeGranularPotential {
            states: &self.states,
            factor_generators: &self.factor_generators,
            potential_identity_sha256: &self.identity_sha256,
        })
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn factor_faces(&self) -> &[GranularFactorFace] {
        &self.factor_faces
    }

    /// Return the complete common receiver chart of the native factor population for one-time
    /// resident mounting. Receiver identifiers and observations remain opaque equality faces.
    pub(super) fn resident_factor_receiver_chart(
        &self,
    ) -> Result<(Vec<u64>, Vec<u64>), NativeGranularPotentialError> {
        self.validate()?;
        let first = self
            .factor_faces
            .first()
            .ok_or(NativeGranularPotentialError::Wire)?;
        let receiver_ids = first
            .receiver_factors
            .iter()
            .map(|receiver| receiver.receiver.0)
            .collect::<Vec<_>>();
        if receiver_ids.is_empty() || receiver_ids.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(NativeGranularPotentialError::Wire);
        }
        let mut observations =
            Vec::with_capacity(self.factor_faces.len().saturating_mul(receiver_ids.len()));
        for (factor, face) in self.factor_faces.iter().enumerate() {
            if face.factor as usize != factor
                || face.receiver_factors.len() != receiver_ids.len()
                || face
                    .receiver_factors
                    .iter()
                    .zip(&receiver_ids)
                    .any(|(receiver, expected)| receiver.receiver.0 != *expected)
            {
                return Err(NativeGranularPotentialError::Wire);
            }
            observations.extend(
                face.receiver_factors
                    .iter()
                    .map(|receiver| receiver.observation.0),
            );
        }
        Ok((receiver_ids, observations))
    }

    /// Compile the rested granular incidence into the dense arrays required by the resident card.
    /// The dense offsets are apparatus coordinates only.  Every multiplicity is recovered from
    /// the exact root-to-boundary transition that already belongs to this native potential.
    pub(super) fn resident_constitution(
        &self,
    ) -> Result<GranularResidentConstitution, NativeGranularPotentialError> {
        self.validate()?;
        let factor_population = self.factor_faces.len();
        let mut factor_capacity = vec![0_u64; factor_population];
        let cell_population = self
            .states
            .iter()
            .try_fold(0_usize, |sum, state| {
                sum.checked_add(state.transitions.len())
            })
            .ok_or(NativeGranularPotentialError::Extent)?;
        let mut cell_offsets = Vec::with_capacity(cell_population.saturating_add(1));
        let mut cell_factors = Vec::new();
        let mut cell_multiplicities = Vec::new();
        let mut cell_total_mass = Vec::with_capacity(cell_population);
        cell_offsets.push(0_u64);
        for state in &self.states {
            for transition in &state.transitions {
                let mut measured = 0_u64;
                for coordinate in &transition.factor_current {
                    let multiplicity = coordinate
                        .incidence
                        .to_u64()
                        .ok_or(NativeGranularPotentialError::CarrierExtent)?;
                    let factor = coordinate.factor as usize;
                    if multiplicity == 0 || factor >= factor_population {
                        return Err(NativeGranularPotentialError::Wire);
                    }
                    factor_capacity[factor] = factor_capacity[factor]
                        .checked_add(multiplicity)
                        .ok_or(NativeGranularPotentialError::CarrierExtent)?;
                    measured = measured
                        .checked_add(multiplicity)
                        .ok_or(NativeGranularPotentialError::CarrierExtent)?;
                    cell_factors.push(coordinate.factor);
                    cell_multiplicities.push(multiplicity);
                }
                if measured == 0 || measured != transition.recurrence_multiplicity {
                    return Err(NativeGranularPotentialError::Wire);
                }
                cell_total_mass.push(measured);
                cell_offsets.push(
                    u64::try_from(cell_factors.len())
                        .map_err(|_| NativeGranularPotentialError::CarrierExtent)?,
                );
            }
        }
        if cell_total_mass.is_empty() || factor_capacity.iter().any(|capacity| *capacity == 0) {
            return Err(NativeGranularPotentialError::Wire);
        }
        Ok(GranularResidentConstitution {
            factor_capacity,
            cell_offsets,
            cell_factors,
            cell_multiplicities,
            cell_total_mass,
        })
    }

    /// Reflect one complete exterior byte occurrence into the already cultivated native factor
    /// base without constituting the much larger membrane-interior receiver family.  The path is
    /// exact and retains its reconstruction DAG; no exterior byte value becomes a native factor
    /// identity.
    pub fn reflect_exterior_projective_current(
        &self,
        occurrence: &str,
        payload: &[u8],
    ) -> Result<GranularExteriorProjectiveCurrent, NativeGranularPotentialError> {
        if occurrence.is_empty() || payload.is_empty() {
            return Err(NativeGranularPotentialError::EmptyOccurrence);
        }
        let ports = std::iter::once(GranularExteriorPort::Opening)
            .chain(payload.iter().copied().map(GranularExteriorPort::Octet))
            .chain(std::iter::once(GranularExteriorPort::Closure))
            .collect::<Vec<_>>();
        self.reflect_exterior_port_path_current(
            occurrence,
            ports,
            u64::try_from(payload.len()).map_err(|_| NativeGranularPotentialError::Extent)?,
            granular_boundary_current(payload)?,
            payload.to_vec(),
        )
    }

    /// Reflect any exact exterior port path through the same cultivated incidence.  Structural
    /// boundary occurrences and octet occurrences therefore share one transducer law; neither is
    /// re-encoded as the other before native current is returned.
    fn reflect_exterior_port_path_current(
        &self,
        occurrence: &str,
        ports: Vec<GranularExteriorPort>,
        entered_octet_population: u64,
        entering_current: ExactComplexWaveCurrent,
        exact_source_fibre: Vec<u8>,
    ) -> Result<GranularExteriorProjectiveCurrent, NativeGranularPotentialError> {
        if occurrence.is_empty()
            || ports.is_empty()
            || entering_current.is_zero()
            || exact_source_fibre.is_empty()
        {
            return Err(NativeGranularPotentialError::EmptyOccurrence);
        }
        self.validate()?;
        let crossed_structural_ports = ports
            .iter()
            .filter(|port| !matches!(port, GranularExteriorPort::Octet(_)))
            .cloned()
            .collect::<Vec<_>>();
        let mounted = self.mount()?;
        let mut diagonal_chronology = Vec::<GranularNativeDiagonalCurrentStep>::new();
        let mut current = GranularPortCurrent::default();
        for (order, entering) in ports.into_iter().enumerate() {
            let order = u32::try_from(order).map_err(|_| NativeGranularPotentialError::Extent)?;
            let active_states = std::iter::once(0_u32)
                .chain(current.contexts.iter().map(|context| context.state))
                .collect::<BTreeSet<_>>();
            let mut front = BTreeSet::new();
            for source_state in active_states {
                let state = self
                    .states
                    .get(source_state as usize)
                    .ok_or(NativeGranularPotentialError::Wire)?;
                let Ok(at) = state
                    .transitions
                    .binary_search_by_key(&&entering, |transition| &transition.port)
                else {
                    continue;
                };
                let transition = &state.transitions[at];
                let admitted = source_state == 0
                    || current.contexts.iter().any(|context| {
                        context.state == source_state
                            && transport_factor_current(
                                &context.factor_current,
                                &transition.factor_current,
                            )
                            .ok()
                            .flatten()
                            .is_some()
                    });
                if admitted {
                    front.insert((
                        source_state,
                        transition.target,
                        transition.factor_current.clone(),
                    ));
                }
            }
            if front.is_empty() {
                return Err(NativeGranularPotentialError::FineInvariant(
                    "the exterior occurrence met no addressed native-state incidence".to_owned(),
                ));
            }
            diagonal_chronology.extend(
                front
                    .into_iter()
                    .map(|(source_state, target_state, factor_current)| {
                        // Developmental multiplicity is a common projective scale on the
                        // transition section.  It belongs to the cold reconstruction fibre, so
                        // the source-neutral chronology must retain only the primitive ray.  In
                        // particular, repeating one developmental occurrence cannot duplicate the
                        // hot native current.
                        let factor_current = primitive_factor_current(&factor_current)
                            .map(|(primitive, _)| primitive)?;
                        Ok(GranularNativeDiagonalCurrentStep {
                            order,
                            source_state,
                            target_state,
                            factor_current,
                        })
                    })
                    .collect::<Result<Vec<_>, NativeGranularPotentialError>>()?,
            );
            current = mounted.carry_current_sections(current, vec![entering])?;
        }
        let boundary_front = current.boundary_front.clone();
        let reconstruction_nodes = current.reconstruction_nodes;
        let contexts = current
            .contexts
            .into_iter()
            .map(|context| {
                let nodes = context
                    .reconstruction_nodes
                    .iter()
                    .map(|node| {
                        reconstruction_nodes
                            .get(*node as usize)
                            .filter(|held| held.node == *node)
                            .ok_or(NativeGranularPotentialError::Wire)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let shortest_extent = nodes
                    .iter()
                    .map(|node| node.shortest_extent)
                    .min()
                    .ok_or(NativeGranularPotentialError::Wire)?;
                let greatest_extent = nodes
                    .iter()
                    .map(|node| node.greatest_extent)
                    .max()
                    .ok_or(NativeGranularPotentialError::Wire)?;
                let path_population = nodes
                    .iter()
                    .fold(BigUint::ZERO, |sum, node| sum + &node.path_population);
                Ok(GranularExteriorProjectiveContext {
                    boundary_state: context.state,
                    quadratic_weight: context.quadratic_weight,
                    path_population,
                    shortest_extent,
                    greatest_extent,
                    factor_current: context.factor_current,
                    reconstruction_nodes: context.reconstruction_nodes,
                })
            })
            .collect::<Result<Vec<_>, NativeGranularPotentialError>>()?;
        let mut integrated = BTreeMap::<u32, BigUint>::new();
        for step in &diagonal_chronology {
            for coordinate in &step.factor_current {
                *integrated.entry(coordinate.factor).or_default() += &coordinate.incidence;
            }
        }
        let integrated_factor_current = integrated
            .into_iter()
            .filter_map(|(factor, incidence)| {
                (!incidence.is_zero()).then_some(GranularFactorCurrent { factor, incidence })
            })
            .collect::<Vec<_>>();
        let integrated_context_occurrence_population = contexts
            .iter()
            .try_fold(0_u64, |sum, context| {
                context
                    .path_population
                    .to_u64()
                    .and_then(|population| sum.checked_add(population))
            })
            .ok_or(NativeGranularPotentialError::Extent)?;
        if contexts.is_empty()
            || integrated_factor_current.is_empty()
            || diagonal_chronology.is_empty()
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the exterior occurrence returned no native factor incidence".to_owned(),
            ));
        }
        let exterior_source_sha256 = hex_sha256(&exact_source_fibre);
        let identity_sha256 = render_hex(&Sha256::digest(
            serde_json::to_vec(&(
                "soma-life.granular-exterior-projective-current.v6",
                occurrence,
                &exterior_source_sha256,
                entered_octet_population,
                &entering_current,
                &crossed_structural_ports,
                &boundary_front,
                &contexts,
                &diagonal_chronology,
                &integrated_factor_current,
                integrated_context_occurrence_population,
                &reconstruction_nodes,
                self.identity(),
            ))
            .map_err(|_| NativeGranularPotentialError::Wire)?,
        ));
        Ok(GranularExteriorProjectiveCurrent {
            schema: "soma-life.granular-exterior-projective-current.v6".to_owned(),
            exterior_occurrence: occurrence.to_owned(),
            exterior_source_sha256,
            entered_octet_population,
            entering_current,
            crossed_structural_ports,
            boundary_front,
            contexts,
            diagonal_chronology,
            integrated_factor_current,
            integrated_context_occurrence_population,
            reconstruction_nodes,
            exact_source_fibre,
            standing_potential_identity_sha256: self.identity().to_owned(),
            quadratic_population_reopens_from_source_fibre: true,
            identity_sha256,
        })
    }

    /// Cross one exterior occurrence and physically sever its reconstruction fibre from the
    /// source-neutral current admitted by the productive body.  This constructor is crate-local
    /// to the exterior apparatus; [`SourceNeutralEcologyRest`](super::SourceNeutralEcologyRest)
    /// exposes no raw-byte inference method.
    pub(super) fn cross_exterior_projective_current(
        &self,
        occurrence: &str,
        payload: &[u8],
    ) -> Result<GranularExteriorProjectivePassage, NativeGranularPotentialError> {
        let exterior = self.reflect_exterior_projective_current(occurrence, payload)?;
        Self::cross_reflected_exterior_projective_current(exterior)
    }

    /// Cross one realized exterior port as its own caused occurrence.  This is the return seam
    /// used after radiation: an opening, octet, or closure is transduced directly through the
    /// cultivated port incidence rather than being disguised as a byte string or used as a
    /// private selector.
    pub(super) fn cross_exterior_port_projective_current(
        &self,
        occurrence: &str,
        port: GranularExteriorPort,
    ) -> Result<GranularExteriorProjectivePassage, NativeGranularPotentialError> {
        let exact_source_fibre =
            serde_json::to_vec(&port).map_err(|_| NativeGranularPotentialError::Wire)?;
        let entered_octet_population = u64::from(matches!(port, GranularExteriorPort::Octet(_)));
        let entering_current = granular_exterior_port_boundary_current(&port)?;
        let exterior = self.reflect_exterior_port_path_current(
            occurrence,
            vec![port],
            entered_octet_population,
            entering_current,
            exact_source_fibre,
        )?;
        Self::cross_reflected_exterior_projective_current(exterior)
    }

    fn cross_reflected_exterior_projective_current(
        exterior: GranularExteriorProjectiveCurrent,
    ) -> Result<GranularExteriorProjectivePassage, NativeGranularPotentialError> {
        let native = exterior.native_current()?;
        let mut exterior_fibre = GranularExteriorProjectiveFibre {
            schema: "soma-life.granular-exterior-projective-fibre.v1".to_owned(),
            exterior_occurrence: exterior.exterior_occurrence,
            exterior_source_sha256: exterior.exterior_source_sha256,
            exact_source_fibre: exterior.exact_source_fibre,
            native_current_identity_sha256: native.identity_sha256.clone(),
            identity_sha256: String::new(),
        };
        exterior_fibre.identity_sha256 = hex_sha256(
            &serde_json::to_vec(&(
                exterior_fibre.schema.as_str(),
                exterior_fibre.exterior_occurrence.as_str(),
                exterior_fibre.exterior_source_sha256.as_str(),
                &exterior_fibre.exact_source_fibre,
                exterior_fibre.native_current_identity_sha256.as_str(),
            ))
            .map_err(|_| NativeGranularPotentialError::Wire)?,
        );
        Ok(GranularExteriorProjectivePassage {
            native,
            exterior_fibre,
        })
    }

    /// Return the source-neutral total generator maps in their admitted order.  The foreign
    /// realization is already absent; these targets are native continuation incidence.
    pub(super) fn receiver_history_generator_targets(&self) -> Vec<Vec<u32>> {
        self.factor_generators
            .iter()
            .map(|generator| generator.targets.clone())
            .collect()
    }

    /// Generator identities in the same addressed order as
    /// [`Self::receiver_history_generator_targets`].
    pub(super) fn receiver_history_generator_ids(&self) -> Vec<InputId> {
        self.factor_generators
            .iter()
            .map(|generator| generator.generator)
            .collect()
    }

    /// Export the complete rested boundary restriction incidence for one-time resident mounting.
    /// Transition order is the native state/port order already validated by this rest; no later
    /// occurrence selects or rebuilds its factor sections on the host.
    pub(super) fn boundary_restriction_atlas(
        &self,
    ) -> Result<ResidentBoundaryRestrictionAtlas, NativeGranularPotentialError> {
        self.validate()?;
        let universal_ports = port_population();
        let mut state_port_transition = vec![u32::MAX; self.states.len() * universal_ports];
        let transition_count = self
            .states
            .iter()
            .map(|state| state.transitions.len())
            .sum::<usize>();
        if self.states.len() > u32::MAX as usize || transition_count > u32::MAX as usize {
            return Err(NativeGranularPotentialError::Extent);
        }
        let mut transition_factor_offsets = Vec::with_capacity(transition_count + 1);
        let mut transition_targets = Vec::with_capacity(transition_count);
        let mut transition_factors = Vec::new();
        let mut transition_currents = Vec::new();
        transition_factor_offsets.push(0_u64);
        for (state_at, state) in self.states.iter().enumerate() {
            for transition in &state.transitions {
                let transition_at = transition_factor_offsets.len() - 1;
                state_port_transition[state_at * universal_ports + port_index(&transition.port)] =
                    transition_at as u32;
                transition_targets.push(transition.target);
                transition_factors.extend(
                    transition
                        .factor_current
                        .iter()
                        .map(|coordinate| coordinate.factor),
                );
                transition_currents.extend(
                    transition
                        .factor_current
                        .iter()
                        .map(|coordinate| coordinate.incidence.clone()),
                );
                transition_factor_offsets.push(
                    u64::try_from(transition_factors.len())
                        .map_err(|_| NativeGranularPotentialError::Extent)?,
                );
            }
        }
        Ok(ResidentBoundaryRestrictionAtlas {
            state_count: self.states.len() as u32,
            universal_port_count: universal_ports as u32,
            state_port_transition,
            transition_targets,
            transition_factor_offsets,
            transition_factors,
            transition_currents,
        })
    }

    /// Reconstruct the cold addressed lineage of a current which has already crossed the complete
    /// descended generator family on the resident apparatus.  The returned current is testimony
    /// of that device passage; this method does not repeat the generator action on the host.
    pub(super) fn carry_resident_returned_front(
        &self,
        prior: GranularBoundaryEmanation,
        returned: &[GranularHigherBoundaryFace],
        transported: ResidentAddressedCurrentPassageReturn,
    ) -> Result<GranularBoundaryEmanation, NativeGranularPotentialError> {
        MountedNativeGranularPotential {
            states: &self.states,
            factor_generators: &self.factor_generators,
            potential_identity_sha256: &self.identity_sha256,
        }
        .carry_resident_returned_faces(prior, returned, transported)
    }

    /// Continue the one resident current from the exact receiver-selected
    /// `(port,generator,state)` family.  The selected passage already enacted `D_p T_g x_s` on
    /// the card; this cold return restores only its addressed reconstruction boundary and never
    /// repeats generator or restriction transport on the host.
    pub(super) fn carry_resident_generated_port_front(
        &self,
        prior: GranularBoundaryEmanation,
        returned: &[GranularHigherBoundaryFace],
        transported: &ResidentGeneratedPortCurrentPassageReturn,
    ) -> Result<GranularBoundaryEmanation, NativeGranularPotentialError> {
        MountedNativeGranularPotential {
            states: &self.states,
            factor_generators: &self.factor_generators,
            potential_identity_sha256: &self.identity_sha256,
        }
        .carry_resident_generated_port_faces(prior, returned, transported)
    }

    /// Pivot the live boundary occurrence from its one-time source family into the admitted image
    /// address. The source contexts disappear from hot anatomy immediately; their complete cold
    /// reconstruction DAG and the returned foundation receipt remain exterior testimony.
    pub(super) fn bind_resident_factored_image_foundation(
        &self,
        mut prior: GranularBoundaryEmanation,
        image: &ResidentFactoredMomentAddress,
    ) -> Result<GranularBoundaryEmanation, NativeGranularPotentialError> {
        if prior.current.contexts.is_empty()
            || prior.current.resident_image.is_some()
            || image.factor_population == 0
            || image.image_population == 0
        {
            return Err(NativeGranularPotentialError::Wire);
        }
        if prior.branches.is_empty()
            || prior.current.boundary_front.is_empty()
            || prior.current.reconstruction_nodes.is_empty()
        {
            return Err(NativeGranularPotentialError::Wire);
        }
        // Founding changes the current representation, not its causal boundary.  The complete
        // `(source state <- transition -> target state)` branch population already returned from
        // ingress and therefore remains the only lawful aperture for the first image order.
        prior.current.contexts.clear();
        prior.current.resident_image = Some(image.clone());
        Ok(prior)
    }

    /// Recover the complete addressed span of one device-returned support face from the rested
    /// native incidence.  The exterior port spelling is only a coordinate; uniqueness is proved
    /// against the source state's admitted transition population.
    pub(super) fn addressed_successor_face(
        &self,
        source_state: u32,
        port: GranularExteriorPort,
        generator: InputId,
    ) -> Result<GranularAddressedHigherBoundaryFace, NativeGranularPotentialError> {
        let source = self
            .states
            .get(source_state as usize)
            .ok_or(NativeGranularPotentialError::Wire)?;
        if !self
            .factor_generators
            .iter()
            .any(|admitted| admitted.generator == generator)
        {
            return Err(NativeGranularPotentialError::Wire);
        }
        let mut targets = source
            .transitions
            .iter()
            .filter(|transition| transition.port == port)
            .map(|transition| transition.target);
        let target_state = targets.next().ok_or(NativeGranularPotentialError::Wire)?;
        if targets.next().is_some() {
            return Err(NativeGranularPotentialError::FineInvariant(
                "one source/port incidence returned plural target legs".to_owned(),
            ));
        }
        Ok(GranularAddressedHigherBoundaryFace {
            source_state,
            port,
            generator,
            target_state,
        })
    }

    /// Validate the complete returned generator/port boundary before the resident current is
    /// mutated.  This makes an absent face an obstruction rather than a partially enacted deed.
    pub(super) fn validate_resident_returned_front(
        &self,
        returned: &[GranularHigherBoundaryFace],
    ) -> Result<(), NativeGranularPotentialError> {
        validate_resident_returned_face_boundary(&self.states, &self.factor_generators, returned)
    }

    fn rederived_identity(&self) -> String {
        let mut digest = Sha256::new();
        digest.update(NATIVE_GRANULAR_POTENTIAL_SCHEMA.as_bytes());
        digest.update((self.supports.len() as u64).to_le_bytes());
        for support in &self.supports {
            digest.update((support.len() as u64).to_le_bytes());
            for factor in support {
                digest.update(factor.to_le_bytes());
            }
        }
        digest.update((self.states.len() as u64).to_le_bytes());
        for state in &self.states {
            digest.update(state.recurrence_multiplicity.to_le_bytes());
            digest.update(state.support.to_le_bytes());
            digest.update((state.transitions.len() as u64).to_le_bytes());
            for transition in &state.transitions {
                digest_port(&mut digest, Some(&transition.port));
                digest.update(transition.target.to_le_bytes());
                digest.update(transition.recurrence_multiplicity.to_le_bytes());
                digest.update(transition.support.to_le_bytes());
                digest.update((transition.factor_current.len() as u64).to_le_bytes());
                for coordinate in &transition.factor_current {
                    digest.update(coordinate.factor.to_le_bytes());
                    let limbs = coordinate.incidence.to_u32_digits();
                    digest.update((limbs.len() as u64).to_le_bytes());
                    for limb in limbs {
                        digest.update(limb.to_le_bytes());
                    }
                }
            }
        }
        for face in &self.factor_faces {
            digest.update(face.factor.to_le_bytes());
            digest.update((face.factor_address.len() as u64).to_le_bytes());
            digest.update(face.factor_address.as_bytes());
            digest.update(face.native.0.to_le_bytes());
            digest.update((face.receiver_factors.len() as u64).to_le_bytes());
            for receiver in &face.receiver_factors {
                digest.update(receiver.receiver.0.to_le_bytes());
                digest.update(receiver.observation.0.to_le_bytes());
            }
            digest.update(face.receiver_schema.to_le_bytes());
            digest.update((face.receiver_words.len() as u64).to_le_bytes());
            for word in &face.receiver_words {
                digest.update(word.to_le_bytes());
            }
        }
        digest.update((self.factor_generators.len() as u64).to_le_bytes());
        for generator in &self.factor_generators {
            digest.update(generator.generator.0.to_le_bytes());
            digest.update((generator.targets.len() as u64).to_le_bytes());
            for target in &generator.targets {
                digest.update(target.to_le_bytes());
            }
        }
        render_hex(&digest.finalize())
    }
}

impl GranularExteriorProjectiveCurrent {
    fn native_current(
        &self,
    ) -> Result<GranularNativeProjectiveCurrent, NativeGranularPotentialError> {
        let mut native = GranularNativeProjectiveCurrent {
            schema: "soma-life.granular-native-projective-current.v7".to_owned(),
            entered_octet_population: self.entered_octet_population,
            entering_current: self.entering_current.clone(),
            crossed_structural_ports: self.crossed_structural_ports.clone(),
            boundary_front: self.boundary_front.clone(),
            contexts: self.contexts.clone(),
            diagonal_chronology: self.diagonal_chronology.clone(),
            integrated_factor_current: self.integrated_factor_current.clone(),
            integrated_context_occurrence_population: self.integrated_context_occurrence_population,
            reconstruction_nodes: self.reconstruction_nodes.clone(),
            standing_potential_identity_sha256: self.standing_potential_identity_sha256.clone(),
            identity_sha256: String::new(),
        };
        native.identity_sha256 = native.rederived_identity()?;
        native.validate()?;
        Ok(native)
    }
}

impl GranularNativeProjectiveCurrent {
    fn validate(&self) -> Result<(), NativeGranularPotentialError> {
        if self.schema != "soma-life.granular-native-projective-current.v7"
            || (self.entered_octet_population == 0 && self.crossed_structural_ports.is_empty())
            || self.entering_current.is_zero()
            || self.boundary_front.is_empty()
            || self
                .boundary_front
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || self.contexts.is_empty()
            || self.contexts.windows(2).any(|pair| {
                (&pair[0].boundary_state, &pair[0].factor_current)
                    >= (&pair[1].boundary_state, &pair[1].factor_current)
            })
            || self
                .contexts
                .iter()
                .any(|context| !self.boundary_front.contains(&context.boundary_state))
            || self.contexts.iter().any(|context| {
                context.quadratic_weight.is_zero() || context.path_population.is_zero()
            })
            || self.diagonal_chronology.is_empty()
            || self.diagonal_chronology.first().map(|step| step.order) != Some(0)
            || self
                .diagonal_chronology
                .windows(2)
                .any(|pair| pair[0].order > pair[1].order || pair[1].order > pair[0].order + 1)
            || self.integrated_factor_current.is_empty()
            || self.integrated_context_occurrence_population == 0
            || self.reconstruction_nodes.is_empty()
            || self
                .reconstruction_nodes
                .iter()
                .enumerate()
                .any(|(at, node)| {
                    node.node as usize != at
                        || node.quadratic_projective_mass.is_zero()
                        || node.removed_common_quadratic_scale.is_zero()
                        || node.path_population.is_zero()
                        || node.incoming.is_empty()
                        || node.incoming.iter().any(|edge| {
                            edge.transport_projective_scale.is_zero()
                                || edge.predecessor.is_some_and(|prior| prior as usize >= at)
                        })
                })
            || !is_digest(&self.standing_potential_identity_sha256)
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the source-neutral projective current lost its complete native incidence"
                    .to_owned(),
            ));
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeGranularPotentialError> {
        serde_json::to_vec(&(
            "soma-life.granular-native-projective-current.v7",
            self.entered_octet_population,
            &self.entering_current,
            &self.crossed_structural_ports,
            &self.boundary_front,
            &self.contexts,
            &self.diagonal_chronology,
            &self.integrated_factor_current,
            self.integrated_context_occurrence_population,
            &self.reconstruction_nodes,
            &self.standing_potential_identity_sha256,
        ))
        .map(|bytes| hex_sha256(&bytes))
        .map_err(|_| NativeGranularPotentialError::Wire)
    }
}

impl GranularBoundaryEmanation {
    /// The exact exterior receiver/path coordinate entering the next native radiation deed.
    /// This is apparatus-visible testimony for the declared receiver quotient; it is not native
    /// particle identity and never selects a continuation.
    pub(super) fn boundary_front(&self) -> &[u32] {
        &self.current.boundary_front
    }

    pub(super) fn resident_factored_image(&self) -> Option<&ResidentFactoredMomentAddress> {
        self.current.resident_image.as_ref()
    }

    pub(super) fn causal_profile(&self) -> (usize, usize, usize, usize, usize, usize, usize) {
        let active_nodes = self
            .current
            .contexts
            .iter()
            .map(|context| context.reconstruction_nodes.len())
            .sum();
        let greatest_mass_bits = self
            .current
            .reconstruction_nodes
            .iter()
            .map(|node| node.quadratic_projective_mass.bits() as usize)
            .max()
            .unwrap_or(0);
        let reconstruction_reference_population = self
            .branches
            .iter()
            .map(|branch| branch.reconstruction_nodes.len())
            .sum();
        (
            self.current.contexts.len(),
            self.current.boundary_front.len(),
            self.current.reconstruction_nodes.len(),
            active_nodes,
            self.branches.len(),
            reconstruction_reference_population,
            greatest_mass_bits,
        )
    }

    pub(super) fn reconstruction_dag(&self) -> &[GranularReconstructionNode] {
        &self.current.reconstruction_nodes
    }
}
