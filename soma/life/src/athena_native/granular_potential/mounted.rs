fn digest_port(digest: &mut Sha256, port: Option<&GranularExteriorPort>) {
    match port {
        None => digest.update([0, 0]),
        Some(GranularExteriorPort::Opening) => digest.update([1, 0]),
        Some(GranularExteriorPort::Octet(octet)) => digest.update([2, *octet]),
        Some(GranularExteriorPort::Closure) => digest.update([3, 0]),
    }
}

impl MountedNativeGranularPotential<'_> {
    /// Admit the exact primitive-ray quotient of one exterior occurrence as the hot boundary
    /// current. The quotient removes only path-population and common-scale coordinates which the
    /// supplied [`GranularExteriorProjectiveCurrent`] can reconstruct from its retained source
    /// fibre and this standing potential. It does not select factors, history cells, words, or a
    /// response surface.
    pub(super) fn receive_projective_returning(
        &self,
        projective: &GranularExteriorProjectiveCurrent,
    ) -> Result<(GranularBoundaryEmanation, Vec<GranularExteriorPort>), NativeGranularPotentialError>
    {
        if projective.contexts.is_empty()
            || projective.boundary_front.is_empty()
            || projective.entered_octet_population == 0
            || projective.exact_source_fibre.len() as u64 != projective.entered_octet_population
            || projective
                .boundary_front
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || projective
                .boundary_front
                .iter()
                .any(|state| *state as usize >= self.states.len())
            || !projective.quadratic_population_reopens_from_source_fibre
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the projective ingress lost its complete source reconstruction fibre".to_owned(),
            ));
        }
        self.receive_native_projective_returning(&projective.native_current()?)
    }

    /// Admit only the source-neutral current after the exterior reconstruction fibre has been
    /// severed.  This is the productive UAR passage; no source digest, locator, text, or byte fibre
    /// is reachable from the method.
    pub(super) fn receive_native_projective_returning(
        &self,
        projective: &GranularNativeProjectiveCurrent,
    ) -> Result<(GranularBoundaryEmanation, Vec<GranularExteriorPort>), NativeGranularPotentialError>
    {
        projective.validate()?;
        if projective.standing_potential_identity_sha256 != self.potential_identity_sha256
            || projective
                .boundary_front
                .iter()
                .any(|state| *state as usize >= self.states.len())
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the source-neutral ingress left its admitted potential".to_owned(),
            ));
        }
        let factor_population = self
            .factor_generators
            .first()
            .map(|generator| generator.targets.len())
            .ok_or(NativeGranularPotentialError::Wire)?;
        // The addressed chronology and reconstruction DAG are cold exact testimony.  Productive
        // ingress preserves the complete `(state, factor current)` terminal section and its node
        // fibres; it does not rebuild them as unrelated one-node roots.
        for step in &projective.diagonal_chronology {
            if step.source_state as usize >= self.states.len()
                || step.target_state as usize >= self.states.len()
                || step.factor_current.is_empty()
                || step
                    .factor_current
                    .windows(2)
                    .any(|pair| pair[0].factor >= pair[1].factor)
                || step.factor_current.iter().any(|coordinate| {
                    coordinate.incidence.is_zero()
                        || coordinate.factor as usize >= factor_population
                })
            {
                return Err(NativeGranularPotentialError::FineInvariant(
                    "the native chronology carried a malformed addressed diagonal current"
                        .to_owned(),
                ));
            }
        }
        let mut reconstruction_fibre = BTreeSet::new();
        for context in &projective.contexts {
            if context.reconstruction_nodes.is_empty()
                || context.reconstruction_nodes.iter().any(|node| {
                    projective
                        .reconstruction_nodes
                        .get(*node as usize)
                        .is_none_or(|held| held.node != *node)
                })
            {
                return Err(NativeGranularPotentialError::FineInvariant(
                    "the native context lost its addressed reconstruction fibre".to_owned(),
                ));
            }
            reconstruction_fibre.extend(context.reconstruction_nodes.iter().copied());
        }
        if reconstruction_fibre.is_empty() {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the integrated native current lost its reconstruction fibre".to_owned(),
            ));
        }
        // Preserve every distinct terminal `(state, factor current)` section.  These are the
        // native future-consequence quotient axes; collapsing them into an integrated current
        // would erase distinct successor boundaries and turn the reconstruction cover into a
        // fabricated one-node root.  The source fibre is still severed: only the exact native
        // sections and their addressed cold nodes cross this seam.
        let contexts = projective
            .contexts
            .iter()
            .map(|context| GranularCausalContext {
                state: context.boundary_state,
                factor_current: context.factor_current.clone(),
                quadratic_weight: context.quadratic_weight.clone(),
                reconstruction_nodes: context.reconstruction_nodes.clone(),
            })
            .collect::<Vec<_>>();
        if holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace {
            let states = contexts
                .iter()
                .map(|context| context.state)
                .collect::<BTreeSet<_>>();
            eprintln!(
                "source-neutral-ingress chronology_steps={} terminal_axes={} boundary_states={:?}",
                projective.diagonal_chronology.len(),
                1,
                states,
            );
        }
        let emanation = self.emanate_current(
            GranularPortCurrent {
                contexts,
                resident_image: None,
                boundary_front: projective.boundary_front.clone(),
                reconstruction_nodes: projective.reconstruction_nodes.clone(),
            },
            usize::try_from(projective.entered_octet_population)
                .map_err(|_| NativeGranularPotentialError::Extent)?,
        )?;
        Ok((emanation, projective.crossed_structural_ports.clone()))
    }

    /// Reopen the exact sparse restriction family for an equality receiver.  Production uses the
    /// resident atlas; this path is deliberately retained as cold direct testimony and never
    /// selects or changes the continuing front.
    pub(super) fn direct_boundary_restrictions(
        &self,
        front: &ResidentBoundaryRestrictionFront,
    ) -> Result<Vec<ResidentQuadraticMomentRestriction>, NativeGranularPotentialError> {
        if front.boundary_states.is_empty()
            || front.universal_ports.is_empty()
            || front
                .boundary_states
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || front
                .boundary_states
                .iter()
                .any(|state| *state as usize >= self.states.len())
            || front
                .universal_ports
                .iter()
                .any(|port| *port as usize >= port_population())
        {
            return Err(NativeGranularPotentialError::Wire);
        }
        let mut restrictions = Vec::new();
        for (local_port, universal_port) in front.universal_ports.iter().copied().enumerate() {
            let port =
                indexed_port(universal_port as usize).ok_or(NativeGranularPotentialError::Wire)?;
            let mut port_population = 0_usize;
            for state in &front.boundary_states {
                let transition = self.states[*state as usize]
                    .transitions
                    .iter()
                    .find(|transition| transition.port == port);
                let Some(transition) = transition else {
                    continue;
                };
                restrictions.push(ResidentQuadraticMomentRestriction {
                    port: u32::try_from(local_port)
                        .map_err(|_| NativeGranularPotentialError::Extent)?,
                    factor_current: transition
                        .factor_current
                        .iter()
                        .map(|coordinate| (coordinate.factor, coordinate.incidence.clone()))
                        .collect(),
                });
                port_population += 1;
            }
            if port_population == 0 {
                return Err(NativeGranularPotentialError::Wire);
            }
        }
        Ok(restrictions)
    }

    pub(super) fn quadratic_moment_current_axes(
        &self,
        emanation: &GranularBoundaryEmanation,
    ) -> Result<GranularQuadraticMomentCurrentAxes, NativeGranularPotentialError> {
        let contexts = emanation
            .current
            .contexts
            .iter()
            .map(|context| {
                if context.quadratic_weight == BigUint::from(0_u8) {
                    return Err(NativeGranularPotentialError::Wire);
                }
                Ok(GranularQuadraticMomentContextAxis {
                    boundary_state: context.state,
                    quadratic_weight: context.quadratic_weight.clone(),
                    factor_current: context.factor_current.clone(),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        if contexts.is_empty() {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the quadratic receiver lost its native current axes".to_owned(),
            ));
        }
        Ok(GranularQuadraticMomentCurrentAxes {
            contexts,
            generator_targets: self
                .factor_generators
                .iter()
                .flat_map(|generator| generator.targets.iter().copied())
                .collect(),
            generator_count: u32::try_from(self.factor_generators.len())
                .map_err(|_| NativeGranularPotentialError::Extent)?,
        })
    }

    pub fn receive_open(
        &self,
        payload: &[u8],
    ) -> Result<GranularBoundaryEmanation, NativeGranularPotentialError> {
        if payload.is_empty() {
            return Err(NativeGranularPotentialError::EmptyOccurrence);
        }
        let mut current = GranularPortCurrent::default();
        current = self.carry_current(current, GranularExteriorPort::Opening)?;
        for octet in payload {
            current = self.carry_current(current, GranularExteriorPort::Octet(*octet))?;
        }
        self.emanate_current(current, payload.len())
    }

    pub fn receive_closed(
        &self,
        payload: &[u8],
    ) -> Result<GranularBoundaryEmanation, NativeGranularPotentialError> {
        let open = self.receive_open(payload)?;
        self.carry_port(&open, GranularExteriorPort::Closure)
    }

    /// Cross the caused closure-to-opening return seam when it is the unique structural
    /// continuation. The opening is apparatus incidence rather than emitted payload and is never
    /// presented as a generated octet.
    pub fn receive_returning(
        &self,
        payload: &[u8],
    ) -> Result<(GranularBoundaryEmanation, Vec<GranularExteriorPort>), NativeGranularPotentialError>
    {
        let closed = self.receive_closed(payload)?;
        let crossed = vec![GranularExteriorPort::Closure];
        if closed.branches.len() == 1 && closed.branches[0].port == GranularExteriorPort::Opening {
            let opened = self.carry_port(&closed, GranularExteriorPort::Opening)?;
            return Ok((
                self.rebase_closed_ingress_to_native_boundary(opened)?,
                vec![GranularExteriorPort::Closure, GranularExteriorPort::Opening],
            ));
        }
        Ok((
            self.rebase_closed_ingress_to_native_boundary(closed)?,
            crossed,
        ))
    }

    /// Condense a completed exterior path into its native causal-factor section.  Equality here
    /// is equality of the complete addressed continuation coordinate: terminal state and factor
    /// section.  The reconstruction DAG retains the paths which realize that coordinate.  Two
    /// equal factor sections at different terminal states are not one native context, because
    /// their admitted successor families can differ.
    fn rebase_closed_ingress_to_native_boundary(
        &self,
        prior: GranularBoundaryEmanation,
    ) -> Result<GranularBoundaryEmanation, NativeGranularPotentialError> {
        let entered = usize::try_from(prior.entered_octet_population)
            .map_err(|_| NativeGranularPotentialError::Extent)?;
        let GranularPortCurrent {
            contexts,
            boundary_front: _,
            resident_image: _,
            reconstruction_nodes,
        } = prior.current;
        let mut native_sections =
            BTreeMap::<(u32, Vec<GranularFactorCurrent>), (BigUint, Vec<u32>)>::new();
        let mut boundary_front = BTreeSet::new();
        for context in contexts {
            self.states
                .get(context.state as usize)
                .ok_or(NativeGranularPotentialError::Wire)?;
            boundary_front.insert(context.state);
            let section = native_sections
                .entry((context.state, context.factor_current))
                .or_default();
            section.0 += context.quadratic_weight;
            section.1.extend(context.reconstruction_nodes);
        }
        let contexts = native_sections
            .into_iter()
            .map(
                |((state, factor_current), (quadratic_weight, mut reconstruction_nodes))| {
                    reconstruction_nodes.sort_unstable();
                    reconstruction_nodes.dedup();
                    GranularCausalContext {
                        state,
                        factor_current,
                        quadratic_weight,
                        reconstruction_nodes,
                    }
                },
            )
            .collect::<Vec<_>>();
        if contexts.is_empty() {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the closed exterior ingress had no native factor section".to_owned(),
            ));
        }
        self.emanate_current(
            GranularPortCurrent {
                contexts,
                resident_image: None,
                boundary_front: boundary_front.into_iter().collect(),
                reconstruction_nodes,
            },
            entered,
        )
    }

    pub fn carry_port(
        &self,
        prior: &GranularBoundaryEmanation,
        returned_port: GranularExteriorPort,
    ) -> Result<GranularBoundaryEmanation, NativeGranularPotentialError> {
        let is_octet = matches!(&returned_port, GranularExteriorPort::Octet(_));
        let current = self.carry_current(prior.current.clone(), returned_port)?;
        let entered = usize::try_from(prior.entered_octet_population)
            .map_err(|_| NativeGranularPotentialError::Extent)?
            .checked_add(usize::from(is_octet))
            .ok_or(NativeGranularPotentialError::Extent)?;
        self.emanate_current(current, entered)
    }

    /// Advance one genuinely returned Athena phase front through the complete descended generator
    /// action. The unique generator family acts once on every current section. Exterior ports are
    /// retained together on the reconstruction edge; they never become native transitions or
    /// multiply the current population. Exterior ingress and structural seams use `carry_port`.
    #[cfg(test)]
    fn carry_returned_faces(
        &self,
        prior: GranularBoundaryEmanation,
        returned: &[GranularHigherBoundaryFace],
    ) -> Result<GranularBoundaryEmanation, NativeGranularPotentialError> {
        if returned.is_empty() {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the returned higher face fibre is empty".to_owned(),
            ));
        }
        if returned.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the returned higher phase front repeats or reorders a face".to_owned(),
            ));
        }
        let ports = returned
            .iter()
            .map(|face| face.port.clone())
            .collect::<BTreeSet<_>>();
        let generator_ids = returned
            .iter()
            .map(|face| face.generator)
            .collect::<BTreeSet<_>>();
        let generators = generator_ids
            .into_iter()
            .map(|generator| {
                self.factor_generators
                    .binary_search_by_key(&generator, |held| held.generator)
                    .ok()
                    .and_then(|at| self.factor_generators.get(at))
                    .ok_or_else(|| {
                        NativeGranularPotentialError::FineInvariant(
                            "the returned higher face named an absent generator".to_owned(),
                        )
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let entered_octet_population = prior.entered_octet_population;
        let current = self.carry_native_generator_front(prior.current, &generators, returned)?;
        if current.contexts.is_empty() {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the returned higher phase front has no transported section".to_owned(),
            ));
        }
        // A plural octet face is still one unresolved output position. Mixed structural and octet
        // faces have no exact octet extent and therefore do not change this receiver shadow.
        let is_octet_position = ports
            .iter()
            .all(|port| matches!(port, GranularExteriorPort::Octet(_)));
        let entered = usize::try_from(entered_octet_population)
            .map_err(|_| NativeGranularPotentialError::Extent)?
            .checked_add(usize::from(is_octet_position))
            .ok_or(NativeGranularPotentialError::Extent)?;
        self.emanate_current(current, entered)
    }

    /// Continue from the exact dynamic current returned by the resident apparatus.  The complete
    /// source/generator-to-target incidence becomes the reconstruction boundary map.  In
    /// particular, no host generator multiplication, projective primitive reduction, or second
    /// condensation is permitted here.
    fn carry_resident_returned_faces(
        &self,
        prior: GranularBoundaryEmanation,
        returned: &[GranularHigherBoundaryFace],
        transported: ResidentAddressedCurrentPassageReturn,
    ) -> Result<GranularBoundaryEmanation, NativeGranularPotentialError> {
        validate_resident_returned_face_boundary(self.states, self.factor_generators, returned)?;
        let passage = transported.passage;
        let source_matches = passage.source.len() == prior.current.contexts.len()
            && passage
                .source
                .iter()
                .zip(&prior.current.contexts)
                .all(|(source, context)| {
                    source.quadratic_weight == context.quadratic_weight
                        && source.factor_current.len() == context.factor_current.len()
                        && source
                            .factor_current
                            .iter()
                            .zip(&context.factor_current)
                            .all(|((factor, coefficient), coordinate)| {
                                *factor == coordinate.factor && *coefficient == coordinate.incidence
                            })
                });
        if passage.target.is_empty()
            || !source_matches
            || passage.generator_population as usize != self.factor_generators.len()
            || passage.occurrences.len()
                != passage
                    .source
                    .len()
                    .checked_mul(passage.generator_population as usize)
                    .ok_or(NativeGranularPotentialError::Extent)?
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the resident returned current lost its dynamic boundary map".to_owned(),
            ));
        }
        let ports = returned
            .iter()
            .map(|face| face.port.clone())
            .collect::<BTreeSet<_>>();
        let entered_octet_population = prior.entered_octet_population;
        let GranularPortCurrent {
            contexts: source_contexts,
            boundary_front: _,
            resident_image: _,
            reconstruction_nodes,
        } = prior.current;
        let mut target_keys = BTreeSet::new();
        let mut candidates = Vec::with_capacity(passage.target.len());
        for (target_at, context) in passage.target.into_iter().enumerate() {
            let factor_current = context
                .factor_current
                .into_iter()
                .map(|(factor, incidence)| GranularFactorCurrent { factor, incidence })
                .collect::<Vec<_>>();
            if factor_current.is_empty()
                || factor_current
                    .windows(2)
                    .any(|pair| pair[0].factor >= pair[1].factor)
                || factor_current
                    .iter()
                    .any(|coordinate| coordinate.incidence == BigUint::from(0_u8))
                || context.quadratic_weight == BigUint::from(0_u8)
            {
                return Err(NativeGranularPotentialError::Wire);
            }
            let target_key = (0, factor_current);
            if !target_keys.insert(target_key.clone()) || target_at > u32::MAX as usize {
                return Err(NativeGranularPotentialError::Wire);
            }
            candidates.push((
                target_key,
                GranularCarriedCandidate {
                    quadratic_weight: context.quadratic_weight,
                    reconstruction_edges: Vec::new(),
                },
            ));
        }
        for edge in passage.occurrences {
            let source = source_contexts
                .get(edge.source_section as usize)
                .ok_or(NativeGranularPotentialError::Wire)?;
            let generator = self
                .factor_generators
                .get(edge.generator as usize)
                .ok_or(NativeGranularPotentialError::Wire)?;
            let generator_faces = returned
                .iter()
                .filter(|face| face.generator == generator.generator)
                .cloned()
                .collect::<Vec<_>>();
            if source.reconstruction_nodes.is_empty() || generator_faces.is_empty() {
                return Err(NativeGranularPotentialError::Wire);
            }
            let (_, candidate) = candidates
                .get_mut(edge.target_section as usize)
                .ok_or(NativeGranularPotentialError::Wire)?;
            for predecessor in &source.reconstruction_nodes {
                candidate
                    .reconstruction_edges
                    .push(GranularReconstructionEdge {
                        predecessor: Some(*predecessor),
                        entering_port: None,
                        returned_higher_faces: generator_faces.clone(),
                        transport_projective_scale: BigUint::from(1_u8),
                    });
            }
        }

        let boundary_front = returned_target_boundary(&prior.branches, returned)?;
        let current =
            finalize_resident_carried_current(reconstruction_nodes, candidates, boundary_front)?;
        let is_octet_position = ports
            .iter()
            .all(|port| matches!(port, GranularExteriorPort::Octet(_)));
        let entered = usize::try_from(entered_octet_population)
            .map_err(|_| NativeGranularPotentialError::Extent)?
            .checked_add(usize::from(is_octet_position))
            .ok_or(NativeGranularPotentialError::Extent)?;
        self.emanate_current(current, entered)
    }

    fn carry_resident_generated_port_faces(
        &self,
        prior: GranularBoundaryEmanation,
        returned: &[GranularHigherBoundaryFace],
        transported: &ResidentGeneratedPortCurrentPassageReturn,
    ) -> Result<GranularBoundaryEmanation, NativeGranularPotentialError> {
        validate_resident_returned_face_boundary(self.states, self.factor_generators, returned)?;
        let passage = &transported.passage;
        let source_matches = passage.source.len() == prior.current.contexts.len()
            && passage
                .source
                .iter()
                .zip(&prior.current.contexts)
                .all(|(source, context)| {
                    source.boundary_state == Some(context.state)
                        && source.quadratic_weight == context.quadratic_weight
                        && source.factor_current.len() == context.factor_current.len()
                        && source
                            .factor_current
                            .iter()
                            .zip(&context.factor_current)
                            .all(|((factor, coefficient), coordinate)| {
                                *factor == coordinate.factor && *coefficient == coordinate.incidence
                            })
                });
        let expected_occurrence_population = passage
            .source
            .iter()
            .filter_map(|source| source.boundary_state)
            .map(|source_state| {
                passage
                    .slots
                    .iter()
                    .filter(|slot| slot.source_boundary_state == source_state)
                    .count()
            })
            .try_fold(0_usize, |sum, extent| sum.checked_add(extent))
            .ok_or(NativeGranularPotentialError::Extent)?;
        if passage.target.is_empty()
            || passage.slots.is_empty()
            || !source_matches
            || passage.generator_population as usize != self.factor_generators.len()
            || passage.occurrences.len() != expected_occurrence_population
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the selected resident current lost its addressed generated-port boundary"
                    .to_owned(),
            ));
        }

        let visible_ports = prior
            .branches
            .iter()
            .map(|branch| branch.port.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if passage.port_population as usize != visible_ports.len() {
            return Err(NativeGranularPotentialError::Wire);
        }
        let returned_set = returned.iter().cloned().collect::<BTreeSet<_>>();
        // `slots` is the complete selected reconstruction fibre.  It deliberately retains
        // local currents annihilated by their restriction, whose occurrence has no target
        // section.  Only slots with at least one productive occurrence constitute the returned
        // higher-face front; requiring every radical slot to appear there confuses retained
        // preimage testimony with completed target incidence.
        let productive_slots = passage
            .occurrences
            .iter()
            .filter_map(|occurrence| occurrence.target_section.map(|_| occurrence.selected_slot))
            .collect::<BTreeSet<_>>();
        if productive_slots.is_empty() {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the completed resident target had no productive local-current incidence"
                    .to_owned(),
            ));
        }
        let slot_faces = passage
            .slots
            .iter()
            .map(|slot| {
                let port = visible_ports
                    .get(slot.port as usize)
                    .cloned()
                    .ok_or(NativeGranularPotentialError::Wire)?;
                let generator = self
                    .factor_generators
                    .get(slot.generator as usize)
                    .map(|generator| generator.generator)
                    .ok_or(NativeGranularPotentialError::Wire)?;
                let face = GranularHigherBoundaryFace { port, generator };
                let transition = self
                    .states
                    .get(slot.source_boundary_state as usize)
                    .ok_or(NativeGranularPotentialError::Wire)?
                    .transitions
                    .iter()
                    .find(|transition| {
                        transition.port == face.port
                            && transition.target == slot.boundary_state
                            && transition.factor_current.len() == slot.restriction.len()
                            && transition.factor_current.iter().zip(&slot.restriction).all(
                                |(coordinate, (factor, coefficient))| {
                                    coordinate.factor == *factor
                                        && coordinate.incidence == *coefficient
                                },
                            )
                    })
                    .ok_or(NativeGranularPotentialError::Wire)?;
                let _ = transition;
                Ok(face)
            })
            .collect::<Result<Vec<_>, NativeGranularPotentialError>>()?;
        let productive_faces = productive_slots
            .iter()
            .map(|slot| {
                slot_faces
                    .get(*slot as usize)
                    .cloned()
                    .ok_or(NativeGranularPotentialError::Wire)
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        if productive_faces != returned_set {
            if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
                eprintln!(
                    "generated-port-front-separator productive={:?} returned={:?}",
                    productive_faces, returned_set,
                );
            }
            return Err(NativeGranularPotentialError::FineInvariant(
                "the selected resident slots did not cover the returned higher-face front"
                    .to_owned(),
            ));
        }

        let ports = returned
            .iter()
            .map(|face| face.port.clone())
            .collect::<BTreeSet<_>>();
        let entered_octet_population = prior.entered_octet_population;
        let GranularPortCurrent {
            contexts: source_contexts,
            boundary_front: _,
            resident_image: _,
            reconstruction_nodes,
        } = prior.current;
        let expected_boundary = passage
            .target
            .iter()
            .map(|target| {
                target.boundary_state.ok_or_else(|| {
                    NativeGranularPotentialError::FineInvariant(
                        "a completed resident target lost its causal-state address".to_owned(),
                    )
                })
            })
            .collect::<Result<BTreeSet<_>, _>>()?
            .into_iter()
            .collect::<Vec<_>>();
        if expected_boundary.is_empty() {
            return Err(NativeGranularPotentialError::Wire);
        }
        let mut target_keys = BTreeSet::new();
        let mut candidates = Vec::with_capacity(passage.target.len());
        for (target_at, context) in passage.target.iter().enumerate() {
            let state = context.boundary_state.ok_or_else(|| {
                NativeGranularPotentialError::FineInvariant(
                    "a selected resident target lost its causal-state address".to_owned(),
                )
            })?;
            if !expected_boundary.contains(&state) {
                return Err(NativeGranularPotentialError::FineInvariant(
                    "a selected resident target escaped its returned boundary".to_owned(),
                ));
            }
            let factor_current = context
                .factor_current
                .iter()
                .map(|(factor, incidence)| GranularFactorCurrent {
                    factor: *factor,
                    incidence: incidence.clone(),
                })
                .collect::<Vec<_>>();
            if factor_current.is_empty()
                || factor_current
                    .windows(2)
                    .any(|pair| pair[0].factor >= pair[1].factor)
                || factor_current
                    .iter()
                    .any(|coordinate| coordinate.incidence.is_zero())
                || context.quadratic_weight.is_zero()
            {
                return Err(NativeGranularPotentialError::Wire);
            }
            let target_key = (state, factor_current);
            if !target_keys.insert(target_key.clone()) || target_at > u32::MAX as usize {
                return Err(NativeGranularPotentialError::Wire);
            }
            candidates.push((
                target_key,
                GranularCarriedCandidate {
                    quadratic_weight: context.quadratic_weight.clone(),
                    reconstruction_edges: Vec::new(),
                },
            ));
        }
        for edge in &passage.occurrences {
            let source = source_contexts
                .get(edge.source_section as usize)
                .ok_or(NativeGranularPotentialError::Wire)?;
            let face = slot_faces
                .get(edge.selected_slot as usize)
                .cloned()
                .ok_or(NativeGranularPotentialError::Wire)?;
            let Some(target_section) = edge.target_section else {
                continue;
            };
            if source.reconstruction_nodes.is_empty() {
                return Err(NativeGranularPotentialError::Wire);
            }
            let (_, candidate) = candidates
                .get_mut(target_section as usize)
                .ok_or(NativeGranularPotentialError::Wire)?;
            for predecessor in &source.reconstruction_nodes {
                candidate
                    .reconstruction_edges
                    .push(GranularReconstructionEdge {
                        predecessor: Some(*predecessor),
                        entering_port: None,
                        returned_higher_faces: vec![face.clone()],
                        transport_projective_scale: BigUint::from(1_u8),
                    });
            }
        }

        let current = finalize_resident_junction_current(
            reconstruction_nodes,
            candidates,
            expected_boundary,
        )?;
        let is_octet_position = ports
            .iter()
            .all(|port| matches!(port, GranularExteriorPort::Octet(_)));
        let entered = usize::try_from(entered_octet_population)
            .map_err(|_| NativeGranularPotentialError::Extent)?
            .checked_add(usize::from(is_octet_position))
            .ok_or(NativeGranularPotentialError::Extent)?;
        self.emanate_current(current, entered)
    }

    fn emanate_current(
        &self,
        current: GranularPortCurrent,
        entered: usize,
    ) -> Result<GranularBoundaryEmanation, NativeGranularPotentialError> {
        if current.boundary_front.is_empty()
            || current
                .boundary_front
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || current
                .boundary_front
                .iter()
                .any(|state| *state as usize >= self.states.len())
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the exterior boundary-state front is empty or malformed".to_owned(),
            ));
        }
        let reached_matched_length = current
            .contexts
            .iter()
            .filter_map(|context| {
                context
                    .reconstruction_nodes
                    .iter()
                    .filter_map(|node| current.reconstruction_nodes.get(*node as usize))
                    .map(|node| node.greatest_extent)
                    .max()
            })
            .max()
            .unwrap_or(0);
        let reached_state = *current.boundary_front.last().unwrap_or(&0);
        let mut grouped =
            BTreeMap::<GranularHigherBoundaryFace, GranularBoundaryBranchFibre>::new();
        for context in &current.contexts {
            // A carried context already owns its addressed target-state summand.  Testing it
            // against every co-present boundary state manufactures a Cartesian cross-state
            // contact and can relabel one context's current as another state's branch.  The
            // target-state direct-sum law instead forms each context/state incidence first and
            // only unions the resulting boundary faces afterwards.
            let boundary_state = context.state;
            if current
                .boundary_front
                .binary_search(&boundary_state)
                .is_err()
            {
                return Err(NativeGranularPotentialError::FineInvariant(
                    "an addressed carried context escaped its boundary-state direct sum".to_owned(),
                ));
            }
            let state = self
                .states
                .get(boundary_state as usize)
                .ok_or(NativeGranularPotentialError::Wire)?;
            for transition in &state.transitions {
                for generator in self.factor_generators {
                    // Contact belongs to the generated current `T_g x_s`, not to the
                    // predecessor ray `x_s`.  Testing once before the generator loop made every
                    // generator inherit the identity chart's contact relation and disagreed with
                    // the resident `D_p T_g x_s` passage.
                    let (transported_current, _) =
                        apply_generator_current(&context.factor_current, generator)?;
                    if !factor_currents_contact(&transported_current, &transition.factor_current) {
                        continue;
                    }
                    let face = GranularHigherBoundaryFace {
                        port: transition.port.clone(),
                        generator: generator.generator,
                    };
                    let fibre = grouped.entry(face).or_default();
                    fibre.context_states.insert(boundary_state);
                    fibre.target_states.insert(transition.target);
                    for reconstruction_node in &context.reconstruction_nodes {
                        let reconstruction = current
                            .reconstruction_nodes
                            .get(*reconstruction_node as usize)
                            .filter(|node| node.node == *reconstruction_node)
                            .ok_or(NativeGranularPotentialError::Wire)?;
                        fibre.shortest_matched_length = Some(
                            fibre
                                .shortest_matched_length
                                .map_or(reconstruction.shortest_extent, |held| {
                                    held.min(reconstruction.shortest_extent)
                                }),
                        );
                        fibre.greatest_matched_length = fibre
                            .greatest_matched_length
                            .max(reconstruction.greatest_extent);
                        fibre.reconstruction_path_population += &reconstruction.path_population;
                        fibre.reconstruction_nodes.insert(*reconstruction_node);
                    }
                }
            }
        }
        let branches = grouped
            .into_iter()
            .map(|(face, fibre)| GranularBoundaryBranch {
                passage: vec![face.port.clone()],
                port: face.port,
                generator: face.generator,
                context_states: fibre.context_states.into_iter().collect(),
                target_states: fibre.target_states.into_iter().collect(),
                shortest_matched_length: fibre.shortest_matched_length.unwrap_or(0),
                greatest_matched_length: fibre.greatest_matched_length,
                reconstruction_nodes: fibre.reconstruction_nodes.into_iter().collect(),
                reconstruction_path_population: fibre.reconstruction_path_population,
            })
            .collect::<Vec<_>>();
        let greatest_productive_matched_length = branches
            .iter()
            .map(|branch| branch.greatest_matched_length)
            .max();
        Ok(GranularBoundaryEmanation {
            entered_octet_population: u64::try_from(entered)
                .map_err(|_| NativeGranularPotentialError::Extent)?,
            reached_state,
            reached_matched_length,
            greatest_productive_matched_length,
            branches,
            current,
        })
    }

    fn carry_current(
        &self,
        current: GranularPortCurrent,
        entering: GranularExteriorPort,
    ) -> Result<GranularPortCurrent, NativeGranularPotentialError> {
        self.carry_current_sections(current, vec![entering])
    }

    /// Advance one returned native phase front. The descended generators form one direct-sum
    /// action on each live causal section. The exterior face population is retained on the one
    /// addressed reconstruction edge and never used as a transition alphabet.
    #[cfg(test)]
    fn carry_native_generator_front(
        &self,
        current: GranularPortCurrent,
        generators: &[&NativeGranularFactorGenerator],
        returned_higher_faces: &[GranularHigherBoundaryFace],
    ) -> Result<GranularPortCurrent, NativeGranularPotentialError> {
        if generators.is_empty() || returned_higher_faces.is_empty() {
            return Err(NativeGranularPotentialError::FineInvariant(
                "a returned native generator front was empty".to_owned(),
            ));
        }
        let GranularPortCurrent {
            contexts,
            boundary_front: _,
            resident_image: _,
            reconstruction_nodes,
        } = current;
        if contexts.is_empty() {
            return Err(NativeGranularPotentialError::FineInvariant(
                "a returned native generator front had no entering current".to_owned(),
            ));
        }
        let mut candidates = GranularCarriedCandidates::new();
        for context in contexts {
            if context.quadratic_weight == BigUint::from(0_u8)
                || context.reconstruction_nodes.is_empty()
            {
                return Err(NativeGranularPotentialError::Wire);
            }
            for generator in generators {
                let (transported_factor_current, transport_projective_scale) =
                    apply_generator_current(&context.factor_current, generator)?;
                let transported_weight = &context.quadratic_weight
                    * &transport_projective_scale
                    * &transport_projective_scale;
                let generator_faces = returned_higher_faces
                    .iter()
                    .filter(|face| face.generator == generator.generator)
                    .cloned()
                    .collect::<Vec<_>>();
                if generator_faces.is_empty() {
                    return Err(NativeGranularPotentialError::FineInvariant(
                        "a descended generator had no returned boundary face".to_owned(),
                    ));
                }
                let candidate = candidates
                    .entry((0, transported_factor_current))
                    .or_default();
                candidate.quadratic_weight += transported_weight;
                for predecessor in &context.reconstruction_nodes {
                    candidate
                        .reconstruction_edges
                        .push(GranularReconstructionEdge {
                            predecessor: Some(*predecessor),
                            entering_port: None,
                            returned_higher_faces: generator_faces.clone(),
                            transport_projective_scale: transport_projective_scale.clone(),
                        });
                }
            }
        }
        let root = self
            .states
            .first()
            .ok_or(NativeGranularPotentialError::Wire)?;
        let boundary_front = returned_higher_faces
            .iter()
            .map(|face| {
                root.transitions
                    .binary_search_by_key(&&face.port, |transition| &transition.port)
                    .ok()
                    .and_then(|at| root.transitions.get(at))
                    .map(|transition| transition.target)
                    .ok_or_else(|| {
                        NativeGranularPotentialError::FineInvariant(
                            "a returned exterior face was absent from the boundary trace"
                                .to_owned(),
                        )
                    })
            })
            .collect::<Result<BTreeSet<_>, _>>()?
            .into_iter()
            .collect();
        finalize_carried_current(reconstruction_nodes, candidates, boundary_front)
    }

    /// Conduct a finite exterior-port stratum and quotient only complete equal future-consequence
    /// signatures. An exterior port never smuggles a summed generator operator into this passage.
    fn carry_current_sections(
        &self,
        current: GranularPortCurrent,
        sections: Vec<GranularExteriorPort>,
    ) -> Result<GranularPortCurrent, NativeGranularPotentialError> {
        if sections.is_empty() {
            return Err(NativeGranularPotentialError::FineInvariant(
                "a carried current supplied no addressed section".to_owned(),
            ));
        }
        let root = self
            .states
            .first()
            .ok_or(NativeGranularPotentialError::Wire)?;
        let GranularPortCurrent {
            contexts,
            boundary_front: _,
            resident_image: _,
            reconstruction_nodes,
        } = current;
        let mut candidates = GranularCarriedCandidates::new();
        for entering in sections {
            if let Ok(at) = root
                .transitions
                .binary_search_by_key(&&entering, |transition| &transition.port)
            {
                let transition = &root.transitions[at];
                let (factor_current, port_scale) =
                    primitive_factor_current(&transition.factor_current)?;
                let transport_projective_scale = port_scale;
                let candidate = candidates
                    .entry((transition.target, factor_current))
                    .or_default();
                candidate.quadratic_weight +=
                    &transport_projective_scale * &transport_projective_scale;
                candidate
                    .reconstruction_edges
                    .push(GranularReconstructionEdge {
                        predecessor: None,
                        entering_port: Some(entering.clone()),
                        returned_higher_faces: Vec::new(),
                        transport_projective_scale,
                    });
            }
            for context in &contexts {
                let standing = self
                    .states
                    .get(context.state as usize)
                    .ok_or(NativeGranularPotentialError::Wire)?;
                let Ok(at) = standing
                    .transitions
                    .binary_search_by_key(&&entering, |transition| &transition.port)
                else {
                    continue;
                };
                let transition = &standing.transitions[at];
                let Some((factor_current, port_scale)) =
                    transport_factor_current(&context.factor_current, &transition.factor_current)?
                else {
                    continue;
                };
                let transport_projective_scale = port_scale;
                if context.quadratic_weight == BigUint::from(0_u8)
                    || context.reconstruction_nodes.is_empty()
                {
                    return Err(NativeGranularPotentialError::Wire);
                }
                let transported_weight = &context.quadratic_weight
                    * &transport_projective_scale
                    * &transport_projective_scale;
                let candidate = candidates
                    .entry((transition.target, factor_current))
                    .or_default();
                candidate.quadratic_weight += transported_weight;
                for predecessor in &context.reconstruction_nodes {
                    candidate
                        .reconstruction_edges
                        .push(GranularReconstructionEdge {
                            predecessor: Some(*predecessor),
                            entering_port: Some(entering.clone()),
                            returned_higher_faces: Vec::new(),
                            transport_projective_scale: transport_projective_scale.clone(),
                        });
                }
            }
        }
        let boundary_front = candidates
            .keys()
            .map(|(state, _)| *state)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        finalize_carried_current(reconstruction_nodes, candidates, boundary_front)
    }
}
