//! Owner-local radiation seam: open world.

use super::super::{ExactMembraneChartPassage, GranularMembraneStanding, NativeCausalMembrane};
use super::*;
use holonic_engine::cuda_refine::{
    ResidentBoundaryRestrictionFront, ResidentCurrentAddress, ResidentQuadraticMomentFront,
    ResidentQuadraticMomentRestrictionSource,
};
use std::{collections::BTreeSet, time::Instant};
impl<Standing: GranularMembraneStanding> NativeCausalMembrane<Standing> {
    /// Carry every presented exterior-current section through the complete native ingress front,
    /// restrict every recurrent section to the source-neutral outward port receiver, and descend
    /// the already-admitted generator action until exact dynamic rest or an exact repeated open
    /// front returns.  The exterior source is moved once and returned whole.  No byte path, word,
    /// modality, native cell, response extent, or terminal clock is supplied by the caller.
    pub fn recur_open_world_tube(
        &mut self,
        exterior: ExteriorOccurrenceFibre,
        charts: &[ExactMembraneChartPassage],
    ) -> Result<NativeOpenWorldTubeReturn, NativeRadiationError> {
        if charts.is_empty() {
            return Err(NativeRadiationError::Exterior);
        }
        let ingress_current_fibre = self
            .complete_ingress_current_sections()
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
        let frontier_current_fibre = self
            .complete_frontier_current_sections()
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
        let mut frontier_contexts = frontier_current_fibre
            .iter()
            .map(|section| section.current.clone())
            .collect::<Vec<_>>();
        let ingress_support = frontier_contexts
            .iter()
            .flat_map(|section| section.factor_current.iter().map(|(factor, _)| *factor))
            .collect::<BTreeSet<_>>();
        let (factor_population, outward_ports, outward_boundary, context_boundary_states) = {
            let rest = self.rested_body();
            let factor_population = u32::try_from(rest.membrane_correspondences().len())
                .map_err(|_| NativeRadiationError::Extent)?;
            let atlas = rest
                .membrane_granular_potential()
                .boundary_restriction_atlas()
                .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
            let states = atlas.state_count as usize;
            let ports = atlas.universal_port_count as usize;
            let mut boundary_states = Vec::new();
            for state in 0..states {
                let touches_ingress = (0..ports).any(|port| {
                    let transition = atlas.state_port_transition[state * ports + port];
                    if transition == u32::MAX {
                        return false;
                    }
                    let transition = transition as usize;
                    let begin = atlas.transition_factor_offsets[transition] as usize;
                    let end = atlas.transition_factor_offsets[transition + 1] as usize;
                    atlas.transition_factors[begin..end]
                        .iter()
                        .any(|factor| ingress_support.contains(factor))
                });
                if touches_ingress {
                    boundary_states
                        .push(u32::try_from(state).map_err(|_| NativeRadiationError::Extent)?);
                }
            }
            let universal_ports = (0..ports)
                .filter(|port| {
                    boundary_states.iter().any(|state| {
                        atlas.state_port_transition[*state as usize * ports + *port] != u32::MAX
                    })
                })
                .map(|port| u32::try_from(port).map_err(|_| NativeRadiationError::Extent))
                .collect::<Result<Vec<_>, _>>()?;
            let context_boundary_states = frontier_contexts
                .iter()
                .map(|context| {
                    boundary_states
                        .iter()
                        .copied()
                        .find(|state| {
                            (0..ports).any(|port| {
                                let transition =
                                    atlas.state_port_transition[*state as usize * ports + port];
                                if transition == u32::MAX {
                                    return false;
                                }
                                let transition = transition as usize;
                                let begin = atlas.transition_factor_offsets[transition] as usize;
                                let end = atlas.transition_factor_offsets[transition + 1] as usize;
                                atlas.transition_factors[begin..end].iter().any(|factor| {
                                    context
                                        .factor_current
                                        .binary_search_by_key(factor, |(at, _)| *at)
                                        .is_ok()
                                })
                            })
                        })
                        .ok_or_else(|| {
                            NativeRadiationError::RadiationDetail(
                                "one frontier current has no addressed boundary state".to_owned(),
                            )
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let outward_ports = universal_ports
                .iter()
                .copied()
                .enumerate()
                .map(|(port, universal_port)| {
                    u32::try_from(port)
                        .map(|port| (port, universal_port))
                        .map_err(|_| NativeRadiationError::Extent)
                })
                .collect::<Result<Vec<_>, _>>()?;
            (
                factor_population,
                outward_ports,
                ResidentBoundaryRestrictionFront {
                    boundary_states,
                    universal_ports,
                },
                context_boundary_states,
            )
        };
        for (context, state) in frontier_contexts.iter_mut().zip(context_boundary_states) {
            context.boundary_state = Some(state);
        }
        if factor_population == 0 || outward_ports.is_empty() {
            return Err(NativeRadiationError::RadiationDetail(
                "the standing body has no complete outward boundary receiver".to_owned(),
            ));
        }
        if holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace {
            eprintln!(
                "open-world-tube boundary states={} ports={} ingress-factors={}",
                outward_boundary.boundary_states.len(),
                outward_ports.len(),
                ingress_support.len(),
            );
        }
        let generators = self
            .receiver_history_generators()
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?
            .to_vec();
        if generators.is_empty() {
            return Err(NativeRadiationError::RadiationDetail(
                "the standing body has no admitted native successor generator".to_owned(),
            ));
        }
        let generator_targets = generators.iter().flatten().copied().collect::<Vec<_>>();
        let generator_count =
            u32::try_from(generators.len()).map_err(|_| NativeRadiationError::Extent)?;
        let port_population = outward_ports.len();
        let mut every_generator_descent_returned_on_card = true;
        let mut invariant_transport_reuploaded = false;
        let mut cpu_semantic_replay_after_device = false;
        let mut lawful_silence_present = false;
        let mut compulsory_nonradical_radiation_present = false;
        let mut current_returns = Vec::with_capacity(charts.len());

        for (source_section, chart) in charts.iter().enumerate() {
            // Each chart is a newly addressed exterior-current occurrence through the same
            // resident morphology.  Its first section must not inherit the private continuation
            // address of the preceding occurrence; only the invariant operation complex persists.
            self.begin_resident_factored_current_occurrence()
                .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
            chart.validate().map_err(|defect| {
                NativeRadiationError::RadiationDetail(format!(
                    "the exterior current chart did not commute: {defect:?}"
                ))
            })?;
            if chart.transported_current.is_zero() {
                return Err(NativeRadiationError::RadiationDetail(
                    "a zero exterior current is absence testimony, not a nonzero lawful-silence section"
                        .to_owned(),
                ));
            }
            let exterior_quadratic_lift =
                exterior_current_quadratic_lift(&chart.transported_current)?;
            let mut contexts = frontier_contexts
                .iter()
                .cloned()
                .map(|mut section| {
                    section.quadratic_weight *= &exterior_quadratic_lift.quadratic_numerator;
                    section
                })
                .collect::<Vec<_>>();
            let mut resident_source = None::<ResidentCurrentAddress>;
            let mut orders = Vec::new();
            let mut causal_order = 0_u64;
            let terminal;
            loop {
                let order_started = Instant::now();
                let front = ResidentQuadraticMomentFront {
                    contexts: contexts.clone(),
                    resident_source: resident_source.clone(),
                    resident_image: None,
                    restrictions: ResidentQuadraticMomentRestrictionSource::ResidentBoundary(
                        outward_boundary.clone(),
                    ),
                    generator_targets: generator_targets.clone(),
                    generator_count,
                    presented_current: None,
                };
                let resident = self
                    .conduct_resident_quadratic_moment_front(
                        &front,
                        port_population,
                        &chart.transported_current,
                        false,
                    )
                    .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
                let resident_target_address =
                    resident.resident_current.clone().ok_or_else(|| {
                        NativeRadiationError::RadiationDetail(
                            "the resident outward receiver did not retain its current".to_owned(),
                        )
                    })?;
                if resident.boundary_port_returns.len() != outward_ports.len()
                    || !resident.local_balance_closes
                {
                    return Err(NativeRadiationError::RadiationDetail(
                        "the complete outward boundary restriction lost a port or local balance"
                            .to_owned(),
                    ));
                }
                let mut lawful_silence_population = 0_usize;
                let mut compulsory_radiation_population = 0_usize;
                let mut outward_port_returns = Vec::with_capacity(outward_ports.len());
                let situated = resident.situated_receiver_pairing.as_ref().ok_or_else(|| {
                    NativeRadiationError::RadiationDetail(
                        "the resident outward receiver omitted its situated coordinate section"
                            .to_owned(),
                    )
                })?;
                if situated.face_ports.len() != situated.coordinates.len()
                    || situated.coordinate_denominator <= BigInt::from(0)
                {
                    return Err(NativeRadiationError::RadiationDetail(
                        "the situated outward coordinate section lost its port chart".to_owned(),
                    ));
                }
                for ((port, universal_port), returned) in
                    outward_ports.iter().zip(&resident.boundary_port_returns)
                {
                    if returned.port != *port
                        || returned.returned_response.is_zero()
                            != returned.lies_in_joint_port_kernel
                    {
                        return Err(NativeRadiationError::RadiationDetail(
                            "an outward boundary port disagreed with its exact kernel".to_owned(),
                        ));
                    }
                    if returned.lies_in_joint_port_kernel {
                        lawful_silence_population += 1;
                    } else {
                        compulsory_radiation_population += 1;
                    }
                    let situated_receiver_coordinates = situated
                        .face_ports
                        .iter()
                        .zip(&situated.coordinates)
                        .filter_map(|(face_port, coordinate)| {
                            (*face_port == *port).then_some(coordinate.clone())
                        })
                        .collect::<Vec<_>>();
                    if situated_receiver_coordinates.is_empty() {
                        return Err(NativeRadiationError::RadiationDetail(
                            "one outward port lost every situated generator coordinate".to_owned(),
                        ));
                    }
                    outward_port_returns.push(NativeOutwardPortReturn {
                        port: *port,
                        universal_port: *universal_port,
                        returned_response: returned.returned_response.clone(),
                        situated_receiver_coordinates,
                        situated_coordinate_denominator: situated.coordinate_denominator.clone(),
                        lies_in_outward_radical: returned.lies_in_joint_port_kernel,
                        lies_in_receiver_phase_front: returned.lies_in_receiver_phase_front,
                    });
                }
                lawful_silence_present |= lawful_silence_population != 0;
                compulsory_nonradical_radiation_present |= compulsory_radiation_population != 0;
                invariant_transport_reuploaded |= resident.invariant_transport_reuploaded;
                cpu_semantic_replay_after_device |= resident.cpu_semantic_replay_after_device;
                let descent = resident.conditioned_current.clone().ok_or_else(|| {
                    NativeRadiationError::RadiationDetail(
                        "the resident outward receiver did not return its completed generated-port passage"
                            .to_owned(),
                    )
                })?;
                if descent.target_address != resident_target_address
                    || descent.passage.source != contexts
                    || descent.invariant_transport_reuploaded
                    || descent.cpu_semantic_replay_after_device
                    || descent.intermediate_semantic_egress_octets != 0
                {
                    every_generator_descent_returned_on_card = false;
                }
                invariant_transport_reuploaded |= descent.invariant_transport_reuploaded;
                cpu_semantic_replay_after_device |= descent.cpu_semantic_replay_after_device;
                let target = descent.passage.target.clone();
                let projective_source = projective_current_section(factor_population, &contexts)?;
                let projective_target = projective_current_section(factor_population, &target)?;
                let projective_descent = generated_port_projective_passage(
                    projective_source.clone(),
                    projective_target.clone(),
                    &descent,
                )?;
                let source_rays = canonical_projective_rays(&projective_source);
                let target_rays = canonical_projective_rays(&projective_target);
                let dynamically_closed = target_rays == source_rays;
                let scale_reconstruction_fibre_retained =
                    projective_descent.complete_reconstruction_fibre_retained;
                let target_identity_sha256 = digest(&descent.target_address)?;
                let next_resident_source = descent.target_address.clone();
                if holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace {
                    eprintln!(
                        "open-world-tube order={causal_order} contexts={} rays={}->{} ports={} dynamically_closed={} elapsed={:?}",
                        contexts.len(),
                        source_rays.len(),
                        target_rays.len(),
                        outward_port_returns.len(),
                        dynamically_closed,
                        order_started.elapsed(),
                    );
                }
                orders.push(NativeOpenWorldTubeOrder {
                    causal_order,
                    local_balance_closes: resident.local_balance_closes,
                    complete_reconstruction_fibre_retained: descent.passage.occurrences.len()
                        == contexts
                            .len()
                            .checked_mul(port_population)
                            .and_then(|population| population.checked_mul(generator_count as usize))
                            .ok_or(NativeRadiationError::Extent)?,
                    resident_restriction: resident,
                    outward_port_returns,
                    projective_descent,
                    lawful_silence_population,
                    compulsory_radiation_population,
                });
                if dynamically_closed {
                    terminal = NativeOpenWorldTubeTerminal::DynamicallyCondensedRest {
                        resident_current_identity_sha256: target_identity_sha256,
                        projective_ray_population: target_rays.len(),
                        scale_reconstruction_fibre_retained,
                    };
                    break;
                }
                // HIF7 declares the immediate section and one causally later re-entry as the
                // receiver family.  Once both have returned, a nonstationary target is exact open
                // testimony; extending until an accidental cycle would impose an unscheduled
                // periodicity claim and an unbounded apparatus loop.
                if causal_order != 0 {
                    terminal = NativeOpenWorldTubeTerminal::OpenLaterFront {
                        returned_causal_order: causal_order,
                        resident_current_identity_sha256: target_identity_sha256,
                        projective_ray_population: target_rays.len(),
                        scale_reconstruction_fibre_retained,
                    };
                    break;
                }
                contexts = target;
                resident_source = Some(next_resident_source);
                causal_order = causal_order
                    .checked_add(1)
                    .ok_or(NativeRadiationError::Extent)?;
            }
            current_returns.push(NativeOpenWorldTubeCurrentReturn {
                source_section: u64::try_from(source_section)
                    .map_err(|_| NativeRadiationError::Extent)?,
                presented_section: chart.presented_section.clone(),
                presented_current: chart.presented_current.clone(),
                transported_section: chart.transported_section.clone(),
                transported_current: chart.transported_current.clone(),
                exterior_quadratic_lift,
                orders,
                terminal,
            });
        }
        let address = exterior.address();
        let mut receipt = NativeOpenWorldTubeReceipt {
            schema: OPEN_WORLD_TUBE_RADIATION_SCHEMA.to_owned(),
            rested_identity_sha256: self.rested_identity().to_owned(),
            exterior_occurrence: address.occurrence.clone(),
            exterior_source_sha256: address.source_identity_sha256.clone(),
            exterior_incidence_sha256: address.incidence_identity_sha256.clone(),
            caused_population: address.caused_population,
            ingress_current_fibre,
            frontier_current_fibre,
            outward_port_population: outward_ports.len(),
            current_returns,
            lawful_silence_present,
            compulsory_nonradical_radiation_present,
            every_generator_descent_returned_on_card,
            exact_dynamic_condensation_or_open_front_returned: true,
            source_fibre_remained_exact: true,
            word_or_clause_renderer_ran: false,
            wake_word_or_vad_gate_present: false,
            timer_or_maximum_turn_present: false,
            host_selected_native_contact: false,
            invariant_transport_reuploaded,
            cpu_semantic_replay_after_device,
            identity_sha256: String::new(),
        };
        receipt.identity_sha256 = digest(&(
            &receipt.schema,
            &receipt.rested_identity_sha256,
            &receipt.exterior_occurrence,
            &receipt.exterior_source_sha256,
            &receipt.exterior_incidence_sha256,
            receipt.caused_population,
            &receipt.ingress_current_fibre,
            &receipt.frontier_current_fibre,
            receipt.outward_port_population,
            &receipt.current_returns,
            receipt.lawful_silence_present,
            receipt.compulsory_nonradical_radiation_present,
            receipt.every_generator_descent_returned_on_card,
        ))?;
        Ok(NativeOpenWorldTubeReturn { exterior, receipt })
    }

    /// Radiate one complete exterior occurrence through the compact receiver-history scale action
    /// and the already-constituted Complex-Parametron interior.  Every port branch survives until
    /// exact cancellation places it in the port kernel; no score or lexical surface chooses one.
    pub fn radiate_granular_occurrence(
        &mut self,
        occurrence: &str,
        payload: &[u8],
    ) -> Result<GranularRadiationSection, NativeRadiationError> {
        if occurrence.is_empty() || payload.is_empty() {
            return Err(NativeRadiationError::Exterior);
        }
        let (mut emanation, crossed_structural_ports) = {
            let rest = self.rested_body();
            rest.membrane_granular_potential()
                .mount()
                .and_then(|mounted| mounted.receive_returning(payload))
                .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?
        };
        let (entering_current, _) = exterior_boundary_current(payload)?;
        self.radiate_granular_emanation(
            occurrence,
            payload,
            &mut emanation,
            crossed_structural_ports,
            &entering_current,
            None,
        )
    }

    /// Return the first resident section from the same projective ingress used by the complete
    /// emanative recurrence. This is the smallest direct receiver over that production path.
    pub fn radiate_projective_granular_occurrence(
        &mut self,
        occurrence: &str,
        payload: &[u8],
    ) -> Result<GranularProjectiveRadiationReturn, NativeRadiationError> {
        if occurrence.is_empty() || payload.is_empty() {
            return Err(NativeRadiationError::Exterior);
        }
        let (ingress, mut emanation, crossed_structural_ports) = {
            let potential = self.rested_body().membrane_granular_potential();
            let ingress = potential
                .reflect_exterior_projective_current(occurrence, payload)
                .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
            let (emanation, crossed) = potential
                .mount()
                .and_then(|mounted| mounted.receive_projective_returning(&ingress))
                .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
            (ingress, emanation, crossed)
        };
        let (entering_current, _) = exterior_boundary_current(payload)?;
        let section = self.radiate_granular_emanation(
            occurrence,
            payload,
            &mut emanation,
            crossed_structural_ports,
            &entering_current,
            None,
        )?;
        Ok(GranularProjectiveRadiationReturn { ingress, section })
    }
}
