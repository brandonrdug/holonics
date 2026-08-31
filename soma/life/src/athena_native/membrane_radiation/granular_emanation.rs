//! Owner-local radiation seam: granular emanation.

use super::super::GranularBoundaryEmanation;
use super::super::{AthenaCausalMembrane, GranularAthenaMembraneStanding};
use super::*;
use holonic_engine::AddressedCurrentSection;
use holonic_engine::cuda_refine::{
    ResidentBoundaryRestrictionFront, ResidentCurrentAddress, ResidentQuadraticMomentFront,
    ResidentQuadraticMomentRestrictionSource, ResidentQuadraticMomentReturn,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    time::Instant,
};
impl<Standing: GranularAthenaMembraneStanding> AthenaCausalMembrane<Standing> {
    /// Continue the complete returned phase front through the same mounted body until its exact
    /// native boundary closes or its projective current recurs. Equal-port generator faces and
    /// distinct-port faces travel as one direct-sum current; there is no authored output extent,
    /// candidate loop, or path enumeration.
    pub fn emanate_granular_response(
        &mut self,
        occurrence: &str,
        payload: &[u8],
    ) -> Result<GranularEmanativeResponse, NativeRadiationError> {
        if occurrence.is_empty() || payload.is_empty() {
            return Err(NativeRadiationError::Exterior);
        }
        let (emanation, crossed_structural_ports) = {
            let rest = self.rested_body();
            rest.membrane_granular_potential()
                .mount()
                .and_then(|mounted| mounted.receive_returning(payload))
                .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?
        };
        let (entering_current, _) = exterior_boundary_current(payload)?;
        self.emanate_granular_response_from(
            occurrence,
            payload,
            emanation,
            crossed_structural_ports,
            entering_current,
        )
    }

    /// Continue the same resident recurrence from the exact primitive-ray quotient of the exterior
    /// occurrence. This is a lawful dynamic condensation because the complete source fibre and the
    /// standing potential which reconstitute the omitted path population are returned beside the
    /// response. No exterior spelling or requested answer enters the quotient law.
    pub fn emanate_projective_granular_response(
        &mut self,
        occurrence: &str,
        payload: &[u8],
    ) -> Result<GranularProjectiveEmanativeReturn, NativeRadiationError> {
        if occurrence.is_empty() || payload.is_empty() {
            return Err(NativeRadiationError::Exterior);
        }
        let (ingress, emanation, crossed_structural_ports) = {
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
        let response = self.emanate_granular_response_from(
            occurrence,
            payload,
            emanation,
            crossed_structural_ports,
            entering_current,
        )?;
        Ok(GranularProjectiveEmanativeReturn { ingress, response })
    }

    fn emanate_granular_response_from(
        &mut self,
        occurrence: &str,
        payload: &[u8],
        mut emanation: GranularBoundaryEmanation,
        mut crossed_structural_ports: Vec<GranularExteriorPort>,
        entering_current: ExactComplexWaveCurrent,
    ) -> Result<GranularEmanativeResponse, NativeRadiationError> {
        let rested_identity_sha256 = self.rested_identity().to_owned();
        let exterior_source_sha256 = hex_sha256(payload);
        let mut seen = Vec::<FactoredObservableContinuation>::new();
        let mut returned_higher_face_strata = Vec::new();
        let mut sections = Vec::new();
        let mut boundary_closure_reached = false;
        let mut profiled_receiver_by_boundary =
            BTreeMap::<Vec<u32>, ResidentQuadraticMomentReturn>::new();
        let mut resident_source = None::<ResidentCurrentAddress>;
        let recurrent_terminal;
        loop {
            let causal_profile = std::env::var_os("MEM6_CAUSAL_PROFILE").is_some();
            let entering_boundary_front = emanation.boundary_front().to_vec();
            if causal_profile {
                let (
                    contexts,
                    boundary_states,
                    nodes,
                    active_nodes,
                    branches,
                    reconstruction_refs,
                    mass_bits,
                ) = emanation.causal_profile();
                eprintln!(
                    "mem6-profile contexts={contexts} boundary_states={boundary_states} boundary_front={entering_boundary_front:?} nodes={nodes} active_nodes={active_nodes} branches={branches} reconstruction_refs={reconstruction_refs} mass_bits={mass_bits}"
                );
            }
            let section_began = Instant::now();
            let entering_emanation = emanation.clone();
            let section = self.radiate_granular_emanation(
                occurrence,
                payload,
                &mut emanation,
                std::mem::take(&mut crossed_structural_ports),
                &entering_current,
                resident_source.clone(),
            )?;
            if causal_profile {
                let receiver_projection = quadratic_receiver_projection_identity_sha256(
                    &entering_boundary_front,
                    &section,
                )?;
                eprintln!(
                    "mem6-receiver projection={} elapsed_ms={} visible_faces={} visible_ports={} phase_locked_ports={} returned={:?}",
                    &receiver_projection[..16],
                    section_began.elapsed().as_millis(),
                    section.visible_higher_faces.len(),
                    section.visible_ports.len(),
                    section.resident_joint_current.phase_locked_port_population,
                    section.visible_higher_faces,
                );
                if let Some(prior) = profiled_receiver_by_boundary.get(&entering_boundary_front) {
                    eprintln!(
                        "mem6-receiver repeated_boundary raw_separator={} projective_separator={}",
                        first_quadratic_receiver_separator(prior, &section.resident_joint_current,)
                            .unwrap_or_else(|| "none".to_owned()),
                        first_quadratic_receiver_projective_separator(
                            prior,
                            &section.resident_joint_current,
                        )
                        .unwrap_or_else(|| "none".to_owned()),
                    );
                } else {
                    profiled_receiver_by_boundary.insert(
                        entering_boundary_front.clone(),
                        section.resident_joint_current.clone(),
                    );
                }
            }
            let selected_faces = section.visible_higher_faces.clone();
            if selected_faces.is_empty() {
                return Err(NativeRadiationError::RadiationDetail(
                    "the resident phase front returned no higher face".to_owned(),
                ));
            }
            let visible_ports = selected_faces
                .iter()
                .map(|face| face.port.clone())
                .collect::<BTreeSet<_>>();
            let continuation = FactoredObservableContinuation::from_section(&section);
            sections.push(section);
            returned_higher_face_strata.push(selected_faces.clone());
            if visible_ports.len() == 1 && visible_ports.contains(&GranularExteriorPort::Closure) {
                boundary_closure_reached = true;
                recurrent_terminal = None;
                break;
            }
            if seen.iter().any(|prior| prior == &continuation) {
                recurrent_terminal = Some(GranularEmanativeTerminal::RecurrentFactorizedMoment {
                    continuation_identity_sha256: digest(&continuation)?,
                });
                break;
            }
            seen.push(continuation);
            if visible_ports.contains(&GranularExteriorPort::Opening) {
                crossed_structural_ports.push(GranularExteriorPort::Opening);
            }
            {
                let rest = self.rested_body();
                rest.membrane_granular_potential()
                    .validate_resident_returned_front(&selected_faces)
                    .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
            }
            let last = sections.last().ok_or(NativeRadiationError::Extent)?;
            let factorization = &last.quadratic_moment_factorization;
            let source_address = last
                .resident_joint_current
                .resident_current
                .clone()
                .ok_or_else(|| {
                    NativeRadiationError::RadiationDetail(
                        "the resident radiation returned no continuing current address".to_owned(),
                    )
                })?;
            if factorization.contexts.is_empty()
                || factorization.resident_image.is_some()
                || factorization.resident_source.as_ref() != resident_source.as_ref()
            {
                return Err(NativeRadiationError::RadiationDetail(
                    "the dynamic current return lost its addressed source world-line".to_owned(),
                ));
            }
            let transported = self
                .continue_resident_addressed_current_passage(
                    &source_address,
                    &factorization.contexts,
                    &factorization.generator_targets,
                    factorization.generator_count,
                )
                .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
            let target_address = transported.target_address.clone();
            emanation = self
                .rested_body()
                .membrane_granular_potential()
                .carry_resident_returned_front(entering_emanation, &selected_faces, transported)
                .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
            resident_source = Some(target_address);
        }
        let exact_exterior_passage = returned_higher_face_strata
            .iter()
            .map(|stratum| {
                let ports = stratum
                    .iter()
                    .map(|face| face.port.clone())
                    .collect::<BTreeSet<_>>();
                (ports.len() == 1)
                    .then(|| ports.into_iter().next())
                    .flatten()
            })
            .collect::<Option<Vec<_>>>();
        let emitted_octets = exact_exterior_passage
            .as_ref()
            .filter(|_| boundary_closure_reached)
            .map(|passage| {
                passage
                    .iter()
                    .filter_map(|port| match port {
                        GranularExteriorPort::Octet(octet) => Some(*octet),
                        GranularExteriorPort::Opening | GranularExteriorPort::Closure => None,
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let exterior_utf8 = boundary_closure_reached
            .then(|| exact_exterior_passage.as_ref())
            .flatten()
            .and_then(|_| String::from_utf8(emitted_octets.clone()).ok());
        let terminal = if let Some(recurrent) = recurrent_terminal {
            recurrent
        } else if exterior_utf8.is_some() {
            GranularEmanativeTerminal::Closure
        } else {
            GranularEmanativeTerminal::PluralReceiverInsufficiency
        };
        let section_identities = sections
            .iter()
            .map(|section| &section.identity_sha256)
            .collect::<Vec<_>>();
        let identity_sha256 = digest(&(
            "soma-life.athena-granular-emanative-response.v6",
            &rested_identity_sha256,
            occurrence,
            &exterior_source_sha256,
            &returned_higher_face_strata,
            &exact_exterior_passage,
            &emitted_octets,
            &section_identities,
            boundary_closure_reached,
            &terminal,
        ))?;
        Ok(GranularEmanativeResponse {
            schema: "soma-life.athena-granular-emanative-response.v6".to_owned(),
            rested_identity_sha256,
            exterior_occurrence: occurrence.to_owned(),
            exterior_source_sha256,
            returned_higher_face_strata,
            exact_exterior_passage,
            emitted_octets,
            exterior_utf8,
            sections,
            boundary_closure_reached,
            terminal,
            renderer_ran_before_native_closure: false,
            identity_sha256,
        })
    }

    pub(super) fn radiate_granular_emanation(
        &mut self,
        occurrence: &str,
        payload: &[u8],
        emanation: &mut GranularBoundaryEmanation,
        crossed_structural_ports: Vec<GranularExteriorPort>,
        entering_current: &ExactComplexWaveCurrent,
        resident_source: Option<ResidentCurrentAddress>,
    ) -> Result<GranularRadiationSection, NativeRadiationError> {
        let profile = std::env::var_os("MEM6_CAUSAL_PROFILE").is_some();
        let radiation_began = Instant::now();
        let rested_identity_sha256 = self.rested_identity().to_owned();
        let exterior_port_addresses = emanation
            .branches
            .iter()
            .map(|branch| branch.port.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .enumerate()
            .map(|(address, port)| {
                u32::try_from(address)
                    .map(|address| (port, address))
                    .map_err(|_| {
                        NativeRadiationError::RadiationDetail(
                            "the exterior port population exceeded its resident address".to_owned(),
                        )
                    })
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let port_population = exterior_port_addresses.len();
        if port_population == 0 {
            return Err(NativeRadiationError::RadiationDetail(
                "the granular return exposed no addressed boundary port".to_owned(),
            ));
        }
        let axes = {
            let rest = self.rested_body();
            rest.membrane_granular_potential()
                .mount()
                .and_then(|mounted| mounted.quadratic_moment_current_axes(emanation))
                .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?
        };
        let mut universal_ports = vec![0_u32; port_population];
        for (port, local) in &exterior_port_addresses {
            universal_ports[*local as usize] = u32::try_from(
                super::super::granular_potential::port_index(port),
            )
            .map_err(|_| {
                NativeRadiationError::RadiationDetail(
                    "a native boundary port exceeded its universal address".to_owned(),
                )
            })?;
        }
        let axes_elapsed = radiation_began.elapsed();
        let quadratic_moment_factorization = ResidentQuadraticMomentFront {
            contexts: axes
                .contexts
                .into_iter()
                .map(|context| AddressedCurrentSection {
                    boundary_state: Some(context.boundary_state),
                    quadratic_weight: context.quadratic_weight,
                    factor_current: context
                        .factor_current
                        .into_iter()
                        .map(|coordinate| (coordinate.factor, coordinate.incidence))
                        .collect(),
                })
                .collect(),
            resident_source,
            resident_image: None,
            restrictions: ResidentQuadraticMomentRestrictionSource::ResidentBoundary(
                ResidentBoundaryRestrictionFront {
                    boundary_states: emanation.boundary_front().to_vec(),
                    universal_ports,
                },
            ),
            generator_targets: axes.generator_targets,
            generator_count: axes.generator_count,
            presented_current: None,
        };
        let reconstruction_dag = emanation.reconstruction_dag().to_vec();
        let mut branch_material = Vec::with_capacity(emanation.branches.len());
        for branch in std::mem::take(&mut emanation.branches) {
            let port = *exterior_port_addresses.get(&branch.port).ok_or_else(|| {
                NativeRadiationError::RadiationDetail(
                    "a higher boundary face lost its shared exterior port address".to_owned(),
                )
            })?;
            branch_material.push((
                port,
                GranularHigherBoundaryFace {
                    port: branch.port.clone(),
                    generator: branch.generator,
                },
                branch.port.clone(),
                branch.passage.clone(),
                branch,
            ));
        }
        let resident_joint_current = self
            .conduct_resident_quadratic_moment_front(
                &quadratic_moment_factorization,
                port_population,
                entering_current,
                false,
            )
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
        let resident_elapsed = radiation_began.elapsed().saturating_sub(axes_elapsed);
        let mut branches = Vec::with_capacity(branch_material.len());
        for (port, higher_face, exterior_port, exterior_passage, boundary) in branch_material {
            let port_return = resident_joint_current
                .port_returns
                .get(port as usize)
                .ok_or_else(|| {
                    NativeRadiationError::RadiationDetail(
                        "resident joint return omitted an addressed port".to_owned(),
                    )
                })?;
            let resident_current = resident_joint_current
                .ports
                .get(port as usize)
                .cloned()
                .ok_or_else(|| {
                    NativeRadiationError::RadiationDetail(
                        "resident moment return omitted an addressed port".to_owned(),
                    )
                })?;
            branches.push(GranularRadiationBranch {
                higher_face,
                exterior_port,
                exterior_passage,
                boundary,
                resident_current,
                lies_in_port_kernel: port_return.lies_in_joint_port_kernel,
                lies_in_receiver_phase_front: port_return.lies_in_receiver_phase_front,
                returned_response: port_return.returned_response.clone(),
            });
        }
        let visible_higher_faces = branches
            .iter()
            .filter(|branch| branch.lies_in_receiver_phase_front)
            .map(|branch| branch.higher_face.clone())
            .collect::<Vec<_>>();
        let visible_ports = visible_higher_faces
            .iter()
            .map(|face| face.port.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let kernel_ports = branches
            .iter()
            .filter(|branch| branch.lies_in_port_kernel)
            .map(|branch| branch.exterior_port.clone())
            .collect::<Vec<_>>();
        let visible_passages = branches
            .iter()
            .filter(|branch| branch.lies_in_receiver_phase_front)
            .map(|branch| branch.exterior_passage.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let exact_decoded_higher_face =
            (visible_higher_faces.len() == 1).then(|| visible_higher_faces[0].clone());
        let exact_decoded_port = (visible_ports.len() == 1).then(|| visible_ports[0].clone());
        let exact_decoded_passage =
            (visible_passages.len() == 1).then(|| visible_passages[0].clone());
        let plural_receiver_insufficiency = visible_ports.len() != 1;
        let exterior_source_sha256 = hex_sha256(payload);
        let identity_sha256 = digest(&(
            "soma-life.athena-granular-radiation.v15",
            &rested_identity_sha256,
            occurrence,
            &exterior_source_sha256,
            emanation.entered_octet_population,
            emanation.reached_state,
            emanation.reached_matched_length,
            emanation.greatest_productive_matched_length,
            &crossed_structural_ports,
            &branches,
            &visible_higher_faces,
            &visible_ports,
            &visible_passages,
            &kernel_ports,
            &resident_joint_current,
            (&quadratic_moment_factorization, &reconstruction_dag),
        ))?;
        if profile {
            let context_coordinates = quadratic_moment_factorization
                .contexts
                .iter()
                .map(|context| context.factor_current.len())
                .sum::<usize>();
            let greatest_context = quadratic_moment_factorization
                .contexts
                .iter()
                .map(|context| context.factor_current.len())
                .max()
                .unwrap_or(0);
            let (boundary_states, active_ports) = match &quadratic_moment_factorization.restrictions
            {
                ResidentQuadraticMomentRestrictionSource::ResidentBoundary(boundary) => (
                    boundary.boundary_states.len(),
                    boundary.universal_ports.len(),
                ),
                ResidentQuadraticMomentRestrictionSource::DirectWitness(_) => (0, 0),
            };
            eprintln!(
                "mem6-radiation axes_ms={} resident_ms={} return_ms={} restrictions={} boundary_states={} active_ports={} contexts={} context_coordinates={} greatest_context={}",
                axes_elapsed.as_millis(),
                resident_elapsed.as_millis(),
                radiation_began
                    .elapsed()
                    .saturating_sub(axes_elapsed)
                    .saturating_sub(resident_elapsed)
                    .as_millis(),
                resident_joint_current.restriction_population,
                boundary_states,
                active_ports,
                quadratic_moment_factorization.contexts.len(),
                context_coordinates,
                greatest_context,
            );
        }
        Ok(GranularRadiationSection {
            schema: "soma-life.athena-granular-radiation.v15".to_owned(),
            rested_identity_sha256,
            exterior_occurrence: occurrence.to_owned(),
            exterior_source_sha256,
            entered_octet_population: emanation.entered_octet_population,
            reached_state: emanation.reached_state,
            reached_matched_length: emanation.reached_matched_length,
            greatest_productive_matched_length: emanation.greatest_productive_matched_length,
            crossed_structural_ports,
            branches,
            visible_higher_faces,
            visible_ports,
            visible_passages,
            kernel_ports,
            resident_joint_current,
            resident_image_passage: None,
            quadratic_moment_factorization,
            reconstruction_dag,
            exact_decoded_higher_face,
            exact_decoded_port,
            exact_decoded_passage,
            plural_receiver_insufficiency,
            complete_reconstruction_fibre_retained: true,
            word_or_clause_renderer_ran: false,
            identity_sha256,
        })
    }
}
