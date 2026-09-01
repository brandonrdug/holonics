use super::*;
impl ResidentSourceNeutralEcology {
    pub fn rest(&self) -> &SourceNeutralEcologyRest {
        &self.rest
    }

    pub fn into_rest(self) -> SourceNeutralEcologyRest {
        self.rest
    }

    /// Derive the UAR3 cross-organ constitutive chart before an exterior occurrence or release
    /// receiver is admitted.  The domain is the complete native factor-current carrier retained
    /// by the granular organ.  Every row is founded by one already-rested winding branch: its
    /// dependent receiver-fibre orientation supplies the signed incidence and the exact squared
    /// Complex-Parametron current supplies the real constitutive pairing.  The complex current,
    /// signed orientation and complete factor carrier remain beside the resulting receiver chart.
    pub fn factor_winding_constitutive_chart(
        &self,
    ) -> Result<SourceNeutralFactorWindingConstitutiveChart, SourceNeutralEcologyError> {
        // `ResidentSourceNeutralEcology` is obtainable only by consuming a validated rest through
        // `mount_resident`; its owned rest is immutable for the resident lifetime.  Rehashing the
        // complete wire here would be an apparatus replay, not another causal check.
        self.receiver_history
            .compression
            .validate()
            .map_err(|error| SourceNeutralEcologyError::Body(error.to_string()))?;

        let faces = self.rest.granular.factor_faces();
        let factor_population = faces.len();
        let mut branches = self.rest.body.branches().iter().collect::<Vec<_>>();
        branches.sort_by_key(|branch| branch.branch);
        if factor_population == 0
            || branches.is_empty()
            || branches
                .iter()
                .enumerate()
                .any(|(coordinate, branch)| branch.branch != coordinate)
        {
            return Err(SourceNeutralEcologyError::Body(
                "the factor/winding constitutive chart lost a total coordinate carrier".to_owned(),
            ));
        }

        let factor_hands = source_neutral_factor_hands(&self.rest)?;
        let mut branch_functionals = Vec::with_capacity(branches.len());
        let mut rows = Vec::with_capacity(branches.len());
        for branch in branches {
            let constitutive_current = source_neutral_emitting_thread_current(
                self.rest.body.ecology(),
                &branch.thread_address,
            )?;
            let constitutive_norm = constitutive_current.norm_square();
            if constitutive_norm.is_zero() {
                return Err(SourceNeutralEcologyError::Body(format!(
                    "standing winding branch {} has zero constitutive current",
                    branch.thread_address
                )));
            }
            let factor_orientations = faces
                .iter()
                .map(|face| {
                    factor_hands
                        .get(&(face.factor, branch.branch))
                        .copied()
                        .ok_or_else(|| {
                            SourceNeutralEcologyError::Body(format!(
                                "native factor {} lost winding branch {} orientation",
                                face.factor, branch.branch
                            ))
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let coefficients = factor_orientations
                .iter()
                .zip(&self.receiver_history.factor_capacity)
                .map(|(orientation, capacity)| {
                    let local_response =
                        &constitutive_norm * Rat::from_integer(BigInt::from(*capacity));
                    if *orientation > 0 {
                        local_response
                    } else {
                        -local_response
                    }
                })
                .collect::<Vec<_>>();
            let total_factor_coverage = factor_orientations.len() == factor_population
                && factor_orientations
                    .iter()
                    .all(|orientation| matches!(orientation, -1 | 1));
            // Reversing one dependent fibre hand negates precisely that coefficient while the
            // squared constitutive current is invariant.  This is the executable covariance
            // square; no exterior label participates in it.
            let orientation_covariant = factor_orientations
                .iter()
                .zip(&coefficients)
                .zip(&self.receiver_history.factor_capacity)
                .all(|((orientation, coefficient), capacity)| {
                    let local_response =
                        &constitutive_norm * Rat::from_integer(BigInt::from(*capacity));
                    let reversed = if *orientation > 0 {
                        -local_response
                    } else {
                        local_response
                    };
                    reversed == -coefficient.clone()
                });
            if !total_factor_coverage || !orientation_covariant {
                return Err(SourceNeutralEcologyError::Body(format!(
                    "standing winding branch {} failed its constitutive covariance",
                    branch.thread_address
                )));
            }
            let identity_sha256 = digest(&(
                "soma-life.source-neutral-winding-branch-functional.v1",
                branch.branch,
                branch.thread_address.as_str(),
                &constitutive_current,
                &constitutive_norm,
                &factor_orientations,
                &coefficients,
                total_factor_coverage,
                orientation_covariant,
            ));
            rows.push(coefficients.clone());
            branch_functionals.push(SourceNeutralWindingBranchFunctional {
                branch: branch.branch,
                thread_address: branch.thread_address.clone(),
                constitutive_current,
                constitutive_norm,
                factor_orientations,
                coefficients,
                total_factor_coverage,
                orientation_covariant,
                identity_sha256,
            });
        }

        let operator = ExactRatMatrix::new(rows)
            .map_err(|error| SourceNeutralEcologyError::Body(error.to_string()))?;
        let rank = operator
            .rank()
            .map_err(|error| SourceNeutralEcologyError::Body(error.to_string()))?;
        if rank == 0 {
            return Err(SourceNeutralEcologyError::Body(
                "the factor/winding constitutive chart has zero receiver rank".to_owned(),
            ));
        }
        let kernel_dimension = factor_population.checked_sub(rank).ok_or_else(|| {
            SourceNeutralEcologyError::Body(
                "the factor/winding rank escaped its complete source carrier".to_owned(),
            )
        })?;

        let factor_native_addresses = faces.iter().map(|face| face.native).collect::<Vec<_>>();
        let expected_quotient = factor_native_addresses
            .iter()
            .enumerate()
            .map(|(factor, native)| (ItemId(factor as u64), *native))
            .collect::<BTreeMap<_, _>>();
        let actual_quotient = self
            .receiver_history
            .compression
            .quotient
            .iter()
            .map(|assignment| (assignment.source, assignment.native))
            .collect::<BTreeMap<_, _>>();
        let receiver_history_fibres_singleton = self
            .receiver_history
            .compression
            .reconstruction_fibres
            .iter()
            .all(|fibre| fibre.sources.len() == 1)
            && self
                .receiver_history
                .compression
                .reconstruction_fibres
                .len()
                == factor_population;
        let native_population = self
            .receiver_history
            .compression
            .native_population
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let factor_native_population = factor_native_addresses
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let generators_total =
            self.receiver_history
                .compression
                .generators
                .iter()
                .all(|generator| {
                    generator.source.len() == factor_population
                        && generator.native.len() == factor_population
                });
        let q_descent_complete = receiver_history_fibres_singleton
            && expected_quotient == actual_quotient
            && native_population == factor_native_population
            && generators_total;
        if !q_descent_complete {
            return Err(SourceNeutralEcologyError::Body(
                "the complete factor/winding chart did not descend through the resident q/U carrier"
                    .to_owned(),
            ));
        }

        let total_factor_coverage = branch_functionals
            .iter()
            .all(|functional| functional.total_factor_coverage);
        let orientation_covariant = branch_functionals
            .iter()
            .all(|functional| functional.orientation_covariant);
        let receiver_history_compression_identity_sha256 = self
            .receiver_history
            .resident_compression
            .compression_identity_sha256
            .clone();
        let schema = "soma-life.source-neutral-factor-winding-constitutive-chart.v1".to_owned();
        let identity_sha256 = digest(&(
            schema.as_str(),
            self.rest.identity(),
            self.rest.relational.identity(),
            receiver_history_compression_identity_sha256.as_str(),
            &factor_native_addresses,
            &self.receiver_history.factor_capacity,
            &branch_functionals,
            &operator,
            rank,
            kernel_dimension,
            total_factor_coverage,
            orientation_covariant,
            receiver_history_fibres_singleton,
            q_descent_complete,
            true,
            false,
        ));
        Ok(SourceNeutralFactorWindingConstitutiveChart {
            schema,
            rest_identity_sha256: self.rest.identity().to_owned(),
            relational_identity_sha256: self.rest.relational.identity().to_owned(),
            receiver_history_compression_identity_sha256,
            factor_native_addresses,
            factor_capacities: self.receiver_history.factor_capacity.clone(),
            branch_functionals,
            operator,
            rank,
            kernel_dimension,
            total_factor_coverage,
            orientation_covariant,
            receiver_history_fibres_singleton,
            q_descent_complete,
            complete_factor_reconstruction_fibre_retained: true,
            exterior_occurrence_consulted: false,
            identity_sha256,
        })
    }

    /// Return the first complete resident pair-current/boundary section before any exterior
    /// codec attempts to condense it.  This is the focused UAR1 owner: the source occurrence has
    /// already become a source-neutral native current, the fixed pair carrier is founded once on
    /// the card, and the complete native phase front is returned without a byte surface decision.
    pub fn condition_native_factored(
        &mut self,
        projective: &GranularNativeProjectiveCurrent,
    ) -> Result<SourceNeutralFactoredRadiationSection, SourceNeutralEcologyError> {
        self.resident
            .begin_factored_current_occurrence()
            .map_err(|error| SourceNeutralEcologyError::Apparatus(error.to_string()))?;
        let (emanation, crossed_structural_ports) = self
            .rest
            .granular
            .mount()
            .and_then(|mounted| mounted.receive_native_projective_returning(projective))
            .map_err(|error| SourceNeutralEcologyError::Granular(error.to_string()))?;
        self.radiate_native_factored_emanation(projective, emanation, crossed_structural_ports)
            .map(|(section, _entering)| section)
    }

    /// Carry one already-transduced native projective current through the resident generator
    /// action, condense equal transported sections, and return exact fine radiation before any
    /// exterior output codec acts.
    pub fn condition_native(
        &mut self,
        projective: &GranularNativeProjectiveCurrent,
    ) -> Result<SourceNeutralResidentRadiationSection, SourceNeutralEcologyError> {
        self.resident
            .begin_factored_current_occurrence()
            .map_err(|error| SourceNeutralEcologyError::Apparatus(error.to_string()))?;
        let (emanation, crossed_structural_ports) = self
            .rest
            .granular
            .mount()
            .and_then(|mounted| mounted.receive_native_projective_returning(projective))
            .map_err(|error| SourceNeutralEcologyError::Granular(error.to_string()))?;
        self.radiate_native_emanation(projective, &emanation, crossed_structural_ports, None, None)
    }

    /// Consume the resident body and found one move-owned exterior circulation.  This method
    /// performs ingress only; it neither realizes an exterior face nor feeds one back privately.
    pub fn begin_native_exterior(
        mut self,
        projective: GranularNativeProjectiveCurrent,
    ) -> Result<SourceNeutralExteriorCirculation, SourceNeutralEcologyError> {
        self.resident
            .begin_factored_current_occurrence()
            .map_err(|error| SourceNeutralEcologyError::Apparatus(error.to_string()))?;
        let (emanation, crossed_structural_ports) = self
            .rest
            .granular
            .mount()
            .and_then(|mounted| mounted.receive_native_projective_returning(&projective))
            .map_err(|error| SourceNeutralEcologyError::Granular(error.to_string()))?;
        let realization_current = quadratic_realization_current(&projective)?;
        let realization_current_identity_sha256 = digest(&(
            "soma-life.source-neutral-exterior-realization-current.v1",
            projective.identity_sha256.as_str(),
            &realization_current,
        ));
        Ok(SourceNeutralExteriorCirculation {
            ingress_current_identity_sha256: projective.identity_sha256.clone(),
            resident: self,
            emanation,
            crossed_structural_ports,
            continuation_path: Vec::new(),
            native_sections: Vec::new(),
            orders: Vec::new(),
            emitted_octets: Vec::new(),
            inference_returns: Vec::new(),
            delivery_returns: Vec::new(),
            causal_order: 0,
            resident_source: None,
            current_projective: projective,
            presented_current: None,
            realization_current_identity_sha256,
            realization_current,
            active_realization: None,
            realization_target_current_address: None,
        })
    }

    /// Carry the native recurrence through the exact resident quadratic image. The entering
    /// source family founds that image once; later orders transport the image and its descended
    /// constitutive spine without reconstructing an `AddressedCurrentSection` population on the
    /// host. Boundary restrictions remain exterior receiver occurrences and the complete native
    /// phase front remains beside the situated receiver fibre.
    pub(super) fn radiate_native_factored_emanation(
        &mut self,
        projective: &GranularNativeProjectiveCurrent,
        mut emanation: GranularBoundaryEmanation,
        crossed_structural_ports: Vec<GranularExteriorPort>,
    ) -> Result<
        (
            SourceNeutralFactoredRadiationSection,
            GranularBoundaryEmanation,
        ),
        SourceNeutralEcologyError,
    > {
        let generator_count =
            u32::try_from(self.receiver_history.generators.len()).map_err(|_| {
                SourceNeutralEcologyError::Body(
                    "the native generator population exceeded its address".to_owned(),
                )
            })?;
        let generator_targets = self
            .receiver_history
            .generators
            .iter()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        let generator_local_addresses = self
            .receiver_history
            .generator_ids
            .iter()
            .copied()
            .enumerate()
            .map(|(local, generator)| {
                u32::try_from(local)
                    .map(|local| (generator, local))
                    .map_err(|_| {
                        SourceNeutralEcologyError::Body(
                            "a native generator escaped its local address".to_owned(),
                        )
                    })
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        if generator_count == 0 {
            return Err(SourceNeutralEcologyError::Body(
                "the native receiver history has no generator current".to_owned(),
            ));
        }

        // The terminal contexts and the occurrence-wide integrated current are complementary
        // native charts.  Omitting the latter collapses different histories which meet the same
        // terminal suffix before the first returned boundary contact.  Keep it as one additional
        // rank-one section at the already-admitted terminal boundary: this is the exact current
        // accumulated by ingress, not a source string, token feature, or authored semantic axis.
        // The quadratic foundation sums the two sections without introducing cross terms and
        // retains their complete reconstruction testimony outside the hot current.  The compact
        // factorization is ecology's resident state; an upper-triangular factor-pair expansion is
        // only a reconstruction chart and is forbidden here.
        let terminal_state = projective
            .boundary_front
            .first()
            .copied()
            .filter(|_| projective.boundary_front.len() == 1)
            .ok_or_else(|| {
                SourceNeutralEcologyError::Body(
                    "the integrated ingress current has no unique admitted terminal boundary"
                        .to_owned(),
                )
            })?;
        let entering_contexts = projective
            .contexts
            .iter()
            .map(|context| AddressedCurrentSection {
                boundary_state: Some(context.boundary_state),
                quadratic_weight: context.quadratic_weight.clone(),
                factor_current: context
                    .factor_current
                    .iter()
                    .map(|coordinate| (coordinate.factor, coordinate.incidence.clone()))
                    .collect(),
            })
            .chain(std::iter::once(AddressedCurrentSection {
                boundary_state: Some(terminal_state),
                quadratic_weight: BigUint::from(1_u8),
                factor_current: projective
                    .integrated_factor_current
                    .iter()
                    .map(|coordinate| (coordinate.factor, coordinate.incidence.clone()))
                    .collect(),
            }))
            .collect::<Vec<_>>();

        let factored_foundation = if emanation.resident_factored_image().is_none() {
            self.resident
                .stage_sparse_relational_current(
                    &projective.identity_sha256,
                    terminal_state,
                    &projective
                        .integrated_factor_current
                        .iter()
                        .map(|coordinate| (coordinate.factor, coordinate.incidence.clone()))
                        .collect::<Vec<_>>(),
                )
                .map_err(|error| SourceNeutralEcologyError::Apparatus(error.to_string()))?;
            let foundation = self
                .resident
                .mount_sparse_quadratic_moment_foundation(
                    &entering_contexts,
                    &generator_targets,
                    generator_count,
                )
                .map_err(|error| SourceNeutralEcologyError::Apparatus(error.to_string()))?;
            if foundation.source_current_retained_hot || foundation.ambient_covariance_materialized
            {
                return Err(SourceNeutralEcologyError::Apparatus(
                    "the resident image foundation retained an uncondensed source family"
                        .to_owned(),
                ));
            }
            emanation = self
                .rest
                .granular
                .bind_resident_factored_image_foundation(emanation, &foundation.target_address)
                .map_err(|error| SourceNeutralEcologyError::Granular(error.to_string()))?;
            Some(foundation)
        } else {
            None
        };
        let source_image = emanation
            .resident_factored_image()
            .cloned()
            .ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "the native recurrence lost its resident quadratic image".to_owned(),
                )
            })?;

        let visible_ports = emanation
            .branches
            .iter()
            .map(|branch| branch.port.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if visible_ports.is_empty() {
            return Err(SourceNeutralEcologyError::Granular(
                "the native image exposed no boundary port".to_owned(),
            ));
        }
        let universal_ports = visible_ports
            .iter()
            .map(|port| {
                u32::try_from(crate::native_intelligence::granular_potential::port_index(
                    port,
                ))
                .map_err(|_| {
                    SourceNeutralEcologyError::Granular(
                        "a native boundary port escaped its resident address".to_owned(),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let local_ports = visible_ports
            .iter()
            .cloned()
            .enumerate()
            .map(|(local, port)| {
                u32::try_from(local)
                    .map(|local| (port, local))
                    .map_err(|_| {
                        SourceNeutralEcologyError::Granular(
                            "a native local port escaped its resident address".to_owned(),
                        )
                    })
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let boundary_front = emanation.boundary_front().to_vec();
        let boundary = ResidentBoundaryRestrictionFront {
            boundary_states: boundary_front.clone(),
            universal_ports,
        };
        if holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace {
            eprintln!(
                "source-neutral-fixed-pair-boundary states={} branches={} ports={} complete-faces={}",
                boundary_front.len(),
                emanation.branches.len(),
                visible_ports.len(),
                emanation
                    .branches
                    .iter()
                    .map(|branch| branch.context_states.len())
                    .sum::<usize>(),
            );
        }
        // The fixed symmetric-pair carrier is the exact HNN aggregate at each addressed site.
        // Rank-one source rows and local restriction rows remain its reconstruction fibre; they
        // never become the population of the next native state.  The standing resident boundary
        // owner transports, reacts, and aggregates the complete selected face population by
        // target state before either the native phase receiver or the situated observer acts.
        let receiver_address = self
            .resident
            .stage_resident_sparse_quadratic_native_boundary_receivers(&source_image, &boundary)
            .map_err(|error| SourceNeutralEcologyError::Apparatus(error.to_string()))?;
        let entering_current = source_neutral_entering_current(&self.rest, projective)?;
        let returned = self
            .resident
            .complete_resident_factored_moment_boundary_receivers(
                &receiver_address,
                visible_ports.len(),
                &entering_current,
            )
            .map_err(|error| SourceNeutralEcologyError::Apparatus(error.to_string()))?;
        let radiation = returned.boundary;
        let factored_image_passage = returned.image;
        if factored_image_passage.host_rational_continuation
            || !factored_image_passage.atomic_image_replacement
            || !factored_image_passage.source_released_only_after_device_admission
            || !factored_image_passage.receiver_history_quotient_rested
            || factored_image_passage.intermediate_host_egress_octets != 0
            || radiation.invariant_transport_reuploaded
            || radiation.cpu_semantic_replay_after_device
        {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the factored image recurrence replayed or retained a predecessor current"
                    .to_owned(),
            ));
        }
        let situated_receiver = radiation
            .situated_receiver_pairing
            .as_ref()
            .ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "resident image radiation omitted the situated exterior receiver".to_owned(),
                )
            })?;
        let situated_front_indices = situated_receiver
            .front_faces
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let addressed_front = |faces: &[u32]| -> Result<Vec<(u32, u32, u32)>, _> {
            faces
                .iter()
                .map(|face| {
                    let at = *face as usize;
                    situated_receiver
                        .face_source_states
                        .get(at)
                        .copied()
                        .zip(situated_receiver.face_ports.get(at).copied())
                        .zip(situated_receiver.face_generators.get(at).copied())
                        .map(|((state, port), generator)| (state, port, generator))
                        .ok_or_else(|| {
                            SourceNeutralEcologyError::Apparatus(
                                "the situated receiver returned an unaddressed native face"
                                    .to_owned(),
                            )
                        })
                })
                .collect()
        };
        let situated_front = addressed_front(&situated_receiver.front_faces)?;
        let native_phase_front = addressed_front(&situated_receiver.native_phase_front_faces)?;
        let situated_front_ports = situated_front
            .iter()
            .map(|(_, port, _)| *port)
            .collect::<BTreeSet<_>>();
        let native_phase_front_ports = native_phase_front
            .iter()
            .map(|(_, port, _)| *port)
            .collect::<BTreeSet<_>>();
        let face_population = situated_receiver.face_ports.len();
        let complete_face_population = boundary_front
            .len()
            .checked_mul(visible_ports.len())
            .and_then(|held| held.checked_mul(generator_count as usize))
            .ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "the complete addressed face chart exceeded its extent".to_owned(),
                )
            })?;
        if !situated_receiver.complete_native_phase_front_retained
            || face_population == 0
            || situated_receiver.coordinates.len() != face_population
            || situated_receiver.face_source_states.len() != face_population
            || situated_receiver.face_ports.len() != situated_receiver.face_generators.len()
            || situated_front_indices.len() != situated_receiver.front_faces.len()
            || situated_receiver
                .face_ports
                .iter()
                .any(|local| *local as usize >= visible_ports.len())
        {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the image observer lost its native reconstruction fibre".to_owned(),
            ));
        }
        if radiation.complete_successor_face_population != complete_face_population {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the fixed-pair successor chart did not cover its complete addressed boundary"
                    .to_owned(),
            ));
        }
        let complete_successor_addressed_faces =
            addressed_front(&radiation.complete_successor_faces)?
                .into_iter()
                .map(|(source_state, local_port, local_generator)| {
                    let port =
                        visible_ports
                            .get(local_port as usize)
                            .cloned()
                            .ok_or_else(|| {
                                SourceNeutralEcologyError::Apparatus(
                                    "a productive successor escaped its exterior port chart"
                                        .to_owned(),
                                )
                            })?;
                    let generator = self
                        .receiver_history
                        .generator_ids
                        .get(local_generator as usize)
                        .copied()
                        .ok_or_else(|| {
                            SourceNeutralEcologyError::Apparatus(
                                "a productive successor escaped its generator chart".to_owned(),
                            )
                        })?;
                    self.rest
                        .granular
                        .addressed_successor_face(source_state, port, generator)
                        .map_err(|error| SourceNeutralEcologyError::Granular(error.to_string()))
                })
                .collect::<Result<BTreeSet<_>, _>>()?
                .into_iter()
                .collect::<Vec<_>>();
        if complete_successor_addressed_faces.is_empty()
            || complete_successor_addressed_faces.len() > complete_face_population
        {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the compact successor lost its addressed incidence support".to_owned(),
            ));
        }
        let complete_successor_zero_face_population = complete_face_population
            .checked_sub(complete_successor_addressed_faces.len())
            .ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "the compact successor exceeded its addressed face chart".to_owned(),
                )
            })?;
        let reconstruction_dag = emanation.reconstruction_dag().to_vec();
        let mut branches = Vec::with_capacity(emanation.branches.len());
        for boundary_branch in &emanation.branches {
            let local_port = *local_ports.get(&boundary_branch.port).ok_or_else(|| {
                SourceNeutralEcologyError::Granular(
                    "a native image face lost its local port map".to_owned(),
                )
            })?;
            let port_return = radiation
                .port_returns
                .get(local_port as usize)
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Apparatus(
                        "resident image radiation omitted an addressed port return".to_owned(),
                    )
                })?;
            let resident_current = radiation
                .ports
                .get(local_port as usize)
                .cloned()
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Apparatus(
                        "resident image radiation omitted an addressed moment return".to_owned(),
                    )
                })?;
            let _local_generator = *generator_local_addresses
                .get(&boundary_branch.generator)
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Granular(
                        "a native image face lost its local generator map".to_owned(),
                    )
                })?;
            branches.push(SourceNeutralRadiationBranch {
                local_port,
                higher_face: GranularHigherBoundaryFace {
                    port: boundary_branch.port.clone(),
                    generator: boundary_branch.generator,
                },
                exterior_port: boundary_branch.port.clone(),
                boundary: boundary_branch.clone(),
                resident_current,
                returned_response: port_return.returned_response.clone(),
                lies_in_port_kernel: port_return.lies_in_joint_port_kernel,
                lies_in_receiver_phase_front: native_phase_front_ports.contains(&local_port),
                // This situated maximum is an exterior measurement face only.  The caller keeps
                // the full native phase front for recurrence and retains this quotient's complete
                // section as its reconstruction fibre.
                lies_in_situated_receiver_front: situated_front_ports.contains(&local_port),
            });
        }
        let phase_front_higher_faces = branches
            .iter()
            .filter(|branch| branch.lies_in_receiver_phase_front)
            .map(|branch| branch.higher_face.clone())
            .collect::<Vec<_>>();
        let phase_front_ports = phase_front_higher_faces
            .iter()
            .map(|face| face.port.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let situated_receiver_higher_faces = branches
            .iter()
            .filter(|branch| branch.lies_in_situated_receiver_front)
            .map(|branch| branch.higher_face.clone())
            .collect::<Vec<_>>();
        let situated_receiver_ports = situated_receiver_higher_faces
            .iter()
            .map(|face| face.port.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        // Native identity excludes CUDA context handles, allocation addresses, launch counts,
        // timings, and transfer testimony.  Those apparatus faces remain in the returned
        // section, but an exact remount of the same causal current and receiver must recover the
        // same native section even when the driver assigns another context address.
        let stable_foundation = factored_foundation.as_ref().map(|foundation| {
            (
                &foundation.foundation.section,
                foundation.target_address.generation,
                foundation.target_address.factor_population,
                foundation.target_address.image_population,
                foundation.source_current_retained_hot,
                foundation.ambient_covariance_materialized,
            )
        });
        let native_section_identity_sha256 = digest(&(
            "soma-life.source-neutral-factored-radiation.native.v2",
            self.rest.identity(),
            &projective.identity_sha256,
            &boundary_front,
            &branches,
            &phase_front_higher_faces,
            &phase_front_ports,
            &situated_receiver_higher_faces,
            &situated_receiver_ports,
            &complete_successor_addressed_faces,
            complete_successor_zero_face_population,
            &stable_foundation,
            (
                &factored_image_passage
                    .source_address
                    .section_identity_sha256,
                factored_image_passage.source_address.generation,
                factored_image_passage.source_address.factor_population,
                factored_image_passage.source_address.image_population,
                &factored_image_passage
                    .target_address
                    .section_identity_sha256,
                factored_image_passage.target_address.generation,
                factored_image_passage.target_address.factor_population,
                factored_image_passage.target_address.image_population,
                &factored_image_passage.receiver_coordinates,
                factored_image_passage.atomic_image_replacement,
                factored_image_passage.source_released_only_after_device_admission,
                factored_image_passage.receiver_history_quotient_rested,
                factored_image_passage.rooted_history_retained_hot,
                factored_image_passage.ambient_factor_square_materialized,
                factored_image_passage.host_rational_continuation,
            ),
            (
                &radiation.receiver_coordinate_denominator,
                &radiation.ports,
                &radiation.port_returns,
                &radiation.entering_current,
                &radiation.total_returned_current,
                &radiation.stored_difference,
                radiation.local_balance_closes,
                radiation.phase_locked_port_population,
                radiation.phase_front_is_unique,
                &radiation.situated_receiver_pairing,
                radiation.active_factor_population,
                radiation.native_factor_population,
                radiation.moment_field_materialized,
                radiation.moment_factorization_retained,
                (
                    radiation.context_population,
                    radiation.restriction_population,
                    radiation.generator_population,
                ),
            ),
            &reconstruction_dag,
        ));
        let section = SourceNeutralFactoredRadiationSection {
            schema: "soma-life.source-neutral-factored-radiation.v1".to_owned(),
            rest_identity_sha256: self.rest.identity().to_owned(),
            ingress_current_identity_sha256: projective.identity_sha256.clone(),
            entered_octet_population: emanation.entered_octet_population,
            crossed_structural_ports,
            boundary_front,
            branches,
            phase_front_higher_faces,
            phase_front_ports,
            situated_receiver_higher_faces,
            situated_receiver_ports,
            complete_successor_addressed_faces,
            complete_successor_zero_face_population,
            factored_foundation,
            factored_image_passage,
            radiation,
            reconstruction_dag,
            native_section_identity_sha256,
            source_codec_consulted: false,
            exterior_reconstruction_fibre_reachable: false,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
        };
        Ok((section, emanation))
    }

    pub(super) fn radiate_native_emanation(
        &mut self,
        projective: &GranularNativeProjectiveCurrent,
        emanation: &GranularBoundaryEmanation,
        crossed_structural_ports: Vec<GranularExteriorPort>,
        resident_source: Option<&ResidentCurrentAddress>,
        presented_current: Option<&[(u32, BigUint)]>,
    ) -> Result<SourceNeutralResidentRadiationSection, SourceNeutralEcologyError> {
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "source-neutral-radiation-enter resident-generation={:?} presented-factors={}",
                resident_source.map(|address| address.generation),
                presented_current.map_or(0, <[(u32, BigUint)]>::len),
            );
        }
        let axes = self
            .rest
            .granular
            .mount()
            .and_then(|mounted| mounted.quadratic_moment_current_axes(emanation))
            .map_err(|error| SourceNeutralEcologyError::Granular(error.to_string()))?;
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "source-neutral-radiation-axes contexts={} generators={}",
                axes.contexts.len(),
                axes.generator_count,
            );
        }
        let generator_targets = axes.generator_targets;
        let generator_count = axes.generator_count;
        let generator_local_addresses = self
            .receiver_history
            .generator_ids
            .iter()
            .copied()
            .enumerate()
            .map(|(local, generator)| {
                u32::try_from(local)
                    .map(|local| (generator, local))
                    .map_err(|_| {
                        SourceNeutralEcologyError::Body(
                            "a native generator escaped its local address".to_owned(),
                        )
                    })
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let contexts = if resident_source.is_none() {
            let terminal_state = projective
                .boundary_front
                .first()
                .copied()
                .filter(|_| projective.boundary_front.len() == 1)
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Body(
                        "the integrated ingress current has no unique admitted terminal boundary"
                            .to_owned(),
                    )
                })?;
            vec![AddressedCurrentSection {
                boundary_state: Some(terminal_state),
                quadratic_weight: BigUint::from(1_u8),
                factor_current: projective
                    .integrated_factor_current
                    .iter()
                    .map(|coordinate| (coordinate.factor, coordinate.incidence.clone()))
                    .collect(),
            }]
        } else {
            // The host section is boundary/reconstruction testimony only.  The exact coefficient
            // carrier remains the already-addressed resident current and is never rebuilt here.
            axes.contexts
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
                .collect::<Vec<_>>()
        };
        // `B† K B` is the fixed-chart causal-adjoint return of the arriving factor current.  It
        // is founded once, before the first HNN step, and thereafter the resident generated-port
        // passage carries that same current through target aggregation.  The quadratic moment
        // below observes this current; it is not permitted to replace it with a growing path
        // history carrier.
        if resident_source.is_none() {
            let terminal_state = projective
                .boundary_front
                .first()
                .copied()
                .filter(|_| projective.boundary_front.len() == 1)
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Body(
                        "the integrated ingress current has no unique admitted terminal boundary"
                            .to_owned(),
                    )
                })?;
            self.resident
                .stage_sparse_relational_current(
                    &projective.identity_sha256,
                    terminal_state,
                    &projective
                        .integrated_factor_current
                        .iter()
                        .map(|coordinate| (coordinate.factor, coordinate.incidence.clone()))
                        .collect::<Vec<_>>(),
                )
                .map_err(|error| SourceNeutralEcologyError::Apparatus(error.to_string()))?;
        }
        let visible_ports = emanation
            .branches
            .iter()
            .map(|branch| branch.port.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if visible_ports.is_empty() {
            return Err(SourceNeutralEcologyError::Granular(
                "the native ingress exposed no boundary port".to_owned(),
            ));
        }
        let universal_ports = visible_ports
            .iter()
            .map(|port| {
                u32::try_from(crate::native_intelligence::granular_potential::port_index(
                    port,
                ))
                .map_err(|_| {
                    SourceNeutralEcologyError::Granular(
                        "a native boundary port escaped its resident address".to_owned(),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let local_ports = visible_ports
            .iter()
            .cloned()
            .enumerate()
            .map(|(local, port)| {
                u32::try_from(local)
                    .map(|local| (port, local))
                    .map_err(|_| {
                        SourceNeutralEcologyError::Granular(
                            "a native local port escaped its resident address".to_owned(),
                        )
                    })
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let entering_current = source_neutral_entering_current(&self.rest, projective)?;
        let boundary_front = emanation.boundary_front().to_vec();
        let reconstruction_dag = emanation.reconstruction_dag().to_vec();
        let front = ResidentQuadraticMomentFront {
            contexts,
            resident_source: resident_source.cloned(),
            resident_image: None,
            restrictions: ResidentQuadraticMomentRestrictionSource::ResidentBoundary(
                ResidentBoundaryRestrictionFront {
                    boundary_states: boundary_front.clone(),
                    universal_ports,
                },
            ),
            generator_targets,
            generator_count,
            presented_current: presented_current.map(<[(u32, BigUint)]>::to_vec),
        };
        if holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace {
            eprintln!(
                "source-neutral-front contexts={} resident-generation={:?} resident-population={:?} boundary-states={} ports={} generators={}",
                front.contexts.len(),
                front
                    .resident_source
                    .as_ref()
                    .map(|address| address.generation),
                front
                    .resident_source
                    .as_ref()
                    .map(|address| address.section_population),
                boundary_front.len(),
                visible_ports.len(),
                generator_count,
            );
        }
        let radiation = self
            .resident
            .conduct_quadratic_moment_front(&front, visible_ports.len(), &entering_current, false)
            .map_err(|error| SourceNeutralEcologyError::Apparatus(error.to_string()))?;
        let conditioned_current = radiation.conditioned_current.as_ref().ok_or_else(|| {
            SourceNeutralEcologyError::Apparatus(
                "resident radiation omitted its selected generated-port continuation".to_owned(),
            )
        })?;
        let complete_face_population = boundary_front
            .len()
            .checked_mul(visible_ports.len())
            .and_then(|held| held.checked_mul(generator_count as usize))
            .ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "the complete addressed face chart exceeded its extent".to_owned(),
                )
            })?;
        let complete_successor_addressed_faces = conditioned_current
            .passage
            .slots
            .iter()
            .map(|slot| {
                Ok(GranularAddressedHigherBoundaryFace {
                    source_state: slot.source_boundary_state,
                    port: visible_ports
                        .get(slot.port as usize)
                        .cloned()
                        .ok_or_else(|| {
                            SourceNeutralEcologyError::Apparatus(
                                "a complete successor slot escaped its port chart".to_owned(),
                            )
                        })?,
                    generator: *self
                        .receiver_history
                        .generator_ids
                        .get(slot.generator as usize)
                        .ok_or_else(|| {
                            SourceNeutralEcologyError::Apparatus(
                                "a complete successor slot escaped its generator chart".to_owned(),
                            )
                        })?,
                    target_state: slot.boundary_state,
                })
            })
            .collect::<Result<BTreeSet<_>, SourceNeutralEcologyError>>()?
            .into_iter()
            .collect::<Vec<_>>();
        if complete_successor_addressed_faces.is_empty()
            || complete_successor_addressed_faces.len() > complete_face_population
            || conditioned_current.passage.slots.len() != complete_successor_addressed_faces.len()
        {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the resident generated-port passage lost its complete successor incidence"
                    .to_owned(),
            ));
        }
        let complete_successor_zero_face_population = complete_face_population
            .checked_sub(complete_successor_addressed_faces.len())
            .ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "the complete successor exceeded its addressed face chart".to_owned(),
                )
            })?;
        let situated_receiver = radiation
            .situated_receiver_pairing
            .as_ref()
            .ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "resident radiation omitted the situated exterior receiver".to_owned(),
                )
            })?;
        let situated_faces = situated_receiver
            .front_faces
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let face_stride = visible_ports
            .len()
            .checked_mul(generator_count as usize)
            .ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "the addressed higher-face population exceeded its extent".to_owned(),
                )
            })?;
        let expected_face_population =
            boundary_front
                .len()
                .checked_mul(face_stride)
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Apparatus(
                        "the state-addressed higher-face population exceeded its extent".to_owned(),
                    )
                })?;
        // The HNN step has already condensed every local current at its addressed target site.
        // Its post-state observer therefore owns one `(port,generator)` face; the former source-
        // state axis survives in `conditioned_current.passage` as the complete reconstruction
        // fibre rather than being rebuilt as a receiver working population.
        let observer_descended_from_source_fibre = situated_receiver.coordinates.len()
            == face_stride
            && situated_receiver.face_source_states.len() == face_stride
            && situated_receiver
                .face_source_states
                .iter()
                .all(|state| *state == u32::MAX);
        let observer_retains_source_chart = situated_receiver.coordinates.len()
            == expected_face_population
            && situated_receiver.face_source_states.len() == expected_face_population
            && situated_receiver
                .face_source_states
                .chunks_exact(face_stride)
                .zip(&boundary_front)
                .all(|(states, expected)| states.iter().all(|state| state == expected));
        if !situated_receiver.complete_native_phase_front_retained
            || face_stride == 0
            || (!observer_descended_from_source_fibre && !observer_retains_source_chart)
            || situated_receiver.face_ports.len() != expected_face_population
                && situated_receiver.face_ports.len() != face_stride
            || situated_receiver.face_generators.len() != situated_receiver.face_ports.len()
            || situated_faces.len() != situated_receiver.front_faces.len()
            || situated_receiver
                .face_ports
                .iter()
                .any(|local| *local as usize >= visible_ports.len())
            || situated_receiver
                .face_generators
                .iter()
                .any(|generator| *generator >= generator_count)
        {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the situated receiver lost its native phase reconstruction fibre".to_owned(),
            ));
        }
        let invariant_transport_reuploaded = radiation.invariant_transport_reuploaded
            || conditioned_current.invariant_transport_reuploaded;
        let cpu_semantic_replay_after_device = radiation.cpu_semantic_replay_after_device
            || conditioned_current.cpu_semantic_replay_after_device;
        if invariant_transport_reuploaded || cpu_semantic_replay_after_device {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the resident recurrence replayed or reuploaded invariant conduct".to_owned(),
            ));
        }
        let mut branches = Vec::with_capacity(emanation.branches.len());
        for boundary in &emanation.branches {
            let local_port = *local_ports.get(&boundary.port).ok_or_else(|| {
                SourceNeutralEcologyError::Granular(
                    "a native higher face lost its local port map".to_owned(),
                )
            })?;
            let local_generator = *generator_local_addresses
                .get(&boundary.generator)
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Granular(
                        "a native higher face lost its local generator map".to_owned(),
                    )
                })?;
            let local_face = local_port
                .checked_mul(generator_count)
                .and_then(|base| base.checked_add(local_generator))
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Apparatus(
                        "a native higher face exceeded its resident address".to_owned(),
                    )
                })?;
            let addressed_faces = if observer_descended_from_source_fibre {
                vec![local_face as usize]
            } else {
                boundary_front
                    .iter()
                    .enumerate()
                    .filter(|(_, state)| boundary.context_states.contains(state))
                    .map(|(state_coordinate, _)| {
                        state_coordinate
                            .checked_mul(face_stride)
                            .and_then(|base| base.checked_add(local_face as usize))
                            .ok_or_else(|| {
                                SourceNeutralEcologyError::Apparatus(
                                    "a state-addressed native face exceeded its extent".to_owned(),
                                )
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()?
            };
            let first_face = *addressed_faces.first().ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "a native branch lost every addressed source-state face".to_owned(),
                )
            })?;
            // `SourceNeutralRadiationBranch` is the pre-existing exterior branch projection.
            // Its scalar fields therefore carry the exact sum over this branch's retained
            // state-addressed faces; `radiation` and `conditioned_current.passage` beside it keep
            // every constituent and the complete reconstruction fibre for recurrence.
            let mut resident_current =
                radiation.ports.get(first_face).cloned().ok_or_else(|| {
                    SourceNeutralEcologyError::Apparatus(
                        "resident radiation omitted an addressed moment return".to_owned(),
                    )
                })?;
            resident_current.port = local_face;
            let first_return = radiation.port_returns.get(first_face).ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "resident radiation omitted an addressed port return".to_owned(),
                )
            })?;
            let mut returned_response = first_return.returned_response.clone();
            for addressed_face in addressed_faces.iter().copied().skip(1) {
                let current = radiation.ports.get(addressed_face).ok_or_else(|| {
                    SourceNeutralEcologyError::Apparatus(
                        "resident radiation omitted a plural addressed moment return".to_owned(),
                    )
                })?;
                if current.moment.len() != resident_current.moment.len()
                    || current.reflected_family_overlaps.len()
                        != resident_current.reflected_family_overlaps.len()
                    || current.family_overlaps.len() != resident_current.family_overlaps.len()
                    || current.receiver_overlaps.len() != resident_current.receiver_overlaps.len()
                    || current.receiver_action_norms.len()
                        != resident_current.receiver_action_norms.len()
                {
                    return Err(SourceNeutralEcologyError::Apparatus(
                        "state-addressed moment faces did not share one exterior receiver chart"
                            .to_owned(),
                    ));
                }
                for (sum, term) in resident_current.moment.iter_mut().zip(&current.moment) {
                    *sum += term;
                }
                for (sum, term) in resident_current
                    .reflected_family_overlaps
                    .iter_mut()
                    .zip(&current.reflected_family_overlaps)
                {
                    *sum += term;
                }
                for (sum, term) in resident_current
                    .family_overlaps
                    .iter_mut()
                    .zip(&current.family_overlaps)
                {
                    *sum += term;
                }
                for (sum, term) in resident_current
                    .receiver_overlaps
                    .iter_mut()
                    .zip(&current.receiver_overlaps)
                {
                    *sum += term;
                }
                for (sum, term) in resident_current
                    .receiver_action_norms
                    .iter_mut()
                    .zip(&current.receiver_action_norms)
                {
                    *sum += term;
                }
                let returned = radiation.port_returns.get(addressed_face).ok_or_else(|| {
                    SourceNeutralEcologyError::Apparatus(
                        "resident radiation omitted a plural addressed port return".to_owned(),
                    )
                })?;
                returned_response = returned_response.add(&returned.returned_response);
            }
            branches.push(SourceNeutralRadiationBranch {
                local_port: local_face,
                higher_face: GranularHigherBoundaryFace {
                    port: boundary.port.clone(),
                    generator: boundary.generator,
                },
                exterior_port: boundary.port.clone(),
                boundary: boundary.clone(),
                resident_current,
                lies_in_port_kernel: returned_response.is_zero(),
                returned_response,
                lies_in_receiver_phase_front: addressed_faces.iter().any(|face| {
                    radiation
                        .port_returns
                        .get(*face)
                        .is_some_and(|returned| returned.lies_in_receiver_phase_front)
                }),
                lies_in_situated_receiver_front: addressed_faces
                    .iter()
                    .any(|face| situated_faces.contains(&(*face as u32))),
            });
        }
        let phase_front_higher_faces = branches
            .iter()
            .filter(|branch| branch.lies_in_receiver_phase_front)
            .map(|branch| branch.higher_face.clone())
            .collect::<Vec<_>>();
        let phase_front_ports = phase_front_higher_faces
            .iter()
            .map(|face| face.port.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let situated_receiver_higher_faces = branches
            .iter()
            .filter(|branch| branch.lies_in_situated_receiver_front)
            .map(|branch| branch.higher_face.clone())
            .collect::<Vec<_>>();
        let situated_receiver_ports = situated_receiver_higher_faces
            .iter()
            .map(|face| face.port.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let native_section_identity_sha256 = digest(&(
            "soma-life.source-neutral-resident-radiation.native.v2",
            self.rest.identity(),
            &projective.identity_sha256,
            (
                &conditioned_current.passage,
                &boundary_front,
                &complete_successor_addressed_faces,
                complete_successor_zero_face_population,
            ),
            (
                &branches,
                &phase_front_higher_faces,
                &phase_front_ports,
                &situated_receiver_higher_faces,
                &situated_receiver_ports,
            ),
            (
                situated_receiver,
                &radiation.ports,
                &radiation.port_returns,
                &radiation.total_returned_current,
                &radiation.stored_difference,
            ),
            &reconstruction_dag,
        ));
        Ok(SourceNeutralResidentRadiationSection {
            schema: "soma-life.source-neutral-resident-radiation.v2".to_owned(),
            rest_identity_sha256: self.rest.identity().to_owned(),
            ingress_current_identity_sha256: projective.identity_sha256.clone(),
            entered_octet_population: emanation.entered_octet_population,
            crossed_structural_ports,
            boundary_front,
            branches,
            phase_front_higher_faces,
            phase_front_ports,
            situated_receiver_higher_faces,
            situated_receiver_ports,
            complete_successor_addressed_faces,
            complete_successor_zero_face_population,
            radiation,
            reconstruction_dag,
            native_section_identity_sha256,
            source_codec_consulted: false,
            exterior_reconstruction_fibre_reachable: false,
            invariant_transport_reuploaded,
            cpu_semantic_replay_after_device,
        })
    }
}
