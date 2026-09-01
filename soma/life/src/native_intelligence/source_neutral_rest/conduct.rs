use super::*;
impl SourceNeutralReceiverHistoryConstitution {
    fn descend_returned_current(
        &self,
        returned_native_current_identity_sha256: &str,
        current: &[(u32, BigUint)],
    ) -> Result<SourceNeutralReturnedCurrentDescent, SourceNeutralEcologyError> {
        self.compression
            .validate()
            .map_err(|error| SourceNeutralEcologyError::Body(error.to_string()))?;
        let source_set = self
            .compression
            .source_population
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let mut sparse = BTreeMap::new();
        for (factor, coefficient) in current {
            let source = ItemId(u64::from(*factor));
            if !source_set.contains(&source) || sparse.insert(source, coefficient.clone()).is_some()
            {
                return Err(SourceNeutralEcologyError::Body(
                    "a returned native current escaped or repeated its quotient source".to_owned(),
                ));
            }
        }
        let source_value = self
            .compression
            .source_population
            .iter()
            .copied()
            .map(|source| (source, sparse.remove(&source).unwrap_or_else(BigUint::zero)))
            .collect::<BTreeMap<_, _>>();
        if !sparse.is_empty() {
            return Err(SourceNeutralEcologyError::Body(
                "a returned native current retained an undeclared source coordinate".to_owned(),
            ));
        }
        let quotient = self
            .compression
            .quotient
            .iter()
            .map(|assignment| (assignment.source, assignment.native))
            .collect::<BTreeMap<_, _>>();
        let mut native_value = BTreeMap::new();
        for fibre in &self.compression.reconstruction_fibres {
            let mut sources = fibre.sources.iter().copied();
            let first = sources.next().ok_or_else(|| {
                SourceNeutralEcologyError::Body(
                    "the returned-current quotient exposed an empty fibre".to_owned(),
                )
            })?;
            let value = source_value.get(&first).cloned().ok_or_else(|| {
                SourceNeutralEcologyError::Body(
                    "the returned-current quotient lost its first fibre source".to_owned(),
                )
            })?;
            for source in sources {
                if source_value.get(&source) != Some(&value) {
                    return Err(SourceNeutralEcologyError::Body(format!(
                        "returned-current fibre reopened between source {} and {}",
                        first.0, source.0
                    )));
                }
            }
            native_value.insert(fibre.native, value);
        }
        if native_value.len() != self.compression.native_population.len() {
            return Err(SourceNeutralEcologyError::Body(
                "the returned current did not descend onto every native quotient state".to_owned(),
            ));
        }

        for square in &self.compression.generators {
            let source_transport = square
                .source
                .iter()
                .map(|edge| (edge.from, edge.to))
                .collect::<BTreeMap<_, _>>();
            let native_transport = square
                .native
                .iter()
                .map(|edge| (edge.from, edge.to))
                .collect::<BTreeMap<_, _>>();
            for source in &self.compression.source_population {
                let source_target = source_transport.get(source).ok_or_else(|| {
                    SourceNeutralEcologyError::Body(
                        "a returned-current composite source square was not total".to_owned(),
                    )
                })?;
                let native_source = quotient.get(source).ok_or_else(|| {
                    SourceNeutralEcologyError::Body(
                        "a returned-current composite square lost q(source)".to_owned(),
                    )
                })?;
                let encoded_target = quotient.get(source_target).ok_or_else(|| {
                    SourceNeutralEcologyError::Body(
                        "a returned-current composite square lost q(target)".to_owned(),
                    )
                })?;
                let native_target = native_transport.get(native_source).ok_or_else(|| {
                    SourceNeutralEcologyError::Body(
                        "a returned-current composite native square was not total".to_owned(),
                    )
                })?;
                if encoded_target != native_target
                    || source_value.get(source_target) != native_value.get(native_target)
                {
                    return Err(SourceNeutralEcologyError::Body(format!(
                        "returned-current composite square failed at generator {} source {}",
                        square.generator.0, source.0
                    )));
                }
            }
        }

        let source_current = self
            .compression
            .source_population
            .iter()
            .map(|source| {
                (
                    source.0,
                    source_value
                        .get(source)
                        .cloned()
                        .unwrap_or_else(BigUint::zero),
                )
            })
            .collect::<Vec<_>>();
        let native_current = self
            .compression
            .native_population
            .iter()
            .map(|native| {
                (
                    native.0,
                    native_value
                        .get(native)
                        .cloned()
                        .unwrap_or_else(BigUint::zero),
                )
            })
            .collect::<Vec<_>>();
        let reconstruction_fibre_identity_sha256 = digest(&self.compression.reconstruction_fibres);
        let schema = "soma-life.source-neutral-returned-current-descent.v1".to_owned();
        let identity_sha256 = digest(&(
            schema.as_str(),
            returned_native_current_identity_sha256,
            self.resident_compression
                .compression_identity_sha256
                .as_str(),
            &source_current,
            &native_current,
            reconstruction_fibre_identity_sha256.as_str(),
            true,
            true,
            true,
        ));
        Ok(SourceNeutralReturnedCurrentDescent {
            schema,
            returned_native_current_identity_sha256: returned_native_current_identity_sha256
                .to_owned(),
            compression_identity_sha256: self
                .resident_compression
                .compression_identity_sha256
                .clone(),
            source_current,
            native_current,
            reconstruction_fibre_identity_sha256,
            fibre_constant: true,
            generator_composite_squares_commute: true,
            every_word_exact_by_induction: true,
            shortest_separator: None,
            identity_sha256,
        })
    }
}

impl SourceNeutralExteriorCirculation {
    /// Execute one native HNN step when no exterior realization is active, otherwise advance the
    /// already-founded boundary world-tube through its exact returned factor current and local
    /// phase.  A nonterminal face leaves the continuation inside a pending-return type, so neither
    /// native conduct nor boundary realization can advance until exterior apparatus returns.
    pub fn emit_next(mut self) -> Result<SourceNeutralExteriorStep, SourceNeutralEcologyError> {
        if let Some(prior) = self.active_realization.take() {
            return self.emit_realization_successor(prior);
        }
        let section = self.resident.radiate_native_emanation(
            &self.current_projective,
            &self.emanation,
            std::mem::take(&mut self.crossed_structural_ports),
            self.resident_source.as_ref(),
            self.presented_current.as_deref(),
        )?;
        let conditioned_current = section
            .radiation
            .conditioned_current
            .as_ref()
            .ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "the native section omitted its target-site continuation".to_owned(),
                )
            })?
            .clone();
        let native_current_passage_identity_sha256 = digest(&conditioned_current.passage);
        let native_oriented_faces = native_oriented_realization_faces(
            &section,
            &conditioned_current.passage,
            &conditioned_current.local_currents,
        )?;
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "oriented-realization-native-faces={}",
                native_oriented_faces.len()
            );
        }
        let realization = self
            .resident
            .rest
            .realization
            .realize_native_section(
                &self.resident.rest.relational,
                &self.resident.realization_site_history,
                &mut self.resident.resident,
                &section.native_section_identity_sha256,
                &native_current_passage_identity_sha256,
                0,
                &conditioned_current.passage.target,
                &native_oriented_faces,
                &self
                    .current_projective
                    .ingress_port_chronology
                    .iter()
                    .map(|port| match port {
                        GranularExteriorPort::Octet(octet) => u16::from(octet.to_owned()) + 1,
                        GranularExteriorPort::Opening => 0,
                        GranularExteriorPort::Closure => 257,
                    })
                    .collect::<Vec<_>>(),
                &self.realization_current_identity_sha256,
                self.realization_current.clone(),
            )
            .map_err(|error| {
                SourceNeutralEcologyError::Wire(format!(
                    "the complete native current did not cross the rested exterior realization incidence: {error}"
                ))
            })?;
        let exact_exterior_port = Some(
            realization_port(realization.selected_target_port).ok_or_else(|| {
                SourceNeutralEcologyError::Wire(
                    "the exterior realization escaped the universal boundary chart".to_owned(),
                )
            })?,
        );
        self.active_realization = Some(realization.clone());
        let emitted_octet_position = match exact_exterior_port.as_ref() {
            Some(GranularExteriorPort::Octet(octet)) => {
                let at = u64::try_from(self.emitted_octets.len()).map_err(|_| {
                    SourceNeutralEcologyError::Wire(
                        "the emitted byte boundary exceeded its address".to_owned(),
                    )
                })?;
                self.emitted_octets.push(*octet);
                Some(at)
            }
            Some(GranularExteriorPort::Opening) | Some(GranularExteriorPort::Closure) | None => {
                None
            }
        };
        let emission = exact_exterior_port.clone().map(|port| {
            let occurrence = format!(
                "resident/exterior-emission/{}/{}",
                &self.ingress_current_identity_sha256[..16],
                self.causal_order
            );
            let schema = "soma-life.source-neutral-exterior-emission.v1".to_owned();
            let identity_sha256 = digest(&(
                schema.as_str(),
                self.causal_order,
                occurrence.as_str(),
                section.native_section_identity_sha256.as_str(),
                &port,
                emitted_octet_position,
            ));
            SourceNeutralExteriorEmission {
                schema,
                causal_order: self.causal_order,
                occurrence,
                native_section_identity_sha256: section.native_section_identity_sha256.clone(),
                port,
                emitted_octet_position,
                identity_sha256,
            }
        });
        self.orders.push(SourceNeutralExteriorCodecOrder {
            causal_order: self.causal_order,
            emission_occurrence: emission
                .as_ref()
                .map(|emission| emission.occurrence.clone()),
            emission_identity_sha256: emission
                .as_ref()
                .map(|emission| emission.identity_sha256.clone()),
            native_section_identity_sha256: section.native_section_identity_sha256.clone(),
            phase_front_higher_faces: section.phase_front_higher_faces.clone(),
            situated_receiver_higher_faces: section.situated_receiver_higher_faces.clone(),
            realization: SourceNeutralExteriorRealizationOrderReceipt::from_passage(
                self.causal_order,
                &realization,
            ),
            exact_exterior_port: exact_exterior_port.clone(),
            emitted_octet_position,
            reconstruction_node_addresses: section
                .reconstruction_dag
                .iter()
                .map(|node| node.node)
                .collect(),
        });

        let continuation = SourceNeutralContinuationState::from_section(&section, &realization)?;
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "source-neutral-step order={} current={} target={} receiver={} port={:?}",
                self.causal_order,
                &self.current_projective.identity_sha256[..16],
                &digest(&section.complete_successor_addressed_faces)[..16],
                &digest(&continuation.canonical_receiver_section)[..16],
                exact_exterior_port,
            );
        }

        let returned_addressed_faces = section.complete_successor_addressed_faces.clone();
        if conditioned_current.passage.presented_current.as_deref()
            != self.presented_current.as_deref()
        {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the native recurrence did not use the exact returned exterior current".to_owned(),
            ));
        }
        if let Some(prior_return) = self.inference_returns.last_mut() {
            if prior_return.joined_causal_order.is_none() {
                if prior_return.causal_order.saturating_add(1) != self.causal_order {
                    return Err(SourceNeutralEcologyError::Apparatus(
                        "the exterior return escaped its addressed successor order".to_owned(),
                    ));
                }
                prior_return.joined_causal_order = Some(self.causal_order);
                prior_return.joined_native_section_identity_sha256 =
                    Some(section.native_section_identity_sha256.clone());
                prior_return.joined_conditioned_passage_identity_sha256 =
                    Some(digest(&conditioned_current.passage));
            }
        } else if self.presented_current.is_some() {
            return Err(SourceNeutralEcologyError::Apparatus(
                "a presented current entered without an exterior-return predecessor".to_owned(),
            ));
        }
        let target_current_address = conditioned_current.target_address.clone();
        if let Some(expected_source) = self.resident_source.as_ref() {
            if &conditioned_current.source_address != expected_source {
                return Err(SourceNeutralEcologyError::Apparatus(
                    "the returned occurrence did not join its held resident source address"
                        .to_owned(),
                ));
            }
        } else if !conditioned_current.source_current_mounted_this_pass {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the initial native occurrence did not found its resident source".to_owned(),
            ));
        }
        if target_current_address.operation_complex_identity_sha256
            != conditioned_current
                .source_address
                .operation_complex_identity_sha256
            || target_current_address.device_context_identity
                != conditioned_current.source_address.device_context_identity
            || target_current_address.generation
                != conditioned_current
                    .source_address
                    .generation
                    .saturating_add(1)
            || target_current_address.section_population != conditioned_current.passage.target.len()
        {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the realized presentation lost its target-address continuation".to_owned(),
            ));
        }
        self.realization_target_current_address = Some(target_current_address.clone());

        let returned_visible_ports = section
            .branches
            .iter()
            .map(|branch| branch.exterior_port.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let returned_higher_faces = conditioned_current
            .passage
            .occurrences
            .iter()
            .filter_map(|occurrence| {
                occurrence
                    .target_section
                    .map(|_| occurrence.selected_slot as usize)
            })
            .map(|selected_slot| {
                let slot = conditioned_current
                    .passage
                    .slots
                    .get(selected_slot)
                    .ok_or_else(|| {
                        SourceNeutralEcologyError::Apparatus(
                            "a productive junction occurrence lost its selected slot".to_owned(),
                        )
                    })?;
                let generator = self
                    .resident
                    .receiver_history
                    .generator_ids
                    .get(slot.generator as usize)
                    .copied()
                    .ok_or_else(|| {
                        SourceNeutralEcologyError::Apparatus(
                            "a productive junction occurrence escaped its generator chart"
                                .to_owned(),
                        )
                    })?;
                returned_visible_ports
                    .get(slot.port as usize)
                    .cloned()
                    .map(|port| GranularHigherBoundaryFace { port, generator })
                    .ok_or_else(|| {
                        SourceNeutralEcologyError::Apparatus(
                            "a productive junction occurrence lost its predecessor branch"
                                .to_owned(),
                        )
                    })
            })
            .collect::<Result<BTreeSet<_>, SourceNeutralEcologyError>>()?
            .into_iter()
            .collect::<Vec<_>>();
        if returned_higher_faces.is_empty() {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the completed target current returned no productive boundary".to_owned(),
            ));
        }

        let first_seen = self
            .continuation_path
            .iter()
            .position(|prior| prior == &continuation);
        self.continuation_path.push(continuation.clone());
        self.native_sections.push(section);

        if exact_exterior_port == Some(GranularExteriorPort::Closure) {
            return self.finish(SourceNeutralExteriorRadiationTerminal::Closure);
        }
        let receiver_radical = self
            .native_sections
            .last()
            .and_then(|held| held.radiation.situated_receiver_pairing.as_ref())
            .is_some_and(|pairing| {
                !pairing.front_faces.is_empty()
                    && pairing.coordinates.iter().all(Zero::is_zero)
                    && pairing.current_self_pairings.iter().all(Zero::is_zero)
                    && pairing.ingress_self_pairings.iter().all(Zero::is_zero)
                    && pairing.squared_norm_products.iter().all(Zero::is_zero)
                    && pairing
                        .relational_oriented_real_coordinates
                        .iter()
                        .all(Zero::is_zero)
                    && pairing
                        .relational_oriented_imaginary_coordinates
                        .iter()
                        .all(Zero::is_zero)
                    && pairing
                        .relational_modulus_squared_coordinates
                        .iter()
                        .all(Zero::is_zero)
                    && pairing
                        .relational_target_self_pairings
                        .iter()
                        .all(Zero::is_zero)
                    && pairing
                        .relational_current_self_pairings
                        .iter()
                        .all(Zero::is_zero)
                    && pairing
                        .relational_squared_norm_products
                        .iter()
                        .all(Zero::is_zero)
            });
        if receiver_radical {
            let causal_order = self.causal_order;
            return self.finish(SourceNeutralExteriorRadiationTerminal::ReceiverRadical {
                causal_order,
                unresolved_higher_faces: returned_addressed_faces,
            });
        }
        if let Some(first_seen) = first_seen {
            return self.finish(
                SourceNeutralExteriorRadiationTerminal::RecurrentNativeSection {
                    first_seen_causal_order: u64::try_from(first_seen).map_err(|_| {
                        SourceNeutralEcologyError::Wire(
                            "the recurrence boundary exceeded its address".to_owned(),
                        )
                    })?,
                    continuation_identity_sha256: digest(&continuation),
                },
            );
        }

        let prior_emanation = self.emanation;
        self.emanation = self
            .resident
            .rest
            .granular
            .carry_resident_generated_port_front(
                prior_emanation,
                &returned_higher_faces,
                &conditioned_current,
            )
            .map_err(|error| SourceNeutralEcologyError::Granular(error.to_string()))?;
        // The resident target occurrence is the source of the next word even when the exterior
        // face returns only delivery testimony.  The former realization-only continuation did
        // not re-enter the HNN and therefore left this address solely on the pending boundary;
        // the coupled recurrence must retain the exact already-proved target, not remount or
        // reconstruct it from the emitted face.
        self.resident_source = Some(target_current_address.clone());
        let emission = emission.ok_or_else(|| {
            SourceNeutralEcologyError::Wire(
                "a continuing exterior step did not realize one exact face".to_owned(),
            )
        })?;
        Ok(SourceNeutralExteriorStep::Emission(
            SourceNeutralPendingExteriorEmission {
                circulation: self,
                emission,
                target_current_address,
            },
        ))
    }

    /// Continue the complete addressed realization-site current founded by the resident HNN
    /// section.  The projective receiver emits one exterior face, while every transported target
    /// site remains in the productive section for later local histories.  Delivery testimony
    /// joins this passage but is never remounted as current, and the resident HNN section is not
    /// recomputed once per displayed octet.
    fn emit_realization_successor(
        mut self,
        prior: SourceNeutralExteriorRealizationPassage,
    ) -> Result<SourceNeutralExteriorStep, SourceNeutralEcologyError> {
        let realization = self
            .resident
            .rest
            .realization
            .continue_realization(
                &self.resident.rest.relational,
                &self.resident.realization_site_history,
                &mut self.resident.resident,
                &prior,
            )
            .map_err(|error| {
                SourceNeutralEcologyError::Wire(format!(
                    "the complete realization-site current did not continue: {error}"
                ))
            })?;
        if let Some(returned) = self.delivery_returns.last_mut() {
            if returned.joined_causal_order.is_none() {
                if returned.causal_order.saturating_add(1) != self.causal_order
                    || returned.emission_identity_sha256
                        != self
                            .orders
                            .last()
                            .and_then(|order| order.emission_identity_sha256.clone())
                            .unwrap_or_default()
                {
                    return Err(SourceNeutralEcologyError::Apparatus(
                        "an exterior delivery return escaped its addressed realization successor"
                            .to_owned(),
                    ));
                }
                returned.joined_causal_order = Some(self.causal_order);
                returned.joined_realization_identity_sha256 =
                    Some(realization.identity_sha256.clone());
            }
        } else if self.causal_order != 0 {
            return Err(SourceNeutralEcologyError::Apparatus(
                "an exterior realization advanced without its delivery return".to_owned(),
            ));
        }

        if prior.native_section_identity_sha256 != realization.native_section_identity_sha256
            || prior.native_current_passage_identity_sha256
                != realization.native_current_passage_identity_sha256
            || prior.selected_target_port != realization.source_port
            || prior.returned_factor_current != realization.factor_current
            || prior.returned_site_current != realization.site_current
            || prior.returned_complex_site_current != realization.complex_site_current
            || prior.returned_phase_numerator != realization.entering_phase_numerator
            || prior.returned_phase_denominator != realization.entering_phase_denominator
            || prior.returned_realization_current_identity_sha256
                != realization.entering_realization_current_identity_sha256
        {
            return Err(SourceNeutralEcologyError::Apparatus(
                "the exterior realization lost its exact returned-current join".to_owned(),
            ));
        }
        let section = self.native_sections.last().ok_or_else(|| {
            SourceNeutralEcologyError::Apparatus(
                "the realization continuation lost its founding native section".to_owned(),
            )
        })?;
        let continuation = SourceNeutralContinuationState::from_section(section, &realization)?;
        let continuation_first_seen = self
            .continuation_path
            .iter()
            .position(|prior| prior == &continuation);
        self.continuation_path.push(continuation);
        let native_section_identity_sha256 = section.native_section_identity_sha256.clone();
        let phase_front_higher_faces = section.phase_front_higher_faces.clone();
        let situated_receiver_higher_faces = section.situated_receiver_higher_faces.clone();
        let reconstruction_node_addresses = section
            .reconstruction_dag
            .iter()
            .map(|node| node.node)
            .collect::<Vec<_>>();
        let exact_exterior_port = Some(
            realization_port(realization.selected_target_port).ok_or_else(|| {
                SourceNeutralEcologyError::Wire(
                    "the continued realization escaped the universal boundary chart".to_owned(),
                )
            })?,
        );
        let emitted_octet_position = match exact_exterior_port.as_ref() {
            Some(GranularExteriorPort::Octet(octet)) => {
                let at = u64::try_from(self.emitted_octets.len()).map_err(|_| {
                    SourceNeutralEcologyError::Wire(
                        "the emitted byte boundary exceeded its address".to_owned(),
                    )
                })?;
                self.emitted_octets.push(*octet);
                Some(at)
            }
            Some(GranularExteriorPort::Opening) | Some(GranularExteriorPort::Closure) | None => {
                None
            }
        };
        let emission = exact_exterior_port.clone().map(|port| {
            let occurrence = format!(
                "resident/exterior-emission/{}/{}",
                &self.ingress_current_identity_sha256[..16],
                self.causal_order
            );
            let schema = "soma-life.source-neutral-exterior-emission.v1".to_owned();
            let identity_sha256 = digest(&(
                schema.as_str(),
                self.causal_order,
                occurrence.as_str(),
                native_section_identity_sha256.as_str(),
                &port,
                emitted_octet_position,
            ));
            SourceNeutralExteriorEmission {
                schema,
                causal_order: self.causal_order,
                occurrence,
                native_section_identity_sha256: native_section_identity_sha256.clone(),
                port,
                emitted_octet_position,
                identity_sha256,
            }
        });
        let realization_receipt = SourceNeutralExteriorRealizationOrderReceipt::from_passage(
            self.causal_order,
            &realization,
        );
        let realization_first_seen = self.orders.iter().position(|order| {
            order.realization.source_site_current_identity_sha256
                == realization_receipt.source_site_current_identity_sha256
                && order.realization.entering_phase_numerator
                    == realization_receipt.entering_phase_numerator
                && order.realization.entering_phase_denominator
                    == realization_receipt.entering_phase_denominator
        });
        self.orders.push(SourceNeutralExteriorCodecOrder {
            causal_order: self.causal_order,
            emission_occurrence: emission
                .as_ref()
                .map(|emission| emission.occurrence.clone()),
            emission_identity_sha256: emission
                .as_ref()
                .map(|emission| emission.identity_sha256.clone()),
            native_section_identity_sha256,
            phase_front_higher_faces,
            situated_receiver_higher_faces,
            realization: realization_receipt,
            exact_exterior_port: exact_exterior_port.clone(),
            emitted_octet_position,
            reconstruction_node_addresses,
        });
        self.active_realization = Some(realization.clone());
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "source-neutral-realization order={} source={} target={} sites={} factors={} alternatives={} port={:?}",
                self.causal_order,
                realization.source_port,
                realization.selected_target_port,
                realization.site_current.len(),
                realization.factor_current.len(),
                realization.target_current.len(),
                exact_exterior_port,
            );
        }
        if exact_exterior_port == Some(GranularExteriorPort::Closure) {
            return self.finish(SourceNeutralExteriorRadiationTerminal::Closure);
        }
        if let Some(first_seen) = continuation_first_seen.or(realization_first_seen) {
            return self.finish(
                SourceNeutralExteriorRadiationTerminal::RecurrentNativeSection {
                    first_seen_causal_order: u64::try_from(first_seen).map_err(|_| {
                        SourceNeutralEcologyError::Wire(
                            "the realization recurrence boundary exceeded its address".to_owned(),
                        )
                    })?,
                    continuation_identity_sha256: realization.identity_sha256,
                },
            );
        }
        let target_current_address =
            self.realization_target_current_address
                .clone()
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Apparatus(
                        "the exterior realization lost its resident target address".to_owned(),
                    )
                })?;
        let emission = emission.ok_or_else(|| {
            SourceNeutralEcologyError::Wire(
                "a continuing exterior realization did not emit one exact face".to_owned(),
            )
        })?;
        Ok(SourceNeutralExteriorStep::Emission(
            SourceNeutralPendingExteriorEmission {
                circulation: self,
                emission,
                target_current_address,
            },
        ))
    }

    fn finish(
        self,
        terminal: SourceNeutralExteriorRadiationTerminal,
    ) -> Result<SourceNeutralExteriorStep, SourceNeutralEcologyError> {
        if self.inference_returns.iter().any(|returned| {
            returned.joined_causal_order.is_none()
                || returned.joined_native_section_identity_sha256.is_none()
                || returned
                    .joined_conditioned_passage_identity_sha256
                    .is_none()
        }) {
            return Err(SourceNeutralEcologyError::Apparatus(
                "an exterior return did not join the following native current occurrence"
                    .to_owned(),
            ));
        }
        if self.delivery_returns.iter().any(|returned| {
            returned.joined_causal_order.is_none()
                || returned.joined_realization_identity_sha256.is_none()
        }) {
            return Err(SourceNeutralEcologyError::Apparatus(
                "an exterior delivery return did not join the following realization occurrence"
                    .to_owned(),
            ));
        }
        let receiver_history = found_continuation_receiver_history(&self.continuation_path)?;
        let closed = terminal == SourceNeutralExteriorRadiationTerminal::Closure;
        let every_order_has_exact_port = self
            .orders
            .iter()
            .all(|incidence| incidence.exact_exterior_port.is_some());
        let exterior_utf8 = (closed && every_order_has_exact_port)
            .then(|| String::from_utf8(self.emitted_octets.clone()).ok())
            .flatten();
        let exterior_to_fine_boundary_exact = every_order_has_exact_port
            && self
                .orders
                .iter()
                .filter_map(|incidence| {
                    incidence
                        .emitted_octet_position
                        .map(|position| (position, &incidence.exact_exterior_port))
                })
                .enumerate()
                .all(|(expected, (position, port))| {
                    position == expected as u64
                        && matches!(port, Some(GranularExteriorPort::Octet(_)))
                });
        let mut codec_passage = SourceNeutralExteriorCodecPassage {
            schema: "soma-life.source-neutral-exterior-codec-passage.v2".to_owned(),
            codec_identity_sha256: universal_byte_glyph_codec_identity(),
            rest_identity_sha256: self.resident.rest.identity().to_owned(),
            ingress_current_identity_sha256: self.ingress_current_identity_sha256,
            orders: self.orders,
            emitted_octets: self.emitted_octets,
            exterior_utf8,
            complete_native_sections_retained: true,
            fine_to_exterior_boundary_total: closed && every_order_has_exact_port,
            exterior_to_fine_boundary_exact,
            source_codec_consulted: false,
            source_utterance_reachable: false,
            source_witness_reachable: false,
            identity_sha256: String::new(),
        };
        codec_passage.identity_sha256 = digest(&(
            codec_passage.schema.as_str(),
            codec_passage.codec_identity_sha256.as_str(),
            codec_passage.rest_identity_sha256.as_str(),
            codec_passage.ingress_current_identity_sha256.as_str(),
            &codec_passage.orders,
            &codec_passage.emitted_octets,
            &codec_passage.exterior_utf8,
            codec_passage.complete_native_sections_retained,
            codec_passage.fine_to_exterior_boundary_total,
            codec_passage.exterior_to_fine_boundary_exact,
        ));
        let native_section_identities = self
            .native_sections
            .iter()
            .map(|section| section.native_section_identity_sha256.as_str())
            .collect::<Vec<_>>();
        let resident_receiver_history = self.resident.receiver_history.resident_compression.clone();
        let identity_sha256 = digest(&(
            "soma-life.source-neutral-exterior-radiation.v8",
            &native_section_identities,
            &resident_receiver_history,
            &receiver_history,
            &self.inference_returns,
            &self.delivery_returns,
            &codec_passage,
            &terminal,
        ));
        let radiation = SourceNeutralExteriorRadiation {
            schema: "soma-life.source-neutral-exterior-radiation.v8".to_owned(),
            native_sections: self.native_sections,
            resident_receiver_history,
            receiver_history,
            inference_returns: self.inference_returns,
            delivery_returns: self.delivery_returns,
            codec_passage,
            terminal,
            identity_sha256,
        };
        Ok(SourceNeutralExteriorStep::Terminal(
            SourceNeutralExteriorTerminalReturn {
                resident: self.resident,
                radiation,
            },
        ))
    }
}

impl SourceNeutralPendingExteriorEmission {
    pub fn emission(&self) -> &SourceNeutralExteriorEmission {
        &self.emission
    }

    /// Return the exact open world boundary without feeding the emitted face back into ecology.
    /// This consumes the sole pending seam and returns the resident body through a typed terminal
    /// obstruction; it does not invent a closure, recurrence, or semantic stopping rule.
    pub fn stop_at_exterior_aperture(
        self,
    ) -> Result<SourceNeutralExteriorStep, SourceNeutralEcologyError> {
        let terminal = SourceNeutralExteriorRadiationTerminal::OpenExteriorAperture {
            causal_order: self.emission.causal_order,
            pending_emission_identity_sha256: self.emission.identity_sha256,
        };
        self.circulation.finish(terminal)
    }

    /// Acknowledge physical delivery of the emitted boundary occurrence without mounting its
    /// byte/glyph face as a new semantic current.  The active realization already owns the exact
    /// returned factor section and local phase which found the next boundary order.
    pub fn acknowledge_delivery(
        mut self,
        delivery_occurrence: impl Into<String>,
    ) -> Result<SourceNeutralAcknowledgedExteriorCirculation, SourceNeutralEcologyError> {
        let delivery_occurrence = delivery_occurrence.into();
        if delivery_occurrence.is_empty()
            || delivery_occurrence == self.emission.occurrence
            || self.circulation.active_realization.is_none()
        {
            return Err(SourceNeutralEcologyError::Wire(
                "exterior emission and delivery return require distinct addressed occurrences and an active realization"
                    .to_owned(),
            ));
        }
        let schema = "soma-life.source-neutral-exterior-delivery-return.v1".to_owned();
        let identity_sha256 = digest(&(
            schema.as_str(),
            self.emission.causal_order,
            self.emission.identity_sha256.as_str(),
            delivery_occurrence.as_str(),
            false,
            false,
        ));
        let returned = SourceNeutralExteriorDeliveryReturn {
            schema,
            causal_order: self.emission.causal_order,
            emission_identity_sha256: self.emission.identity_sha256,
            delivery_occurrence,
            morphology_changed: false,
            semantic_ingress_mounted: false,
            joined_causal_order: None,
            joined_realization_identity_sha256: None,
            identity_sha256,
        };
        self.circulation.delivery_returns.push(returned.clone());
        self.circulation.causal_order =
            self.circulation
                .causal_order
                .checked_add(1)
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Wire(
                        "the exterior realization order exceeded its address".to_owned(),
                    )
                })?;
        Ok(SourceNeutralAcknowledgedExteriorCirculation {
            circulation: self.circulation,
            returned,
        })
    }

    fn cross_returned_occurrence(
        &mut self,
        returned_occurrence: String,
        returned_port: GranularExteriorPort,
    ) -> Result<
        (
            GranularNativeProjectiveCurrent,
            SourceNeutralExteriorInferenceReturn,
        ),
        SourceNeutralEcologyError,
    > {
        if returned_occurrence.is_empty() || returned_occurrence == self.emission.occurrence {
            return Err(SourceNeutralEcologyError::Wire(
                "exterior emission and return require distinct addressed occurrences".to_owned(),
            ));
        }
        let returned = self
            .circulation
            .resident
            .rest
            .granular
            .cross_exterior_port_projective_current(&returned_occurrence, returned_port.clone())
            .map_err(|error| SourceNeutralEcologyError::Granular(error.to_string()))?;
        let returned_factor_current = returned
            .native
            .integrated_factor_current
            .iter()
            .map(|coordinate| (coordinate.factor, coordinate.incidence.clone()))
            .collect::<Vec<_>>();
        let returned_current_descent = self
            .circulation
            .resident
            .receiver_history
            .descend_returned_current(&returned.native.identity_sha256, &returned_factor_current)?;
        let receipt = SourceNeutralExteriorInferenceReturn {
            causal_order: self.circulation.causal_order,
            emitting_native_section_identity_sha256: self
                .emission
                .native_section_identity_sha256
                .clone(),
            emission_occurrence: self.emission.occurrence.clone(),
            emitted_port: self.emission.port.clone(),
            returned_occurrence,
            returned_port,
            returned_native_current_identity_sha256: returned.native.identity_sha256.clone(),
            returned_current_descent,
            cold_fibre_identity_sha256: returned.exterior_fibre.identity_sha256,
            cold_fibre_reachable_from_productive_body: false,
            morphology_changed: false,
            joined_causal_order: None,
            joined_native_section_identity_sha256: None,
            joined_conditioned_passage_identity_sha256: None,
        };
        Ok((returned.native, receipt))
    }

    /// Consume a published seam and a separately caused world occurrence as developmental
    /// current.  Unlike the fixed-morphology return, this passage does not privately feed the
    /// return into another inference step.  It returns the same resident parent and one exact
    /// situated difference ready for the existing atomic cultivation owner.
    pub fn return_cultivation_occurrence(
        mut self,
        chart: SourceNeutralFactorWindingConstitutiveChart,
        returned_occurrence: impl Into<String>,
        returned_port: GranularExteriorPort,
    ) -> Result<SourceNeutralExteriorCultivationReturn, SourceNeutralEcologyError> {
        let expected_chart = self
            .circulation
            .resident
            .factor_winding_constitutive_chart()?;
        if chart != expected_chart
            || chart.rest_identity_sha256 != self.circulation.resident.rest.identity()
            || chart.exterior_occurrence_consulted
        {
            return Err(SourceNeutralEcologyError::Body(
                "the world return was offered a counterfeit or occurrence-conditioned winding chart"
                    .to_owned(),
            ));
        }
        let candidate_current = self.circulation.current_projective.clone();
        let emission = self.emission.clone();
        let (returned_current, exterior_return) =
            self.cross_returned_occurrence(returned_occurrence.into(), returned_port)?;
        let body = source_neutral_situated_difference_from_world_return(
            &self.circulation.resident.rest,
            &chart,
            &candidate_current,
            &returned_current,
            &emission,
            &exterior_return,
        )?;
        let schema = "soma-life.source-neutral-situated-difference-receipt.v1".to_owned();
        let identity_sha256 = digest(&(
            schema.as_str(),
            self.circulation.resident.rest.identity(),
            &emission,
            &exterior_return,
            chart.identity_sha256.as_str(),
            &body.candidate_winding_coordinates,
            &body.returned_winding_coordinates,
            &body.winding_difference,
            body.selected_branch,
            body.selected_branch_thread.as_str(),
            body.selected_factor,
            body.selected_factor_native,
            body.selected_reconstruction_fibre_address.as_str(),
            &body.situated_difference,
            true,
            false,
        ));
        let receipt = SourceNeutralSituatedDifferenceReceipt {
            schema,
            rest_identity_sha256: self.circulation.resident.rest.identity().to_owned(),
            emission,
            exterior_return,
            factor_winding_chart_identity_sha256: chart.identity_sha256,
            candidate_winding_coordinates: body.candidate_winding_coordinates,
            returned_winding_coordinates: body.returned_winding_coordinates,
            winding_difference: body.winding_difference,
            selected_branch: body.selected_branch,
            selected_branch_thread: body.selected_branch_thread,
            selected_factor: body.selected_factor,
            selected_factor_native: body.selected_factor_native,
            selected_reconstruction_fibre_address: body.selected_reconstruction_fibre_address,
            situated_difference: body.situated_difference,
            complete_factor_reconstruction_fibre_retained: true,
            exterior_source_fibre_reachable_from_productive_body: false,
            identity_sha256,
        };
        Ok(SourceNeutralExteriorCultivationReturn {
            resident: self.circulation.resident,
            receipt,
        })
    }

    /// Consume the unique pending seam with a separately caused exterior occurrence.  The
    /// returned port may differ from the emitted port; that difference is exterior testimony and
    /// is transduced through the same source-neutral membrane rather than becoming a selector.
    pub fn return_occurrence(
        mut self,
        returned_occurrence: impl Into<String>,
        returned_port: GranularExteriorPort,
    ) -> Result<SourceNeutralReturnedExteriorCirculation, SourceNeutralEcologyError> {
        let (returned_native, returned_receipt) =
            self.cross_returned_occurrence(returned_occurrence.into(), returned_port)?;
        let returned_factor_current = returned_native
            .integrated_factor_current
            .iter()
            .map(|coordinate| (coordinate.factor, coordinate.incidence.clone()))
            .collect::<Vec<_>>();
        let realization_current = quadratic_realization_current(&returned_native)?;
        let realization_current_identity_sha256 = digest(&(
            "soma-life.source-neutral-exterior-realization-current.v1",
            returned_native.identity_sha256.as_str(),
            &realization_current,
        ));
        self.circulation.presented_current = Some(returned_factor_current);
        self.circulation.realization_current = realization_current;
        self.circulation.realization_current_identity_sha256 = realization_current_identity_sha256;
        self.circulation
            .inference_returns
            .push(returned_receipt.clone());
        self.circulation.current_projective = returned_native;
        self.circulation.resident_source = Some(self.target_current_address);
        self.circulation.active_realization = None;
        self.circulation.causal_order =
            self.circulation
                .causal_order
                .checked_add(1)
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Wire(
                        "the causal-order boundary exceeded its address".to_owned(),
                    )
                })?;
        Ok(SourceNeutralReturnedExteriorCirculation {
            circulation: self.circulation,
            returned: returned_receipt,
        })
    }
}

impl SourceNeutralAcknowledgedExteriorCirculation {
    pub fn returned(&self) -> &SourceNeutralExteriorDeliveryReturn {
        &self.returned
    }

    pub fn into_circulation(self) -> SourceNeutralExteriorCirculation {
        self.circulation
    }
}

impl SourceNeutralReturnedExteriorCirculation {
    pub fn returned(&self) -> &SourceNeutralExteriorInferenceReturn {
        &self.returned
    }

    pub fn into_circulation(self) -> SourceNeutralExteriorCirculation {
        self.circulation
    }
}

impl SourceNeutralExteriorCultivationReturn {
    pub fn receipt(&self) -> &SourceNeutralSituatedDifferenceReceipt {
        &self.receipt
    }

    pub fn into_parts(
        self,
    ) -> (
        ResidentSourceNeutralEcology,
        SourceNeutralSituatedDifferenceReceipt,
    ) {
        (self.resident, self.receipt)
    }
}

impl SourceNeutralExteriorTerminalReturn {
    pub fn radiation(&self) -> &SourceNeutralExteriorRadiation {
        &self.radiation
    }

    pub fn into_parts(self) -> (ResidentSourceNeutralEcology, SourceNeutralExteriorRadiation) {
        (self.resident, self.radiation)
    }
}
