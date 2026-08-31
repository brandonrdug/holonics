use super::*;

impl ResidentMembraneInteriorWord {
    pub fn mount_observable_integral_form_frame(
        &mut self,
        frame: &ObservableIntegralFormFrame,
    ) -> Result<(), CudaRefineError> {
        let forms = frame.forms.len();
        let generators = frame.descended_generator_factors.len();
        let present = frame.present_receiver_factors.len();
        if frame.schema != "holonic-engine.observable-integral-form-frame.v1"
            || frame.factor_population != self.factors
            || forms == 0
            || generators == 0
            || present == 0
            || forms > u32::MAX as usize
            || generators > u32::MAX as usize
            || present > u32::MAX as usize
            || frame.forms.iter().any(|form| {
                form.factor_population != self.factors
                    || form.entries.is_empty()
                    || form
                        .entries
                        .windows(2)
                        .any(|pair| (pair[0].row, pair[0].column) >= (pair[1].row, pair[1].column))
                    || form.entries.iter().any(|entry| {
                        entry.row >= self.factors
                            || entry.column >= self.factors
                            || entry.coefficient.is_zero()
                    })
            })
            || frame
                .descended_generator_factors
                .iter()
                .any(|action| action.len() != forms)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let identity = serde_json::to_vec(frame)
            .map(|bytes| {
                Sha256::digest(bytes)
                    .iter()
                    .map(|octet| format!("{octet:02x}"))
                    .collect::<String>()
            })
            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        if let Some(mounted) = &self.observable_integral_form_frame {
            return if mounted.identity_sha256 == identity {
                Ok(())
            } else {
                Err(CudaRefineError::MembraneInteriorWordShape)
            };
        }

        let maximal_coefficient = frame
            .forms
            .iter()
            .flat_map(|form| &form.entries)
            .map(|entry| entry.coefficient.magnitude().clone())
            .max()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let maximal_scale = frame
            .present_receiver_factors
            .iter()
            .chain(frame.descended_generator_factors.iter().flatten())
            .map(|factor| factor.scale.magnitude().clone())
            .max()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let coefficient_limb_count = maximal_coefficient.to_u32_digits().len().max(1);
        let scale_limb_count = maximal_scale.to_u32_digits().len().max(1);
        if coefficient_limb_count > u32::MAX as usize || scale_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }

        let mut form_entry_offsets = Vec::with_capacity(forms + 1);
        let mut form_entry_rows = Vec::new();
        let mut form_entry_columns = Vec::new();
        let mut form_entry_signs = Vec::new();
        let mut form_entry_limbs = Vec::new();
        form_entry_offsets.push(0_u64);
        let mut maximal_form_entry_population = 0_u64;
        for form in &frame.forms {
            maximal_form_entry_population = maximal_form_entry_population.max(
                u64::try_from(form.entries.len())
                    .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
            );
            for entry in &form.entries {
                form_entry_rows.push(entry.row);
                form_entry_columns.push(entry.column);
                let (sign, limbs) = encode_integer(&entry.coefficient, coefficient_limb_count)?;
                form_entry_signs.push(sign);
                form_entry_limbs.extend(limbs);
            }
            form_entry_offsets.push(
                u64::try_from(form_entry_rows.len())
                    .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
            );
        }
        let (present_factor_sources, present_factor_scale_signs, present_factor_scale_limbs) =
            encode_integral_form_factors(&frame.present_receiver_factors, scale_limb_count)?;
        let generator_factors = frame
            .descended_generator_factors
            .iter()
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        let (generator_factor_sources, generator_factor_scale_signs, generator_factor_scale_limbs) =
            encode_integral_form_factors(&generator_factors, scale_limb_count)?;
        if present_factor_sources
            .iter()
            .chain(&generator_factor_sources)
            .any(|source| *source != u32::MAX && *source as usize >= forms)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let invariant_octets = [
            std::mem::size_of_val(&form_entry_offsets[..]),
            std::mem::size_of_val(&form_entry_rows[..]),
            std::mem::size_of_val(&form_entry_columns[..]),
            std::mem::size_of_val(&form_entry_signs[..]),
            std::mem::size_of_val(&form_entry_limbs[..]),
            std::mem::size_of_val(&present_factor_sources[..]),
            std::mem::size_of_val(&present_factor_scale_signs[..]),
            std::mem::size_of_val(&present_factor_scale_limbs[..]),
            std::mem::size_of_val(&generator_factor_sources[..]),
            std::mem::size_of_val(&generator_factor_scale_signs[..]),
            std::mem::size_of_val(&generator_factor_scale_limbs[..]),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        self.observable_integral_form_frame = Some(ResidentObservableIntegralFormMount {
            identity_sha256: identity,
            form_count: forms as u32,
            generator_count: generators as u32,
            present_receiver_count: present as u32,
            coefficient_limb_count: coefficient_limb_count as u32,
            scale_limb_count: scale_limb_count as u32,
            maximal_form_entry_population,
            maximal_coefficient,
            maximal_scale,
            form_entry_offsets: Buffer::of(&form_entry_offsets)?,
            form_entry_rows: Buffer::of(&form_entry_rows)?,
            form_entry_columns: Buffer::of(&form_entry_columns)?,
            form_entry_signs: Buffer::of(&form_entry_signs)?,
            form_entry_limbs: Buffer::of(&form_entry_limbs)?,
            present_factor_sources: Buffer::of(&present_factor_sources)?,
            present_factor_scale_signs: Buffer::of(&present_factor_scale_signs)?,
            present_factor_scale_limbs: Buffer::of(&present_factor_scale_limbs)?,
            generator_factor_sources: Buffer::of(&generator_factor_sources)?,
            generator_factor_scale_signs: Buffer::of(&generator_factor_scale_signs)?,
            generator_factor_scale_limbs: Buffer::of(&generator_factor_scale_limbs)?,
        });
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(invariant_octets)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        Ok(())
    }
    pub fn mount_addressed_factored_receiver_complexes(
        &mut self,
        complexes: &[AddressedFactoredIntegralReceiverComplex],
        support_receiver_classes: &[u32],
        support_quadratic_scales: &[BigUint],
        occurrence_ports: &[u32],
    ) -> Result<ResidentAddressedFactoredReceiverFrameReturn, CudaRefineError> {
        if complexes.is_empty()
            || support_receiver_classes.is_empty()
            || support_receiver_classes.len() != support_quadratic_scales.len()
            || occurrence_ports.len() != support_receiver_classes.len()
            || complexes.len() > u32::MAX as usize
            || support_receiver_classes.len() > u32::MAX as usize
            || support_receiver_classes
                .iter()
                .any(|address| *address as usize >= complexes.len())
            || support_quadratic_scales.iter().any(BigUint::is_zero)
            || complexes.iter().any(|complex| {
                complex.schema != "holonic-engine.addressed-factored-integral-receiver-complex.v1"
                    || complex.factor_population != self.factors
                    || complex.family_population != self.families
                    || complex.receiver_population != self.receiver_count
                    || complex.generator_population == 0
                    || complex.functionals.is_empty()
                    || complex.receivers.is_empty()
                    || complex.receivers.len()
                        != (2_u32
                            .checked_mul(complex.family_population)
                            .and_then(|held| {
                                held.checked_add(2_u32.checked_mul(complex.receiver_population)?)
                            })
                            .unwrap_or(u32::MAX)) as usize
                    || complex.functionals.iter().any(|functional| {
                        functional.factor_population != self.factors
                            || functional
                                .entries
                                .windows(2)
                                .any(|pair| pair[0].factor >= pair[1].factor)
                            || functional.entries.iter().any(|entry| {
                                entry.factor >= self.factors || entry.coefficient.is_zero()
                            })
                    })
                    || complex
                        .receivers
                        .iter()
                        .flat_map(|receiver| &receiver.terms)
                        .any(|term| {
                            term.coefficient.is_zero()
                                || term.left_functional as usize >= complex.functionals.len()
                                || term.right_functional as usize >= complex.functionals.len()
                        })
            })
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let generator_count = complexes[0].generator_population;
        if complexes
            .iter()
            .any(|complex| complex.generator_population != generator_count)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        if self
            .factored_receiver_history
            .as_ref()
            .and_then(|mount| mount.transported_image.as_ref())
            .is_some()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let identity_sha256 = serde_json::to_vec(&(
            complexes,
            support_receiver_classes,
            support_quadratic_scales,
            occurrence_ports,
        ))
        .map(|bytes| {
            Sha256::digest(bytes)
                .iter()
                .map(|octet| format!("{octet:02x}"))
                .collect::<String>()
        })
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        if let Some(mounted) = &self.addressed_factored_receiver_frame {
            if mounted.identity_sha256 == identity_sha256 {
                return Ok(ResidentAddressedFactoredReceiverFrameReturn {
                    identity_sha256,
                    occurrence_population: mounted.support_count,
                    functional_population: mounted.functional_count,
                    receiver_population: mounted.receiver_count,
                    term_population: mounted.term_count,
                    device: self.card.device_name.clone(),
                    context_identity: self.card.context as usize,
                    host_ingress_octets: 0,
                    resident_octets: mounted.resident_octets,
                    ambient_factor_square_materialized: false,
                });
            }
        }

        let primitive_frame = AddressedPrimitiveReceiverFrame::found(complexes)
            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let sparse_pair_receiver_host = self
            .factored_receiver_history
            .as_ref()
            .and_then(|mount| mount.sparse_pair.as_ref())
            .map(|state| {
                let mut offsets = Vec::new();
                let mut coordinates = Vec::new();
                let mut coefficients = Vec::<BigInt>::new();
                let mut maximal_receiver_l1 = BigUint::zero();
                offsets.push(0_u64);
                for complex in complexes {
                    let frame = SparseQuadraticPairReceiverFrame::found(&state.action, complex)
                        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
                    for receiver in 0..frame.receiver_population as usize {
                        let begin = frame.receiver_term_offsets[receiver] as usize;
                        let end = frame.receiver_term_offsets[receiver + 1] as usize;
                        let l1 = frame.terms[begin..end]
                            .iter()
                            .fold(BigUint::zero(), |sum, term| {
                                sum + term.coefficient.magnitude()
                            });
                        maximal_receiver_l1 = maximal_receiver_l1.max(l1);
                        for term in &frame.terms[begin..end] {
                            coordinates.push(term.pair_coordinate);
                            coefficients.push(term.coefficient.clone());
                        }
                        offsets.push(u64::try_from(coordinates.len()).map_err(|_| {
                            CudaRefineError::MembraneInteriorCurrentOutsideApparatus
                        })?);
                    }
                }
                if offsets.len() != primitive_frame.receiver_factor_offsets.len()
                    || coefficients.is_empty()
                    || maximal_receiver_l1.is_zero()
                {
                    return Err(CudaRefineError::MembraneInteriorWordShape);
                }
                let coefficient_limb_count = coefficients
                    .iter()
                    .map(|coefficient| coefficient.magnitude().to_u32_digits().len().max(1))
                    .max()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
                let mut signs = Vec::with_capacity(coefficients.len());
                let mut limbs = Vec::with_capacity(
                    coefficients
                        .len()
                        .checked_mul(coefficient_limb_count)
                        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
                );
                for coefficient in &coefficients {
                    let (sign, encoded) = encode_integer(coefficient, coefficient_limb_count)?;
                    signs.push(sign);
                    limbs.extend(encoded);
                }
                let octets = [
                    std::mem::size_of_val(offsets.as_slice()),
                    std::mem::size_of_val(coordinates.as_slice()),
                    std::mem::size_of_val(signs.as_slice()),
                    std::mem::size_of_val(limbs.as_slice()),
                ]
                .into_iter()
                .try_fold(0_u64, |sum, octets| {
                    sum.checked_add(u64::try_from(octets).ok()?)
                })
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                Ok((
                    offsets,
                    coordinates,
                    signs,
                    limbs,
                    coefficient_limb_count as u32,
                    maximal_receiver_l1,
                    octets,
                ))
            })
            .transpose()?;
        let receiver_count = primitive_frame.receiver_factor_offsets.len() - 1;
        let term_count = primitive_frame.receiver_factors.len();
        let presented_term_count = primitive_frame.presented_term_factors.len();
        let functional_count = primitive_frame.functionals.len();
        let pair_count = primitive_frame.functional_pairs.len();
        if receiver_count == 0
            || term_count == 0
            || presented_term_count == 0
            || functional_count == 0
            || pair_count == 0
            || receiver_count > u32::MAX as usize
            || functional_count > u32::MAX as usize
            || pair_count > u32::MAX as usize
        {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let maximal_support_quadratic_scale = support_quadratic_scales
            .iter()
            .cloned()
            .max()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let support_quadratic_scale_limb_count =
            maximal_support_quadratic_scale.to_u32_digits().len().max(1);
        if support_quadratic_scale_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let mut support_quadratic_scale_limbs = Vec::with_capacity(
            support_quadratic_scales
                .len()
                .checked_mul(support_quadratic_scale_limb_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        );
        for scale in support_quadratic_scales {
            let mut limbs = scale.to_u32_digits();
            limbs.resize(support_quadratic_scale_limb_count, 0);
            support_quadratic_scale_limbs.extend(limbs);
        }

        if trace_configuration().holonics_phase_trace {
            eprintln!(
                "mem6-image receiver-frame occurrences={} presented_functionals={} primitive_functionals={} presented_terms={} primitive_pairs={} receiver_factors={}",
                complexes.len(),
                primitive_frame.occurrence_functional_coordinates.len(),
                functional_count,
                presented_term_count,
                pair_count,
                term_count,
            );
        }
        let maximal_functional_coefficient = primitive_frame
            .functionals
            .iter()
            .flat_map(|functional| &functional.entries)
            .map(|entry| entry.coefficient.magnitude().clone())
            .max()
            .unwrap_or_else(BigUint::one);
        let maximal_term_coefficient = primitive_frame
            .receiver_factors
            .iter()
            .map(|factor| factor.scale.magnitude().clone())
            .max()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let functional_limb_count = maximal_functional_coefficient.to_u32_digits().len().max(1);
        let term_limb_count = maximal_term_coefficient.to_u32_digits().len().max(1);
        if functional_limb_count > u32::MAX as usize || term_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }

        let mut functional_offsets = Vec::with_capacity(functional_count + 1);
        let mut functional_factors = Vec::new();
        let mut functional_signs = Vec::new();
        let mut functional_limbs = Vec::new();
        let receiver_factor_offsets = primitive_frame.receiver_factor_offsets.clone();
        let mut pair_left_functionals = Vec::with_capacity(pair_count);
        let mut pair_right_functionals = Vec::with_capacity(pair_count);
        let mut receiver_factor_pairs = Vec::with_capacity(term_count);
        let mut receiver_factor_signs = Vec::with_capacity(term_count);
        let mut receiver_factor_limbs = Vec::new();
        let mut maximal_functional_entry_population = 0_u64;
        let mut maximal_receiver_term_population = 0_u64;
        functional_offsets.push(0_u64);
        for functional in &primitive_frame.functionals {
            maximal_functional_entry_population = maximal_functional_entry_population.max(
                u64::try_from(functional.entries.len())
                    .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
            );
            for entry in &functional.entries {
                functional_factors.push(entry.factor);
                let (sign, limbs) = encode_integer(&entry.coefficient, functional_limb_count)?;
                functional_signs.push(sign);
                functional_limbs.extend(limbs);
            }
            functional_offsets.push(
                u64::try_from(functional_factors.len())
                    .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
            );
        }
        for &(left, right) in &primitive_frame.functional_pairs {
            pair_left_functionals.push(left);
            pair_right_functionals.push(right);
        }
        for factor in &primitive_frame.receiver_factors {
            receiver_factor_pairs.push(factor.coordinate);
            let (sign, limbs) = encode_integer(&factor.scale, term_limb_count)?;
            receiver_factor_signs.push(sign);
            receiver_factor_limbs.extend(limbs);
        }
        for pair in receiver_factor_offsets.windows(2) {
            maximal_receiver_term_population =
                maximal_receiver_term_population.max(pair[1] - pair[0]);
        }
        let occurrence_receiver_offsets_host = primitive_frame.occurrence_receiver_offsets.clone();
        let occurrence_term_offsets_host = occurrence_receiver_offsets_host
            .iter()
            .map(|receiver| {
                receiver_factor_offsets
                    .get(*receiver as usize)
                    .copied()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)
            })
            .collect::<Result<Vec<_>, _>>()?;
        if functional_offsets.len() != functional_count + 1
            || receiver_factor_offsets.len() != receiver_count + 1
            || pair_left_functionals.len() != pair_count
            || pair_right_functionals.len() != pair_count
            || receiver_factor_pairs.len() != term_count
            || receiver_factor_signs.len() != term_count
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let resident_octets = [
            std::mem::size_of_val(&functional_offsets[..]),
            std::mem::size_of_val(&functional_factors[..]),
            std::mem::size_of_val(&functional_signs[..]),
            std::mem::size_of_val(&functional_limbs[..]),
            std::mem::size_of_val(&receiver_factor_offsets[..]),
            std::mem::size_of_val(&pair_left_functionals[..]),
            std::mem::size_of_val(&pair_right_functionals[..]),
            std::mem::size_of_val(&receiver_factor_pairs[..]),
            std::mem::size_of_val(&receiver_factor_signs[..]),
            std::mem::size_of_val(&receiver_factor_limbs[..]),
            std::mem::size_of_val(occurrence_ports),
            std::mem::size_of_val(support_receiver_classes),
            std::mem::size_of_val(&support_quadratic_scale_limbs[..]),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .and_then(|held| {
            held.checked_add(
                sparse_pair_receiver_host
                    .as_ref()
                    .map(|host| host.6)
                    .unwrap_or(0),
            )
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let sparse_pair_receivers = sparse_pair_receiver_host
            .map(
                |(
                    offsets,
                    coordinates,
                    signs,
                    limbs,
                    coefficient_limb_count,
                    maximal_receiver_l1,
                    _resident_octets,
                )| {
                    Ok(ResidentSparseQuadraticReceiverMount {
                        receiver_offsets: Buffer::of(&offsets)?,
                        pair_coordinates: Buffer::of(&coordinates)?,
                        coefficient_signs: Buffer::of(&signs)?,
                        coefficient_limbs: Buffer::of(&limbs)?,
                        coefficient_limb_count,
                        maximal_receiver_l1,
                    })
                },
            )
            .transpose()?;
        self.addressed_factored_receiver_frame = Some(ResidentAddressedFactoredReceiverMount {
            identity_sha256: identity_sha256.clone(),
            occurrence_count: complexes.len() as u32,
            support_count: support_receiver_classes.len() as u32,
            family_count: self.families,
            opaque_receiver_count: self.receiver_count,
            generator_count,
            functional_count: functional_count as u32,
            pair_count: pair_count as u32,
            receiver_count: receiver_count as u32,
            term_count: term_count as u64,
            functional_limb_count: functional_limb_count as u32,
            term_limb_count: term_limb_count as u32,
            maximal_functional_entry_population,
            maximal_receiver_term_population,
            maximal_functional_coefficient,
            functional_offsets: Buffer::of(&functional_offsets)?,
            functional_factors: Buffer::of(&functional_factors)?,
            functional_signs: Buffer::of(&functional_signs)?,
            functional_limbs: Buffer::of(&functional_limbs)?,
            receiver_factor_offsets: Buffer::of(&receiver_factor_offsets)?,
            pair_left_functionals: Buffer::of(&pair_left_functionals)?,
            pair_right_functionals: Buffer::of(&pair_right_functionals)?,
            receiver_factor_pairs: Buffer::of(&receiver_factor_pairs)?,
            receiver_factor_signs: Buffer::of(&receiver_factor_signs)?,
            receiver_factor_limbs: Buffer::of(&receiver_factor_limbs)?,
            occurrence_ports: Buffer::of(occurrence_ports)?,
            occurrence_ports_host: occurrence_ports.to_vec(),
            support_receiver_classes: Buffer::of(support_receiver_classes)?,
            support_quadratic_scale_limbs: Buffer::of(&support_quadratic_scale_limbs)?,
            support_quadratic_scale_limb_count: support_quadratic_scale_limb_count as u32,
            maximal_support_quadratic_scale,
            occurrence_receiver_offsets_host,
            occurrence_term_offsets_host,
            sparse_pair_receivers,
            sparse_pair_boundary_conditioners: None,
            reconstruction_fibre: primitive_frame,
            resident_octets,
        });
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(resident_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(ResidentAddressedFactoredReceiverFrameReturn {
            identity_sha256,
            occurrence_population: support_receiver_classes.len() as u32,
            functional_population: functional_count as u32,
            receiver_population: receiver_count as u32,
            term_population: term_count as u64,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            host_ingress_octets: resident_octets,
            resident_octets,
            ambient_factor_square_materialized: false,
        })
    }
    pub fn mount_sparse_quadratic_returned_restrictions(
        &mut self,
        restrictions: &[ResidentQuadraticMomentRestriction],
        port_population: usize,
    ) -> Result<(), CudaRefineError> {
        let factors = self.factors as usize;
        if port_population == 0
            || port_population > u32::MAX as usize
            || factors == 0
            || restrictions.len() != port_population
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut by_port = vec![None; port_population];
        let mut maximal_coefficient = BigUint::zero();
        for restriction in restrictions {
            let port = restriction.port as usize;
            if port >= port_population
                || by_port[port].is_some()
                || restriction.factor_current.is_empty()
                || restriction
                    .factor_current
                    .windows(2)
                    .any(|pair| pair[0].0 >= pair[1].0)
                || restriction
                    .factor_current
                    .iter()
                    .any(|(factor, coefficient)| {
                        *factor as usize >= factors || coefficient.is_zero()
                    })
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            for (_, coefficient) in &restriction.factor_current {
                maximal_coefficient = maximal_coefficient.max(coefficient.clone());
            }
            by_port[port] = Some(restriction);
        }
        if by_port.iter().any(Option::is_none) || maximal_coefficient.is_zero() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let coefficient_limb_count = maximal_coefficient.to_u32_digits().len().max(1);
        if coefficient_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let entries = port_population
            .checked_mul(factors)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut dense = vec![
            0_u32;
            entries
                .checked_mul(coefficient_limb_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus,)?
        ];
        for (port, restriction) in by_port.into_iter().enumerate() {
            let restriction = restriction.ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            for (factor, coefficient) in &restriction.factor_current {
                let begin = (port * factors + *factor as usize) * coefficient_limb_count;
                let limbs = coefficient.to_u32_digits();
                dense[begin..begin + limbs.len()].copy_from_slice(&limbs);
            }
        }
        let identity_sha256 = serde_json::to_vec(&(
            "holonic-engine.sparse-quadratic-returned-restrictions.v1",
            restrictions,
            port_population,
            self.factors,
        ))
        .map(|bytes| {
            Sha256::digest(bytes)
                .iter()
                .map(|octet| format!("{octet:02x}"))
                .collect::<String>()
        })
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let resident_octets = u64::try_from(std::mem::size_of_val(dense.as_slice()))
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let frame = self
            .addressed_factored_receiver_frame
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if frame
            .sparse_pair_boundary_conditioners
            .as_ref()
            .is_some_and(|held| held.identity_sha256 == identity_sha256)
        {
            return Ok(());
        }
        if frame.sparse_pair_boundary_conditioners.is_some() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        frame.sparse_pair_boundary_conditioners =
            Some(ResidentSparseQuadraticBoundaryConditionerMount {
                port_population: port_population as u32,
                factor_population: self.factors,
                coefficient_limb_count: coefficient_limb_count as u32,
                maximal_coefficient,
                coefficients: Buffer::of(&dense)?,
                identity_sha256,
            });
        frame.resident_octets = frame
            .resident_octets
            .checked_add(resident_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(resident_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(())
    }
    pub(super) fn mount_quadratic_action(
        &mut self,
        generator_count: u32,
        generator_targets: &[u32],
    ) -> Result<(), CudaRefineError> {
        let native_factors = self.factors as usize;
        let generators = generator_count as usize;
        if generators == 0
            || generator_targets.len() != generators.saturating_mul(native_factors)
            || generator_targets
                .iter()
                .any(|target| *target >= self.factors)
            || self.receiver_count == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut identity = Sha256::new();
        identity.update(b"holonic-engine.resident-quadratic-action.v1");
        identity.update(self.factors.to_le_bytes());
        identity.update(self.receiver_count.to_le_bytes());
        identity.update(generator_count.to_le_bytes());
        for target in generator_targets {
            identity.update(target.to_le_bytes());
        }
        let identity = identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        if let Some(mounted) = &self.quadratic_action {
            return if mounted.identity_sha256 == identity
                && mounted.generator_targets == generator_targets
                && mounted.generator_count == generator_count
            {
                Ok(())
            } else {
                Err(CudaRefineError::MembraneInteriorWordShape)
            };
        }
        let factor_receiver_classes = self
            .factor_receiver_classes
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let receiver_class_counts = self
            .receiver_class_counts
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if factor_receiver_classes.len() != native_factors * self.receiver_count as usize
            || receiver_class_counts.len() != self.receiver_count as usize
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut receiver_class_bases = Vec::with_capacity(self.receiver_count as usize + 1);
        receiver_class_bases.push(0_u32);
        for count in receiver_class_counts {
            let next = receiver_class_bases
                .last()
                .copied()
                .and_then(|base| base.checked_add(*count))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            receiver_class_bases.push(next);
        }
        let total_receiver_classes = *receiver_class_bases
            .last()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut source_class_groups = vec![Vec::<u32>::new(); total_receiver_classes as usize];
        for source in 0..native_factors {
            for receiver in 0..self.receiver_count as usize {
                let local_class =
                    factor_receiver_classes[source * self.receiver_count as usize + receiver];
                if local_class >= receiver_class_counts[receiver] {
                    return Err(CudaRefineError::MembraneInteriorWordShape);
                }
                let class = receiver_class_bases[receiver] + local_class;
                source_class_groups[class as usize].push(source as u32);
            }
        }
        let mut source_class_factor_offsets =
            Vec::with_capacity(total_receiver_classes as usize + 1);
        let mut source_class_factors: Vec<u32> =
            Vec::with_capacity(native_factors.saturating_mul(self.receiver_count as usize));
        source_class_factor_offsets.push(0_u64);
        for group in &source_class_groups {
            source_class_factors.extend(group);
            source_class_factor_offsets.push(
                u64::try_from(source_class_factors.len())
                    .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
            );
        }
        let mut generator_class_factor_offsets = generators
            .checked_mul(total_receiver_classes as usize + 1)
            .map(Vec::with_capacity)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut generator_class_factors: Vec<u32> = Vec::with_capacity(
            generators
                .saturating_mul(native_factors)
                .saturating_mul(self.receiver_count as usize),
        );
        for generator in 0..generators {
            let mut groups = vec![Vec::<u32>::new(); total_receiver_classes as usize];
            for source in 0..native_factors {
                let target = generator_targets[generator * native_factors + source] as usize;
                for receiver in 0..self.receiver_count as usize {
                    let local_class =
                        factor_receiver_classes[target * self.receiver_count as usize + receiver];
                    let class = receiver_class_bases[receiver] + local_class;
                    groups[class as usize].push(source as u32);
                }
            }
            generator_class_factor_offsets.push(
                u64::try_from(generator_class_factors.len())
                    .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
            );
            for group in groups {
                generator_class_factors.extend(group);
                generator_class_factor_offsets.push(
                    u64::try_from(generator_class_factors.len())
                        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
                );
            }
        }
        let invariant_octets = [
            std::mem::size_of_val(generator_targets),
            std::mem::size_of_val(factor_receiver_classes.as_slice()),
            std::mem::size_of_val(&receiver_class_bases[..]),
            std::mem::size_of_val(&source_class_factor_offsets[..]),
            std::mem::size_of_val(&source_class_factors[..]),
            std::mem::size_of_val(&generator_class_factor_offsets[..]),
            std::mem::size_of_val(&generator_class_factors[..]),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        self.quadratic_action = Some(ResidentQuadraticActionMount {
            identity_sha256: identity,
            generator_targets: generator_targets.to_vec(),
            generator_count,
            receiver_class_count: total_receiver_classes,
            native_generator_targets: Buffer::of(generator_targets)?,
            native_factor_receiver_classes: Buffer::of(factor_receiver_classes)?,
            receiver_class_bases: Buffer::of(&receiver_class_bases)?,
            source_class_factor_offsets: Buffer::of(&source_class_factor_offsets)?,
            source_class_factors: Buffer::of(&source_class_factors)?,
            generator_class_factor_offsets: Buffer::of(&generator_class_factor_offsets)?,
            generator_class_factors: Buffer::of(&generator_class_factors)?,
        });
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(invariant_octets)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        Ok(())
    }
}
