impl GranularFactorAction {
    pub fn validate(&self) -> Result<(), NativeGranularPotentialError> {
        let factor_population = self.native_states.len();
        if factor_population == 0
            || self.native_states.iter().collect::<BTreeSet<_>>().len() != factor_population
            || self.receiver_factors.len() != factor_population
            || self.generators.is_empty()
            || !is_digest(&self.source_action_identity_sha256)
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the higher factor action lost its complete native population".to_owned(),
            ));
        }
        let receiver_family = self.receiver_factors[0]
            .iter()
            .map(|factor| factor.receiver)
            .collect::<BTreeSet<_>>();
        if receiver_family.is_empty()
            || self.receiver_factors.iter().any(|factors| {
                factors.is_empty()
                    || factors.windows(2).any(|pair| pair[0] >= pair[1])
                    || factors
                        .iter()
                        .map(|factor| factor.receiver)
                        .collect::<BTreeSet<_>>()
                        != receiver_family
            })
            || self
                .generators
                .windows(2)
                .any(|pair| pair[0].generator >= pair[1].generator)
            || self.generators.iter().any(|generator| {
                generator.targets.len() != factor_population
                    || generator
                        .targets
                        .iter()
                        .any(|target| *target as usize >= factor_population)
                    || !is_digest(&generator.source_square_identity_sha256)
            })
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the higher factor action is not a total receiver/history generator family"
                    .to_owned(),
            ));
        }
        Ok(())
    }
}

impl NativeGranularPotentialBuilder {
    pub fn new(
        factor_addresses: &[String],
        action: GranularFactorAction,
    ) -> Result<Self, NativeGranularPotentialError> {
        if factor_addresses.is_empty()
            || factor_addresses.iter().any(String::is_empty)
            || factor_addresses.iter().collect::<BTreeSet<_>>().len() != factor_addresses.len()
        {
            return Err(NativeGranularPotentialError::FactorOutsideBase);
        }
        action.validate()?;
        if action.native_states.len() != factor_addresses.len()
            || action.receiver_factors.len() != factor_addresses.len()
        {
            return Err(NativeGranularPotentialError::FactorOutsideBase);
        }
        let factor_faces = factor_addresses
            .iter()
            .enumerate()
            .map(|(at, _address)| {
                let factor = u32::try_from(at).map_err(|_| NativeGranularPotentialError::Extent)?;
                let native_address = native_factor_address(
                    factor,
                    action.native_states[at],
                    &action.receiver_factors[at],
                );
                let identity = factor_identity(&native_address);
                Ok::<_, NativeGranularPotentialError>(GranularFactorFace {
                    factor,
                    // `address` is only a cardinality/order witness at this boundary.  The
                    // resident address is derived from the native future-consequence face.
                    factor_address: native_address,
                    native: action.native_states[at],
                    receiver_factors: action.receiver_factors[at].clone(),
                    receiver_schema: identity.schema(),
                    receiver_words: identity.words().to_vec(),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let factor_bit_words = factor_faces
            .len()
            .checked_add(u64::BITS as usize - 1)
            .ok_or(NativeGranularPotentialError::Extent)?
            / u64::BITS as usize;
        let ports = port_population();
        let factor_generators = action
            .generators
            .into_iter()
            .map(|generator| NativeGranularFactorGenerator {
                generator: generator.generator,
                targets: generator.targets,
            })
            .collect();
        Ok(Self {
            factor_faces,
            factor_generators,
            factor_bit_words,
            port_occurrences: vec![0; ports],
            port_support_bits: vec![0; ports * factor_bit_words],
            port_factor_occurrences: vec![0; ports * factor_addresses.len()],
            exposure_lineage: Vec::new(),
            material_octet_population: 0,
            material_port_population: 0,
        })
    }

    /// Cross one addressed chronology of exterior occurrences without erasing the return joins.
    /// Each occurrence contributes an opening seam, its codec-port path, and a closure seam; the
    /// closure-to-opening edge between successive occurrences is the caused world-tube lineage.
    /// Only oriented port incidence, exact factor support, extent, and lineage survive.
    pub fn receive_world_tube<'a, Messages>(
        &mut self,
        factor: u32,
        messages: Messages,
    ) -> Result<(), NativeGranularPotentialError>
    where
        Messages: IntoIterator<Item = (&'a str, &'a [u8])>,
    {
        let factor_at =
            usize::try_from(factor).map_err(|_| NativeGranularPotentialError::Extent)?;
        self.factor_faces
            .get(factor_at)
            .filter(|face| face.factor == factor)
            .ok_or(NativeGranularPotentialError::FactorOutsideBase)?;
        let factor_word = factor_at / u64::BITS as usize;
        let mask = 1u64 << (factor_at % u64::BITS as usize);
        let mut crossed = false;
        for (occurrence_identity, payload) in messages {
            if occurrence_identity.is_empty() || payload.is_empty() {
                return Err(NativeGranularPotentialError::EmptyOccurrence);
            }
            crossed = true;
            let extent =
                u64::try_from(payload.len()).map_err(|_| NativeGranularPotentialError::Extent)?;
            self.material_octet_population = self
                .material_octet_population
                .checked_add(extent)
                .ok_or(NativeGranularPotentialError::Extent)?;
            let occurrence_ports = extent
                .checked_add(2)
                .ok_or(NativeGranularPotentialError::Extent)?;
            self.material_port_population = self
                .material_port_population
                .checked_add(occurrence_ports)
                .ok_or(NativeGranularPotentialError::Extent)?;
            self.receive_port(factor_at, factor_word, mask, GranularExteriorPort::Opening)?;
            for octet in payload.iter().copied() {
                self.receive_port(
                    factor_at,
                    factor_word,
                    mask,
                    GranularExteriorPort::Octet(octet),
                )?;
            }
            self.receive_port(factor_at, factor_word, mask, GranularExteriorPort::Closure)?;
            self.exposure_lineage.push(GranularExposureLineage {
                factor,
                occurrence_identity_sha256: hex_sha256(occurrence_identity.as_bytes()),
                caused_octet_population: extent,
            });
        }
        if !crossed {
            return Err(NativeGranularPotentialError::EmptyOccurrence);
        }
        Ok(())
    }

    fn receive_port(
        &mut self,
        factor_at: usize,
        factor_word: usize,
        mask: u64,
        port: GranularExteriorPort,
    ) -> Result<(), NativeGranularPotentialError> {
        let port_at = port_index(&port);
        self.port_occurrences[port_at] = self.port_occurrences[port_at]
            .checked_add(1)
            .ok_or(NativeGranularPotentialError::Extent)?;
        let port_factor = port_at
            .checked_mul(self.factor_faces.len())
            .and_then(|base| base.checked_add(factor_at))
            .ok_or(NativeGranularPotentialError::Extent)?;
        self.port_factor_occurrences[port_factor] = self.port_factor_occurrences[port_factor]
            .checked_add(1)
            .ok_or(NativeGranularPotentialError::Extent)?;
        self.port_support_bits[port_at * self.factor_bit_words + factor_word] |= mask;
        Ok(())
    }

    pub fn finish(self) -> Result<NativeGranularPotential, NativeGranularPotentialError> {
        if self.exposure_lineage.is_empty() || self.material_octet_population == 0 {
            return Err(NativeGranularPotentialError::EmptyOccurrence);
        }
        let ports = port_population();
        let mut supports = Vec::<Vec<u32>>::new();
        let mut support_lookup = BTreeMap::<Vec<u32>, u32>::new();
        let mut root_bits = vec![0u64; self.factor_bit_words];
        for port in 0..ports {
            for (root, held) in root_bits.iter_mut().zip(self.port_bits(port)) {
                *root |= *held;
            }
        }
        let root_support = intern_support(
            factors_from_bits(&root_bits, self.factor_faces.len())?,
            &mut supports,
            &mut support_lookup,
        )?;
        let mut root = NativeGranularState {
            recurrence_multiplicity: self.material_port_population,
            support: root_support,
            transitions: Vec::new(),
        };
        for port in 0..ports {
            if self.port_occurrences[port] == 0 {
                continue;
            }
            let support = intern_support(
                factors_from_bits(self.port_bits(port), self.factor_faces.len())?,
                &mut supports,
                &mut support_lookup,
            )?;
            root.transitions.push(GranularPortTransition {
                port: indexed_port(port).ok_or(NativeGranularPotentialError::CarrierExtent)?,
                // Exterior ports are boundary faces of one universal root; they are never
                // recurrent state addresses.
                target: 0,
                recurrence_multiplicity: self.port_occurrences[port],
                support,
                factor_current: self.port_factor_current(port)?,
            });
        }
        let states = vec![root];
        let mut potential = NativeGranularPotential {
            schema: NATIVE_GRANULAR_POTENTIAL_SCHEMA.to_owned(),
            supports,
            states,
            factor_faces: self.factor_faces,
            factor_generators: self.factor_generators,
            identity_sha256: String::new(),
        };
        potential.identity_sha256 = potential.rederived_identity();
        potential.validate()?;
        Ok(potential)
    }

    fn port_bits(&self, port: usize) -> &[u64] {
        let from = port * self.factor_bit_words;
        &self.port_support_bits[from..from + self.factor_bit_words]
    }

    fn port_factor_current(
        &self,
        port: usize,
    ) -> Result<Vec<GranularFactorCurrent>, NativeGranularPotentialError> {
        let base = port
            .checked_mul(self.factor_faces.len())
            .ok_or(NativeGranularPotentialError::Extent)?;
        self.port_factor_occurrences[base..base + self.factor_faces.len()]
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, incidence)| *incidence != 0)
            .map(|(factor, incidence)| {
                Ok(GranularFactorCurrent {
                    factor: u32::try_from(factor)
                        .map_err(|_| NativeGranularPotentialError::CarrierExtent)?,
                    incidence: BigUint::from(incidence),
                })
            })
            .collect()
    }
}
