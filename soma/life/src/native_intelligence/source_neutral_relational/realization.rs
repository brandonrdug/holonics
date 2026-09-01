//! Exterior realization conduct owner implementations.

use super::*;
impl SourceNeutralExteriorRealizationMorphology {
    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn factor_population(&self) -> usize {
        self.factor_population as usize
    }

    pub fn site_population(&self) -> usize {
        self.sites.len()
    }

    pub fn face_population(&self) -> usize {
        self.face_population as usize
    }

    pub fn cell_population(&self) -> usize {
        self.cell_population as usize
    }

    pub fn relational_identity(&self) -> &str {
        &self.relational_identity_sha256
    }

    pub fn transition_population(&self) -> usize {
        self.transitions.len()
    }

    pub fn developmental_transition_population(&self) -> u64 {
        self.developmental_transition_population
    }

    fn source_transitions(
        &self,
        source_port: u16,
    ) -> &[SourceNeutralExteriorRealizationTransition] {
        let begin = self
            .transitions
            .partition_point(|transition| transition.source < source_port);
        let end = self
            .transitions
            .partition_point(|transition| transition.source <= source_port);
        &self.transitions[begin..end]
    }

    fn face_source_transitions(
        &self,
        face: u32,
        source_port: u16,
    ) -> &[SourceNeutralExteriorRealizationTransition] {
        let source = self.source_transitions(source_port);
        let begin = source.partition_point(|transition| transition.face < face);
        let end = source.partition_point(|transition| transition.face <= face);
        &source[begin..end]
    }

    /// The oriented cell boundary supplies the target incidence. The exterior port chooses a
    /// generator row only; its displayed coordinate never chooses a site. A missing successor is
    /// the exterior boundary and therefore leaves the carrier diagonal with an explicit residual.
    fn successor_transport_target(
        &self,
        relational: &SourceNeutralRelationalMorphology,
        site_quotient: &SourceNeutralExteriorSiteHistoryQuotient,
        source_site: &SourceNeutralExteriorRealizationSite,
        factor: u32,
        phase: u8,
        transition_population: u64,
    ) -> Result<Option<(u32, u32, BigUint)>, SourceNeutralRelationalError> {
        let Some(successor_site) = source_site.successor_site else {
            return Ok(None);
        };
        let successor = self.site(successor_site)?;
        let cell = relational
            .cells
            .get(source_site.cell as usize)
            .ok_or(SourceNeutralRelationalError::Quotient)?;
        let positions = relational_boundary_positions(cell.oriented_boundary.len())?;
        let source_at = positions
            .iter()
            .position(|position| *position == source_site.boundary_position)
            .ok_or(SourceNeutralRelationalError::Quotient)?;
        let expected_position = positions
            .get(source_at + 1)
            .copied()
            .ok_or(SourceNeutralRelationalError::Quotient)?;
        if successor.cell != source_site.cell || successor.boundary_position != expected_position {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        let face_population = phase_population(
            &relational
                .faces
                .get(successor.face as usize)
                .ok_or(SourceNeutralRelationalError::Quotient)?
                .phase_population,
            factor,
            phase,
        )
        .ok_or(SourceNeutralRelationalError::Quotient)?;
        let target_site = site_quotient.class(successor_site)?;
        let target_carrier = site_quotient.carrier(target_site, factor, phase)?;
        Ok(Some((
            target_carrier,
            target_site,
            BigUint::from(transition_population)
                * BigUint::from(successor.incidence_population)
                * BigUint::from(face_population),
        )))
    }

    pub(super) fn site(
        &self,
        site: u32,
    ) -> Result<&SourceNeutralExteriorRealizationSite, SourceNeutralRelationalError> {
        self.sites
            .get(site as usize)
            .ok_or(SourceNeutralRelationalError::Quotient)
    }

    pub(crate) fn found_site_history_quotient(
        &self,
        relational: &SourceNeutralRelationalMorphology,
    ) -> Result<SourceNeutralExteriorSiteHistoryQuotient, SourceNeutralRelationalError> {
        SourceNeutralExteriorSiteHistoryQuotient::found(self, relational)
    }

    /// Push the complete reacted native current through the rested local boundary incidence and
    /// meet it with one separately caused realization current.
    ///
    /// The contraction is quadratic because `native_sections` is the exact rank-one
    /// representation `sum_s w_s x_s x_s^T` returned by the resident ecology.  Summing the
    /// vectors first would manufacture cross terms and destroy their occurrence lineage.  The
    /// initial modulus founds a projective phase; it is not a probability score.  The phase meets
    /// the disjoint half-open partition whose interval measures are the returned target currents.
    pub(crate) fn realize_native_section(
        &self,
        relational: &SourceNeutralRelationalMorphology,
        site_quotient: &SourceNeutralExteriorSiteHistoryQuotient,
        resident: &mut ResidentMembraneInteriorWord,
        native_section_identity_sha256: &str,
        native_current_passage_identity_sha256: &str,
        source_port: u16,
        native_sections: &[AddressedCurrentSection],
        native_oriented_faces: &[SourceNeutralNativeOrientedFace],
        entering_realization_current_identity_sha256: &str,
        entering_realization_current: BigUint,
    ) -> Result<SourceNeutralExteriorRealizationPassage, SourceNeutralRelationalError> {
        self.validate_relational(relational)?;
        if !is_digest(native_section_identity_sha256)
            || !is_digest(native_current_passage_identity_sha256)
            || !is_digest(entering_realization_current_identity_sha256)
            || source_port >= 257
            || native_sections.is_empty()
            || native_oriented_faces.is_empty()
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }

        let factor_current = self.native_factor_current(native_sections)?;
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "oriented-realization-positive-factors={}",
                factor_current.len()
            );
        }
        let oriented_factor_current =
            self.native_complex_factor_current(native_sections, native_oriented_faces)?;
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "oriented-realization-complex-factors={}",
                oriented_factor_current.len()
            );
        }
        let (complex_site_current, phase_modulus) = self.lift_complex_factor_current(
            relational,
            site_quotient,
            source_port,
            &factor_current,
            &oriented_factor_current,
        )?;
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "oriented-realization-complex-sites={}",
                complex_site_current.len()
            );
        }
        let site_current = positive_site_shadow(&complex_site_current)?;
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "oriented-realization-positive-shadow={}",
                site_current.len()
            );
        }
        let phase_numerator = entering_realization_current % &phase_modulus;
        self.realize_site_current(
            relational,
            site_quotient,
            resident,
            native_section_identity_sha256,
            native_current_passage_identity_sha256,
            source_port,
            factor_current,
            oriented_factor_current,
            native_oriented_faces.to_vec(),
            site_current,
            complex_site_current,
            entering_realization_current_identity_sha256,
            phase_numerator,
            phase_modulus,
        )
    }

    fn native_factor_current(
        &self,
        native_sections: &[AddressedCurrentSection],
    ) -> Result<Vec<SourceNeutralExteriorRealizationFactorCurrent>, SourceNeutralRelationalError>
    {
        let mut factor_current = BTreeMap::<u32, BigUint>::new();
        for section in native_sections {
            if section.quadratic_weight.is_zero()
                || section.factor_current.is_empty()
                || section
                    .factor_current
                    .windows(2)
                    .any(|pair| pair[0].0 >= pair[1].0)
                || section
                    .factor_current
                    .iter()
                    .any(|(factor, current)| *factor >= self.factor_population || current.is_zero())
            {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            for (factor, coefficient) in &section.factor_current {
                let contribution = &section.quadratic_weight * coefficient * coefficient;
                *factor_current.entry(*factor).or_default() += contribution;
            }
        }
        factor_current.retain(|_, current| !current.is_zero());
        if factor_current.is_empty() {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        Ok(factor_current
            .into_iter()
            .map(
                |(factor, current)| SourceNeutralExteriorRealizationFactorCurrent {
                    factor,
                    current: Ratio::from_integer(current),
                },
            )
            .collect())
    }

    /// Continue one already-founded exterior realization without remounting the emitted boundary
    /// face as semantic ingress.  The prior returned factor section and local phase are the exact
    /// joining object.  This is the boundary world-tube recurrence, not another HNN inference.
    pub(crate) fn continue_realization(
        &self,
        relational: &SourceNeutralRelationalMorphology,
        site_quotient: &SourceNeutralExteriorSiteHistoryQuotient,
        resident: &mut ResidentMembraneInteriorWord,
        prior: &SourceNeutralExteriorRealizationPassage,
    ) -> Result<SourceNeutralExteriorRealizationPassage, SourceNeutralRelationalError> {
        // `SourceNeutralEcologyRest::read` validates this immutable morphology and its exact
        // relational join before a resident body can own it.  Rehashing every face, cell, site,
        // and local transition at each continuation would replay the sealed rest rather than
        // conduct the already-admitted local current.  The joining passage below still validates
        // its complete fibre and names this morphology by identity.
        prior.validate()?;
        if prior.morphology_identity_sha256 != self.identity_sha256
            || prior.selected_target_port >= 257
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        self.realize_site_current(
            relational,
            site_quotient,
            resident,
            &prior.native_section_identity_sha256,
            &prior.native_current_passage_identity_sha256,
            prior.selected_target_port,
            prior.returned_factor_current.clone(),
            prior.oriented_factor_current.clone(),
            prior.native_oriented_faces.clone(),
            prior.returned_site_current.clone(),
            prior.returned_complex_site_current.clone(),
            &prior.returned_realization_current_identity_sha256,
            prior.returned_phase_numerator.clone(),
            prior.returned_phase_denominator.clone(),
        )
    }

    /// Pull the joined complex factor section into the same exact realization incidence as its
    /// positive receiver shadow. The common positive scale is returned separately as the phase
    /// modulus and is not inserted into every hot coefficient: it cancels exactly from the later
    /// normalized port family. Real/imaginary orientation and cancellation survive this lawful
    /// projective rebase.
    fn lift_complex_factor_current(
        &self,
        relational: &SourceNeutralRelationalMorphology,
        site_quotient: &SourceNeutralExteriorSiteHistoryQuotient,
        source_port: u16,
        positive_factor_current: &[SourceNeutralExteriorRealizationFactorCurrent],
        factor_current: &[SourceNeutralExteriorRealizationOrientedFactorCurrent],
    ) -> Result<
        (
            Vec<SourceNeutralExteriorRealizationComplexSiteCurrent>,
            BigUint,
        ),
        SourceNeutralRelationalError,
    > {
        if positive_factor_current.is_empty()
            || factor_current.is_empty()
            || factor_current
                .windows(2)
                .any(|pair| pair[0].factor >= pair[1].factor)
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        let by_factor = factor_current
            .iter()
            .map(|current| (current.factor, &current.current))
            .collect::<BTreeMap<_, _>>();
        let positive_by_factor = positive_factor_current
            .iter()
            .map(|current| (current.factor, &current.current))
            .collect::<BTreeMap<_, _>>();
        let active_faces = self
            .source_transitions(source_port)
            .iter()
            .map(|transition| transition.face)
            .collect::<BTreeSet<_>>();
        let mut lifted = BTreeMap::<(u32, u32, u8, u16), BigUint>::new();
        let mut projective_scale = BigUint::zero();
        for (site_at, site) in self.sites.iter().enumerate() {
            if site.boundary_position != 0 || !active_faces.contains(&site.face) {
                continue;
            }
            let face = relational
                .faces
                .get(site.face as usize)
                .ok_or(SourceNeutralRelationalError::Quotient)?;
            let cell = relational
                .cells
                .get(site.cell as usize)
                .ok_or(SourceNeutralRelationalError::Quotient)?;
            for cell_population in &cell.phase_population {
                let Some(_current) = by_factor.get(&cell_population.factor) else {
                    continue;
                };
                let positive = positive_by_factor
                    .get(&cell_population.factor)
                    .ok_or(SourceNeutralRelationalError::Quotient)?;
                if !cell.oriented_boundary.iter().all(|face_at| {
                    relational.faces[*face_at as usize]
                        .phase_population
                        .binary_search_by_key(
                            &(cell_population.factor, cell_population.phase),
                            |population| (population.factor, population.phase),
                        )
                        .is_ok()
                }) {
                    continue;
                }
                let face_population = phase_population(
                    &face.phase_population,
                    cell_population.factor,
                    cell_population.phase,
                )
                .ok_or(SourceNeutralRelationalError::Quotient)?;
                let site_class = site_quotient.class(
                    u32::try_from(site_at).map_err(|_| SourceNeutralRelationalError::Extent)?,
                )?;
                let carrier = site_quotient.carrier(
                    site_class,
                    cell_population.factor,
                    cell_population.phase,
                )?;
                let incidence_scale = BigUint::from(cell_population.occurrence_population)
                    * BigUint::from(face_population)
                    * BigUint::from(site.incidence_population);
                let positive_contribution =
                    (*positive).clone() * Ratio::from_integer(incidence_scale.clone());
                if positive_contribution.denom() != &BigUint::one() {
                    return Err(SourceNeutralRelationalError::Quotient);
                }
                projective_scale += positive_contribution.numer();
                *lifted
                    .entry((
                        carrier,
                        cell_population.factor,
                        cell_population.phase,
                        source_port,
                    ))
                    .or_default() += incidence_scale;
            }
        }
        lifted.retain(|_, coefficient| !coefficient.is_zero());
        if lifted.is_empty() || projective_scale.is_zero() {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        Ok((
            lifted
                .into_iter()
                .map(|((carrier, factor, phase, local_source_port), numerator)| {
                    let (site, _, _) = site_quotient.carrier_representative(carrier)?;
                    Ok(SourceNeutralExteriorRealizationComplexSiteCurrent {
                        carrier,
                        site,
                        factor,
                        phase,
                        local_source_port,
                        incidence_coefficient: Ratio::from_integer(numerator),
                    })
                })
                .collect::<Result<Vec<_>, SourceNeutralRelationalError>>()?,
            projective_scale,
        ))
    }

    /// Apply the sparse oriented port law before any exterior target is selected.  Each returned
    /// term retains source site, target site, local boundary state, factor, and phase.  The
    /// exterior target population is therefore a later projection of this pair-current fibre.
    fn complex_site_transport_contributions(
        &self,
        relational: &SourceNeutralRelationalMorphology,
        site_quotient: &SourceNeutralExteriorSiteHistoryQuotient,
        site_current: &[SourceNeutralExteriorRealizationComplexSiteCurrent],
    ) -> Result<
        Vec<SourceNeutralExteriorComplexSiteTransportContribution>,
        SourceNeutralRelationalError,
    > {
        // The public entry deed validates the sealed morphology/relational pair once.  This
        // private contraction owns only the sparse addressed current and must not rescan the
        // complete rested atlas for every emitted occurrence.
        let mut contributions = Vec::new();
        for current in site_current {
            let (source_site_class, _, _) =
                site_quotient.carrier_representative(current.carrier)?;
            if current.site != source_site_class
                || site_quotient.carrier(source_site_class, current.factor, current.phase)?
                    != current.carrier
            {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            let source_site = self.site(site_quotient.representative(source_site_class)?)?;
            let transitions =
                self.face_source_transitions(source_site.face, current.local_source_port);
            if transitions.is_empty() {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            let mut row = Vec::<(u16, u32, u32, u16, BigUint)>::new();
            for transition in transitions {
                let successor = self.successor_transport_target(
                    relational,
                    site_quotient,
                    source_site,
                    current.factor,
                    current.phase,
                    transition.occurrence_population,
                )?;
                let (target_carrier, target_site, oriented_weight) = successor.unwrap_or((
                    current.carrier,
                    source_site_class,
                    BigUint::from(transition.occurrence_population),
                ));
                // Closure is a distinct boundary passage: an interior close crosses to the next
                // incidence through Opening, while an exterior close returns the closure port.
                // An ordinary generator uses the same addressed incidence map but retains its
                // own local target port.
                let (exterior_target_port, target_local_source_port) =
                    if transition.target == 257 && source_site.successor_site.is_some() {
                        (u16::from(b' ') + 1, 0)
                    } else {
                        (transition.target, transition.target)
                    };
                row.push((
                    exterior_target_port,
                    target_carrier,
                    target_site,
                    target_local_source_port,
                    oriented_weight,
                ));
            }
            let row_total = row
                .iter()
                .map(|(_, _, _, _, weight)| weight.clone())
                .sum::<BigUint>();
            if row.is_empty() || row_total.is_zero() {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            for (
                exterior_target_port,
                target_carrier,
                target_site,
                target_local_source_port,
                oriented_weight,
            ) in row
            {
                let transported =
                    &current.incidence_coefficient * Ratio::new(oriented_weight, row_total.clone());
                if transported.is_zero() {
                    return Err(SourceNeutralRelationalError::Quotient);
                }
                site_quotient.carrier_representative(target_carrier)?;
                contributions.push(SourceNeutralExteriorComplexSiteTransportContribution {
                    exterior_target_port,
                    source_carrier: current.carrier,
                    source_site: source_site_class,
                    source_local_port: current.local_source_port,
                    target_carrier,
                    target_site,
                    target_local_source_port,
                    factor: current.factor,
                    phase: current.phase,
                    incidence_coefficient: transported,
                });
            }
        }
        if contributions.is_empty() {
            Err(SourceNeutralRelationalError::Quotient)
        } else {
            Ok(contributions)
        }
    }

    /// Compose the retained response-face fibre with the addressed site transport before either
    /// endpoint is projected away. The result is the sparse `c_m d_(m,z,f) A_p(z,z')`
    /// population consumed by the target/port junction below.
    fn addressed_realization_pair_currents(
        contributions: &[SourceNeutralExteriorComplexSiteTransportContribution],
        oriented_factor_current: &[SourceNeutralExteriorRealizationOrientedFactorCurrent],
    ) -> Result<Vec<SourceNeutralAddressedRealizationPairCurrent>, SourceNeutralRelationalError>
    {
        let factors = oriented_factor_current
            .iter()
            .map(|factor| (factor.factor, factor))
            .collect::<BTreeMap<_, _>>();
        let mut pairs = Vec::new();
        for contribution in contributions {
            let factor = factors
                .get(&contribution.factor)
                .ok_or(SourceNeutralRelationalError::Quotient)?;
            let coefficient = Ratio::new(
                BigInt::from(contribution.incidence_coefficient.numer().clone()),
                BigInt::from(contribution.incidence_coefficient.denom().clone()),
            );
            for response in &factor.pair_currents {
                let current = response.current.scaled(&coefficient);
                if current.is_zero() {
                    return Err(SourceNeutralRelationalError::Quotient);
                }
                pairs.push(SourceNeutralAddressedRealizationPairCurrent {
                    response: response.clone(),
                    source_carrier: contribution.source_carrier,
                    source_site: contribution.source_site,
                    source_local_port: contribution.source_local_port,
                    target_carrier: contribution.target_carrier,
                    target_site: contribution.target_site,
                    target_local_port: contribution.target_local_source_port,
                    exterior_target_port: contribution.exterior_target_port,
                    factor: contribution.factor,
                    phase: contribution.phase,
                    current,
                });
            }
        }
        pairs.sort();
        if pairs.is_empty() || pairs.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        Ok(pairs)
    }

    fn realize_site_current(
        &self,
        relational: &SourceNeutralRelationalMorphology,
        site_quotient: &SourceNeutralExteriorSiteHistoryQuotient,
        resident: &mut ResidentMembraneInteriorWord,
        native_section_identity_sha256: &str,
        native_current_passage_identity_sha256: &str,
        source_port: u16,
        factor_current: Vec<SourceNeutralExteriorRealizationFactorCurrent>,
        oriented_factor_current: Vec<SourceNeutralExteriorRealizationOrientedFactorCurrent>,
        native_oriented_faces: Vec<SourceNeutralNativeOrientedFace>,
        site_current: Vec<SourceNeutralExteriorRealizationSiteCurrent>,
        complex_site_current: Vec<SourceNeutralExteriorRealizationComplexSiteCurrent>,
        entering_realization_current_identity_sha256: &str,
        mut entering_phase_numerator: BigUint,
        mut entering_phase_denominator: BigUint,
    ) -> Result<SourceNeutralExteriorRealizationPassage, SourceNeutralRelationalError> {
        // Morphology validity belongs to rest admission.  Recurrence validates the entering
        // current and its exact passage join below; a complete morphology rehash here would turn
        // each local successor into an exterior remount.
        if !is_digest(native_section_identity_sha256)
            || !is_digest(native_current_passage_identity_sha256)
            || !is_digest(entering_realization_current_identity_sha256)
            || source_port >= 257
            || factor_current.is_empty()
            || factor_current
                .windows(2)
                .any(|pair| pair[0].factor >= pair[1].factor)
            || factor_current.iter().any(|current| {
                current.factor >= self.factor_population || current.current.is_zero()
            })
            || oriented_factor_current.is_empty()
            || oriented_factor_current
                .windows(2)
                .any(|pair| pair[0].factor >= pair[1].factor)
            || oriented_factor_current.iter().any(|current| {
                current.factor >= self.factor_population || current.current.is_zero()
            })
            || native_oriented_faces.is_empty()
            || native_oriented_faces
                .windows(2)
                .any(|pair| pair[0].mode >= pair[1].mode)
            || site_current.is_empty()
            || site_current.windows(2).any(|pair| {
                (
                    pair[0].carrier,
                    pair[0].factor,
                    pair[0].phase,
                    pair[0].local_source_port,
                ) >= (
                    pair[1].carrier,
                    pair[1].factor,
                    pair[1].phase,
                    pair[1].local_source_port,
                )
            })
            || site_current.iter().any(|current| {
                current.carrier as usize >= site_quotient.quotient_population()
                    || current.factor >= self.factor_population
                    || current.phase > 2
                    || current.local_source_port >= 257
                    || current.current.is_zero()
            })
            || complex_site_current.is_empty()
            || complex_site_current.windows(2).any(|pair| {
                (
                    pair[0].carrier,
                    pair[0].factor,
                    pair[0].phase,
                    pair[0].local_source_port,
                ) >= (
                    pair[1].carrier,
                    pair[1].factor,
                    pair[1].phase,
                    pair[1].local_source_port,
                )
            })
            || complex_site_current.iter().any(|current| {
                current.carrier as usize >= site_quotient.quotient_population()
                    || current.factor >= self.factor_population
                    || current.phase > 2
                    || current.local_source_port >= 257
                    || current.incidence_coefficient.is_zero()
            })
            || entering_phase_denominator.is_zero()
            || entering_phase_numerator >= entering_phase_denominator
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        reduce_fraction(
            &mut entering_phase_numerator,
            &mut entering_phase_denominator,
        )?;

        let contributions = self.complex_site_transport_contributions(
            relational,
            site_quotient,
            &complex_site_current,
        )?;
        let pair_currents =
            Self::addressed_realization_pair_currents(&contributions, &oriented_factor_current)?;
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!("oriented-realization-pair-current={}", pair_currents.len());
        }
        // The existing resident membrane context consumes the complete pair population. It joins
        // target subsections into `(port,factor)` complex currents and forms the positive norm only
        // afterward, with no intermediate semantic readback.
        let port_extent = 258_usize;
        let factor_extent = self.factor_population as usize;
        let mut target_witness_population = vec![0_usize; port_extent];
        for contribution in &contributions {
            let target_port = contribution.exterior_target_port as usize;
            if target_port == 0 || target_port >= port_extent {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            target_witness_population[target_port] = target_witness_population[target_port]
                .checked_add(1)
                .ok_or(SourceNeutralRelationalError::Extent)?;
        }
        let resident_terms = pair_currents
            .iter()
            .enumerate()
            .map(|(occurrence, pair)| {
                Ok(ResidentAddressedComplexJunctionTerm {
                    occurrence: u32::try_from(occurrence)
                        .map_err(|_| SourceNeutralRelationalError::Extent)?,
                    target_site: pair.target_site,
                    exterior_port: u32::from(pair.exterior_target_port),
                    factor: pair.factor,
                    current: pair.current.clone(),
                })
            })
            .collect::<Result<Vec<_>, SourceNeutralRelationalError>>()?;
        let resident_complex_junction = resident
            .conduct_addressed_complex_junction(&resident_terms)
            .map_err(|_| SourceNeutralRelationalError::Quotient)?;
        if resident_complex_junction.intermediate_semantic_egress_octets != 0
            || resident_complex_junction.invariant_transport_reuploaded
            || resident_complex_junction.cpu_semantic_replay_after_device
            || resident_complex_junction.groups.is_empty()
            || resident_complex_junction.positive_denominator.is_zero()
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        let active_port_factor_population = resident_complex_junction.groups.len();
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "oriented-realization-linear-port-factors={}",
                active_port_factor_population
            );
        }
        let mut target_current = BTreeMap::<u16, (SourceNeutralPositiveCurrent, usize)>::new();
        for group in &resident_complex_junction.groups {
            let target_port = group.exterior_port as usize;
            if target_port == 0
                || target_port >= port_extent
                || group.factor as usize >= factor_extent
                || group.occurrences.is_empty()
                || group.target_sections.is_empty()
            {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            if group.joined_current.is_zero() {
                if !group.positive_numerator.is_zero() {
                    return Err(SourceNeutralRelationalError::Quotient);
                }
                continue;
            }
            let joined_norm = Ratio::new(
                group.positive_numerator.clone(),
                resident_complex_junction.positive_denominator.clone(),
            );
            if joined_norm.is_zero() {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            let target_port = target_port as u16;
            let target = target_current.entry(target_port).or_insert_with(|| {
                (
                    Ratio::zero(),
                    target_witness_population[target_port as usize],
                )
            });
            target.0 += joined_norm;
        }
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!("oriented-realization-port-mass={}", target_current.len());
        }
        target_current.retain(|_, (current, witness_population)| {
            !current.is_zero() && *witness_population != 0
        });
        let raw_total_target_current = target_current
            .values()
            .fold(Ratio::zero(), |sum, (current, _)| sum + current);
        if target_current.is_empty() || raw_total_target_current.is_zero() {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        target_current
            .values_mut()
            .for_each(|(current, _)| *current /= &raw_total_target_current);
        let total_target_current = Ratio::one();

        let entering_phase = Ratio::new(
            entering_phase_numerator.clone(),
            entering_phase_denominator.clone(),
        );
        let phase_position = &entering_phase * &total_target_current;
        let mut interval_begin = Ratio::zero();
        let mut selected = None;
        for (target_port, (current, _)) in &target_current {
            let interval_end = &interval_begin + current;
            if phase_position >= interval_begin && phase_position < interval_end {
                selected = Some((*target_port, interval_begin.clone(), interval_end.clone()));
                break;
            }
            interval_begin = interval_end;
        }
        let (selected_target_port, selected_interval_begin, selected_interval_end) =
            selected.ok_or(SourceNeutralRelationalError::Quotient)?;

        // The complete port-potential family and its source current remain above as the exact
        // reconstruction fibre.  The exterior interaction enacts one orientation, so the live
        // world-line continues with that port-indexed target section.  Summing mutually exclusive
        // port branches would erase their orientation and manufacture the measured support
        // explosion; retaining only this enacted member without the family above would instead
        // erase counterfactual receiver consequence.
        let selected_mass = &selected_interval_end - &selected_interval_begin;
        if selected_mass.is_zero() {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        let mut selected_target_complex =
            BTreeMap::<(u32, u32, u8, u16), SourceNeutralPositiveCurrent>::new();
        for contribution in contributions
            .into_iter()
            .filter(|contribution| contribution.exterior_target_port == selected_target_port)
        {
            *selected_target_complex
                .entry((
                    contribution.target_carrier,
                    contribution.factor,
                    contribution.phase,
                    contribution.target_local_source_port,
                ))
                .or_default() += contribution.incidence_coefficient;
        }
        selected_target_complex.retain(|_, coefficient| !coefficient.is_zero());
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "oriented-realization-selected-target-complex={}",
                selected_target_complex.len()
            );
        }
        let returned_complex_site_current = selected_target_complex
            .into_iter()
            .map(
                |((carrier, factor, phase, local_source_port), incidence_coefficient)| {
                    let (site, _, _) = site_quotient.carrier_representative(carrier)?;
                    Ok(SourceNeutralExteriorRealizationComplexSiteCurrent {
                        carrier,
                        site,
                        factor,
                        phase,
                        local_source_port,
                        incidence_coefficient,
                    })
                },
            )
            .collect::<Result<Vec<_>, SourceNeutralRelationalError>>()?;
        if returned_complex_site_current.is_empty() {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        let returned_site_current = positive_site_shadow(&returned_complex_site_current)?;
        let mut returned_factor_map = BTreeMap::<u32, SourceNeutralPositiveCurrent>::new();
        for current in &returned_site_current {
            *returned_factor_map.entry(current.factor).or_default() += &current.current;
        }
        let returned_factor_current = returned_factor_map
            .into_iter()
            .map(
                |(factor, current)| SourceNeutralExteriorRealizationFactorCurrent {
                    factor,
                    current,
                },
            )
            .collect::<Vec<_>>();

        let returned_phase = (phase_position - &selected_interval_begin) / &selected_mass;
        let returned_phase_numerator = returned_phase.numer().clone();
        let returned_phase_denominator = returned_phase.denom().clone();
        let returned_realization_current_identity_sha256 = digest(&(
            "soma-life.source-neutral-exterior-returned-realization-current.v2",
            self.identity_sha256.as_str(),
            native_section_identity_sha256,
            native_current_passage_identity_sha256,
            source_port,
            selected_target_port,
            &returned_factor_current,
            &returned_site_current,
            &returned_complex_site_current,
            &returned_phase_numerator,
            &returned_phase_denominator,
        ));
        let target_current = target_current
            .into_iter()
            .map(
                |(target_port, (current, supporting_transition_population))| {
                    SourceNeutralExteriorRealizationTargetCurrent {
                        target_port,
                        current,
                        supporting_transition_population,
                    }
                },
            )
            .collect::<Vec<_>>();
        let mut passage = SourceNeutralExteriorRealizationPassage {
            schema: SOURCE_NEUTRAL_EXTERIOR_REALIZATION_PASSAGE_SCHEMA.to_owned(),
            morphology_identity_sha256: self.identity_sha256.clone(),
            native_section_identity_sha256: native_section_identity_sha256.to_owned(),
            native_current_passage_identity_sha256: native_current_passage_identity_sha256
                .to_owned(),
            source_port,
            factor_current,
            oriented_factor_current,
            native_oriented_faces,
            site_current,
            complex_site_current,
            pair_currents,
            resident_complex_junction,
            target_current,
            total_target_current,
            entering_realization_current_identity_sha256:
                entering_realization_current_identity_sha256.to_owned(),
            entering_phase_numerator,
            entering_phase_denominator,
            selected_target_port,
            selected_interval_begin,
            selected_interval_end,
            returned_factor_current,
            returned_site_current,
            returned_complex_site_current,
            returned_phase_numerator,
            returned_phase_denominator,
            returned_realization_current_identity_sha256,
            source_boundary_total: true,
            target_boundary_total: true,
            complete_reconstruction_fibre_retained: true,
            source_codec_consulted: false,
            source_surface_reachable: false,
            identity_sha256: String::new(),
        };
        passage.identity_sha256 = passage.rederived_identity();
        passage.validate()?;
        Ok(passage)
    }

    pub(crate) fn validate(
        &self,
        factor_population: usize,
    ) -> Result<(), SourceNeutralRelationalError> {
        if self.schema != SOURCE_NEUTRAL_EXTERIOR_REALIZATION_MORPHOLOGY_SCHEMA
            || !is_digest(&self.relational_identity_sha256)
            || self.face_population == 0
            || self.cell_population == 0
            || self.sites.is_empty()
            || factor_population == 0
            || self.factor_population as usize != factor_population
            || self.transitions.is_empty()
            || self.developmental_transition_population == 0
            || self.sites.windows(2).any(|pair| {
                (pair[0].face, pair[0].cell, pair[0].boundary_position)
                    >= (pair[1].face, pair[1].cell, pair[1].boundary_position)
            })
            || self.sites.iter().enumerate().any(|(at, site)| {
                site.face >= self.face_population
                    || site.cell >= self.cell_population
                    || site.boundary_position > 3
                    || site.incidence_population == 0
                    || site.successor_site.is_some_and(|successor| {
                        successor as usize >= self.sites.len() || successor as usize == at
                    })
            })
            || self.transitions.windows(2).any(|pair| {
                (pair[0].source, pair[0].face, pair[0].target)
                    >= (pair[1].source, pair[1].face, pair[1].target)
            })
            || self.transitions.iter().any(|transition| {
                transition.face >= self.face_population
                    || transition.source > 257
                    || transition.target > 257
                    || transition.source == 257
                    || transition.target == 0
                    || transition.occurrence_population == 0
            })
            || !self
                .transitions
                .iter()
                .any(|transition| transition.source == 0)
            || !self
                .transitions
                .iter()
                .any(|transition| transition.target == 257)
            || self.identity_sha256 != self.rederived_identity()
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        Ok(())
    }

    pub(crate) fn validate_relational(
        &self,
        relational: &SourceNeutralRelationalMorphology,
    ) -> Result<(), SourceNeutralRelationalError> {
        relational.validate()?;
        self.validate(relational.factor_population())?;
        if self.relational_identity_sha256 != relational.identity()
            || self.face_population as usize != relational.face_population()
            || self.cell_population as usize != relational.cell_population()
            || !realization_sites_match_relational(&self.sites, relational)?
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        Ok(())
    }

    pub(crate) fn rederived_identity(&self) -> String {
        digest(&(
            SOURCE_NEUTRAL_EXTERIOR_REALIZATION_MORPHOLOGY_SCHEMA,
            self.relational_identity_sha256.as_str(),
            self.face_population,
            self.cell_population,
            &self.sites,
            self.factor_population,
            &self.transitions,
            self.developmental_transition_population,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn phase_population_one() -> Vec<SourceNeutralPhasePopulation> {
        vec![SourceNeutralPhasePopulation {
            factor: 0,
            phase: 0,
            occurrence_population: 1,
        }]
    }

    fn bounded_transport_fixture() -> (
        SourceNeutralExteriorRealizationMorphology,
        SourceNeutralRelationalMorphology,
        SourceNeutralExteriorSiteHistoryQuotient,
    ) {
        let face = |address: &str| SourceNeutralRelationalFace {
            address: address.to_owned(),
            factor_support: vec![0],
            phase_population: phase_population_one(),
            cell_incidence: Vec::new(),
        };
        let relational = SourceNeutralRelationalMorphology {
            schema: String::new(),
            factor_population: 1,
            factor_adjacency: Vec::new(),
            faces: vec![face("face-0"), face("face-1")],
            cells: vec![SourceNeutralRelationalCell {
                address: "cell-0".to_owned(),
                oriented_boundary: vec![0, 1, 0],
                factor_support: vec![0],
                phase_population: phase_population_one(),
            }],
            obstructed_delivery_population: 0,
            identity_sha256: String::new(),
        };
        let morphology = SourceNeutralExteriorRealizationMorphology {
            schema: String::new(),
            relational_identity_sha256: String::new(),
            face_population: 2,
            cell_population: 1,
            sites: vec![
                SourceNeutralExteriorRealizationSite {
                    face: 0,
                    cell: 0,
                    boundary_position: 0,
                    incidence_population: 1,
                    successor_site: Some(1),
                },
                SourceNeutralExteriorRealizationSite {
                    face: 1,
                    cell: 0,
                    boundary_position: 1,
                    incidence_population: 1,
                    successor_site: None,
                },
            ],
            factor_population: 1,
            transitions: vec![
                SourceNeutralExteriorRealizationTransition {
                    face: 0,
                    source: 1,
                    target: 2,
                    occurrence_population: 1,
                },
                SourceNeutralExteriorRealizationTransition {
                    face: 0,
                    source: 1,
                    target: 3,
                    occurrence_population: 1,
                },
                SourceNeutralExteriorRealizationTransition {
                    face: 1,
                    source: 1,
                    target: 4,
                    occurrence_population: 1,
                },
            ],
            developmental_transition_population: 3,
            identity_sha256: String::new(),
        };
        let quotient = SourceNeutralExteriorSiteHistoryQuotient {
            site_to_class: vec![0, 1],
            representatives: vec![0, 1],
            fibres: vec![vec![0], vec![1]],
            carrier_addresses: BTreeMap::from([((0, 0, 0), 0), ((1, 0, 0), 1)]),
            carrier_representatives: vec![(0, 0, 0), (1, 0, 0)],
            carrier_fibres: vec![vec![(0, 0, 0)], vec![(1, 0, 0)]],
            identity_sha256: String::new(),
        };
        (morphology, relational, quotient)
    }

    #[test]
    fn ordinary_port_law_retains_diagonal_and_off_diagonal_pair_fibres() {
        let (morphology, relational, quotient) = bounded_transport_fixture();
        let source_currents = vec![
            SourceNeutralExteriorRealizationComplexSiteCurrent {
                carrier: 0,
                site: 0,
                factor: 0,
                phase: 0,
                local_source_port: 1,
                incidence_coefficient: Ratio::one(),
            },
            SourceNeutralExteriorRealizationComplexSiteCurrent {
                carrier: 1,
                site: 1,
                factor: 0,
                phase: 0,
                local_source_port: 1,
                incidence_coefficient: Ratio::one(),
            },
        ];
        let contributions = morphology
            .complex_site_transport_contributions(&relational, &quotient, &source_currents)
            .expect("the oriented ordinary port law returns");
        assert!(contributions.iter().any(|current| {
            current.source_carrier == 0
                && current.source_site == 0
                && current.target_carrier == 1
                && current.target_site == 1
        }));
        assert!(contributions.iter().any(|current| {
            current.source_carrier == 1
                && current.source_site == 1
                && current.target_carrier == 1
                && current.target_site == 1
        }));
        for source in [0_u32, 1] {
            let returned = contributions
                .iter()
                .filter(|current| current.source_carrier == source)
                .fold(Ratio::zero(), |sum, current| {
                    sum + &current.incidence_coefficient
                });
            assert_eq!(returned, Ratio::one());
        }

        let response = SourceNeutralAddressedResponsePairCurrent {
            response_face: 5,
            native_port: 7,
            native_generator: 11,
            source_section: 13,
            selected_slot: 17,
            target_section: 19,
            factor: 0,
            current: ExactComplexWaveCurrent::one(),
        };
        let oriented = vec![SourceNeutralExteriorRealizationOrientedFactorCurrent {
            factor: 0,
            current: ExactComplexWaveCurrent::one(),
            pair_currents: vec![response.clone()],
        }];
        let pairs =
            SourceNeutralExteriorRealizationMorphology::addressed_realization_pair_currents(
                &contributions,
                &oriented,
            )
            .expect("response and site endpoints compose");
        assert!(pairs.iter().all(|pair| pair.response == response));
        assert!(pairs
            .iter()
            .any(|pair| pair.source_site == 0 && pair.target_site == 1));
        assert!(pairs
            .iter()
            .any(|pair| pair.source_site == 1 && pair.target_site == 1));
    }
}
