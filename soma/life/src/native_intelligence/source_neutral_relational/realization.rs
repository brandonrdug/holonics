//! Exterior realization conduct owner implementations.

use super::*;

type RealizationFutureState = (u32, u16, u32, u8, u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RealizationFutureGrade {
    Dead(u32),
    Cycle,
    Closure(u32),
}

impl RealizationFutureGrade {
    fn rank(self) -> u8 {
        match self {
            Self::Dead(_) => 0,
            Self::Cycle => 1,
            Self::Closure(_) => 2,
        }
    }

    fn advanced(self) -> Result<Self, SourceNeutralRelationalError> {
        match self {
            Self::Dead(depth) => depth
                .checked_add(1)
                .map(Self::Dead)
                .ok_or(SourceNeutralRelationalError::Extent),
            Self::Cycle => Ok(Self::Cycle),
            Self::Closure(depth) => depth
                .checked_add(1)
                .map(Self::Closure)
                .ok_or(SourceNeutralRelationalError::Extent),
        }
    }

    fn preferred_over(self, other: Self) -> bool {
        self.rank() > other.rank()
            || self.rank() == other.rank()
                && match (self, other) {
                    (Self::Dead(left), Self::Dead(right))
                    | (Self::Closure(left), Self::Closure(right)) => left > right,
                    _ => false,
                }
    }
}

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

    fn state_source_transitions(
        &self,
        state: u32,
        source_port: u16,
    ) -> &[SourceNeutralExteriorRealizationTransition] {
        let source = self.source_transitions(source_port);
        let begin = source.partition_point(|transition| transition.state < state);
        let end = source.partition_point(|transition| transition.state <= state);
        &source[begin..end]
    }

    fn face_root_state(&self, face: u32) -> Result<u32, SourceNeutralRelationalError> {
        self.face_root_states
            .get(face as usize)
            .copied()
            .ok_or(SourceNeutralRelationalError::Quotient)
    }

    fn ingress_substring_closure_population(
        &self,
        ingress_ports: &[u16],
    ) -> Result<BTreeMap<u32, u64>, SourceNeutralRelationalError> {
        let Some(first) = ingress_ports.first().copied() else {
            return Ok(BTreeMap::new());
        };
        let mut candidates = self
            .transitions
            .iter()
            .filter(|transition| transition.target == first)
            .filter_map(|transition| {
                transition
                    .target_state
                    .map(|state| (transition.face, state))
            })
            .collect::<BTreeSet<_>>();
        let mut source = first;
        for target in ingress_ports.iter().copied().skip(1) {
            let mut next = BTreeSet::new();
            for (face, state) in candidates {
                for transition in self.state_source_transitions(state, source) {
                    if transition.face == face && transition.target == target {
                        if let Some(target_state) = transition.target_state {
                            next.insert((face, target_state));
                        }
                    }
                }
            }
            if next.is_empty() {
                return Ok(BTreeMap::new());
            }
            candidates = next;
            source = target;
        }
        let mut closures = BTreeMap::<u32, u64>::new();
        for (face, state) in candidates {
            for transition in self.state_source_transitions(state, source) {
                if transition.face == face && transition.target == 257 {
                    let population = closures.entry(face).or_default();
                    *population = population
                        .checked_add(transition.occurrence_population)
                        .ok_or(SourceNeutralRelationalError::Extent)?;
                }
            }
        }
        Ok(closures)
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

    fn realization_future_grade(
        &self,
        relational: &SourceNeutralRelationalMorphology,
        site_quotient: &SourceNeutralExteriorSiteHistoryQuotient,
        state: RealizationFutureState,
        memo: &mut BTreeMap<RealizationFutureState, RealizationFutureGrade>,
        visiting: &mut BTreeSet<RealizationFutureState>,
    ) -> Result<RealizationFutureGrade, SourceNeutralRelationalError> {
        if let Some(grade) = memo.get(&state).copied() {
            return Ok(grade);
        }
        if !visiting.insert(state) {
            return Ok(RealizationFutureGrade::Cycle);
        }
        let (carrier, local_source_port, factor, phase, realization_state) = state;
        let (site_class, _, _) = site_quotient.carrier_representative(carrier)?;
        let source_site = self.site(site_quotient.representative(site_class)?)?;
        let transitions = self.state_source_transitions(realization_state, local_source_port);
        let mut best = RealizationFutureGrade::Dead(0);
        for transition in transitions {
            let successor = match self.successor_transport_target(
                relational,
                site_quotient,
                source_site,
                factor,
                phase,
                transition.occurrence_population,
            ) {
                Ok(successor) => successor,
                Err(SourceNeutralRelationalError::Quotient) => continue,
                Err(error) => return Err(error),
            };
            let (target_carrier, _, _) = successor.unwrap_or((
                carrier,
                site_class,
                BigUint::from(transition.occurrence_population),
            ));
            let (exterior_target_port, target_local_source_port) =
                if transition.target == 257 && source_site.successor_site.is_some() {
                    (u16::from(b' ') + 1, 0)
                } else {
                    (transition.target, transition.target)
                };
            let target_realization_state = if transition.target == 257 {
                if let Some(successor_site) = source_site.successor_site {
                    let successor = self.site(successor_site)?;
                    Some(self.face_root_state(successor.face)?)
                } else {
                    None
                }
            } else {
                transition.target_state
            };
            let grade = if exterior_target_port == 257 {
                RealizationFutureGrade::Closure(1)
            } else {
                match self.realization_future_grade(
                    relational,
                    site_quotient,
                    (
                        target_carrier,
                        target_local_source_port,
                        factor,
                        phase,
                        target_realization_state.ok_or(SourceNeutralRelationalError::Quotient)?,
                    ),
                    memo,
                    visiting,
                ) {
                    Ok(grade) => grade.advanced()?,
                    Err(SourceNeutralRelationalError::Quotient) => RealizationFutureGrade::Dead(0),
                    Err(error) => return Err(error),
                }
            };
            if grade.preferred_over(best) {
                best = grade;
            }
        }
        visiting.remove(&state);
        memo.insert(state, best);
        Ok(best)
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
        ingress_ports: &[u16],
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
            ingress_ports,
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
        if let Err(error) = prior.validate() {
            if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
                eprintln!("oriented-realization-prior-validation={error}");
            }
            return Err(error);
        }
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
        ingress_ports: &[u16],
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
        let mut lifted = BTreeMap::<(u32, u32, u8, u16, u32), BigUint>::new();
        let mut projective_scale = BigUint::zero();
        let ingress_closures = if source_port == 0 && !ingress_ports.is_empty() {
            self.ingress_substring_closure_population(ingress_ports)?
        } else {
            BTreeMap::new()
        };
        let ingress_path_matched = !ingress_closures.is_empty();
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "oriented-realization-ingress-path matched={} faces={}",
                ingress_path_matched,
                ingress_closures.len(),
            );
        }
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
            let ingress_closure_population = ingress_closures.get(&site.face).copied();
            if source_port == 0
                && !ingress_ports.is_empty()
                && ingress_path_matched
                && ingress_closure_population.is_none()
            {
                continue;
            }
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
                let source_carrier = site_quotient.carrier(
                    site_class,
                    cell_population.factor,
                    cell_population.phase,
                )?;
                let (carrier, local_source_port, realization_state, incidence_scale) =
                    if let Some(closure_population) = ingress_closure_population {
                        let Some((carrier, target_site, oriented_weight)) = self
                            .successor_transport_target(
                                relational,
                                site_quotient,
                                site,
                                cell_population.factor,
                                cell_population.phase,
                                closure_population,
                            )?
                        else {
                            continue;
                        };
                        let successor = self.site(site_quotient.representative(target_site)?)?;
                        (
                            carrier,
                            0,
                            self.face_root_state(successor.face)?,
                            BigUint::from(cell_population.occurrence_population)
                                * BigUint::from(face_population)
                                * oriented_weight,
                        )
                    } else {
                        (
                            source_carrier,
                            source_port,
                            self.face_root_state(site.face)?,
                            BigUint::from(cell_population.occurrence_population)
                                * BigUint::from(face_population)
                                * BigUint::from(site.incidence_population),
                        )
                    };
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
                        local_source_port,
                        realization_state,
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
                .map(
                    |(
                        (carrier, factor, phase, local_source_port, realization_state),
                        numerator,
                    )| {
                        let (site, _, _) = site_quotient.carrier_representative(carrier)?;
                        Ok(SourceNeutralExteriorRealizationComplexSiteCurrent {
                            carrier,
                            site,
                            factor,
                            phase,
                            local_source_port,
                            realization_state: Some(realization_state),
                            incidence_coefficient: Ratio::from_integer(numerator),
                        })
                    },
                )
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
        (
            Vec<SourceNeutralExteriorRealizationTransportContribution>,
            Vec<SourceNeutralExteriorRealizationTransportObstruction>,
        ),
        SourceNeutralRelationalError,
    > {
        // The public entry deed validates the sealed morphology/relational pair once.  This
        // private contraction owns only the sparse addressed current and must not rescan the
        // complete rested atlas for every emitted occurrence.
        let mut contributions = Vec::new();
        let mut obstructions = Vec::new();
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
            let realization_state = current
                .realization_state
                .ok_or(SourceNeutralRelationalError::Quotient)?;
            let transitions =
                self.state_source_transitions(realization_state, current.local_source_port);
            if transitions.is_empty() {
                obstructions.push(SourceNeutralExteriorRealizationTransportObstruction {
                    source_carrier: current.carrier,
                    source_site: source_site_class,
                    source_local_port: current.local_source_port,
                    source_realization_state: realization_state,
                    factor: current.factor,
                    phase: current.phase,
                    incidence_coefficient: current.incidence_coefficient.clone(),
                });
                continue;
            }
            let mut row = Vec::<(u16, u32, u32, u16, Option<u32>, BigUint)>::new();
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
                let target_realization_state = if transition.target == 257 {
                    if let Some(successor_site) = source_site.successor_site {
                        let successor = self.site(successor_site)?;
                        Some(self.face_root_state(successor.face)?)
                    } else {
                        None
                    }
                } else {
                    transition.target_state
                };
                row.push((
                    exterior_target_port,
                    target_carrier,
                    target_site,
                    target_local_source_port,
                    target_realization_state,
                    oriented_weight,
                ));
            }
            let row_total = row
                .iter()
                .map(|(_, _, _, _, _, weight)| weight.clone())
                .sum::<BigUint>();
            if row.is_empty() || row_total.is_zero() {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            for (
                exterior_target_port,
                target_carrier,
                target_site,
                target_local_source_port,
                target_realization_state,
                oriented_weight,
            ) in row
            {
                let transported =
                    &current.incidence_coefficient * Ratio::new(oriented_weight, row_total.clone());
                if transported.is_zero() {
                    return Err(SourceNeutralRelationalError::Quotient);
                }
                site_quotient.carrier_representative(target_carrier)?;
                contributions.push(SourceNeutralExteriorRealizationTransportContribution {
                    exterior_target_port,
                    source_carrier: current.carrier,
                    source_site: source_site_class,
                    source_local_port: current.local_source_port,
                    source_realization_state: realization_state,
                    target_carrier,
                    target_site,
                    target_local_source_port,
                    target_realization_state,
                    factor: current.factor,
                    phase: current.phase,
                    incidence_coefficient: transported,
                });
            }
        }
        if contributions.is_empty() {
            Err(SourceNeutralRelationalError::Quotient)
        } else {
            Ok((contributions, obstructions))
        }
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
                    pair[0].realization_state,
                ) >= (
                    pair[1].carrier,
                    pair[1].factor,
                    pair[1].phase,
                    pair[1].local_source_port,
                    pair[1].realization_state,
                )
            })
            || site_current.iter().any(|current| {
                current.carrier as usize >= site_quotient.quotient_population()
                    || current.factor >= self.factor_population
                    || current.phase > 2
                    || current.local_source_port >= 257
                    || current
                        .realization_state
                        .is_none_or(|state| state >= self.realization_state_population)
                    || current.current.is_zero()
            })
            || complex_site_current.is_empty()
            || complex_site_current.windows(2).any(|pair| {
                (
                    pair[0].carrier,
                    pair[0].factor,
                    pair[0].phase,
                    pair[0].local_source_port,
                    pair[0].realization_state,
                ) >= (
                    pair[1].carrier,
                    pair[1].factor,
                    pair[1].phase,
                    pair[1].local_source_port,
                    pair[1].realization_state,
                )
            })
            || complex_site_current.iter().any(|current| {
                current.carrier as usize >= site_quotient.quotient_population()
                    || current.factor >= self.factor_population
                    || current.phase > 2
                    || current.local_source_port >= 257
                    || current
                        .realization_state
                        .is_none_or(|state| state >= self.realization_state_population)
                    || current.incidence_coefficient.is_zero()
            })
            || entering_phase_denominator.is_zero()
            || entering_phase_numerator >= entering_phase_denominator
        {
            if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
                eprintln!("oriented-realization-shape-obstruction source-port={source_port}");
            }
            return Err(SourceNeutralRelationalError::Quotient);
        }
        reduce_fraction(
            &mut entering_phase_numerator,
            &mut entering_phase_denominator,
        )?;

        let (contributions, transport_obstructions) = self
            .complex_site_transport_contributions(relational, site_quotient, &complex_site_current)
            .map_err(|error| {
                if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
                    eprintln!(
                        "oriented-realization-transport-obstruction source-port={source_port}"
                    );
                }
                error
            })?;
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "oriented-realization-transport-contributions={}",
                contributions.len()
            );
            eprintln!(
                "oriented-realization-transport-obstructions={}",
                transport_obstructions.len()
            );
        }
        let mut future_memo = BTreeMap::<RealizationFutureState, RealizationFutureGrade>::new();
        let mut future_visiting = BTreeSet::<RealizationFutureState>::new();
        let mut target_future_grades = BTreeMap::<u16, RealizationFutureGrade>::new();
        for contribution in &contributions {
            let grade = if contribution.exterior_target_port == 257 {
                RealizationFutureGrade::Closure(0)
            } else {
                self.realization_future_grade(
                    relational,
                    site_quotient,
                    (
                        contribution.target_carrier,
                        contribution.target_local_source_port,
                        contribution.factor,
                        contribution.phase,
                        contribution
                            .target_realization_state
                            .ok_or(SourceNeutralRelationalError::Quotient)?,
                    ),
                    &mut future_memo,
                    &mut future_visiting,
                )?
            };
            target_future_grades
                .entry(contribution.exterior_target_port)
                .and_modify(|held| {
                    if grade.preferred_over(*held) {
                        *held = grade;
                    }
                })
                .or_insert(grade);
        }
        let best_rank = target_future_grades
            .values()
            .map(|grade| grade.rank())
            .max()
            .ok_or(SourceNeutralRelationalError::Quotient)?;
        let best_dead_depth = (best_rank == 0)
            .then(|| {
                target_future_grades
                    .values()
                    .filter_map(|grade| match grade {
                        RealizationFutureGrade::Dead(depth) => Some(*depth),
                        _ => None,
                    })
                    .max()
            })
            .flatten();
        let continuing_target_ports = target_future_grades
            .iter()
            .filter_map(|(port, grade)| {
                (grade.rank() == best_rank
                    && (best_rank != 0
                        || matches!(grade, RealizationFutureGrade::Dead(depth) if Some(*depth) == best_dead_depth)))
                .then_some(*port)
            })
            .collect::<BTreeSet<_>>();
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
        let oriented_by_factor = oriented_factor_current
            .iter()
            .map(|factor| (factor.factor, &factor.current))
            .collect::<BTreeMap<_, _>>();
        let resident_terms = contributions
            .iter()
            .enumerate()
            .map(|(occurrence, contribution)| {
                let coefficient = Ratio::new(
                    BigInt::from(contribution.incidence_coefficient.numer().clone()),
                    BigInt::from(contribution.incidence_coefficient.denom().clone()),
                );
                let current = oriented_by_factor
                    .get(&contribution.factor)
                    .ok_or(SourceNeutralRelationalError::Quotient)?
                    .scaled(&coefficient);
                if current.is_zero() {
                    return Err(SourceNeutralRelationalError::Quotient);
                }
                Ok(ResidentAddressedComplexJunctionTerm {
                    occurrence: u32::try_from(occurrence)
                        .map_err(|_| SourceNeutralRelationalError::Extent)?,
                    target_site: contribution.target_site,
                    exterior_port: u32::from(contribution.exterior_target_port),
                    factor: contribution.factor,
                    current,
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

        let mut continuing_target_current = target_current
            .iter()
            .filter(|(port, _)| continuing_target_ports.contains(port))
            .map(|(port, current)| (*port, current.clone()))
            .collect::<BTreeMap<_, _>>();
        let continuing_total = continuing_target_current
            .values()
            .fold(Ratio::zero(), |sum, (current, _)| sum + current);
        if continuing_target_current.is_empty() || continuing_total.is_zero() {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        continuing_target_current
            .values_mut()
            .for_each(|(current, _)| *current /= &continuing_total);

        let entering_phase = Ratio::new(
            entering_phase_numerator.clone(),
            entering_phase_denominator.clone(),
        );
        let phase_position = &entering_phase * &total_target_current;
        let mut interval_begin = Ratio::zero();
        let mut selected = None;
        for (target_port, (current, _)) in &continuing_target_current {
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
            BTreeMap::<(u32, u32, u8, u16, Option<u32>), SourceNeutralPositiveCurrent>::new();
        for contribution in contributions
            .iter()
            .filter(|contribution| contribution.exterior_target_port == selected_target_port)
        {
            *selected_target_complex
                .entry((
                    contribution.target_carrier,
                    contribution.factor,
                    contribution.phase,
                    contribution.target_local_source_port,
                    contribution.target_realization_state,
                ))
                .or_default() += &contribution.incidence_coefficient;
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
                |(
                    (carrier, factor, phase, local_source_port, realization_state),
                    incidence_coefficient,
                )| {
                    let (site, _, _) = site_quotient.carrier_representative(carrier)?;
                    Ok(SourceNeutralExteriorRealizationComplexSiteCurrent {
                        carrier,
                        site,
                        factor,
                        phase,
                        local_source_port,
                        realization_state,
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
        let continuing_target_current = continuing_target_current
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
            transport_contributions: contributions,
            transport_obstructions,
            resident_complex_junction,
            target_current,
            total_target_current,
            continuing_target_current,
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
            || self.face_root_states.len() != self.face_population as usize
            || self.realization_state_population < self.face_population
            || self
                .face_root_states
                .iter()
                .enumerate()
                .any(|(face, state)| {
                    *state as usize != face || *state >= self.realization_state_population
                })
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
                (pair[0].source, pair[0].state, pair[0].face, pair[0].target)
                    >= (pair[1].source, pair[1].state, pair[1].face, pair[1].target)
            })
            || self.transitions.iter().any(|transition| {
                transition.face >= self.face_population
                    || transition.state >= self.realization_state_population
                    || transition.source > 257
                    || transition.target > 257
                    || transition.source == 257
                    || transition.target == 0
                    || (transition.target == 257) != transition.target_state.is_none()
                    || transition
                        .target_state
                        .is_some_and(|state| state >= self.realization_state_population)
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
            &self.face_root_states,
            self.realization_state_population,
            &self.transitions,
            self.developmental_transition_population,
        ))
    }
}

#[cfg(test)]
#[path = "realization_tests.rs"]
mod tests;
