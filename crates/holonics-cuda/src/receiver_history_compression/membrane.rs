use super::*;
/// A pivot-free executable receiver-history quotient.  The frame may retain linearly dependent
/// receiver rays, but it is closed under every admitted generator and therefore transports by
/// exact addressed integral factors.  Rational span reduction remains a colder optional
/// condensation of this already-lawful carrier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservableIntegralFormFrame {
    pub schema: String,
    pub factor_population: u32,
    pub forms: Vec<SparseIntegralBilinearForm>,
    pub present_receiver_factors: Vec<IntegralFormFrameFactor>,
    /// Generator-major rows; one factor for every frame coordinate.
    pub descended_generator_factors: Vec<Vec<IntegralFormFrameFactor>>,
}

impl ObservableIntegralFormFrame {
    pub fn found(
        present_forms: Vec<SparseIntegralBilinearForm>,
        generators: Vec<Vec<u32>>,
    ) -> Result<Self, ObservableMomentCompressionError> {
        let factor_population = present_forms
            .first()
            .map(|form| form.factor_population)
            .unwrap_or(0);
        if factor_population == 0
            || present_forms.is_empty()
            || generators.is_empty()
            || present_forms
                .iter()
                .any(|form| form.factor_population != factor_population)
            || generators.iter().any(|generator| {
                generator.len() != factor_population as usize
                    || generator.iter().any(|target| *target >= factor_population)
            })
        {
            return Err(ObservableMomentCompressionError::Shape);
        }

        let mut forms = Vec::<SparseIntegralBilinearForm>::new();
        let mut addresses = BTreeMap::<SparseIntegralBilinearForm, u32>::new();
        let intern = |candidate: SparseIntegralBilinearForm,
                      forms: &mut Vec<SparseIntegralBilinearForm>,
                      addresses: &mut BTreeMap<SparseIntegralBilinearForm, u32>|
         -> Result<IntegralFormFrameFactor, ObservableMomentCompressionError> {
            if candidate.is_zero() {
                return Ok(IntegralFormFrameFactor {
                    coordinate: None,
                    scale: BigInt::ZERO,
                });
            }
            let (scale, primitive) = candidate.primitive()?;
            let coordinate = if let Some(coordinate) = addresses.get(&primitive).copied() {
                coordinate
            } else {
                let coordinate = u32::try_from(forms.len())
                    .map_err(|_| ObservableMomentCompressionError::Shape)?;
                addresses.insert(primitive.clone(), coordinate);
                forms.push(primitive);
                coordinate
            };
            Ok(IntegralFormFrameFactor {
                coordinate: Some(coordinate),
                scale,
            })
        };
        let mut present_receiver_factors = Vec::with_capacity(present_forms.len());
        for form in present_forms {
            present_receiver_factors.push(intern(form, &mut forms, &mut addresses)?);
        }
        if forms.is_empty() {
            return Err(ObservableMomentCompressionError::Shape);
        }

        let mut descended_generator_factors = vec![Vec::new(); generators.len()];
        let mut cursor = 0;
        while cursor < forms.len() {
            let form = forms[cursor].clone();
            for (generator_at, generator) in generators.iter().enumerate() {
                let pulled = form.pullback_by_targets(generator)?;
                let factor = intern(pulled, &mut forms, &mut addresses)?;
                descended_generator_factors[generator_at].push(factor);
            }
            cursor += 1;
        }
        if descended_generator_factors
            .iter()
            .any(|action| action.len() != forms.len())
        {
            return Err(ObservableMomentCompressionError::Factorization);
        }
        Ok(Self {
            schema: "holonic-engine.observable-integral-form-frame.v1".to_owned(),
            factor_population,
            forms,
            present_receiver_factors,
            descended_generator_factors,
        })
    }

    pub fn quotient_rank_one_family(
        &self,
        family: &[(BigInt, Vec<BigInt>)],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        if family.is_empty() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        self.forms
            .iter()
            .map(|form| {
                family
                    .iter()
                    .try_fold(BigInt::ZERO, |sum, (weight, current)| {
                        Ok(sum + weight * form.contract_rank_one(current)?)
                    })
            })
            .collect()
    }

    pub fn present_receivers(
        &self,
        coordinates: &[BigInt],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        self.apply_factors(&self.present_receiver_factors, coordinates)
    }

    pub fn transport(
        &self,
        generator: usize,
        coordinates: &[BigInt],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        self.apply_factors(
            self.descended_generator_factors
                .get(generator)
                .ok_or(ObservableMomentCompressionError::Address)?,
            coordinates,
        )
    }

    fn apply_factors(
        &self,
        factors: &[IntegralFormFrameFactor],
        coordinates: &[BigInt],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        if coordinates.len() != self.forms.len() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        factors
            .iter()
            .map(|factor| match factor.coordinate {
                None if factor.scale.is_zero() => Ok(BigInt::ZERO),
                Some(coordinate) => coordinates
                    .get(coordinate as usize)
                    .map(|value| &factor.scale * value)
                    .ok_or(ObservableMomentCompressionError::Address),
                None => Err(ObservableMomentCompressionError::Factorization),
            })
            .collect()
    }
}

/// One exact transition restriction factored through a primitive current ray. This belongs to the
/// direct ambient-form equality witness and is excluded from production construction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntegralRestrictionFrameFactor {
    pub restriction_class: u32,
    pub quadratic_scale: BigUint,
}

/// The production membrane receiver/history image.  Every present restriction face is retained
/// as a finite sum of functional pairs and every generator pullback stays in that representation;
/// no factor-square matrix is ever founded.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MembraneFactoredIntegralReceiverHistory {
    pub schema: String,
    pub frame: FactoredRationalReceiverHistoryFrame,
    pub primitive_restrictions: Vec<Vec<(u32, BigUint)>>,
    pub transition_restriction_factors: Vec<IntegralRestrictionFrameFactor>,
    pub family_population: u32,
    pub receiver_population: u32,
    pub generator_population: u32,
    /// Native total generator incidence retained for direct reconstruction and resident mounting.
    pub generator_targets: Vec<Vec<u32>>,
    /// Order inside one restriction is `(reflected families, action families, receiver overlaps,
    /// receiver norms)` and is shared by every transition factor below.
    pub present_forms_per_restriction: u32,
}

#[allow(clippy::too_many_arguments)]
fn membrane_factored_present_terms(
    restriction: &[(u32, BigUint)],
    factor_capacity: &[u64],
    family_orientation: &[i8],
    factor_receiver_classes: &[u32],
    generators: &[Vec<u32>],
    factors: usize,
    families: usize,
    receivers: usize,
) -> Result<Vec<Vec<FactoredIntegralReceiverTerm>>, ObservableMomentCompressionError> {
    let factor_population = factors as u32;
    let functional =
        |entries: Vec<(u32, BigInt)>| SparseIntegralFunctional::new(factor_population, entries);
    let singleton =
        |factor: u32, coefficient: &BigInt| functional(vec![(factor, coefficient.clone())]);
    let term = |coefficient: BigInt,
                left: SparseIntegralFunctional,
                right: SparseIntegralFunctional| FactoredIntegralReceiverTerm {
        coefficient,
        left,
        right,
    };
    let restricted = restriction
        .iter()
        .map(|(factor, coefficient)| (*factor, BigInt::from(coefficient.clone())))
        .collect::<BTreeMap<_, _>>();
    let mut returned = Vec::with_capacity(families.saturating_mul(2) + receivers.saturating_mul(2));
    for family in 0..families {
        let mut terms = Vec::new();
        for (factor, incidence) in &restricted {
            let orientation = family_orientation[family * factors + *factor as usize];
            if orientation == 0 {
                continue;
            }
            let reading = singleton(*factor, incidence)?;
            terms.push(term(
                BigInt::from(factor_capacity[*factor as usize])
                    * BigInt::from(orientation)
                    * BigInt::from(generators.len()),
                reading.clone(),
                reading,
            ));
        }
        returned.push(terms);
    }
    for family in 0..families {
        let mut terms = Vec::new();
        for (source, source_incidence) in &restricted {
            let source_orientation = family_orientation[family * factors + *source as usize];
            if source_orientation != 0 {
                let reading = singleton(*source, source_incidence)?;
                terms.push(term(
                    -BigInt::from(factor_capacity[*source as usize])
                        * BigInt::from(source_orientation)
                        * BigInt::from(generators.len()),
                    reading.clone(),
                    reading,
                ));
            }
            for generator in generators {
                let target = generator[*source as usize];
                let Some(target_incidence) = restricted.get(&target) else {
                    continue;
                };
                let target_orientation = family_orientation[family * factors + target as usize];
                if target_orientation == 0 {
                    continue;
                }
                terms.push(term(
                    BigInt::from(factor_capacity[target as usize])
                        * BigInt::from(target_orientation),
                    singleton(*source, source_incidence)?,
                    singleton(target, target_incidence)?,
                ));
            }
        }
        returned.push(terms);
    }
    for receiver in 0..receivers {
        let mut overlap_terms = Vec::new();
        let mut norm_terms = Vec::new();
        let mut source_entries = BTreeMap::<u32, Vec<(u32, BigInt)>>::new();
        for (factor, coefficient) in &restricted {
            let class = factor_receiver_classes[*factor as usize * receivers + receiver];
            source_entries
                .entry(class)
                .or_default()
                .push((*factor, coefficient.clone()));
        }
        let sources = source_entries
            .into_iter()
            .map(|(class, entries)| Ok((class, functional(entries)?)))
            .collect::<Result<BTreeMap<_, _>, ObservableMomentCompressionError>>()?;
        for generator in generators {
            let mut target_entries = BTreeMap::<u32, Vec<(u32, BigInt)>>::new();
            for (factor, coefficient) in &restricted {
                let target = generator[*factor as usize];
                let class = factor_receiver_classes[target as usize * receivers + receiver];
                target_entries
                    .entry(class)
                    .or_default()
                    .push((*factor, coefficient.clone()));
            }
            let targets = target_entries
                .into_iter()
                .map(|(class, entries)| Ok((class, functional(entries)?)))
                .collect::<Result<BTreeMap<_, _>, ObservableMomentCompressionError>>()?;
            for (class, source) in &sources {
                let target = targets
                    .get(class)
                    .cloned()
                    .unwrap_or(SparseIntegralFunctional {
                        factor_population,
                        entries: Vec::new(),
                    });
                overlap_terms.push(term(BigInt::from(1), source.clone(), target));
                overlap_terms.push(term(BigInt::from(-1), source.clone(), source.clone()));
            }
            let classes = sources
                .keys()
                .chain(targets.keys())
                .copied()
                .collect::<BTreeSet<_>>();
            for class in classes {
                let source = sources
                    .get(&class)
                    .cloned()
                    .unwrap_or(SparseIntegralFunctional {
                        factor_population,
                        entries: Vec::new(),
                    });
                let target = targets
                    .get(&class)
                    .cloned()
                    .unwrap_or(SparseIntegralFunctional {
                        factor_population,
                        entries: Vec::new(),
                    });
                let mut difference = target
                    .entries
                    .iter()
                    .map(|entry| (entry.factor, entry.coefficient.clone()))
                    .collect::<BTreeMap<_, _>>();
                for entry in &source.entries {
                    *difference.entry(entry.factor).or_default() -= &entry.coefficient;
                }
                difference.retain(|_, coefficient| !coefficient.is_zero());
                let difference = functional(difference.into_iter().collect())?;
                norm_terms.push(term(BigInt::from(1), difference.clone(), difference));
            }
        }
        returned.push(overlap_terms);
        returned.push(norm_terms);
    }
    Ok(returned)
}

/// Found the complete present membrane receiver family for one already-addressed restriction
/// while preserving every receiver as its ordered functional-pair occurrences.  Restriction and
/// receiver-class incidence already address these terms, so this ingress does not replay the
/// primitive-ray/hash quotient before conduct.  It does not close a backward receiver atlas and
/// does not materialize an ambient factor-square form; it is the dual readout consumed by the
/// factored moment operation complex.
#[allow(clippy::too_many_arguments)]
pub fn membrane_factored_present_receiver_forms(
    restriction: &[(u32, BigUint)],
    factor_capacity: &[u64],
    family_orientation: &[i8],
    factor_receiver_classes: &[u32],
    receiver_class_counts: &[u32],
    generators: &[Vec<u32>],
) -> Result<Vec<FactoredIntegralReceiverForm>, ObservableMomentCompressionError> {
    let factors = factor_capacity.len();
    let families = if factors == 0 {
        0
    } else {
        family_orientation.len() / factors
    };
    let receivers = receiver_class_counts.len();
    if factors == 0
        || families == 0
        || receivers == 0
        || restriction.is_empty()
        || restriction.windows(2).any(|pair| pair[0].0 >= pair[1].0)
        || restriction
            .iter()
            .any(|(factor, coefficient)| *factor as usize >= factors || coefficient.is_zero())
        || generators.is_empty()
        || family_orientation.len() != families.saturating_mul(factors)
        || factor_receiver_classes.len() != factors.saturating_mul(receivers)
        || factor_capacity.iter().any(|capacity| *capacity == 0)
        || family_orientation
            .iter()
            .any(|orientation| !matches!(*orientation, -1 | 0 | 1))
        || factor_receiver_classes
            .chunks_exact(receivers)
            .any(|classes| {
                classes
                    .iter()
                    .zip(receiver_class_counts)
                    .any(|(class, count)| *count == 0 || *class >= *count)
            })
        || generators.iter().any(|generator| {
            generator.len() != factors || generator.iter().any(|target| *target as usize >= factors)
        })
    {
        return Err(ObservableMomentCompressionError::Shape);
    }
    membrane_factored_present_terms(
        restriction,
        factor_capacity,
        family_orientation,
        factor_receiver_classes,
        generators,
        factors,
        families,
        receivers,
    )?
    .into_iter()
    .map(|terms| FactoredIntegralReceiverForm::from_addressed_terms(factors as u32, terms))
    .collect()
}

struct AddressedFunctionalPool {
    factor_population: u32,
    functionals: Vec<SparseIntegralFunctional>,
    singleton_addresses: Vec<Option<u32>>,
}

impl AddressedFunctionalPool {
    fn new(factor_population: u32) -> Result<Self, ObservableMomentCompressionError> {
        let empty = SparseIntegralFunctional::new(factor_population, Vec::new())?;
        Ok(Self {
            factor_population,
            functionals: vec![empty],
            singleton_addresses: vec![None; factor_population as usize],
        })
    }

    fn push(
        &mut self,
        entries: Vec<(u32, BigInt)>,
    ) -> Result<u32, ObservableMomentCompressionError> {
        let address = u32::try_from(self.functionals.len())
            .map_err(|_| ObservableMomentCompressionError::Shape)?;
        self.functionals.push(SparseIntegralFunctional::new(
            self.factor_population,
            entries,
        )?);
        Ok(address)
    }

    fn singleton(
        &mut self,
        factor: u32,
        coefficient: &BigInt,
    ) -> Result<u32, ObservableMomentCompressionError> {
        let slot = self
            .singleton_addresses
            .get(factor as usize)
            .copied()
            .ok_or(ObservableMomentCompressionError::Address)?;
        if let Some(address) = slot {
            return Ok(address);
        }
        let address = self.push(vec![(factor, coefficient.clone())])?;
        self.singleton_addresses[factor as usize] = Some(address);
        Ok(address)
    }

    fn difference(
        &mut self,
        target: u32,
        source: u32,
    ) -> Result<u32, ObservableMomentCompressionError> {
        let mut entries = self
            .functionals
            .get(target as usize)
            .ok_or(ObservableMomentCompressionError::Address)?
            .entries
            .iter()
            .map(|entry| (entry.factor, entry.coefficient.clone()))
            .collect::<BTreeMap<_, _>>();
        for entry in &self
            .functionals
            .get(source as usize)
            .ok_or(ObservableMomentCompressionError::Address)?
            .entries
        {
            *entries.entry(entry.factor).or_default() -= &entry.coefficient;
        }
        entries.retain(|_, coefficient| !coefficient.is_zero());
        self.push(entries.into_iter().collect())
    }
}

/// Found the same complete present receiver family as
/// [`membrane_factored_present_receiver_forms`], but retain shared functionals once and address
/// every term occurrence into that pool.  This is the production-shaped reference for the
/// resident operation complex; receiver order remains `(reflected families, action families,
/// receiver overlaps, receiver norms)`.
#[allow(clippy::too_many_arguments)]
pub fn membrane_addressed_factored_receiver_complex(
    restriction: &[(u32, BigUint)],
    factor_capacity: &[u64],
    family_orientation: &[i8],
    factor_receiver_classes: &[u32],
    receiver_class_counts: &[u32],
    generators: &[Vec<u32>],
) -> Result<AddressedFactoredIntegralReceiverComplex, ObservableMomentCompressionError> {
    let factors = factor_capacity.len();
    let families = if factors == 0 {
        0
    } else {
        family_orientation.len() / factors
    };
    let receivers = receiver_class_counts.len();
    if factors == 0
        || families == 0
        || receivers == 0
        || factors > u32::MAX as usize
        || families > u32::MAX as usize
        || receivers > u32::MAX as usize
        || generators.is_empty()
        || generators.len() > u32::MAX as usize
        || restriction.is_empty()
        || restriction.windows(2).any(|pair| pair[0].0 >= pair[1].0)
        || restriction
            .iter()
            .any(|(factor, coefficient)| *factor as usize >= factors || coefficient.is_zero())
        || family_orientation.len() != families.saturating_mul(factors)
        || factor_receiver_classes.len() != factors.saturating_mul(receivers)
        || factor_capacity.iter().any(|capacity| *capacity == 0)
        || family_orientation
            .iter()
            .any(|orientation| !matches!(*orientation, -1 | 0 | 1))
        || factor_receiver_classes
            .chunks_exact(receivers)
            .any(|classes| {
                classes
                    .iter()
                    .zip(receiver_class_counts)
                    .any(|(class, count)| *count == 0 || *class >= *count)
            })
        || generators.iter().any(|generator| {
            generator.len() != factors || generator.iter().any(|target| *target as usize >= factors)
        })
    {
        return Err(ObservableMomentCompressionError::Shape);
    }

    let factor_population = factors as u32;
    let restricted = restriction
        .iter()
        .map(|(factor, coefficient)| (*factor, BigInt::from(coefficient.clone())))
        .collect::<BTreeMap<_, _>>();
    let mut pool = AddressedFunctionalPool::new(factor_population)?;
    let mut returned = Vec::with_capacity(families.saturating_mul(2) + receivers.saturating_mul(2));
    let term = |coefficient: BigInt, left_functional: u32, right_functional: u32| {
        AddressedFactoredIntegralReceiverTerm {
            coefficient,
            left_functional,
            right_functional,
        }
    };

    for family in 0..families {
        let mut terms = Vec::new();
        for (factor, incidence) in &restricted {
            let orientation = family_orientation[family * factors + *factor as usize];
            if orientation == 0 {
                continue;
            }
            let reading = pool.singleton(*factor, incidence)?;
            terms.push(term(
                BigInt::from(factor_capacity[*factor as usize])
                    * BigInt::from(orientation)
                    * BigInt::from(generators.len()),
                reading,
                reading,
            ));
        }
        returned.push(AddressedFactoredIntegralReceiver { terms });
    }
    for family in 0..families {
        let mut terms = Vec::new();
        for (source, source_incidence) in &restricted {
            let source_orientation = family_orientation[family * factors + *source as usize];
            let source_reading = pool.singleton(*source, source_incidence)?;
            if source_orientation != 0 {
                terms.push(term(
                    -BigInt::from(factor_capacity[*source as usize])
                        * BigInt::from(source_orientation)
                        * BigInt::from(generators.len()),
                    source_reading,
                    source_reading,
                ));
            }
            for generator in generators {
                let target = generator[*source as usize];
                let Some(target_incidence) = restricted.get(&target) else {
                    continue;
                };
                let target_orientation = family_orientation[family * factors + target as usize];
                if target_orientation == 0 {
                    continue;
                }
                let target_reading = pool.singleton(target, target_incidence)?;
                terms.push(term(
                    BigInt::from(factor_capacity[target as usize])
                        * BigInt::from(target_orientation),
                    source_reading,
                    target_reading,
                ));
            }
        }
        returned.push(AddressedFactoredIntegralReceiver { terms });
    }
    for receiver in 0..receivers {
        let mut source_entries = BTreeMap::<u32, Vec<(u32, BigInt)>>::new();
        for (factor, coefficient) in &restricted {
            let class = factor_receiver_classes[*factor as usize * receivers + receiver];
            source_entries
                .entry(class)
                .or_default()
                .push((*factor, coefficient.clone()));
        }
        let mut sources = BTreeMap::<u32, u32>::new();
        for (class, entries) in source_entries {
            sources.insert(class, pool.push(entries)?);
        }
        let mut overlap_terms = Vec::new();
        let mut norm_terms = Vec::new();
        for (generator_at, generator) in generators.iter().enumerate() {
            let mut target_entries = BTreeMap::<u32, Vec<(u32, BigInt)>>::new();
            for (factor, coefficient) in &restricted {
                let target = generator[*factor as usize];
                let class = factor_receiver_classes[target as usize * receivers + receiver];
                target_entries
                    .entry(class)
                    .or_default()
                    .push((*factor, coefficient.clone()));
            }
            let mut targets = BTreeMap::<u32, u32>::new();
            for (class, entries) in target_entries {
                targets.insert(class, pool.push(entries)?);
            }
            for (class, source) in &sources {
                let target = targets.get(class).copied().unwrap_or(0);
                overlap_terms.push(term(BigInt::ONE, *source, target));
                overlap_terms.push(term(-BigInt::ONE, *source, *source));
            }
            let classes = sources
                .keys()
                .chain(targets.keys())
                .copied()
                .collect::<BTreeSet<_>>();
            for class in classes {
                let source = sources.get(&class).copied().unwrap_or(0);
                let target = targets.get(&class).copied().unwrap_or(0);
                let difference = pool.difference(target, source)?;
                norm_terms.push(term(BigInt::ONE, difference, difference));
            }
            let _ = generator_at;
        }
        returned.push(AddressedFactoredIntegralReceiver {
            terms: overlap_terms,
        });
        returned.push(AddressedFactoredIntegralReceiver { terms: norm_terms });
    }

    Ok(AddressedFactoredIntegralReceiverComplex {
        schema: "holonic-engine.addressed-factored-integral-receiver-complex.v1".to_owned(),
        factor_population,
        family_population: families as u32,
        receiver_population: receivers as u32,
        generator_population: generators.len() as u32,
        functionals: pool.functionals,
        receivers: returned,
        reconstruction_fibre: restriction.to_vec(),
    })
}

/// Found the one-dimensional projective current receiver used after a complete HNN state step.
/// The sparse restriction itself is one exact functional `r`; every standing receiver-coordinate
/// slot receives the same diagonal pullback `r ⊗ r`.  This is a faithful diagonal embedding of
/// one current norm into the already-mounted receiver product, so it adds no distinction and its
/// projective normalization is unchanged.  The complete pre-aggregation local-current family
/// remains reconstruction testimony outside this observer.
#[allow(clippy::too_many_arguments)]
pub fn membrane_diagonal_projective_receiver_complex(
    restriction: &[(u32, BigUint)],
    factor_population: usize,
    family_population: usize,
    receiver_population: usize,
    generator_population: usize,
) -> Result<AddressedFactoredIntegralReceiverComplex, ObservableMomentCompressionError> {
    if factor_population == 0
        || family_population == 0
        || receiver_population == 0
        || generator_population == 0
        || factor_population > u32::MAX as usize
        || family_population > u32::MAX as usize
        || receiver_population > u32::MAX as usize
        || generator_population > u32::MAX as usize
        || restriction.is_empty()
        || restriction.windows(2).any(|pair| pair[0].0 >= pair[1].0)
        || restriction.iter().any(|(factor, coefficient)| {
            *factor as usize >= factor_population || coefficient.is_zero()
        })
    {
        return Err(ObservableMomentCompressionError::Shape);
    }
    let functional = SparseIntegralFunctional::new(
        factor_population as u32,
        restriction
            .iter()
            .map(|(factor, coefficient)| (*factor, BigInt::from(coefficient.clone())))
            .collect::<Vec<_>>(),
    )?;
    let coordinate_population = family_population
        .checked_mul(2)
        .and_then(|held| held.checked_add(receiver_population.checked_mul(2)?))
        .ok_or(ObservableMomentCompressionError::Extent)?;
    let diagonal = AddressedFactoredIntegralReceiverTerm {
        coefficient: BigInt::ONE,
        left_functional: 0,
        right_functional: 0,
    };
    Ok(AddressedFactoredIntegralReceiverComplex {
        schema: "holonic-engine.addressed-factored-integral-receiver-complex.v1".to_owned(),
        factor_population: factor_population as u32,
        family_population: family_population as u32,
        receiver_population: receiver_population as u32,
        generator_population: generator_population as u32,
        functionals: vec![functional],
        receivers: (0..coordinate_population)
            .map(|_| AddressedFactoredIntegralReceiver {
                terms: vec![diagonal.clone()],
            })
            .collect(),
        reconstruction_fibre: restriction.to_vec(),
    })
}

impl MembraneFactoredIntegralReceiverHistory {
    #[allow(clippy::too_many_arguments)]
    pub fn found(
        factor_capacity: &[u64],
        family_orientation: &[i8],
        factor_receiver_classes: &[u32],
        receiver_class_counts: &[u32],
        restrictions: Vec<Vec<(u32, BigUint)>>,
        generators: Vec<Vec<u32>>,
    ) -> Result<Self, ObservableMomentCompressionError> {
        let factors = factor_capacity.len();
        let families = if factors == 0 {
            0
        } else {
            family_orientation.len() / factors
        };
        let receivers = receiver_class_counts.len();
        if factors == 0
            || families == 0
            || receivers == 0
            || restrictions.is_empty()
            || generators.is_empty()
            || factors > u32::MAX as usize
            || family_orientation.len() != families.saturating_mul(factors)
            || factor_receiver_classes.len() != factors.saturating_mul(receivers)
            || factor_capacity.iter().any(|capacity| *capacity == 0)
            || family_orientation
                .iter()
                .any(|orientation| !matches!(*orientation, -1 | 0 | 1))
            || factor_receiver_classes
                .chunks_exact(receivers)
                .any(|classes| {
                    classes
                        .iter()
                        .zip(receiver_class_counts)
                        .any(|(class, count)| *count == 0 || *class >= *count)
                })
            || generators.iter().any(|generator| {
                generator.len() != factors
                    || generator.iter().any(|target| *target as usize >= factors)
            })
        {
            return Err(ObservableMomentCompressionError::Shape);
        }

        let mut primitive_restrictions = Vec::<Vec<(u32, BigUint)>>::new();
        let mut restriction_addresses = BTreeMap::<Vec<(u32, BigUint)>, u32>::new();
        let mut transition_restriction_factors = Vec::with_capacity(restrictions.len());
        for mut restriction in restrictions {
            restriction.sort_by_key(|(factor, _)| *factor);
            if restriction.is_empty()
                || restriction.windows(2).any(|pair| pair[0].0 >= pair[1].0)
                || restriction.iter().any(|(factor, coefficient)| {
                    *factor as usize >= factors || coefficient.is_zero()
                })
            {
                return Err(ObservableMomentCompressionError::Shape);
            }
            let divisor = restriction
                .iter()
                .map(|(_, coefficient)| coefficient.clone())
                .reduce(exact_biguint_gcd)
                .ok_or(ObservableMomentCompressionError::Shape)?;
            let primitive = restriction
                .into_iter()
                .map(|(factor, coefficient)| (factor, coefficient / &divisor))
                .collect::<Vec<_>>();
            let restriction_class = if let Some(address) = restriction_addresses.get(&primitive) {
                *address
            } else {
                let address = u32::try_from(primitive_restrictions.len())
                    .map_err(|_| ObservableMomentCompressionError::Shape)?;
                restriction_addresses.insert(primitive.clone(), address);
                primitive_restrictions.push(primitive);
                address
            };
            transition_restriction_factors.push(IntegralRestrictionFrameFactor {
                restriction_class,
                quadratic_scale: &divisor * &divisor,
            });
        }
        if std::env::var_os("MEM6_FOUND_FACTORED_HISTORY_PROFILE").is_some() {
            eprintln!(
                "mem6-frame-restrictions transitions={} primitive={}",
                transition_restriction_factors.len(),
                primitive_restrictions.len()
            );
        }

        let factor_population = factors as u32;
        let mut present_forms = Vec::<FactoredIntegralReceiverForm>::new();
        let worker_population = std::thread::available_parallelism()
            .map(|population| population.get())
            .unwrap_or(1);
        let mut restriction_at = 0_usize;
        for batch in primitive_restrictions.chunks(worker_population) {
            let generator_family = &generators;
            let term_families = std::thread::scope(|scope| {
                let handles = batch
                    .iter()
                    .map(|restriction| {
                        scope.spawn(move || {
                            membrane_factored_present_terms(
                                restriction,
                                factor_capacity,
                                family_orientation,
                                factor_receiver_classes,
                                generator_family,
                                factors,
                                families,
                                receivers,
                            )
                        })
                    })
                    .collect::<Vec<_>>();
                handles
                    .into_iter()
                    .map(|handle| {
                        handle
                            .join()
                            .map_err(|_| ObservableMomentCompressionError::Factorization)?
                    })
                    .collect::<Result<Vec<_>, ObservableMomentCompressionError>>()
            })?;
            for receivers_at_restriction in term_families {
                for terms in receivers_at_restriction {
                    present_forms
                        .push(FactoredIntegralReceiverForm::new(factor_population, terms)?);
                }
                restriction_at += 1;
            }
            if std::env::var_os("MEM6_FOUND_FACTORED_HISTORY_PROFILE").is_some() {
                eprintln!(
                    "mem6-frame-present restriction={} of={} receivers={} coordinates={}",
                    restriction_at,
                    primitive_restrictions.len(),
                    present_forms.len(),
                    0
                );
            }
        }
        let present_forms_per_restriction = families
            .checked_mul(2)
            .and_then(|count| count.checked_add(receivers.checked_mul(2)?))
            .ok_or(ObservableMomentCompressionError::Shape)?;
        if present_forms.len()
            != primitive_restrictions
                .len()
                .saturating_mul(present_forms_per_restriction)
        {
            return Err(ObservableMomentCompressionError::Factorization);
        }
        if std::env::var_os("MEM6_FOUND_FACTORED_HISTORY_PROFILE").is_some() {
            eprintln!(
                "mem6-frame-present-complete receivers={} coordinates={}",
                present_forms.len(),
                0
            );
        }
        let frame = FactoredRationalReceiverHistoryFrame::found_direct_sum(
            present_forms,
            generators.clone(),
        )?;
        Ok(Self {
            schema: "holonic-engine.membrane-factored-integral-receiver-history.v1".to_owned(),
            frame,
            primitive_restrictions,
            transition_restriction_factors,
            family_population: families as u32,
            receiver_population: receivers as u32,
            generator_population: generators.len() as u32,
            generator_targets: generators,
            present_forms_per_restriction: present_forms_per_restriction as u32,
        })
    }

    pub fn present_transition_receivers(
        &self,
        coordinates: &[BigInt],
    ) -> Result<Vec<Vec<BigInt>>, ObservableMomentCompressionError> {
        let primitive = self.frame.present_receivers(coordinates)?;
        let stride = self.present_forms_per_restriction as usize;
        if primitive.len() != self.primitive_restrictions.len().saturating_mul(stride) {
            return Err(ObservableMomentCompressionError::Factorization);
        }
        self.transition_restriction_factors
            .iter()
            .map(|factor| {
                let begin = factor.restriction_class as usize * stride;
                primitive
                    .get(begin..begin + stride)
                    .map(|values| {
                        let scale = BigInt::from(factor.quadratic_scale.clone());
                        values.iter().map(|value| &scale * value).collect()
                    })
                    .ok_or(ObservableMomentCompressionError::Address)
            })
            .collect()
    }
}
