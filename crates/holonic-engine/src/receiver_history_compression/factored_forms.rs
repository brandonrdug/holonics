use super::*;
/// One addressed nonzero coefficient of an exact integral bilinear receiver form.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SparseIntegralFormEntry {
    pub row: u32,
    pub column: u32,
    pub coefficient: BigInt,
}

/// One exact bilinear receiver form on the native factor current.  Entries are ordered, unique,
/// and nonzero.  The form is not required to be symmetric: contraction against a symmetric moment
/// supplies the declared receiver face without silently changing its orientation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SparseIntegralBilinearForm {
    pub factor_population: u32,
    pub entries: Vec<SparseIntegralFormEntry>,
}

impl SparseIntegralBilinearForm {
    pub fn new(
        factor_population: u32,
        entries: impl IntoIterator<Item = ((u32, u32), BigInt)>,
    ) -> Result<Self, ObservableMomentCompressionError> {
        if factor_population == 0 {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let mut combined = BTreeMap::<(u32, u32), BigInt>::new();
        for ((row, column), coefficient) in entries {
            if row >= factor_population || column >= factor_population {
                return Err(ObservableMomentCompressionError::Shape);
            }
            *combined.entry((row, column)).or_default() += coefficient;
        }
        combined.retain(|_, coefficient| !coefficient.is_zero());
        Ok(Self {
            factor_population,
            entries: combined
                .into_iter()
                .map(|((row, column), coefficient)| SparseIntegralFormEntry {
                    row,
                    column,
                    coefficient,
                })
                .collect(),
        })
    }

    pub fn is_zero(&self) -> bool {
        self.entries.is_empty()
    }

    /// Return `self = scale * primitive`, with a positive first primitive coefficient.  This
    /// makes a receiver ray exact without erasing the scale which later output must reconstruct.
    pub fn primitive(
        &self,
    ) -> Result<(BigInt, SparseIntegralBilinearForm), ObservableMomentCompressionError> {
        let first = self
            .entries
            .first()
            .ok_or(ObservableMomentCompressionError::Shape)?;
        let gcd = self
            .entries
            .iter()
            .map(|entry| entry.coefficient.abs())
            .reduce(exact_bigint_gcd)
            .ok_or(ObservableMomentCompressionError::Shape)?;
        if gcd.is_zero() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let scale = if first.coefficient.is_negative() {
            -gcd
        } else {
            gcd
        };
        let primitive = Self::new(
            self.factor_population,
            self.entries
                .iter()
                .map(|entry| ((entry.row, entry.column), &entry.coefficient / &scale)),
        )?;
        Ok((scale, primitive))
    }

    /// Pull this receiver backward through the push-forward current law
    /// `P[target(source), source] = 1`.  Hence
    /// `(P^T R P)[i,j] = R[target(i), target(j)]`; non-injective transport expands the exact
    /// preimage population rather than pretending that a class sum is an unweighted partition.
    pub fn pullback_by_targets(
        &self,
        targets: &[u32],
    ) -> Result<Self, ObservableMomentCompressionError> {
        if targets.len() != self.factor_population as usize
            || targets
                .iter()
                .any(|target| *target >= self.factor_population)
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let mut preimages = vec![Vec::<u32>::new(); self.factor_population as usize];
        for (source, target) in targets.iter().copied().enumerate() {
            preimages[target as usize].push(source as u32);
        }
        let mut pulled = Vec::new();
        for entry in &self.entries {
            for row in &preimages[entry.row as usize] {
                for column in &preimages[entry.column as usize] {
                    pulled.push(((*row, *column), entry.coefficient.clone()));
                }
            }
        }
        Self::new(self.factor_population, pulled)
    }

    pub fn contract_rank_one(
        &self,
        current: &[BigInt],
    ) -> Result<BigInt, ObservableMomentCompressionError> {
        if current.len() != self.factor_population as usize {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Ok(self.entries.iter().fold(BigInt::ZERO, |sum, entry| {
            sum + &entry.coefficient
                * &current[entry.row as usize]
                * &current[entry.column as usize]
        }))
    }
}

pub(crate) fn exact_bigint_gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    while !right.is_zero() {
        let remainder = left % &right;
        left = right;
        right = remainder;
    }
    left.abs()
}

/// One exact factor through the primitive integral form frame.  `None` is the zero receiver;
/// otherwise the represented form is `scale * forms[coordinate]`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntegralFormFrameFactor {
    pub coordinate: Option<u32>,
    pub scale: BigInt,
}

/// One addressed coefficient of a sparse integral functional on the native factor current.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SparseIntegralFunctionalEntry {
    pub factor: u32,
    pub coefficient: BigInt,
}

/// An exact linear reading retained as a sparse covector.  This is the native constituent of a
/// factored receiver term; it is not expanded into a row of an ambient bilinear matrix.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SparseIntegralFunctional {
    pub factor_population: u32,
    pub entries: Vec<SparseIntegralFunctionalEntry>,
}

impl SparseIntegralFunctional {
    pub fn new(
        factor_population: u32,
        entries: impl IntoIterator<Item = (u32, BigInt)>,
    ) -> Result<Self, ObservableMomentCompressionError> {
        if factor_population == 0 {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let mut combined = BTreeMap::<u32, BigInt>::new();
        for (factor, coefficient) in entries {
            if factor >= factor_population {
                return Err(ObservableMomentCompressionError::Shape);
            }
            *combined.entry(factor).or_default() += coefficient;
        }
        combined.retain(|_, coefficient| !coefficient.is_zero());
        Ok(Self {
            factor_population,
            entries: combined
                .into_iter()
                .map(|(factor, coefficient)| SparseIntegralFunctionalEntry {
                    factor,
                    coefficient,
                })
                .collect(),
        })
    }

    pub fn is_zero(&self) -> bool {
        self.entries.is_empty()
    }

    /// Return `self = scale * primitive`, fixing the first primitive coefficient positive.
    pub fn primitive(&self) -> Result<(BigInt, Self), ObservableMomentCompressionError> {
        let first = self
            .entries
            .first()
            .ok_or(ObservableMomentCompressionError::Shape)?;
        let gcd = self
            .entries
            .iter()
            .map(|entry| entry.coefficient.abs())
            .reduce(exact_bigint_gcd)
            .ok_or(ObservableMomentCompressionError::Shape)?;
        if gcd.is_zero() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let scale = if first.coefficient.is_negative() {
            -gcd
        } else {
            gcd
        };
        Ok((
            scale.clone(),
            Self::new(
                self.factor_population,
                self.entries
                    .iter()
                    .map(|entry| (entry.factor, &entry.coefficient / &scale)),
            )?,
        ))
    }

    /// Pull a covector backward through `P[target(source), source] = 1` without constructing `P`.
    pub fn pullback_by_targets(
        &self,
        targets: &[u32],
    ) -> Result<Self, ObservableMomentCompressionError> {
        if targets.len() != self.factor_population as usize
            || targets
                .iter()
                .any(|target| *target >= self.factor_population)
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let coefficient_by_target = self
            .entries
            .iter()
            .map(|entry| (entry.factor, &entry.coefficient))
            .collect::<BTreeMap<_, _>>();
        Self::new(
            self.factor_population,
            targets.iter().enumerate().filter_map(|(source, target)| {
                coefficient_by_target
                    .get(target)
                    .map(|coefficient| (source as u32, (*coefficient).clone()))
            }),
        )
    }

    pub(crate) fn pullback_by_preimages(
        &self,
        preimages: &[Vec<u32>],
    ) -> Result<Self, ObservableMomentCompressionError> {
        if preimages.len() != self.factor_population as usize {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Self::new(
            self.factor_population,
            self.entries.iter().flat_map(|entry| {
                preimages[entry.factor as usize]
                    .iter()
                    .copied()
                    .map(move |source| (source, entry.coefficient.clone()))
            }),
        )
    }

    pub fn read(&self, current: &[BigInt]) -> Result<BigInt, ObservableMomentCompressionError> {
        if current.len() != self.factor_population as usize {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Ok(self.entries.iter().fold(BigInt::ZERO, |sum, entry| {
            sum + &entry.coefficient * &current[entry.factor as usize]
        }))
    }
}

/// One exact coefficient multiplying a pair of sparse functional readings.  Its contraction
/// against a rank-one current `x tensor x` is `coefficient * left(x) * right(x)`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FactoredIntegralReceiverTerm {
    pub coefficient: BigInt,
    pub left: SparseIntegralFunctional,
    pub right: SparseIntegralFunctional,
}

/// A bilinear receiver represented solely by its exact functional pairs.  Because the admitted
/// moment is symmetric, term construction canonically identifies `left tensor right` with
/// `right tensor left`; no other algebraic identification is assumed.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FactoredIntegralReceiverForm {
    pub factor_population: u32,
    pub terms: Vec<FactoredIntegralReceiverTerm>,
}

/// One term occurrence in an addressed functional pool.  Equal left/right functionals may share
/// their immutable occurrence, while this term keeps its own coefficient and receiver position.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddressedFactoredIntegralReceiverTerm {
    pub coefficient: BigInt,
    pub left_functional: u32,
    pub right_functional: u32,
}

/// One complete receiver as an ordered population of addressed term occurrences.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddressedFactoredIntegralReceiver {
    pub terms: Vec<AddressedFactoredIntegralReceiverTerm>,
}

/// A membrane receiver complex whose reusable sparse functionals are owned once.  The restriction
/// section is retained as its reconstruction fibre; the hot terms refer only to pool addresses
/// and never duplicate a sparse functional or materialize an ambient bilinear matrix.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddressedFactoredIntegralReceiverComplex {
    pub schema: String,
    pub factor_population: u32,
    pub family_population: u32,
    pub receiver_population: u32,
    pub generator_population: u32,
    pub functionals: Vec<SparseIntegralFunctional>,
    pub receivers: Vec<AddressedFactoredIntegralReceiver>,
    pub reconstruction_fibre: Vec<(u32, BigUint)>,
}

/// One exact coefficient of a primitive functional-pair coordinate.  The coordinate names a
/// symmetric bilinear face; `scale` retains the complete integral coefficient presented to its
/// declared receiver.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddressedPrimitivePairFactor {
    pub coordinate: u32,
    pub scale: BigInt,
}

/// One apparatus-neutral receiver frame shared by every resident realization.  Sparse
/// functionals are made primitive once over the complete occurrence population; symmetric
/// functional pairs are interned once; and each receiver is the exact sparse sum of those pair
/// coordinates.  `presented_*` retains the ordered pre-condensation term fibre, so combining equal
/// pair coordinates inside one declared receiver never loses lineage or reconstruction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddressedPrimitiveReceiverFrame {
    pub schema: String,
    pub factor_population: u32,
    pub family_population: u32,
    pub receiver_population: u32,
    pub generator_population: u32,
    pub functionals: Vec<SparseIntegralFunctional>,
    pub functional_pairs: Vec<(u32, u32)>,
    pub receiver_factor_offsets: Vec<u64>,
    pub receiver_factors: Vec<AddressedPrimitivePairFactor>,
    pub occurrence_receiver_offsets: Vec<u32>,
    /// The ordered term population before the receiver-local sum quotient.
    pub presented_receiver_term_offsets: Vec<u64>,
    pub presented_term_factors: Vec<AddressedPrimitivePairFactor>,
    /// Exact local-functional decomposition of every presented occurrence.  Together with the
    /// presented pair fibre this reopens the original factorization rather than merely its sum.
    pub occurrence_functional_offsets: Vec<u64>,
    pub occurrence_functional_coordinates: Vec<u32>,
    pub occurrence_functional_scales: Vec<BigInt>,
    pub occurrence_reconstruction_fibres: Vec<Vec<(u32, BigUint)>>,
}

impl AddressedPrimitiveReceiverFrame {
    pub fn found(
        complexes: &[AddressedFactoredIntegralReceiverComplex],
    ) -> Result<Self, ObservableMomentCompressionError> {
        let first = complexes
            .first()
            .ok_or(ObservableMomentCompressionError::Shape)?;
        if first.factor_population == 0
            || first.generator_population == 0
            || first.functionals.is_empty()
            || first.receivers.is_empty()
            || complexes.iter().any(|complex| {
                complex.schema != "holonic-engine.addressed-factored-integral-receiver-complex.v1"
                    || complex.factor_population != first.factor_population
                    || complex.family_population != first.family_population
                    || complex.receiver_population != first.receiver_population
                    || complex.generator_population != first.generator_population
                    || complex.functionals.is_empty()
                    || complex.receivers.is_empty()
                    || complex
                        .functionals
                        .iter()
                        .any(|functional| functional.factor_population != first.factor_population)
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
            return Err(ObservableMomentCompressionError::Shape);
        }

        let mut functional_addresses = BTreeMap::<SparseIntegralFunctional, u32>::new();
        let mut functionals = Vec::<SparseIntegralFunctional>::new();
        let mut occurrence_functional_offsets = Vec::with_capacity(complexes.len() + 1);
        let mut occurrence_functional_coordinates = Vec::new();
        let mut occurrence_functional_scales = Vec::new();
        let mut local_functionals = Vec::<Vec<(u32, BigInt)>>::with_capacity(complexes.len());
        occurrence_functional_offsets.push(0);
        for complex in complexes {
            let mut local = Vec::with_capacity(complex.functionals.len());
            for functional in &complex.functionals {
                let (scale, primitive) = if functional.is_zero() {
                    (BigInt::one(), functional.clone())
                } else {
                    functional.primitive()?
                };
                let coordinate = if let Some(coordinate) = functional_addresses.get(&primitive) {
                    *coordinate
                } else {
                    let coordinate = u32::try_from(functionals.len())
                        .map_err(|_| ObservableMomentCompressionError::Extent)?;
                    functional_addresses.insert(primitive.clone(), coordinate);
                    functionals.push(primitive);
                    coordinate
                };
                local.push((coordinate, scale.clone()));
                occurrence_functional_coordinates.push(coordinate);
                occurrence_functional_scales.push(scale);
            }
            occurrence_functional_offsets.push(
                u64::try_from(occurrence_functional_coordinates.len())
                    .map_err(|_| ObservableMomentCompressionError::Extent)?,
            );
            local_functionals.push(local);
        }

        let mut pair_addresses = BTreeMap::<(u32, u32), u32>::new();
        let mut functional_pairs = Vec::<(u32, u32)>::new();
        let mut receiver_factor_offsets = Vec::new();
        let mut receiver_factors = Vec::new();
        let mut occurrence_receiver_offsets = Vec::with_capacity(complexes.len() + 1);
        let mut presented_receiver_term_offsets = Vec::new();
        let mut presented_term_factors = Vec::new();
        receiver_factor_offsets.push(0);
        occurrence_receiver_offsets.push(0);
        presented_receiver_term_offsets.push(0);
        for (complex, local) in complexes.iter().zip(&local_functionals) {
            for receiver in &complex.receivers {
                let mut combined = BTreeMap::<u32, BigInt>::new();
                for term in &receiver.terms {
                    let (left, left_scale) = local
                        .get(term.left_functional as usize)
                        .ok_or(ObservableMomentCompressionError::Address)?;
                    let (right, right_scale) = local
                        .get(term.right_functional as usize)
                        .ok_or(ObservableMomentCompressionError::Address)?;
                    let (mut left, mut right) = (*left, *right);
                    if right < left {
                        std::mem::swap(&mut left, &mut right);
                    }
                    let pair = (left, right);
                    let coordinate = if let Some(coordinate) = pair_addresses.get(&pair) {
                        *coordinate
                    } else {
                        let coordinate = u32::try_from(functional_pairs.len())
                            .map_err(|_| ObservableMomentCompressionError::Extent)?;
                        pair_addresses.insert(pair, coordinate);
                        functional_pairs.push(pair);
                        coordinate
                    };
                    let scale = &term.coefficient * left_scale * right_scale;
                    presented_term_factors.push(AddressedPrimitivePairFactor {
                        coordinate,
                        scale: scale.clone(),
                    });
                    *combined.entry(coordinate).or_default() += scale;
                }
                presented_receiver_term_offsets.push(
                    u64::try_from(presented_term_factors.len())
                        .map_err(|_| ObservableMomentCompressionError::Extent)?,
                );
                combined.retain(|_, coefficient| !coefficient.is_zero());
                receiver_factors.extend(
                    combined
                        .into_iter()
                        .map(|(coordinate, scale)| AddressedPrimitivePairFactor {
                            coordinate,
                            scale,
                        }),
                );
                receiver_factor_offsets.push(
                    u64::try_from(receiver_factors.len())
                        .map_err(|_| ObservableMomentCompressionError::Extent)?,
                );
            }
            occurrence_receiver_offsets.push(
                u32::try_from(receiver_factor_offsets.len() - 1)
                    .map_err(|_| ObservableMomentCompressionError::Extent)?,
            );
        }
        if functionals.is_empty()
            || functional_pairs.is_empty()
            || receiver_factors.is_empty()
            || receiver_factor_offsets.len() != presented_receiver_term_offsets.len()
            || occurrence_receiver_offsets.last().copied()
                != u32::try_from(receiver_factor_offsets.len() - 1).ok()
        {
            return Err(ObservableMomentCompressionError::Factorization);
        }
        Ok(Self {
            schema: "holonic-engine.addressed-primitive-receiver-frame.v1".to_owned(),
            factor_population: first.factor_population,
            family_population: first.family_population,
            receiver_population: first.receiver_population,
            generator_population: first.generator_population,
            functionals,
            functional_pairs,
            receiver_factor_offsets,
            receiver_factors,
            occurrence_receiver_offsets,
            presented_receiver_term_offsets,
            presented_term_factors,
            occurrence_functional_offsets,
            occurrence_functional_coordinates,
            occurrence_functional_scales,
            occurrence_reconstruction_fibres: complexes
                .iter()
                .map(|complex| complex.reconstruction_fibre.clone())
                .collect(),
        })
    }

    /// Contract the retained rank-one current family into the primitive symmetric pair chart.
    /// This is the apparatus-neutral reference law used to grade a resident realization; it does
    /// not replace the current family with its receiver image or discard the reconstruction fibre.
    pub fn pair_coordinates(
        &self,
        family: &[(BigInt, Vec<BigInt>)],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        if self.schema != "holonic-engine.addressed-primitive-receiver-frame.v1"
            || family.is_empty()
            || family
                .iter()
                .any(|(_, current)| current.len() != self.factor_population as usize)
            || self.functional_pairs.iter().any(|(left, right)| {
                *left as usize >= self.functionals.len()
                    || *right as usize >= self.functionals.len()
            })
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let readings = self
            .functionals
            .iter()
            .map(|functional| {
                family
                    .iter()
                    .map(|(_, current)| functional.read(current))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.functional_pairs
            .iter()
            .map(|(left, right)| {
                family
                    .iter()
                    .enumerate()
                    .try_fold(BigInt::ZERO, |sum, (context, (weight, _))| {
                        Ok(sum
                            + weight
                                * &readings[*left as usize][context]
                                * &readings[*right as usize][context])
                    })
            })
            .collect()
    }

    fn contract_factor_section(
        offsets: &[u64],
        factors: &[AddressedPrimitivePairFactor],
        pair_coordinates: &[BigInt],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        if offsets.first() != Some(&0)
            || offsets.last().copied() != u64::try_from(factors.len()).ok()
            || offsets.windows(2).any(|pair| pair[0] > pair[1])
            || factors
                .iter()
                .any(|factor| factor.coordinate as usize >= pair_coordinates.len())
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        offsets
            .windows(2)
            .map(|window| {
                let begin = usize::try_from(window[0])
                    .map_err(|_| ObservableMomentCompressionError::Extent)?;
                let end = usize::try_from(window[1])
                    .map_err(|_| ObservableMomentCompressionError::Extent)?;
                Ok(factors[begin..end]
                    .iter()
                    .fold(BigInt::ZERO, |sum, factor| {
                        sum + &factor.scale * &pair_coordinates[factor.coordinate as usize]
                    }))
            })
            .collect()
    }

    /// Return every addressed receiver from the condensed sparse pair-factor section.
    pub fn receiver_coordinates(
        &self,
        pair_coordinates: &[BigInt],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        Self::contract_factor_section(
            &self.receiver_factor_offsets,
            &self.receiver_factors,
            pair_coordinates,
        )
    }

    /// Reopen the ordered pre-condensation term fibre against the same pair coordinates.  Equality
    /// with `receiver_coordinates` is the exact local reconstruction gate for the sparse quotient.
    pub fn presented_receiver_coordinates(
        &self,
        pair_coordinates: &[BigInt],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        Self::contract_factor_section(
            &self.presented_receiver_term_offsets,
            &self.presented_term_factors,
            pair_coordinates,
        )
    }
}

impl AddressedFactoredIntegralReceiverComplex {
    /// Reopen pooled functional addresses as their complete ordered receiver occurrences.  No
    /// term is condensed here; image restriction decides equality only after the complete
    /// occurrence has crossed into its current moment chart.
    pub fn reopen_receiver_forms(
        &self,
    ) -> Result<Vec<FactoredIntegralReceiverForm>, ObservableMomentCompressionError> {
        if self.schema != "holonic-engine.addressed-factored-integral-receiver-complex.v1"
            || self.factor_population == 0
            || self.receivers.is_empty()
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        self.receivers
            .iter()
            .map(|receiver| {
                let terms = receiver
                    .terms
                    .iter()
                    .map(|term| {
                        Ok(FactoredIntegralReceiverTerm {
                            coefficient: term.coefficient.clone(),
                            left: self
                                .functionals
                                .get(term.left_functional as usize)
                                .cloned()
                                .ok_or(ObservableMomentCompressionError::Address)?,
                            right: self
                                .functionals
                                .get(term.right_functional as usize)
                                .cloned()
                                .ok_or(ObservableMomentCompressionError::Address)?,
                        })
                    })
                    .collect::<Result<Vec<_>, ObservableMomentCompressionError>>()?;
                FactoredIntegralReceiverForm::from_addressed_terms(self.factor_population, terms)
            })
            .collect()
    }

    /// Contract a weighted rank-one presentation after reading each addressed functional exactly
    /// once per current row.  This is a cold/reference chart for the resident operation; it does
    /// not identify the source presentation with the receiver quotient.
    pub fn contract_rank_one_family(
        &self,
        family: &[(BigInt, Vec<BigInt>)],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        if self.schema != "holonic-engine.addressed-factored-integral-receiver-complex.v1"
            || self.factor_population == 0
            || self.functionals.is_empty()
            || self.receivers.is_empty()
            || family.is_empty()
            || family
                .iter()
                .any(|(_, current)| current.len() != self.factor_population as usize)
            || self.functionals.iter().any(|functional| {
                functional.factor_population != self.factor_population
                    || functional
                        .entries
                        .iter()
                        .any(|entry| entry.factor >= self.factor_population)
            })
            || self
                .receivers
                .iter()
                .flat_map(|receiver| &receiver.terms)
                .any(|term| {
                    term.left_functional as usize >= self.functionals.len()
                        || term.right_functional as usize >= self.functionals.len()
                })
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let readings = self
            .functionals
            .iter()
            .map(|functional| {
                family
                    .iter()
                    .map(|(_, current)| functional.read(current))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.receivers
            .iter()
            .map(|receiver| {
                receiver.terms.iter().try_fold(BigInt::ZERO, |sum, term| {
                    let left = readings
                        .get(term.left_functional as usize)
                        .ok_or(ObservableMomentCompressionError::Address)?;
                    let right = readings
                        .get(term.right_functional as usize)
                        .ok_or(ObservableMomentCompressionError::Address)?;
                    Ok(sum
                        + family.iter().enumerate().fold(
                            BigInt::ZERO,
                            |held, (context, (weight, _))| {
                                held + weight * &term.coefficient * &left[context] * &right[context]
                            },
                        ))
                })
            })
            .collect()
    }
}
