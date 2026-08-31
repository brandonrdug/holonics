use super::compression::exact_biguint_gcd;
use super::factored_forms::exact_bigint_gcd;
use super::*;
/// One primitive nonzero projective current ray on the native factor population.  The ray is a
/// hot coordinate of the quadratic moment; its removed positive scale is carried separately and
/// squared in the moment weight.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ProjectiveIntegralCurrentRay {
    pub factor_population: u32,
    pub entries: Vec<(u32, BigUint)>,
}

/// One source context entering the projective-ray quotient.  The complete source address and
/// removed scale remain reconstruction testimony even when several contexts meet one ray.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectiveCurrentIngressFactor {
    pub source_context: u32,
    pub ray: u32,
    pub source_weight: BigUint,
    pub removed_scale: BigUint,
}

/// One generator edge in an addressed projective-current passage.  If `x` is the primitive source
/// ray, the exact transported section is `removed_scale * target_rays[target]`; covariance
/// therefore carries `removed_scale^2`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectiveCurrentGeneratorEdge {
    pub source: u32,
    pub generator: u32,
    pub target: u32,
    pub removed_scale: BigUint,
}

/// One finite projective-current section of the factored receiver-history law.  Its population is
/// founded from the current which actually arrived; it is not widened into the union of every
/// possible successor ray.  Factored receiver forms are the dual readout and never become an
/// ambient factor-square matrix.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectiveCurrentSection {
    pub schema: String,
    pub factor_population: u32,
    pub rays: Vec<ProjectiveIntegralCurrentRay>,
    pub weights: Vec<BigUint>,
    pub reconstruction_fibre: Vec<ProjectiveCurrentIngressFactor>,
}

/// One exact dynamic passage between two finite projective-current sections.  The target extent is
/// derived by transporting and condensing this front only.  Repeated transport therefore founds a
/// lightning path while current moves rather than pre-enumerating an infinite ray atlas.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectiveCurrentPassage {
    pub schema: String,
    pub factor_population: u32,
    pub generator_population: u32,
    pub source_ray_population: u32,
    pub target_ray_population: u32,
    pub edges: Vec<ProjectiveCurrentGeneratorEdge>,
    pub target: ProjectiveCurrentSection,
}

impl ProjectiveIntegralCurrentRay {
    fn primitive(
        factor_population: u32,
        entries: impl IntoIterator<Item = (u32, BigUint)>,
    ) -> Result<(BigUint, Self), ObservableMomentCompressionError> {
        if factor_population == 0 {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let mut combined = BTreeMap::<u32, BigUint>::new();
        for (factor, coefficient) in entries {
            if factor >= factor_population {
                return Err(ObservableMomentCompressionError::Shape);
            }
            if coefficient.is_zero() {
                continue;
            }
            *combined.entry(factor).or_default() += coefficient;
        }
        if combined.is_empty() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let divisor = combined
            .values()
            .cloned()
            .reduce(exact_biguint_gcd)
            .ok_or(ObservableMomentCompressionError::Shape)?;
        if divisor.is_zero() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Ok((
            divisor.clone(),
            Self {
                factor_population,
                entries: combined
                    .into_iter()
                    .map(|(factor, coefficient)| (factor, coefficient / &divisor))
                    .collect(),
            },
        ))
    }

    fn transport(
        &self,
        targets: &[u32],
    ) -> Result<(BigUint, Self), ObservableMomentCompressionError> {
        if targets.len() != self.factor_population as usize
            || targets
                .iter()
                .any(|target| *target >= self.factor_population)
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Self::primitive(
            self.factor_population,
            self.entries
                .iter()
                .map(|(source, coefficient)| (targets[*source as usize], coefficient.clone())),
        )
    }

    fn dense_bigint(&self) -> Vec<BigInt> {
        let mut current = vec![BigInt::ZERO; self.factor_population as usize];
        for (factor, coefficient) in &self.entries {
            current[*factor as usize] = BigInt::from(coefficient.clone());
        }
        current
    }
}

impl ProjectiveCurrentSection {
    pub fn found(
        factor_population: u32,
        contexts: Vec<(BigUint, Vec<(u32, BigUint)>)>,
    ) -> Result<Self, ObservableMomentCompressionError> {
        if factor_population == 0
            || contexts.is_empty()
            || contexts
                .iter()
                .any(|(weight, entries)| weight.is_zero() || entries.is_empty())
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let mut rays = Vec::<ProjectiveIntegralCurrentRay>::new();
        let mut ray_addresses = BTreeMap::<ProjectiveIntegralCurrentRay, u32>::new();
        let mut entering_weights = Vec::<BigUint>::new();
        let mut reconstruction_fibre = Vec::with_capacity(contexts.len());
        for (source_context, (source_weight, entries)) in contexts.into_iter().enumerate() {
            let (removed_scale, ray) =
                ProjectiveIntegralCurrentRay::primitive(factor_population, entries)?;
            let ray_address = if let Some(address) = ray_addresses.get(&ray).copied() {
                address
            } else {
                let address = u32::try_from(rays.len())
                    .map_err(|_| ObservableMomentCompressionError::Shape)?;
                ray_addresses.insert(ray.clone(), address);
                rays.push(ray);
                entering_weights.push(BigUint::ZERO);
                address
            };
            let quadratic_scale = &removed_scale * &removed_scale;
            entering_weights[ray_address as usize] += &source_weight * quadratic_scale;
            reconstruction_fibre.push(ProjectiveCurrentIngressFactor {
                source_context: u32::try_from(source_context)
                    .map_err(|_| ObservableMomentCompressionError::Shape)?,
                ray: ray_address,
                source_weight,
                removed_scale,
            });
        }
        Ok(Self {
            schema: "holonic-engine.projective-current-section.v1".to_owned(),
            factor_population,
            rays,
            weights: entering_weights,
            reconstruction_fibre,
        })
    }

    pub fn transport_direct_sum(
        &self,
        generators: &[Vec<u32>],
    ) -> Result<ProjectiveCurrentPassage, ObservableMomentCompressionError> {
        if self.schema != "holonic-engine.projective-current-section.v1"
            || self.rays.is_empty()
            || self.weights.len() != self.rays.len()
            || generators.is_empty()
            || generators.iter().any(|generator| {
                generator.len() != self.factor_population as usize
                    || generator
                        .iter()
                        .any(|target| *target >= self.factor_population)
            })
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let mut target_rays = Vec::<ProjectiveIntegralCurrentRay>::new();
        let mut target_addresses = BTreeMap::<ProjectiveIntegralCurrentRay, u32>::new();
        let mut target_weights = Vec::<BigUint>::new();
        let mut edges = Vec::with_capacity(self.rays.len().saturating_mul(generators.len()));
        let mut reconstruction_fibre = Vec::with_capacity(edges.capacity());
        for (source, (ray, weight)) in self.rays.iter().zip(&self.weights).enumerate() {
            if weight.is_zero() {
                return Err(ObservableMomentCompressionError::Shape);
            }
            for (generator, targets) in generators.iter().enumerate() {
                let (removed_scale, target_ray) = ray.transport(targets)?;
                let target = if let Some(address) = target_addresses.get(&target_ray).copied() {
                    address
                } else {
                    let address = u32::try_from(target_rays.len())
                        .map_err(|_| ObservableMomentCompressionError::Shape)?;
                    target_addresses.insert(target_ray.clone(), address);
                    target_rays.push(target_ray);
                    target_weights.push(BigUint::ZERO);
                    address
                };
                target_weights[target as usize] += weight * &removed_scale * &removed_scale;
                edges.push(ProjectiveCurrentGeneratorEdge {
                    source: source as u32,
                    generator: generator as u32,
                    target,
                    removed_scale: removed_scale.clone(),
                });
                reconstruction_fibre.push(ProjectiveCurrentIngressFactor {
                    source_context: source as u32,
                    ray: target,
                    source_weight: weight.clone(),
                    removed_scale,
                });
            }
        }
        let target = ProjectiveCurrentSection {
            schema: "holonic-engine.projective-current-section.v1".to_owned(),
            factor_population: self.factor_population,
            rays: target_rays,
            weights: target_weights,
            reconstruction_fibre,
        };
        Ok(ProjectiveCurrentPassage {
            schema: "holonic-engine.projective-current-passage.v1".to_owned(),
            factor_population: self.factor_population,
            generator_population: generators.len() as u32,
            source_ray_population: self.rays.len() as u32,
            target_ray_population: target.rays.len() as u32,
            edges,
            target,
        })
    }

    pub fn coordinates_for_family(
        &self,
        contexts: &[(BigUint, Vec<(u32, BigUint)>)],
    ) -> Result<Vec<BigUint>, ObservableMomentCompressionError> {
        let addresses = self
            .rays
            .iter()
            .cloned()
            .enumerate()
            .map(|(address, ray)| (ray, address as u32))
            .collect::<BTreeMap<_, _>>();
        let mut returned = vec![BigUint::ZERO; self.rays.len()];
        for (weight, entries) in contexts {
            if weight.is_zero() {
                return Err(ObservableMomentCompressionError::Shape);
            }
            let (scale, ray) = ProjectiveIntegralCurrentRay::primitive(
                self.factor_population,
                entries.iter().cloned(),
            )?;
            let address = addresses
                .get(&ray)
                .copied()
                .ok_or(ObservableMomentCompressionError::Factorization)?;
            returned[address as usize] += weight * &scale * &scale;
        }
        Ok(returned)
    }

    pub fn rank_one_family(
        &self,
    ) -> Result<Vec<(BigInt, Vec<BigInt>)>, ObservableMomentCompressionError> {
        if self.weights.len() != self.rays.len() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Ok(self
            .weights
            .iter()
            .zip(&self.rays)
            .filter(|(weight, _)| !weight.is_zero())
            .map(|(weight, ray)| (BigInt::from(weight.clone()), ray.dense_bigint()))
            .collect())
    }
}

impl FactoredIntegralReceiverForm {
    /// Retain one already-addressed finite term construction without imposing the separate
    /// primitive-ray quotient.  This is the lawful ingress when restriction, receiver class and
    /// generator incidence already supply term lineage: equal algebraic terms remain distinct
    /// occurrences until a declared condensation asks to identify them.
    pub fn from_addressed_terms(
        factor_population: u32,
        terms: Vec<FactoredIntegralReceiverTerm>,
    ) -> Result<Self, ObservableMomentCompressionError> {
        if factor_population == 0
            || terms.iter().any(|term| {
                term.left.factor_population != factor_population
                    || term.right.factor_population != factor_population
            })
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Ok(Self {
            factor_population,
            terms,
        })
    }

    pub fn new(
        factor_population: u32,
        terms: impl IntoIterator<Item = FactoredIntegralReceiverTerm>,
    ) -> Result<Self, ObservableMomentCompressionError> {
        if factor_population == 0 {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let mut combined =
            HashMap::<(SparseIntegralFunctional, SparseIntegralFunctional), BigInt>::new();
        for term in terms {
            if term.left.factor_population != factor_population
                || term.right.factor_population != factor_population
                || term.coefficient.is_zero()
                || term.left.is_zero()
                || term.right.is_zero()
            {
                continue;
            }
            let (left_scale, mut left) = term.left.primitive()?;
            let (right_scale, mut right) = term.right.primitive()?;
            if right < left {
                std::mem::swap(&mut left, &mut right);
            }
            *combined.entry((left, right)).or_default() +=
                term.coefficient * left_scale * right_scale;
        }
        combined.retain(|_, coefficient| !coefficient.is_zero());
        let mut terms = combined
            .into_iter()
            .map(
                |((left, right), coefficient)| FactoredIntegralReceiverTerm {
                    coefficient,
                    left,
                    right,
                },
            )
            .collect::<Vec<_>>();
        terms.sort_by(|left, right| (&left.left, &left.right).cmp(&(&right.left, &right.right)));
        Ok(Self {
            factor_population,
            terms,
        })
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Return `self = scale * primitive`, retaining the scale needed by every descended factor.
    pub fn primitive(&self) -> Result<(BigInt, Self), ObservableMomentCompressionError> {
        let first = self
            .terms
            .first()
            .ok_or(ObservableMomentCompressionError::Shape)?;
        let gcd = self
            .terms
            .iter()
            .map(|term| term.coefficient.abs())
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
                self.terms.iter().cloned().map(|mut term| {
                    term.coefficient /= &scale;
                    term
                }),
            )?,
        ))
    }

    pub fn pullback_by_targets(
        &self,
        targets: &[u32],
    ) -> Result<Self, ObservableMomentCompressionError> {
        Self::new(
            self.factor_population,
            self.terms
                .iter()
                .map(|term| {
                    Ok(FactoredIntegralReceiverTerm {
                        coefficient: term.coefficient.clone(),
                        left: term.left.pullback_by_targets(targets)?,
                        right: term.right.pullback_by_targets(targets)?,
                    })
                })
                .collect::<Result<Vec<_>, ObservableMomentCompressionError>>()?,
        )
    }

    fn pullback_by_preimages(
        &self,
        preimages: &[Vec<u32>],
    ) -> Result<Self, ObservableMomentCompressionError> {
        Self::new(
            self.factor_population,
            self.terms
                .iter()
                .map(|term| {
                    Ok(FactoredIntegralReceiverTerm {
                        coefficient: term.coefficient.clone(),
                        left: term.left.pullback_by_preimages(preimages)?,
                        right: term.right.pullback_by_preimages(preimages)?,
                    })
                })
                .collect::<Result<Vec<_>, ObservableMomentCompressionError>>()?,
        )
    }

    pub fn contract_rank_one(
        &self,
        current: &[BigInt],
    ) -> Result<BigInt, ObservableMomentCompressionError> {
        self.terms.iter().try_fold(BigInt::ZERO, |sum, term| {
            Ok(sum + &term.coefficient * term.left.read(current)? * term.right.read(current)?)
        })
    }

    pub fn contract_rank_one_family(
        &self,
        family: &[(BigInt, Vec<BigInt>)],
    ) -> Result<BigInt, ObservableMomentCompressionError> {
        if family.is_empty() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        family
            .iter()
            .try_fold(BigInt::ZERO, |sum, (weight, current)| {
                Ok(sum + weight * self.contract_rank_one(current)?)
            })
    }
}

/// A pivot-free receiver-history frame whose forms remain functional pairs.  Pullback closure is
/// exact structural equality in this declared factorization; the ambient bilinear matrices and
/// source rank-one family remain reconstruction testimony.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactoredIntegralReceiverHistoryFrame {
    pub schema: String,
    pub factor_population: u32,
    /// Primitive functional-pair coordinates of the quotient.  Each form has exactly one term
    /// with primitive coefficient one; sums belong to receiver projections below, not to the hot
    /// coordinate identity.
    pub forms: Vec<FactoredIntegralReceiverForm>,
    /// Sparse coordinate combinations for every present receiver.
    pub present_receiver_factors: Vec<Vec<IntegralFormFrameFactor>>,
    pub descended_generator_factors: Vec<Vec<IntegralFormFrameFactor>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RationalIntegralFormFrameFactor {
    pub coordinate: u32,
    pub scale: Rat,
}

/// The exact linear span of complete factored receivers under one plural covariance action.
/// Basis forms remain primitive integral operation complexes; rational factors record only chart
/// change inside their saturated receiver span.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactoredRationalReceiverHistoryFrame {
    pub schema: String,
    pub factor_population: u32,
    pub forms: Vec<FactoredIntegralReceiverForm>,
    pub present_receiver_factors: Vec<Vec<RationalIntegralFormFrameFactor>>,
    pub descended_generator_factors: Vec<Vec<Vec<RationalIntegralFormFrameFactor>>>,
}

type FunctionalPair = (SparseIntegralFunctional, SparseIntegralFunctional);

#[derive(Clone, Debug, PartialEq, Eq)]
struct RationalFactoredForm {
    factor_population: u32,
    terms: BTreeMap<FunctionalPair, Rat>,
}

impl RationalFactoredForm {
    fn from_integral(form: &FactoredIntegralReceiverForm) -> Self {
        Self {
            factor_population: form.factor_population,
            terms: form
                .terms
                .iter()
                .map(|term| {
                    (
                        (term.left.clone(), term.right.clone()),
                        Rat::from_integer(term.coefficient.clone()),
                    )
                })
                .collect(),
        }
    }

    fn pullback_direct_sum(
        &self,
        generator_preimages: &[Vec<Vec<u32>>],
    ) -> Result<Self, ObservableMomentCompressionError> {
        let mut terms = BTreeMap::<FunctionalPair, Rat>::new();
        for preimages in generator_preimages {
            for ((left, right), coefficient) in &self.terms {
                let pulled_left = left.pullback_by_preimages(preimages)?;
                let pulled_right = right.pullback_by_preimages(preimages)?;
                if pulled_left.is_zero() || pulled_right.is_zero() {
                    continue;
                }
                let (left_scale, mut left) = pulled_left.primitive()?;
                let (right_scale, mut right) = pulled_right.primitive()?;
                if right < left {
                    std::mem::swap(&mut left, &mut right);
                }
                *terms.entry((left, right)).or_default() +=
                    coefficient * Rat::from_integer(left_scale * right_scale);
            }
        }
        terms.retain(|_, coefficient| !coefficient.is_zero());
        Ok(Self {
            factor_population: self.factor_population,
            terms,
        })
    }

    fn primitive_integral(
        &self,
    ) -> Result<(Rat, FactoredIntegralReceiverForm), ObservableMomentCompressionError> {
        let first = self
            .terms
            .first_key_value()
            .ok_or(ObservableMomentCompressionError::Shape)?;
        let common_denominator = self.terms.values().fold(BigInt::one(), |held, value| {
            exact_bigint_lcm(held, value.denom().clone())
        });
        let integral = self
            .terms
            .iter()
            .map(|(pair, coefficient)| {
                (
                    pair.clone(),
                    coefficient.numer() * (&common_denominator / coefficient.denom()),
                )
            })
            .collect::<Vec<_>>();
        let divisor = integral
            .iter()
            .map(|(_, coefficient)| coefficient.abs())
            .reduce(exact_bigint_gcd)
            .ok_or(ObservableMomentCompressionError::Shape)?;
        if divisor.is_zero() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let sign = if first.1.is_negative() {
            BigInt::from(-1)
        } else {
            BigInt::one()
        };
        let signed_divisor = sign * divisor;
        let form = FactoredIntegralReceiverForm::new(
            self.factor_population,
            integral.into_iter().map(
                |((left, right), coefficient)| FactoredIntegralReceiverTerm {
                    coefficient: coefficient / &signed_divisor,
                    left,
                    right,
                },
            ),
        )?;
        Ok((Rat::new(signed_divisor, common_denominator), form))
    }
}

fn exact_bigint_lcm(left: BigInt, right: BigInt) -> BigInt {
    if left.is_zero() || right.is_zero() {
        BigInt::ZERO
    } else {
        let divisor = exact_bigint_gcd(left.clone().abs(), right.clone().abs());
        (left / divisor * right).abs()
    }
}

struct RationalFactoredSpanFounder {
    factor_population: u32,
    basis: Vec<RationalFactoredForm>,
    pivot_to_basis: BTreeMap<FunctionalPair, usize>,
}

impl RationalFactoredSpanFounder {
    fn new(factor_population: u32) -> Result<Self, ObservableMomentCompressionError> {
        if factor_population == 0 {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Ok(Self {
            factor_population,
            basis: Vec::new(),
            pivot_to_basis: BTreeMap::new(),
        })
    }

    fn reduce(
        &self,
        mut candidate: RationalFactoredForm,
    ) -> Result<(RationalFactoredForm, Vec<Rat>), ObservableMomentCompressionError> {
        if candidate.factor_population != self.factor_population {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let mut coordinates = vec![Rat::from_integer(BigInt::ZERO); self.basis.len()];
        loop {
            let Some((pivot, coefficient)) = candidate
                .terms
                .first_key_value()
                .map(|(pivot, coefficient)| (pivot.clone(), coefficient.clone()))
            else {
                break;
            };
            let Some(basis_at) = self.pivot_to_basis.get(&pivot).copied() else {
                for value in candidate.terms.values_mut() {
                    *value /= &coefficient;
                }
                return Ok((candidate, coordinates));
            };
            coordinates[basis_at] += &coefficient;
            for (term, basis_coefficient) in &self.basis[basis_at].terms {
                *candidate.terms.entry(term.clone()).or_default() -=
                    &coefficient * basis_coefficient;
            }
            candidate
                .terms
                .retain(|_, coefficient| !coefficient.is_zero());
        }
        Ok((candidate, coordinates))
    }

    fn admit(
        &mut self,
        candidate: RationalFactoredForm,
    ) -> Result<bool, ObservableMomentCompressionError> {
        let (remainder, _) = self.reduce(candidate)?;
        let Some(pivot) = remainder
            .terms
            .first_key_value()
            .map(|(pivot, _)| pivot.clone())
        else {
            return Ok(false);
        };
        let basis_at = self.basis.len();
        self.pivot_to_basis.insert(pivot, basis_at);
        self.basis.push(remainder);
        Ok(true)
    }

    fn factors(
        &self,
        candidate: RationalFactoredForm,
        basis_scales: &[Rat],
    ) -> Result<Vec<RationalIntegralFormFrameFactor>, ObservableMomentCompressionError> {
        let (remainder, coordinates) = self.reduce(candidate)?;
        if !remainder.terms.is_empty() || coordinates.len() != basis_scales.len() {
            return Err(ObservableMomentCompressionError::Factorization);
        }
        Ok(coordinates
            .into_iter()
            .zip(basis_scales)
            .enumerate()
            .filter_map(|(coordinate, (coefficient, basis_scale))| {
                let scale = coefficient * basis_scale;
                (!scale.is_zero()).then_some(RationalIntegralFormFrameFactor {
                    coordinate: coordinate as u32,
                    scale,
                })
            })
            .collect())
    }
}

impl FactoredRationalReceiverHistoryFrame {
    pub fn found_direct_sum(
        present_forms: Vec<FactoredIntegralReceiverForm>,
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
        let generator_preimages = generators
            .iter()
            .map(|generator| {
                let mut preimages = vec![Vec::new(); factor_population as usize];
                for (source, target) in generator.iter().copied().enumerate() {
                    preimages[target as usize].push(source as u32);
                }
                preimages
            })
            .collect::<Vec<_>>();
        let rational_present = present_forms
            .iter()
            .map(RationalFactoredForm::from_integral)
            .collect::<Vec<_>>();
        let mut founder = RationalFactoredSpanFounder::new(factor_population)?;
        for receiver in &rational_present {
            founder.admit(receiver.clone())?;
        }
        if founder.basis.is_empty() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let mut cursor = 0;
        while cursor < founder.basis.len() {
            if std::env::var_os("MEM6_FOUND_FACTORED_HISTORY_PROFILE").is_some() {
                eprintln!(
                    "mem6-rational-span cursor={} rank={}",
                    cursor,
                    founder.basis.len()
                );
            }
            let pulled = founder.basis[cursor].pullback_direct_sum(&generator_preimages)?;
            founder.admit(pulled)?;
            cursor += 1;
        }
        let integral_basis = founder
            .basis
            .iter()
            .map(RationalFactoredForm::primitive_integral)
            .collect::<Result<Vec<_>, _>>()?;
        let basis_scales = integral_basis
            .iter()
            .map(|(scale, _)| scale.clone())
            .collect::<Vec<_>>();
        let forms = integral_basis
            .into_iter()
            .map(|(_, form)| form)
            .collect::<Vec<_>>();
        let present_receiver_factors = rational_present
            .into_iter()
            .map(|receiver| founder.factors(receiver, &basis_scales))
            .collect::<Result<Vec<_>, _>>()?;
        let descended = founder
            .basis
            .iter()
            .map(|form| {
                founder.factors(
                    form.pullback_direct_sum(&generator_preimages)?,
                    &basis_scales,
                )
            })
            .collect::<Result<Vec<_>, ObservableMomentCompressionError>>()?;
        Ok(Self {
            schema: "holonic-engine.factored-rational-receiver-history-frame.v1".to_owned(),
            factor_population,
            forms,
            present_receiver_factors,
            descended_generator_factors: vec![descended],
        })
    }

    pub fn quotient_rank_one_family(
        &self,
        family: &[(BigInt, Vec<BigInt>)],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        self.forms
            .iter()
            .map(|form| form.contract_rank_one_family(family))
            .collect()
    }

    fn apply(
        factors: &[Vec<RationalIntegralFormFrameFactor>],
        coordinates: &[BigInt],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        factors
            .iter()
            .map(|combination| {
                let value = combination.iter().try_fold(
                    Rat::from_integer(BigInt::ZERO),
                    |sum, factor| {
                        coordinates
                            .get(factor.coordinate as usize)
                            .map(|coordinate| {
                                sum + &factor.scale * Rat::from_integer(coordinate.clone())
                            })
                            .ok_or(ObservableMomentCompressionError::Address)
                    },
                )?;
                (value.denom() == &BigInt::one())
                    .then(|| value.numer().clone())
                    .ok_or(ObservableMomentCompressionError::Factorization)
            })
            .collect()
    }

    pub fn present_receivers(
        &self,
        coordinates: &[BigInt],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        if coordinates.len() != self.forms.len() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Self::apply(&self.present_receiver_factors, coordinates)
    }

    pub fn transport_direct_sum(
        &self,
        actions: &[usize],
        coordinates: &[BigInt],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        if actions != [0] || coordinates.len() != self.forms.len() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Self::apply(&self.descended_generator_factors[0], coordinates)
    }
}

struct FactoredIntegralReceiverHistoryFounder {
    factor_population: u32,
    forms: Vec<FactoredIntegralReceiverForm>,
    addresses: HashMap<(SparseIntegralFunctional, SparseIntegralFunctional), u32>,
    present_receiver_factors: Vec<Vec<IntegralFormFrameFactor>>,
}

impl FactoredIntegralReceiverHistoryFounder {
    fn new(factor_population: u32) -> Result<Self, ObservableMomentCompressionError> {
        if factor_population == 0 {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Ok(Self {
            factor_population,
            forms: Vec::new(),
            addresses: HashMap::new(),
            present_receiver_factors: Vec::new(),
        })
    }

    fn intern_term(
        &mut self,
        term: FactoredIntegralReceiverTerm,
    ) -> Result<IntegralFormFrameFactor, ObservableMomentCompressionError> {
        if term.coefficient.is_zero() || term.left.is_zero() || term.right.is_zero() {
            return Ok(IntegralFormFrameFactor {
                coordinate: None,
                scale: BigInt::ZERO,
            });
        }
        if term.left.factor_population != self.factor_population
            || term.right.factor_population != self.factor_population
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let (left_scale, mut left) = term.left.primitive()?;
        let (right_scale, mut right) = term.right.primitive()?;
        if right < left {
            std::mem::swap(&mut left, &mut right);
        }
        let scale = term.coefficient * left_scale * right_scale;
        let key = (left, right);
        let coordinate = if let Some(coordinate) = self.addresses.get(&key).copied() {
            coordinate
        } else {
            let coordinate = u32::try_from(self.forms.len())
                .map_err(|_| ObservableMomentCompressionError::Shape)?;
            let primitive = FactoredIntegralReceiverForm {
                factor_population: self.factor_population,
                terms: vec![FactoredIntegralReceiverTerm {
                    coefficient: BigInt::from(1),
                    left: key.0.clone(),
                    right: key.1.clone(),
                }],
            };
            self.addresses.insert(key, coordinate);
            self.forms.push(primitive);
            coordinate
        };
        Ok(IntegralFormFrameFactor {
            coordinate: Some(coordinate),
            scale,
        })
    }

    fn push_present_receiver(
        &mut self,
        terms: impl IntoIterator<Item = FactoredIntegralReceiverTerm>,
    ) -> Result<(), ObservableMomentCompressionError> {
        let mut combined = BTreeMap::<u32, BigInt>::new();
        for term in terms {
            let factor = self.intern_term(term)?;
            match factor.coordinate {
                None if factor.scale.is_zero() => {}
                Some(coordinate) => *combined.entry(coordinate).or_default() += factor.scale,
                None => return Err(ObservableMomentCompressionError::Factorization),
            }
        }
        combined.retain(|_, scale| !scale.is_zero());
        self.present_receiver_factors.push(
            combined
                .into_iter()
                .map(|(coordinate, scale)| IntegralFormFrameFactor {
                    coordinate: Some(coordinate),
                    scale,
                })
                .collect(),
        );
        Ok(())
    }

    fn finish(
        mut self,
        generators: Vec<Vec<u32>>,
    ) -> Result<FactoredIntegralReceiverHistoryFrame, ObservableMomentCompressionError> {
        if self.forms.is_empty()
            || generators.is_empty()
            || generators.iter().any(|generator| {
                generator.len() != self.factor_population as usize
                    || generator
                        .iter()
                        .any(|target| *target >= self.factor_population)
            })
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let generator_preimages = generators
            .iter()
            .map(|generator| {
                let mut preimages = vec![Vec::new(); self.factor_population as usize];
                for (source, target) in generator.iter().copied().enumerate() {
                    preimages[target as usize].push(source as u32);
                }
                preimages
            })
            .collect::<Vec<_>>();
        let mut descended_generator_factors = vec![Vec::new(); generators.len()];
        let mut cursor = 0;
        while cursor < self.forms.len() {
            if std::env::var_os("MEM6_FOUND_FACTORED_HISTORY_PROFILE").is_some()
                && cursor % 1_000 == 0
            {
                eprintln!(
                    "mem6-frame-closure cursor={} coordinates={}",
                    cursor,
                    self.forms.len()
                );
            }
            let term = self.forms[cursor].terms[0].clone();
            for (generator_at, preimages) in generator_preimages.iter().enumerate() {
                let pulled = FactoredIntegralReceiverTerm {
                    coefficient: term.coefficient.clone(),
                    left: term.left.pullback_by_preimages(preimages)?,
                    right: term.right.pullback_by_preimages(preimages)?,
                };
                descended_generator_factors[generator_at].push(self.intern_term(pulled)?);
            }
            cursor += 1;
        }
        if descended_generator_factors
            .iter()
            .any(|action| action.len() != self.forms.len())
        {
            return Err(ObservableMomentCompressionError::Factorization);
        }
        Ok(FactoredIntegralReceiverHistoryFrame {
            schema: "holonic-engine.factored-integral-receiver-history-frame.v1".to_owned(),
            factor_population: self.factor_population,
            forms: self.forms,
            present_receiver_factors: self.present_receiver_factors,
            descended_generator_factors,
        })
    }
}

impl FactoredIntegralReceiverHistoryFrame {
    /// Found the receiver-history frame for one plural generator front.  Every addressed
    /// generator component acts on the covariance independently and the results add only after
    /// two-leg transport; the descended hot action is the single adjoint direct sum.
    pub fn found_whole_direct_sum(
        present_forms: Vec<FactoredIntegralReceiverForm>,
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
        let mut forms = Vec::<FactoredIntegralReceiverForm>::new();
        let mut addresses = HashMap::<FactoredIntegralReceiverForm, u32>::new();
        let intern = |candidate: FactoredIntegralReceiverForm,
                      forms: &mut Vec<FactoredIntegralReceiverForm>,
                      addresses: &mut HashMap<FactoredIntegralReceiverForm, u32>|
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
            present_receiver_factors.push(vec![intern(form, &mut forms, &mut addresses)?]);
        }
        if forms.is_empty() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let generator_preimages = generators
            .iter()
            .map(|generator| {
                let mut preimages = vec![Vec::new(); factor_population as usize];
                for (source, target) in generator.iter().copied().enumerate() {
                    preimages[target as usize].push(source as u32);
                }
                preimages
            })
            .collect::<Vec<_>>();
        let mut descended = Vec::new();
        let mut cursor = 0;
        while cursor < forms.len() {
            if std::env::var_os("MEM6_FOUND_FACTORED_HISTORY_PROFILE").is_some() && cursor % 25 == 0
            {
                eprintln!(
                    "mem6-direct-sum-closure cursor={} coordinates={}",
                    cursor,
                    forms.len()
                );
            }
            let form = forms[cursor].clone();
            let mut pulled_terms = Vec::new();
            for preimages in &generator_preimages {
                for term in &form.terms {
                    pulled_terms.push(FactoredIntegralReceiverTerm {
                        coefficient: term.coefficient.clone(),
                        left: term.left.pullback_by_preimages(preimages)?,
                        right: term.right.pullback_by_preimages(preimages)?,
                    });
                }
            }
            descended.push(intern(
                FactoredIntegralReceiverForm::new(factor_population, pulled_terms)?,
                &mut forms,
                &mut addresses,
            )?);
            cursor += 1;
        }
        if descended.len() != forms.len() {
            return Err(ObservableMomentCompressionError::Factorization);
        }
        Ok(Self {
            schema: "holonic-engine.factored-integral-receiver-history-frame.v1".to_owned(),
            factor_population,
            forms,
            present_receiver_factors,
            descended_generator_factors: vec![descended],
        })
    }

    /// Found a pivot-free frame whose coordinate atoms are complete factored receivers.  Terms
    /// remain internal incidence of each coordinate, so backward transport preserves exact
    /// cancellation and reconvergence before projective ray interning.
    pub fn found_whole(
        present_forms: Vec<FactoredIntegralReceiverForm>,
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
        let mut forms = Vec::<FactoredIntegralReceiverForm>::new();
        let mut addresses = HashMap::<FactoredIntegralReceiverForm, u32>::new();
        let intern = |candidate: FactoredIntegralReceiverForm,
                      forms: &mut Vec<FactoredIntegralReceiverForm>,
                      addresses: &mut HashMap<FactoredIntegralReceiverForm, u32>|
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
            present_receiver_factors.push(vec![intern(form, &mut forms, &mut addresses)?]);
        }
        if forms.is_empty() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let generator_preimages = generators
            .iter()
            .map(|generator| {
                let mut preimages = vec![Vec::new(); factor_population as usize];
                for (source, target) in generator.iter().copied().enumerate() {
                    preimages[target as usize].push(source as u32);
                }
                preimages
            })
            .collect::<Vec<_>>();
        let mut descended_generator_factors = vec![Vec::new(); generators.len()];
        let mut cursor = 0;
        while cursor < forms.len() {
            if std::env::var_os("MEM6_FOUND_FACTORED_HISTORY_PROFILE").is_some()
                && cursor % 100 == 0
            {
                eprintln!(
                    "mem6-whole-form-closure cursor={} coordinates={}",
                    cursor,
                    forms.len()
                );
            }
            let form = forms[cursor].clone();
            for (generator_at, preimages) in generator_preimages.iter().enumerate() {
                let pulled = form.pullback_by_preimages(preimages)?;
                descended_generator_factors[generator_at].push(intern(
                    pulled,
                    &mut forms,
                    &mut addresses,
                )?);
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
            schema: "holonic-engine.factored-integral-receiver-history-frame.v1".to_owned(),
            factor_population,
            forms,
            present_receiver_factors,
            descended_generator_factors,
        })
    }

    pub fn found(
        present_forms: Vec<FactoredIntegralReceiverForm>,
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
        let mut founder = FactoredIntegralReceiverHistoryFounder::new(factor_population)?;
        for form in present_forms {
            founder.push_present_receiver(form.terms)?;
        }
        founder.finish(generators)
    }

    pub fn quotient_rank_one_family(
        &self,
        family: &[(BigInt, Vec<BigInt>)],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        self.forms
            .iter()
            .map(|form| form.contract_rank_one_family(family))
            .collect()
    }

    pub fn present_receivers(
        &self,
        coordinates: &[BigInt],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        if coordinates.len() != self.forms.len() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        self.present_receiver_factors
            .iter()
            .map(|combination| {
                combination
                    .iter()
                    .try_fold(BigInt::ZERO, |sum, factor| match factor.coordinate {
                        None if factor.scale.is_zero() => Ok(sum),
                        Some(coordinate) => coordinates
                            .get(coordinate as usize)
                            .map(|value| sum + &factor.scale * value)
                            .ok_or(ObservableMomentCompressionError::Address),
                        None => Err(ObservableMomentCompressionError::Factorization),
                    })
            })
            .collect()
    }

    pub fn transport_direct_sum(
        &self,
        generators: &[usize],
        coordinates: &[BigInt],
    ) -> Result<Vec<BigInt>, ObservableMomentCompressionError> {
        if generators.is_empty() || coordinates.len() != self.forms.len() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let mut returned = vec![BigInt::ZERO; self.forms.len()];
        for generator in generators {
            let action = self
                .descended_generator_factors
                .get(*generator)
                .ok_or(ObservableMomentCompressionError::Address)?;
            for (target, factor) in action.iter().enumerate() {
                match factor.coordinate {
                    None if factor.scale.is_zero() => {}
                    Some(source) => {
                        returned[target] += &factor.scale
                            * coordinates
                                .get(source as usize)
                                .ok_or(ObservableMomentCompressionError::Address)?;
                    }
                    None => return Err(ObservableMomentCompressionError::Factorization),
                }
            }
        }
        Ok(returned)
    }
}
