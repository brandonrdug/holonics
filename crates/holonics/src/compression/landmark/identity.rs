//! **The identity atlas: an identity is two constructions with one face, certified on charts
//! whose coverage is checked per component.**
//!
//! [definition] A receiver reads polynomial constructions on a configuration `V ⊆ ℚˢ` through
//! their evaluation face; an **identity** is two constructions with one face, a difference in the
//! kernel of the face, the identity ideal `I(V)` (Lean `Compression/Landmark/Identity.IsIdentity`,
//! `identity_iff_sub_mem_identityIdeal`, `mem_identityIdeal_iff`). A landmark search certifies
//! candidates on **charts**: one-parameter rational parametrizations `t ↦ (N_i(t)/D_i(t))_i`
//! landing in `V`. A construction vanishes on a chart exactly when the numerator of its pullback,
//! a univariate polynomial over ℚ ([`RationalPolynomial`]), is zero; nothing is sampled.
//!
//! [proved-derived; implemented-exact] **Coverage is Zariski density, checked per component, not
//! pointwise.** A chart family certifies a polynomial exactly when it lies in the identity ideal of
//! the union of the images, so it certifies exactly the identities of `V` exactly when
//! `I(⋃ images) = I(V)`; for a sound family that is `V ⊆` the Zariski closure of the images (Lean
//! `certified_eval_iff`, `certifies_exactly_iff`, `identityIdeal_eq_iff_dense`). `V` is declared as
//! its irreducible components ([`Component`]), each a point or a curve with its generators. A
//! chart lands in a component when every generator pulls back to zero, and
//! [`IdentityAtlas::check_coverage`] asks, per component, for a landing chart of its dimension;
//! then `I(⋃ images) = ⋂ I(Vⱼ) = I(V)`. The half-angle chart of the circle misses `(−1, 0)` yet
//! covers the circle, as the punctured chart of the plane does (Lean
//! `punctured_plane_certifies_exactly`); the principal winding of the Galilean fibre `C² = 1`
//! misses the whole component `C = −1`, so its image has a strictly larger identity ideal and it
//! **invents** the identity `C − 1` (`principal_image_ideal_strictly_larger`). A missing component
//! is refused by name, and [`IdentityAtlas::chart_span`] exhibits what the charts alone would
//! certify. Pointwise covering (`certification_sound_iff_covers`) is the law for arbitrary,
//! non-polynomial receivers, which the atlas does not read.
//!
//! [proved-standard; implemented-exact] **The dimension is certified, not trusted.** A component's
//! dimension is the largest number of its coordinates algebraically independent on it (a
//! transcendence basis of its function field can be chosen among the coordinates). A nonzero
//! generator in each single coordinate therefore bounds a point component's dimension by zero, and
//! one in each pair of coordinates bounds a curve's by one; [`IdentityAtlas::new`] refuses a
//! component without that eliminant certificate. A nonconstant chart landing in a curve has an
//! infinite image, and an infinite subset of an irreducible curve is Zariski dense in it; a constant
//! chart landing in a point is the point. Without the certificate a declaration would invent
//! identities: the plane declared a curve and covered by the `x`-axis chart would certify `y`.
//! Neither step is stated in Lean; both are owed in #62 with the identity atlas.
//!
//! [proved-derived; implemented-exact] **The search** ([`IdentityAtlas::search`]) takes a finite
//! family of constructions and returns a basis of the identities in its span: the kernel of the
//! exact matrix of pullback coefficients over every chart, over one common denominator per chart.
//! A candidate that is not an identity is refused with a witness: a point of `V` on a chart where
//! its face is nonzero ([`IdentityVerdict::Distinguished`]), found among `deg N + Σ deg Dᵢ + 1`
//! integer parameters, since only that many can be roots or poles.
//!
//! [open] Out of scope here: the irreducible decomposition of `V` and the irreducibility of each
//! declared component are declared, not computed (primary decomposition), and a curve's eliminants
//! are supplied among its generators, not computed by elimination; charts of more than one
//! parameter (components of dimension two or more); and, owed in #62 (Lean
//! `Compression/Landmark/Identity`), Gröbner completion with the all-degree equality
//! `J = ker(face)` and Richardson's undecidability of identity for expressions in `exp`, `sin`,
//! `|·|` and `π`, where only holonomic classes certify; this owner has no holonomic search.
//!
//! | Lean `Compression/Landmark/Identity` | Rust |
//! |---|---|
//! | `IsIdentity`, `face`, `identityIdeal`, `identity_iff_sub_mem_identityIdeal`, `mem_identityIdeal_iff` | [`IdentityAtlas::is_identity`], [`IdentityAtlas::certify`] |
//! | `certified_of_vanishes` (a sound family) | [`IdentityAtlas::new`] |
//! | `Certified`, `certified_eval_iff`, `certifies_exactly_iff`, `zariskiClosure`, `identityIdeal_eq_iff_dense`, `identityIdeal_antitone` | [`IdentityAtlas::check_coverage`], [`IdentityAtlas::chart_span`], [`IdentityAtlas::search`] |
//! | `galileanFibre`, `windingChart`, `principal_winding_invents_an_identity`, `principal_image_ideal_strictly_larger`, `two_windings_cover`, `two_windings_image_ideal`, `two_windings_certify_exactly`, `galilean_identity_ideal` | tests |
//! | `puncturedChart`, `punctured_plane_certifies_exactly`, `polynomial_density_suffices` (a missing point is harmless; the one-parameter instance is the half-angle circle chart) | tests |
//! | `vanishes_of_certified`, `certification_sound_iff_covers` (arbitrary receivers need pointwise covering) | not read: the atlas certifies polynomial receivers |

use std::collections::BTreeMap;

use num_traits::{One, Zero};

use crate::compression::landmark::LandmarkError;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::polynomial::RationalPolynomial;
use crate::ratio::{Rat, integer};

/// [definition] **A polynomial construction over ℚ** in `s` declared coordinates, sparse, with
/// exponent vectors as keys and no zero coefficient.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Construction {
    variables: usize,
    terms: BTreeMap<Vec<u32>, Rat>,
}

impl Construction {
    /// The zero construction.
    pub fn zero(variables: usize) -> Self {
        Self {
            variables,
            terms: BTreeMap::new(),
        }
    }

    /// A constant.
    pub fn constant(variables: usize, value: Rat) -> Self {
        let mut construction = Self::zero(variables);
        if !value.is_zero() {
            construction.terms.insert(vec![0; variables], value);
        }
        construction
    }

    /// The coordinate `x_index`.
    pub fn variable(variables: usize, index: usize) -> Result<Self, LandmarkError> {
        let mut exponents = vec![0; variables];
        *exponents
            .get_mut(index)
            .ok_or(LandmarkError::VariableCount {
                expected: variables,
                found: index + 1,
            })? = 1;
        Ok(Self::monomial(exponents, Rat::one()))
    }

    /// `c · x^e`, over as many coordinates as the exponent vector has.
    pub fn monomial(exponents: Vec<u32>, coefficient: Rat) -> Self {
        let mut construction = Self::zero(exponents.len());
        if !coefficient.is_zero() {
            construction.terms.insert(exponents, coefficient);
        }
        construction
    }

    /// **Every monomial of total degree at most `degree`**, graded, the finite family a search
    /// declares.
    pub fn monomials(variables: usize, degree: u32) -> Vec<Self> {
        let mut exponents: Vec<Vec<u32>> = vec![Vec::new()];
        for _ in 0..variables {
            exponents = exponents
                .into_iter()
                .flat_map(|prefix: Vec<u32>| {
                    let used: u32 = prefix.iter().sum();
                    (0..=degree - used).map(move |power| {
                        let mut next = prefix.clone();
                        next.push(power);
                        next
                    })
                })
                .collect();
        }
        exponents.sort_by_key(|vector| {
            (
                vector.iter().sum::<u32>(),
                std::cmp::Reverse(vector.clone()),
            )
        });
        exponents
            .into_iter()
            .map(|vector| Self::monomial(vector, Rat::one()))
            .collect()
    }

    /// The declared coordinate count.
    pub fn variables(&self) -> usize {
        self.variables
    }

    /// The terms, keyed by exponent vector.
    pub fn terms(&self) -> &BTreeMap<Vec<u32>, Rat> {
        &self.terms
    }

    /// Whether this is the zero construction.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Whether every term uses only the given coordinates.
    fn supported_within(&self, coordinates: &[usize]) -> bool {
        self.terms.keys().all(|exponents| {
            exponents
                .iter()
                .enumerate()
                .all(|(variable, exponent)| *exponent == 0 || coordinates.contains(&variable))
        })
    }

    /// The largest exponent of one coordinate.
    pub fn degree_in(&self, variable: usize) -> u32 {
        self.terms
            .keys()
            .map(|exponents| exponents[variable])
            .max()
            .unwrap_or(0)
    }

    fn check(&self, other: &Self) -> Result<(), LandmarkError> {
        if self.variables != other.variables {
            return Err(LandmarkError::VariableCount {
                expected: self.variables,
                found: other.variables,
            });
        }
        Ok(())
    }

    fn insert(&mut self, exponents: Vec<u32>, coefficient: Rat) {
        let entry = self.terms.entry(exponents).or_insert_with(Rat::zero);
        *entry += coefficient;
        if entry.is_zero() {
            self.terms.retain(|_, value| !value.is_zero());
        }
    }

    /// `self + other`.
    pub fn add(&self, other: &Self) -> Result<Self, LandmarkError> {
        self.check(other)?;
        let mut sum = self.clone();
        for (exponents, coefficient) in &other.terms {
            sum.insert(exponents.clone(), coefficient.clone());
        }
        Ok(sum)
    }

    /// `self − other`.
    pub fn sub(&self, other: &Self) -> Result<Self, LandmarkError> {
        self.add(&other.scaled(&-Rat::one()))
    }

    /// `c · self`.
    pub fn scaled(&self, factor: &Rat) -> Self {
        let mut scaled = Self::zero(self.variables);
        if !factor.is_zero() {
            for (exponents, coefficient) in &self.terms {
                scaled.terms.insert(exponents.clone(), coefficient * factor);
            }
        }
        scaled
    }

    /// `self · other`.
    pub fn mul(&self, other: &Self) -> Result<Self, LandmarkError> {
        self.check(other)?;
        let mut product = Self::zero(self.variables);
        for (left, left_coefficient) in &self.terms {
            for (right, right_coefficient) in &other.terms {
                let exponents = left.iter().zip(right).map(|(a, b)| a + b).collect();
                product.insert(exponents, left_coefficient * right_coefficient);
            }
        }
        Ok(product)
    }

    /// The face at a point of `ℚˢ`.
    pub fn evaluate(&self, point: &[Rat]) -> Result<Rat, LandmarkError> {
        if point.len() != self.variables {
            return Err(LandmarkError::VariableCount {
                expected: self.variables,
                found: point.len(),
            });
        }
        let mut value = Rat::zero();
        for (exponents, coefficient) in &self.terms {
            let mut term = coefficient.clone();
            for (coordinate, exponent) in point.iter().zip(exponents) {
                for _ in 0..*exponent {
                    term *= coordinate;
                }
            }
            value += term;
        }
        Ok(value)
    }
}

/// [definition] The dimension of a declared irreducible component, and of a chart's image.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ComponentDimension {
    Point,
    Curve,
}

/// [definition] **A one-parameter rational chart** `t ↦ (N_i(t)/D_i(t))_i`, defined off the roots
/// of its denominators.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RationalChart {
    name: String,
    coordinates: Vec<(RationalPolynomial, RationalPolynomial)>,
}

impl RationalChart {
    /// A chart from its coordinate ratios; a zero denominator is refused.
    pub fn new(
        name: impl Into<String>,
        coordinates: Vec<(RationalPolynomial, RationalPolynomial)>,
    ) -> Result<Self, LandmarkError> {
        let name = name.into();
        if coordinates
            .iter()
            .any(|(_, denominator)| denominator.is_zero())
        {
            return Err(LandmarkError::ZeroDenominator { chart: name });
        }
        Ok(Self { name, coordinates })
    }

    /// A polynomial chart `t ↦ (P_i(t))_i`.
    pub fn polynomial(
        name: impl Into<String>,
        coordinates: Vec<RationalPolynomial>,
    ) -> Result<Self, LandmarkError> {
        Self::new(
            name,
            coordinates
                .into_iter()
                .map(|numerator| (numerator, RationalPolynomial::one()))
                .collect(),
        )
    }

    /// The chart's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// **A curve when some coordinate is nonconstant** (`N′D − ND′ ≠ 0`), a point otherwise.
    pub fn dimension(&self) -> ComponentDimension {
        let moves = self.coordinates.iter().any(|(numerator, denominator)| {
            !numerator
                .derivative()
                .times(denominator)
                .minus(&numerator.times(&denominator.derivative()))
                .is_zero()
        });
        if moves {
            ComponentDimension::Curve
        } else {
            ComponentDimension::Point
        }
    }

    /// The chart point at `t`, or `None` where a denominator vanishes.
    pub fn point(&self, parameter: &Rat) -> Option<Vec<Rat>> {
        self.coordinates
            .iter()
            .map(|(numerator, denominator)| {
                let below = denominator.evaluate(parameter);
                (!below.is_zero()).then(|| numerator.evaluate(parameter) / below)
            })
            .collect()
    }

    fn check(&self, construction: &Construction) -> Result<(), LandmarkError> {
        if construction.variables() != self.coordinates.len() {
            return Err(LandmarkError::VariableCount {
                expected: self.coordinates.len(),
                found: construction.variables(),
            });
        }
        Ok(())
    }

    /// **The numerator of the pullback** `p ∘ χ = N / ∏ D_i^(E_i)`, over the declared per-coordinate
    /// degree bounds `E_i ≥ deg_i p`: `N = Σ_m c_m ∏ N_i^(m_i) D_i^(E_i − m_i)`. One bound per
    /// coordinate is required, and a bound below the construction's degree in its coordinate is
    /// refused: it would drop denominator powers and return a polynomial that is not the numerator.
    pub fn pullback(
        &self,
        construction: &Construction,
        bounds: &[u32],
    ) -> Result<RationalPolynomial, LandmarkError> {
        self.check(construction)?;
        if bounds.len() != self.coordinates.len() {
            return Err(LandmarkError::VariableCount {
                expected: self.coordinates.len(),
                found: bounds.len(),
            });
        }
        for (variable, bound) in bounds.iter().enumerate() {
            let degree = construction.degree_in(variable);
            if *bound < degree {
                return Err(LandmarkError::DegreeBound {
                    variable,
                    bound: *bound,
                    degree,
                });
            }
        }
        let mut numerator = RationalPolynomial::zero();
        for (exponents, coefficient) in construction.terms() {
            let mut term = RationalPolynomial::constant(coefficient.clone());
            for ((index, (top, bottom)), exponent) in
                self.coordinates.iter().enumerate().zip(exponents)
            {
                let bound = bounds[index];
                for _ in 0..*exponent {
                    term = term.times(top);
                }
                for _ in *exponent..bound {
                    term = term.times(bottom);
                }
            }
            numerator = numerator.plus(&term);
        }
        Ok(numerator)
    }

    /// Whether a construction vanishes on the whole chart.
    pub fn vanishes(&self, construction: &Construction) -> Result<bool, LandmarkError> {
        Ok(self
            .pullback(construction, &own_bounds(construction))?
            .is_zero())
    }
}

fn own_bounds(construction: &Construction) -> Vec<u32> {
    (0..construction.variables())
        .map(|variable| construction.degree_in(variable))
        .collect()
}

/// [definition] **A declared irreducible component** of the configuration: its generators and its
/// dimension. Irreducibility is a declaration (primary decomposition is out of scope); the dimension
/// is certified by [`IdentityAtlas::new`] from the generators' eliminants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Component {
    name: String,
    generators: Vec<Construction>,
    dimension: ComponentDimension,
}

impl Component {
    /// A component with its generators.
    pub fn new(
        name: impl Into<String>,
        generators: Vec<Construction>,
        dimension: ComponentDimension,
    ) -> Self {
        Self {
            name: name.into(),
            generators,
            dimension,
        }
    }

    /// The component's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Its dimension.
    pub fn dimension(&self) -> ComponentDimension {
        self.dimension
    }

    /// **The eliminant certificate of the declared dimension `d`**: every `d + 1` of the `variables`
    /// coordinates carry a nonzero generator in those coordinates alone (every coordinate for a
    /// point, every pair for a curve), so they are algebraically dependent on the component and its
    /// dimension is at most `d`. The first coordinate set without one is refused.
    fn certify_dimension(&self, variables: usize) -> Result<(), LandmarkError> {
        let sets: Vec<Vec<usize>> = match self.dimension {
            ComponentDimension::Point => (0..variables).map(|first| vec![first]).collect(),
            ComponentDimension::Curve => (0..variables)
                .flat_map(|first| (first + 1..variables).map(move |second| vec![first, second]))
                .collect(),
        };
        for coordinates in sets {
            let bounded = self
                .generators
                .iter()
                .any(|generator| !generator.is_zero() && generator.supported_within(&coordinates));
            if !bounded {
                return Err(LandmarkError::UncertifiedDimension {
                    component: self.name.clone(),
                    dimension: self.dimension,
                    coordinates,
                });
            }
        }
        Ok(())
    }
}

/// [definition] **The verdict on a candidate identity.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IdentityVerdict {
    /// The two constructions have one face on every chart, hence on `V`.
    Identity,
    /// A point of `V` on `chart` at `parameter` where the difference has the nonzero `face`.
    Distinguished {
        chart: String,
        parameter: Rat,
        point: Vec<Rat>,
        face: Rat,
    },
}

/// [definition] **The identities in the span of a finite family**: a basis, both as coefficient
/// vectors over the family and as constructions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentitySearch {
    pub coefficients: Vec<Vec<Rat>>,
    pub identities: Vec<Construction>,
}

/// [definition] **An identity atlas**: a configuration declared by its components, and a family of
/// sound charts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentityAtlas {
    variables: usize,
    components: Vec<Component>,
    charts: Vec<RationalChart>,
}

impl IdentityAtlas {
    /// An atlas. Every component's declared dimension must be **certified by its eliminants**
    /// (a nonzero generator in every coordinate for a point, in every pair of coordinates for a
    /// curve), and every chart must speak the configuration's coordinates and **land in some
    /// component** (Lean `certified_of_vanishes` needs a sound family); an uncertified dimension and
    /// an unsound chart are refused by name.
    pub fn new(
        variables: usize,
        components: Vec<Component>,
        charts: Vec<RationalChart>,
    ) -> Result<Self, LandmarkError> {
        if components.is_empty() {
            return Err(LandmarkError::EmptyConfiguration);
        }
        for generator in components
            .iter()
            .flat_map(|component| &component.generators)
        {
            if generator.variables() != variables {
                return Err(LandmarkError::VariableCount {
                    expected: variables,
                    found: generator.variables(),
                });
            }
        }
        for component in &components {
            component.certify_dimension(variables)?;
        }
        let atlas = Self {
            variables,
            components,
            charts,
        };
        for chart in &atlas.charts {
            if chart.coordinates.len() != variables {
                return Err(LandmarkError::VariableCount {
                    expected: variables,
                    found: chart.coordinates.len(),
                });
            }
            let mut lands = false;
            for component in &atlas.components {
                lands |= atlas.lands_in(chart, component)?;
            }
            if !lands {
                return Err(LandmarkError::ChartOutsideConfiguration {
                    chart: chart.name.clone(),
                });
            }
        }
        Ok(atlas)
    }

    fn lands_in(
        &self,
        chart: &RationalChart,
        component: &Component,
    ) -> Result<bool, LandmarkError> {
        for generator in &component.generators {
            if !chart.vanishes(generator)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// The charts.
    pub fn charts(&self) -> &[RationalChart] {
        &self.charts
    }

    /// **The coverage of each component**: the first chart of its dimension landing in it.
    pub fn coverage(&self) -> Result<Vec<Option<usize>>, LandmarkError> {
        let mut coverage = Vec::with_capacity(self.components.len());
        for component in &self.components {
            let mut covering = None;
            for (index, chart) in self.charts.iter().enumerate() {
                if chart.dimension() == component.dimension && self.lands_in(chart, component)? {
                    covering = Some(index);
                    break;
                }
            }
            coverage.push(covering);
        }
        Ok(coverage)
    }

    /// **Coverage per component**, `I(⋃ images) = I(V)`: refused naming the first component no chart
    /// of its dimension lands in, the invented-identity failure.
    pub fn check_coverage(&self) -> Result<(), LandmarkError> {
        for (component, covering) in self.components.iter().zip(self.coverage()?) {
            if covering.is_none() {
                return Err(LandmarkError::UncoveredComponent {
                    component: component.name.clone(),
                });
            }
        }
        Ok(())
    }

    /// **What the charts alone certify** in the span of a family: the kernel of the exact matrix of
    /// pullback coefficients. It equals the identities exactly when the atlas covers `V`; with a
    /// missing component it contains invented identities.
    pub fn chart_span(&self, family: &[Construction]) -> Result<IdentitySearch, LandmarkError> {
        if family.is_empty() {
            return Err(LandmarkError::EmptyFamily);
        }
        for construction in family {
            if construction.variables() != self.variables {
                return Err(LandmarkError::VariableCount {
                    expected: self.variables,
                    found: construction.variables(),
                });
            }
        }
        let bounds: Vec<u32> = (0..self.variables)
            .map(|variable| {
                family
                    .iter()
                    .map(|construction| construction.degree_in(variable))
                    .max()
                    .unwrap_or(0)
            })
            .collect();
        let mut rows: Vec<Vec<Rat>> = Vec::new();
        for chart in &self.charts {
            let pullbacks = family
                .iter()
                .map(|construction| chart.pullback(construction, &bounds))
                .collect::<Result<Vec<_>, _>>()?;
            let top = pullbacks
                .iter()
                .filter_map(RationalPolynomial::degree)
                .max()
                .unwrap_or(0);
            for power in 0..=top {
                rows.push(
                    pullbacks
                        .iter()
                        .map(|pullback| pullback.coefficient(power))
                        .collect(),
                );
            }
        }
        let coefficients = if rows.is_empty() {
            (0..family.len())
                .map(|index| {
                    (0..family.len())
                        .map(|column| integer(i64::from(column == index)))
                        .collect()
                })
                .collect()
        } else {
            ExactRatMatrix::new(rows)?.kernel_basis()?
        };
        let identities = coefficients
            .iter()
            .map(|vector| combine(self.variables, family, vector))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(IdentitySearch {
            coefficients,
            identities,
        })
    }

    /// **The identities in the span of a finite family**, refused unless every component is covered.
    pub fn search(&self, family: &[Construction]) -> Result<IdentitySearch, LandmarkError> {
        self.check_coverage()?;
        self.chart_span(family)
    }

    /// **Whether a construction vanishes on `V`**, refused unless every component is covered; a
    /// nonzero face is returned with its point.
    pub fn certify(&self, construction: &Construction) -> Result<IdentityVerdict, LandmarkError> {
        self.check_coverage()?;
        if construction.variables() != self.variables {
            return Err(LandmarkError::VariableCount {
                expected: self.variables,
                found: construction.variables(),
            });
        }
        let bounds = own_bounds(construction);
        for chart in &self.charts {
            let numerator = chart.pullback(construction, &bounds)?;
            let Some(degree) = numerator.degree() else {
                continue;
            };
            let poles: usize = chart
                .coordinates
                .iter()
                .filter_map(|(_, denominator)| denominator.degree())
                .sum();
            for step in 0..=(degree + poles) {
                let magnitude = i64::try_from(step.div_ceil(2)).unwrap_or(i64::MAX);
                let parameter = integer(if step % 2 == 1 { magnitude } else { -magnitude });
                let Some(point) = chart.point(&parameter) else {
                    continue;
                };
                if numerator.evaluate(&parameter).is_zero() {
                    continue;
                }
                let face = construction.evaluate(&point)?;
                return Ok(IdentityVerdict::Distinguished {
                    chart: chart.name.clone(),
                    parameter,
                    point,
                    face,
                });
            }
        }
        Ok(IdentityVerdict::Identity)
    }

    /// **Two constructions with one face** (Lean `IsIdentity`, `identity_iff_sub_mem_identityIdeal`).
    pub fn is_identity(
        &self,
        left: &Construction,
        right: &Construction,
    ) -> Result<IdentityVerdict, LandmarkError> {
        self.certify(&left.sub(right)?)
    }
}

fn combine(
    variables: usize,
    family: &[Construction],
    coefficients: &[Rat],
) -> Result<Construction, LandmarkError> {
    let mut sum = Construction::zero(variables);
    for (construction, coefficient) in family.iter().zip(coefficients) {
        sum = sum.add(&construction.scaled(coefficient))?;
    }
    Ok(sum)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn polynomial(coefficients: &[i64]) -> RationalPolynomial {
        RationalPolynomial::new(coefficients.iter().map(|value| integer(*value)).collect())
    }

    fn x(variables: usize, index: usize) -> Construction {
        Construction::variable(variables, index).unwrap()
    }

    fn one(variables: usize) -> Construction {
        Construction::constant(variables, Rat::one())
    }

    /// `x² + y² − 1`.
    fn circle_equation() -> Construction {
        x(2, 0)
            .mul(&x(2, 0))
            .unwrap()
            .add(&x(2, 1).mul(&x(2, 1)).unwrap())
            .unwrap()
            .sub(&one(2))
            .unwrap()
    }

    /// The circle with its half-angle chart `t ↦ ((1 − t²)/(1 + t²), 2t/(1 + t²))`.
    fn circle() -> IdentityAtlas {
        let half_angle = RationalChart::new(
            "half-angle",
            vec![
                (polynomial(&[1, 0, -1]), polynomial(&[1, 0, 1])),
                (polynomial(&[0, 2]), polynomial(&[1, 0, 1])),
            ],
        )
        .unwrap();
        IdentityAtlas::new(
            2,
            vec![Component::new(
                "circle",
                vec![circle_equation()],
                ComponentDimension::Curve,
            )],
            vec![half_angle],
        )
        .unwrap()
    }

    /// Lean `galileanFibre` in `(C, S)`: the components `C = 1` and `C = −1`.
    fn galilean_components() -> Vec<Component> {
        vec![
            Component::new(
                "C = 1",
                vec![x(2, 0).sub(&one(2)).unwrap()],
                ComponentDimension::Curve,
            ),
            Component::new(
                "C = -1",
                vec![x(2, 0).add(&one(2)).unwrap()],
                ComponentDimension::Curve,
            ),
        ]
    }

    /// Lean `windingChart e` at `k = 0`: `t ↦ (e, 2et)`.
    fn winding(e: i64) -> RationalChart {
        RationalChart::polynomial(
            format!("winding {e}"),
            vec![polynomial(&[e]), polynomial(&[0, 2 * e])],
        )
        .unwrap()
    }

    /// Lean `IsIdentity`, `identity_iff_sub_mem_identityIdeal`: on the circle `(x + y)²` and
    /// `1 + 2xy` are two constructions with one face; `x` and `1` are not, and the refusal carries a
    /// point of the circle where they differ.
    #[test]
    fn an_identity_is_two_constructions_with_one_face() {
        let atlas = circle();
        let sum = x(2, 0).add(&x(2, 1)).unwrap();
        let left = sum.mul(&sum).unwrap();
        let right = one(2)
            .add(&x(2, 0).mul(&x(2, 1)).unwrap().scaled(&integer(2)))
            .unwrap();
        assert_ne!(left, right);
        assert_eq!(
            atlas.is_identity(&left, &right).unwrap(),
            IdentityVerdict::Identity
        );
        let IdentityVerdict::Distinguished { point, face, .. } =
            atlas.is_identity(&x(2, 0), &one(2)).unwrap()
        else {
            panic!("x = 1 is not an identity of the circle");
        };
        assert!(circle_equation().evaluate(&point).unwrap().is_zero());
        assert_eq!(face, &point[0] - Rat::one());
        assert!(!face.is_zero());
    }

    /// Lean `punctured_plane_certifies_exactly`, `identityIdeal_eq_iff_dense`: **the half-angle
    /// chart misses `(−1, 0)` and still covers the circle.** The pullback of `x + 1` is the nonzero constant `2`, so no parameter reaches
    /// `(−1, 0)`; yet the chart is a nonconstant curve landing in the one component, and the search
    /// over the monomials of degree at most two returns exactly the line of `x² + y² − 1`.
    #[test]
    fn a_chart_missing_a_point_still_covers_its_component() {
        let atlas = circle();
        let chart = &atlas.charts()[0];
        let shifted = x(2, 0).add(&one(2)).unwrap();
        assert_eq!(chart.pullback(&shifted, &[1, 0]).unwrap(), polynomial(&[2]));
        assert!(
            circle_equation()
                .evaluate(&[integer(-1), integer(0)])
                .unwrap()
                .is_zero()
        );
        assert_eq!(atlas.coverage().unwrap(), vec![Some(0)]);
        let found = atlas.search(&Construction::monomials(2, 2)).unwrap();
        assert_eq!(found.identities.len(), 1);
        let identity = &found.identities[0];
        let unit = identity.terms()[&vec![0u32, 0]].clone();
        assert_eq!(identity.scaled(&-unit.recip()), circle_equation());
    }

    /// Lean `principal_winding_invents_an_identity`, `principal_image_ideal_strictly_larger`: **the
    /// principal winding misses the component `C = −1`**, and the coverage check refuses it by name; what the chart
    /// alone certifies in degree two is the three-dimensional `(C − 1)·{1, C, S}`, which contains the
    /// invented identity `C − 1`.
    #[test]
    fn one_winding_invents_an_identity() {
        let atlas = IdentityAtlas::new(2, galilean_components(), vec![winding(1)]).unwrap();
        let refusal = Err(LandmarkError::UncoveredComponent {
            component: "C = -1".into(),
        });
        assert_eq!(atlas.check_coverage(), refusal);
        assert_eq!(
            atlas.search(&Construction::monomials(2, 2)),
            Err(LandmarkError::UncoveredComponent {
                component: "C = -1".into()
            })
        );
        let invented = x(2, 0).sub(&one(2)).unwrap();
        assert!(atlas.charts()[0].vanishes(&invented).unwrap());
        let span = atlas.chart_span(&Construction::monomials(2, 2)).unwrap();
        assert_eq!(span.identities.len(), 3);
        let with_invented = atlas.chart_span(&[invented.clone(), one(2)]).unwrap();
        assert_eq!(with_invented.identities.len(), 1);
    }

    /// Lean `two_windings_cover`, `two_windings_image_ideal`, `two_windings_certify_exactly`,
    /// `galilean_identity_ideal`: the half-turn winding covers `C = −1`; the degree-two identities
    /// are the line of `C² − 1`, and `C − 1` is refused at the point `(−1, 0)` with face `−2`.
    #[test]
    fn two_windings_refuse_the_invented_identity() {
        let atlas =
            IdentityAtlas::new(2, galilean_components(), vec![winding(1), winding(-1)]).unwrap();
        assert_eq!(atlas.coverage().unwrap(), vec![Some(0), Some(1)]);
        let found = atlas.search(&Construction::monomials(2, 2)).unwrap();
        assert_eq!(found.identities.len(), 1);
        let square = x(2, 0).mul(&x(2, 0)).unwrap().sub(&one(2)).unwrap();
        assert_eq!(atlas.certify(&square).unwrap(), IdentityVerdict::Identity);
        let identity = &found.identities[0];
        let unit = identity.terms()[&vec![0u32, 0]].clone();
        assert_eq!(identity.scaled(&-unit.recip()), square);
        assert_eq!(
            atlas.certify(&x(2, 0).sub(&one(2)).unwrap()).unwrap(),
            IdentityVerdict::Distinguished {
                chart: "winding -1".into(),
                parameter: integer(0),
                point: vec![integer(-1), integer(0)],
                face: integer(-2),
            }
        );
    }

    /// **A point does not cover a curve.** With the constant chart at `(−1, 0)` beside the principal
    /// winding, the component `C = −1` is still uncovered, and the charts certify the invented
    /// `(C − 1)·S`, which is not an identity of the fibre.
    #[test]
    fn a_point_chart_does_not_cover_a_curve_component() {
        let point =
            RationalChart::polynomial("(-1, 0)", vec![polynomial(&[-1]), polynomial(&[])]).unwrap();
        assert_eq!(point.dimension(), ComponentDimension::Point);
        let atlas = IdentityAtlas::new(2, galilean_components(), vec![winding(1), point]).unwrap();
        assert!(matches!(
            atlas.check_coverage(),
            Err(LandmarkError::UncoveredComponent { .. })
        ));
        let invented = x(2, 0).sub(&one(2)).unwrap().mul(&x(2, 1)).unwrap();
        let span = atlas.chart_span(&[invented]).unwrap();
        assert_eq!(span.identities.len(), 1);
        let covered =
            IdentityAtlas::new(2, galilean_components(), vec![winding(1), winding(-1)]).unwrap();
        assert!(matches!(
            covered.certify(&x(2, 0).sub(&one(2)).unwrap().mul(&x(2, 1)).unwrap()),
            Ok(IdentityVerdict::Distinguished { .. })
        ));
    }

    /// Lean `certified_of_vanishes` needs soundness: a chart leaving the configuration is refused.
    #[test]
    fn a_chart_outside_the_configuration_is_refused() {
        let diagonal =
            RationalChart::polynomial("diagonal", vec![polynomial(&[0, 1]), polynomial(&[0, 1])])
                .unwrap();
        assert_eq!(
            IdentityAtlas::new(2, galilean_components(), vec![diagonal]),
            Err(LandmarkError::ChartOutsideConfiguration {
                chart: "diagonal".into()
            })
        );
        assert!(matches!(
            RationalChart::new("pole", vec![(polynomial(&[1]), RationalPolynomial::zero())]),
            Err(LandmarkError::ZeroDenominator { .. })
        ));
    }

    /// **A pullback over short or deficient bounds is refused, not panicked on or misread.** The
    /// circle's generator has degree two in each coordinate: one bound, or the bounds `[1, 1]`,
    /// would drop denominator powers and return a nonzero polynomial for a construction vanishing
    /// on the chart; the bounds `[2, 2]` and any larger ones return the zero numerator.
    #[test]
    fn a_pullback_refuses_short_and_deficient_bounds() {
        let atlas = circle();
        let chart = &atlas.charts()[0];
        let equation = circle_equation();
        assert_eq!(
            chart.pullback(&equation, &[2]),
            Err(LandmarkError::VariableCount {
                expected: 2,
                found: 1
            })
        );
        assert_eq!(
            chart.pullback(&equation, &[1, 1]),
            Err(LandmarkError::DegreeBound {
                variable: 0,
                bound: 1,
                degree: 2
            })
        );
        assert_eq!(
            chart.pullback(&equation, &[2, 1]),
            Err(LandmarkError::DegreeBound {
                variable: 1,
                bound: 1,
                degree: 2
            })
        );
        assert!(chart.pullback(&equation, &[2, 2]).unwrap().is_zero());
        assert!(chart.pullback(&equation, &[3, 5]).unwrap().is_zero());
    }

    /// **A false dimension declaration is refused, so it cannot invent an identity.** The plane
    /// declared a curve (no generator) with the `x`-axis chart would certify `y = 0`; the curve
    /// `C = 1` declared a point with the constant chart `(1, 0)` would certify `S = 0`; the plane
    /// `z = 0` of `ℚ³` declared a curve with the chart `(t, 0, 0)` would certify `y = 0`. Each lacks
    /// the eliminant of its declared dimension and is refused by name.
    #[test]
    fn a_false_dimension_is_refused() {
        let axis = RationalChart::polynomial("x-axis", vec![polynomial(&[0, 1]), polynomial(&[])])
            .unwrap();
        assert_eq!(
            IdentityAtlas::new(
                2,
                vec![Component::new("plane", vec![], ComponentDimension::Curve)],
                vec![axis],
            ),
            Err(LandmarkError::UncertifiedDimension {
                component: "plane".into(),
                dimension: ComponentDimension::Curve,
                coordinates: vec![0, 1],
            })
        );
        let point =
            RationalChart::polynomial("(1, 0)", vec![polynomial(&[1]), polynomial(&[])]).unwrap();
        assert_eq!(
            IdentityAtlas::new(
                2,
                vec![Component::new(
                    "C = 1",
                    vec![x(2, 0).sub(&one(2)).unwrap()],
                    ComponentDimension::Point,
                )],
                vec![point],
            ),
            Err(LandmarkError::UncertifiedDimension {
                component: "C = 1".into(),
                dimension: ComponentDimension::Point,
                coordinates: vec![1],
            })
        );
        let line = RationalChart::polynomial(
            "(t, 0, 0)",
            vec![polynomial(&[0, 1]), polynomial(&[]), polynomial(&[])],
        )
        .unwrap();
        assert_eq!(
            IdentityAtlas::new(
                3,
                vec![Component::new(
                    "z = 0",
                    vec![x(3, 2)],
                    ComponentDimension::Curve,
                )],
                vec![line],
            ),
            Err(LandmarkError::UncertifiedDimension {
                component: "z = 0".into(),
                dimension: ComponentDimension::Curve,
                coordinates: vec![0, 1],
            })
        );
    }

    /// **A curve of `ℚ³` is certified by an eliminant in every pair of coordinates.** The twisted
    /// cubic `t ↦ (t, t², t³)` with the generators `y − x²`, `z − x³` has none in `(y, z)` and is
    /// refused; adding `y³ − z²`, which vanishes on it, certifies its dimension. Then `xz − y²` is
    /// an identity and `y − x` is refused at a point of the cubic.
    #[test]
    fn a_space_curve_is_certified_by_its_eliminants() {
        let (x0, x1, x2) = (x(3, 0), x(3, 1), x(3, 2));
        let square = x0.mul(&x0).unwrap();
        let generators = vec![
            x1.sub(&square).unwrap(),
            x2.sub(&square.mul(&x0).unwrap()).unwrap(),
        ];
        let cubic = || {
            RationalChart::polynomial(
                "(t, t^2, t^3)",
                vec![
                    polynomial(&[0, 1]),
                    polynomial(&[0, 0, 1]),
                    polynomial(&[0, 0, 0, 1]),
                ],
            )
            .unwrap()
        };
        assert_eq!(
            IdentityAtlas::new(
                3,
                vec![Component::new(
                    "cubic",
                    generators.clone(),
                    ComponentDimension::Curve,
                )],
                vec![cubic()],
            ),
            Err(LandmarkError::UncertifiedDimension {
                component: "cubic".into(),
                dimension: ComponentDimension::Curve,
                coordinates: vec![1, 2],
            })
        );
        let eliminant = x1
            .mul(&x1)
            .unwrap()
            .mul(&x1)
            .unwrap()
            .sub(&x2.mul(&x2).unwrap())
            .unwrap();
        let mut certified = generators;
        certified.push(eliminant);
        let atlas = IdentityAtlas::new(
            3,
            vec![Component::new(
                "cubic",
                certified,
                ComponentDimension::Curve,
            )],
            vec![cubic()],
        )
        .unwrap();
        let relation = x0.mul(&x2).unwrap().sub(&x1.mul(&x1).unwrap()).unwrap();
        assert_eq!(atlas.certify(&relation).unwrap(), IdentityVerdict::Identity);
        let IdentityVerdict::Distinguished { point, face, .. } =
            atlas.certify(&x1.sub(&x0).unwrap()).unwrap()
        else {
            panic!("y = x is not an identity of the cubic");
        };
        assert_eq!(point[1], &point[0] * &point[0]);
        assert_eq!(point[2], &point[1] * &point[0]);
        assert!(!face.is_zero());
    }
}
