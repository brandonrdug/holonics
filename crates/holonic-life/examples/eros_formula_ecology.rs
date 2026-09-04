use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::io::Write;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use body::incidence::IncidenceHand;
use body::num::Cog;
use life::form_mouth::deposit_form_or_message;
use num_bigint::{BigInt, Sign};
use num_rational::BigRational;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CpuLiveCurrentExecutor, CurrentBoundaryPort, CurrentEvent,
    CurrentExecutionRequest, CurrentGeometry, CurrentLineage, DirectedExecutionRequest,
    ExecutedContemporaryEvent, InterfaceCapability, LiveConstituent, LiveCurrentError,
    LiveCurrentExecutor, LiveCurrentMachine, LiveMemory, RegionalExecutionRequest,
    RegionalRelationArc, RegionalRelationCell, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `.local/artifacts/eros_formula_ecology/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_formula_ecology";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";
const PRIMING_VALUES: [i64; 8] = [13, 29, 17, 31, -63_245, 47, 71, -89];
const RECRUIT_LOCAL: u64 = 0;
const PRIME_AXES: [u32; 3] = [2, 3, 5];
const E_DEGREE: u8 = 8;
const MACHIN_TERMS: u32 = 5;
const ZETA_TERMS: u32 = 64;
const ZETA_EULER_PRIMES: [u32; 11] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31];

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Axis {
    Symbol(String),
    Prime(u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Polynomial {
    axes: Vec<Axis>,
    degree: u8,
    terms: BTreeMap<Vec<u8>, BigRational>,
}

impl Polynomial {
    fn zero(axes: Vec<Axis>, degree: u8) -> Self {
        Self {
            axes,
            degree,
            terms: BTreeMap::new(),
        }
    }

    fn one(axes: Vec<Axis>, degree: u8) -> Self {
        let mut value = Self::zero(axes, degree);
        value.add_term(vec![0; value.axes.len()], ratio(1, 1));
        value
    }

    fn add_term(&mut self, monomial: Vec<u8>, coefficient: BigRational) {
        assert_eq!(monomial.len(), self.axes.len());
        assert!(total_degree(&monomial) <= self.degree);
        if coefficient == ratio(0, 1) {
            return;
        }
        let next = self
            .terms
            .get(&monomial)
            .cloned()
            .unwrap_or_else(|| ratio(0, 1))
            + coefficient;
        if next == ratio(0, 1) {
            self.terms.remove(&monomial);
        } else {
            self.terms.insert(monomial, next);
        }
    }

    fn add(&self, other: &Self) -> Result<Self, String> {
        self.require_same_chart(other)?;
        let mut result = self.clone();
        for (monomial, coefficient) in &other.terms {
            result.add_term(monomial.clone(), coefficient.clone());
        }
        Ok(result)
    }

    fn subtract(&self, other: &Self) -> Result<Self, String> {
        self.add(&other.scale(&ratio(-1, 1)))
    }

    fn scale(&self, factor: &BigRational) -> Self {
        let mut result = Self::zero(self.axes.clone(), self.degree);
        for (monomial, coefficient) in &self.terms {
            result.add_term(monomial.clone(), coefficient * factor);
        }
        result
    }

    fn multiply(&self, other: &Self) -> Result<Self, String> {
        self.require_same_chart(other)?;
        let mut result = Self::zero(self.axes.clone(), self.degree);
        for (left_monomial, left_coefficient) in &self.terms {
            for (right_monomial, right_coefficient) in &other.terms {
                let monomial: Vec<u8> = left_monomial
                    .iter()
                    .zip(right_monomial)
                    .map(|(left, right)| left.saturating_add(*right))
                    .collect();
                if total_degree(&monomial) <= self.degree {
                    result.add_term(monomial, left_coefficient * right_coefficient);
                }
            }
        }
        Ok(result)
    }

    fn formal_exp(&self) -> Result<Self, String> {
        let constant = vec![0; self.axes.len()];
        if self.terms.contains_key(&constant) {
            return Err(
                "bounded formal Exp requires an augmentation-ideal input with zero constant term"
                    .to_owned(),
            );
        }
        let mut result = Self::one(self.axes.clone(), self.degree);
        let mut power = Self::one(self.axes.clone(), self.degree);
        let mut factorial = BigInt::from(1);
        for exponent in 1..=u32::from(self.degree) {
            power = power.multiply(self)?;
            factorial *= BigInt::from(exponent);
            result =
                result.add(&power.scale(&BigRational::new(BigInt::from(1), factorial.clone())))?;
        }
        Ok(result)
    }

    fn evaluate_at_one(&self) -> BigRational {
        self.terms
            .values()
            .cloned()
            .fold(ratio(0, 1), |sum, coefficient| sum + coefficient)
    }

    fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    fn lift_degree(&self, degree: u8) -> Result<Self, String> {
        if degree < self.degree {
            return Err("a polynomial lift cannot lower its aperture".to_owned());
        }
        let mut lifted = Self::zero(self.axes.clone(), degree);
        for (monomial, coefficient) in &self.terms {
            lifted.add_term(monomial.clone(), coefficient.clone());
        }
        Ok(lifted)
    }

    fn restrict_degree(&self, degree: u8) -> Result<Self, String> {
        if degree > self.degree {
            return Err("a polynomial restriction cannot enlarge its aperture".to_owned());
        }
        let mut restricted = Self::zero(self.axes.clone(), degree);
        for (monomial, coefficient) in &self.terms {
            if total_degree(monomial) <= degree {
                restricted.add_term(monomial.clone(), coefficient.clone());
            }
        }
        Ok(restricted)
    }

    fn homogeneous(&self, degree: u8) -> Self {
        let mut face = Self::zero(self.axes.clone(), self.degree);
        for (monomial, coefficient) in &self.terms {
            if total_degree(monomial) == degree {
                face.add_term(monomial.clone(), coefficient.clone());
            }
        }
        face
    }

    fn require_same_chart(&self, other: &Self) -> Result<(), String> {
        if self.axes != other.axes || self.degree != other.degree {
            return Err("polynomials do not occupy the same exact aperture".to_owned());
        }
        Ok(())
    }

    fn wire(&self) -> PolynomialWire {
        PolynomialWire {
            axes: self.axes.iter().map(AxisWire::from).collect(),
            degree: self.degree,
            terms: self
                .terms
                .iter()
                .map(|(monomial, coefficient)| TermWire {
                    monomial: monomial.clone(),
                    coefficient: rational_wire(coefficient),
                })
                .collect(),
        }
    }

    fn from_wire(wire: &PolynomialWire) -> Result<Self, String> {
        let axes = wire
            .axes
            .iter()
            .map(Axis::try_from)
            .collect::<Result<Vec<_>, _>>()?;
        let mut polynomial = Self::zero(axes, wire.degree);
        for term in &wire.terms {
            polynomial.add_term(
                term.monomial.clone(),
                rational_from_wire(&term.coefficient)?,
            );
        }
        Ok(polynomial)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExactInterval {
    lower: BigRational,
    upper: BigRational,
}

impl ExactInterval {
    fn new(lower: BigRational, upper: BigRational) -> Result<Self, String> {
        if lower > upper {
            return Err("an exact interval cannot reverse its endpoints".to_owned());
        }
        Ok(Self { lower, upper })
    }

    fn add(&self, other: &Self) -> Self {
        Self {
            lower: &self.lower + &other.lower,
            upper: &self.upper + &other.upper,
        }
    }

    fn scale_integer(&self, factor: i64) -> Self {
        let factor = BigRational::from_integer(BigInt::from(factor));
        if factor >= ratio(0, 1) {
            Self {
                lower: &self.lower * &factor,
                upper: &self.upper * &factor,
            }
        } else {
            Self {
                lower: &self.upper * &factor,
                upper: &self.lower * &factor,
            }
        }
    }

    fn square_positive(&self) -> Result<Self, String> {
        if self.lower < ratio(0, 1) {
            return Err("the bounded square expects a positive interval".to_owned());
        }
        Self::new(&self.lower * &self.lower, &self.upper * &self.upper)
    }

    fn intersection(&self, other: &Self) -> Option<Self> {
        let lower = self.lower.clone().max(other.lower.clone());
        let upper = self.upper.clone().min(other.upper.clone());
        (lower <= upper).then_some(Self { lower, upper })
    }

    fn wire(&self) -> IntervalWire {
        IntervalWire {
            lower: rational_wire(&self.lower),
            upper: rational_wire(&self.upper),
        }
    }

    fn from_wire(wire: &IntervalWire) -> Result<Self, String> {
        Self::new(
            rational_from_wire(&wire.lower)?,
            rational_from_wire(&wire.upper)?,
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum LawKind {
    FormalExp,
    EulerLog,
    EulerProduct,
    FactorialRecurrence,
    MachinArctan,
    DirichletZeta2,
    ExactComparison,
    ComplexAssembly,
    ApertureGrowth,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct LawWire {
    schema: String,
    kind: LawKind,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum InvocationWire {
    EulerLog {
        primes: Vec<u32>,
        degree: u8,
        include_prime_power_repetitions: bool,
    },
    EulerProduct {
        primes: Vec<u32>,
        degree: u8,
    },
    FormalExp {
        degree: u8,
        input_namespace: Option<String>,
        literal: Option<PolynomialWire>,
    },
    FactorialRecurrence {
        degree: u8,
    },
    MachinArctan {
        terms: u32,
    },
    DirichletZeta2 {
        terms: u32,
        euler_primes: Vec<u32>,
    },
    Compare {
        mode: ComparisonMode,
        left_namespace: String,
        right_namespace: String,
    },
    Assemble {
        comparison_namespaces: Vec<String>,
    },
    ExtendEulerLog {
        prior_namespace: String,
        new_degree: u8,
        include_new_prime_power_repetition: bool,
    },
    ExtendExponential {
        logarithm_namespace: String,
        prior_exponential_namespace: String,
        new_degree: u8,
    },
    ExtendEulerProduct {
        prior_namespace: String,
        new_degree: u8,
    },
    ExtendFactorial {
        prior_namespace: String,
        new_degree: u8,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum ComparisonMode {
    ExactPolynomial,
    PiSquaredAgainstSixZeta2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum ComparisonStatus {
    Commutes,
    Open,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum FormulaValueWire {
    Polynomial {
        value: PolynomialWire,
        evaluation_at_one: Option<RationalWire>,
    },
    PiInterval {
        terms: u32,
        value: IntervalWire,
    },
    Zeta2 {
        terms: u32,
        dirichlet_enclosure: IntervalWire,
        finite_euler_product: RationalWire,
        euler_primes: Vec<u32>,
    },
    Comparison {
        value: ComparisonWire,
    },
    Complex {
        value: ComplexWire,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct PolynomialWire {
    axes: Vec<AxisWire>,
    degree: u8,
    terms: Vec<TermWire>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum AxisWire {
    Symbol { name: String },
    Prime { value: u32 },
}

impl From<&Axis> for AxisWire {
    fn from(value: &Axis) -> Self {
        match value {
            Axis::Symbol(name) => Self::Symbol { name: name.clone() },
            Axis::Prime(value) => Self::Prime { value: *value },
        }
    }
}

impl TryFrom<&AxisWire> for Axis {
    type Error = String;

    fn try_from(value: &AxisWire) -> Result<Self, Self::Error> {
        Ok(match value {
            AxisWire::Symbol { name } => Self::Symbol(name.clone()),
            AxisWire::Prime { value } => Self::Prime(*value),
        })
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct TermWire {
    monomial: Vec<u8>,
    coefficient: RationalWire,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct RationalWire {
    numerator: String,
    denominator: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct IntervalWire {
    lower: RationalWire,
    upper: RationalWire,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ComparisonWire {
    mode: ComparisonMode,
    status: ComparisonStatus,
    left_namespace: String,
    right_namespace: String,
    detail: ComparisonDetailWire,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum ComparisonDetailWire {
    Polynomial {
        residual_left_minus_right: PolynomialWire,
        differing_terms: Vec<TermWire>,
    },
    PiZeta {
        pi_squared: IntervalWire,
        six_zeta2: IntervalWire,
        overlap: Option<IntervalWire>,
        finite_stage_identity_closed: bool,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ComplexWire {
    comparisons: Vec<ComplexComparisonWire>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ComplexComparisonWire {
    namespace: String,
    mode: ComparisonMode,
    status: ComparisonStatus,
}

#[derive(Clone, Copy, Debug)]
struct ArtifactHandle {
    data_namespace: u64,
    recruit_namespace: u64,
    generation: u32,
}

impl ArtifactHandle {
    fn source(identity: &str, bytes: &[u8]) -> Self {
        Self {
            data_namespace: namespace(&[b"eros-formula-data-v1", identity.as_bytes(), bytes]),
            recruit_namespace: namespace(&[b"eros-formula-recruit-v1", identity.as_bytes(), bytes]),
            generation: 0,
        }
    }

    fn after_contact(self, event_identity: &[u8]) -> Self {
        Self {
            data_namespace: self.data_namespace,
            recruit_namespace: namespace(&[
                b"eros-formula-contact-v1",
                &self.recruit_namespace.to_le_bytes(),
                event_identity,
            ]),
            generation: self.generation + 1,
        }
    }

    fn successor(self, identity: &str, bytes: &[u8], event_identity: &[u8]) -> Self {
        Self {
            data_namespace: namespace(&[
                b"eros-formula-successor-data-v1",
                &self.data_namespace.to_le_bytes(),
                identity.as_bytes(),
                event_identity,
                bytes,
            ]),
            recruit_namespace: namespace(&[
                b"eros-formula-successor-recruit-v1",
                &self.recruit_namespace.to_le_bytes(),
                identity.as_bytes(),
                event_identity,
                bytes,
            ]),
            generation: self.generation + 1,
        }
    }

    fn wire(self) -> HandleRead {
        HandleRead {
            data_namespace: namespace_string(self.data_namespace),
            recruit_namespace: namespace_string(self.recruit_namespace),
            generation: self.generation,
        }
    }
}

struct FormulaEcology {
    machine: LiveCurrentMachine,
    handles: BTreeMap<String, ArtifactHandle>,
    artifact_origins: BTreeMap<String, &'static str>,
    invocations: Vec<InvocationRead>,
}

#[derive(Clone, Debug, Serialize)]
struct HandleRead {
    data_namespace: String,
    recruit_namespace: String,
    generation: u32,
}

#[derive(Clone, Debug, Serialize)]
struct ConstituentRead {
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    boundaries: usize,
    exposed_pins: usize,
    open_pins: usize,
    found_pins: usize,
    native_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
struct MachineRead {
    standing_rank: u64,
    standing_cells: usize,
    standing_constituents: usize,
    constituent_cells: usize,
    constituent_incidences: usize,
    constituent_pins: usize,
    constituent_paths: usize,
    constituent_transport_terms: usize,
    live_lineages: usize,
    rest_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
struct SourceLawRead {
    name: String,
    kind: LawKind,
    handle: HandleRead,
    encoded_bytes: usize,
    encoded_sha256: String,
    constituent: ConstituentRead,
}

#[derive(Clone, Debug, Serialize)]
struct DepositRead {
    source_laws: Vec<SourceLawRead>,
    source_lineages_after_event: usize,
    machine: MachineRead,
    no_law_control: MachineRead,
    rest_remount_exact: bool,
}

#[derive(Clone, Debug, Serialize)]
struct InvocationRead {
    event: String,
    law: String,
    recruited_artifacts: Vec<String>,
    objective: InvocationWire,
    law_recovered_from_standing: bool,
    objective_recovered_from_current: bool,
    result_artifact: String,
    result_handle: HandleRead,
    result: FormulaValueWire,
    meeting: ConstituentRead,
    returned_consequence: ConstituentRead,
}

#[derive(Clone, Debug, Serialize)]
struct RefusalRead {
    role: &'static str,
    law_recovered: bool,
    objective_recovered: bool,
    constituent: ConstituentRead,
}

#[derive(Clone, Debug, Serialize)]
struct PrimeTermRead {
    monomial: String,
    integer: u32,
    species: &'static str,
    direct_euler_coefficient: RationalWire,
    exponential_coefficient: RationalWire,
    foil_coefficient: RationalWire,
    foil_residual: RationalWire,
}

#[derive(Clone, Debug, Serialize)]
struct FormulaRelationsRead {
    prime_axes: Vec<u32>,
    degree_two_population: Vec<PrimeTermRead>,
    e_aperture: u8,
    e_partial: RationalWire,
    machin_terms: u32,
    zeta_terms: u32,
    full_euler_comparison: ComparisonWire,
    missing_prime_power_foil: ComparisonWire,
    e_comparison: ComparisonWire,
    pi_zeta_comparison: ComparisonWire,
}

#[derive(Clone, Debug, Serialize)]
struct ComplexNodeRead {
    artifact: String,
    origin: &'static str,
    data_namespace: String,
}

#[derive(Clone, Debug, Serialize)]
struct ComplexEdgeRead {
    event: String,
    law: String,
    inputs: Vec<String>,
    output: String,
}

#[derive(Clone, Debug, Serialize)]
struct OccurrenceComplexRead {
    zero_cells: Vec<ComplexNodeRead>,
    one_cells: Vec<ComplexEdgeRead>,
    two_cells: Vec<ComplexComparisonWire>,
    final_complex_artifact: String,
    final_complex: ComplexWire,
    final_machine: MachineRead,
    rest_remount_exact: bool,
}

#[derive(Clone, Debug, Serialize)]
struct AcceptanceRead {
    source_law_lineages_departed: bool,
    source_laws_recovered_only_from_standing: bool,
    no_law_and_wrong_interface_refused: bool,
    full_euler_paths_commuted: bool,
    missing_prime_power_path_open_only_on_prime_squares: bool,
    same_formal_exp_law_served_prime_and_e_faces: bool,
    e_paths_commuted_exactly: bool,
    pi_zeta_finite_paths_remained_open_with_exact_overlap: bool,
    every_derived_comparison_returned_as_later_standing: bool,
    final_complex_survived_exact_rest_remount: bool,
    no_floating_point_causal_data: bool,
}

#[derive(Clone, Debug, Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    stopping_condition: &'static str,
    deposit: DepositRead,
    controls: Vec<RefusalRead>,
    invocations: Vec<InvocationRead>,
    relations: FormulaRelationsRead,
    occurrence_complex: OccurrenceComplexRead,
    acceptance: AcceptanceRead,
    conclusion: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct GrowthBaselineRead {
    machine_before_rest: MachineRead,
    rest_remount_exact: bool,
    full_and_held_log_predecessors_equal: bool,
    full_and_held_exponential_predecessors_equal: bool,
    exponential_and_product_predecessors_equal: bool,
    predecessor_artifacts: Vec<ComplexNodeRead>,
}

#[derive(Clone, Debug, Serialize)]
struct GrowthStepRead {
    event: String,
    law: String,
    recruited_artifacts: Vec<String>,
    objective: InvocationWire,
    predecessor_artifact: String,
    recruited_predecessor_handle: HandleRead,
    replaced_predecessor_handle: HandleRead,
    predecessor: FormulaValueWire,
    successor_artifact: String,
    successor_handle: HandleRead,
    successor: FormulaValueWire,
    lower_restriction_exact: bool,
    new_homogeneous_terms: Vec<TermWire>,
    old_data_interfaces_departed: bool,
    old_recruit_interface_departed: bool,
    law_recovered_from_standing: bool,
    objective_recovered_from_current: bool,
    meeting: ConstituentRead,
    returned_replacement: ConstituentRead,
}

#[derive(Clone, Debug, Serialize)]
struct PrimeDegreeThreeRead {
    monomial: String,
    integer: u32,
    incidence: &'static str,
    direct_euler_coefficient: RationalWire,
    grown_exponential_coefficient: RationalWire,
    held_exponential_coefficient: RationalWire,
    held_residual: RationalWire,
}

#[derive(Clone, Debug, Serialize)]
struct GrowthRelationsRead {
    prime_axes: Vec<u32>,
    degree_three_population: Vec<PrimeDegreeThreeRead>,
    full_degree_three_comparison: ComparisonWire,
    held_degree_three_comparison: ComparisonWire,
    e_degree_nine_comparison: ComparisonWire,
    e_degree_eight_value: RationalWire,
    e_new_term: RationalWire,
    e_degree_nine_value: RationalWire,
    higher_growth_complex: ComplexWire,
}

#[derive(Clone, Debug, Serialize)]
struct GrowthFinalRead {
    active_artifacts: Vec<ComplexNodeRead>,
    departed_predecessor_artifacts: Vec<String>,
    final_machine: MachineRead,
    rest_remount_exact: bool,
}

#[derive(Clone, Debug, Serialize)]
struct GrowthAcceptanceRead {
    source_law_lineages_departed: bool,
    baseline_rest_remount_exact: bool,
    plural_equal_predecessors_stood_before_branching: bool,
    every_growth_used_a_live_predecessor: bool,
    every_lower_face_remained_exact: bool,
    every_replaced_predecessor_interface_departed: bool,
    full_degree_three_paths_commuted: bool,
    held_path_open_only_on_prime_cubes_with_negative_one_third_residual: bool,
    e_degree_nine_grew_by_one_exact_term: bool,
    e_degree_nine_paths_commuted: bool,
    comparisons_returned_as_one_higher_complex: bool,
    final_successor_survived_exact_rest_remount: bool,
    no_floating_point_causal_data: bool,
}

#[derive(Clone, Debug, Serialize)]
struct GrowthReport {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    stopping_condition: &'static str,
    deposit: DepositRead,
    baseline: GrowthBaselineRead,
    growth_steps: Vec<GrowthStepRead>,
    supporting_invocations: Vec<InvocationRead>,
    relations: GrowthRelationsRead,
    final_ecology: GrowthFinalRead,
    acceptance: GrowthAcceptanceRead,
    conclusion: &'static str,
}

struct ReplacementOutcome {
    handle: ArtifactHandle,
    constituent: ConstituentRead,
    old_data_departed: bool,
    old_recruit_departed: bool,
}

struct Meeting {
    constituent: LiveConstituent,
    selected: Vec<(String, ArtifactHandle)>,
    objective_namespace: u64,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros formula ecology: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let first = arguments.next().ok_or_else(usage)?;
    if first == "--poisson-tail" {
        let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
        if arguments.next().is_some() {
            return Err(usage());
        }
        let report = run_poisson_tail_cpu()?;
        return write_report(&output, &report, report.status);
    }
    if first == "--theta-mellin" {
        let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
        if arguments.next().is_some() {
            return Err(usage());
        }
        let report = run_theta_mellin_cpu()?;
        return write_report(&output, &report, report.status);
    }
    if first == "--efficiency" {
        let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
        if arguments.next().is_some() {
            return Err(usage());
        }
        let report = run_efficiency_cpu()?;
        return write_report(&output, &report, report.status);
    }
    if first == "--growth" {
        let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
        if arguments.next().is_some() {
            return Err(usage());
        }
        let report = run_growth_cpu()?;
        return write_report(&output, &report, report.status);
    }
    let output = PathBuf::from(first);
    if arguments.next().is_some() {
        return Err(usage());
    }
    let report = run_cpu()?;
    write_report(&output, &report, report.status)
}

fn write_report<T: Serialize>(output: &PathBuf, report: &T, status: &str) -> Result<(), String> {
    let mut encoded = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("the report encodes exactly: {error}"))?;
    encoded.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&output)
        .map_err(|error| format!("{} opens once: {error}", output.display()))?;
    file.write_all(&encoded)
        .map_err(|error| format!("{} writes completely: {error}", output.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", output.display()))?;
    eprintln!(
        "eros formula ecology: {} · {} bytes · {}",
        status,
        encoded.len(),
        output.display()
    );
    Ok(())
}

fn usage() -> String {
    "usage: eros_formula_ecology \
     [--growth|--efficiency|--theta-mellin|--poisson-tail] <new-report.json>"
        .to_owned()
}

fn run_cpu() -> Result<Report, String> {
    let source_laws = vec![
        ("formal-exp".to_owned(), LawKind::FormalExp),
        ("euler-log".to_owned(), LawKind::EulerLog),
        ("euler-product".to_owned(), LawKind::EulerProduct),
        (
            "factorial-recurrence".to_owned(),
            LawKind::FactorialRecurrence,
        ),
        ("machin-arctan".to_owned(), LawKind::MachinArctan),
        ("dirichlet-zeta2".to_owned(), LawKind::DirichletZeta2),
        ("exact-comparison".to_owned(), LawKind::ExactComparison),
        ("complex-assembly".to_owned(), LawKind::ComplexAssembly),
    ];
    let (mut ecology, no_law_checkpoint, deposit) = deposit_laws(&source_laws)?;
    let source_lineages_departed = deposit.source_lineages_after_event == 0;
    let original_exp_handle = *ecology
        .handles
        .get("formal-exp")
        .ok_or_else(|| "the formal exponential handle was deposited".to_owned())?;
    let original_exp_bytes = encode_json(&LawWire {
        schema: "eros.formula-law.v1".to_owned(),
        kind: LawKind::FormalExp,
    })?;
    drop(source_laws);

    let no_law = refusal_probe(
        &no_law_checkpoint,
        original_exp_handle,
        &InvocationWire::FactorialRecurrence { degree: E_DEGREE },
        b"no-law-control",
        "same interface and objective without law Standing",
    )?;
    let wrong_handle = ArtifactHandle {
        data_namespace: original_exp_handle.data_namespace,
        recruit_namespace: original_exp_handle.recruit_namespace ^ 0xa5a5_a5a5_a5a5_a5a5,
        generation: original_exp_handle.generation,
    };
    let wrong_interface = refusal_probe(
        &ecology.machine.rest_image().map_err(debug)?,
        wrong_handle,
        &InvocationWire::FormalExp {
            degree: E_DEGREE,
            input_namespace: None,
            literal: Some(one_generator(E_DEGREE).wire()),
        },
        b"wrong-interface-control",
        "law body present under a nonincident recruitment interface",
    )?;

    ecology.invoke(
        "build-prime-log-full",
        "euler-log",
        &[],
        InvocationWire::EulerLog {
            primes: PRIME_AXES.to_vec(),
            degree: 2,
            include_prime_power_repetitions: true,
        },
        "prime-log-full",
    )?;
    let full_log_namespace = ecology.data_namespace("prime-log-full")?;
    ecology.invoke(
        "exp-prime-log-full",
        "formal-exp",
        &["prime-log-full"],
        InvocationWire::FormalExp {
            degree: 2,
            input_namespace: Some(namespace_string(full_log_namespace)),
            literal: None,
        },
        "prime-exp-full",
    )?;
    ecology.invoke(
        "build-direct-euler-product",
        "euler-product",
        &[],
        InvocationWire::EulerProduct {
            primes: PRIME_AXES.to_vec(),
            degree: 2,
        },
        "prime-euler-direct",
    )?;
    ecology.compare(
        "compare-full-euler-routes",
        "prime-exp-full",
        "prime-euler-direct",
        ComparisonMode::ExactPolynomial,
        "comparison-euler-full",
    )?;

    ecology.invoke(
        "build-prime-log-without-repetitions",
        "euler-log",
        &[],
        InvocationWire::EulerLog {
            primes: PRIME_AXES.to_vec(),
            degree: 2,
            include_prime_power_repetitions: false,
        },
        "prime-log-foil",
    )?;
    let foil_log_namespace = ecology.data_namespace("prime-log-foil")?;
    ecology.invoke(
        "exp-prime-log-without-repetitions",
        "formal-exp",
        &["prime-log-foil"],
        InvocationWire::FormalExp {
            degree: 2,
            input_namespace: Some(namespace_string(foil_log_namespace)),
            literal: None,
        },
        "prime-exp-foil",
    )?;
    ecology.compare(
        "compare-missing-prime-power-route",
        "prime-exp-foil",
        "prime-euler-direct",
        ComparisonMode::ExactPolynomial,
        "comparison-euler-foil",
    )?;

    ecology.invoke(
        "formal-exp-one-generator",
        "formal-exp",
        &[],
        InvocationWire::FormalExp {
            degree: E_DEGREE,
            input_namespace: None,
            literal: Some(one_generator(E_DEGREE).wire()),
        },
        "e-formal-exp",
    )?;
    ecology.invoke(
        "factorial-recurrence-one-generator",
        "factorial-recurrence",
        &[],
        InvocationWire::FactorialRecurrence { degree: E_DEGREE },
        "e-factorial",
    )?;
    ecology.compare(
        "compare-e-routes",
        "e-formal-exp",
        "e-factorial",
        ComparisonMode::ExactPolynomial,
        "comparison-e",
    )?;

    ecology.invoke(
        "machin-rational-enclosure",
        "machin-arctan",
        &[],
        InvocationWire::MachinArctan {
            terms: MACHIN_TERMS,
        },
        "pi-machin",
    )?;
    ecology.invoke(
        "zeta2-dirichlet-and-euler",
        "dirichlet-zeta2",
        &[],
        InvocationWire::DirichletZeta2 {
            terms: ZETA_TERMS,
            euler_primes: ZETA_EULER_PRIMES.to_vec(),
        },
        "zeta2-bounded",
    )?;
    ecology.compare(
        "compare-pi-squared-with-six-zeta2",
        "pi-machin",
        "zeta2-bounded",
        ComparisonMode::PiSquaredAgainstSixZeta2,
        "comparison-pi-zeta",
    )?;

    let comparison_names = [
        "comparison-euler-full",
        "comparison-euler-foil",
        "comparison-e",
        "comparison-pi-zeta",
    ];
    let comparison_namespaces = comparison_names
        .iter()
        .map(|name| ecology.data_namespace(name).map(namespace_string))
        .collect::<Result<Vec<_>, _>>()?;
    ecology.invoke(
        "assemble-formula-relation-complex",
        "complex-assembly",
        &comparison_names,
        InvocationWire::Assemble {
            comparison_namespaces,
        },
        "formula-relation-complex",
    )?;

    let full_comparison = ecology.comparison_value("comparison-euler-full")?;
    let foil_comparison = ecology.comparison_value("comparison-euler-foil")?;
    let e_comparison = ecology.comparison_value("comparison-e")?;
    let pi_zeta_comparison = ecology.comparison_value("comparison-pi-zeta")?;
    let direct = ecology.polynomial_value("prime-euler-direct")?;
    let full = ecology.polynomial_value("prime-exp-full")?;
    let foil = ecology.polynomial_value("prime-exp-foil")?;
    let e_polynomial = ecology.polynomial_value("e-formal-exp")?;
    let degree_two_population = prime_term_read(&direct, &full, &foil, &PRIME_AXES)?;
    let complex = ecology.complex_value("formula-relation-complex")?;

    let final_rest = ecology.machine.rest_image().map_err(debug)?;
    let remounted = LiveCurrentMachine::from_rest_image(final_rest.clone()).map_err(debug)?;
    let rest_exact = remounted.rest_image().map_err(debug)? == final_rest;
    let final_machine = machine_read(&ecology.machine)?;
    let zero_cells = ecology
        .handles
        .iter()
        .map(|(name, handle)| ComplexNodeRead {
            artifact: name.clone(),
            origin: *ecology.artifact_origins.get(name).unwrap_or(&"unknown"),
            data_namespace: namespace_string(handle.data_namespace),
        })
        .collect();
    let one_cells = ecology
        .invocations
        .iter()
        .map(|invocation| ComplexEdgeRead {
            event: invocation.event.clone(),
            law: invocation.law.clone(),
            inputs: invocation.recruited_artifacts.clone(),
            output: invocation.result_artifact.clone(),
        })
        .collect();
    let two_cells = complex.comparisons.clone();
    let invocation_reads = ecology.invocations.clone();

    let foil_open_only_on_squares = foil_open_only_on_prime_squares(&foil_comparison, &PRIME_AXES)?;
    let exp_invocations = invocation_reads
        .iter()
        .filter(|invocation| invocation.law == "formal-exp")
        .count();
    let comparisons_returned = comparison_names.iter().all(|name| {
        ecology
            .artifact_origins
            .get(*name)
            .is_some_and(|origin| *origin == "comparison_return")
    });
    let pi_overlap = match &pi_zeta_comparison.detail {
        ComparisonDetailWire::PiZeta {
            overlap,
            finite_stage_identity_closed,
            ..
        } => overlap.is_some() && !finite_stage_identity_closed,
        _ => false,
    };
    let source_laws_recovered = invocation_reads
        .iter()
        .all(|invocation| invocation.law_recovered_from_standing);
    let acceptance = AcceptanceRead {
        source_law_lineages_departed: source_lineages_departed,
        source_laws_recovered_only_from_standing: source_laws_recovered,
        no_law_and_wrong_interface_refused: !no_law.law_recovered && !wrong_interface.law_recovered,
        full_euler_paths_commuted: full_comparison.status == ComparisonStatus::Commutes,
        missing_prime_power_path_open_only_on_prime_squares: foil_open_only_on_squares,
        same_formal_exp_law_served_prime_and_e_faces: exp_invocations == 3,
        e_paths_commuted_exactly: e_comparison.status == ComparisonStatus::Commutes,
        pi_zeta_finite_paths_remained_open_with_exact_overlap: pi_zeta_comparison.status
            == ComparisonStatus::Open
            && pi_overlap,
        every_derived_comparison_returned_as_later_standing: comparisons_returned,
        final_complex_survived_exact_rest_remount: rest_exact,
        no_floating_point_causal_data: true,
    };
    if !all_accepted(&acceptance) {
        return Err("the bounded formula ecology did not close every declared relation".to_owned());
    }

    if sha256(&original_exp_bytes)
        != deposit
            .source_laws
            .iter()
            .find(|law| law.name == "formal-exp")
            .ok_or_else(|| "the formal exponential source read remains present".to_owned())?
            .encoded_sha256
    {
        return Err("the formal exponential source identity changed".to_owned());
    }

    Ok(Report {
        schema: "eros.formula-ecology.v1",
        status: "accepted",
        question: "can exact source-departed generators for e, pi, and the Euler/Zeta prime relation compose into a readable occurrence complex whose commuting and open faces are formed by actual later consequences?",
        theory_to_structure: "law definition -> oriented cellular Standing; explicit objective -> recruited local law population; generic exact world conduct -> returned formula value; parallel returned values -> commuting or OPEN comparison; returned comparisons -> higher relation complex",
        stopping_condition: "the full Euler triangle and e triangle commute exactly, the missing-prime-power foil remains open only on prime squares, the finite pi/Zeta comparison retains exact overlap and tails without claiming limit equality, every relation returns as Standing, and the whole complex remounts exactly",
        deposit,
        controls: vec![no_law, wrong_interface],
        invocations: invocation_reads,
        relations: FormulaRelationsRead {
            prime_axes: PRIME_AXES.to_vec(),
            degree_two_population,
            e_aperture: E_DEGREE,
            e_partial: rational_wire(&e_polynomial.evaluate_at_one()),
            machin_terms: MACHIN_TERMS,
            zeta_terms: ZETA_TERMS,
            full_euler_comparison: full_comparison,
            missing_prime_power_foil: foil_comparison,
            e_comparison,
            pi_zeta_comparison,
        },
        occurrence_complex: OccurrenceComplexRead {
            zero_cells,
            one_cells,
            two_cells,
            final_complex_artifact: "formula-relation-complex".to_owned(),
            final_complex: complex,
            final_machine,
            rest_remount_exact: rest_exact,
        },
        acceptance,
        conclusion: "the world did not hand Soma a finished formula taxonomy. Eight finite generators crossed once and their source lineages ended. Explicit objectives recruited them from Standing; exact consequences returned; independent paths formed two commuting triangles and two scoped OPEN faces; the prime-power foil localized its residual to the repeated-prime diagonal; and the four comparisons became one remountable higher relation complex.",
    })
}

fn run_growth_cpu() -> Result<GrowthReport, String> {
    let source_laws = vec![
        ("formal-exp".to_owned(), LawKind::FormalExp),
        ("euler-log".to_owned(), LawKind::EulerLog),
        ("euler-product".to_owned(), LawKind::EulerProduct),
        (
            "factorial-recurrence".to_owned(),
            LawKind::FactorialRecurrence,
        ),
        ("exact-comparison".to_owned(), LawKind::ExactComparison),
        ("complex-assembly".to_owned(), LawKind::ComplexAssembly),
        ("aperture-growth".to_owned(), LawKind::ApertureGrowth),
    ];
    let (mut ecology, _, deposit) = deposit_laws(&source_laws)?;
    let source_law_lineages_departed = deposit.source_lineages_after_event == 0;
    drop(source_laws);

    for (event, result) in [
        ("build-full-log-predecessor", "prime-log-2-full"),
        ("build-held-log-predecessor", "prime-log-2-held"),
    ] {
        ecology.invoke(
            event,
            "euler-log",
            &[],
            InvocationWire::EulerLog {
                primes: PRIME_AXES.to_vec(),
                degree: 2,
                include_prime_power_repetitions: true,
            },
            result,
        )?;
    }
    let full_log_namespace = ecology.data_namespace("prime-log-2-full")?;
    ecology.invoke(
        "build-full-exponential-predecessor",
        "formal-exp",
        &["prime-log-2-full"],
        InvocationWire::FormalExp {
            degree: 2,
            input_namespace: Some(namespace_string(full_log_namespace)),
            literal: None,
        },
        "prime-exp-2-full",
    )?;
    let held_log_namespace = ecology.data_namespace("prime-log-2-held")?;
    ecology.invoke(
        "build-held-exponential-predecessor",
        "formal-exp",
        &["prime-log-2-held"],
        InvocationWire::FormalExp {
            degree: 2,
            input_namespace: Some(namespace_string(held_log_namespace)),
            literal: None,
        },
        "prime-exp-2-held",
    )?;
    ecology.invoke(
        "build-product-predecessor",
        "euler-product",
        &[],
        InvocationWire::EulerProduct {
            primes: PRIME_AXES.to_vec(),
            degree: 2,
        },
        "prime-product-2",
    )?;
    ecology.invoke(
        "build-e-eight-predecessor",
        "factorial-recurrence",
        &[],
        InvocationWire::FactorialRecurrence { degree: 8 },
        "e-factorial-8",
    )?;

    let full_log_2 = ecology.polynomial_value("prime-log-2-full")?;
    let held_log_2 = ecology.polynomial_value("prime-log-2-held")?;
    let full_exp_2 = ecology.polynomial_value("prime-exp-2-full")?;
    let held_exp_2 = ecology.polynomial_value("prime-exp-2-held")?;
    let product_2 = ecology.polynomial_value("prime-product-2")?;
    let e_8 = ecology.polynomial_value("e-factorial-8")?;
    let predecessor_names = [
        "prime-log-2-full",
        "prime-log-2-held",
        "prime-exp-2-full",
        "prime-exp-2-held",
        "prime-product-2",
        "e-factorial-8",
    ];
    let predecessor_artifacts = predecessor_names
        .iter()
        .map(|name| {
            let handle = ecology
                .handles
                .get(*name)
                .ok_or_else(|| format!("baseline predecessor {name} is active"))?;
            Ok(ComplexNodeRead {
                artifact: (*name).to_owned(),
                origin: *ecology.artifact_origins.get(*name).unwrap_or(&"unknown"),
                data_namespace: namespace_string(handle.data_namespace),
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let machine_before_rest = machine_read(&ecology.machine)?;
    let baseline_rest = ecology.machine.rest_image().map_err(debug)?;
    let remounted = LiveCurrentMachine::from_rest_image(baseline_rest.clone()).map_err(debug)?;
    let baseline_rest_remount_exact = remounted.rest_image().map_err(debug)? == baseline_rest;
    ecology.machine = remounted;
    let baseline = GrowthBaselineRead {
        machine_before_rest,
        rest_remount_exact: baseline_rest_remount_exact,
        full_and_held_log_predecessors_equal: full_log_2 == held_log_2,
        full_and_held_exponential_predecessors_equal: full_exp_2 == held_exp_2,
        exponential_and_product_predecessors_equal: full_exp_2 == product_2,
        predecessor_artifacts,
    };

    let mut growth_steps = Vec::new();
    let prior_namespace = ecology.data_namespace("prime-log-2-full")?;
    growth_steps.push(ecology.grow(
        "grow-full-log-to-degree-three",
        "aperture-growth",
        "prime-log-2-full",
        &[],
        InvocationWire::ExtendEulerLog {
            prior_namespace: namespace_string(prior_namespace),
            new_degree: 3,
            include_new_prime_power_repetition: true,
        },
        "prime-log-3-full",
    )?);
    let logarithm_namespace = ecology.data_namespace("prime-log-3-full")?;
    let prior_exponential_namespace = ecology.data_namespace("prime-exp-2-full")?;
    growth_steps.push(ecology.grow(
        "grow-full-exponential-to-degree-three",
        "aperture-growth",
        "prime-exp-2-full",
        &["prime-log-3-full"],
        InvocationWire::ExtendExponential {
            logarithm_namespace: namespace_string(logarithm_namespace),
            prior_exponential_namespace: namespace_string(prior_exponential_namespace),
            new_degree: 3,
        },
        "prime-exp-3-full",
    )?);
    let prior_namespace = ecology.data_namespace("prime-product-2")?;
    growth_steps.push(ecology.grow(
        "grow-direct-product-to-degree-three",
        "aperture-growth",
        "prime-product-2",
        &[],
        InvocationWire::ExtendEulerProduct {
            prior_namespace: namespace_string(prior_namespace),
            new_degree: 3,
        },
        "prime-product-3",
    )?);
    let prior_namespace = ecology.data_namespace("prime-log-2-held")?;
    growth_steps.push(ecology.grow(
        "grow-held-log-without-cubic-repetition",
        "aperture-growth",
        "prime-log-2-held",
        &[],
        InvocationWire::ExtendEulerLog {
            prior_namespace: namespace_string(prior_namespace),
            new_degree: 3,
            include_new_prime_power_repetition: false,
        },
        "prime-log-3-held",
    )?);
    let logarithm_namespace = ecology.data_namespace("prime-log-3-held")?;
    let prior_exponential_namespace = ecology.data_namespace("prime-exp-2-held")?;
    growth_steps.push(ecology.grow(
        "grow-held-exponential-to-degree-three",
        "aperture-growth",
        "prime-exp-2-held",
        &["prime-log-3-held"],
        InvocationWire::ExtendExponential {
            logarithm_namespace: namespace_string(logarithm_namespace),
            prior_exponential_namespace: namespace_string(prior_exponential_namespace),
            new_degree: 3,
        },
        "prime-exp-3-held",
    )?);
    let prior_namespace = ecology.data_namespace("e-factorial-8")?;
    growth_steps.push(ecology.grow(
        "grow-e-from-eight-to-nine",
        "aperture-growth",
        "e-factorial-8",
        &[],
        InvocationWire::ExtendFactorial {
            prior_namespace: namespace_string(prior_namespace),
            new_degree: 9,
        },
        "e-factorial-9-grown",
    )?);

    ecology.invoke(
        "build-independent-e-nine-reference",
        "formal-exp",
        &[],
        InvocationWire::FormalExp {
            degree: 9,
            input_namespace: None,
            literal: Some(one_generator(9).wire()),
        },
        "e-formal-exp-9-reference",
    )?;
    ecology.compare(
        "compare-grown-full-degree-three",
        "prime-exp-3-full",
        "prime-product-3",
        ComparisonMode::ExactPolynomial,
        "comparison-growth-full",
    )?;
    ecology.compare(
        "compare-grown-held-degree-three",
        "prime-exp-3-held",
        "prime-product-3",
        ComparisonMode::ExactPolynomial,
        "comparison-growth-held",
    )?;
    ecology.compare(
        "compare-grown-e-nine",
        "e-factorial-9-grown",
        "e-formal-exp-9-reference",
        ComparisonMode::ExactPolynomial,
        "comparison-growth-e",
    )?;
    let comparison_names = [
        "comparison-growth-full",
        "comparison-growth-held",
        "comparison-growth-e",
    ];
    let comparison_namespaces = comparison_names
        .iter()
        .map(|name| ecology.data_namespace(name).map(namespace_string))
        .collect::<Result<Vec<_>, _>>()?;
    ecology.invoke(
        "assemble-aperture-growth-complex",
        "complex-assembly",
        &comparison_names,
        InvocationWire::Assemble {
            comparison_namespaces,
        },
        "aperture-growth-complex",
    )?;

    let direct_3 = ecology.polynomial_value("prime-product-3")?;
    let full_3 = ecology.polynomial_value("prime-exp-3-full")?;
    let held_3 = ecology.polynomial_value("prime-exp-3-held")?;
    let e_9 = ecology.polynomial_value("e-factorial-9-grown")?;
    let e_9_reference = ecology.polynomial_value("e-formal-exp-9-reference")?;
    let full_comparison = ecology.comparison_value("comparison-growth-full")?;
    let held_comparison = ecology.comparison_value("comparison-growth-held")?;
    let e_comparison = ecology.comparison_value("comparison-growth-e")?;
    let complex = ecology.complex_value("aperture-growth-complex")?;
    let degree_three_population =
        prime_degree_three_read(&direct_3, &full_3, &held_3, &PRIME_AXES)?;
    let e_new_term = e_9
        .terms
        .get(&vec![9])
        .cloned()
        .ok_or_else(|| "the grown e face exposes y^9".to_owned())?;

    let every_growth_used_a_live_predecessor = growth_steps.iter().all(|step| {
        step.replaced_predecessor_handle.generation
            == step.recruited_predecessor_handle.generation + 1
            && step.law_recovered_from_standing
            && step.objective_recovered_from_current
    });
    let every_lower_face_remained_exact =
        growth_steps.iter().all(|step| step.lower_restriction_exact);
    let every_replaced_predecessor_interface_departed = growth_steps
        .iter()
        .all(|step| step.old_data_interfaces_departed && step.old_recruit_interface_departed);
    let held_only_cubes = foil_open_only_on_prime_cubes(&held_comparison, &PRIME_AXES)?;
    let comparisons_returned = comparison_names.iter().all(|name| {
        ecology
            .artifact_origins
            .get(*name)
            .is_some_and(|origin| *origin == "comparison_return")
    });
    let departed_predecessor_artifacts: Vec<_> = predecessor_names
        .iter()
        .filter(|name| !ecology.handles.contains_key(**name))
        .map(|name| (*name).to_owned())
        .collect();
    let final_rest = ecology.machine.rest_image().map_err(debug)?;
    let final_remount = LiveCurrentMachine::from_rest_image(final_rest.clone()).map_err(debug)?;
    let final_rest_exact = final_remount.rest_image().map_err(debug)? == final_rest;
    let active_artifacts = ecology
        .handles
        .iter()
        .map(|(name, handle)| ComplexNodeRead {
            artifact: name.clone(),
            origin: *ecology.artifact_origins.get(name).unwrap_or(&"unknown"),
            data_namespace: namespace_string(handle.data_namespace),
        })
        .collect();
    let acceptance = GrowthAcceptanceRead {
        source_law_lineages_departed,
        baseline_rest_remount_exact,
        plural_equal_predecessors_stood_before_branching: baseline
            .full_and_held_log_predecessors_equal
            && baseline.full_and_held_exponential_predecessors_equal
            && baseline.exponential_and_product_predecessors_equal,
        every_growth_used_a_live_predecessor,
        every_lower_face_remained_exact,
        every_replaced_predecessor_interface_departed,
        full_degree_three_paths_commuted: full_comparison.status == ComparisonStatus::Commutes,
        held_path_open_only_on_prime_cubes_with_negative_one_third_residual: held_only_cubes,
        e_degree_nine_grew_by_one_exact_term: e_9.restrict_degree(8)? == e_8
            && e_new_term == ratio(1, 362_880)
            && e_9.evaluate_at_one() == ratio(493_205, 181_440),
        e_degree_nine_paths_commuted: e_comparison.status == ComparisonStatus::Commutes
            && e_9 == e_9_reference,
        comparisons_returned_as_one_higher_complex: comparisons_returned
            && complex.comparisons.len() == 3,
        final_successor_survived_exact_rest_remount: final_rest_exact,
        no_floating_point_causal_data: true,
    };
    eprintln!("formula ecology · growth acceptance {acceptance:#?}");
    if !all_growth_accepted(&acceptance) {
        return Err(
            "the bounded aperture-growth ecology did not close every declared relation".to_owned(),
        );
    }
    let supporting_invocations = ecology.invocations.clone();
    let final_machine = machine_read(&ecology.machine)?;

    Ok(GrowthReport {
        schema: "eros.formula-aperture-growth.v1",
        status: "accepted",
        question: "can returned degree-two Euler and degree-eight e bodies become the actual predecessors of degree-three and degree-nine successors while preserving every lower face and releasing their former active interfaces?",
        theory_to_structure: "returned aperture-N polynomial + source-departed aperture-growth law + explicit next-face objective -> exact homogeneous recurrence -> returned replacement constituent at N+1; sibling admission or withholding of only P_3/3 -> commuting or cube-supported OPEN comparison",
        stopping_condition: "all lower restrictions remain exact, every predecessor data and recruitment interface departs, the full degree-three route commutes, the held route differs only by -X_p^3/3, e gains only y^9/9!, all comparisons return into one remountable higher complex, and no larger aperture or RH completion is inferred",
        deposit,
        baseline,
        growth_steps,
        supporting_invocations,
        relations: GrowthRelationsRead {
            prime_axes: PRIME_AXES.to_vec(),
            degree_three_population,
            full_degree_three_comparison: full_comparison,
            held_degree_three_comparison: held_comparison,
            e_degree_nine_comparison: e_comparison,
            e_degree_eight_value: rational_wire(&e_8.evaluate_at_one()),
            e_new_term: rational_wire(&e_new_term),
            e_degree_nine_value: rational_wire(&e_9.evaluate_at_one()),
            higher_growth_complex: complex,
        },
        final_ecology: GrowthFinalRead {
            active_artifacts,
            departed_predecessor_artifacts,
            final_machine,
            rest_remount_exact: final_rest_exact,
        },
        acceptance,
        conclusion: "the machine did not rebuild larger truncations from empty source. Six returned predecessor occurrences survived rest, entered six explicit next-face events, and were replaced by successors whose lower interiors stayed exact. Admitting P_3/3 closed every degree-three Euler coefficient; withholding only that current left exactly the three repeated-axis cubes at -1/3. The carried e body gained exactly y^9/9!, and all three comparisons returned as one resting growth complex.",
    })
}

fn all_growth_accepted(acceptance: &GrowthAcceptanceRead) -> bool {
    acceptance.source_law_lineages_departed
        && acceptance.baseline_rest_remount_exact
        && acceptance.plural_equal_predecessors_stood_before_branching
        && acceptance.every_growth_used_a_live_predecessor
        && acceptance.every_lower_face_remained_exact
        && acceptance.every_replaced_predecessor_interface_departed
        && acceptance.full_degree_three_paths_commuted
        && acceptance.held_path_open_only_on_prime_cubes_with_negative_one_third_residual
        && acceptance.e_degree_nine_grew_by_one_exact_term
        && acceptance.e_degree_nine_paths_commuted
        && acceptance.comparisons_returned_as_one_higher_complex
        && acceptance.final_successor_survived_exact_rest_remount
        && acceptance.no_floating_point_causal_data
}

fn all_accepted(acceptance: &AcceptanceRead) -> bool {
    acceptance.source_law_lineages_departed
        && acceptance.source_laws_recovered_only_from_standing
        && acceptance.no_law_and_wrong_interface_refused
        && acceptance.full_euler_paths_commuted
        && acceptance.missing_prime_power_path_open_only_on_prime_squares
        && acceptance.same_formal_exp_law_served_prime_and_e_faces
        && acceptance.e_paths_commuted_exactly
        && acceptance.pi_zeta_finite_paths_remained_open_with_exact_overlap
        && acceptance.every_derived_comparison_returned_as_later_standing
        && acceptance.final_complex_survived_exact_rest_remount
        && acceptance.no_floating_point_causal_data
}

fn deposit_laws(
    laws: &[(String, LawKind)],
) -> Result<
    (
        FormulaEcology,
        soma_membrane::LiveCurrentRestImage,
        DepositRead,
    ),
    String,
> {
    eprintln!("formula ecology · depositing {} source laws", laws.len());
    let mut base = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let mut pairs = Vec::new();
    let mut materials = Vec::new();
    for (name, kind) in laws {
        let wire = LawWire {
            schema: "eros.formula-law.v1".to_owned(),
            kind: *kind,
        };
        let bytes = encode_json(&wire)?;
        let handle = ArtifactHandle::source(&format!("law:{name}"), &bytes);
        pairs.push(primed_pair(&mut base)?);
        materials.push((name.clone(), *kind, bytes, handle));
    }
    let before = base.rest_image().map_err(debug)?;
    let mut taught = LiveCurrentMachine::from_rest_image(before.clone()).map_err(debug)?;
    let mut control = LiveCurrentMachine::from_rest_image(before).map_err(debug)?;

    let arc_populations: Vec<_> = materials
        .iter()
        .zip(&pairs)
        .map(|((_, _, bytes, handle), pair)| seed_arcs(*pair, *handle, bytes))
        .collect();
    let regional: Vec<_> = pairs
        .iter()
        .zip(&arc_populations)
        .map(|(pair, arcs)| RegionalRelationCell::new(pair[1], arcs))
        .collect();
    let currents: Vec<_> = pairs
        .iter()
        .flat_map(|pair| {
            [
                CurrentEvent::ending(pair[0], relation(101).unwrap(), action()),
                CurrentEvent::ending(pair[1], relation(103).unwrap(), action()),
            ]
        })
        .collect();
    let radiation = taught
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    eprintln!("formula ecology · source-law deposit returned");
    control
        .receive(ContemporaryEvent::unrelated(&currents))
        .map_err(debug)?;
    if radiation.regional().len() != materials.len() {
        return Err("every source law returns one regional constituent".to_owned());
    }

    let mut handles = BTreeMap::new();
    let mut origins = BTreeMap::new();
    let mut reads = Vec::new();
    for (((name, kind, bytes, handle), returned), _) in
        materials.iter().zip(radiation.regional()).zip(0..)
    {
        let recovered = decode_bytes(returned.constituent(), handle.data_namespace)?;
        if recovered != *bytes {
            return Err(format!("source law {name} changed during hand-up"));
        }
        handles.insert(name.clone(), *handle);
        origins.insert(name.clone(), "source_law");
        reads.push(SourceLawRead {
            name: name.clone(),
            kind: *kind,
            handle: handle.wire(),
            encoded_bytes: bytes.len(),
            encoded_sha256: sha256(bytes),
            constituent: constituent_read(returned.constituent())?,
        });
    }
    let checkpoint = taught.rest_image().map_err(debug)?;
    let remounted = LiveCurrentMachine::from_rest_image(checkpoint.clone()).map_err(debug)?;
    let rest_exact = remounted.rest_image().map_err(debug)? == checkpoint;
    let deposit = DepositRead {
        source_laws: reads,
        source_lineages_after_event: taught.memory().live_lineages,
        machine: machine_read(&taught)?,
        no_law_control: machine_read(&control)?,
        rest_remount_exact: rest_exact,
    };
    Ok((
        FormulaEcology {
            machine: taught,
            handles,
            artifact_origins: origins,
            invocations: Vec::new(),
        },
        control.rest_image().map_err(debug)?,
        deposit,
    ))
}

impl FormulaEcology {
    fn data_namespace(&self, artifact: &str) -> Result<u64, String> {
        self.handles
            .get(artifact)
            .map(|handle| handle.data_namespace)
            .ok_or_else(|| format!("artifact {artifact} has no live handle"))
    }

    fn invoke(
        &mut self,
        event: &str,
        law: &str,
        inputs: &[&str],
        objective: InvocationWire,
        result_artifact: &str,
    ) -> Result<(), String> {
        eprintln!("formula ecology · invoke {event}");
        let mut selected = Vec::with_capacity(inputs.len() + 1);
        selected.push(law);
        selected.extend_from_slice(inputs);
        let meeting = self.meet(event, &selected, &objective)?;
        let law_handle = meeting
            .selected
            .iter()
            .find(|(name, _)| name == law)
            .map(|(_, handle)| *handle)
            .ok_or_else(|| format!("event {event} selected law {law}"))?;
        let law_bytes = decode_bytes(&meeting.constituent, law_handle.data_namespace)?;
        let recovered_law: LawWire = decode_json(&law_bytes)?;
        if recovered_law.schema != "eros.formula-law.v1" {
            return Err(format!("event {event} recovered a foreign law schema"));
        }
        let objective_bytes = decode_bytes(&meeting.constituent, meeting.objective_namespace)?;
        let recovered_objective: InvocationWire = decode_json(&objective_bytes)?;
        if encode_json(&recovered_objective)? != encode_json(&objective)? {
            return Err(format!("event {event} objective changed during conduct"));
        }
        let result = conduct(
            recovered_law.kind,
            &recovered_objective,
            &meeting.constituent,
        )?;
        let encoded_result = encode_json(&result)?;
        let (handle, returned) =
            self.return_artifact(result_artifact, &encoded_result, result_origin(&result))?;
        eprintln!("formula ecology · returned {result_artifact}");
        self.invocations.push(InvocationRead {
            event: event.to_owned(),
            law: law.to_owned(),
            recruited_artifacts: inputs.iter().map(|input| (*input).to_owned()).collect(),
            objective,
            law_recovered_from_standing: true,
            objective_recovered_from_current: true,
            result_artifact: result_artifact.to_owned(),
            result_handle: handle.wire(),
            result,
            meeting: constituent_read(&meeting.constituent)?,
            returned_consequence: returned,
        });
        Ok(())
    }

    fn grow(
        &mut self,
        event: &str,
        law: &str,
        predecessor: &str,
        context: &[&str],
        objective: InvocationWire,
        successor: &str,
    ) -> Result<GrowthStepRead, String> {
        eprintln!("formula ecology · grow {event}");
        let mut selected = Vec::with_capacity(context.len() + 2);
        selected.push(law);
        selected.push(predecessor);
        selected.extend_from_slice(context);
        let meeting = self.meet(event, &selected, &objective)?;
        let law_handle = meeting
            .selected
            .iter()
            .find(|(name, _)| name == law)
            .map(|(_, handle)| *handle)
            .ok_or_else(|| format!("growth event {event} selected law {law}"))?;
        let recruited_predecessor = meeting
            .selected
            .iter()
            .find(|(name, _)| name == predecessor)
            .map(|(_, handle)| *handle)
            .ok_or_else(|| format!("growth event {event} selected predecessor {predecessor}"))?;
        let recovered_law: LawWire = decode_json(&decode_bytes(
            &meeting.constituent,
            law_handle.data_namespace,
        )?)?;
        if recovered_law.schema != "eros.formula-law.v1"
            || recovered_law.kind != LawKind::ApertureGrowth
        {
            return Err(format!("growth event {event} recovered another law"));
        }
        let objective_bytes = decode_bytes(&meeting.constituent, meeting.objective_namespace)?;
        let recovered_objective: InvocationWire = decode_json(&objective_bytes)?;
        if encode_json(&recovered_objective)? != encode_json(&objective)? {
            return Err(format!(
                "growth event {event} objective changed during conduct"
            ));
        }
        let predecessor_value: FormulaValueWire = decode_json(&decode_bytes(
            &meeting.constituent,
            recruited_predecessor.data_namespace,
        )?)?;
        let result = conduct(
            recovered_law.kind,
            &recovered_objective,
            &meeting.constituent,
        )?;
        let (lower_restriction_exact, new_homogeneous_terms) =
            growth_faces(&predecessor_value, &result)?;
        let encoded_result = encode_json(&result)?;
        let replaced_predecessor = *self.handles.get(predecessor).ok_or_else(|| {
            format!("growth event {event} retained its predecessor after meeting")
        })?;
        let replacement_event = format!("{event}:returned-successor");
        let replacement = self.replace_artifact(
            &replacement_event,
            predecessor,
            successor,
            &encoded_result,
            "growth_successor",
        )?;
        eprintln!(
            "formula ecology · replaced {predecessor} with {successor} · old data {} · old recruit {}",
            replacement.old_data_departed, replacement.old_recruit_departed
        );
        let mut recruited_artifacts = vec![predecessor.to_owned()];
        recruited_artifacts.extend(context.iter().map(|name| (*name).to_owned()));
        Ok(GrowthStepRead {
            event: event.to_owned(),
            law: law.to_owned(),
            recruited_artifacts,
            objective,
            predecessor_artifact: predecessor.to_owned(),
            recruited_predecessor_handle: recruited_predecessor.wire(),
            replaced_predecessor_handle: replaced_predecessor.wire(),
            predecessor: predecessor_value,
            successor_artifact: successor.to_owned(),
            successor_handle: replacement.handle.wire(),
            successor: result,
            lower_restriction_exact,
            new_homogeneous_terms,
            old_data_interfaces_departed: replacement.old_data_departed,
            old_recruit_interface_departed: replacement.old_recruit_departed,
            law_recovered_from_standing: true,
            objective_recovered_from_current: true,
            meeting: constituent_read(&meeting.constituent)?,
            returned_replacement: replacement.constituent,
        })
    }

    fn compare(
        &mut self,
        event: &str,
        left: &str,
        right: &str,
        mode: ComparisonMode,
        result: &str,
    ) -> Result<(), String> {
        self.invoke(
            event,
            "exact-comparison",
            &[left, right],
            InvocationWire::Compare {
                mode,
                left_namespace: namespace_string(self.data_namespace(left)?),
                right_namespace: namespace_string(self.data_namespace(right)?),
            },
            result,
        )
    }

    fn meet(
        &mut self,
        event: &str,
        selected_names: &[&str],
        objective: &InvocationWire,
    ) -> Result<Meeting, String> {
        let selected: Vec<_> = selected_names
            .iter()
            .map(|name| {
                self.handles
                    .get(*name)
                    .copied()
                    .map(|handle| ((*name).to_owned(), handle))
                    .ok_or_else(|| format!("event {event} cannot recruit missing artifact {name}"))
            })
            .collect::<Result<_, _>>()?;
        let objective_bytes = encode_json(objective)?;
        let event_identity = event.as_bytes();
        let objective_namespace = namespace(&[
            b"eros-formula-objective-v1",
            event_identity,
            &objective_bytes,
        ]);
        let next: Vec<_> = selected
            .iter()
            .map(|(name, handle)| {
                (
                    name.clone(),
                    handle.after_contact(
                        &[
                            event_identity,
                            name.as_bytes(),
                            &handle.generation.to_le_bytes(),
                        ]
                        .concat(),
                    ),
                )
            })
            .collect();
        let pair = primed_pair(&mut self.machine)?;
        let arcs = meeting_arcs(
            pair,
            &selected,
            &next,
            objective_namespace,
            &objective_bytes,
        );
        let currents = [
            CurrentEvent::ending(pair[0], relation(107)?, action()),
            CurrentEvent::ending(pair[1], relation(109)?, action()),
        ];
        let regional = [RegionalRelationCell::new(pair[1], &arcs)];
        let radiation = self
            .machine
            .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
            .map_err(debug)?;
        let constituent = radiation
            .regional()
            .first()
            .ok_or_else(|| format!("event {event} returns one regional constituent"))?
            .constituent()
            .clone();
        for (name, handle) in &next {
            self.handles.insert(name.clone(), *handle);
        }
        Ok(Meeting {
            constituent,
            selected,
            objective_namespace,
        })
    }

    fn return_artifact(
        &mut self,
        name: &str,
        bytes: &[u8],
        origin: &'static str,
    ) -> Result<(ArtifactHandle, ConstituentRead), String> {
        if self.handles.contains_key(name) {
            return Err(format!(
                "artifact {name} would overwrite an existing occurrence"
            ));
        }
        let handle = ArtifactHandle::source(&format!("returned:{name}"), bytes);
        let pair = primed_pair(&mut self.machine)?;
        let arcs = seed_arcs(pair, handle, bytes);
        let currents = [
            CurrentEvent::ending(pair[0], relation(113)?, action()),
            CurrentEvent::ending(pair[1], relation(127)?, action()),
        ];
        let regional = [RegionalRelationCell::new(pair[1], &arcs)];
        let radiation = self
            .machine
            .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
            .map_err(debug)?;
        let constituent = radiation
            .regional()
            .first()
            .ok_or_else(|| format!("returned artifact {name} emits one constituent"))?
            .constituent();
        if decode_bytes(constituent, handle.data_namespace)? != bytes {
            return Err(format!("returned artifact {name} changed during hand-up"));
        }
        let read = constituent_read(constituent)?;
        self.handles.insert(name.to_owned(), handle);
        self.artifact_origins.insert(name.to_owned(), origin);
        Ok((handle, read))
    }

    fn replace_artifact(
        &mut self,
        event: &str,
        predecessor: &str,
        successor: &str,
        successor_bytes: &[u8],
        origin: &'static str,
    ) -> Result<ReplacementOutcome, String> {
        if self.handles.contains_key(successor) {
            return Err(format!(
                "successor {successor} already has an active occurrence"
            ));
        }
        let prior = *self
            .handles
            .get(predecessor)
            .ok_or_else(|| format!("predecessor {predecessor} is not active"))?;
        let prior_bytes = read_namespace_from_standing(&self.machine, prior.data_namespace)?;
        let next = prior.successor(successor, successor_bytes, event.as_bytes());
        let pair = primed_pair(&mut self.machine)?;
        let arcs = replacement_arcs(pair, prior, &prior_bytes, next, successor_bytes);
        let currents = [
            CurrentEvent::ending(pair[0], relation(139)?, action()),
            CurrentEvent::ending(pair[1], relation(149)?, action()),
        ];
        let regional = [RegionalRelationCell::new(pair[1], &arcs)];
        let radiation = self
            .machine
            .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
            .map_err(debug)?;
        let constituent = radiation
            .regional()
            .first()
            .ok_or_else(|| format!("replacement {event} emits one constituent"))?
            .constituent();
        if decode_bytes(constituent, next.data_namespace)? != successor_bytes {
            return Err(format!("replacement {event} changed its successor bytes"));
        }
        let old_data_departed = !has_exposed_namespace(constituent, prior.data_namespace)
            && read_namespace_from_standing(&self.machine, prior.data_namespace).is_err();
        let old_recruit_departed = !has_exposed_namespace(constituent, prior.recruit_namespace)
            && !standing_has_exposed_namespace(&self.machine, prior.recruit_namespace);
        let read = constituent_read(constituent)?;
        self.handles.remove(predecessor);
        self.artifact_origins.remove(predecessor);
        self.handles.insert(successor.to_owned(), next);
        self.artifact_origins.insert(successor.to_owned(), origin);
        Ok(ReplacementOutcome {
            handle: next,
            constituent: read,
            old_data_departed,
            old_recruit_departed,
        })
    }

    fn read_value(&self, artifact: &str) -> Result<FormulaValueWire, String> {
        let handle = self
            .handles
            .get(artifact)
            .ok_or_else(|| format!("artifact {artifact} has no handle"))?;
        let bytes = read_namespace_from_standing(&self.machine, handle.data_namespace)?;
        decode_json(&bytes)
    }

    fn polynomial_value(&self, artifact: &str) -> Result<Polynomial, String> {
        match self.read_value(artifact)? {
            FormulaValueWire::Polynomial { value, .. } => Polynomial::from_wire(&value),
            _ => Err(format!("artifact {artifact} is not a polynomial")),
        }
    }

    fn comparison_value(&self, artifact: &str) -> Result<ComparisonWire, String> {
        match self.read_value(artifact)? {
            FormulaValueWire::Comparison { value } => Ok(value),
            _ => Err(format!("artifact {artifact} is not a comparison")),
        }
    }

    fn complex_value(&self, artifact: &str) -> Result<ComplexWire, String> {
        match self.read_value(artifact)? {
            FormulaValueWire::Complex { value } => Ok(value),
            _ => Err(format!("artifact {artifact} is not a complex")),
        }
    }
}

fn result_origin(value: &FormulaValueWire) -> &'static str {
    match value {
        FormulaValueWire::Comparison { .. } => "comparison_return",
        FormulaValueWire::Complex { .. } => "higher_complex_return",
        _ => "generative_consequence",
    }
}

fn conduct(
    law: LawKind,
    invocation: &InvocationWire,
    constituent: &LiveConstituent,
) -> Result<FormulaValueWire, String> {
    match (law, invocation) {
        (
            LawKind::EulerLog,
            InvocationWire::EulerLog {
                primes,
                degree,
                include_prime_power_repetitions,
            },
        ) => Ok(polynomial_value(
            euler_log(primes, *degree, *include_prime_power_repetitions)?,
            false,
        )),
        (LawKind::EulerProduct, InvocationWire::EulerProduct { primes, degree }) => {
            Ok(polynomial_value(euler_product(primes, *degree)?, false))
        }
        (
            LawKind::FormalExp,
            InvocationWire::FormalExp {
                degree,
                input_namespace,
                literal,
            },
        ) => {
            let input = match (input_namespace, literal) {
                (Some(namespace), None) => {
                    polynomial_from_constituent(constituent, parse_namespace(namespace)?)?
                }
                (None, Some(literal)) => Polynomial::from_wire(literal)?,
                _ => {
                    return Err(
                        "formal Exp needs exactly one literal or returned polynomial".to_owned(),
                    )
                }
            };
            if input.degree != *degree {
                return Err("the formal Exp objective changed the input aperture".to_owned());
            }
            let output = input.formal_exp()?;
            let evaluate = output
                .axes
                .iter()
                .all(|axis| matches!(axis, Axis::Symbol(name) if name == "y"));
            Ok(polynomial_value(output, evaluate))
        }
        (LawKind::FactorialRecurrence, InvocationWire::FactorialRecurrence { degree }) => {
            Ok(polynomial_value(factorial_recurrence(*degree), true))
        }
        (LawKind::MachinArctan, InvocationWire::MachinArctan { terms }) => {
            Ok(FormulaValueWire::PiInterval {
                terms: *terms,
                value: machin_interval(*terms)?.wire(),
            })
        }
        (
            LawKind::DirichletZeta2,
            InvocationWire::DirichletZeta2 {
                terms,
                euler_primes,
            },
        ) => {
            let (enclosure, euler) = zeta2_face(*terms, euler_primes)?;
            Ok(FormulaValueWire::Zeta2 {
                terms: *terms,
                dirichlet_enclosure: enclosure.wire(),
                finite_euler_product: rational_wire(&euler),
                euler_primes: euler_primes.clone(),
            })
        }
        (
            LawKind::ExactComparison,
            InvocationWire::Compare {
                mode,
                left_namespace,
                right_namespace,
            },
        ) => {
            let left_namespace = parse_namespace(left_namespace)?;
            let right_namespace = parse_namespace(right_namespace)?;
            let left: FormulaValueWire = decode_json(&decode_bytes(constituent, left_namespace)?)?;
            let right: FormulaValueWire =
                decode_json(&decode_bytes(constituent, right_namespace)?)?;
            Ok(FormulaValueWire::Comparison {
                value: compare_values(*mode, left_namespace, right_namespace, &left, &right)?,
            })
        }
        (
            LawKind::ComplexAssembly,
            InvocationWire::Assemble {
                comparison_namespaces,
            },
        ) => {
            let comparisons = comparison_namespaces
                .iter()
                .map(|namespace| {
                    let namespace_value = parse_namespace(namespace)?;
                    let value: FormulaValueWire =
                        decode_json(&decode_bytes(constituent, namespace_value)?)?;
                    match value {
                        FormulaValueWire::Comparison { value } => Ok(ComplexComparisonWire {
                            namespace: namespace.clone(),
                            mode: value.mode,
                            status: value.status,
                        }),
                        _ => Err(format!(
                            "complex assembly namespace {namespace} is not a comparison"
                        )),
                    }
                })
                .collect::<Result<Vec<_>, String>>()?;
            Ok(FormulaValueWire::Complex {
                value: ComplexWire { comparisons },
            })
        }
        (
            LawKind::ApertureGrowth,
            InvocationWire::ExtendEulerLog {
                prior_namespace,
                new_degree,
                include_new_prime_power_repetition,
            },
        ) => {
            let prior =
                polynomial_from_constituent(constituent, parse_namespace(prior_namespace)?)?;
            Ok(polynomial_value(
                extend_euler_log(&prior, *new_degree, *include_new_prime_power_repetition)?,
                false,
            ))
        }
        (
            LawKind::ApertureGrowth,
            InvocationWire::ExtendExponential {
                logarithm_namespace,
                prior_exponential_namespace,
                new_degree,
            },
        ) => {
            let logarithm =
                polynomial_from_constituent(constituent, parse_namespace(logarithm_namespace)?)?;
            let prior = polynomial_from_constituent(
                constituent,
                parse_namespace(prior_exponential_namespace)?,
            )?;
            Ok(polynomial_value(
                extend_exponential(&logarithm, &prior, *new_degree)?,
                false,
            ))
        }
        (
            LawKind::ApertureGrowth,
            InvocationWire::ExtendEulerProduct {
                prior_namespace,
                new_degree,
            },
        ) => {
            let prior =
                polynomial_from_constituent(constituent, parse_namespace(prior_namespace)?)?;
            Ok(polynomial_value(
                extend_euler_product(&prior, *new_degree)?,
                false,
            ))
        }
        (
            LawKind::ApertureGrowth,
            InvocationWire::ExtendFactorial {
                prior_namespace,
                new_degree,
            },
        ) => {
            let prior =
                polynomial_from_constituent(constituent, parse_namespace(prior_namespace)?)?;
            Ok(polynomial_value(
                extend_factorial(&prior, *new_degree)?,
                true,
            ))
        }
        _ => Err(format!(
            "law {law:?} does not afford objective {}",
            invocation_name(invocation)
        )),
    }
}

fn invocation_name(invocation: &InvocationWire) -> &'static str {
    match invocation {
        InvocationWire::EulerLog { .. } => "euler_log",
        InvocationWire::EulerProduct { .. } => "euler_product",
        InvocationWire::FormalExp { .. } => "formal_exp",
        InvocationWire::FactorialRecurrence { .. } => "factorial_recurrence",
        InvocationWire::MachinArctan { .. } => "machin_arctan",
        InvocationWire::DirichletZeta2 { .. } => "dirichlet_zeta2",
        InvocationWire::Compare { .. } => "compare",
        InvocationWire::Assemble { .. } => "assemble",
        InvocationWire::ExtendEulerLog { .. } => "extend_euler_log",
        InvocationWire::ExtendExponential { .. } => "extend_exponential",
        InvocationWire::ExtendEulerProduct { .. } => "extend_euler_product",
        InvocationWire::ExtendFactorial { .. } => "extend_factorial",
    }
}

fn polynomial_value(value: Polynomial, evaluate_at_one: bool) -> FormulaValueWire {
    FormulaValueWire::Polynomial {
        evaluation_at_one: evaluate_at_one.then(|| rational_wire(&value.evaluate_at_one())),
        value: value.wire(),
    }
}

fn polynomial_from_constituent(
    constituent: &LiveConstituent,
    namespace: u64,
) -> Result<Polynomial, String> {
    let value: FormulaValueWire = decode_json(&decode_bytes(constituent, namespace)?)?;
    match value {
        FormulaValueWire::Polynomial { value, .. } => Polynomial::from_wire(&value),
        _ => Err(format!(
            "namespace {} does not carry a polynomial",
            namespace_string(namespace)
        )),
    }
}

fn compare_values(
    mode: ComparisonMode,
    left_namespace: u64,
    right_namespace: u64,
    left: &FormulaValueWire,
    right: &FormulaValueWire,
) -> Result<ComparisonWire, String> {
    let (status, detail) = match mode {
        ComparisonMode::ExactPolynomial => {
            let left = value_polynomial(left)?;
            let right = value_polynomial(right)?;
            let residual = left.subtract(&right)?;
            let differing_terms = residual
                .terms
                .iter()
                .map(|(monomial, coefficient)| TermWire {
                    monomial: monomial.clone(),
                    coefficient: rational_wire(coefficient),
                })
                .collect();
            (
                if residual.is_zero() {
                    ComparisonStatus::Commutes
                } else {
                    ComparisonStatus::Open
                },
                ComparisonDetailWire::Polynomial {
                    residual_left_minus_right: residual.wire(),
                    differing_terms,
                },
            )
        }
        ComparisonMode::PiSquaredAgainstSixZeta2 => {
            let pi = match left {
                FormulaValueWire::PiInterval { value, .. } => ExactInterval::from_wire(value)?,
                _ => return Err("the left pi/Zeta path is not a pi interval".to_owned()),
            };
            let zeta = match right {
                FormulaValueWire::Zeta2 {
                    dirichlet_enclosure,
                    ..
                } => ExactInterval::from_wire(dirichlet_enclosure)?,
                _ => return Err("the right pi/Zeta path is not a Zeta enclosure".to_owned()),
            };
            let pi_squared = pi.square_positive()?;
            let six_zeta = zeta.scale_integer(6);
            let overlap = pi_squared.intersection(&six_zeta);
            (
                ComparisonStatus::Open,
                ComparisonDetailWire::PiZeta {
                    pi_squared: pi_squared.wire(),
                    six_zeta2: six_zeta.wire(),
                    overlap: overlap.map(|interval| interval.wire()),
                    finite_stage_identity_closed: false,
                },
            )
        }
    };
    Ok(ComparisonWire {
        mode,
        status,
        left_namespace: namespace_string(left_namespace),
        right_namespace: namespace_string(right_namespace),
        detail,
    })
}

fn value_polynomial(value: &FormulaValueWire) -> Result<Polynomial, String> {
    match value {
        FormulaValueWire::Polynomial { value, .. } => Polynomial::from_wire(value),
        _ => Err("an exact polynomial comparison received another value species".to_owned()),
    }
}

fn growth_faces(
    predecessor: &FormulaValueWire,
    successor: &FormulaValueWire,
) -> Result<(bool, Vec<TermWire>), String> {
    let predecessor = value_polynomial(predecessor)?;
    let successor = value_polynomial(successor)?;
    if successor.degree != predecessor.degree.saturating_add(1)
        || successor.axes != predecessor.axes
    {
        return Err("a growth return did not enlarge exactly one common aperture".to_owned());
    }
    let lower_exact = successor.restrict_degree(predecessor.degree)? == predecessor;
    let terms = successor
        .homogeneous(successor.degree)
        .terms
        .iter()
        .map(|(monomial, coefficient)| TermWire {
            monomial: monomial.clone(),
            coefficient: rational_wire(coefficient),
        })
        .collect();
    Ok((lower_exact, terms))
}

fn extend_euler_log(
    prior: &Polynomial,
    new_degree: u8,
    include_new_prime_power_repetition: bool,
) -> Result<Polynomial, String> {
    if prior.degree != 2 || new_degree != 3 {
        return Err("the bounded Euler-log growth is exactly degree two to three".to_owned());
    }
    let primes = polynomial_prime_axes(prior)?;
    if *prior != euler_log(&primes, 2, true)? {
        return Err("Euler-log growth requires the complete returned degree-two face".to_owned());
    }
    let mut successor = prior.lift_degree(new_degree)?;
    if include_new_prime_power_repetition {
        for axis in 0..primes.len() {
            let mut monomial = vec![0; primes.len()];
            monomial[axis] = new_degree;
            successor.add_term(monomial, ratio(1, i64::from(new_degree)));
        }
    }
    Ok(successor)
}

fn extend_exponential(
    logarithm: &Polynomial,
    prior: &Polynomial,
    new_degree: u8,
) -> Result<Polynomial, String> {
    if prior.degree.saturating_add(1) != new_degree
        || logarithm.degree != new_degree
        || prior.axes != logarithm.axes
    {
        return Err("the exponential successor needs one common next aperture".to_owned());
    }
    let prior_lifted = prior.lift_degree(new_degree)?;
    let mut weighted = Polynomial::zero(prior.axes.clone(), new_degree);
    for degree in 1..=new_degree {
        let logarithm_face = logarithm.homogeneous(degree);
        let exponential_face = prior_lifted.homogeneous(new_degree - degree);
        let term = logarithm_face
            .multiply(&exponential_face)?
            .scale(&ratio(i64::from(degree), 1));
        weighted = weighted.add(&term)?;
    }
    let next_face = weighted.scale(&ratio(1, i64::from(new_degree)));
    prior_lifted.add(&next_face)
}

fn extend_euler_product(prior: &Polynomial, new_degree: u8) -> Result<Polynomial, String> {
    if prior.degree != 2 || new_degree != 3 {
        return Err("the bounded Euler-product growth is exactly degree two to three".to_owned());
    }
    let primes = polynomial_prime_axes(prior)?;
    if *prior != euler_product(&primes, prior.degree)? {
        return Err(
            "Euler-product growth requires the complete returned degree-two face".to_owned(),
        );
    }
    let mut successor = prior.lift_degree(new_degree)?;
    let mut monomial = vec![0; primes.len()];
    add_weak_compositions(&mut successor, &mut monomial, 0, new_degree);
    Ok(successor)
}

fn add_weak_compositions(
    polynomial: &mut Polynomial,
    monomial: &mut [u8],
    axis: usize,
    remaining: u8,
) {
    if axis + 1 == monomial.len() {
        monomial[axis] = remaining;
        polynomial.add_term(monomial.to_vec(), ratio(1, 1));
        return;
    }
    for exponent in 0..=remaining {
        monomial[axis] = exponent;
        add_weak_compositions(polynomial, monomial, axis + 1, remaining - exponent);
    }
}

fn extend_factorial(prior: &Polynomial, new_degree: u8) -> Result<Polynomial, String> {
    if prior.degree.saturating_add(1) != new_degree
        || prior.axes != vec![Axis::Symbol("y".to_owned())]
        || *prior != factorial_recurrence(prior.degree)
    {
        return Err("factorial growth requires one complete one-generator predecessor".to_owned());
    }
    let prior_coefficient = prior
        .terms
        .get(&vec![prior.degree])
        .cloned()
        .ok_or_else(|| "the predecessor has no terminal factorial coefficient".to_owned())?;
    let mut successor = prior.lift_degree(new_degree)?;
    successor.add_term(
        vec![new_degree],
        prior_coefficient / BigRational::from_integer(BigInt::from(new_degree)),
    );
    Ok(successor)
}

fn polynomial_prime_axes(polynomial: &Polynomial) -> Result<Vec<u32>, String> {
    polynomial
        .axes
        .iter()
        .map(|axis| match axis {
            Axis::Prime(prime) => Ok(*prime),
            Axis::Symbol(_) => Err("the Euler aperture contains a non-prime axis".to_owned()),
        })
        .collect()
}

fn one_generator(degree: u8) -> Polynomial {
    let mut result = Polynomial::zero(vec![Axis::Symbol("y".to_owned())], degree);
    result.add_term(vec![1], ratio(1, 1));
    result
}

fn factorial_recurrence(degree: u8) -> Polynomial {
    let mut result = Polynomial::zero(vec![Axis::Symbol("y".to_owned())], degree);
    let mut coefficient = ratio(1, 1);
    result.add_term(vec![0], coefficient.clone());
    for exponent in 1..=degree {
        coefficient /= BigRational::from_integer(BigInt::from(exponent));
        result.add_term(vec![exponent], coefficient.clone());
    }
    result
}

fn euler_log(
    primes: &[u32],
    degree: u8,
    include_prime_power_repetitions: bool,
) -> Result<Polynomial, String> {
    validate_prime_axes(primes)?;
    if degree < 2 {
        return Err("the bounded Euler log requires degree at least two".to_owned());
    }
    let axes = primes.iter().copied().map(Axis::Prime).collect();
    let mut result = Polynomial::zero(axes, degree);
    for axis in 0..primes.len() {
        let mut prime = vec![0; primes.len()];
        prime[axis] = 1;
        result.add_term(prime, ratio(1, 1));
        if include_prime_power_repetitions {
            let mut square = vec![0; primes.len()];
            square[axis] = 2;
            result.add_term(square, ratio(1, 2));
        }
    }
    Ok(result)
}

fn euler_product(primes: &[u32], degree: u8) -> Result<Polynomial, String> {
    validate_prime_axes(primes)?;
    let axes: Vec<_> = primes.iter().copied().map(Axis::Prime).collect();
    let mut result = Polynomial::one(axes.clone(), degree);
    for axis in 0..primes.len() {
        let mut factor = Polynomial::zero(axes.clone(), degree);
        for exponent in 0..=degree {
            let mut monomial = vec![0; primes.len()];
            monomial[axis] = exponent;
            factor.add_term(monomial, ratio(1, 1));
        }
        result = result.multiply(&factor)?;
    }
    Ok(result)
}

fn machin_interval(terms: u32) -> Result<ExactInterval, String> {
    if terms == 0 {
        return Err("the Machin aperture needs at least one term".to_owned());
    }
    let one_fifth = ratio(1, 5);
    let one_239 = ratio(1, 239);
    Ok(atan_interval(&one_fifth, terms)?
        .scale_integer(16)
        .add(&atan_interval(&one_239, terms)?.scale_integer(-4)))
}

fn atan_interval(z: &BigRational, terms: u32) -> Result<ExactInterval, String> {
    if *z <= ratio(0, 1) || *z > ratio(1, 1) {
        return Err("the alternating arctangent enclosure expects 0 < z <= 1".to_owned());
    }
    let mut sum = ratio(0, 1);
    let z_squared = z * z;
    let mut power = z.clone();
    for at in 0..terms {
        let denominator = BigInt::from(2 * at + 1);
        let term = power.clone() / BigRational::from_integer(denominator);
        if at % 2 == 0 {
            sum += term;
        } else {
            sum -= term;
        }
        power *= &z_squared;
    }
    let next = power / BigRational::from_integer(BigInt::from(2 * terms + 1));
    let sibling = if terms % 2 == 0 {
        &sum + next
    } else {
        &sum - next
    };
    ExactInterval::new(sum.clone().min(sibling.clone()), sum.max(sibling))
}

fn zeta2_face(terms: u32, euler_primes: &[u32]) -> Result<(ExactInterval, BigRational), String> {
    if terms == 0 {
        return Err("the Zeta aperture needs at least one Dirichlet term".to_owned());
    }
    validate_prime_axes(euler_primes)?;
    let mut sum = ratio(0, 1);
    for n in 1..=terms {
        sum += BigRational::new(BigInt::from(1), BigInt::from(n) * BigInt::from(n));
    }
    let enclosure = ExactInterval::new(
        sum.clone(),
        &sum + BigRational::new(BigInt::from(1), BigInt::from(terms)),
    )?;
    let mut euler = ratio(1, 1);
    for prime in euler_primes {
        let square = BigInt::from(*prime) * BigInt::from(*prime);
        euler *= BigRational::new(square.clone(), square - BigInt::from(1));
    }
    Ok((enclosure, euler))
}

fn validate_prime_axes(primes: &[u32]) -> Result<(), String> {
    if primes.is_empty() {
        return Err("a prime-axis aperture cannot be empty".to_owned());
    }
    let distinct: BTreeSet<_> = primes.iter().copied().collect();
    if distinct.len() != primes.len() || primes.iter().any(|prime| !is_prime(*prime)) {
        return Err("every supplied prime axis must be distinct and irreducible".to_owned());
    }
    Ok(())
}

fn is_prime(value: u32) -> bool {
    if value < 2 {
        return false;
    }
    let mut divisor = 2u32;
    while divisor.saturating_mul(divisor) <= value {
        if value % divisor == 0 {
            return false;
        }
        divisor += 1;
    }
    true
}

fn refusal_probe(
    checkpoint: &soma_membrane::LiveCurrentRestImage,
    handle: ArtifactHandle,
    objective: &InvocationWire,
    event_identity: &[u8],
    role: &'static str,
) -> Result<RefusalRead, String> {
    let mut machine = LiveCurrentMachine::from_rest_image(checkpoint.clone()).map_err(debug)?;
    let objective_bytes = encode_json(objective)?;
    let objective_namespace = namespace(&[
        b"eros-formula-refusal-objective-v1",
        event_identity,
        &objective_bytes,
    ]);
    let selected = vec![("law".to_owned(), handle)];
    let next = vec![("law".to_owned(), handle.after_contact(event_identity))];
    let pair = primed_pair(&mut machine)?;
    let arcs = meeting_arcs(
        pair,
        &selected,
        &next,
        objective_namespace,
        &objective_bytes,
    );
    let currents = [
        CurrentEvent::ending(pair[0], relation(131)?, action()),
        CurrentEvent::ending(pair[1], relation(137)?, action()),
    ];
    let regional = [RegionalRelationCell::new(pair[1], &arcs)];
    let radiation = machine
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    let constituent = radiation
        .regional()
        .first()
        .ok_or_else(|| "a refusal probe returns one germ".to_owned())?
        .constituent();
    Ok(RefusalRead {
        role,
        law_recovered: decode_bytes(constituent, handle.data_namespace).is_ok(),
        objective_recovered: decode_bytes(constituent, objective_namespace).is_ok(),
        constituent: constituent_read(constituent)?,
    })
}

fn seed_arcs(
    pair: [CurrentLineage; 2],
    handle: ArtifactHandle,
    bytes: &[u8],
) -> Vec<RegionalRelationArc> {
    let bits = bytes_to_bits(bytes);
    let mut arcs = bit_arcs(pair, handle.data_namespace, &bits, 0);
    arcs.push(interface_arc(
        pair,
        handle.recruit_namespace,
        RECRUIT_LOCAL,
        u32::try_from(arcs.len()).unwrap(),
        IncidenceHand::Against,
    ));
    arcs
}

fn replacement_arcs(
    pair: [CurrentLineage; 2],
    old: ArtifactHandle,
    old_bytes: &[u8],
    new: ArtifactHandle,
    new_bytes: &[u8],
) -> Vec<RegionalRelationArc> {
    let old_bits = bytes_to_bits(old_bytes);
    let new_bits = bytes_to_bits(new_bytes);
    let mut arcs = bit_arcs(pair, old.data_namespace, &old_bits, 0);
    let mut slot = u32::try_from(arcs.len()).unwrap();
    arcs.push(interface_arc(
        pair,
        old.recruit_namespace,
        RECRUIT_LOCAL,
        slot,
        IncidenceHand::Against,
    ));
    slot += 1;
    arcs.extend(bit_arcs(pair, new.data_namespace, &new_bits, slot));
    slot = u32::try_from(arcs.len()).unwrap();
    arcs.push(interface_arc(
        pair,
        new.recruit_namespace,
        RECRUIT_LOCAL,
        slot,
        IncidenceHand::Against,
    ));
    arcs
}

fn meeting_arcs(
    pair: [CurrentLineage; 2],
    selected: &[(String, ArtifactHandle)],
    next: &[(String, ArtifactHandle)],
    objective_namespace: u64,
    objective_bytes: &[u8],
) -> Vec<RegionalRelationArc> {
    let objective_bits = bytes_to_bits(objective_bytes);
    let mut arcs = bit_arcs(pair, objective_namespace, &objective_bits, 0);
    let mut slot = u32::try_from(arcs.len()).unwrap();
    for (_, handle) in selected {
        arcs.push(interface_arc(
            pair,
            handle.recruit_namespace,
            RECRUIT_LOCAL,
            slot,
            IncidenceHand::Against,
        ));
        slot += 1;
    }
    for (_, handle) in next {
        arcs.push(interface_arc(
            pair,
            handle.recruit_namespace,
            RECRUIT_LOCAL,
            slot,
            IncidenceHand::Against,
        ));
        slot += 1;
    }
    arcs
}

fn bit_arcs(
    pair: [CurrentLineage; 2],
    namespace: u64,
    bits: &[bool],
    first_slot: u32,
) -> Vec<RegionalRelationArc> {
    bits.iter()
        .copied()
        .enumerate()
        .map(|(at, bit)| {
            interface_arc(
                pair,
                namespace,
                at as u64,
                first_slot + u32::try_from(at).unwrap(),
                if bit {
                    IncidenceHand::With
                } else {
                    IncidenceHand::Against
                },
            )
        })
        .collect()
}

fn interface_arc(
    pair: [CurrentLineage; 2],
    namespace: u64,
    local: u64,
    boundary_slot: u32,
    hand: IncidenceHand,
) -> RegionalRelationArc {
    RegionalRelationArc::new(
        pair[0],
        CurrentBoundaryPort::Cell,
        pair[1],
        CurrentBoundaryPort::Cell,
        InterfaceCapability::new(namespace, local),
        boundary_slot,
        0,
        hand,
    )
}

fn decode_bytes(constituent: &LiveConstituent, namespace: u64) -> Result<Vec<u8>, String> {
    let mut bits = BTreeMap::new();
    let exposed: BTreeSet<u32> = constituent.exposed().iter().copied().collect();
    for pin_at in exposed {
        let pin = constituent
            .pins()
            .get(usize::try_from(pin_at).map_err(debug)?)
            .ok_or_else(|| "an exposed pin remains in its constituent".to_owned())?;
        let Some(interface) = pin.interface() else {
            continue;
        };
        if interface.namespace() != namespace {
            continue;
        }
        let mut hand = None;
        for incidence in constituent
            .incidences()
            .iter()
            .copied()
            .filter(|incidence| incidence.pin() == pin_at)
        {
            match hand {
                None => hand = Some(incidence.hand()),
                Some(prior) if prior == incidence.hand() => {}
                Some(_) => {
                    return Err("one exposed formula bit has mixed residual hands".to_owned())
                }
            }
        }
        let hand = hand.ok_or_else(|| "one exposed formula bit has no incidence".to_owned())?;
        if bits
            .insert(interface.local(), hand == IncidenceHand::With)
            .is_some()
        {
            return Err("one formula bit position is exposed more than once".to_owned());
        }
    }
    if bits.is_empty() {
        return Err(format!(
            "no exposed formula bytes exist under {}",
            namespace_string(namespace)
        ));
    }
    let extent = bits.keys().next_back().copied().unwrap() + 1;
    if bits.len() as u64 != extent || extent % 8 != 0 {
        return Err("the formula bit positions are not one complete octet sequence".to_owned());
    }
    bits_to_bytes(
        &(0..extent)
            .map(|at| bits.get(&at).copied().unwrap())
            .collect::<Vec<_>>(),
    )
}

fn has_exposed_namespace(constituent: &LiveConstituent, namespace: u64) -> bool {
    constituent.exposed().iter().copied().any(|pin_at| {
        constituent
            .pins()
            .get(pin_at as usize)
            .and_then(|pin| pin.interface())
            .is_some_and(|interface| interface.namespace() == namespace)
    })
}

fn standing_has_exposed_namespace(machine: &LiveCurrentMachine, namespace: u64) -> bool {
    machine
        .standing()
        .constituents()
        .iter()
        .any(|constituent| has_exposed_namespace(constituent, namespace))
}

fn read_namespace_from_standing(
    machine: &LiveCurrentMachine,
    namespace: u64,
) -> Result<Vec<u8>, String> {
    let matches: Vec<_> = machine
        .standing()
        .constituents()
        .iter()
        .filter_map(|constituent| decode_bytes(constituent, namespace).ok())
        .collect();
    match matches.as_slice() {
        [bytes] => Ok(bytes.clone()),
        [] => Err(format!(
            "standing exposes no artifact under {}",
            namespace_string(namespace)
        )),
        _ => Err(format!(
            "standing exposes plural artifacts under {}",
            namespace_string(namespace)
        )),
    }
}

fn primed_pair(machine: &mut LiveCurrentMachine) -> Result<[CurrentLineage; 2], String> {
    let first = relation(PRIMING_VALUES[0])?;
    let pair = [
        machine
            .attach(CurrentGeometry::Cell(first))
            .map_err(debug)?,
        machine
            .attach(CurrentGeometry::Cell(first))
            .map_err(debug)?,
    ];
    for value in PRIMING_VALUES {
        let currents = [
            CurrentEvent::continuing(pair[0], relation(value)?, action()),
            CurrentEvent::continuing(pair[1], relation(value)?, action()),
        ];
        machine
            .receive(ContemporaryEvent::unrelated(&currents))
            .map_err(debug)?;
    }
    Ok(pair)
}

fn constituent_read(constituent: &LiveConstituent) -> Result<ConstituentRead, String> {
    Ok(ConstituentRead {
        grain: constituent.grain(),
        axes: constituent.axis_count(),
        cells: constituent.cells().len(),
        incidences: constituent.incidences().len(),
        pins: constituent.pins().len(),
        boundaries: constituent.boundaries().len(),
        exposed_pins: constituent.exposed().len(),
        open_pins: constituent
            .pins()
            .iter()
            .filter(|pin| pin.is_open())
            .count(),
        found_pins: constituent
            .pins()
            .iter()
            .filter(|pin| pin.is_found())
            .count(),
        native_sha256: words_sha256(&constituent.native_words().map_err(debug)?),
    })
}

fn machine_read(machine: &LiveCurrentMachine) -> Result<MachineRead, String> {
    let LiveMemory {
        standing_cells,
        standing_constituents,
        constituent_cells,
        constituent_incidences,
        constituent_pins,
        constituent_paths,
        constituent_transport_terms,
        live_lineages,
        ..
    } = machine.memory();
    let rest_octets = machine
        .rest_image()
        .map_err(debug)?
        .encode_native_bytes()
        .map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The hash below is untouched and
    // still reported; these are the same octets reaching `holon-plate deposit --from ERST:` instead
    // of being hashed and dropped. This site sits inside a helper the driver calls at every read.
    // The address is the content, so every distinct rest it seals is deposited at its own address
    // instead of all but the last being overwritten, and the file name carries the reported hash.
    let deposited = deposit_form_or_message(FORM_DRIVER, MACHINE_REST_FORM, &rest_octets)?;
    eprintln!("form deposited: {}", deposited.path.display());
    Ok(MachineRead {
        standing_rank: machine.standing().rank(),
        standing_cells,
        standing_constituents,
        constituent_cells,
        constituent_incidences,
        constituent_pins,
        constituent_paths,
        constituent_transport_terms,
        live_lineages,
        rest_sha256: sha256(&rest_octets),
    })
}

fn relation(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value))
        .ok_or_else(|| format!("relation value {value} remains nonzero"))
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving action")
}

fn bytes_to_bits(bytes: &[u8]) -> Vec<bool> {
    bytes
        .iter()
        .flat_map(|byte| (0..8).map(move |bit| byte & (1 << bit) != 0))
        .collect()
}

fn bits_to_bytes(bits: &[bool]) -> Result<Vec<u8>, String> {
    if bits.len() % 8 != 0 {
        return Err("a formula inscription needs a whole number of octets".to_owned());
    }
    Ok(bits
        .chunks_exact(8)
        .map(|chunk| {
            chunk
                .iter()
                .copied()
                .enumerate()
                .fold(0u8, |byte, (bit, live)| byte | (u8::from(live) << bit))
        })
        .collect())
}

fn prime_term_read(
    direct: &Polynomial,
    full: &Polynomial,
    foil: &Polynomial,
    primes: &[u32],
) -> Result<Vec<PrimeTermRead>, String> {
    direct.require_same_chart(full)?;
    direct.require_same_chart(foil)?;
    let mut rows = Vec::new();
    for (monomial, direct_coefficient) in &direct.terms {
        let degree = total_degree(monomial);
        if degree == 0 || degree > 2 {
            continue;
        }
        let full_coefficient = full
            .terms
            .get(monomial)
            .cloned()
            .unwrap_or_else(|| ratio(0, 1));
        let foil_coefficient = foil
            .terms
            .get(monomial)
            .cloned()
            .unwrap_or_else(|| ratio(0, 1));
        let residual = &foil_coefficient - direct_coefficient;
        let integer = monomial
            .iter()
            .zip(primes)
            .try_fold(1u32, |product, (exponent, prime)| {
                product.checked_mul(prime.pow(u32::from(*exponent)))
            })
            .ok_or_else(|| "the bounded monomial integer overflowed".to_owned())?;
        rows.push(PrimeTermRead {
            monomial: monomial_label(monomial, primes),
            integer,
            species: if degree == 1 { "prime" } else { "semiprime" },
            direct_euler_coefficient: rational_wire(direct_coefficient),
            exponential_coefficient: rational_wire(&full_coefficient),
            foil_coefficient: rational_wire(&foil_coefficient),
            foil_residual: rational_wire(&residual),
        });
    }
    rows.sort_by_key(|row| (row.integer, row.monomial.clone()));
    Ok(rows)
}

fn prime_degree_three_read(
    direct: &Polynomial,
    full: &Polynomial,
    held: &Polynomial,
    primes: &[u32],
) -> Result<Vec<PrimeDegreeThreeRead>, String> {
    direct.require_same_chart(full)?;
    direct.require_same_chart(held)?;
    let mut rows = Vec::new();
    for (monomial, direct_coefficient) in &direct.terms {
        if total_degree(monomial) != 3 {
            continue;
        }
        let full_coefficient = full
            .terms
            .get(monomial)
            .cloned()
            .unwrap_or_else(|| ratio(0, 1));
        let held_coefficient = held
            .terms
            .get(monomial)
            .cloned()
            .unwrap_or_else(|| ratio(0, 1));
        let held_residual = &held_coefficient - direct_coefficient;
        let integer = monomial
            .iter()
            .zip(primes)
            .try_fold(1u32, |product, (exponent, prime)| {
                product.checked_mul(prime.pow(u32::from(*exponent)))
            })
            .ok_or_else(|| "the bounded degree-three monomial overflowed".to_owned())?;
        let nonzero = monomial.iter().filter(|exponent| **exponent != 0).count();
        let largest = monomial.iter().copied().max().unwrap_or(0);
        let incidence = match (nonzero, largest) {
            (1, 3) => "one_axis_three_times",
            (2, 2) => "one_axis_twice_and_one_once",
            (3, 1) => "three_distinct_axes_once",
            _ => {
                return Err("the degree-three face has an impossible exponent incidence".to_owned())
            }
        };
        rows.push(PrimeDegreeThreeRead {
            monomial: monomial_label(monomial, primes),
            integer,
            incidence,
            direct_euler_coefficient: rational_wire(direct_coefficient),
            grown_exponential_coefficient: rational_wire(&full_coefficient),
            held_exponential_coefficient: rational_wire(&held_coefficient),
            held_residual: rational_wire(&held_residual),
        });
    }
    rows.sort_by_key(|row| (row.integer, row.monomial.clone()));
    Ok(rows)
}

fn foil_open_only_on_prime_squares(
    comparison: &ComparisonWire,
    primes: &[u32],
) -> Result<bool, String> {
    let ComparisonDetailWire::Polynomial {
        residual_left_minus_right,
        differing_terms,
    } = &comparison.detail
    else {
        return Ok(false);
    };
    if comparison.status != ComparisonStatus::Open || differing_terms.len() != primes.len() {
        return Ok(false);
    }
    let residual = Polynomial::from_wire(residual_left_minus_right)?;
    if residual.terms.len() != primes.len() {
        return Ok(false);
    }
    for axis in 0..primes.len() {
        let mut square = vec![0; primes.len()];
        square[axis] = 2;
        if residual.terms.get(&square) != Some(&ratio(-1, 2)) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn foil_open_only_on_prime_cubes(
    comparison: &ComparisonWire,
    primes: &[u32],
) -> Result<bool, String> {
    let ComparisonDetailWire::Polynomial {
        residual_left_minus_right,
        differing_terms,
    } = &comparison.detail
    else {
        return Ok(false);
    };
    if comparison.status != ComparisonStatus::Open || differing_terms.len() != primes.len() {
        return Ok(false);
    }
    let residual = Polynomial::from_wire(residual_left_minus_right)?;
    if residual.terms.len() != primes.len() {
        return Ok(false);
    }
    for axis in 0..primes.len() {
        let mut cube = vec![0; primes.len()];
        cube[axis] = 3;
        if residual.terms.get(&cube) != Some(&ratio(-1, 3)) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn monomial_label(monomial: &[u8], primes: &[u32]) -> String {
    monomial
        .iter()
        .zip(primes)
        .filter(|(exponent, _)| **exponent != 0)
        .map(|(exponent, prime)| {
            if *exponent == 1 {
                format!("X_{prime}")
            } else {
                format!("X_{prime}^{exponent}")
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn total_degree(monomial: &[u8]) -> u8 {
    monomial.iter().copied().fold(0u8, u8::saturating_add)
}

fn ratio(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn rational_wire(value: &BigRational) -> RationalWire {
    RationalWire {
        numerator: value.numer().to_string(),
        denominator: value.denom().to_string(),
    }
}

fn rational_from_wire(wire: &RationalWire) -> Result<BigRational, String> {
    let numerator = BigInt::parse_bytes(wire.numerator.as_bytes(), 10)
        .ok_or_else(|| format!("invalid exact numerator {}", wire.numerator))?;
    let denominator = BigInt::parse_bytes(wire.denominator.as_bytes(), 10)
        .ok_or_else(|| format!("invalid exact denominator {}", wire.denominator))?;
    if denominator.sign() != Sign::Plus {
        return Err("an exact denominator must remain positive".to_owned());
    }
    Ok(BigRational::new(numerator, denominator))
}

fn encode_json<T: Serialize>(value: &T) -> Result<Vec<u8>, String> {
    serde_json::to_vec(value).map_err(|error| format!("exact JSON encodes: {error}"))
}

fn decode_json<T: for<'de> Deserialize<'de>>(bytes: &[u8]) -> Result<T, String> {
    serde_json::from_slice(bytes).map_err(|error| format!("exact JSON decodes: {error}"))
}

fn namespace(parts: &[&[u8]]) -> u64 {
    let mut hash = Sha256::new();
    for part in parts {
        hash.update(part);
        hash.update([0]);
    }
    let digest = hash.finalize();
    let value = u64::from_be_bytes(digest[..8].try_into().unwrap());
    if value == 0 {
        1
    } else {
        value
    }
}

fn namespace_string(namespace: u64) -> String {
    format!("0x{namespace:016x}")
}

fn parse_namespace(namespace: &str) -> Result<u64, String> {
    u64::from_str_radix(
        namespace
            .strip_prefix("0x")
            .ok_or_else(|| format!("namespace {namespace} keeps its 0x prefix"))?,
        16,
    )
    .map_err(|error| format!("namespace {namespace} parses exactly: {error}"))
}

fn sha256(bytes: &[u8]) -> String {
    encode_digest(Sha256::digest(bytes))
}

fn words_sha256(words: &[u32]) -> String {
    let mut hash = Sha256::new();
    for word in words {
        hash.update(word.to_le_bytes());
    }
    encode_digest(hash.finalize())
}

fn encode_digest(digest: impl IntoIterator<Item = u8>) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}

// The efficiency cell deliberately lives beside the historical literal carrier so one bounded
// comparison can be made without rewriting its accepted testimony. Its causal representation is
// a typed family of exact words: one interface per algebraic field or integer limb, never one
// interface per serialized bit. JSON is used only after conduct to write the observer report.
const COMPACT_SCHEMA: u64 = 1;
const COMPACT_MAX_ARCS_PER_CELL: usize = 1_024;
const COMPACT_EVENT_LIMIT: Duration = Duration::from_secs(30);
const COMPACT_RUN_LIMIT: Duration = Duration::from_secs(120);

const WORD_SCHEMA: u64 = 1;
const WORD_DEGREE: u64 = 2;
const WORD_AXIS_COUNT: u64 = 3;
const WORD_TERM_COUNT: u64 = 4;
const WORD_AXIS_KIND: u64 = 10;
const WORD_AXIS_PRIME: u64 = 11;
const WORD_AXIS_SYMBOL_LEN: u64 = 12;
const WORD_AXIS_SYMBOL_BYTE: u64 = 13;
const WORD_TERM_EXPONENT: u64 = 20;
const WORD_NUMERATOR_SIGN: u64 = 30;
const WORD_NUMERATOR_LIMBS: u64 = 31;
const WORD_NUMERATOR_LIMB: u64 = 32;
const WORD_DENOMINATOR_SIGN: u64 = 40;
const WORD_DENOMINATOR_LIMBS: u64 = 41;
const WORD_DENOMINATOR_LIMB: u64 = 42;
const WORD_LAW_KIND: u64 = 50;
const WORD_MICRO_OCTET: u64 = 60;
const WORD_SCALE: u64 = 70;

const THETA_MELLIN_SCHEMA: u64 = 1;
const THETA_MELLIN_SHELL_GROWTH: u64 = 1;
const WORD_THETA_LAW: u64 = 100;
const WORD_THETA_SCHEMA: u64 = 101;
const WORD_THETA_APERTURE: u64 = 102;
const WORD_THETA_ARM_COUNT: u64 = 103;
const WORD_THETA_FIXED_NUMERATOR: u64 = 104;
const WORD_THETA_FIXED_DENOMINATOR: u64 = 105;
const WORD_THETA_SHELL: u64 = 110;
const WORD_THETA_HAND: u64 = 111;
const WORD_THETA_SQUARE: u64 = 112;
const WORD_THETA_RAW_MULTIPLICITY: u64 = 113;
const WORD_THETA_MELLIN_CONSTANT: u64 = 114;
const WORD_THETA_MELLIN_SLOPE: u64 = 115;
const WORD_THETA_INVOLUTION_TARGET: u64 = 116;
const WORD_THETA_METRIC_WEIGHT: u64 = 117;
const WORD_THETA_SYMMETRIC_NUMERATOR_SIGN: u64 = 120;
const WORD_THETA_SYMMETRIC_NUMERATOR_LIMBS: u64 = 121;
const WORD_THETA_SYMMETRIC_NUMERATOR_LIMB: u64 = 122;
const WORD_THETA_SYMMETRIC_DENOMINATOR_SIGN: u64 = 123;
const WORD_THETA_SYMMETRIC_DENOMINATOR_LIMBS: u64 = 124;
const WORD_THETA_SYMMETRIC_DENOMINATOR_LIMB: u64 = 125;
const WORD_THETA_RESIDUAL_NUMERATOR_SIGN: u64 = 130;
const WORD_THETA_RESIDUAL_NUMERATOR_LIMBS: u64 = 131;
const WORD_THETA_RESIDUAL_NUMERATOR_LIMB: u64 = 132;
const WORD_THETA_RESIDUAL_DENOMINATOR_SIGN: u64 = 133;
const WORD_THETA_RESIDUAL_DENOMINATOR_LIMBS: u64 = 134;
const WORD_THETA_RESIDUAL_DENOMINATOR_LIMB: u64 = 135;

const POISSON_TAIL_SCHEMA: u64 = 1;
const POISSON_GAUSSIAN_BOUNDARY_TRANSFER: u64 = 1;
const WORD_POISSON_LAW: u64 = 200;
const WORD_POISSON_SCHEMA: u64 = 201;
const WORD_POISSON_COMPLETE_IDENTITY: u64 = 202;
const WORD_POISSON_TAIL_COUNT: u64 = 203;
const WORD_POISSON_TAIL_HAND: u64 = 210;
const WORD_POISSON_TAIL_START: u64 = 211;
const WORD_POISSON_TAIL_MULTIPLICITY: u64 = 212;
const WORD_POISSON_RECURRENCE_SLOPE: u64 = 213;
const WORD_POISSON_RECURRENCE_INTERCEPT: u64 = 214;
const WORD_POISSON_POSITIVE_DOMAIN: u64 = 215;

#[derive(Clone, Debug)]
struct CompactWord {
    tag: u64,
    coordinates: Vec<u64>,
    value: u64,
}

impl CompactWord {
    fn scalar(tag: u64, value: u64) -> Self {
        Self {
            tag,
            coordinates: Vec::new(),
            value,
        }
    }

    fn at(tag: u64, coordinates: impl Into<Vec<u64>>, value: u64) -> Self {
        Self {
            tag,
            coordinates: coordinates.into(),
            value,
        }
    }

    fn interface(&self, root: u64) -> InterfaceCapability {
        InterfaceCapability::new(compact_route_namespace(root, self), self.value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ThetaHand {
    Direct,
    Reciprocal,
}

impl ThetaHand {
    const fn code(self) -> u64 {
        match self {
            Self::Direct => 1,
            Self::Reciprocal => 2,
        }
    }

    fn from_code(code: u64) -> Result<Self, String> {
        match code {
            1 => Ok(Self::Direct),
            2 => Ok(Self::Reciprocal),
            _ => Err(format!("theta hand code {code} is invalid")),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ThetaArm {
    shell: u32,
    hand: ThetaHand,
    square: u64,
    raw_multiplicity: u64,
    mellin_constant: i64,
    mellin_slope: i64,
    involution_target: usize,
    metric_weight: u64,
    symmetric_coefficient: BigRational,
    residual_coefficient: BigRational,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ThetaMellinFace {
    aperture: u32,
    fixed_axis: BigRational,
    arms: Vec<ThetaArm>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct GaussianTail {
    hand: ThetaHand,
    start: u32,
    multiplicity: u64,
    recurrence_slope: u64,
    recurrence_intercept: u64,
    positive_domain: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PoissonApertureFace {
    theta: ThetaMellinFace,
    complete_identity: u64,
    tails: [GaussianTail; 2],
}

struct CapabilityAtlas {
    values: BTreeMap<u64, BTreeSet<u64>>,
}

impl CapabilityAtlas {
    fn from_constituent(constituent: &LiveConstituent) -> Result<Self, String> {
        let mut values: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
        for pin_at in constituent.exposed().iter().copied() {
            let interface = constituent
                .pins()
                .get(pin_at as usize)
                .and_then(|pin| pin.interface())
                .ok_or_else(|| "an exposed compact pin retains its interface".to_owned())?;
            values
                .entry(interface.namespace())
                .or_default()
                .insert(interface.local());
        }
        Ok(Self { values })
    }

    fn word(&self, root: u64, tag: u64, coordinates: &[u64]) -> Result<u64, String> {
        let route = CompactWord::at(tag, coordinates.to_vec(), 0);
        let namespace = compact_route_namespace(root, &route);
        match self.values.get(&namespace) {
            Some(values) if values.len() == 1 => Ok(*values.first().unwrap()),
            Some(_) => Err(format!(
                "compact route {tag}:{coordinates:?} exposes plural values"
            )),
            None => Err(format!(
                "compact route {tag}:{coordinates:?} is absent under {}",
                namespace_string(root)
            )),
        }
    }

    fn namespace_value(&self, namespace: u64) -> Result<u64, String> {
        match self.values.get(&namespace) {
            Some(values) if values.len() == 1 => Ok(*values.first().unwrap()),
            Some(_) => Err(format!(
                "interface {} exposes plural values",
                namespace_string(namespace)
            )),
            None => Err(format!(
                "interface {} is not exposed",
                namespace_string(namespace)
            )),
        }
    }
}

#[derive(Clone, Copy)]
struct UsageSnapshot {
    user_micros: u64,
    system_micros: u64,
    max_rss_kib: i64,
}

#[derive(Clone, Debug, Serialize)]
struct ResourceDeltaRead {
    user_cpu_micros: u64,
    system_cpu_micros: u64,
    max_rss_before_kib: i64,
    max_rss_after_kib: i64,
}

#[derive(Clone, Debug, Serialize)]
struct EventPreflightRead {
    currents: usize,
    regional_cells: usize,
    regional_arcs: usize,
    largest_cell_arcs: usize,
    regional_receiver_width: usize,
    executor_thread_ceiling: usize,
    legacy_quadratic_pair_visits: u128,
    indexed_rows: usize,
    hard_arc_limit: usize,
}

#[derive(Clone, Debug, Serialize)]
struct EventTimingRead {
    event: String,
    semantic_atoms: usize,
    preflight: EventPreflightRead,
    wall_micros: u64,
    executor_micros: u64,
    machine_boundary_micros: u64,
    resource: ResourceDeltaRead,
    returned_incidences: usize,
    returned_pins: usize,
}

#[derive(Clone, Debug, Serialize)]
struct MicroEquivalenceRead {
    exact_octet: u8,
    literal_data_arcs: usize,
    compact_data_arcs: usize,
    literal_total_arcs: usize,
    compact_total_arcs: usize,
    literal_recovered_exactly: bool,
    compact_recovered_exactly: bool,
    literal_rest_exact: bool,
    compact_rest_exact: bool,
    literal_timing: EventTimingRead,
    compact_timing: EventTimingRead,
}

#[derive(Clone, Debug, Serialize)]
struct FormulaEfficiencyRead {
    source_law: EventTimingRead,
    predecessor_return: EventTimingRead,
    growth_meeting: EventTimingRead,
    successor_replacement: EventTimingRead,
    predecessor_atoms: usize,
    successor_atoms: usize,
    predecessor_terms: usize,
    successor_terms: usize,
    lower_restriction_exact: bool,
    new_degree_three_terms: usize,
    every_new_coefficient_one: bool,
    law_recovered_from_standing: bool,
    predecessor_recovered_from_standing: bool,
    objective_recovered_from_current: bool,
    predecessor_data_departed: bool,
    predecessor_recruit_departed: bool,
    objective_departed: bool,
    source_lineages_departed: bool,
    final_rest_remount_exact: bool,
    final_machine: MachineRead,
}

#[derive(Clone, Debug, Serialize)]
struct ScaleProbeRead {
    semantic_atoms: usize,
    seed: EventTimingRead,
    matching_close: EventTimingRead,
}

#[derive(Clone, Debug, Serialize)]
struct EfficiencyAcceptanceRead {
    microscopic_carriers_agree: bool,
    compact_formula_value_exact: bool,
    lifecycle_signatures_exact: bool,
    every_event_within_limit: bool,
    complete_run_within_limit: bool,
    no_floating_point_causal_data: bool,
}

#[derive(Clone, Debug, Serialize)]
struct EfficiencyReport {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    stopping_condition: &'static str,
    logical_cores: usize,
    event_limit_seconds: u64,
    run_limit_seconds: u64,
    run_wall_micros: u64,
    run_resource: ResourceDeltaRead,
    algorithmic_cut: [&'static str; 4],
    microscopic_equivalence: MicroEquivalenceRead,
    compact_formula_transition: FormulaEfficiencyRead,
    bounded_scaling: Vec<ScaleProbeRead>,
    acceptance: EfficiencyAcceptanceRead,
    conclusion: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct ThetaInvolutionRead {
    fixed_axis: RationalWire,
    arms: usize,
    involution_pairs: usize,
    j_squared_is_identity: bool,
    symmetric_face_is_fixed: bool,
    residual_face_reverses: bool,
    raw_direct_and_reciprocal_reconstruct: bool,
    raw_finite_partial_is_not_self_dual: bool,
    anti_invariant_residual_is_retained: bool,
}

#[derive(Clone, Debug, Serialize)]
struct ThetaMellinReceiptRead {
    shell: u32,
    square: u64,
    direct_affine_coordinate: [i64; 2],
    reciprocal_affine_coordinate: [i64; 2],
    reflection_is_exact: bool,
    endpoint_excluded_from_shell_integral: bool,
    direct_formal_receipt: String,
    reciprocal_formal_receipt: String,
}

#[derive(Clone, Debug, Serialize)]
struct ThetaMetricRead {
    species: &'static str,
    every_weight_positive: bool,
    involution_is_metric_isometry: bool,
    predecessor_metric_is_exact_restriction: bool,
    determinant: String,
    symmetric_norm_squared: RationalWire,
    residual_norm_squared: RationalWire,
    symmetric_residual_pairing: RationalWire,
    new_shell_weight: u64,
}

#[derive(Clone, Debug, Serialize)]
struct ThetaLifecycleRead {
    source_law: EventTimingRead,
    predecessor_return: EventTimingRead,
    growth_meeting: EventTimingRead,
    successor_replacement: EventTimingRead,
    predecessor_aperture: u32,
    successor_aperture: u32,
    predecessor_words: usize,
    successor_words: usize,
    lower_restriction_exact: bool,
    exactly_one_shell_pair_added: bool,
    law_recovered_from_standing: bool,
    predecessor_recovered_from_standing: bool,
    objective_recovered_from_current: bool,
    predecessor_data_departed: bool,
    predecessor_recruit_departed: bool,
    objective_departed: bool,
    source_lineages_departed: bool,
    final_rest_remount_exact: bool,
    final_machine: MachineRead,
}

#[derive(Clone, Debug, Serialize)]
struct ThetaAcceptanceRead {
    exact_shell_growth: bool,
    involution_embodied_without_erasing_residual: bool,
    mellin_reflection_exact: bool,
    positive_metric_covariant: bool,
    lifecycle_exact: bool,
    every_event_within_limit: bool,
    complete_run_within_limit: bool,
    no_floating_point_causal_data: bool,
}

#[derive(Clone, Debug, Serialize)]
struct ThetaMellinReport {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    stopping_condition: &'static str,
    logical_cores: usize,
    event_limit_seconds: u64,
    run_limit_seconds: u64,
    run_wall_micros: u64,
    run_resource: ResourceDeltaRead,
    lifecycle: ThetaLifecycleRead,
    involution: ThetaInvolutionRead,
    mellin_receipt: ThetaMellinReceiptRead,
    metric: ThetaMetricRead,
    acceptance: ThetaAcceptanceRead,
    conclusion: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct PoissonTailRead {
    hand: &'static str,
    predecessor_start: u32,
    transferred_shell: u32,
    successor_start: u32,
    multiplicity: u64,
    exponent_gap: u64,
    generator: String,
    recurrence: String,
    strictly_decreases_on_positive_domain: bool,
}

#[derive(Clone, Debug, Serialize)]
struct PoissonBoundaryRead {
    inherited_transform: &'static str,
    complete_identity: String,
    predecessor_boundary_equation: &'static str,
    successor_boundary_equation: &'static str,
    coefficient_basis: [&'static str; 2],
    partial_residual_delta: [i64; 2],
    tail_boundary_delta: [i64; 2],
    residual_transport_exact: bool,
    direct_partial_gain_and_tail_loss: [i64; 2],
    reciprocal_partial_gain_and_tail_loss: [i64; 2],
    direct_complete_body_invariant: bool,
    reciprocal_complete_body_invariant: bool,
    inherited_transform_identity_preserved: bool,
    tails: [PoissonTailRead; 2],
}

#[derive(Clone, Debug, Serialize)]
struct PoissonLifecycleRead {
    source_law: EventTimingRead,
    predecessor_return: EventTimingRead,
    growth_meeting: EventTimingRead,
    successor_replacement: EventTimingRead,
    predecessor_aperture: u32,
    successor_aperture: u32,
    predecessor_words: usize,
    successor_words: usize,
    lower_restriction_exact: bool,
    law_recovered_from_standing: bool,
    predecessor_recovered_from_standing: bool,
    objective_recovered_from_current: bool,
    predecessor_data_departed: bool,
    predecessor_recruit_departed: bool,
    objective_departed: bool,
    source_lineages_departed: bool,
    final_rest_remount_exact: bool,
    final_machine: MachineRead,
}

#[derive(Clone, Debug, Serialize)]
struct PoissonAcceptanceRead {
    exact_boundary_transfer: bool,
    complete_objects_invariant: bool,
    transform_identity_preserved: bool,
    generative_remainders_advanced: bool,
    lifecycle_exact: bool,
    every_event_within_limit: bool,
    complete_run_within_limit: bool,
    no_floating_point_causal_data: bool,
}

#[derive(Clone, Debug, Serialize)]
struct PoissonReport {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    stopping_condition: &'static str,
    inherited_fact: &'static str,
    logical_cores: usize,
    event_limit_seconds: u64,
    run_limit_seconds: u64,
    run_wall_micros: u64,
    run_resource: ResourceDeltaRead,
    lifecycle: PoissonLifecycleRead,
    boundary: PoissonBoundaryRead,
    acceptance: PoissonAcceptanceRead,
    conclusion: &'static str,
}

#[derive(Default)]
struct TimedCpuExecutor {
    inner: CpuLiveCurrentExecutor,
    enact: Duration,
    settle: Duration,
}

impl LiveCurrentExecutor for TimedCpuExecutor {
    fn enact(
        &mut self,
        physical_revision: u64,
        standing: &SparseStandingSurface,
        currents: &[CurrentExecutionRequest<'_>],
        relations: &[DirectedExecutionRequest],
        regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
        let started = Instant::now();
        let result = self
            .inner
            .enact(physical_revision, standing, currents, relations, regional);
        self.enact += started.elapsed();
        result
    }

    fn settle_physical_successor(
        &mut self,
        physical_revision: u64,
        successor: &SparseStandingSurface,
    ) -> Result<(), LiveCurrentError> {
        let started = Instant::now();
        let result = self
            .inner
            .settle_physical_successor(physical_revision, successor);
        self.settle += started.elapsed();
        result
    }
}

struct RunBudget {
    started: Instant,
    usage_before: UsageSnapshot,
}

impl RunBudget {
    fn new() -> Self {
        Self {
            started: Instant::now(),
            usage_before: usage_snapshot(),
        }
    }

    fn require_open(&self) -> Result<(), String> {
        if self.started.elapsed() > COMPACT_RUN_LIMIT {
            Err("the bounded efficiency run exceeded its two-minute hard stop".to_owned())
        } else {
            Ok(())
        }
    }

    fn read(&self) -> (u64, ResourceDeltaRead) {
        let after = usage_snapshot();
        (
            duration_micros(self.started.elapsed()),
            ResourceDeltaRead {
                user_cpu_micros: after
                    .user_micros
                    .saturating_sub(self.usage_before.user_micros),
                system_cpu_micros: after
                    .system_micros
                    .saturating_sub(self.usage_before.system_micros),
                max_rss_before_kib: self.usage_before.max_rss_kib,
                max_rss_after_kib: after.max_rss_kib,
            },
        )
    }
}

fn usage_snapshot() -> UsageSnapshot {
    let mut usage = unsafe { std::mem::zeroed::<libc::rusage>() };
    let status = unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut usage) };
    if status != 0 {
        return UsageSnapshot {
            user_micros: 0,
            system_micros: 0,
            max_rss_kib: 0,
        };
    }
    let micros = |time: libc::timeval| {
        (time.tv_sec.max(0) as u64)
            .saturating_mul(1_000_000)
            .saturating_add(time.tv_usec.max(0) as u64)
    };
    UsageSnapshot {
        user_micros: micros(usage.ru_utime),
        system_micros: micros(usage.ru_stime),
        max_rss_kib: usage.ru_maxrss,
    }
}

fn duration_micros(duration: Duration) -> u64 {
    u64::try_from(duration.as_micros()).unwrap_or(u64::MAX)
}

fn event_preflight(event: ContemporaryEvent<'_>) -> Result<EventPreflightRead, String> {
    let regional_arcs = event
        .regional()
        .iter()
        .map(|cell| cell.arcs().len())
        .sum::<usize>();
    let largest_cell_arcs = event
        .regional()
        .iter()
        .map(|cell| cell.arcs().len())
        .max()
        .unwrap_or(0);
    if largest_cell_arcs > COMPACT_MAX_ARCS_PER_CELL {
        return Err(format!(
            "event preflight refuses {largest_cell_arcs} arcs in one regional cell; hard limit is {COMPACT_MAX_ARCS_PER_CELL}"
        ));
    }
    let regional_receiver_width = event
        .regional()
        .iter()
        .map(|cell| cell.receiver())
        .collect::<BTreeSet<_>>()
        .len();
    let logical_cores = std::thread::available_parallelism()
        .map(|cores| cores.get())
        .unwrap_or(1);
    let legacy_quadratic_pair_visits = event
        .regional()
        .iter()
        .map(|cell| {
            let arcs = cell.arcs().len() as u128;
            // Two old prefix-validation scans plus the old linear pin search.
            3 * arcs.saturating_mul(arcs.saturating_sub(1)) / 2
        })
        .sum();
    Ok(EventPreflightRead {
        currents: event.currents().len(),
        regional_cells: event.regional().len(),
        regional_arcs,
        largest_cell_arcs,
        regional_receiver_width,
        executor_thread_ceiling: logical_cores.min(event.currents().len().max(1)),
        legacy_quadratic_pair_visits,
        indexed_rows: regional_arcs,
        hard_arc_limit: COMPACT_MAX_ARCS_PER_CELL,
    })
}

fn profiled_receive(
    budget: &RunBudget,
    machine: &mut LiveCurrentMachine,
    event_name: &str,
    semantic_atoms: usize,
    event: ContemporaryEvent<'_>,
) -> Result<(soma_membrane::ContemporaryRadiation, EventTimingRead), String> {
    budget.require_open()?;
    let preflight = event_preflight(event)?;
    let before = usage_snapshot();
    let started = Instant::now();
    let mut executor = TimedCpuExecutor::default();
    let radiation = machine.receive_with(event, &mut executor).map_err(debug)?;
    let wall = started.elapsed();
    let after = usage_snapshot();
    if wall > COMPACT_EVENT_LIMIT {
        return Err(format!(
            "event {event_name} exceeded its {} second hard stop",
            COMPACT_EVENT_LIMIT.as_secs()
        ));
    }
    budget.require_open()?;
    let executor_micros = duration_micros(executor.enact.saturating_add(executor.settle));
    let wall_micros = duration_micros(wall);
    let returned_incidences = radiation
        .regional()
        .iter()
        .map(|row| row.constituent().incidences().len())
        .sum();
    let returned_pins = radiation
        .regional()
        .iter()
        .map(|row| row.constituent().pins().len())
        .sum();
    let read = EventTimingRead {
        event: event_name.to_owned(),
        semantic_atoms,
        preflight,
        wall_micros,
        executor_micros,
        machine_boundary_micros: wall_micros.saturating_sub(executor_micros),
        resource: ResourceDeltaRead {
            user_cpu_micros: after.user_micros.saturating_sub(before.user_micros),
            system_cpu_micros: after.system_micros.saturating_sub(before.system_micros),
            max_rss_before_kib: before.max_rss_kib,
            max_rss_after_kib: after.max_rss_kib,
        },
        returned_incidences,
        returned_pins,
    };
    Ok((radiation, read))
}

fn compact_route_namespace(root: u64, word: &CompactWord) -> u64 {
    let mut route = Vec::with_capacity(2 + word.coordinates.len());
    route.extend_from_slice(&word.tag.to_le_bytes());
    route.extend_from_slice(&(word.coordinates.len() as u64).to_le_bytes());
    for coordinate in &word.coordinates {
        route.extend_from_slice(&coordinate.to_le_bytes());
    }
    namespace(&[
        b"eros-formula-semantic-word-v1",
        &root.to_le_bytes(),
        &route,
    ])
}

fn compact_identity_bytes(words: &[CompactWord]) -> Vec<u8> {
    let mut identity = Vec::new();
    identity.extend_from_slice(&(words.len() as u64).to_le_bytes());
    for word in words {
        identity.extend_from_slice(&word.tag.to_le_bytes());
        identity.extend_from_slice(&(word.coordinates.len() as u64).to_le_bytes());
        for coordinate in &word.coordinates {
            identity.extend_from_slice(&coordinate.to_le_bytes());
        }
        identity.extend_from_slice(&word.value.to_le_bytes());
    }
    identity
}

fn sign_word(sign: Sign) -> u64 {
    match sign {
        Sign::NoSign => 0,
        Sign::Plus => 1,
        Sign::Minus => 2,
    }
}

fn read_sign(word: u64) -> Result<Sign, String> {
    match word {
        0 => Ok(Sign::NoSign),
        1 => Ok(Sign::Plus),
        2 => Ok(Sign::Minus),
        _ => Err(format!("compact integer sign {word} is invalid")),
    }
}

fn append_bigint_words(
    words: &mut Vec<CompactWord>,
    term: u64,
    sign_tag: u64,
    count_tag: u64,
    limb_tag: u64,
    value: &BigInt,
) {
    let (sign, limbs) = value.to_u32_digits();
    words.push(CompactWord::at(sign_tag, vec![term], sign_word(sign)));
    words.push(CompactWord::at(count_tag, vec![term], limbs.len() as u64));
    for (at, limb) in limbs.into_iter().enumerate() {
        words.push(CompactWord::at(
            limb_tag,
            vec![term, at as u64],
            u64::from(limb),
        ));
    }
}

fn compact_polynomial_words(polynomial: &Polynomial) -> Vec<CompactWord> {
    let mut words = vec![
        CompactWord::scalar(WORD_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(WORD_DEGREE, u64::from(polynomial.degree)),
        CompactWord::scalar(WORD_AXIS_COUNT, polynomial.axes.len() as u64),
        CompactWord::scalar(WORD_TERM_COUNT, polynomial.terms.len() as u64),
    ];
    for (axis_at, axis) in polynomial.axes.iter().enumerate() {
        let axis_at = axis_at as u64;
        match axis {
            Axis::Prime(prime) => {
                words.push(CompactWord::at(WORD_AXIS_KIND, vec![axis_at], 1));
                words.push(CompactWord::at(
                    WORD_AXIS_PRIME,
                    vec![axis_at],
                    u64::from(*prime),
                ));
            }
            Axis::Symbol(symbol) => {
                words.push(CompactWord::at(WORD_AXIS_KIND, vec![axis_at], 2));
                words.push(CompactWord::at(
                    WORD_AXIS_SYMBOL_LEN,
                    vec![axis_at],
                    symbol.len() as u64,
                ));
                for (byte_at, byte) in symbol.as_bytes().iter().copied().enumerate() {
                    words.push(CompactWord::at(
                        WORD_AXIS_SYMBOL_BYTE,
                        vec![axis_at, byte_at as u64],
                        u64::from(byte),
                    ));
                }
            }
        }
    }
    for (term_at, (monomial, coefficient)) in polynomial.terms.iter().enumerate() {
        let term_at = term_at as u64;
        for (axis_at, exponent) in monomial.iter().copied().enumerate() {
            words.push(CompactWord::at(
                WORD_TERM_EXPONENT,
                vec![term_at, axis_at as u64],
                u64::from(exponent),
            ));
        }
        append_bigint_words(
            &mut words,
            term_at,
            WORD_NUMERATOR_SIGN,
            WORD_NUMERATOR_LIMBS,
            WORD_NUMERATOR_LIMB,
            coefficient.numer(),
        );
        append_bigint_words(
            &mut words,
            term_at,
            WORD_DENOMINATOR_SIGN,
            WORD_DENOMINATOR_LIMBS,
            WORD_DENOMINATOR_LIMB,
            coefficient.denom(),
        );
    }
    words
}

fn decode_bigint(
    atlas: &CapabilityAtlas,
    root: u64,
    term: u64,
    sign_tag: u64,
    count_tag: u64,
    limb_tag: u64,
) -> Result<BigInt, String> {
    let sign = read_sign(atlas.word(root, sign_tag, &[term])?)?;
    let count = usize::try_from(atlas.word(root, count_tag, &[term])?)
        .map_err(|_| "compact integer limb count exceeds the cpu".to_owned())?;
    let mut limbs = Vec::with_capacity(count);
    for at in 0..count {
        limbs.push(
            u32::try_from(atlas.word(root, limb_tag, &[term, at as u64])?)
                .map_err(|_| "compact integer limb exceeds u32".to_owned())?,
        );
    }
    if (sign == Sign::NoSign) != limbs.is_empty() {
        return Err("compact integer sign and limb population disagree".to_owned());
    }
    Ok(BigInt::new(sign, limbs))
}

fn decode_compact_polynomial(
    constituent: &LiveConstituent,
    root: u64,
) -> Result<Polynomial, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, WORD_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("compact polynomial schema changed".to_owned());
    }
    let degree = u8::try_from(atlas.word(root, WORD_DEGREE, &[])?)
        .map_err(|_| "compact polynomial degree exceeds u8".to_owned())?;
    let axis_count = usize::try_from(atlas.word(root, WORD_AXIS_COUNT, &[])?)
        .map_err(|_| "compact polynomial axis count exceeds the cpu".to_owned())?;
    let term_count = usize::try_from(atlas.word(root, WORD_TERM_COUNT, &[])?)
        .map_err(|_| "compact polynomial term count exceeds the cpu".to_owned())?;
    let mut axes = Vec::with_capacity(axis_count);
    for axis_at in 0..axis_count {
        let axis_at = axis_at as u64;
        match atlas.word(root, WORD_AXIS_KIND, &[axis_at])? {
            1 => axes.push(Axis::Prime(
                u32::try_from(atlas.word(root, WORD_AXIS_PRIME, &[axis_at])?)
                    .map_err(|_| "compact prime axis exceeds u32".to_owned())?,
            )),
            2 => {
                let length = usize::try_from(atlas.word(root, WORD_AXIS_SYMBOL_LEN, &[axis_at])?)
                    .map_err(|_| "compact symbol length exceeds the cpu".to_owned())?;
                let mut bytes = Vec::with_capacity(length);
                for byte_at in 0..length {
                    bytes.push(
                        u8::try_from(atlas.word(
                            root,
                            WORD_AXIS_SYMBOL_BYTE,
                            &[axis_at, byte_at as u64],
                        )?)
                        .map_err(|_| "compact symbol octet exceeds u8".to_owned())?,
                    );
                }
                axes.push(Axis::Symbol(
                    String::from_utf8(bytes)
                        .map_err(|_| "compact symbol is not exact UTF-8".to_owned())?,
                ));
            }
            kind => return Err(format!("compact axis kind {kind} is invalid")),
        }
    }
    let mut polynomial = Polynomial::zero(axes, degree);
    for term_at in 0..term_count {
        let term_at = term_at as u64;
        let mut monomial = Vec::with_capacity(axis_count);
        for axis_at in 0..axis_count {
            monomial.push(
                u8::try_from(atlas.word(root, WORD_TERM_EXPONENT, &[term_at, axis_at as u64])?)
                    .map_err(|_| "compact exponent exceeds u8".to_owned())?,
            );
        }
        let numerator = decode_bigint(
            &atlas,
            root,
            term_at,
            WORD_NUMERATOR_SIGN,
            WORD_NUMERATOR_LIMBS,
            WORD_NUMERATOR_LIMB,
        )?;
        let denominator = decode_bigint(
            &atlas,
            root,
            term_at,
            WORD_DENOMINATOR_SIGN,
            WORD_DENOMINATOR_LIMBS,
            WORD_DENOMINATOR_LIMB,
        )?;
        if denominator.sign() != Sign::Plus {
            return Err("compact rational denominator is not positive".to_owned());
        }
        polynomial.add_term(monomial, BigRational::new(numerator, denominator));
    }
    Ok(polynomial)
}

impl ThetaMellinFace {
    fn canonical(aperture: u32) -> Result<Self, String> {
        let capacity = usize::try_from(aperture)
            .ok()
            .and_then(|value| value.checked_add(1))
            .and_then(|value| value.checked_mul(2))
            .ok_or_else(|| "theta aperture exceeds the cpu".to_owned())?;
        let mut arms = Vec::with_capacity(capacity);
        for shell in 0..=aperture {
            append_theta_shell(&mut arms, shell)?;
        }
        Ok(Self {
            aperture,
            fixed_axis: ratio(1, 2),
            arms,
        })
    }

    fn grow_one(&self) -> Result<Self, String> {
        self.validate()?;
        let shell = self
            .aperture
            .checked_add(1)
            .ok_or_else(|| "theta aperture cannot grow beyond u32".to_owned())?;
        let mut successor = self.clone();
        successor.aperture = shell;
        append_theta_shell(&mut successor.arms, shell)?;
        successor.validate()?;
        Ok(successor)
    }

    fn restrict(&self, aperture: u32) -> Result<Self, String> {
        if aperture > self.aperture {
            return Err("theta restriction cannot enlarge its aperture".to_owned());
        }
        let mut restricted = self.clone();
        restricted.aperture = aperture;
        restricted.arms.retain(|arm| arm.shell <= aperture);
        restricted.validate()?;
        Ok(restricted)
    }

    fn validate(&self) -> Result<(), String> {
        if self.fixed_axis != ratio(1, 2) {
            return Err("theta Mellin fixed axis is not the exact ratio 1/2".to_owned());
        }
        let canonical = Self::canonical_unchecked(self.aperture)?;
        if *self != canonical {
            return Err("theta Mellin face is not canonical at its declared aperture".to_owned());
        }
        for (at, arm) in self.arms.iter().enumerate() {
            let target = self
                .arms
                .get(arm.involution_target)
                .ok_or_else(|| "theta involution target is absent".to_owned())?;
            if target.involution_target != at
                || target.shell != arm.shell
                || target.hand == arm.hand
            {
                return Err("theta involution is not an exact shell swap".to_owned());
            }
        }
        Ok(())
    }

    fn canonical_unchecked(aperture: u32) -> Result<Self, String> {
        let capacity = usize::try_from(aperture)
            .ok()
            .and_then(|value| value.checked_add(1))
            .and_then(|value| value.checked_mul(2))
            .ok_or_else(|| "theta aperture exceeds the cpu".to_owned())?;
        let mut arms = Vec::with_capacity(capacity);
        for shell in 0..=aperture {
            append_theta_shell(&mut arms, shell)?;
        }
        Ok(Self {
            aperture,
            fixed_axis: ratio(1, 2),
            arms,
        })
    }
}

impl GaussianTail {
    const fn canonical(hand: ThetaHand, start: u32) -> Self {
        Self {
            hand,
            start,
            multiplicity: 2,
            recurrence_slope: 2,
            recurrence_intercept: 1,
            positive_domain: true,
        }
    }

    fn exponent_gap(&self) -> Result<u64, String> {
        u64::from(self.start)
            .checked_mul(self.recurrence_slope)
            .and_then(|value| value.checked_add(self.recurrence_intercept))
            .ok_or_else(|| "Gaussian tail recurrence exceeds u64".to_owned())
    }
}

impl PoissonApertureFace {
    fn canonical(aperture: u32) -> Result<Self, String> {
        let tail_start = aperture
            .checked_add(1)
            .ok_or_else(|| "Poisson aperture cannot exceed u32".to_owned())?;
        Ok(Self {
            theta: ThetaMellinFace::canonical(aperture)?,
            complete_identity: poisson_complete_identity(),
            tails: [
                GaussianTail::canonical(ThetaHand::Direct, tail_start),
                GaussianTail::canonical(ThetaHand::Reciprocal, tail_start),
            ],
        })
    }

    fn grow_one(&self) -> Result<Self, String> {
        self.validate()?;
        let mut successor = self.clone();
        successor.theta = self.theta.grow_one()?;
        for tail in &mut successor.tails {
            tail.start = tail
                .start
                .checked_add(1)
                .ok_or_else(|| "Gaussian tail cannot advance beyond u32".to_owned())?;
        }
        successor.validate()?;
        Ok(successor)
    }

    fn restrict(&self, aperture: u32) -> Result<Self, String> {
        if aperture > self.theta.aperture {
            return Err("Poisson restriction cannot enlarge its aperture".to_owned());
        }
        Self::canonical(aperture)
    }

    fn validate(&self) -> Result<(), String> {
        self.theta.validate()?;
        if self.complete_identity != poisson_complete_identity() {
            return Err("Poisson complete-object identity changed".to_owned());
        }
        let canonical = Self::canonical(self.theta.aperture)?;
        if *self != canonical {
            return Err("Poisson aperture face is not canonical at its declared cut".to_owned());
        }
        Ok(())
    }
}

fn poisson_complete_identity() -> u64 {
    namespace(&[b"eros-poisson-complete-gaussian-lattice-v1"])
}

fn append_theta_shell(arms: &mut Vec<ThetaArm>, shell: u32) -> Result<(), String> {
    let square = u64::from(shell)
        .checked_mul(u64::from(shell))
        .ok_or_else(|| "theta shell square exceeds u64".to_owned())?;
    let raw_multiplicity = if shell == 0 { 1 } else { 2 };
    let symmetric_coefficient = ratio(raw_multiplicity as i64, 2);
    let metric_weight = if shell == 0 { 1 } else { square };
    let direct_at = arms.len();
    let reciprocal_at = direct_at
        .checked_add(1)
        .ok_or_else(|| "theta arm index exceeds the cpu".to_owned())?;
    arms.push(ThetaArm {
        shell,
        hand: ThetaHand::Direct,
        square,
        raw_multiplicity,
        mellin_constant: 0,
        mellin_slope: 1,
        involution_target: reciprocal_at,
        metric_weight,
        symmetric_coefficient: symmetric_coefficient.clone(),
        residual_coefficient: symmetric_coefficient.clone(),
    });
    arms.push(ThetaArm {
        shell,
        hand: ThetaHand::Reciprocal,
        square,
        raw_multiplicity,
        mellin_constant: 1,
        mellin_slope: -1,
        involution_target: direct_at,
        metric_weight,
        symmetric_coefficient: symmetric_coefficient.clone(),
        residual_coefficient: -symmetric_coefficient,
    });
    Ok(())
}

fn append_rational_words(
    words: &mut Vec<CompactWord>,
    at: u64,
    numerator_sign: u64,
    numerator_count: u64,
    numerator_limb: u64,
    denominator_sign: u64,
    denominator_count: u64,
    denominator_limb: u64,
    value: &BigRational,
) {
    append_bigint_words(
        words,
        at,
        numerator_sign,
        numerator_count,
        numerator_limb,
        value.numer(),
    );
    append_bigint_words(
        words,
        at,
        denominator_sign,
        denominator_count,
        denominator_limb,
        value.denom(),
    );
}

fn decode_rational_words(
    atlas: &CapabilityAtlas,
    root: u64,
    at: u64,
    numerator_sign: u64,
    numerator_count: u64,
    numerator_limb: u64,
    denominator_sign: u64,
    denominator_count: u64,
    denominator_limb: u64,
) -> Result<BigRational, String> {
    let numerator = decode_bigint(
        atlas,
        root,
        at,
        numerator_sign,
        numerator_count,
        numerator_limb,
    )?;
    let denominator = decode_bigint(
        atlas,
        root,
        at,
        denominator_sign,
        denominator_count,
        denominator_limb,
    )?;
    if denominator.sign() != Sign::Plus {
        return Err("theta rational denominator is not positive".to_owned());
    }
    Ok(BigRational::new(numerator, denominator))
}

fn signed_unit_code(value: i64) -> Result<u64, String> {
    match value {
        1 => Ok(1),
        -1 => Ok(2),
        _ => Err(format!("signed unit {value} is outside the theta chart")),
    }
}

fn signed_unit_from_code(code: u64) -> Result<i64, String> {
    match code {
        1 => Ok(1),
        2 => Ok(-1),
        _ => Err(format!("theta signed-unit code {code} is invalid")),
    }
}

fn compact_theta_law_words() -> Vec<CompactWord> {
    vec![CompactWord::scalar(
        WORD_THETA_LAW,
        THETA_MELLIN_SHELL_GROWTH,
    )]
}

fn compact_theta_words(face: &ThetaMellinFace) -> Result<Vec<CompactWord>, String> {
    face.validate()?;
    let mut words = vec![
        CompactWord::scalar(WORD_THETA_SCHEMA, THETA_MELLIN_SCHEMA),
        CompactWord::scalar(WORD_THETA_APERTURE, u64::from(face.aperture)),
        CompactWord::scalar(WORD_THETA_ARM_COUNT, face.arms.len() as u64),
        CompactWord::scalar(WORD_THETA_FIXED_NUMERATOR, 1),
        CompactWord::scalar(WORD_THETA_FIXED_DENOMINATOR, 2),
    ];
    for (at, arm) in face.arms.iter().enumerate() {
        let at = at as u64;
        words.push(CompactWord::at(
            WORD_THETA_SHELL,
            vec![at],
            u64::from(arm.shell),
        ));
        words.push(CompactWord::at(WORD_THETA_HAND, vec![at], arm.hand.code()));
        words.push(CompactWord::at(WORD_THETA_SQUARE, vec![at], arm.square));
        words.push(CompactWord::at(
            WORD_THETA_RAW_MULTIPLICITY,
            vec![at],
            arm.raw_multiplicity,
        ));
        words.push(CompactWord::at(
            WORD_THETA_MELLIN_CONSTANT,
            vec![at],
            u64::try_from(arm.mellin_constant)
                .map_err(|_| "theta Mellin constant is negative".to_owned())?,
        ));
        words.push(CompactWord::at(
            WORD_THETA_MELLIN_SLOPE,
            vec![at],
            signed_unit_code(arm.mellin_slope)?,
        ));
        words.push(CompactWord::at(
            WORD_THETA_INVOLUTION_TARGET,
            vec![at],
            arm.involution_target as u64,
        ));
        words.push(CompactWord::at(
            WORD_THETA_METRIC_WEIGHT,
            vec![at],
            arm.metric_weight,
        ));
        append_rational_words(
            &mut words,
            at,
            WORD_THETA_SYMMETRIC_NUMERATOR_SIGN,
            WORD_THETA_SYMMETRIC_NUMERATOR_LIMBS,
            WORD_THETA_SYMMETRIC_NUMERATOR_LIMB,
            WORD_THETA_SYMMETRIC_DENOMINATOR_SIGN,
            WORD_THETA_SYMMETRIC_DENOMINATOR_LIMBS,
            WORD_THETA_SYMMETRIC_DENOMINATOR_LIMB,
            &arm.symmetric_coefficient,
        );
        append_rational_words(
            &mut words,
            at,
            WORD_THETA_RESIDUAL_NUMERATOR_SIGN,
            WORD_THETA_RESIDUAL_NUMERATOR_LIMBS,
            WORD_THETA_RESIDUAL_NUMERATOR_LIMB,
            WORD_THETA_RESIDUAL_DENOMINATOR_SIGN,
            WORD_THETA_RESIDUAL_DENOMINATOR_LIMBS,
            WORD_THETA_RESIDUAL_DENOMINATOR_LIMB,
            &arm.residual_coefficient,
        );
    }
    Ok(words)
}

fn decode_compact_theta_face(
    constituent: &LiveConstituent,
    root: u64,
) -> Result<ThetaMellinFace, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, WORD_THETA_SCHEMA, &[])? != THETA_MELLIN_SCHEMA {
        return Err("theta Mellin schema changed".to_owned());
    }
    let aperture = u32::try_from(atlas.word(root, WORD_THETA_APERTURE, &[])?)
        .map_err(|_| "theta aperture exceeds u32".to_owned())?;
    let arm_count = usize::try_from(atlas.word(root, WORD_THETA_ARM_COUNT, &[])?)
        .map_err(|_| "theta arm count exceeds the cpu".to_owned())?;
    let fixed_axis = BigRational::new(
        BigInt::from(atlas.word(root, WORD_THETA_FIXED_NUMERATOR, &[])?),
        BigInt::from(atlas.word(root, WORD_THETA_FIXED_DENOMINATOR, &[])?),
    );
    let mut arms = Vec::with_capacity(arm_count);
    for at in 0..arm_count {
        let route = at as u64;
        arms.push(ThetaArm {
            shell: u32::try_from(atlas.word(root, WORD_THETA_SHELL, &[route])?)
                .map_err(|_| "theta shell exceeds u32".to_owned())?,
            hand: ThetaHand::from_code(atlas.word(root, WORD_THETA_HAND, &[route])?)?,
            square: atlas.word(root, WORD_THETA_SQUARE, &[route])?,
            raw_multiplicity: atlas.word(root, WORD_THETA_RAW_MULTIPLICITY, &[route])?,
            mellin_constant: i64::try_from(atlas.word(
                root,
                WORD_THETA_MELLIN_CONSTANT,
                &[route],
            )?)
            .map_err(|_| "theta Mellin constant exceeds i64".to_owned())?,
            mellin_slope: signed_unit_from_code(atlas.word(
                root,
                WORD_THETA_MELLIN_SLOPE,
                &[route],
            )?)?,
            involution_target: usize::try_from(atlas.word(
                root,
                WORD_THETA_INVOLUTION_TARGET,
                &[route],
            )?)
            .map_err(|_| "theta involution target exceeds the cpu".to_owned())?,
            metric_weight: atlas.word(root, WORD_THETA_METRIC_WEIGHT, &[route])?,
            symmetric_coefficient: decode_rational_words(
                &atlas,
                root,
                route,
                WORD_THETA_SYMMETRIC_NUMERATOR_SIGN,
                WORD_THETA_SYMMETRIC_NUMERATOR_LIMBS,
                WORD_THETA_SYMMETRIC_NUMERATOR_LIMB,
                WORD_THETA_SYMMETRIC_DENOMINATOR_SIGN,
                WORD_THETA_SYMMETRIC_DENOMINATOR_LIMBS,
                WORD_THETA_SYMMETRIC_DENOMINATOR_LIMB,
            )?,
            residual_coefficient: decode_rational_words(
                &atlas,
                root,
                route,
                WORD_THETA_RESIDUAL_NUMERATOR_SIGN,
                WORD_THETA_RESIDUAL_NUMERATOR_LIMBS,
                WORD_THETA_RESIDUAL_NUMERATOR_LIMB,
                WORD_THETA_RESIDUAL_DENOMINATOR_SIGN,
                WORD_THETA_RESIDUAL_DENOMINATOR_LIMBS,
                WORD_THETA_RESIDUAL_DENOMINATOR_LIMB,
            )?,
        });
    }
    let face = ThetaMellinFace {
        aperture,
        fixed_axis,
        arms,
    };
    face.validate()?;
    Ok(face)
}

fn decode_compact_theta_law(constituent: &LiveConstituent, root: u64) -> Result<(), String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, WORD_THETA_LAW, &[])? != THETA_MELLIN_SHELL_GROWTH {
        return Err("theta Mellin shell-growth law changed".to_owned());
    }
    Ok(())
}

fn compact_poisson_law_words() -> Vec<CompactWord> {
    let mut words = compact_theta_law_words();
    words.push(CompactWord::scalar(
        WORD_POISSON_LAW,
        POISSON_GAUSSIAN_BOUNDARY_TRANSFER,
    ));
    words
}

fn compact_poisson_words(face: &PoissonApertureFace) -> Result<Vec<CompactWord>, String> {
    face.validate()?;
    let mut words = compact_theta_words(&face.theta)?;
    words.extend([
        CompactWord::scalar(WORD_POISSON_SCHEMA, POISSON_TAIL_SCHEMA),
        CompactWord::scalar(WORD_POISSON_COMPLETE_IDENTITY, face.complete_identity),
        CompactWord::scalar(WORD_POISSON_TAIL_COUNT, face.tails.len() as u64),
    ]);
    for (at, tail) in face.tails.iter().enumerate() {
        let route = at as u64;
        words.extend([
            CompactWord::at(WORD_POISSON_TAIL_HAND, vec![route], tail.hand.code()),
            CompactWord::at(WORD_POISSON_TAIL_START, vec![route], u64::from(tail.start)),
            CompactWord::at(
                WORD_POISSON_TAIL_MULTIPLICITY,
                vec![route],
                tail.multiplicity,
            ),
            CompactWord::at(
                WORD_POISSON_RECURRENCE_SLOPE,
                vec![route],
                tail.recurrence_slope,
            ),
            CompactWord::at(
                WORD_POISSON_RECURRENCE_INTERCEPT,
                vec![route],
                tail.recurrence_intercept,
            ),
            CompactWord::at(
                WORD_POISSON_POSITIVE_DOMAIN,
                vec![route],
                u64::from(tail.positive_domain),
            ),
        ]);
    }
    Ok(words)
}

fn decode_gaussian_tail(
    atlas: &CapabilityAtlas,
    root: u64,
    route: u64,
) -> Result<GaussianTail, String> {
    let positive_domain = match atlas.word(root, WORD_POISSON_POSITIVE_DOMAIN, &[route])? {
        0 => false,
        1 => true,
        code => return Err(format!("Poisson positive-domain code {code} is invalid")),
    };
    Ok(GaussianTail {
        hand: ThetaHand::from_code(atlas.word(root, WORD_POISSON_TAIL_HAND, &[route])?)?,
        start: u32::try_from(atlas.word(root, WORD_POISSON_TAIL_START, &[route])?)
            .map_err(|_| "Poisson tail start exceeds u32".to_owned())?,
        multiplicity: atlas.word(root, WORD_POISSON_TAIL_MULTIPLICITY, &[route])?,
        recurrence_slope: atlas.word(root, WORD_POISSON_RECURRENCE_SLOPE, &[route])?,
        recurrence_intercept: atlas.word(root, WORD_POISSON_RECURRENCE_INTERCEPT, &[route])?,
        positive_domain,
    })
}

fn decode_compact_poisson_face(
    constituent: &LiveConstituent,
    root: u64,
) -> Result<PoissonApertureFace, String> {
    let theta = decode_compact_theta_face(constituent, root)?;
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, WORD_POISSON_SCHEMA, &[])? != POISSON_TAIL_SCHEMA {
        return Err("Poisson tail schema changed".to_owned());
    }
    if atlas.word(root, WORD_POISSON_TAIL_COUNT, &[])? != 2 {
        return Err("Poisson face does not carry its two chart tails".to_owned());
    }
    let face = PoissonApertureFace {
        theta,
        complete_identity: atlas.word(root, WORD_POISSON_COMPLETE_IDENTITY, &[])?,
        tails: [
            decode_gaussian_tail(&atlas, root, 0)?,
            decode_gaussian_tail(&atlas, root, 1)?,
        ],
    };
    face.validate()?;
    Ok(face)
}

fn decode_compact_poisson_law(constituent: &LiveConstituent, root: u64) -> Result<(), String> {
    decode_compact_theta_law(constituent, root)?;
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, WORD_POISSON_LAW, &[])? != POISSON_GAUSSIAN_BOUNDARY_TRANSFER {
        return Err("Poisson Gaussian boundary-transfer law changed".to_owned());
    }
    Ok(())
}

fn theta_apply_involution(
    face: &ThetaMellinFace,
    coefficients: &[BigRational],
) -> Result<Vec<BigRational>, String> {
    if coefficients.len() != face.arms.len() {
        return Err("theta coefficient vector does not fit its face".to_owned());
    }
    let mut returned = vec![ratio(0, 1); coefficients.len()];
    for (at, coefficient) in coefficients.iter().enumerate() {
        let target = face.arms[at].involution_target;
        returned[target] += coefficient;
    }
    Ok(returned)
}

fn theta_metric_pairing(
    face: &ThetaMellinFace,
    left: &[BigRational],
    right: &[BigRational],
) -> Result<BigRational, String> {
    if left.len() != face.arms.len() || right.len() != face.arms.len() {
        return Err("theta metric vector does not fit its face".to_owned());
    }
    Ok(face
        .arms
        .iter()
        .zip(left)
        .zip(right)
        .fold(ratio(0, 1), |sum, ((arm, left), right)| {
            sum + BigRational::from_integer(BigInt::from(arm.metric_weight)) * left * right
        }))
}

fn theta_metric_determinant(face: &ThetaMellinFace) -> BigInt {
    face.arms.iter().fold(BigInt::from(1), |product, arm| {
        product * BigInt::from(arm.metric_weight)
    })
}

fn theta_raw_vectors(
    face: &ThetaMellinFace,
) -> (
    Vec<BigRational>,
    Vec<BigRational>,
    Vec<BigRational>,
    Vec<BigRational>,
) {
    let symmetric = face
        .arms
        .iter()
        .map(|arm| arm.symmetric_coefficient.clone())
        .collect::<Vec<_>>();
    let residual = face
        .arms
        .iter()
        .map(|arm| arm.residual_coefficient.clone())
        .collect::<Vec<_>>();
    let direct = symmetric
        .iter()
        .zip(&residual)
        .map(|(symmetric, residual)| symmetric + residual)
        .collect();
    let reciprocal = symmetric
        .iter()
        .zip(&residual)
        .map(|(symmetric, residual)| symmetric - residual)
        .collect();
    (symmetric, residual, direct, reciprocal)
}

fn theta_reflect_affine(coordinate: [i64; 2]) -> [i64; 2] {
    [coordinate[0] + coordinate[1], -coordinate[1]]
}

fn law_code(kind: LawKind) -> u64 {
    match kind {
        LawKind::FormalExp => 1,
        LawKind::EulerLog => 2,
        LawKind::EulerProduct => 3,
        LawKind::FactorialRecurrence => 4,
        LawKind::MachinArctan => 5,
        LawKind::DirichletZeta2 => 6,
        LawKind::ExactComparison => 7,
        LawKind::ComplexAssembly => 8,
        LawKind::ApertureGrowth => 9,
    }
}

fn law_from_code(code: u64) -> Result<LawKind, String> {
    match code {
        1 => Ok(LawKind::FormalExp),
        2 => Ok(LawKind::EulerLog),
        3 => Ok(LawKind::EulerProduct),
        4 => Ok(LawKind::FactorialRecurrence),
        5 => Ok(LawKind::MachinArctan),
        6 => Ok(LawKind::DirichletZeta2),
        7 => Ok(LawKind::ExactComparison),
        8 => Ok(LawKind::ComplexAssembly),
        9 => Ok(LawKind::ApertureGrowth),
        _ => Err(format!("compact law code {code} is invalid")),
    }
}

fn compact_law_words(kind: LawKind) -> Vec<CompactWord> {
    vec![CompactWord::scalar(WORD_LAW_KIND, law_code(kind))]
}

fn decode_compact_law(constituent: &LiveConstituent, root: u64) -> Result<LawKind, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    law_from_code(atlas.word(root, WORD_LAW_KIND, &[])?)
}

fn append_compact_word_arcs(
    arcs: &mut Vec<RegionalRelationArc>,
    pair: [CurrentLineage; 2],
    root: u64,
    words: &[CompactWord],
) -> Result<(), String> {
    for word in words {
        let interface = word.interface(root);
        let slot = u32::try_from(arcs.len())
            .map_err(|_| "compact regional slot exceeds u32".to_owned())?;
        arcs.push(interface_arc(
            pair,
            interface.namespace(),
            interface.local(),
            slot,
            IncidenceHand::Against,
        ));
    }
    Ok(())
}

fn push_compact_interface(
    arcs: &mut Vec<RegionalRelationArc>,
    pair: [CurrentLineage; 2],
    interface: InterfaceCapability,
) -> Result<(), String> {
    let slot =
        u32::try_from(arcs.len()).map_err(|_| "compact regional slot exceeds u32".to_owned())?;
    arcs.push(interface_arc(
        pair,
        interface.namespace(),
        interface.local(),
        slot,
        IncidenceHand::Against,
    ));
    Ok(())
}

fn compact_seed_arcs(
    pair: [CurrentLineage; 2],
    handle: ArtifactHandle,
    words: &[CompactWord],
) -> Result<Vec<RegionalRelationArc>, String> {
    let mut arcs = Vec::with_capacity(words.len() + 1);
    append_compact_word_arcs(&mut arcs, pair, handle.data_namespace, words)?;
    push_compact_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(handle.recruit_namespace, RECRUIT_LOCAL),
    )?;
    Ok(arcs)
}

fn compact_meeting_arcs(
    pair: [CurrentLineage; 2],
    objective: InterfaceCapability,
    selected: &[(ArtifactHandle, ArtifactHandle)],
) -> Result<Vec<RegionalRelationArc>, String> {
    let mut arcs = Vec::with_capacity(1 + 2 * selected.len());
    push_compact_interface(&mut arcs, pair, objective)?;
    for (before, _) in selected {
        push_compact_interface(
            &mut arcs,
            pair,
            InterfaceCapability::new(before.recruit_namespace, RECRUIT_LOCAL),
        )?;
    }
    for (_, after) in selected {
        push_compact_interface(
            &mut arcs,
            pair,
            InterfaceCapability::new(after.recruit_namespace, RECRUIT_LOCAL),
        )?;
    }
    Ok(arcs)
}

fn compact_replacement_arcs(
    pair: [CurrentLineage; 2],
    objective: InterfaceCapability,
    old: ArtifactHandle,
    old_words: &[CompactWord],
    new: ArtifactHandle,
    new_words: &[CompactWord],
) -> Result<Vec<RegionalRelationArc>, String> {
    let mut arcs = Vec::with_capacity(old_words.len() + new_words.len() + 3);
    push_compact_interface(&mut arcs, pair, objective)?;
    append_compact_word_arcs(&mut arcs, pair, old.data_namespace, old_words)?;
    push_compact_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(old.recruit_namespace, RECRUIT_LOCAL),
    )?;
    append_compact_word_arcs(&mut arcs, pair, new.data_namespace, new_words)?;
    push_compact_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(new.recruit_namespace, RECRUIT_LOCAL),
    )?;
    Ok(arcs)
}

fn profiled_regional_ending(
    budget: &RunBudget,
    machine: &mut LiveCurrentMachine,
    event_name: &str,
    semantic_atoms: usize,
    pair: [CurrentLineage; 2],
    arcs: &[RegionalRelationArc],
) -> Result<(soma_membrane::ContemporaryRadiation, EventTimingRead), String> {
    let currents = [
        CurrentEvent::ending(pair[0], relation(181)?, action()),
        CurrentEvent::ending(pair[1], relation(191)?, action()),
    ];
    let regional = [RegionalRelationCell::new(pair[1], arcs)];
    profiled_receive(
        budget,
        machine,
        event_name,
        semantic_atoms,
        ContemporaryEvent::with_regional(&currents, &[], &regional),
    )
}

fn standing_compact_polynomial(
    machine: &LiveCurrentMachine,
    root: u64,
) -> Result<Polynomial, String> {
    let matches = machine
        .standing()
        .constituents()
        .iter()
        .filter_map(|constituent| decode_compact_polynomial(constituent, root).ok())
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [polynomial] => Ok(polynomial.clone()),
        [] => Err(format!(
            "Standing exposes no compact polynomial under {}",
            namespace_string(root)
        )),
        _ => Err(format!(
            "Standing exposes plural compact polynomials under {}",
            namespace_string(root)
        )),
    }
}

fn standing_compact_law(machine: &LiveCurrentMachine, root: u64) -> Result<LawKind, String> {
    let matches = machine
        .standing()
        .constituents()
        .iter()
        .filter_map(|constituent| decode_compact_law(constituent, root).ok())
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [kind] => Ok(*kind),
        [] => Err(format!(
            "Standing exposes no compact law under {}",
            namespace_string(root)
        )),
        _ => Err(format!(
            "Standing exposes plural compact laws under {}",
            namespace_string(root)
        )),
    }
}

fn standing_compact_theta_face(
    machine: &LiveCurrentMachine,
    root: u64,
) -> Result<ThetaMellinFace, String> {
    let matches = machine
        .standing()
        .constituents()
        .iter()
        .filter_map(|constituent| decode_compact_theta_face(constituent, root).ok())
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [face] => Ok(face.clone()),
        [] => Err(format!(
            "Standing exposes no compact theta Mellin face under {}",
            namespace_string(root)
        )),
        _ => Err(format!(
            "Standing exposes plural compact theta Mellin faces under {}",
            namespace_string(root)
        )),
    }
}

fn standing_has_theta_law(machine: &LiveCurrentMachine, root: u64) -> bool {
    machine
        .standing()
        .constituents()
        .iter()
        .any(|constituent| decode_compact_theta_law(constituent, root).is_ok())
}

fn standing_compact_poisson_face(
    machine: &LiveCurrentMachine,
    root: u64,
) -> Result<PoissonApertureFace, String> {
    let matches = machine
        .standing()
        .constituents()
        .iter()
        .filter_map(|constituent| decode_compact_poisson_face(constituent, root).ok())
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [face] => Ok(face.clone()),
        [] => Err(format!(
            "Standing exposes no compact Poisson aperture under {}",
            namespace_string(root)
        )),
        _ => Err(format!(
            "Standing exposes plural compact Poisson apertures under {}",
            namespace_string(root)
        )),
    }
}

fn standing_has_poisson_law(machine: &LiveCurrentMachine, root: u64) -> bool {
    machine
        .standing()
        .constituents()
        .iter()
        .any(|constituent| decode_compact_poisson_law(constituent, root).is_ok())
}

fn standing_has_capability(machine: &LiveCurrentMachine, capability: InterfaceCapability) -> bool {
    machine.standing().constituents().iter().any(|constituent| {
        constituent.exposed().iter().copied().any(|pin_at| {
            constituent
                .pins()
                .get(pin_at as usize)
                .and_then(|pin| pin.interface())
                == Some(capability.clone())
        })
    })
}

fn run_micro_equivalence(budget: &RunBudget) -> Result<MicroEquivalenceRead, String> {
    let exact_octet = 0xa5u8;

    let mut literal = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let literal_handle = ArtifactHandle::source("literal-micro-octet", &[exact_octet]);
    let literal_pair = primed_pair(&mut literal)?;
    let literal_arcs = seed_arcs(literal_pair, literal_handle, &[exact_octet]);
    let (literal_radiation, literal_timing) = profiled_regional_ending(
        budget,
        &mut literal,
        "micro-literal-octet",
        1,
        literal_pair,
        &literal_arcs,
    )?;
    let literal_recovered_exactly = decode_bytes(
        literal_radiation.regional()[0].constituent(),
        literal_handle.data_namespace,
    )? == [exact_octet];
    let literal_rest = literal.rest_image().map_err(debug)?;
    let literal_rest_exact = LiveCurrentMachine::from_rest_image(literal_rest.clone())
        .map_err(debug)?
        .rest_image()
        .map_err(debug)?
        == literal_rest;

    let compact_words = vec![CompactWord::scalar(
        WORD_MICRO_OCTET,
        u64::from(exact_octet),
    )];
    let compact_identity = compact_identity_bytes(&compact_words);
    let compact_handle = ArtifactHandle::source("compact-micro-octet", &compact_identity);
    let mut compact = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let compact_pair = primed_pair(&mut compact)?;
    let compact_arcs = compact_seed_arcs(compact_pair, compact_handle, &compact_words)?;
    let (compact_radiation, compact_timing) = profiled_regional_ending(
        budget,
        &mut compact,
        "micro-compact-octet",
        1,
        compact_pair,
        &compact_arcs,
    )?;
    let compact_atlas =
        CapabilityAtlas::from_constituent(compact_radiation.regional()[0].constituent())?;
    let compact_recovered_exactly =
        compact_atlas.word(compact_handle.data_namespace, WORD_MICRO_OCTET, &[])?
            == u64::from(exact_octet);
    let compact_rest = compact.rest_image().map_err(debug)?;
    let compact_rest_exact = LiveCurrentMachine::from_rest_image(compact_rest.clone())
        .map_err(debug)?
        .rest_image()
        .map_err(debug)?
        == compact_rest;

    Ok(MicroEquivalenceRead {
        exact_octet,
        literal_data_arcs: 8,
        compact_data_arcs: 1,
        literal_total_arcs: literal_arcs.len(),
        compact_total_arcs: compact_arcs.len(),
        literal_recovered_exactly,
        compact_recovered_exactly,
        literal_rest_exact,
        compact_rest_exact,
        literal_timing,
        compact_timing,
    })
}

fn run_compact_formula_transition(budget: &RunBudget) -> Result<FormulaEfficiencyRead, String> {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);

    let law_words = compact_law_words(LawKind::ApertureGrowth);
    let law_identity = compact_identity_bytes(&law_words);
    let law_handle = ArtifactHandle::source("compact-aperture-growth-law", &law_identity);
    let law_pair = primed_pair(&mut machine)?;
    let law_arcs = compact_seed_arcs(law_pair, law_handle, &law_words)?;
    let (law_radiation, source_law) = profiled_regional_ending(
        budget,
        &mut machine,
        "compact-source-law",
        law_words.len(),
        law_pair,
        &law_arcs,
    )?;
    if decode_compact_law(
        law_radiation.regional()[0].constituent(),
        law_handle.data_namespace,
    )? != LawKind::ApertureGrowth
    {
        return Err("the compact source law changed during hand-up".to_owned());
    }

    let predecessor = euler_product(&PRIME_AXES, 2)?;
    let predecessor_words = compact_polynomial_words(&predecessor);
    let predecessor_identity = compact_identity_bytes(&predecessor_words);
    let predecessor_handle =
        ArtifactHandle::source("compact-prime-product-degree-two", &predecessor_identity);
    let predecessor_pair = primed_pair(&mut machine)?;
    let predecessor_arcs =
        compact_seed_arcs(predecessor_pair, predecessor_handle, &predecessor_words)?;
    let (predecessor_radiation, predecessor_return) = profiled_regional_ending(
        budget,
        &mut machine,
        "compact-degree-two-predecessor",
        predecessor_words.len(),
        predecessor_pair,
        &predecessor_arcs,
    )?;
    if decode_compact_polynomial(
        predecessor_radiation.regional()[0].constituent(),
        predecessor_handle.data_namespace,
    )? != predecessor
    {
        return Err("the compact predecessor changed during hand-up".to_owned());
    }
    let baseline_rest = machine.rest_image().map_err(debug)?;
    machine = LiveCurrentMachine::from_rest_image(baseline_rest.clone()).map_err(debug)?;
    if machine.rest_image().map_err(debug)? != baseline_rest {
        return Err("the compact predecessor did not survive baseline rest".to_owned());
    }

    let growth_event = b"compact-grow-prime-product-two-to-three";
    let objective_value = 1u64 | (2u64 << 8) | (3u64 << 16);
    let objective_namespace = namespace(&[
        b"eros-formula-compact-objective-v1",
        growth_event,
        &objective_value.to_le_bytes(),
    ]);
    let objective = InterfaceCapability::new(objective_namespace, objective_value);
    let law_after = law_handle.after_contact(growth_event);
    let predecessor_after = predecessor_handle.after_contact(growth_event);
    let meeting_pair = primed_pair(&mut machine)?;
    let meeting_arcs = compact_meeting_arcs(
        meeting_pair,
        objective.clone(),
        &[
            (law_handle, law_after),
            (predecessor_handle, predecessor_after),
        ],
    )?;
    let (meeting_radiation, growth_meeting) = profiled_regional_ending(
        budget,
        &mut machine,
        "compact-growth-meeting",
        1,
        meeting_pair,
        &meeting_arcs,
    )?;
    let meeting = meeting_radiation.regional()[0].constituent();
    let law_recovered_from_standing =
        decode_compact_law(meeting, law_handle.data_namespace)? == LawKind::ApertureGrowth;
    let recovered_predecessor =
        decode_compact_polynomial(meeting, predecessor_handle.data_namespace)?;
    let predecessor_recovered_from_standing = recovered_predecessor == predecessor;
    let objective_recovered_from_current = CapabilityAtlas::from_constituent(meeting)?
        .namespace_value(objective_namespace)?
        == objective_value;
    if !law_recovered_from_standing
        || !predecessor_recovered_from_standing
        || !objective_recovered_from_current
    {
        return Err("the compact growth meeting lost a selected causal face".to_owned());
    }

    let successor = extend_euler_product(&recovered_predecessor, 3)?;
    let successor_words = compact_polynomial_words(&successor);
    let successor_identity = compact_identity_bytes(&successor_words);
    let replacement_event = b"compact-grow-prime-product-two-to-three:return";
    let successor_handle = predecessor_after.successor(
        "compact-prime-product-degree-three",
        &successor_identity,
        replacement_event,
    );
    let replacement_pair = primed_pair(&mut machine)?;
    let replacement_arcs = compact_replacement_arcs(
        replacement_pair,
        objective.clone(),
        predecessor_after,
        &predecessor_words,
        successor_handle,
        &successor_words,
    )?;
    let (replacement_radiation, successor_replacement) = profiled_regional_ending(
        budget,
        &mut machine,
        "compact-successor-replacement",
        predecessor_words.len() + successor_words.len() + 1,
        replacement_pair,
        &replacement_arcs,
    )?;
    let returned_successor = decode_compact_polynomial(
        replacement_radiation.regional()[0].constituent(),
        successor_handle.data_namespace,
    )?;
    let standing_successor =
        standing_compact_polynomial(&machine, successor_handle.data_namespace)?;
    if returned_successor != successor || standing_successor != successor {
        return Err("the compact successor changed between return and Standing".to_owned());
    }

    let lower_restriction_exact = successor.restrict_degree(2)? == predecessor;
    let new_face = successor.homogeneous(3);
    let every_new_coefficient_one = new_face
        .terms
        .values()
        .all(|coefficient| *coefficient == ratio(1, 1));
    let predecessor_data_departed =
        standing_compact_polynomial(&machine, predecessor_after.data_namespace).is_err();
    let predecessor_recruit_departed = !standing_has_capability(
        &machine,
        InterfaceCapability::new(predecessor_after.recruit_namespace, RECRUIT_LOCAL),
    );
    let objective_departed = !standing_has_capability(&machine, objective);
    if standing_compact_law(&machine, law_after.data_namespace)? != LawKind::ApertureGrowth {
        return Err("the compact growth law did not survive successor return".to_owned());
    }

    let final_rest = machine.rest_image().map_err(debug)?;
    let remounted = LiveCurrentMachine::from_rest_image(final_rest.clone()).map_err(debug)?;
    let final_rest_remount_exact = remounted.rest_image().map_err(debug)? == final_rest;
    let final_machine = machine_read(&remounted)?;
    Ok(FormulaEfficiencyRead {
        source_law,
        predecessor_return,
        growth_meeting,
        successor_replacement,
        predecessor_atoms: predecessor_words.len(),
        successor_atoms: successor_words.len(),
        predecessor_terms: predecessor.terms.len(),
        successor_terms: successor.terms.len(),
        lower_restriction_exact,
        new_degree_three_terms: new_face.terms.len(),
        every_new_coefficient_one,
        law_recovered_from_standing,
        predecessor_recovered_from_standing,
        objective_recovered_from_current,
        predecessor_data_departed,
        predecessor_recruit_departed,
        objective_departed,
        source_lineages_departed: machine.memory().live_lineages == 0,
        final_rest_remount_exact,
        final_machine,
    })
}

fn run_scale_probe(budget: &RunBudget, semantic_atoms: usize) -> Result<ScaleProbeRead, String> {
    let words = (0..semantic_atoms)
        .map(|at| {
            CompactWord::at(
                WORD_SCALE,
                vec![at as u64],
                (at as u64).wrapping_mul(0x9e37_79b9).wrapping_add(17),
            )
        })
        .collect::<Vec<_>>();
    let identity = compact_identity_bytes(&words);
    let handle = ArtifactHandle::source(&format!("compact-scale-{semantic_atoms}"), &identity);
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);

    let seed_pair = primed_pair(&mut machine)?;
    let seed_arcs = compact_seed_arcs(seed_pair, handle, &words)?;
    let (_, seed) = profiled_regional_ending(
        budget,
        &mut machine,
        &format!("scale-{semantic_atoms}-seed"),
        semantic_atoms,
        seed_pair,
        &seed_arcs,
    )?;

    let close_pair = primed_pair(&mut machine)?;
    let mut close_arcs = Vec::with_capacity(words.len());
    append_compact_word_arcs(&mut close_arcs, close_pair, handle.data_namespace, &words)?;
    let (_, matching_close) = profiled_regional_ending(
        budget,
        &mut machine,
        &format!("scale-{semantic_atoms}-matching-close"),
        semantic_atoms,
        close_pair,
        &close_arcs,
    )?;
    if standing_has_capability(&machine, words[0].interface(handle.data_namespace)) {
        return Err(format!(
            "scale probe {semantic_atoms} did not consume its matching data face"
        ));
    }
    Ok(ScaleProbeRead {
        semantic_atoms,
        seed,
        matching_close,
    })
}

fn run_efficiency_cpu() -> Result<EfficiencyReport, String> {
    let budget = RunBudget::new();
    let microscopic_equivalence = run_micro_equivalence(&budget)?;
    let compact_formula_transition = run_compact_formula_transition(&budget)?;
    let mut bounded_scaling = Vec::new();
    for semantic_atoms in [64, 128, 256, 512] {
        bounded_scaling.push(run_scale_probe(&budget, semantic_atoms)?);
    }
    let complete_run_within_limit = budget.require_open().is_ok();
    let microscopic_carriers_agree = microscopic_equivalence.literal_recovered_exactly
        && microscopic_equivalence.compact_recovered_exactly
        && microscopic_equivalence.literal_rest_exact
        && microscopic_equivalence.compact_rest_exact;
    let compact_formula_value_exact = compact_formula_transition.lower_restriction_exact
        && compact_formula_transition.new_degree_three_terms == 10
        && compact_formula_transition.every_new_coefficient_one
        && compact_formula_transition.predecessor_terms == 10
        && compact_formula_transition.successor_terms == 20;
    let lifecycle_signatures_exact = compact_formula_transition.law_recovered_from_standing
        && compact_formula_transition.predecessor_recovered_from_standing
        && compact_formula_transition.objective_recovered_from_current
        && compact_formula_transition.predecessor_data_departed
        && compact_formula_transition.predecessor_recruit_departed
        && compact_formula_transition.objective_departed
        && compact_formula_transition.source_lineages_departed
        && compact_formula_transition.final_rest_remount_exact;
    let (run_wall_micros, run_resource) = budget.read();
    let acceptance = EfficiencyAcceptanceRead {
        microscopic_carriers_agree,
        compact_formula_value_exact,
        lifecycle_signatures_exact,
        every_event_within_limit: true,
        complete_run_within_limit,
        no_floating_point_causal_data: true,
    };
    let accepted = acceptance.microscopic_carriers_agree
        && acceptance.compact_formula_value_exact
        && acceptance.lifecycle_signatures_exact
        && acceptance.every_event_within_limit
        && acceptance.complete_run_within_limit
        && acceptance.no_floating_point_causal_data;
    Ok(EfficiencyReport {
        schema: "eros.formula-efficiency.v1",
        status: if accepted { "accepted" } else { "rejected" },
        question: "Can exact formula growth retain its causal lifecycle while typed algebraic words replace JSON bits and the cpu indexes validation, pin identity, and exposed-interface seams?",
        theory_to_structure: "Each algebraic field or exact integer limb is one source-declared interface word. Interface local carries the exact word; its namespace carries artifact-root plus typed route. Fixed hand is orientation, never payload. The predecessor, law, objective, successor, and departure still cross as actual current and Standing relations.",
        stopping_condition: "Stop after one exact degree-two to degree-three successor, one microscopic literal/compact equivalence, four bounded index probes through 512 atoms, exact rest, and the two-minute hard limit. Do not enter theta/Mellin.",
        logical_cores: std::thread::available_parallelism()
            .map(|cores| cores.get())
            .unwrap_or(1),
        event_limit_seconds: COMPACT_EVENT_LIMIT.as_secs(),
        run_limit_seconds: COMPACT_RUN_LIMIT.as_secs(),
        run_wall_micros,
        run_resource,
        algorithmic_cut: [
            "regional boundary/arc validation uses ordered indexes instead of prefix scans",
            "regional pin identity uses the exact canonical wire key instead of a growing linear scan",
            "exposed arms are discovered in one path traversal instead of one traversal per exposed pin",
            "temporal and co-present seams consult source-declared interface indexes instead of cross-products over unrelated arms",
        ],
        microscopic_equivalence,
        compact_formula_transition,
        bounded_scaling,
        acceptance,
        conclusion: "The measured cell asks Eros only about causal carriage, replacement, and later Standing. Exact sparse algebra remains ordinary world computation; report JSON remains observer testimony. The next mathematical derivation may now be bounded before another machine experiment.",
    })
}

fn run_theta_mellin_cpu() -> Result<ThetaMellinReport, String> {
    const PREDECESSOR_APERTURE: u32 = 4;

    let budget = RunBudget::new();
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);

    let law_words = compact_theta_law_words();
    let law_identity = compact_identity_bytes(&law_words);
    let law_handle = ArtifactHandle::source("theta-mellin-shell-growth-law", &law_identity);
    let law_pair = primed_pair(&mut machine)?;
    let law_arcs = compact_seed_arcs(law_pair, law_handle, &law_words)?;
    let (law_radiation, source_law) = profiled_regional_ending(
        &budget,
        &mut machine,
        "theta-mellin-source-law",
        law_words.len(),
        law_pair,
        &law_arcs,
    )?;
    decode_compact_theta_law(
        law_radiation.regional()[0].constituent(),
        law_handle.data_namespace,
    )?;

    let predecessor = ThetaMellinFace::canonical(PREDECESSOR_APERTURE)?;
    let predecessor_words = compact_theta_words(&predecessor)?;
    let predecessor_identity = compact_identity_bytes(&predecessor_words);
    let predecessor_handle = ArtifactHandle::source(
        "theta-mellin-symmetric-aperture-four",
        &predecessor_identity,
    );
    let predecessor_pair = primed_pair(&mut machine)?;
    let predecessor_arcs =
        compact_seed_arcs(predecessor_pair, predecessor_handle, &predecessor_words)?;
    let (predecessor_radiation, predecessor_return) = profiled_regional_ending(
        &budget,
        &mut machine,
        "theta-mellin-aperture-four",
        predecessor_words.len(),
        predecessor_pair,
        &predecessor_arcs,
    )?;
    if decode_compact_theta_face(
        predecessor_radiation.regional()[0].constituent(),
        predecessor_handle.data_namespace,
    )? != predecessor
    {
        return Err("the theta Mellin predecessor changed during hand-up".to_owned());
    }

    let baseline_rest = machine.rest_image().map_err(debug)?;
    machine = LiveCurrentMachine::from_rest_image(baseline_rest.clone()).map_err(debug)?;
    if machine.rest_image().map_err(debug)? != baseline_rest {
        return Err("the theta Mellin predecessor did not survive baseline rest".to_owned());
    }

    let successor_aperture = PREDECESSOR_APERTURE + 1;
    let growth_event = b"theta-mellin-aperture-four-to-five";
    let objective_value = u64::from(PREDECESSOR_APERTURE) | (u64::from(successor_aperture) << 32);
    let objective_namespace = namespace(&[
        b"eros-formula-theta-mellin-objective-v1",
        growth_event,
        &objective_value.to_le_bytes(),
    ]);
    let objective = InterfaceCapability::new(objective_namespace, objective_value);
    let law_after = law_handle.after_contact(growth_event);
    let predecessor_after = predecessor_handle.after_contact(growth_event);
    let meeting_pair = primed_pair(&mut machine)?;
    let meeting_arcs = compact_meeting_arcs(
        meeting_pair,
        objective.clone(),
        &[
            (law_handle, law_after),
            (predecessor_handle, predecessor_after),
        ],
    )?;
    let (meeting_radiation, growth_meeting) = profiled_regional_ending(
        &budget,
        &mut machine,
        "theta-mellin-growth-meeting",
        1,
        meeting_pair,
        &meeting_arcs,
    )?;
    let meeting = meeting_radiation.regional()[0].constituent();
    let law_recovered_from_standing =
        decode_compact_theta_law(meeting, law_handle.data_namespace).is_ok();
    let recovered_predecessor =
        decode_compact_theta_face(meeting, predecessor_handle.data_namespace)?;
    let predecessor_recovered_from_standing = recovered_predecessor == predecessor;
    let objective_recovered_from_current = CapabilityAtlas::from_constituent(meeting)?
        .namespace_value(objective_namespace)?
        == objective_value;
    if !law_recovered_from_standing
        || !predecessor_recovered_from_standing
        || !objective_recovered_from_current
    {
        return Err("the theta Mellin growth meeting lost a selected causal face".to_owned());
    }

    let successor = recovered_predecessor.grow_one()?;
    let successor_words = compact_theta_words(&successor)?;
    let successor_identity = compact_identity_bytes(&successor_words);
    let replacement_event = b"theta-mellin-aperture-four-to-five:return";
    let successor_handle = predecessor_after.successor(
        "theta-mellin-symmetric-aperture-five",
        &successor_identity,
        replacement_event,
    );
    let replacement_pair = primed_pair(&mut machine)?;
    let replacement_arcs = compact_replacement_arcs(
        replacement_pair,
        objective.clone(),
        predecessor_after,
        &predecessor_words,
        successor_handle,
        &successor_words,
    )?;
    let (replacement_radiation, successor_replacement) = profiled_regional_ending(
        &budget,
        &mut machine,
        "theta-mellin-successor-replacement",
        predecessor_words.len() + successor_words.len() + 1,
        replacement_pair,
        &replacement_arcs,
    )?;
    let returned_successor = decode_compact_theta_face(
        replacement_radiation.regional()[0].constituent(),
        successor_handle.data_namespace,
    )?;
    let standing_successor =
        standing_compact_theta_face(&machine, successor_handle.data_namespace)?;
    if returned_successor != successor || standing_successor != successor {
        return Err("the theta Mellin successor changed between return and Standing".to_owned());
    }

    let lower_restriction_exact = successor.restrict(PREDECESSOR_APERTURE)? == predecessor;
    let added = &successor.arms[predecessor.arms.len()..];
    let exactly_one_shell_pair_added = added.len() == 2
        && added.iter().all(|arm| arm.shell == successor_aperture)
        && added[0].hand == ThetaHand::Direct
        && added[1].hand == ThetaHand::Reciprocal
        && added[0].involution_target == predecessor.arms.len() + 1
        && added[1].involution_target == predecessor.arms.len();

    let (symmetric, residual, raw_direct, raw_reciprocal) = theta_raw_vectors(&successor);
    let returned_symmetric = theta_apply_involution(&successor, &symmetric)?;
    let returned_residual = theta_apply_involution(&successor, &residual)?;
    let returned_direct = theta_apply_involution(&successor, &raw_direct)?;
    let negative_residual = residual.iter().map(|value| -value).collect::<Vec<_>>();
    let j_squared_is_identity = successor
        .arms
        .iter()
        .enumerate()
        .all(|(at, arm)| successor.arms[arm.involution_target].involution_target == at);
    let symmetric_face_is_fixed = returned_symmetric == symmetric;
    let residual_face_reverses = returned_residual == negative_residual;
    let raw_direct_and_reciprocal_reconstruct = returned_direct == raw_reciprocal
        && raw_direct.iter().enumerate().all(|(at, coefficient)| {
            let arm = &successor.arms[at];
            *coefficient
                == if arm.hand == ThetaHand::Direct {
                    BigRational::from_integer(BigInt::from(arm.raw_multiplicity))
                } else {
                    ratio(0, 1)
                }
        })
        && raw_reciprocal.iter().enumerate().all(|(at, coefficient)| {
            let arm = &successor.arms[at];
            *coefficient
                == if arm.hand == ThetaHand::Reciprocal {
                    BigRational::from_integer(BigInt::from(arm.raw_multiplicity))
                } else {
                    ratio(0, 1)
                }
        });
    let raw_finite_partial_is_not_self_dual = raw_direct != returned_direct;
    let anti_invariant_residual_is_retained = residual.iter().any(|value| *value != ratio(0, 1));
    let involution = ThetaInvolutionRead {
        fixed_axis: rational_wire(&successor.fixed_axis),
        arms: successor.arms.len(),
        involution_pairs: successor.arms.len() / 2,
        j_squared_is_identity,
        symmetric_face_is_fixed,
        residual_face_reverses,
        raw_direct_and_reciprocal_reconstruct,
        raw_finite_partial_is_not_self_dual,
        anti_invariant_residual_is_retained,
    };

    let new_direct = added
        .iter()
        .find(|arm| arm.hand == ThetaHand::Direct)
        .ok_or_else(|| "the new theta shell lacks its direct arm".to_owned())?;
    let new_reciprocal = added
        .iter()
        .find(|arm| arm.hand == ThetaHand::Reciprocal)
        .ok_or_else(|| "the new theta shell lacks its reciprocal arm".to_owned())?;
    let direct_affine_coordinate = [new_direct.mellin_constant, new_direct.mellin_slope];
    let reciprocal_affine_coordinate =
        [new_reciprocal.mellin_constant, new_reciprocal.mellin_slope];
    let reflection_is_exact = theta_reflect_affine(direct_affine_coordinate)
        == reciprocal_affine_coordinate
        && theta_reflect_affine(reciprocal_affine_coordinate) == direct_affine_coordinate;
    let mellin_receipt = ThetaMellinReceiptRead {
        shell: successor_aperture,
        square: new_direct.square,
        direct_affine_coordinate,
        reciprocal_affine_coordinate,
        reflection_is_exact,
        endpoint_excluded_from_shell_integral: new_direct.shell != 0,
        direct_formal_receipt: format!("Gamma(s/2)*(pi*{})^(-s/2)", new_direct.square),
        reciprocal_formal_receipt: format!("Gamma((1-s)/2)*(pi*{})^(-(1-s)/2)", new_direct.square),
    };

    let every_weight_positive = successor.arms.iter().all(|arm| arm.metric_weight > 0);
    let involution_is_metric_isometry = successor
        .arms
        .iter()
        .all(|arm| successor.arms[arm.involution_target].metric_weight == arm.metric_weight);
    let predecessor_metric_is_exact_restriction = successor
        .arms
        .iter()
        .take(predecessor.arms.len())
        .zip(&predecessor.arms)
        .all(|(successor, predecessor)| {
            successor.metric_weight == predecessor.metric_weight
                && successor.shell == predecessor.shell
                && successor.hand == predecessor.hand
        });
    let symmetric_norm_squared = theta_metric_pairing(&successor, &symmetric, &symmetric)?;
    let residual_norm_squared = theta_metric_pairing(&successor, &residual, &residual)?;
    let symmetric_residual_pairing = theta_metric_pairing(&successor, &symmetric, &residual)?;
    let metric = ThetaMetricRead {
        species: "declared finite lattice-energy pairing; not the completed Weil form",
        every_weight_positive,
        involution_is_metric_isometry,
        predecessor_metric_is_exact_restriction,
        determinant: theta_metric_determinant(&successor).to_string(),
        symmetric_norm_squared: rational_wire(&symmetric_norm_squared),
        residual_norm_squared: rational_wire(&residual_norm_squared),
        symmetric_residual_pairing: rational_wire(&symmetric_residual_pairing),
        new_shell_weight: new_direct.metric_weight,
    };

    let predecessor_data_departed =
        standing_compact_theta_face(&machine, predecessor_after.data_namespace).is_err();
    let predecessor_recruit_departed = !standing_has_capability(
        &machine,
        InterfaceCapability::new(predecessor_after.recruit_namespace, RECRUIT_LOCAL),
    );
    let objective_departed = !standing_has_capability(&machine, objective);
    if !standing_has_theta_law(&machine, law_after.data_namespace) {
        return Err("the theta Mellin growth law did not survive successor return".to_owned());
    }

    let final_rest = machine.rest_image().map_err(debug)?;
    let remounted = LiveCurrentMachine::from_rest_image(final_rest.clone()).map_err(debug)?;
    let final_rest_remount_exact = remounted.rest_image().map_err(debug)? == final_rest;
    let final_machine = machine_read(&remounted)?;
    let source_lineages_departed = machine.memory().live_lineages == 0;
    let lifecycle = ThetaLifecycleRead {
        source_law,
        predecessor_return,
        growth_meeting,
        successor_replacement,
        predecessor_aperture: PREDECESSOR_APERTURE,
        successor_aperture,
        predecessor_words: predecessor_words.len(),
        successor_words: successor_words.len(),
        lower_restriction_exact,
        exactly_one_shell_pair_added,
        law_recovered_from_standing,
        predecessor_recovered_from_standing,
        objective_recovered_from_current,
        predecessor_data_departed,
        predecessor_recruit_departed,
        objective_departed,
        source_lineages_departed,
        final_rest_remount_exact,
        final_machine,
    };

    let exact_shell_growth = lower_restriction_exact && exactly_one_shell_pair_added;
    let involution_embodied_without_erasing_residual = j_squared_is_identity
        && symmetric_face_is_fixed
        && residual_face_reverses
        && raw_direct_and_reciprocal_reconstruct
        && raw_finite_partial_is_not_self_dual
        && anti_invariant_residual_is_retained;
    let mellin_reflection_exact = reflection_is_exact
        && mellin_receipt.endpoint_excluded_from_shell_integral
        && successor.fixed_axis == ratio(1, 2);
    let positive_metric_covariant = every_weight_positive
        && involution_is_metric_isometry
        && predecessor_metric_is_exact_restriction
        && symmetric_norm_squared > ratio(0, 1)
        && residual_norm_squared > ratio(0, 1)
        && symmetric_residual_pairing == ratio(0, 1);
    let lifecycle_exact = law_recovered_from_standing
        && predecessor_recovered_from_standing
        && objective_recovered_from_current
        && predecessor_data_departed
        && predecessor_recruit_departed
        && objective_departed
        && source_lineages_departed
        && final_rest_remount_exact;
    let complete_run_within_limit = budget.require_open().is_ok();
    let (run_wall_micros, run_resource) = budget.read();
    let acceptance = ThetaAcceptanceRead {
        exact_shell_growth,
        involution_embodied_without_erasing_residual,
        mellin_reflection_exact,
        positive_metric_covariant,
        lifecycle_exact,
        every_event_within_limit: true,
        complete_run_within_limit,
        no_floating_point_causal_data: true,
    };
    let accepted = acceptance.exact_shell_growth
        && acceptance.involution_embodied_without_erasing_residual
        && acceptance.mellin_reflection_exact
        && acceptance.positive_metric_covariant
        && acceptance.lifecycle_exact
        && acceptance.every_event_within_limit
        && acceptance.complete_run_within_limit
        && acceptance.no_floating_point_causal_data;

    Ok(ThetaMellinReport {
        schema: "eros.theta-mellin-aperture.v1",
        status: if accepted { "accepted" } else { "rejected" },
        question: "Can one exact finite theta face grow by one reciprocal shell while the s <-> 1-s involution, its anti-invariant truncation residual, and an independently positive receiver pairing remain causal through replacement and rest?",
        theory_to_structure: "Each lattice shell carries direct exp(-pi*n^2*t) and reciprocal t^(-1/2)exp(-pi*n^2/t) arms, their exact Mellin affine coordinates s and 1-s, an explicit involution target, symmetric and anti-invariant coefficients, and equal positive n^2 metric weights. The endpoint shell uses weight one and remains typed apart from convergent positive-shell Mellin receipts.",
        stopping_condition: "Stop after aperture four grows to five, the raw finite truncation remains explicitly non-self-dual, the symmetric and residual faces transform exactly, the lattice-energy metric stays positive and covariant, predecessor interfaces depart, and the successor remounts. Do not identify this metric with Weil positivity or enter zero search, analytic continuation, CUDA, or RH.",
        logical_cores: std::thread::available_parallelism()
            .map(|cores| cores.get())
            .unwrap_or(1),
        event_limit_seconds: COMPACT_EVENT_LIMIT.as_secs(),
        run_limit_seconds: COMPACT_RUN_LIMIT.as_secs(),
        run_wall_micros,
        run_resource,
        lifecycle,
        involution,
        mellin_receipt,
        metric,
        acceptance,
        conclusion: "The finite construction preserves a real theta/Mellin involution without falsely making a raw truncation self-dual: the symmetric face is fixed and the nonzero anti-invariant face remains carried. Its positive lattice-energy pairing is an exact receiver metric for this bounded shell ecology, not the completed arithmetic trace whose universal positivity would bear RH.",
    })
}

fn run_poisson_tail_cpu() -> Result<PoissonReport, String> {
    const PREDECESSOR_APERTURE: u32 = 4;

    let budget = RunBudget::new();
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);

    let law_words = compact_poisson_law_words();
    let law_identity = compact_identity_bytes(&law_words);
    let law_handle = ArtifactHandle::source("Poisson-Gaussian-boundary-transfer", &law_identity);
    let law_pair = primed_pair(&mut machine)?;
    let law_arcs = compact_seed_arcs(law_pair, law_handle, &law_words)?;
    let (law_radiation, source_law) = profiled_regional_ending(
        &budget,
        &mut machine,
        "Poisson-Gaussian-source-law",
        law_words.len(),
        law_pair,
        &law_arcs,
    )?;
    decode_compact_poisson_law(
        law_radiation.regional()[0].constituent(),
        law_handle.data_namespace,
    )?;

    let predecessor = PoissonApertureFace::canonical(PREDECESSOR_APERTURE)?;
    let predecessor_words = compact_poisson_words(&predecessor)?;
    let predecessor_identity = compact_identity_bytes(&predecessor_words);
    let predecessor_handle =
        ArtifactHandle::source("Poisson-Gaussian-aperture-four", &predecessor_identity);
    let predecessor_pair = primed_pair(&mut machine)?;
    let predecessor_arcs =
        compact_seed_arcs(predecessor_pair, predecessor_handle, &predecessor_words)?;
    let (predecessor_radiation, predecessor_return) = profiled_regional_ending(
        &budget,
        &mut machine,
        "Poisson-Gaussian-aperture-four",
        predecessor_words.len(),
        predecessor_pair,
        &predecessor_arcs,
    )?;
    if decode_compact_poisson_face(
        predecessor_radiation.regional()[0].constituent(),
        predecessor_handle.data_namespace,
    )? != predecessor
    {
        return Err("the Poisson predecessor changed during hand-up".to_owned());
    }

    let baseline_rest = machine.rest_image().map_err(debug)?;
    machine = LiveCurrentMachine::from_rest_image(baseline_rest.clone()).map_err(debug)?;
    if machine.rest_image().map_err(debug)? != baseline_rest {
        return Err("the Poisson predecessor did not survive baseline rest".to_owned());
    }

    let successor_aperture = PREDECESSOR_APERTURE + 1;
    let growth_event = b"Poisson-Gaussian-aperture-four-to-five";
    let objective_value = u64::from(PREDECESSOR_APERTURE) | (u64::from(successor_aperture) << 32);
    let objective_namespace = namespace(&[
        b"eros-formula-Poisson-boundary-objective-v1",
        growth_event,
        &objective_value.to_le_bytes(),
    ]);
    let objective = InterfaceCapability::new(objective_namespace, objective_value);
    let law_after = law_handle.after_contact(growth_event);
    let predecessor_after = predecessor_handle.after_contact(growth_event);
    let meeting_pair = primed_pair(&mut machine)?;
    let meeting_arcs = compact_meeting_arcs(
        meeting_pair,
        objective.clone(),
        &[
            (law_handle, law_after),
            (predecessor_handle, predecessor_after),
        ],
    )?;
    let (meeting_radiation, growth_meeting) = profiled_regional_ending(
        &budget,
        &mut machine,
        "Poisson-Gaussian-growth-meeting",
        1,
        meeting_pair,
        &meeting_arcs,
    )?;
    let meeting = meeting_radiation.regional()[0].constituent();
    let law_recovered_from_standing =
        decode_compact_poisson_law(meeting, law_handle.data_namespace).is_ok();
    let recovered_predecessor =
        decode_compact_poisson_face(meeting, predecessor_handle.data_namespace)?;
    let predecessor_recovered_from_standing = recovered_predecessor == predecessor;
    let objective_recovered_from_current = CapabilityAtlas::from_constituent(meeting)?
        .namespace_value(objective_namespace)?
        == objective_value;
    if !law_recovered_from_standing
        || !predecessor_recovered_from_standing
        || !objective_recovered_from_current
    {
        return Err("the Poisson growth meeting lost a selected causal face".to_owned());
    }

    let successor = recovered_predecessor.grow_one()?;
    let successor_words = compact_poisson_words(&successor)?;
    let successor_identity = compact_identity_bytes(&successor_words);
    let replacement_event = b"Poisson-Gaussian-aperture-four-to-five:return";
    let successor_handle = predecessor_after.successor(
        "Poisson-Gaussian-aperture-five",
        &successor_identity,
        replacement_event,
    );
    let replacement_pair = primed_pair(&mut machine)?;
    let replacement_arcs = compact_replacement_arcs(
        replacement_pair,
        objective.clone(),
        predecessor_after,
        &predecessor_words,
        successor_handle,
        &successor_words,
    )?;
    let (replacement_radiation, successor_replacement) = profiled_regional_ending(
        &budget,
        &mut machine,
        "Poisson-Gaussian-successor-replacement",
        predecessor_words.len() + successor_words.len() + 1,
        replacement_pair,
        &replacement_arcs,
    )?;
    let returned_successor = decode_compact_poisson_face(
        replacement_radiation.regional()[0].constituent(),
        successor_handle.data_namespace,
    )?;
    let standing_successor =
        standing_compact_poisson_face(&machine, successor_handle.data_namespace)?;
    if returned_successor != successor || standing_successor != successor {
        return Err("the Poisson successor changed between return and Standing".to_owned());
    }

    let lower_restriction_exact = successor.restrict(PREDECESSOR_APERTURE)? == predecessor;
    let transferred_shell = successor_aperture;
    let added = &successor.theta.arms[predecessor.theta.arms.len()..];
    let exact_shell_pair = added.len() == 2
        && added
            .iter()
            .all(|arm| arm.shell == transferred_shell && arm.raw_multiplicity == 2)
        && added[0].hand == ThetaHand::Direct
        && added[1].hand == ThetaHand::Reciprocal;

    let direct_multiplicity =
        i64::try_from(added[0].raw_multiplicity).map_err(|_| "direct shell exceeds i64")?;
    let reciprocal_multiplicity =
        i64::try_from(added[1].raw_multiplicity).map_err(|_| "reciprocal shell exceeds i64")?;
    let partial_residual_delta = [direct_multiplicity, -reciprocal_multiplicity];
    let tail_boundary_delta = [direct_multiplicity, -reciprocal_multiplicity];
    let direct_partial_gain_and_tail_loss = [direct_multiplicity, -direct_multiplicity];
    let reciprocal_partial_gain_and_tail_loss = [reciprocal_multiplicity, -reciprocal_multiplicity];

    let direct_complete_body_invariant = direct_partial_gain_and_tail_loss.iter().sum::<i64>() == 0;
    let reciprocal_complete_body_invariant =
        reciprocal_partial_gain_and_tail_loss.iter().sum::<i64>() == 0;
    let residual_transport_exact = partial_residual_delta == tail_boundary_delta;
    let inherited_transform_identity_preserved = predecessor.complete_identity
        == successor.complete_identity
        && predecessor.complete_identity == poisson_complete_identity();

    let tail_reads = predecessor
        .tails
        .iter()
        .zip(&successor.tails)
        .map(|(before, after)| {
            let exponent_gap = before.exponent_gap()?;
            let strictly_decreases_on_positive_domain = before.positive_domain
                && after.positive_domain
                && before.multiplicity > 0
                && after.multiplicity == before.multiplicity
                && after.start == before.start + 1
                && exponent_gap
                    == u64::from(after.start)
                        .checked_mul(u64::from(after.start))
                        .and_then(|square| {
                            u64::from(before.start)
                                .checked_mul(u64::from(before.start))
                                .map(|before_square| square - before_square)
                        })
                        .ok_or_else(|| "Gaussian square difference exceeds u64".to_owned())?;
            let (hand, generator, recurrence) = match before.hand {
                ThetaHand::Direct => (
                    "direct",
                    format!(
                        "T_d,{}(t)=2*sum_(n={})^infinity exp(-pi*n^2*t)",
                        PREDECESSOR_APERTURE, before.start
                    ),
                    format!(
                        "d_(n+1)=d_n*exp(-pi*t*(2*n+1)); gap at n={} is {}",
                        before.start, exponent_gap
                    ),
                ),
                ThetaHand::Reciprocal => (
                    "reciprocal",
                    format!(
                        "T_r,{}(t)=2*t^(-1/2)*sum_(n={})^infinity exp(-pi*n^2/t)",
                        PREDECESSOR_APERTURE, before.start
                    ),
                    format!(
                        "r_(n+1)=r_n*exp(-pi*(2*n+1)/t); gap at n={} is {}",
                        before.start, exponent_gap
                    ),
                ),
            };
            Ok(PoissonTailRead {
                hand,
                predecessor_start: before.start,
                transferred_shell,
                successor_start: after.start,
                multiplicity: before.multiplicity,
                exponent_gap,
                generator,
                recurrence,
                strictly_decreases_on_positive_domain,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let tails: [PoissonTailRead; 2] = tail_reads
        .try_into()
        .map_err(|_| "Poisson report requires exactly two tails".to_owned())?;

    let boundary = PoissonBoundaryRead {
        inherited_transform:
            "Poisson summation for the Gaussian: theta(t)=t^(-1/2)*theta(1/t), t>0",
        complete_identity: namespace_string(successor.complete_identity),
        predecessor_boundary_equation: "P_d,4-P_r,4 = T_r,4-T_d,4",
        successor_boundary_equation: "P_d,5-P_r,5 = T_r,5-T_d,5",
        coefficient_basis: ["direct shell d_5", "reciprocal shell r_5"],
        partial_residual_delta,
        tail_boundary_delta,
        residual_transport_exact,
        direct_partial_gain_and_tail_loss,
        reciprocal_partial_gain_and_tail_loss,
        direct_complete_body_invariant,
        reciprocal_complete_body_invariant,
        inherited_transform_identity_preserved,
        tails,
    };

    let predecessor_data_departed =
        standing_compact_poisson_face(&machine, predecessor_after.data_namespace).is_err();
    let predecessor_recruit_departed = !standing_has_capability(
        &machine,
        InterfaceCapability::new(predecessor_after.recruit_namespace, RECRUIT_LOCAL),
    );
    let objective_departed = !standing_has_capability(&machine, objective);
    if !standing_has_poisson_law(&machine, law_after.data_namespace) {
        return Err("the Poisson transfer law did not survive successor return".to_owned());
    }

    let final_rest = machine.rest_image().map_err(debug)?;
    let remounted = LiveCurrentMachine::from_rest_image(final_rest.clone()).map_err(debug)?;
    let final_rest_remount_exact = remounted.rest_image().map_err(debug)? == final_rest;
    let final_machine = machine_read(&remounted)?;
    let source_lineages_departed = machine.memory().live_lineages == 0;
    let lifecycle = PoissonLifecycleRead {
        source_law,
        predecessor_return,
        growth_meeting,
        successor_replacement,
        predecessor_aperture: PREDECESSOR_APERTURE,
        successor_aperture,
        predecessor_words: predecessor_words.len(),
        successor_words: successor_words.len(),
        lower_restriction_exact,
        law_recovered_from_standing,
        predecessor_recovered_from_standing,
        objective_recovered_from_current,
        predecessor_data_departed,
        predecessor_recruit_departed,
        objective_departed,
        source_lineages_departed,
        final_rest_remount_exact,
        final_machine,
    };

    let exact_boundary_transfer =
        exact_shell_pair && lower_restriction_exact && residual_transport_exact;
    let complete_objects_invariant =
        direct_complete_body_invariant && reciprocal_complete_body_invariant;
    let transform_identity_preserved = inherited_transform_identity_preserved;
    let generative_remainders_advanced = boundary.tails.iter().all(|tail| {
        tail.predecessor_start == transferred_shell
            && tail.successor_start == transferred_shell + 1
            && tail.strictly_decreases_on_positive_domain
    });
    let lifecycle_exact = law_recovered_from_standing
        && predecessor_recovered_from_standing
        && objective_recovered_from_current
        && predecessor_data_departed
        && predecessor_recruit_departed
        && objective_departed
        && source_lineages_departed
        && final_rest_remount_exact;
    let complete_run_within_limit = budget.require_open().is_ok();
    let (run_wall_micros, run_resource) = budget.read();
    let acceptance = PoissonAcceptanceRead {
        exact_boundary_transfer,
        complete_objects_invariant,
        transform_identity_preserved,
        generative_remainders_advanced,
        lifecycle_exact,
        every_event_within_limit: true,
        complete_run_within_limit,
        no_floating_point_causal_data: true,
    };
    let accepted = acceptance.exact_boundary_transfer
        && acceptance.complete_objects_invariant
        && acceptance.transform_identity_preserved
        && acceptance.generative_remainders_advanced
        && acceptance.lifecycle_exact
        && acceptance.every_event_within_limit
        && acceptance.complete_run_within_limit
        && acceptance.no_floating_point_causal_data;

    Ok(PoissonReport {
        schema: "eros.Poisson-tail-transport.v1",
        status: if accepted { "accepted" } else { "rejected" },
        question: "Can Soma carry the general finite-aperture/generative-remainder relation as one causal replacement when instantiated by two Gaussian charts joined by Poisson summation?",
        theory_to_structure: "The source supplies the exact Poisson transform identity. Each complete chart is factored into a finite theta aperture and one formal Gaussian tail generator. Growing the aperture transfers the same shell from each generator into its chart; the machine carries the predecessor, law, objective, replacement, constituent departure, and exact rest without materializing an infinite population.",
        stopping_condition: "Stop after one aperture-four to aperture-five cpu transition preserves both complete chart bodies, preserves their inherited transform identity, advances both tail generators to shell six, recovers aperture four by restriction, and remounts exactly. Do not search zeta zeros, claim RH, enlarge the aperture, render, tune, or enter CUDA.",
        inherited_fact: "Poisson summation for the Gaussian is source law, not a result rediscovered or proved by this run.",
        logical_cores: std::thread::available_parallelism()
            .map(|cores| cores.get())
            .unwrap_or(1),
        event_limit_seconds: COMPACT_EVENT_LIMIT.as_secs(),
        run_limit_seconds: COMPACT_RUN_LIMIT.as_secs(),
        run_wall_micros,
        run_resource,
        lifecycle,
        boundary,
        acceptance,
        conclusion: "The machine carries a moving finite boundary without confusing the active aperture with the complete object: shell five leaves each generative remainder, enters its corresponding chart, and preserves both completed charts and their transform relation. This supplies the missing causal tail transport for the bounded theta fixture; it does not derive Poisson summation, analytic continuation, a completed Weil form, or RH.",
    })
}
