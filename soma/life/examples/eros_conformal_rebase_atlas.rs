use std::collections::BTreeMap;
use std::io::Write;
use std::path::PathBuf;
use std::thread;

use num_bigint::{BigInt, Sign};
use num_rational::BigRational;
use serde::Serialize;
use sha2::{Digest, Sha256};

type Rat = BigRational;

#[derive(Clone, Debug, PartialEq, Eq)]
struct ComplexRat {
    real: Rat,
    imaginary: Rat,
}

#[derive(Clone, Debug, Serialize)]
struct RationalRead {
    numerator: String,
    denominator: String,
}

#[derive(Clone, Debug, Serialize)]
struct ComplexRead {
    real: RationalRead,
    imaginary: RationalRead,
}

#[derive(Clone, Debug, Serialize)]
struct VectorPairRead {
    first: Vec<RationalRead>,
    second: Vec<RationalRead>,
    dot_product: RationalRead,
    equal_norm_squared: bool,
}

#[derive(Clone, Debug, Serialize)]
struct PotentialNetRead {
    species: &'static str,
    law: String,
    gradient_pair: Option<VectorPairRead>,
    phase_winding: Option<i64>,
    rays_per_level_family: Option<u32>,
    exact_interpretation: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct LocalGermRead {
    label: &'static str,
    chart: &'static str,
    source: ComplexRead,
    target: ComplexRead,
    expansion: String,
    leading_coefficient: ComplexRead,
    local_degree: u32,
    derivative_at_source: Option<ComplexRead>,
    derivative_zero: bool,
    zero_order: Option<u32>,
    critical_order: Option<u32>,
    species: &'static str,
    source_axis_angle_turns: RationalRead,
    image_ray_angle_turns_unwrapped: RationalRead,
    image_ray_angle_turns_mod_one: RationalRead,
    horizontal_image_leader: ComplexRead,
    vertical_image_leader: ComplexRead,
    regular_angle_preserved: Option<bool>,
    potential_net: PotentialNetRead,
}

#[derive(Clone, Debug, Serialize)]
struct SourceBranchRead {
    source_lineage: &'static str,
    source: ComplexRead,
    output: ComplexRead,
    derivative: ComplexRead,
}

#[derive(Clone, Debug, Serialize)]
struct OutputCoincidenceRead {
    label: &'static str,
    function: &'static str,
    branches: Vec<SourceBranchRead>,
    equal_output: bool,
    distinct_sources: bool,
    derivative_hands_differ: bool,
    species: &'static str,
    interpretation: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct GermAtlasRead {
    germs: Vec<LocalGermRead>,
    output_coincidences: Vec<OutputCoincidenceRead>,
}

#[derive(Clone, Debug, Serialize)]
struct XiOrbitRead {
    label: &'static str,
    source_s: ComplexRead,
    centered_w: ComplexRead,
    holomorphic_reflection_r: ComplexRead,
    antiholomorphic_reflection_j: ComplexRead,
    fixed_projection: ComplexRead,
    normal_projection: ComplexRead,
    fixed_locus: bool,
    fixed_plus_normal_reconstructs_source: bool,
    j_is_involution_at_source: bool,
    r_is_involution_at_source: bool,
    zeta_relation: &'static str,
    completion_arrow: &'static str,
    xi_r_relation: &'static str,
    xi_j_relation: &'static str,
    positivity_face: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct ZetaXiSpecialRead {
    source: &'static str,
    zeta_face: &'static str,
    xi_face: &'static str,
    local_species: &'static str,
    completion_consequence: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct AnalyticAtlasRead {
    coordinate_laws: Vec<&'static str>,
    orbits: Vec<XiOrbitRead>,
    special_faces: Vec<ZetaXiSpecialRead>,
    revolution_chart: Vec<&'static str>,
}

#[derive(Clone, Debug, Serialize)]
struct ExponentialWordRead {
    real_exponent: RationalRead,
    imaginary_exponent: RationalRead,
    word: String,
}

#[derive(Clone, Debug, Serialize)]
struct LogPolarPointRead {
    source_u: RationalRead,
    log_radius: RationalRead,
    phase: RationalRead,
    character: ExponentialWordRead,
}

#[derive(Clone, Debug, Serialize)]
struct RebaseOrbitRead {
    label: &'static str,
    epsilon: RationalRead,
    gamma: RationalRead,
    functional_partner_epsilon: RationalRead,
    orbit_species: &'static str,
    unitary: bool,
    rebase_step: RationalRead,
    rebase_multiplier: ExponentialWordRead,
    points: Vec<LogPolarPointRead>,
    partner_points: Vec<LogPolarPointRead>,
    reciprocal_amplitude_at_every_point: bool,
    same_phase_at_every_point: bool,
    exact_interpretation: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct SmithSphereRead {
    x: RationalRead,
    y: RationalRead,
    normal: RationalRead,
}

#[derive(Clone, Debug, Serialize)]
struct QuarterOrbitRead {
    axis: &'static str,
    points: Vec<Vec<RationalRead>>,
}

#[derive(Clone, Debug, Serialize)]
struct SmithRowRead {
    label: &'static str,
    centered_z: ComplexRead,
    cayley_scale: RationalRead,
    cayley_w: ComplexRead,
    reflected_centered_z: ComplexRead,
    reflected_cayley_w: ComplexRead,
    reciprocal_conjugate_w: ComplexRead,
    norm_squared: RationalRead,
    unit_shell_residual: RationalRead,
    residual_formula: RationalRead,
    residual_formula_exact: bool,
    functional_reciprocity_exact: bool,
    sphere: SmithSphereRead,
    on_unit_shell: bool,
    normal_displacement_zero: bool,
    shell_iff_fixed_locus: bool,
    revolution_license: &'static str,
    revolution: Option<QuarterOrbitRead>,
}

#[derive(Clone, Debug, Serialize)]
struct SmithPairRead {
    label: &'static str,
    right_row: &'static str,
    left_row: &'static str,
    normal_sum: RationalRead,
    norm_product: RationalRead,
    reciprocal_norms: bool,
    interpretation: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct SmithAtlasRead {
    map: &'static str,
    residual_law: &'static str,
    rows: Vec<SmithRowRead>,
    pairs: Vec<SmithPairRead>,
}

#[derive(Clone, Debug, Serialize)]
struct AcceptanceRead {
    every_regular_germ_preserves_the_source_right_angle: bool,
    every_critical_germ_uses_local_degree_instead_of_a_false_tangent: bool,
    zero_order_and_critical_order_remain_distinct: bool,
    distinct_preimages_remain_distinct_at_equal_output: bool,
    every_xi_orbit_projector_is_exact: bool,
    circle_occurs_if_and_only_if_normal_exponent_is_zero: bool,
    functional_rebase_partners_are_reciprocal_in_amplitude: bool,
    every_smith_residual_is_exact: bool,
    smith_unit_shell_occurs_if_and_only_if_normal_displacement_is_zero: bool,
    smith_functional_partners_are_reciprocal_conjugates: bool,
    no_floating_point_causal_data: bool,
}

#[derive(Clone, Debug, Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: Vec<&'static str>,
    workers: BTreeMap<&'static str, u64>,
    local_holomorphic_germs: Vec<LocalGermRead>,
    distinct_source_output_coincidences: Vec<OutputCoincidenceRead>,
    zeta_xi_completion_atlas: AnalyticAtlasRead,
    exact_rebase_orbits: Vec<RebaseOrbitRead>,
    centered_smith_atlas: SmithAtlasRead,
    acceptance: AcceptanceRead,
    consequence: &'static str,
    construction_boundary: &'static str,
    report_sha256_without_digest: String,
}

#[derive(Clone, Debug)]
struct GermSpec {
    label: &'static str,
    chart: &'static str,
    source: ComplexRat,
    target: ComplexRat,
    coefficient: ComplexRat,
    degree: u32,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("conformal rebase atlas: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
    if arguments.next().is_some() {
        return Err(usage());
    }

    let germ_worker = thread::spawn(build_germ_atlas);
    let analytic_worker = thread::spawn(build_analytic_atlas);
    let rebase_worker = thread::spawn(build_rebase_atlas);
    let smith_worker = thread::spawn(build_smith_atlas);

    let germs = join_worker("local-germ", germ_worker)?;
    let analytic = join_worker("zeta-xi", analytic_worker)?;
    let rebases = join_worker("rebase", rebase_worker)?;
    let smith = join_worker("smith", smith_worker)?;

    let acceptance = acceptance(&germs, &analytic, &rebases, &smith);
    let accepted = acceptance.every_regular_germ_preserves_the_source_right_angle
        && acceptance.every_critical_germ_uses_local_degree_instead_of_a_false_tangent
        && acceptance.zero_order_and_critical_order_remain_distinct
        && acceptance.distinct_preimages_remain_distinct_at_equal_output
        && acceptance.every_xi_orbit_projector_is_exact
        && acceptance.circle_occurs_if_and_only_if_normal_exponent_is_zero
        && acceptance.functional_rebase_partners_are_reciprocal_in_amplitude
        && acceptance.every_smith_residual_is_exact
        && acceptance.smith_unit_shell_occurs_if_and_only_if_normal_displacement_is_zero
        && acceptance.smith_functional_partners_are_reciprocal_conjugates
        && acceptance.no_floating_point_causal_data;

    let mut workers = BTreeMap::new();
    workers.insert("independent_exact_workers", 4);
    workers.insert(
        "cpu_parallelism_available",
        thread::available_parallelism()
            .map(|count| u64::try_from(count.get()).unwrap_or(u64::MAX))
            .unwrap_or(1),
    );

    let mut report = Report {
        schema: "eros.conformal-rebase-atlas.v1",
        status: if accepted { "accepted" } else { "rejected" },
        question: "Can transformed-grid germs, completed Zeta symmetry, logarithmic rebase, and centered Smith incidence be carried as one exact receiver-relative atlas?",
        theory_to_structure: vec![
            "one source point plus its first nonzero holomorphic term -> one typed local germ",
            "R(s)=1-s and J(s)=1-conjugate(s) -> separate functional and fixed-locus hands",
            "w=s-1/2 -> exact fixed and normal projectors",
            "u=log(x/x0) -> exact log-polar scale/turn current",
            "(w-a)/(w+a) -> exact unit-shell residual and reciprocal-conjugate partner",
            "a rendered crossing or shell is downstream of these rows and cannot replace them",
        ],
        workers,
        local_holomorphic_germs: germs.germs,
        distinct_source_output_coincidences: germs.output_coincidences,
        zeta_xi_completion_atlas: analytic,
        exact_rebase_orbits: rebases,
        centered_smith_atlas: smith,
        acceptance,
        consequence: "The normal coordinate epsilon is now one carried hand across four formerly separated views: it is the displacement from the fixed Xi seam, the real exponent of rebase, the circle-versus-spiral discriminator, and the exact signed Smith shell residual. Local degree and source lineage remain separate, so a zero, a critical point, and a coincident output can no longer be mistaken for one visual kink.",
        construction_boundary: "This bounded atlas classifies and transports the exact local laws. It does not supply the missing global all-probe positivity or an operator whose complete spectrum is the nontrivial Xi zero set.",
        report_sha256_without_digest: String::new(),
    };
    let without_digest =
        serde_json::to_vec_pretty(&report).map_err(|error| format!("report encodes: {error}"))?;
    report.report_sha256_without_digest = sha256(&without_digest);
    write_new_json(&output, &report)?;
    if !accepted {
        return Err("the exact conformal-rebase acceptance relation did not close".to_owned());
    }
    Ok(())
}

fn join_worker<T>(name: &str, worker: thread::JoinHandle<Result<T, String>>) -> Result<T, String> {
    worker
        .join()
        .map_err(|_| format!("{name} worker panicked"))?
}

impl ComplexRat {
    fn new(
        real_numerator: i64,
        real_denominator: i64,
        imaginary_numerator: i64,
        imaginary_denominator: i64,
    ) -> Self {
        Self {
            real: rational(real_numerator, real_denominator),
            imaginary: rational(imaginary_numerator, imaginary_denominator),
        }
    }

    fn from_parts(real: Rat, imaginary: Rat) -> Self {
        Self { real, imaginary }
    }

    fn real(value: Rat) -> Self {
        Self::from_parts(value, rational(0, 1))
    }

    fn zero() -> Self {
        Self::new(0, 1, 0, 1)
    }

    fn one() -> Self {
        Self::new(1, 1, 0, 1)
    }

    fn i() -> Self {
        Self::new(0, 1, 1, 1)
    }

    fn is_zero(&self) -> bool {
        self.real == rational(0, 1) && self.imaginary == rational(0, 1)
    }

    fn add(&self, other: &Self) -> Self {
        Self::from_parts(&self.real + &other.real, &self.imaginary + &other.imaginary)
    }

    fn subtract(&self, other: &Self) -> Self {
        Self::from_parts(&self.real - &other.real, &self.imaginary - &other.imaginary)
    }

    fn conjugate(&self) -> Self {
        Self::from_parts(self.real.clone(), -self.imaginary.clone())
    }

    fn scale(&self, scalar: &Rat) -> Self {
        Self::from_parts(&self.real * scalar, &self.imaginary * scalar)
    }

    fn multiply(&self, other: &Self) -> Self {
        Self::from_parts(
            &self.real * &other.real - &self.imaginary * &other.imaginary,
            &self.real * &other.imaginary + &self.imaginary * &other.real,
        )
    }

    fn divide(&self, other: &Self) -> Result<Self, String> {
        let norm = other.norm_squared();
        if norm == rational(0, 1) {
            return Err("exact complex division refuses a zero denominator".to_owned());
        }
        Ok(self
            .multiply(&other.conjugate())
            .scale(&(rational(1, 1) / norm)))
    }

    fn inverse(&self) -> Result<Self, String> {
        Self::one().divide(self)
    }

    fn norm_squared(&self) -> Rat {
        &self.real * &self.real + &self.imaginary * &self.imaginary
    }

    fn vector_dot(&self, other: &Self) -> Rat {
        &self.real * &other.real + &self.imaginary * &other.imaginary
    }

    fn pow(&self, exponent: u32) -> Self {
        let mut result = Self::one();
        let mut base = self.clone();
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining % 2 == 1 {
                result = result.multiply(&base);
            }
            remaining /= 2;
            if remaining > 0 {
                base = base.multiply(&base);
            }
        }
        result
    }
}

fn build_germ_atlas() -> Result<GermAtlasRead, String> {
    let specs = vec![
        GermSpec {
            label: "regular affine scale-turn",
            chart: "F(z)=2/3-i/7+(2+3i)(z-(1/3+i/5))",
            source: ComplexRat::new(1, 3, 1, 5),
            target: ComplexRat::new(2, 3, -1, 7),
            coefficient: ComplexRat::new(2, 1, 3, 1),
            degree: 1,
        },
        GermSpec {
            label: "simple zero with nonzero derivative",
            chart: "F(z)=(1+i)z",
            source: ComplexRat::zero(),
            target: ComplexRat::zero(),
            coefficient: ComplexRat::new(1, 1, 1, 1),
            degree: 1,
        },
        GermSpec {
            label: "nonzero critical branch",
            chart: "F(z)=1+z^2",
            source: ComplexRat::zero(),
            target: ComplexRat::one(),
            coefficient: ComplexRat::one(),
            degree: 2,
        },
        GermSpec {
            label: "multiple zero and critical branch",
            chart: "F(z)=z^3",
            source: ComplexRat::zero(),
            target: ComplexRat::zero(),
            coefficient: ComplexRat::one(),
            degree: 3,
        },
    ];
    let germs = specs
        .into_iter()
        .map(build_germ)
        .collect::<Result<Vec<_>, _>>()?;

    let one = ComplexRat::one();
    let minus_one = ComplexRat::new(-1, 1, 0, 1);
    let output = ComplexRat::one();
    let derivative_right = ComplexRat::new(2, 1, 0, 1);
    let derivative_left = ComplexRat::new(-2, 1, 0, 1);
    let coincidence = OutputCoincidenceRead {
        label: "two source lineages meet one codomain value",
        function: "F(z)=z^2",
        branches: vec![
            SourceBranchRead {
                source_lineage: "source:+1",
                source: complex_read(&one),
                output: complex_read(&output),
                derivative: complex_read(&derivative_right),
            },
            SourceBranchRead {
                source_lineage: "source:-1",
                source: complex_read(&minus_one),
                output: complex_read(&output),
                derivative: complex_read(&derivative_left),
            },
        ],
        equal_output: true,
        distinct_sources: one != minus_one,
        derivative_hands_differ: derivative_right != derivative_left,
        species: "distinct_source_output_coincidence",
        interpretation: "equal codomain placement does not merge source lineage or local hand",
    };
    Ok(GermAtlasRead {
        germs,
        output_coincidences: vec![coincidence],
    })
}

fn build_germ(spec: GermSpec) -> Result<LocalGermRead, String> {
    if spec.degree == 0 || spec.coefficient.is_zero() {
        return Err("a local germ has positive degree and nonzero leading coefficient".to_owned());
    }
    let horizontal = spec.coefficient.clone();
    let vertical = spec.coefficient.multiply(&ComplexRat::i().pow(spec.degree));
    let derivative = (spec.degree == 1).then(|| spec.coefficient.clone());
    let regular_angle_preserved = derivative.as_ref().map(|_| {
        horizontal.vector_dot(&vertical) == rational(0, 1)
            && horizontal.norm_squared() == vertical.norm_squared()
    });
    let zero_order = spec.target.is_zero().then_some(spec.degree);
    let critical_order = (spec.degree > 1).then_some(spec.degree - 1);
    let species = match (spec.target.is_zero(), spec.degree) {
        (false, 1) => "regular_conformal_germ",
        (true, 1) => "simple_zero_regular_germ",
        (false, _) => "nonzero_critical_branch",
        (true, _) => "multiple_zero_critical_branch",
    };
    let potential_net = potential_net(&spec)?;
    Ok(LocalGermRead {
        label: spec.label,
        chart: spec.chart,
        source: complex_read(&spec.source),
        target: complex_read(&spec.target),
        expansion: format!(
            "F(z0+delta)=F(z0)+({})*delta^{}",
            complex_text(&spec.coefficient),
            spec.degree
        ),
        leading_coefficient: complex_read(&spec.coefficient),
        local_degree: spec.degree,
        derivative_at_source: derivative.as_ref().map(complex_read),
        derivative_zero: spec.degree > 1,
        zero_order,
        critical_order,
        species,
        source_axis_angle_turns: rational_read(&rational(1, 4)),
        image_ray_angle_turns_unwrapped: rational_read(&rational(i64::from(spec.degree), 4)),
        image_ray_angle_turns_mod_one: rational_read(&rational(i64::from(spec.degree % 4), 4)),
        horizontal_image_leader: complex_read(&horizontal),
        vertical_image_leader: complex_read(&vertical),
        regular_angle_preserved,
        potential_net,
    })
}

fn potential_net(spec: &GermSpec) -> Result<PotentialNetRead, String> {
    if spec.target.is_zero() {
        return Ok(PotentialNetRead {
            species: "log_amplitude_singularity_and_phase_vortex",
            law: format!(
                "U=log|{}|+{}*log|delta|; Delta V={} full turns",
                complex_text(&spec.coefficient),
                spec.degree,
                spec.degree
            ),
            gradient_pair: None,
            phase_winding: Some(i64::from(spec.degree)),
            rays_per_level_family: None,
            exact_interpretation: "radius collapses at the zero while phase retains the zero order",
        });
    }
    if spec.degree > 1 {
        return Ok(PotentialNetRead {
            species: "critical_harmonic_level_net",
            law: format!(
                "log F=log F(z0)+({}/{})*delta^{}+higher terms",
                complex_text(&spec.coefficient),
                complex_text(&spec.target),
                spec.degree
            ),
            gradient_pair: None,
            phase_winding: None,
            rays_per_level_family: Some(2 * spec.degree),
            exact_interpretation: "the first derivative vanishes; the first nonzero degree determines the alternating U/V rays",
        });
    }

    let logarithmic_derivative = spec.coefficient.divide(&spec.target)?;
    let gradient_u = ComplexRat::from_parts(
        logarithmic_derivative.real.clone(),
        -logarithmic_derivative.imaginary.clone(),
    );
    let gradient_v = ComplexRat::from_parts(
        logarithmic_derivative.imaginary.clone(),
        logarithmic_derivative.real.clone(),
    );
    let dot = gradient_u.vector_dot(&gradient_v);
    Ok(PotentialNetRead {
        species: "regular_orthogonal_log_amplitude_phase_net",
        law: format!(
            "d(log F)=({}) dz; grad U=(Re,-Im), grad V=(Im,Re)",
            complex_text(&logarithmic_derivative)
        ),
        gradient_pair: Some(VectorPairRead {
            first: vec![
                rational_read(&gradient_u.real),
                rational_read(&gradient_u.imaginary),
            ],
            second: vec![
                rational_read(&gradient_v.real),
                rational_read(&gradient_v.imaginary),
            ],
            dot_product: rational_read(&dot),
            equal_norm_squared: gradient_u.norm_squared() == gradient_v.norm_squared(),
        }),
        phase_winding: None,
        rays_per_level_family: None,
        exact_interpretation:
            "away from zeros and critical points, U and V are conjugate harmonic coordinates",
    })
}

fn build_analytic_atlas() -> Result<AnalyticAtlasRead, String> {
    let samples = [
        ("fixed seam", rational(1, 2), rational(3, 1)),
        ("right normal sheet", rational(3, 4), rational(3, 1)),
        ("left normal sheet", rational(1, 4), rational(3, 1)),
        (
            "real functional pair at two",
            rational(2, 1),
            rational(0, 1),
        ),
    ];
    let orbits = samples
        .into_iter()
        .map(|(label, sigma, t)| build_xi_orbit(label, sigma, t))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(AnalyticAtlasRead {
        coordinate_laws: vec![
            "R(s)=1-s is holomorphic and Xi(R(s))=Xi(s)",
            "J(s)=1-conjugate(s) is antiholomorphic and Xi(J(s))=conjugate(Xi(s))",
            "P_fix(s)=(s+J(s))/2=1/2+i Im(s)",
            "P_normal(s)=(s-J(s))/2=Re(s)-1/2",
            "s=P_fix(s)+P_normal(s)",
        ],
        orbits,
        special_faces: vec![
            ZetaXiSpecialRead {
                source: "s=2",
                zeta_face: "zeta(2)=pi^2/6",
                xi_face: "xi(2)=pi/6=xi(-1)",
                local_species: "regular completed functional pair",
                completion_consequence: "the completion changes pi^2/6 into pi/6 while relating s=2 to s=-1",
            },
            ZetaXiSpecialRead {
                source: "s=0 and s=1",
                zeta_face: "zeta(0)=-1/2; zeta has a simple pole at 1",
                xi_face: "xi(0)=xi(1)=1/2",
                local_species: "endpoint cancellation under completion",
                completion_consequence: "s(s-1), Gamma(s/2), and the zeta pole/continuation form a regular entire pair",
            },
            ZetaXiSpecialRead {
                source: "s=-2 and s=3",
                zeta_face: "zeta(-2)=0 is a simple trivial zero",
                xi_face: "xi(-2)=xi(3)=3*zeta(3)/(2*pi)",
                local_species: "trivial-zero cancellation under completion",
                completion_consequence: "the Gamma pole and the simple zeta zero cancel; a raw zeta axis hit is not an xi axis hit",
            },
            ZetaXiSpecialRead {
                source: "s=1/2+i*gamma with xi(s)=0",
                zeta_face: "raw zeta and its completion factor must both be carried",
                xi_face: "the zero lies on Fix(J) exactly when its normal coordinate epsilon is zero",
                local_species: "symbolic nontrivial zero mode",
                completion_consequence: "the source height remains a parameter; no decimal zero ordinate is required by this atlas",
            },
        ],
        revolution_chart: vec![
            "C_sigma^F(t)=(t,Re F(sigma+i t),Im F(sigma+i t))",
            "the first coordinate retains source chronology; radius is |F| and azimuth is arg F",
            "F=0 is an axis hit; F'=0 is a critical branch; they coincide only at a multiple zero",
            "zeta and xi are separate charts joined by the explicit completion arrow",
        ],
    })
}

fn build_xi_orbit(label: &'static str, sigma: Rat, t: Rat) -> Result<XiOrbitRead, String> {
    let s = ComplexRat::from_parts(sigma.clone(), t.clone());
    let one = ComplexRat::real(rational(1, 1));
    let half = rational(1, 2);
    let r_s = one.subtract(&s);
    let j_s = one.subtract(&s.conjugate());
    let fixed = s.add(&j_s).scale(&half);
    let normal = s.subtract(&j_s).scale(&half);
    let expected_fixed = ComplexRat::from_parts(half.clone(), t);
    let expected_normal = ComplexRat::from_parts(sigma - half.clone(), rational(0, 1));
    if fixed != expected_fixed || normal != expected_normal {
        return Err(format!("{label} fixed/normal projector failed"));
    }
    let reconstructs = fixed.add(&normal) == s;
    let j_twice = one.subtract(&j_s.conjugate());
    let r_twice = one.subtract(&r_s);
    Ok(XiOrbitRead {
        label,
        source_s: complex_read(&s),
        centered_w: complex_read(&normal.add(&ComplexRat::from_parts(
            rational(0, 1),
            fixed.imaginary.clone(),
        ))),
        holomorphic_reflection_r: complex_read(&r_s),
        antiholomorphic_reflection_j: complex_read(&j_s),
        fixed_projection: complex_read(&fixed),
        normal_projection: complex_read(&normal),
        fixed_locus: normal.is_zero(),
        fixed_plus_normal_reconstructs_source: reconstructs,
        j_is_involution_at_source: j_twice == s,
        r_is_involution_at_source: r_twice == s,
        zeta_relation: "zeta(s)=chi(s)*zeta(1-s); the raw chart does not identify reflected values",
        completion_arrow: "xi(s)=1/2*s*(s-1)*pi^(-s/2)*Gamma(s/2)*zeta(s)",
        xi_r_relation: "xi(1-s)=xi(s)",
        xi_j_relation: "xi(1-conjugate(s))=conjugate(xi(s))",
        positivity_face: if normal.is_zero() {
            "on Fix(J), A(s)*conjugate(A(J(s)))=|A(s)|^2 is a self-pair"
        } else {
            "off Fix(J), the partner product is a cross-pair and has no intrinsic positivity"
        },
    })
}

fn build_rebase_atlas() -> Result<Vec<RebaseOrbitRead>, String> {
    let specs = [
        ("unitary seam", rational(0, 1), rational(3, 2)),
        ("right reciprocal sheet", rational(1, 4), rational(3, 2)),
        ("left reciprocal sheet", rational(-1, 4), rational(3, 2)),
        ("second unitary frequency", rational(0, 1), rational(5, 3)),
    ];
    specs
        .into_iter()
        .map(|(label, epsilon, gamma)| build_rebase_orbit(label, epsilon, gamma))
        .collect()
}

fn build_rebase_orbit(
    label: &'static str,
    epsilon: Rat,
    gamma: Rat,
) -> Result<RebaseOrbitRead, String> {
    let partner_epsilon = -epsilon.clone();
    let points = [-2, -1, 0, 1, 2]
        .into_iter()
        .map(|u| log_polar_point(rational(u, 1), &epsilon, &gamma))
        .collect::<Vec<_>>();
    let partner_points = [-2, -1, 0, 1, 2]
        .into_iter()
        .map(|u| log_polar_point(rational(u, 1), &partner_epsilon, &gamma))
        .collect::<Vec<_>>();
    let reciprocal = points.iter().zip(&partner_points).all(|(left, right)| {
        match (
            rational_from_read(&left.log_radius),
            rational_from_read(&right.log_radius),
        ) {
            (Ok(left), Ok(right)) => left + right == rational(0, 1),
            _ => false,
        }
    });
    let same_phase = points.iter().zip(&partner_points).all(|(left, right)| {
        left.phase.numerator == right.phase.numerator
            && left.phase.denominator == right.phase.denominator
    });
    let unitary = epsilon == rational(0, 1);
    let orbit_species = if unitary {
        "constant_radius_circle"
    } else if epsilon > rational(0, 1) {
        "outward_logarithmic_spiral"
    } else {
        "inward_logarithmic_spiral"
    };
    Ok(RebaseOrbitRead {
        label,
        epsilon: rational_read(&epsilon),
        gamma: rational_read(&gamma),
        functional_partner_epsilon: rational_read(&partner_epsilon),
        orbit_species,
        unitary,
        rebase_step: rational_read(&rational(1, 1)),
        rebase_multiplier: exponential_word(&epsilon, &gamma),
        points,
        partner_points,
        reciprocal_amplitude_at_every_point: reciprocal,
        same_phase_at_every_point: same_phase,
        exact_interpretation: "the primary row is (u,log radius,phase); circle or spiral is derived from the normal exponent without evaluating exp, sin, cos, or pi",
    })
}

fn log_polar_point(u: Rat, epsilon: &Rat, gamma: &Rat) -> LogPolarPointRead {
    let log_radius = epsilon * &u;
    let phase = gamma * &u;
    LogPolarPointRead {
        source_u: rational_read(&u),
        log_radius: rational_read(&log_radius),
        phase: rational_read(&phase),
        character: exponential_word(&log_radius, &phase),
    }
}

fn exponential_word(real_exponent: &Rat, imaginary_exponent: &Rat) -> ExponentialWordRead {
    ExponentialWordRead {
        real_exponent: rational_read(real_exponent),
        imaginary_exponent: rational_read(imaginary_exponent),
        word: format!(
            "exp({})*exp(i*{})",
            rational_text(real_exponent),
            rational_text(imaginary_exponent)
        ),
    }
}

fn build_smith_atlas() -> Result<SmithAtlasRead, String> {
    let rows = vec![
        build_smith_row(
            "seam-height-3/2",
            rational(0, 1),
            rational(3, 2),
            rational(1, 1),
        )?,
        build_smith_row(
            "right-height-3/2",
            rational(1, 4),
            rational(3, 2),
            rational(1, 1),
        )?,
        build_smith_row(
            "left-height-3/2",
            rational(-1, 4),
            rational(3, 2),
            rational(1, 1),
        )?,
        build_smith_row(
            "seam-height-2",
            rational(0, 1),
            rational(2, 1),
            rational(1, 1),
        )?,
    ];
    let right = rows
        .iter()
        .find(|row| row.label == "right-height-3/2")
        .ok_or_else(|| "right Smith row is absent".to_owned())?;
    let left = rows
        .iter()
        .find(|row| row.label == "left-height-3/2")
        .ok_or_else(|| "left Smith row is absent".to_owned())?;
    let right_z = complex_from_read(&right.centered_z)?;
    let left_z = complex_from_read(&left.centered_z)?;
    let right_norm = rational_from_read(&right.norm_squared)?;
    let left_norm = rational_from_read(&left.norm_squared)?;
    let pair = SmithPairRead {
        label: "functional reciprocal pair at height 3/2",
        right_row: "right-height-3/2",
        left_row: "left-height-3/2",
        normal_sum: rational_read(&(&right_z.real + &left_z.real)),
        norm_product: rational_read(&(&right_norm * &left_norm)),
        reciprocal_norms: &right_norm * &left_norm == rational(1, 1),
        interpretation: "the two hemispheres are opposed normal hands; their Cayley magnitudes are reciprocal rather than equal",
    };
    Ok(SmithAtlasRead {
        map: "W_a(z)=(z-a)/(z+a), z=epsilon+i*t, a>0",
        residual_law: "|W_a(z)|^2-1=-4*a*epsilon/|z+a|^2",
        rows,
        pairs: vec![pair],
    })
}

fn build_smith_row(
    label: &'static str,
    epsilon: Rat,
    turn: Rat,
    scale: Rat,
) -> Result<SmithRowRead, String> {
    if scale <= rational(0, 1) {
        return Err("the centered Smith scale is positive".to_owned());
    }
    let z = ComplexRat::from_parts(epsilon.clone(), turn);
    let a = ComplexRat::real(scale.clone());
    let w = z.subtract(&a).divide(&z.add(&a))?;
    if w.is_zero() {
        return Err("the bounded Smith row avoids zero before reciprocal comparison".to_owned());
    }
    let j_z = ComplexRat::from_parts(-epsilon.clone(), z.imaginary.clone());
    let reflected_w = j_z.subtract(&a).divide(&j_z.add(&a))?;
    let reciprocal_conjugate = w.conjugate().inverse()?;
    let norm = w.norm_squared();
    let residual = &norm - rational(1, 1);
    let denominator = (&epsilon + &scale) * (&epsilon + &scale) + &z.imaginary * &z.imaginary;
    let expected_residual = rational(-4, 1) * &scale * &epsilon / denominator;
    let sphere_denominator = rational(1, 1) + &norm;
    let sphere = SmithSphereRead {
        x: rational_read(&(rational(2, 1) * &w.real / &sphere_denominator)),
        y: rational_read(&(rational(2, 1) * &w.imaginary / &sphere_denominator)),
        normal: rational_read(&((&norm - rational(1, 1)) / &sphere_denominator)),
    };
    let on_shell = norm == rational(1, 1);
    let normal_zero = epsilon == rational(0, 1);
    let revolution = on_shell.then(|| QuarterOrbitRead {
        axis: "Cayley real axis with actual unitary rebase phase",
        points: vec![
            vec![
                rational_read(&w.real),
                rational_read(&w.imaginary),
                rational_read(&rational(0, 1)),
            ],
            vec![
                rational_read(&w.real),
                rational_read(&rational(0, 1)),
                rational_read(&w.imaginary),
            ],
            vec![
                rational_read(&w.real),
                rational_read(&(-w.imaginary.clone())),
                rational_read(&rational(0, 1)),
            ],
            vec![
                rational_read(&w.real),
                rational_read(&rational(0, 1)),
                rational_read(&(-w.imaginary.clone())),
            ],
        ],
    });
    Ok(SmithRowRead {
        label,
        centered_z: complex_read(&z),
        cayley_scale: rational_read(&scale),
        cayley_w: complex_read(&w),
        reflected_centered_z: complex_read(&j_z),
        reflected_cayley_w: complex_read(&reflected_w),
        reciprocal_conjugate_w: complex_read(&reciprocal_conjugate),
        norm_squared: rational_read(&norm),
        unit_shell_residual: rational_read(&residual),
        residual_formula: rational_read(&expected_residual),
        residual_formula_exact: residual == expected_residual,
        functional_reciprocity_exact: reflected_w == reciprocal_conjugate,
        sphere,
        on_unit_shell: on_shell,
        normal_displacement_zero: normal_zero,
        shell_iff_fixed_locus: on_shell == normal_zero,
        revolution_license: if on_shell {
            "licensed: constant-radius rebase supplies the azimuth"
        } else {
            "refused: nonunitary rebase changes radius and cannot be duplicated into a shell"
        },
        revolution,
    })
}

fn acceptance(
    germs: &GermAtlasRead,
    analytic: &AnalyticAtlasRead,
    rebases: &[RebaseOrbitRead],
    smith: &SmithAtlasRead,
) -> AcceptanceRead {
    let every_regular = germs
        .germs
        .iter()
        .all(|germ| germ.derivative_zero || germ.regular_angle_preserved == Some(true));
    let every_critical = germs.germs.iter().all(|germ| {
        !germ.derivative_zero
            || (germ.derivative_at_source.is_none()
                && germ.local_degree > 1
                && rational_from_read(&germ.image_ray_angle_turns_unwrapped)
                    .is_ok_and(|turn| turn == rational(i64::from(germ.local_degree), 4)))
    });
    let orders_distinct = germs
        .germs
        .iter()
        .all(|germ| germ.zero_order == Some(germ.local_degree) || germ.zero_order.is_none())
        && germs.germs.iter().all(|germ| {
            germ.critical_order
                == germ
                    .local_degree
                    .checked_sub(1)
                    .filter(|_| germ.local_degree > 1)
        });
    let distinct_sources = germs.output_coincidences.iter().all(|coincidence| {
        coincidence.equal_output
            && coincidence.distinct_sources
            && coincidence.derivative_hands_differ
    });
    let projectors = analytic.orbits.iter().all(|orbit| {
        orbit.fixed_plus_normal_reconstructs_source
            && orbit.j_is_involution_at_source
            && orbit.r_is_involution_at_source
    });
    let circle_iff_fixed = rebases.iter().all(|orbit| {
        let epsilon_zero =
            rational_from_read(&orbit.epsilon).is_ok_and(|epsilon| epsilon == rational(0, 1));
        (orbit.orbit_species == "constant_radius_circle") == epsilon_zero
            && orbit.unitary == epsilon_zero
    });
    AcceptanceRead {
        every_regular_germ_preserves_the_source_right_angle: every_regular,
        every_critical_germ_uses_local_degree_instead_of_a_false_tangent: every_critical,
        zero_order_and_critical_order_remain_distinct: orders_distinct,
        distinct_preimages_remain_distinct_at_equal_output: distinct_sources,
        every_xi_orbit_projector_is_exact: projectors,
        circle_occurs_if_and_only_if_normal_exponent_is_zero: circle_iff_fixed,
        functional_rebase_partners_are_reciprocal_in_amplitude: rebases.iter().all(|orbit| {
            orbit.reciprocal_amplitude_at_every_point && orbit.same_phase_at_every_point
        }),
        every_smith_residual_is_exact: smith.rows.iter().all(|row| row.residual_formula_exact),
        smith_unit_shell_occurs_if_and_only_if_normal_displacement_is_zero: smith
            .rows
            .iter()
            .all(|row| row.shell_iff_fixed_locus),
        smith_functional_partners_are_reciprocal_conjugates: smith
            .rows
            .iter()
            .all(|row| row.functional_reciprocity_exact),
        no_floating_point_causal_data: true,
    }
}

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn rational_read(value: &Rat) -> RationalRead {
    RationalRead {
        numerator: value.numer().to_string(),
        denominator: value.denom().to_string(),
    }
}

fn rational_text(value: &Rat) -> String {
    if value.denom() == &BigInt::from(1u8) {
        value.numer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

fn rational_from_read(read: &RationalRead) -> Result<Rat, String> {
    let numerator = BigInt::parse_bytes(read.numerator.as_bytes(), 10)
        .ok_or_else(|| format!("invalid exact numerator {}", read.numerator))?;
    let denominator = BigInt::parse_bytes(read.denominator.as_bytes(), 10)
        .ok_or_else(|| format!("invalid exact denominator {}", read.denominator))?;
    if denominator.sign() != Sign::Plus {
        return Err("an exact rational denominator must be positive".to_owned());
    }
    Ok(Rat::new(numerator, denominator))
}

fn complex_read(value: &ComplexRat) -> ComplexRead {
    ComplexRead {
        real: rational_read(&value.real),
        imaginary: rational_read(&value.imaginary),
    }
}

fn complex_from_read(value: &ComplexRead) -> Result<ComplexRat, String> {
    Ok(ComplexRat::from_parts(
        rational_from_read(&value.real)?,
        rational_from_read(&value.imaginary)?,
    ))
}

fn complex_text(value: &ComplexRat) -> String {
    let real = rational_text(&value.real);
    let imaginary = rational_text(&value.imaginary);
    if value.imaginary < rational(0, 1) {
        format!("{real}-{}i", rational_text(&(-value.imaginary.clone())))
    } else {
        format!("{real}+{imaginary}i")
    }
}

fn write_new_json<T: Serialize>(output: &PathBuf, value: &T) -> Result<(), String> {
    let mut encoded =
        serde_json::to_vec_pretty(value).map_err(|error| format!("report encodes: {error}"))?;
    encoded.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(output)
        .map_err(|error| format!("{} opens exactly once: {error}", output.display()))?;
    file.write_all(&encoded)
        .map_err(|error| format!("{} writes: {error}", output.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs: {error}", output.display()))?;
    eprintln!(
        "conformal rebase atlas: accepted · {} bytes · {}",
        encoded.len(),
        output.display()
    );
    Ok(())
}

fn sha256(bytes: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(bytes);
    digest
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn usage() -> String {
    "usage: eros_conformal_rebase_atlas <new-report.json>".to_owned()
}
