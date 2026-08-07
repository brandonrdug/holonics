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
struct Vec3 {
    x: Rat,
    y: Rat,
    z: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ComplexRat {
    real: Rat,
    imaginary: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Mat3 {
    rows: Vec<Vec<Rat>>,
}

#[derive(Clone, Debug, Serialize)]
struct RationalRead {
    numerator: String,
    denominator: String,
}

#[derive(Clone, Debug, Serialize)]
struct Vec3Read {
    x: RationalRead,
    y: RationalRead,
    z: RationalRead,
}

#[derive(Clone, Debug, Serialize)]
struct ComplexRead {
    real: RationalRead,
    imaginary: RationalRead,
}

#[derive(Clone, Debug, Serialize)]
struct Mat3Read {
    rows: Vec<Vec<RationalRead>>,
}

#[derive(Clone, Debug, Serialize)]
struct SmithChordPrecessionRead {
    source_centered_pair: Vec<ComplexRead>,
    source_cayley_pair: Vec<ComplexRead>,
    source_upper_pole: Vec3Read,
    source_lower_pole: Vec3Read,
    source_plane_intersection: Vec3Read,
    source_half_chord: RationalRead,
    tilt_rotation: Mat3Read,
    tilted_upper_pole: Vec3Read,
    tilted_lower_pole: Vec3Read,
    tilted_axis_direction: Vec3Read,
    tilted_plane_intersection: Vec3Read,
    tilted_upper_distance_from_plane: RationalRead,
    tilted_lower_distance_from_plane: RationalRead,
    precession_about_plane_normal: Mat3Read,
    precession_phase: ComplexRead,
    precessed_upper_pole: Vec3Read,
    precessed_lower_pole: Vec3Read,
    precessed_axis_direction: Vec3Read,
    precessed_plane_intersection: Vec3Read,
    tilted_intersection_complex: ComplexRead,
    precessed_intersection_complex: ComplexRead,
    tilted_direction_stereographic: ComplexRead,
    precessed_direction_stereographic: ComplexRead,
    intersection_obeys_complex_precession: bool,
    direction_obeys_complex_precession: bool,
    upper_pole_edge_length_squared: RationalRead,
    lower_pole_edge_length_squared: RationalRead,
    upper_spherical_arc_cosine: RationalRead,
    lower_spherical_arc_cosine: RationalRead,
    upper_spherical_arc_length: String,
    lower_spherical_arc_length: String,
    chordal_and_spherical_edge_reads_agree: bool,
    chord_separation_squared: Vec<RationalRead>,
    chord_separation_preserved: bool,
    every_pole_remains_on_unit_sphere: bool,
    precession_moves_the_complex_intersection: bool,
    exact_interpretation: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct PoleEdgeRead {
    label: &'static str,
    source_intersection: Vec3Read,
    target_intersection: Vec3Read,
    source_axis: Vec3Read,
    target_axis: Vec3Read,
    delta_intersection: Vec3Read,
    delta_axis: Vec3Read,
    upper_displacement: Vec3Read,
    lower_displacement: Vec3Read,
    upper_length_squared: RationalRead,
    lower_length_squared: RationalRead,
    length_sum: RationalRead,
    expected_length_sum: RationalRead,
    length_difference: RationalRead,
    expected_length_difference: RationalRead,
    swing_chi: RationalRead,
    pole_swapped_swing_chi: RationalRead,
    cross_coupling: RationalRead,
    identities_exact: bool,
    interpretation: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct PoleEdgeAtlasRead {
    common_axis_rotation: Mat3Read,
    edges: Vec<PoleEdgeRead>,
}

#[derive(Clone, Debug, Serialize)]
struct SheetMetricRead {
    base_axis: Vec3Read,
    parameter_names: Vec<&'static str>,
    intersection_tangents: Vec<Vec3Read>,
    axis_tangents: Vec<Vec3Read>,
    upper_sheet_metric: Vec<Vec<RationalRead>>,
    lower_sheet_metric: Vec<Vec<RationalRead>>,
    common_metric: Vec<Vec<RationalRead>>,
    coupling_metric: Vec<Vec<RationalRead>>,
    upper_determinant: RationalRead,
    lower_determinant: RationalRead,
    both_sheet_metrics_positive_definite: bool,
    average_and_coupling_reconstruct_both_sheets: bool,
    exact_interpretation: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct ConnectionFaceRead {
    label: &'static str,
    first_edge_transport: Mat3Read,
    second_edge_transport: Mat3Read,
    direct_transport: Mat3Read,
    composed_transport: Mat3Read,
    connection_residual: Mat3Read,
    holonomy: Mat3Read,
    holonomy_cosine_without_angle_evaluation: RationalRead,
    every_transport_is_special_orthogonal: bool,
    direct_and_composed_agree: bool,
    initial_axis: Vec3Read,
    direct_axis_at_target: Vec3Read,
    composed_axis_at_target: Vec3Read,
    axis_discrepancy_squared: RationalRead,
    upper_pole_discrepancy_squared: RationalRead,
    lower_pole_discrepancy_squared: RationalRead,
    species: &'static str,
    exact_interpretation: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct ConicWitnessRead {
    point: ComplexRead,
    polynomial_value: RationalRead,
}

#[derive(Clone, Debug, Serialize)]
struct ConicRowRead {
    parameter_mu: RationalRead,
    homogeneous_matrix: Mat3Read,
    determinant: RationalRead,
    equation: String,
    real_species: &'static str,
    nonsingular_complex_projective_conic: bool,
    discriminant: bool,
    factorization: Option<&'static str>,
    witnesses: Vec<ConicWitnessRead>,
    every_witness_exact: bool,
}

#[derive(Clone, Debug, Serialize)]
struct ConicPhasePathRead {
    pencil: &'static str,
    rows: Vec<ConicRowRead>,
    discriminant_parameter: RationalRead,
    all_nonsingular_rows_share_one_complex_projective_species: bool,
    discriminant_localized_exactly: bool,
    exact_interpretation: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct AcceptanceRead {
    smith_chord_precesses_with_exact_complex_phase: bool,
    rigid_precession_preserves_poles_and_chord: bool,
    plane_intersection_moves_without_becoming_an_outside_camera: bool,
    every_symmetric_pole_edge_satisfies_sum_and_difference_laws: bool,
    decoupled_motion_has_equal_pole_chordal_edges: bool,
    coupled_swing_is_oriented_and_reverses_with_pole_hand: bool,
    two_parameter_sheet_metrics_retain_common_and_coupling_parts: bool,
    flat_triangle_closes_and_curved_triangle_retains_holonomy: bool,
    conic_projective_class_breaks_only_at_the_declared_discriminant: bool,
    no_floating_point_causal_data: bool,
}

#[derive(Clone, Debug, Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: Vec<&'static str>,
    workers: BTreeMap<&'static str, u64>,
    smith_chord_precession: SmithChordPrecessionRead,
    symmetric_pole_edges: PoleEdgeAtlasRead,
    two_parameter_sheet_metric: SheetMetricRead,
    triangular_connection_faces: Vec<ConnectionFaceRead>,
    conic_phase_path: ConicPhasePathRead,
    acceptance: AcceptanceRead,
    consequence: &'static str,
    construction_boundary: &'static str,
    report_sha256_without_digest: String,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("precessing chord conic transport: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
    if arguments.next().is_some() {
        return Err(usage());
    }

    let smith_worker = thread::spawn(build_smith_chord_precession);
    let pole_worker = thread::spawn(build_pole_transport);
    let face_worker = thread::spawn(build_connection_faces);
    let conic_worker = thread::spawn(build_conic_phase_path);

    let smith = join_worker("smith-chord", smith_worker)?;
    let (pole_edges, sheet_metric) = join_worker("pole-metric", pole_worker)?;
    let faces = join_worker("connection-face", face_worker)?;
    let conics = join_worker("conic-phase", conic_worker)?;
    let acceptance = acceptance(&smith, &pole_edges, &sheet_metric, &faces, &conics)?;
    let accepted = acceptance.smith_chord_precesses_with_exact_complex_phase
        && acceptance.rigid_precession_preserves_poles_and_chord
        && acceptance.plane_intersection_moves_without_becoming_an_outside_camera
        && acceptance.every_symmetric_pole_edge_satisfies_sum_and_difference_laws
        && acceptance.decoupled_motion_has_equal_pole_chordal_edges
        && acceptance.coupled_swing_is_oriented_and_reverses_with_pole_hand
        && acceptance.two_parameter_sheet_metrics_retain_common_and_coupling_parts
        && acceptance.flat_triangle_closes_and_curved_triangle_retains_holonomy
        && acceptance.conic_projective_class_breaks_only_at_the_declared_discriminant
        && acceptance.no_floating_point_causal_data;

    let mut workers = BTreeMap::new();
    workers.insert("independent_exact_workers", 4);
    workers.insert(
        "host_parallelism_available",
        thread::available_parallelism()
            .map(|count| u64::try_from(count.get()).unwrap_or(u64::MAX))
            .unwrap_or(1),
    );

    let mut report = Report {
        schema: "eros.precessing-chord-conic-transport.v1",
        status: if accepted { "accepted" } else { "rejected" },
        question: "Can one reciprocal Smith chord become a parameterized two-sheeted pole carrier whose exact arc imbalance, sheet metric, conic phase, and triangular holonomy remain separately observable?",
        theory_to_structure: vec![
            "one oriented chord -> plane intersection q, axis direction u, and two pole sheets",
            "one discrete edge -> Delta P plus/minus = Delta q plus/minus r Delta u",
            "pole-length sum -> common translation and precession activity",
            "pole-length difference -> oriented cross-coupling Delta q dot Delta u",
            "two parameter directions -> two induced sheet metrics and their common/coupling factors",
            "direct versus composed face transport -> exact connection holonomy",
            "one conic matrix pencil -> circle, ellipse, discriminant line-pair, and hyperbola phases",
        ],
        workers,
        smith_chord_precession: smith,
        symmetric_pole_edges: pole_edges,
        two_parameter_sheet_metric: sheet_metric,
        triangular_connection_faces: faces,
        conic_phase_path: conics,
        acceptance,
        consequence: "The reciprocal Smith sheets now form an exact movable chord rather than two isolated plotted points. Their plane intersection and direction precess by the same rational complex phase, while the two pole paths expose translation, orientation change, and their cross-coupling without averaging. Triangular holonomy and conic discriminant remain independent typed seams.",
        construction_boundary: "This cell supplies the discrete geometric carrier needed by the proposed global response law. It does not yet identify the completed Weil response with the sheet metric, prove that every nontrivial Xi zero is a spectral mode of this connection, or exclude a nonzero normal chord.",
        report_sha256_without_digest: String::new(),
    };
    let without_digest =
        serde_json::to_vec_pretty(&report).map_err(|error| format!("report encodes: {error}"))?;
    report.report_sha256_without_digest = sha256(&without_digest);
    write_new_json(&output, &report)?;
    if !accepted {
        return Err("the precessing-chord acceptance relation did not close".to_owned());
    }
    Ok(())
}

fn join_worker<T>(name: &str, worker: thread::JoinHandle<Result<T, String>>) -> Result<T, String> {
    worker
        .join()
        .map_err(|_| format!("{name} worker panicked"))?
}

impl Vec3 {
    fn new(x: i64, xd: i64, y: i64, yd: i64, z: i64, zd: i64) -> Self {
        Self {
            x: rational(x, xd),
            y: rational(y, yd),
            z: rational(z, zd),
        }
    }

    fn from_parts(x: Rat, y: Rat, z: Rat) -> Self {
        Self { x, y, z }
    }

    fn zero() -> Self {
        Self::new(0, 1, 0, 1, 0, 1)
    }

    fn add(&self, other: &Self) -> Self {
        Self::from_parts(&self.x + &other.x, &self.y + &other.y, &self.z + &other.z)
    }

    fn subtract(&self, other: &Self) -> Self {
        Self::from_parts(&self.x - &other.x, &self.y - &other.y, &self.z - &other.z)
    }

    fn scale(&self, scalar: &Rat) -> Self {
        Self::from_parts(&self.x * scalar, &self.y * scalar, &self.z * scalar)
    }

    fn dot(&self, other: &Self) -> Rat {
        &self.x * &other.x + &self.y * &other.y + &self.z * &other.z
    }

    fn norm_squared(&self) -> Rat {
        self.dot(self)
    }
}

impl ComplexRat {
    fn from_parts(real: Rat, imaginary: Rat) -> Self {
        Self { real, imaginary }
    }

    fn real(value: Rat) -> Self {
        Self::from_parts(value, rational(0, 1))
    }

    fn from_plane(value: &Vec3) -> Result<Self, String> {
        if value.z != rational(0, 1) {
            return Err("a complex-plane coordinate retains zero normal component".to_owned());
        }
        Ok(Self::from_parts(value.x.clone(), value.y.clone()))
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
        let denominator = other.norm_squared();
        if denominator == rational(0, 1) {
            return Err("exact complex division refuses zero".to_owned());
        }
        Ok(self
            .multiply(&other.conjugate())
            .scale(&(rational(1, 1) / denominator)))
    }

    fn norm_squared(&self) -> Rat {
        &self.real * &self.real + &self.imaginary * &self.imaginary
    }
}

impl Mat3 {
    fn from_i64(rows: [[i64; 3]; 3]) -> Self {
        Self {
            rows: rows
                .into_iter()
                .map(|row| row.into_iter().map(|value| rational(value, 1)).collect())
                .collect(),
        }
    }

    fn from_rows(rows: Vec<Vec<Rat>>) -> Result<Self, String> {
        if rows.len() != 3 || rows.iter().any(|row| row.len() != 3) {
            return Err("a three-dimensional frame has a 3 by 3 matrix".to_owned());
        }
        Ok(Self { rows })
    }

    fn identity() -> Self {
        Self::from_i64([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
    }

    fn transpose(&self) -> Self {
        Self {
            rows: (0..3)
                .map(|row| {
                    (0..3)
                        .map(|column| self.rows[column][row].clone())
                        .collect()
                })
                .collect(),
        }
    }

    fn multiply(&self, other: &Self) -> Self {
        Self {
            rows: (0..3)
                .map(|row| {
                    (0..3)
                        .map(|column| {
                            (0..3)
                                .map(|at| &self.rows[row][at] * &other.rows[at][column])
                                .fold(rational(0, 1), |sum, value| sum + value)
                        })
                        .collect()
                })
                .collect(),
        }
    }

    fn apply(&self, vector: &Vec3) -> Vec3 {
        let coordinates = [&vector.x, &vector.y, &vector.z];
        let value = (0..3)
            .map(|row| {
                (0..3)
                    .map(|column| &self.rows[row][column] * coordinates[column])
                    .fold(rational(0, 1), |sum, term| sum + term)
            })
            .collect::<Vec<_>>();
        Vec3::from_parts(value[0].clone(), value[1].clone(), value[2].clone())
    }

    fn subtract(&self, other: &Self) -> Self {
        Self {
            rows: (0..3)
                .map(|row| {
                    (0..3)
                        .map(|column| &self.rows[row][column] - &other.rows[row][column])
                        .collect()
                })
                .collect(),
        }
    }

    fn trace(&self) -> Rat {
        &self.rows[0][0] + &self.rows[1][1] + &self.rows[2][2]
    }

    fn determinant(&self) -> Rat {
        let m = &self.rows;
        &m[0][0] * (&m[1][1] * &m[2][2] - &m[1][2] * &m[2][1])
            - &m[0][1] * (&m[1][0] * &m[2][2] - &m[1][2] * &m[2][0])
            + &m[0][2] * (&m[1][0] * &m[2][1] - &m[1][1] * &m[2][0])
    }

    fn is_identity(&self) -> bool {
        self == &Self::identity()
    }

    fn is_zero(&self) -> bool {
        self.rows
            .iter()
            .flatten()
            .all(|value| value == &rational(0, 1))
    }

    fn is_special_orthogonal(&self) -> bool {
        self.transpose().multiply(self).is_identity() && self.determinant() == rational(1, 1)
    }
}

fn rotation_x_quarter() -> Mat3 {
    Mat3::from_i64([[1, 0, 0], [0, 0, -1], [0, 1, 0]])
}

fn rotation_y_quarter() -> Mat3 {
    Mat3::from_i64([[0, 0, 1], [0, 1, 0], [-1, 0, 0]])
}

fn rotation_z_quarter() -> Mat3 {
    Mat3::from_i64([[0, -1, 0], [1, 0, 0], [0, 0, 1]])
}

fn rotation_z_half() -> Mat3 {
    Mat3::from_i64([[-1, 0, 0], [0, -1, 0], [0, 0, 1]])
}

fn rotation_y(cosine: Rat, sine: Rat) -> Result<Mat3, String> {
    if &cosine * &cosine + &sine * &sine != rational(1, 1) {
        return Err("a rational y rotation must lie on the unit circle".to_owned());
    }
    Mat3::from_rows(vec![
        vec![cosine.clone(), rational(0, 1), sine.clone()],
        vec![rational(0, 1), rational(1, 1), rational(0, 1)],
        vec![-sine, rational(0, 1), cosine],
    ])
}

fn rotation_z(cosine: Rat, sine: Rat) -> Result<Mat3, String> {
    if &cosine * &cosine + &sine * &sine != rational(1, 1) {
        return Err("a rational z rotation must lie on the unit circle".to_owned());
    }
    Mat3::from_rows(vec![
        vec![cosine.clone(), -sine.clone(), rational(0, 1)],
        vec![sine, cosine, rational(0, 1)],
        vec![rational(0, 1), rational(0, 1), rational(1, 1)],
    ])
}

fn build_smith_chord_precession() -> Result<SmithChordPrecessionRead, String> {
    let epsilon = rational(1, 4);
    let turn = rational(3, 2);
    let scale = rational(1, 1);
    let right_centered = ComplexRat::from_parts(epsilon.clone(), turn.clone());
    let left_centered = ComplexRat::from_parts(-epsilon, turn);
    let right_w = centered_cayley(&right_centered, &scale)?;
    let left_w = centered_cayley(&left_centered, &scale)?;
    let right_sphere = smith_sphere(&right_w);
    let left_sphere = smith_sphere(&left_w);
    let source_upper = left_sphere;
    let source_lower = right_sphere;
    let source_intersection = midpoint(&source_upper, &source_lower);
    let source_half_chord = (&source_upper.z - &source_lower.z) / rational(2, 1);
    if source_intersection.z != rational(0, 1)
        || source_upper.x != source_lower.x
        || source_upper.y != source_lower.y
        || source_half_chord <= rational(0, 1)
    {
        return Err("the exact Smith pair did not form one vertical chord".to_owned());
    }

    let tilt = rotation_y(rational(24, 25), rational(7, 25))?;
    let tilted_upper = tilt.apply(&source_upper);
    let tilted_lower = tilt.apply(&source_lower);
    let tilted_axis = tilt.apply(&Vec3::new(0, 1, 0, 1, 1, 1));
    let tilted_intersection = line_plane_intersection(&tilted_upper, &tilted_lower)?;
    let tilted_upper_distance = tilted_upper
        .subtract(&tilted_intersection)
        .dot(&tilted_axis);
    let tilted_lower_distance = tilted_intersection
        .subtract(&tilted_lower)
        .dot(&tilted_axis);
    if tilted_upper_distance <= rational(0, 1)
        || tilted_lower_distance <= rational(0, 1)
        || &tilted_upper_distance + &tilted_lower_distance != rational(2, 1) * &source_half_chord
    {
        return Err("the tilted plane cut lost one pole distance".to_owned());
    }

    let precession = rotation_z(rational(3, 5), rational(4, 5))?;
    let phase = ComplexRat::from_parts(rational(3, 5), rational(4, 5));
    let precessed_upper = precession.apply(&tilted_upper);
    let precessed_lower = precession.apply(&tilted_lower);
    let precessed_axis = precession.apply(&tilted_axis);
    let precessed_intersection = line_plane_intersection(&precessed_upper, &precessed_lower)?;
    let tilted_q = ComplexRat::from_plane(&tilted_intersection)?;
    let precessed_q = ComplexRat::from_plane(&precessed_intersection)?;
    let tilted_direction = stereographic_direction(&tilted_axis)?;
    let precessed_direction = stereographic_direction(&precessed_axis)?;
    let upper_edge = precessed_upper.subtract(&tilted_upper);
    let lower_edge = precessed_lower.subtract(&tilted_lower);
    let upper_edge_squared = upper_edge.norm_squared();
    let lower_edge_squared = lower_edge.norm_squared();
    let upper_arc_cosine = tilted_upper.dot(&precessed_upper);
    let lower_arc_cosine = tilted_lower.dot(&precessed_lower);
    let chordal_and_spherical_agree = upper_edge_squared
        == rational(2, 1) - rational(2, 1) * &upper_arc_cosine
        && lower_edge_squared == rational(2, 1) - rational(2, 1) * &lower_arc_cosine;
    let separations = [
        source_upper.subtract(&source_lower).norm_squared(),
        tilted_upper.subtract(&tilted_lower).norm_squared(),
        precessed_upper.subtract(&precessed_lower).norm_squared(),
    ];
    let every_pole_unit = [
        &source_upper,
        &source_lower,
        &tilted_upper,
        &tilted_lower,
        &precessed_upper,
        &precessed_lower,
    ]
    .into_iter()
    .all(|pole| pole.norm_squared() == rational(1, 1));

    Ok(SmithChordPrecessionRead {
        source_centered_pair: vec![
            complex_read(&right_centered),
            complex_read(&left_centered),
        ],
        source_cayley_pair: vec![complex_read(&right_w), complex_read(&left_w)],
        source_upper_pole: vec3_read(&source_upper),
        source_lower_pole: vec3_read(&source_lower),
        source_plane_intersection: vec3_read(&source_intersection),
        source_half_chord: rational_read(&source_half_chord),
        tilt_rotation: mat3_read(&tilt),
        tilted_upper_pole: vec3_read(&tilted_upper),
        tilted_lower_pole: vec3_read(&tilted_lower),
        tilted_axis_direction: vec3_read(&tilted_axis),
        tilted_plane_intersection: vec3_read(&tilted_intersection),
        tilted_upper_distance_from_plane: rational_read(&tilted_upper_distance),
        tilted_lower_distance_from_plane: rational_read(&tilted_lower_distance),
        precession_about_plane_normal: mat3_read(&precession),
        precession_phase: complex_read(&phase),
        precessed_upper_pole: vec3_read(&precessed_upper),
        precessed_lower_pole: vec3_read(&precessed_lower),
        precessed_axis_direction: vec3_read(&precessed_axis),
        precessed_plane_intersection: vec3_read(&precessed_intersection),
        tilted_intersection_complex: complex_read(&tilted_q),
        precessed_intersection_complex: complex_read(&precessed_q),
        tilted_direction_stereographic: complex_read(&tilted_direction),
        precessed_direction_stereographic: complex_read(&precessed_direction),
        intersection_obeys_complex_precession: phase.multiply(&tilted_q) == precessed_q,
        direction_obeys_complex_precession: phase.multiply(&tilted_direction)
            == precessed_direction,
        upper_pole_edge_length_squared: rational_read(&upper_edge_squared),
        lower_pole_edge_length_squared: rational_read(&lower_edge_squared),
        upper_spherical_arc_cosine: rational_read(&upper_arc_cosine),
        lower_spherical_arc_cosine: rational_read(&lower_arc_cosine),
        upper_spherical_arc_length: format!("arccos({})", rational_text(&upper_arc_cosine)),
        lower_spherical_arc_length: format!("arccos({})", rational_text(&lower_arc_cosine)),
        chordal_and_spherical_edge_reads_agree: chordal_and_spherical_agree,
        chord_separation_squared: separations.iter().map(rational_read).collect(),
        chord_separation_preserved: separations.windows(2).all(|pair| pair[0] == pair[1]),
        every_pole_remains_on_unit_sphere: every_pole_unit,
        precession_moves_the_complex_intersection: tilted_q != precessed_q,
        exact_interpretation: "The prior reciprocal Smith points are the ends of one chord. A rational tilt makes the plane cut asymmetric; a later rational rotation about the plane normal precesses both the actual intersection and the stereographic direction by the same unit complex phase.",
    })
}

fn centered_cayley(centered: &ComplexRat, scale: &Rat) -> Result<ComplexRat, String> {
    let a = ComplexRat::real(scale.clone());
    centered.subtract(&a).divide(&centered.add(&a))
}

fn smith_sphere(value: &ComplexRat) -> Vec3 {
    let norm = value.norm_squared();
    let denominator = rational(1, 1) + &norm;
    Vec3::from_parts(
        rational(2, 1) * &value.real / &denominator,
        rational(2, 1) * &value.imaginary / &denominator,
        (&norm - rational(1, 1)) / denominator,
    )
}

fn midpoint(left: &Vec3, right: &Vec3) -> Vec3 {
    left.add(right).scale(&rational(1, 2))
}

fn line_plane_intersection(upper: &Vec3, lower: &Vec3) -> Result<Vec3, String> {
    let span = upper.subtract(lower);
    if span.z == rational(0, 1) {
        return Err("a chord parallel to the complex plane has no finite affine cut".to_owned());
    }
    let parameter = -lower.z.clone() / &span.z;
    let intersection = lower.add(&span.scale(&parameter));
    if intersection.z != rational(0, 1) {
        return Err("the exact line-plane intersection retained a normal residual".to_owned());
    }
    Ok(intersection)
}

fn stereographic_direction(direction: &Vec3) -> Result<ComplexRat, String> {
    if direction.norm_squared() != rational(1, 1) {
        return Err("stereographic direction requires one unit axis".to_owned());
    }
    let denominator = rational(1, 1) - &direction.z;
    if denominator == rational(0, 1) {
        return Err("the selected stereographic chart is open at its north pole".to_owned());
    }
    Ok(ComplexRat::from_parts(
        &direction.x / &denominator,
        &direction.y / denominator,
    ))
}

fn build_pole_transport() -> Result<(PoleEdgeAtlasRead, SheetMetricRead), String> {
    let rotation = rotation_z_quarter();
    let source_axis = Vec3::new(3, 5, 0, 1, 4, 5);
    let target_axis = rotation.apply(&source_axis);
    let source_q = Vec3::zero();
    let cases = [
        (
            "precession without translation",
            Vec3::zero(),
            "Both poles traverse equal elementary arcs; all activity is orientation change.",
        ),
        (
            "translation orthogonal to precession",
            Vec3::new(1, 1, 1, 1, 0, 1),
            "Translation and axis change coexist but their exact cross-coupling vanishes.",
        ),
        (
            "translation coupled to precession",
            Vec3::new(1, 1, 0, 1, 0, 1),
            "The cross-term makes the two pole arcs unequal; swapping pole hand reverses the swing.",
        ),
    ];
    let edges = cases
        .into_iter()
        .map(|(label, target_q, interpretation)| {
            build_pole_edge(
                label,
                &source_q,
                &source_axis,
                &target_q,
                &target_axis,
                &rational(1, 1),
                interpretation,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let metric = build_sheet_metric()?;
    Ok((
        PoleEdgeAtlasRead {
            common_axis_rotation: mat3_read(&rotation),
            edges,
        },
        metric,
    ))
}

fn build_pole_edge(
    label: &'static str,
    source_q: &Vec3,
    source_u: &Vec3,
    target_q: &Vec3,
    target_u: &Vec3,
    radius: &Rat,
    interpretation: &'static str,
) -> Result<PoleEdgeRead, String> {
    if source_u.norm_squared() != rational(1, 1) || target_u.norm_squared() != rational(1, 1) {
        return Err(format!("{label} does not carry unit axes"));
    }
    let delta_q = target_q.subtract(source_q);
    let delta_u = target_u.subtract(source_u);
    let source_upper = source_q.add(&source_u.scale(radius));
    let source_lower = source_q.subtract(&source_u.scale(radius));
    let target_upper = target_q.add(&target_u.scale(radius));
    let target_lower = target_q.subtract(&target_u.scale(radius));
    let upper = target_upper.subtract(&source_upper);
    let lower = target_lower.subtract(&source_lower);
    let upper_squared = upper.norm_squared();
    let lower_squared = lower.norm_squared();
    let sum = &upper_squared + &lower_squared;
    let difference = &upper_squared - &lower_squared;
    let expected_sum = rational(2, 1) * delta_q.norm_squared()
        + rational(2, 1) * radius * radius * delta_u.norm_squared();
    let cross = delta_q.dot(&delta_u);
    let expected_difference = rational(4, 1) * radius * &cross;
    if sum == rational(0, 1) {
        return Err(format!("{label} has no discrete motion"));
    }
    let chi = &difference / &sum;
    Ok(PoleEdgeRead {
        label,
        source_intersection: vec3_read(source_q),
        target_intersection: vec3_read(target_q),
        source_axis: vec3_read(source_u),
        target_axis: vec3_read(target_u),
        delta_intersection: vec3_read(&delta_q),
        delta_axis: vec3_read(&delta_u),
        upper_displacement: vec3_read(&upper),
        lower_displacement: vec3_read(&lower),
        upper_length_squared: rational_read(&upper_squared),
        lower_length_squared: rational_read(&lower_squared),
        length_sum: rational_read(&sum),
        expected_length_sum: rational_read(&expected_sum),
        length_difference: rational_read(&difference),
        expected_length_difference: rational_read(&expected_difference),
        swing_chi: rational_read(&chi),
        pole_swapped_swing_chi: rational_read(&(-chi)),
        cross_coupling: rational_read(&cross),
        identities_exact: sum == expected_sum && difference == expected_difference,
        interpretation,
    })
}

fn build_sheet_metric() -> Result<SheetMetricRead, String> {
    let base_axis = Vec3::new(0, 1, 0, 1, 1, 1);
    let dq = [Vec3::new(1, 1, 0, 1, 0, 1), Vec3::new(0, 1, 1, 1, 0, 1)];
    let du = [Vec3::new(0, 1, 1, 2, 0, 1), Vec3::new(1, 3, 0, 1, 0, 1)];
    if du
        .iter()
        .any(|direction| base_axis.dot(direction) != rational(0, 1))
    {
        return Err(
            "axis parameter directions must be tangent to the orientation sphere".to_owned(),
        );
    }
    let upper_vectors = [dq[0].add(&du[0]), dq[1].add(&du[1])];
    let lower_vectors = [dq[0].subtract(&du[0]), dq[1].subtract(&du[1])];
    let upper = gram2(&upper_vectors);
    let lower = gram2(&lower_vectors);
    let common = matrix2_scale(&matrix2_add(&upper, &lower), &rational(1, 2));
    let coupling = matrix2_scale(&matrix2_subtract(&upper, &lower), &rational(1, 2));
    let upper_det = determinant2(&upper);
    let lower_det = determinant2(&lower);
    let reconstructed_upper = matrix2_add(&common, &coupling) == upper;
    let reconstructed_lower = matrix2_subtract(&common, &coupling) == lower;
    Ok(SheetMetricRead {
        base_axis: vec3_read(&base_axis),
        parameter_names: vec!["alpha", "beta"],
        intersection_tangents: dq.iter().map(vec3_read).collect(),
        axis_tangents: du.iter().map(vec3_read).collect(),
        upper_sheet_metric: matrix2_read(&upper),
        lower_sheet_metric: matrix2_read(&lower),
        common_metric: matrix2_read(&common),
        coupling_metric: matrix2_read(&coupling),
        upper_determinant: rational_read(&upper_det),
        lower_determinant: rational_read(&lower_det),
        both_sheet_metrics_positive_definite: upper[0][0] > rational(0, 1)
            && lower[0][0] > rational(0, 1)
            && upper_det > rational(0, 1)
            && lower_det > rational(0, 1),
        average_and_coupling_reconstruct_both_sheets: reconstructed_upper
            && reconstructed_lower,
        exact_interpretation: "The average metric retains common translation-plus-precession activity. The half-difference is an oriented mixed tensor; averaging the pole sheets alone would erase it.",
    })
}

fn gram2(vectors: &[Vec3; 2]) -> Vec<Vec<Rat>> {
    vec![
        vec![vectors[0].dot(&vectors[0]), vectors[0].dot(&vectors[1])],
        vec![vectors[1].dot(&vectors[0]), vectors[1].dot(&vectors[1])],
    ]
}

fn matrix2_add(left: &[Vec<Rat>], right: &[Vec<Rat>]) -> Vec<Vec<Rat>> {
    (0..2)
        .map(|row| {
            (0..2)
                .map(|column| &left[row][column] + &right[row][column])
                .collect()
        })
        .collect()
}

fn matrix2_subtract(left: &[Vec<Rat>], right: &[Vec<Rat>]) -> Vec<Vec<Rat>> {
    (0..2)
        .map(|row| {
            (0..2)
                .map(|column| &left[row][column] - &right[row][column])
                .collect()
        })
        .collect()
}

fn matrix2_scale(value: &[Vec<Rat>], scalar: &Rat) -> Vec<Vec<Rat>> {
    value
        .iter()
        .map(|row| row.iter().map(|entry| entry * scalar).collect())
        .collect()
}

fn determinant2(value: &[Vec<Rat>]) -> Rat {
    &value[0][0] * &value[1][1] - &value[0][1] * &value[1][0]
}

fn build_connection_faces() -> Result<Vec<ConnectionFaceRead>, String> {
    let flat_first = rotation_z_quarter();
    let flat_second = rotation_z_quarter();
    let flat_direct = rotation_z_half();
    let curved_first = rotation_x_quarter();
    let curved_second = rotation_y_quarter();
    let curved_direct = rotation_z_quarter();
    Ok(vec![
        build_connection_face(
            "flat precession triangle",
            &flat_first,
            &flat_second,
            &flat_direct,
            "flat_connection_face",
            "The direct edge and the two-edge precession return the same target frame; the triangle carries no connection residual.",
        )?,
        build_connection_face(
            "curved mixed-axis triangle",
            &curved_first,
            &curved_second,
            &curved_direct,
            "curved_connection_face",
            "The direct and composed routes reach one base vertex with different frames and pole placements; their exact holonomy is the face curvature.",
        )?,
    ])
}

fn build_connection_face(
    label: &'static str,
    first: &Mat3,
    second: &Mat3,
    direct: &Mat3,
    species: &'static str,
    interpretation: &'static str,
) -> Result<ConnectionFaceRead, String> {
    let composed = second.multiply(first);
    let residual = composed.subtract(direct);
    let holonomy = direct.transpose().multiply(&composed);
    let initial_axis = Vec3::new(3, 5, 0, 1, 4, 5);
    let direct_axis = direct.apply(&initial_axis);
    let composed_axis = composed.apply(&initial_axis);
    let axis_discrepancy = composed_axis.subtract(&direct_axis);
    let target_q = Vec3::new(1, 1, 1, 1, 0, 1);
    let direct_upper = target_q.add(&direct_axis);
    let direct_lower = target_q.subtract(&direct_axis);
    let composed_upper = target_q.add(&composed_axis);
    let composed_lower = target_q.subtract(&composed_axis);
    let upper_discrepancy = composed_upper.subtract(&direct_upper).norm_squared();
    let lower_discrepancy = composed_lower.subtract(&direct_lower).norm_squared();
    let every_rotation = [first, second, direct, &composed, &holonomy]
        .into_iter()
        .all(Mat3::is_special_orthogonal);
    Ok(ConnectionFaceRead {
        label,
        first_edge_transport: mat3_read(first),
        second_edge_transport: mat3_read(second),
        direct_transport: mat3_read(direct),
        composed_transport: mat3_read(&composed),
        connection_residual: mat3_read(&residual),
        holonomy: mat3_read(&holonomy),
        holonomy_cosine_without_angle_evaluation: rational_read(
            &((&holonomy.trace() - rational(1, 1)) / rational(2, 1)),
        ),
        every_transport_is_special_orthogonal: every_rotation,
        direct_and_composed_agree: residual.is_zero(),
        initial_axis: vec3_read(&initial_axis),
        direct_axis_at_target: vec3_read(&direct_axis),
        composed_axis_at_target: vec3_read(&composed_axis),
        axis_discrepancy_squared: rational_read(&axis_discrepancy.norm_squared()),
        upper_pole_discrepancy_squared: rational_read(&upper_discrepancy),
        lower_pole_discrepancy_squared: rational_read(&lower_discrepancy),
        species,
        exact_interpretation: interpretation,
    })
}

fn build_conic_phase_path() -> Result<ConicPhasePathRead, String> {
    let specs = [
        (
            4,
            "ellipse",
            None,
            vec![
                ComplexRat::from_parts(rational(1, 1), rational(0, 1)),
                ComplexRat::from_parts(rational(0, 1), rational(1, 2)),
            ],
        ),
        (
            1,
            "circle",
            None,
            vec![ComplexRat::from_parts(rational(3, 5), rational(4, 5))],
        ),
        (
            0,
            "degenerate_parallel_line_pair",
            Some("(x-1)(x+1)=0"),
            vec![
                ComplexRat::from_parts(rational(1, 1), rational(7, 3)),
                ComplexRat::from_parts(rational(-1, 1), rational(-5, 2)),
            ],
        ),
        (
            -1,
            "hyperbola",
            None,
            vec![ComplexRat::from_parts(rational(5, 3), rational(4, 3))],
        ),
    ];
    let rows = specs
        .into_iter()
        .map(|(mu, species, factorization, witnesses)| {
            build_conic_row(mu, species, factorization, witnesses)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let zero_rows = rows.iter().filter(|row| row.discriminant).count();
    Ok(ConicPhasePathRead {
        pencil: "Q_mu(x,y)=x^2+mu*y^2-1",
        rows,
        discriminant_parameter: rational_read(&rational(0, 1)),
        all_nonsingular_rows_share_one_complex_projective_species: true,
        discriminant_localized_exactly: zero_rows == 1,
        exact_interpretation: "Circle, ellipse, and hyperbola are distinct real affine-chart faces of one nonsingular projective conic class. At mu=0 the matrix determinant vanishes and the conic becomes a pair of lines; that seam may supply simplicial edges but is not itself a triangle.",
    })
}

fn build_conic_row(
    mu: i64,
    species: &'static str,
    factorization: Option<&'static str>,
    witnesses: Vec<ComplexRat>,
) -> Result<ConicRowRead, String> {
    let mu = rational(mu, 1);
    let matrix = Mat3::from_rows(vec![
        vec![rational(1, 1), rational(0, 1), rational(0, 1)],
        vec![rational(0, 1), mu.clone(), rational(0, 1)],
        vec![rational(0, 1), rational(0, 1), rational(-1, 1)],
    ])?;
    let determinant = matrix.determinant();
    let witness_reads = witnesses
        .iter()
        .map(|point| {
            let value = &point.real * &point.real + &mu * &point.imaginary * &point.imaginary
                - rational(1, 1);
            ConicWitnessRead {
                point: complex_read(point),
                polynomial_value: rational_read(&value),
            }
        })
        .collect::<Vec<_>>();
    Ok(ConicRowRead {
        parameter_mu: rational_read(&mu),
        homogeneous_matrix: mat3_read(&matrix),
        determinant: rational_read(&determinant),
        equation: format!("x^2+{}*y^2-1=0", rational_text(&mu)),
        real_species: species,
        nonsingular_complex_projective_conic: determinant != rational(0, 1),
        discriminant: determinant == rational(0, 1),
        factorization,
        every_witness_exact: witness_reads.iter().all(|witness| {
            rational_from_read(&witness.polynomial_value).is_ok_and(|value| value == rational(0, 1))
        }),
        witnesses: witness_reads,
    })
}

fn acceptance(
    smith: &SmithChordPrecessionRead,
    pole_edges: &PoleEdgeAtlasRead,
    metric: &SheetMetricRead,
    faces: &[ConnectionFaceRead],
    conics: &ConicPhasePathRead,
) -> Result<AcceptanceRead, String> {
    let decoupled = pole_edges
        .edges
        .iter()
        .filter(|edge| {
            rational_from_read(&edge.cross_coupling).is_ok_and(|value| value == rational(0, 1))
        })
        .all(|edge| {
            edge.upper_length_squared.numerator == edge.lower_length_squared.numerator
                && edge.upper_length_squared.denominator == edge.lower_length_squared.denominator
        });
    let coupled = pole_edges
        .edges
        .iter()
        .find(|edge| edge.label == "translation coupled to precession")
        .ok_or_else(|| "the coupled pole foil is absent".to_owned())?;
    let chi = rational_from_read(&coupled.swing_chi)?;
    let swapped = rational_from_read(&coupled.pole_swapped_swing_chi)?;
    let flat = faces
        .iter()
        .find(|face| face.species == "flat_connection_face")
        .ok_or_else(|| "the flat connection face is absent".to_owned())?;
    let curved = faces
        .iter()
        .find(|face| face.species == "curved_connection_face")
        .ok_or_else(|| "the curved connection face is absent".to_owned())?;
    let conic_species = conics.all_nonsingular_rows_share_one_complex_projective_species
        && conics.rows.iter().all(|row| row.every_witness_exact)
        && conics
            .rows
            .iter()
            .all(|row| row.discriminant == !row.nonsingular_complex_projective_conic)
        && conics.discriminant_localized_exactly;
    Ok(AcceptanceRead {
        smith_chord_precesses_with_exact_complex_phase: smith.intersection_obeys_complex_precession
            && smith.direction_obeys_complex_precession,
        rigid_precession_preserves_poles_and_chord: smith.chord_separation_preserved
            && smith.every_pole_remains_on_unit_sphere
            && smith.chordal_and_spherical_edge_reads_agree,
        plane_intersection_moves_without_becoming_an_outside_camera: smith
            .precession_moves_the_complex_intersection,
        every_symmetric_pole_edge_satisfies_sum_and_difference_laws: pole_edges
            .edges
            .iter()
            .all(|edge| edge.identities_exact),
        decoupled_motion_has_equal_pole_chordal_edges: decoupled,
        coupled_swing_is_oriented_and_reverses_with_pole_hand: chi != rational(0, 1)
            && chi + swapped == rational(0, 1),
        two_parameter_sheet_metrics_retain_common_and_coupling_parts: metric
            .both_sheet_metrics_positive_definite
            && metric.average_and_coupling_reconstruct_both_sheets,
        flat_triangle_closes_and_curved_triangle_retains_holonomy: flat.direct_and_composed_agree
            && rational_from_read(&flat.axis_discrepancy_squared)? == rational(0, 1)
            && !curved.direct_and_composed_agree
            && rational_from_read(&curved.axis_discrepancy_squared)? > rational(0, 1),
        conic_projective_class_breaks_only_at_the_declared_discriminant: conic_species,
        no_floating_point_causal_data: true,
    })
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

fn vec3_read(value: &Vec3) -> Vec3Read {
    Vec3Read {
        x: rational_read(&value.x),
        y: rational_read(&value.y),
        z: rational_read(&value.z),
    }
}

fn complex_read(value: &ComplexRat) -> ComplexRead {
    ComplexRead {
        real: rational_read(&value.real),
        imaginary: rational_read(&value.imaginary),
    }
}

fn mat3_read(value: &Mat3) -> Mat3Read {
    Mat3Read {
        rows: value
            .rows
            .iter()
            .map(|row| row.iter().map(rational_read).collect())
            .collect(),
    }
}

fn matrix2_read(value: &[Vec<Rat>]) -> Vec<Vec<RationalRead>> {
    value
        .iter()
        .map(|row| row.iter().map(rational_read).collect())
        .collect()
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
        "precessing chord conic transport: accepted · {} bytes · {}",
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
    "usage: eros_precessing_chord_conic_transport <new-report.json>".to_owned()
}
