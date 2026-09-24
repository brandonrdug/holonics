//! Cross-owner checks for the exact causal chord, kept beside the engine owners they compare.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::Zero;
use holonic_engine::lattice_gauge;
use holonic_engine::physical_constraint_complex::{ConstraintEdge, ConstraintVertexId};
use holonic_engine::physical_constraint_grading::EdgeProvenance;
use holonic_engine::rigidity_receiver::{ExactConfiguration, RigidityJacobian, rigidity_reading};
use holonics::causal_chord::*;
use holonics::exact_linear::ExactRatMatrix;
use holonics::geometry::Rat;
use holonics::rational_polynomial::RationalPolynomial;

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().copied().map(integer).collect())
            .collect(),
    )
    .expect("a declared integer matrix is rectangular")
}

/// Ascending coefficients, as the polynomial owner stores them.
fn polynomial(ascending: &[i64]) -> RationalPolynomial {
    RationalPolynomial::new(ascending.iter().copied().map(integer).collect())
}

fn column(entries: &[i64]) -> ExactRatMatrix {
    ExactRatMatrix::shaped(
        entries.len(),
        1,
        entries.iter().map(|value| vec![integer(*value)]).collect(),
    )
    .expect("a column is rectangular")
}

fn row(entries: &[i64]) -> ExactRatMatrix {
    ExactRatMatrix::shaped(
        1,
        entries.len(),
        vec![entries.iter().copied().map(integer).collect()],
    )
    .expect("a row is rectangular")
}

fn declared(lineage: &str, state: &[&[i64]], excite: &[i64], read: &[i64]) -> Linearization {
    Linearization::declared(
        lineage,
        matrix(state),
        column(excite),
        row(read),
        vec!["u".to_owned()],
        vec!["y".to_owned()],
    )
    .expect("the declared linearization is well shaped")
}

// ---------------------------------------------------------------------------------------------
// the expansion
// ---------------------------------------------------------------------------------------------

/// **The recurrence agrees with the owner it is not replacing.**
///
/// `exact_linear.rs:336` already computes the characteristic polynomial by the same recurrence and

/// **The mode population agrees with the existing spectrum owner.**
///
/// [`rational_mode_supports`] reads its rational eigenvalues through the prime-lifting route
/// because `lattice_gauge::exact_spectrum`'s Sturm census descends from a Cauchy bound that a
/// physical network operator makes astronomically wide. On material where both routes are cheap
/// they must agree exactly, and this is what holds them to it.
#[test]
fn the_mode_population_agrees_with_the_existing_spectrum_owner() {
    for state in [
        matrix(&[&[1, 0], &[0, 2]]),
        matrix(&[&[2, 1, 0], &[0, 2, 0], &[0, 0, -3]]),
        matrix(&[&[0, 1], &[2, 0]]),
    ] {
        let base = Linearization::single_probe("spectrum", state.clone(), 0, 0)
            .expect("declared");
        let mine = rational_mode_supports(&base).expect("the modes return");
        let owner = lattice_gauge::exact_spectrum(&state).expect("the spectrum returns");
        let population = mine
            .iter()
            .map(|mode| (mode.eigenvalue.clone(), mode.algebraic_multiplicity))
            .collect::<Vec<_>>();
        assert_eq!(population, owner.rational_eigenvalues, "{state:?}");
    }
    // And a defective rational eigenvalue is reported as defective rather than as a second mode.
    let defective = Linearization::single_probe(
        "defective",
        matrix(&[&[2, 1, 0], &[0, 2, 0], &[0, 0, -3]]),
        0,
        0,
    )
    .expect("declared");
    let modes = rational_mode_supports(&defective).expect("the modes return");
    let doubled = modes
        .iter()
        .find(|mode| mode.eigenvalue == integer(2))
        .expect("2 is a rational eigenvalue");
    assert_eq!(doubled.algebraic_multiplicity, 2);
    assert_eq!(doubled.geometric_multiplicity, 1);
    assert!(doubled.is_defective());
}

// ---------------------------------------------------------------------------------------------
// the elastic network, synthetically
// ---------------------------------------------------------------------------------------------

fn place(coordinates: &[i64]) -> Vec<Rat> {
    coordinates.iter().copied().map(integer).collect()
}

fn triangle_jacobian() -> RigidityJacobian {
    let configuration = ExactConfiguration::declared(
        2,
        [
            (ConstraintVertexId(1), place(&[0, 0])),
            (ConstraintVertexId(2), place(&[4, 0])),
            (ConstraintVertexId(3), place(&[0, 3])),
        ],
    )
    .expect("a declared configuration");
    let mut constraints = BTreeMap::new();
    for (left, right) in [(1, 2), (1, 3), (2, 3)] {
        let (edge, _) = ConstraintEdge::new(
            ConstraintVertexId(left),
            ConstraintVertexId(right),
        )
        .expect("a well-formed edge");
        constraints.insert(edge, EdgeProvenance::Polygonal);
    }
    RigidityJacobian::found("synthetic-triangle", &configuration, &constraints)
        .expect("the Jacobian returns")
}

/// **The construction the M5 reading uses, with no fixture at all.**
///
/// `A = −JᵀJ` on a rigid planar triangle. Its kernel is exactly `ker J` — the infinitesimal motions
/// the rigidity receiver already returns — so the axis count of the chord's spectrum and `dim ker J`
/// are the same number computed two ways, and the operator is negative semidefinite with no
/// right-half-plane mode at all.
#[test]
fn the_elastic_network_of_a_rigid_triangle_has_its_motions_on_the_axis() {
    let jacobian = triangle_jacobian();
    let reading = rigidity_reading(&jacobian).expect("the rigidity reading returns");
    let network = elastic_network(
        "synthetic-triangle",
        &jacobian.matrix,
        NetworkForm::OverdampedRelaxation,
        0,
        4,
    )
    .expect("the network returns");
    let count = half_plane_from_symmetric(&network.state).expect("the inertia route returns");
    assert_eq!(count.right, 0, "−JᵀJ is negative semidefinite");
    assert_eq!(
        count.axis, reading.motion_dimension,
        "the axis modes are exactly the infinitesimal motions"
    );
    assert_eq!(count.left + count.axis, 6);

    let chord = causal_chord_read(&network, PoleReading::Named).expect("the chord returns");
    assert_eq!(chord.extent, 6);
    assert!(chord.semisimple, "a symmetric operator is semisimple");
    // Every returned component carries its whole provenance.
    for component in &chord.components {
        assert_eq!(component.lineage, "synthetic-triangle");
        assert_eq!(component.excitation, 0);
        assert_eq!(component.transport_path, 0);
        assert!(component.residual.is_zero());
    }
    // The transfer entry's certificate is exactly zero and the reduced denominator divides the
    // characteristic polynomial.
    let entry = &chord.transfer.entries[0];
    assert!(entry.residual.is_zero());
    assert!(
        entry
            .denominator
            .divided_exactly_by(&entry.reduced_denominator)
            .is_ok()
    );
}

// ---------------------------------------------------------------------------------------------
// the measured M5 presentation
// ---------------------------------------------------------------------------------------------

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The RBX1 chain is the one component present in all three presentations.
const RBX1_RESIDUES: usize = 108;
/// The residue window the chord is measured on. The exact transfer object of a `3·n × 3·n` operator
/// is a `3n`-step Faddeev–LeVerrier recurrence over exact rationals; the window is **declared here**
/// rather than inferred, and it is smaller than the rigidity receiver's twenty-four because this
/// receiver computes a characteristic polynomial and that one computes a rank.
const WINDOW: usize = 5;
/// Eight angstroms, squared, on the exact decimal wire the intake reads.
const CONTACT_SQUARED: i64 = 64;

/// One alpha carbon, exactly: the deposited decimal is a rational and is used as one.
fn exact_decimal(token: &str) -> Result<Rat, String> {
    let token = token
        .strip_prefix('\'')
        .and_then(|body| body.strip_suffix('\''))
        .unwrap_or(token);
    let negative = token.starts_with('-');
    let unsigned = token.trim_start_matches(['-', '+']);
    let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
    if whole.is_empty()
        || !whole.chars().all(|character| character.is_ascii_digit())
        || !fraction.chars().all(|character| character.is_ascii_digit())
    {
        return Err(format!("coordinate token {token:?} is not a plain decimal"));
    }
    let digits = format!("{whole}{fraction}");
    let numerator = digits
        .parse::<BigInt>()
        .map_err(|error| error.to_string())?;
    let denominator = BigInt::from(10_u8).pow(fraction.len() as u32);
    let value = Rat::new(numerator, denominator);
    Ok(if negative { -value } else { value })
}

/// The alpha carbons of every chain, in residue order, as exact rational places.
fn read_alpha_carbons(path: &Path) -> Result<BTreeMap<String, Vec<Vec<Rat>>>, String> {
    let text = std::fs::read_to_string(path).map_err(|error| error.to_string())?;
    let lines = text.lines().collect::<Vec<_>>();
    let mut headers = Vec::<String>::new();
    let mut rows = Vec::<Vec<&str>>::new();
    let mut at = 0usize;
    while at < lines.len() {
        if lines[at].trim() != "loop_" {
            at += 1;
            continue;
        }
        let mut cursor = at + 1;
        let mut candidate = Vec::<String>::new();
        while cursor < lines.len() && lines[cursor].trim_start().starts_with('_') {
            candidate.push(lines[cursor].trim().to_owned());
            cursor += 1;
        }
        if !candidate.iter().any(|name| name.starts_with("_atom_site.")) {
            at = cursor;
            continue;
        }
        headers = candidate;
        while cursor < lines.len() {
            let line = lines[cursor].trim();
            if line == "#" || line == "loop_" || line.starts_with('_') {
                break;
            }
            if !line.is_empty() {
                let fields = line.split_whitespace().collect::<Vec<_>>();
                if fields.len() != headers.len() {
                    return Err(format!(
                        "{} atom_site row {} has {} fields under {} headers",
                        path.display(),
                        cursor + 1,
                        fields.len(),
                        headers.len()
                    ));
                }
                rows.push(fields);
            }
            cursor += 1;
        }
        break;
    }
    if headers.is_empty() || rows.is_empty() {
        return Err(format!("{} has no atom_site loop", path.display()));
    }
    let column_of = |name: &str| -> Result<usize, String> {
        headers
            .iter()
            .position(|candidate| candidate == name)
            .ok_or_else(|| format!("{} has no {name} atom_site face", path.display()))
    };
    let atom = column_of("_atom_site.label_atom_id")?;
    let chain = column_of("_atom_site.label_asym_id")?;
    let x = column_of("_atom_site.Cartn_x")?;
    let y = column_of("_atom_site.Cartn_y")?;
    let z = column_of("_atom_site.Cartn_z")?;

    let mut chains: BTreeMap<String, Vec<Vec<Rat>>> = BTreeMap::new();
    for entry in rows {
        if entry[atom] != "CA" {
            continue;
        }
        let mut point = Vec::with_capacity(3);
        for axis in [x, y, z] {
            point.push(exact_decimal(entry[axis])?);
        }
        chains.entry(entry[chain].to_owned()).or_default().push(point);
    }
    Ok(chains)
}

fn squared_distance(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter().zip(right).fold(Rat::zero(), |sum, (a, b)| {
        let difference = a - b;
        sum + &difference * &difference
    })
}

/// The rigidity Jacobian of one declared residue window of one M5 presentation.
fn measured_jacobian(lineage: &'static str, path: &Path) -> Result<RigidityJacobian, String> {
    let chains = read_alpha_carbons(path)?;
    let rbx1 = chains
        .values()
        .filter(|places| places.len() == RBX1_RESIDUES)
        .collect::<Vec<_>>();
    if rbx1.len() != 1 {
        return Err(format!(
            "{} carries {} chains of {RBX1_RESIDUES} alpha carbons, not one",
            path.display(),
            rbx1.len()
        ));
    }
    let window = &rbx1[0][..WINDOW];
    let configuration = ExactConfiguration::declared(
        3,
        window
            .iter()
            .enumerate()
            .map(|(at, point)| (ConstraintVertexId(at as u64 + 1), point.clone())),
    )
    .map_err(|error| error.to_string())?;
    let aperture = Rat::from_integer(BigInt::from(CONTACT_SQUARED));
    let mut constraints = BTreeMap::new();
    for left in 0..WINDOW {
        for right in (left + 1)..WINDOW {
            let backbone = right == left + 1;
            if !backbone && squared_distance(&window[left], &window[right]) > aperture {
                continue;
            }
            let (edge, _) = ConstraintEdge::new(
                ConstraintVertexId(left as u64 + 1),
                ConstraintVertexId(right as u64 + 1),
            )
            .map_err(|error| error.to_string())?;
            constraints.insert(
                edge,
                if backbone {
                    EdgeProvenance::Polygonal
                } else {
                    EdgeProvenance::AdmittedContact
                },
            );
        }
    }
    RigidityJacobian::found(lineage, &configuration, &constraints)
        .map_err(|error| error.to_string())
}

/// **The measured causal chord of one authenticated M5 presentation.**
///
/// The object is the rigidity receiver's own exact rational Jacobian on a declared five-residue
/// window of the RBX1 chain. The declared elastic-network form is `A = −JᵀJ`: the overdamped
/// relaxation of the quadratic constraint energy at unit mobility, which is symmetric negative
/// semidefinite with `ker A = ker J`. The declared probe site is the first coordinate of the first
/// residue and the declared readout site is the first coordinate of the third residue, so the chord
/// is the response transported along the chain.
///
/// The reading is [`PoleReading::Named`] and says so: the poles are named by their exact squarefree
/// factors and their multiplicities, the half-plane population comes from Sylvester's signature
/// through `inertia.rs:375` rather than from the Routh–Hurwitz route, and no isolating boxes are
/// taken. **Absent the release this test refuses.** Every law this module owns is checked without
/// any fixture by the synthetic tests above.
///
/// **`#[ignore]`d because it is a measurement, not a law.** A fifteen-coordinate exact
/// Faddeev–LeVerrier recurrence over rationals whose numerators reach a hundred and twenty digits
/// costs 38 s on the declared workstation, against under a second for every other test in this
/// module. Run it with
/// `cargo test -p holonic-engine --test causal_chord_engine the_causal_chord_measures -- --ignored --nocapture`.
/// Measured 2026-09-17 on `designed-free-rbx1.cif`: extent 15, 10 constraints, `rank J = 9`,
/// `dim ker J = 6`, spectrum `(left, axis, right) = (9, 6, 0)`, characteristic degree 15, atlas
/// denominator degree 10, cancelled degree 5, one pole factor, two components, residual exactly 0.
#[test]
#[ignore = "a 38 s exact measurement on the authenticated M5 release, not a law"]
fn the_causal_chord_measures_one_m5_presentation() {
    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured causal chord cannot be \
         taken, and this test refuses to report success without taking it. Place the authenticated \
         release at that path, or set {STRUCTURE_ROOT_ENV} to the directory carrying \
         designed-free-rbx1.cif. Every law this module owns is checked without any fixture by the \
         synthetic tests above, in particular \
         the_elastic_network_of_a_rigid_triangle_has_its_motions_on_the_axis.",
        root.display()
    );
    let jacobian = measured_jacobian("designed-free", &root.join("designed-free-rbx1.cif"))
        .unwrap_or_else(|error| panic!("designed-free: {error}"));
    let rigidity = rigidity_reading(&jacobian).expect("the rigidity reading returns");

    let probe = 0;
    let readout_site = 6;
    let network = elastic_network(
        "designed-free|rbx1|window5|-JtJ",
        &jacobian.matrix,
        NetworkForm::OverdampedRelaxation,
        probe,
        readout_site,
    )
    .expect("the network returns");
    assert_eq!(network.extent(), 3 * WINDOW);

    // The half-plane population, through the owner that already answers it exactly for a symmetric
    // form. The axis count must equal `dim ker J`, which the rigidity receiver computed
    // independently as a rank.
    let count = half_plane_from_symmetric(&network.state).expect("the inertia route returns");
    assert_eq!(count.right, 0, "−JᵀJ carries no growing mode");
    assert_eq!(
        count.axis, rigidity.motion_dimension,
        "the axis modes of −JᵀJ are exactly the infinitesimal motions of J"
    );
    assert_eq!(count.total(), 3 * WINDOW);

    let chord = causal_chord_read(&network, PoleReading::Named).expect("the chord returns");
    assert!(chord.semisimple);
    assert_eq!(chord.poles.accounted(), chord.transfer.atlas_denominator.degree().unwrap_or(0));
    let entry = &chord.transfer.entries[0];
    assert!(entry.residual.is_zero());
    assert!(
        entry.reduced_numerator.degree().unwrap_or(0)
            <= entry.reduced_denominator.degree().unwrap_or(0),
        "a strictly proper network response has no polynomial part"
    );
    for component in &chord.components {
        assert_eq!(component.excitation, 0);
        assert_eq!(component.transport_path, 0);
        assert_eq!(component.lineage, "designed-free|rbx1|window5|-JtJ");
        assert!(component.residual.is_zero());
    }

    println!(
        "causal_chord M5 | designed-free | window {WINDOW} residues | extent {} | constraints {} \
         | rank J {} | dim ker J {} | spectrum (left, axis, right) ({}, {}, {}) | \
         det degree {} | atlas denominator degree {} | cancelled degree {} | pole factors {} | \
         components {} | probe coordinate {probe} | readout coordinate {readout_site} | \
         reading Named | residual 0",
        network.extent(),
        jacobian.constraint_count(),
        rigidity.rank,
        rigidity.motion_dimension,
        count.left,
        count.axis,
        count.right,
        chord.characteristic().degree().unwrap_or(0),
        chord.transfer.atlas_denominator.degree().unwrap_or(0),
        chord.hidden_modes.degree().unwrap_or(0),
        chord.poles.factors.len(),
        chord.components.len(),
    );
}

/// **The certified reading of the same degree-fifteen M5 chord.**
///
/// [`PoleReading::Certified`] adds, to everything [`PoleReading::Named`] returns, a Sturm-certified
/// isolating box per real root of every pole factor and a sign-certified half-plane count. On this
/// object the denominator is degree ten over a characteristic polynomial of degree fifteen whose
/// coefficients reach a hundred and twenty digits, which is exactly the size at which the isolation
/// owner's cost decides whether the certified reading is affordable at all.
///
/// The reading is compared against the `Named` one on the parts both carry, so the certification
/// is held to change nothing but what it adds.
#[test]
#[ignore = "the certified degree-15 reading of the authenticated M5 chord; measured cost is printed"]
fn the_certified_chord_reads_the_same_m5_presentation() {
    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the certified chord cannot be \
         measured, and this test refuses to report success without measuring it. Place the \
         authenticated release at that path, or set {STRUCTURE_ROOT_ENV} to the directory carrying \
         designed-free-rbx1.cif.",
        root.display()
    );
    let jacobian = measured_jacobian("designed-free", &root.join("designed-free-rbx1.cif"))
        .unwrap_or_else(|error| panic!("designed-free: {error}"));
    let network = elastic_network(
        "designed-free|rbx1|window5|-JtJ",
        &jacobian.matrix,
        NetworkForm::OverdampedRelaxation,
        0,
        6,
    )
    .expect("the network returns");

    let started = std::time::Instant::now();
    let named = causal_chord_read(&network, PoleReading::Named).expect("the named chord returns");
    let named_elapsed = started.elapsed();

    let started = std::time::Instant::now();
    let certified =
        causal_chord_read(&network, PoleReading::Certified).expect("the certified chord returns");
    let certified_elapsed = started.elapsed();

    assert_eq!(certified.poles.factors.len(), named.poles.factors.len());
    assert_eq!(certified.poles.accounted(), named.poles.accounted());
    assert_eq!(
        certified.transfer.atlas_denominator,
        named.transfer.atlas_denominator
    );
    let count = certified
        .poles
        .half_plane
        .clone()
        .expect("the certified reading carries the half-plane count");
    assert_eq!(
        count.total(),
        certified.transfer.atlas_denominator.degree().unwrap_or(0),
        "the certified half-plane count must account for the whole atlas denominator"
    );

    // The degree-fifteen cross-check the plan asks for: Routh-Hurwitz on the characteristic
    // polynomial against Sylvester's signature on the same symmetric operator.
    let started = std::time::Instant::now();
    let by_routh =
        half_plane_count(certified.characteristic()).expect("the Routh-Hurwitz route returns");
    let routh_elapsed = started.elapsed();
    let symmetric = half_plane_from_symmetric(&network.state).expect("the symmetric route returns");
    assert_eq!(
        (by_routh.left, by_routh.axis, by_routh.right),
        (symmetric.left, symmetric.axis, symmetric.right),
        "the Routh-Hurwitz half-plane count disagrees with Sylvester's signature on the same \
         symmetric operator"
    );

    let isolations: usize = certified
        .poles
        .factors
        .iter()
        .map(|factor| factor.real_isolations.len())
        .sum();
    println!(
        "causal_chord M5 certified | designed-free | characteristic degree {} | denominator \
         degree {} | pole factors {} | real isolations {} | denominator half-plane \
         (left, axis, right) ({}, {}, {}) | characteristic half-plane ({}, {}, {}) | \
         Named {:?} | Certified {:?} | degree-15 Routh-Hurwitz {:?}",
        certified.characteristic().degree().unwrap_or(0),
        certified.transfer.atlas_denominator.degree().unwrap_or(0),
        certified.poles.factors.len(),
        isolations,
        count.left,
        count.axis,
        count.right,
        by_routh.left,
        by_routh.axis,
        by_routh.right,
        named_elapsed,
        certified_elapsed,
        routh_elapsed,
    );
}
