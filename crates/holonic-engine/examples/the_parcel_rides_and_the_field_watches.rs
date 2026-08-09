//! The parcel rides, and the field watches: two routes to one harmonic measure.
//!
//! `crates/holonic-engine/src/diffusion.rs` is Eulerian. It assembles `M = C + tau*L` over the whole
//! complex (`:456-468`), inverts the interior block exactly (`:474`), and refuses at `:499` when the
//! inverse residual is not identically zero. Its rows `−M_II⁻¹ M_I∂` are the hitting distribution of
//! the killed walk — the discrete harmonic measure.
//!
//! `crates/holonic-engine/src/parcel.rs` is Lagrangian. It releases a cohort at an interior site,
//! forks at every admissible passage, retains the ordered word each parcel spelled, and reports
//! where the mass went.
//!
//! The two are glued by the boundary-integral identity, exact at every horizon:
//!
//! ```text
//!   E[x][b]  ==  lower_k[x][b]  +  SUM over interior v of  open_k[x][v] * E[v][b]
//! ```
//!
//! Nothing here is tuned. Every figure is an exact rational and every one is printed whole.

use std::collections::BTreeMap;

use holonic_engine::diffusion::{
    DiffusionBoundaryTransferCertificate, DiffusionBranch, DiffusionComplex, DiffusionEvent,
    DiffusionNode, ExactDiffusionLaw,
};
use holonic_engine::parcel::{
    BoundaryIntegralReading, DiffusionCarriedField, Letter, ParcelCohort, ParcelError,
    ParcelSite, WordSeparation, boundary_integral_reading, harmonic_measure, separating_word,
};
use holonic_engine::{CurrentBranchId, CurrentNodeId};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use relational_geometry::Rat;

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

/// The interior sites, the boundary sites, and the letter every branch spells.
const INTERIOR: [u64; 3] = [1, 2, 3];
const BOUNDARY: [u64; 2] = [10, 11];

/// Three interior sites, two boundary sites, and no two conductances equal.
///
/// `kelvin.rs`'s falsifier `equal_capacities_collapse_the_two_transports_and_unequal_ones_separate_them`
/// is the reason nothing here is equal to anything else: a complex with equal weights collapses
/// transports that unequal ones separate, and a cross-check run on collapsed transports is a check
/// whose material cannot vary the property under test.
fn declared_complex() -> DiffusionComplex {
    DiffusionComplex::new(
        [
            (1u64, rational(1, 5)),
            (2, rational(1, 7)),
            (3, rational(1, 3)),
            (10, integer(2)),
            (11, integer(3)),
        ]
        .map(|(node, capacity)| DiffusionNode {
            node: CurrentNodeId(node),
            capacity,
        }),
        [
            (1u64, 1u64, 2u64, integer(3)),
            (2, 2, 3, rational(5, 2)),
            (3, 1, 3, rational(7, 3)),
            (4, 1, 10, rational(1, 2)),
            (5, 3, 11, integer(4)),
            (6, 2, 11, rational(1, 4)),
            (7, 2, 10, rational(6, 5)),
        ]
        .map(|(branch, source, target, conductance)| DiffusionBranch {
            branch: CurrentBranchId(branch),
            source: CurrentNodeId(source),
            target: CurrentNodeId(target),
            conductance,
        }),
    )
    .expect("the declared diffusion complex is well formed")
}

/// The same complex with each interior--interior branch split into three parallel branches whose
/// conductances sum to the original, all three spelling the original's letter.
///
/// The assembled operator is bit-identical: `diffusion.rs:463-467` accumulates `-= coupling` per
/// branch, so three parallel conductances summing to `c` produce the same entry as one of `c`. The
/// retained words are identical too, because the three spell one letter. What changes by orders of
/// magnitude is the **path** population.
fn split_complex() -> (DiffusionComplex, BTreeMap<CurrentBranchId, Letter>) {
    let mut branches = Vec::new();
    let mut letters = BTreeMap::new();
    let splits: [(u64, u64, u64, [Rat; 3]); 3] = [
        (1, 1, 2, [integer(1), integer(1), integer(1)]),
        (2, 2, 3, [rational(1, 2), integer(1), integer(1)]),
        (3, 1, 3, [rational(1, 3), integer(1), integer(1)]),
    ];
    for (original, source, target, shares) in splits {
        for (index, conductance) in shares.into_iter().enumerate() {
            let branch = CurrentBranchId(original * 100 + index as u64 + 1);
            letters.insert(branch, Letter(original));
            branches.push(DiffusionBranch {
                branch,
                source: CurrentNodeId(source),
                target: CurrentNodeId(target),
                conductance,
            });
        }
    }
    for branch in declared_complex().branches().values() {
        if branch.branch.0 > 3 {
            branches.push(branch.clone());
        }
    }
    let complex = DiffusionComplex::new(declared_complex().nodes().values().cloned(), branches)
        .expect("the split complex is well formed");
    (complex, letters)
}

/// Run one declared event so `diffusion.rs` compiles and certifies its own boundary transfer.
fn certify(complex: &DiffusionComplex, interval: &Rat) -> DiffusionBoundaryTransferCertificate {
    let law = ExactDiffusionLaw::with_boundary(
        complex.clone(),
        BOUNDARY.map(CurrentNodeId),
    )
    .expect("the diffusion law admits the declared boundary");
    let standing = law
        .initial_standing(
            complex
                .nodes()
                .keys()
                .map(|node| (*node, Rat::zero()))
                .collect(),
        )
        .expect("the standing populates every node");
    let (_, receipt) = law
        .enact(
            &standing,
            &DiffusionEvent {
                interval: interval.clone(),
                source: BTreeMap::new(),
            },
        )
        .expect("the declared event completes");
    receipt.transfer.certificate
}

fn render_word(word: &[Letter]) -> String {
    if word.is_empty() {
        return "<empty>".to_owned();
    }
    word.iter()
        .map(|letter| format!("b{}", letter.0))
        .collect::<Vec<_>>()
        .join(" ")
}

fn print_reading(reading: &BoundaryIntegralReading) {
    println!(
        "  release {:?}  steps {}  open mass {}  dissipated {}  stalled {}",
        reading.release.0, reading.steps, reading.open_mass, reading.dissipated_mass,
        reading.stalled_mass
    );
    for term in &reading.terms {
        println!(
            "    boundary {:>2}   parcel_lower {:>28}   frontier_tail {:>28}",
            term.boundary.0,
            term.parcel_lower.to_string(),
            term.frontier_tail.to_string()
        );
        println!(
            "                   glued        {:>28}   eulerian      {:>28}   residual {}",
            term.glued.to_string(),
            term.eulerian.to_string(),
            term.residual
        );
    }
    println!(
        "    identity exact: {}     enclosure contains the Eulerian value: {}",
        reading.exact(),
        reading.contained()
    );
}

fn main() {
    let interval = integer(1);
    let complex = declared_complex();
    let certificate = certify(&complex, &interval);
    let eulerian = harmonic_measure(&certificate);
    let field = DiffusionCarriedField::new(&complex, interval.clone(), BOUNDARY.map(CurrentNodeId));
    let boundary = field.boundary().to_vec();
    // Caller-declared. Nothing in `parcel.rs` picks it and nothing derives it there; this driver is
    // the caller and it declares what it can hold.
    let declared_width: u64 = 1 << 20;

    println!("THE PARCEL RIDES, AND THE FIELD WATCHES");
    println!("=======================================");

    println!("\nI. THE DECLARED COMPLEX");
    println!("  interval tau = {interval}");
    println!("  node   capacity      role");
    for node in complex.nodes().values() {
        let role = if BOUNDARY.contains(&node.node.0) {
            "boundary (absorbing)"
        } else {
            "interior"
        };
        println!("  {:>4}   {:>10}    {role}", node.node.0, node.capacity.to_string());
    }
    println!("  branch  from -> to    conductance   letter");
    for branch in complex.branches().values() {
        println!(
            "  {:>6}  {:>4} -> {:<4}  {:>11}   b{}",
            branch.branch.0,
            branch.source.0,
            branch.target.0,
            branch.conductance.to_string(),
            branch.branch.0
        );
    }

    println!("\nII. THE EULERIAN ROUTE  --  -M_II^-1 M_I@  read off diffusion.rs's certificate");
    let residual_is_zero = certificate
        .interior_inverse_residual
        .iter()
        .flatten()
        .chain(certificate.boundary_inverse_residual.iter().flatten())
        .all(Zero::is_zero);
    println!("  diffusion.rs's own inverse residuals identically zero: {residual_is_zero}");
    println!("  the assembled operator M = C + tau*L, in node order {:?}",
        certificate.node_order.iter().map(|node| node.0).collect::<Vec<_>>());
    for (row, node) in certificate.node_order.iter().enumerate() {
        println!(
            "    {:>4} | {}",
            node.0,
            certificate.operator[row]
                .iter()
                .map(|value| format!("{value:>10}"))
                .collect::<Vec<_>>()
                .join("  ")
        );
    }
    println!("  harmonic measure, row by row (rows do NOT sum to one: the capacity kills):");
    for site in INTERIOR.map(ParcelSite) {
        let row = &eulerian[&site];
        let total = row.values().fold(Rat::zero(), |sum, value| sum + value);
        println!(
            "    E[{}] = {{ {} }}   row sum {}   (killed share {})",
            site.0,
            row.iter()
                .map(|(target, value)| format!("{} -> {}", target.0, value))
                .collect::<Vec<_>>()
                .join(",  "),
            total.to_string(),
            Rat::from_integer(BigInt::from(1)) - total
        );
    }

    println!("\nIII. THE RETAINED WORDS  --  the complete landed population at horizon 4 from site 1");
    let short = ParcelCohort::advanced_to(&field, ParcelSite(1), 4, declared_width)
        .expect("the declared width holds this frontier");
    println!(
        "  {} landed entries, {} riding, {} dissipated; nothing is truncated",
        short.landed().len(),
        short.riding().len(),
        short.dissipated().len()
    );
    for (word, site, carried) in short.landed_words() {
        println!(
            "    {:<26} -> boundary {:>2}   mass {:>34}   paths {}",
            render_word(&word),
            site.0,
            carried.mass.to_string(),
            carried.paths
        );
    }

    println!("\nIV. THE CROSS-CHECK  --  both routes, entry by entry, at horizon 8");
    for release in INTERIOR.map(ParcelSite) {
        let cohort = ParcelCohort::advanced_to(&field, release, 8, declared_width)
            .expect("the declared width holds this frontier");
        print_reading(&boundary_integral_reading(&cohort, &boundary, &eulerian));
    }

    println!("\nV. THE ORBIT  --  the retained remainder shrinks and the identity holds at each horizon");
    println!("  horizon   frontier width   distinct words   open mass (exact)                       residuals");
    let mut cohort = ParcelCohort::release(&field, ParcelSite(1));
    for horizon in 0..=10 {
        let reading = boundary_integral_reading(&cohort, &boundary, &eulerian);
        println!(
            "  {horizon:>7}   {:>14}   {:>14}   {:>38}   {}",
            cohort.frontier_width(),
            cohort.distinct_words(),
            reading.open_mass.to_string(),
            if reading.exact() { "all zero" } else { "NONZERO" }
        );
        cohort = cohort
            .advanced(&field, declared_width)
            .expect("the declared width holds this frontier");
    }

    println!("\nVI. THE CONTROL AND ITS ORBIT");
    println!("  The identity is asserted against an Eulerian atlas built from a complex whose branch 5");
    println!("  carries conductance 9/2 instead of 4. Nothing else moves. Every residual must leave zero.");
    let mut moved_branches = complex.branches().values().cloned().collect::<Vec<_>>();
    for branch in &mut moved_branches {
        if branch.branch == CurrentBranchId(5) {
            branch.conductance = rational(9, 2);
        }
    }
    let moved = DiffusionComplex::new(complex.nodes().values().cloned(), moved_branches)
        .expect("the moved complex is well formed");
    let moved_eulerian = harmonic_measure(&certify(&moved, &interval));
    let control = ParcelCohort::advanced_to(&field, ParcelSite(1), 8, declared_width)
        .expect("the declared width holds this frontier");
    print_reading(&boundary_integral_reading(&control, &boundary, &moved_eulerian));
    println!("  (the same cohort against the unmoved atlas, for the orbit:)");
    print_reading(&boundary_integral_reading(&control, &boundary, &eulerian));
    println!();
    println!("  The two checks are NOT equally sharp, and the difference is measurable. The identity");
    println!("  refuses the moved atlas at every horizon; the enclosure cannot see the move until the");
    println!("  retained remainder is narrower than it. Where the enclosure first closes past it:");
    println!("  horizon   open mass                                    identity exact   enclosure contains");
    let mut control_cohort = ParcelCohort::advanced_to(&field, ParcelSite(1), 6, declared_width)
        .expect("the declared width holds this frontier");
    for horizon in 6..=16 {
        let reading = boundary_integral_reading(&control_cohort, &boundary, &moved_eulerian);
        println!(
            "  {horizon:>7}   {:>42}   {:>14}   {}",
            reading.open_mass.to_string(),
            reading.exact(),
            reading.contained()
        );
        if !reading.contained() {
            break;
        }
        control_cohort = control_cohort
            .advanced(&field, declared_width)
            .expect("the declared width holds this frontier");
    }

    println!("\nVII. THE SEPARATING WORD ON A REAL FORK");
    let words = short.landed_words();
    let mut exhibited = 0usize;
    for index in 0..words.len() {
        for other in index + 1..words.len() {
            let separation = separating_word(&words[index].0, &words[other].0);
            let show = match separation {
                WordSeparation::Separated { index: at, .. } => at >= 1 && exhibited < 4,
                WordSeparation::Prefix { .. } => exhibited < 4,
                WordSeparation::Identical => false,
            };
            if !show {
                continue;
            }
            exhibited += 1;
            println!(
                "  {:<24} vs {:<24}  ->  {:?}",
                render_word(&words[index].0),
                render_word(&words[other].0),
                separation
            );
        }
    }
    let fork = ParcelCohort::advanced_to(&field, ParcelSite(1), 2, declared_width).unwrap();
    let riding = fork.riding_words();
    println!("  the fork itself, at horizon 2 from site 1 -- every admissible continuation retained:");
    for (word, site, carried) in &riding {
        println!(
            "    {:<16} riding at site {:>2}   mass {:>26}   paths {}",
            render_word(word),
            site.0,
            carried.mass.to_string(),
            carried.paths
        );
    }
    println!(
        "  frontier mass {} + landed {} + dissipated {} = {}",
        fork.open_mass(),
        fork.landed_mass(),
        fork.dissipated_mass(),
        fork.open_mass() + fork.landed_mass() + fork.dissipated_mass()
    );

    println!("\nVIII. THE FACTORIZATION  --  distinct words against path population");
    let (split, letters) = split_complex();
    let split_certificate = certify(&split, &interval);
    let split_eulerian = harmonic_measure(&split_certificate);
    println!(
        "  the split complex has {} branches against {}; its harmonic measure is identical: {}",
        split.branches().len(),
        complex.branches().len(),
        split_eulerian == eulerian
    );
    let split_field = DiffusionCarriedField::with_declared_letters(
        &split,
        interval.clone(),
        BOUNDARY.map(CurrentNodeId),
        &letters,
    );
    println!("  horizon   distinct words   path population        ratio (floor)   open mass equal");
    for horizon in 1..=12 {
        let plain = ParcelCohort::advanced_to(&field, ParcelSite(1), horizon, declared_width)
            .expect("the declared width holds this frontier");
        let split_cohort =
            ParcelCohort::advanced_to(&split_field, ParcelSite(1), horizon, declared_width)
                .expect("the declared width holds this frontier");
        let words = BigUint::from(split_cohort.distinct_words());
        let paths = split_cohort.path_population();
        println!(
            "  {horizon:>7}   {:>14}   {:>17}   {:>13}   {}",
            words,
            paths,
            &paths / &words,
            plain.open_mass() == split_cohort.open_mass()
                && plain.distinct_words() == split_cohort.distinct_words()
        );
    }
    let deep = ParcelCohort::advanced_to(&split_field, ParcelSite(1), 12, declared_width)
        .expect("the declared width holds this frontier");
    println!(
        "  at horizon 12 the split cohort's identity against the split atlas is exact: {}",
        boundary_integral_reading(&deep, &boundary, &split_eulerian).exact()
    );

    println!("\nIX. THE OBSTRUCTION  --  a declared width the material exceeds");
    let standing = ParcelCohort::advanced_to(&field, ParcelSite(1), 5, declared_width)
        .expect("the declared width holds this frontier");
    let required = standing
        .advanced(&field, declared_width)
        .expect("the declared width holds this frontier")
        .frontier_width();
    for declared in [1u64, 16, 64] {
        match standing.advanced(&field, declared) {
            Err(ParcelError::TerminalWidthExceeded {
                required: named,
                declared: refused,
            }) => println!(
                "  declared width {refused:>3}  ->  refused, naming required width {named} (actual {required})"
            ),
            Ok(_) => println!("  declared width {declared:>3}  ->  admitted"),
            Err(other) => println!("  declared width {declared:>3}  ->  {other}"),
        }
    }
    let unchanged = ParcelCohort::advanced_to(&field, ParcelSite(1), 5, declared_width).unwrap();
    println!(
        "  standing preserved through the refusals: {}",
        standing == unchanged
    );

    println!("\nX. PRIMITIVE CLOSED WORDS  --  parcels that came back to site 1");
    let closed = ParcelCohort::advanced_to(&field, ParcelSite(1), 6, declared_width)
        .expect("the declared width holds this frontier");
    let census = closed.primitive_closed_word_census();
    println!(
        "  primitive closed word census by length (index 0 is length one): {:?}",
        census.iter().map(|count| count.to_string()).collect::<Vec<_>>()
    );
    println!(
        "  {} closed words of which {} primitive; the complete primitive population at length <= 3:",
        closed.closed_words().len(),
        closed.primitive_closed_words().len()
    );
    for word in closed.primitive_closed_words() {
        if word.word.len() > 3 {
            continue;
        }
        println!(
            "    {:<20}  returned mass {:>26}   paths {}",
            render_word(&word.word),
            word.returned.mass.to_string(),
            word.returned.paths
        );
    }
    let repeated = closed
        .closed_words()
        .iter()
        .filter(|word| !word.primitive)
        .take(3)
        .collect::<Vec<_>>();
    println!("  and the non-primitive ones this filters out, exhibited so the filter is legible:");
    for word in repeated {
        println!("    {}", render_word(&word.word));
    }
    println!("  Note b1 b1: a parcel retracing the branch it just took spells a SQUARE, so half of");
    println!("  Ihara's non-backtracking condition arrives from the word rather than from a rule.");
    println!(
        "  comparable in shape to relational_geometry::IharaSignature::primitive_oriented_cycles,"
    );
    println!(
        "  which is indexed the same way. NOT the same population: Ihara quotients by the cyclic"
    );
    println!(
        "  choice of starting dart and admits no backtracking; a closed word here is rooted at the"
    );
    println!("  release site and a parcel may retrace the passage it just took.");
}
