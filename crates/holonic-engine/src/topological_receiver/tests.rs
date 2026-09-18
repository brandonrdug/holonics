//! The topological receiver's own checks.
//!
//! Every law — the filtration and its `Open` order, the persistence pairing over `ℚ` and over
//! `𝔽_p`, the integral torsion beside it, the community reading, the crossing convention, the
//! linking number and the refusal discipline — is checked on synthetic exact material that needs
//! no fixture and runs everywhere. The last test is the measured M5 reading: it **refuses** rather
//! than reports success when the authenticated release is absent.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::Instant;

use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

use super::*;
use crate::EventId;
use crate::physical_intake::mmcif::StructurePresentation;
use crate::rebase_invariants::PivotRule;

// ---------------------------------------------------------------------------------------------
// synthetic material
// ---------------------------------------------------------------------------------------------

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn place(x: i64, y: i64, z: i64) -> [Rat; 3] {
    [integer(x), integer(y), integer(z)]
}

fn point_box(x: i64, y: i64, z: i64) -> CoordinateBox3 {
    CoordinateBox3::point(integer(x), integer(y), integer(z))
}

fn positions(places: &[(u64, [i64; 3])]) -> BTreeMap<ConstraintVertexId, CoordinateBox3> {
    places
        .iter()
        .map(|(id, place)| {
            (
                ConstraintVertexId(*id),
                point_box(place[0], place[1], place[2]),
            )
        })
        .collect()
}

fn one_component(
    places: &[(u64, [i64; 3])],
) -> BTreeMap<ConstraintVertexId, ConstraintComponentId> {
    places
        .iter()
        .map(|(id, _)| (ConstraintVertexId(*id), ConstraintComponentId(1)))
        .collect()
}

/// The four corners of a square of side two: every side squared is four, every diagonal eight.
const SQUARE: [(u64, [i64; 3]); 4] = [
    (1, [0, 0, 0]),
    (2, [2, 0, 0]),
    (3, [2, 2, 0]),
    (4, [0, 2, 0]),
];

fn square_filtration(top_grade: u32) -> ApertureFiltration {
    ApertureFiltration::found(
        "square",
        EventId(1),
        &positions(&SQUARE),
        &one_component(&SQUARE),
        integer(8),
        top_grade,
        256,
    )
    .expect("the square filtration stands")
}

fn rational_reading(filtration: &ApertureFiltration) -> (FiltrationOrder, PersistenceReading) {
    let order = FiltrationOrder::found(filtration, &OrderLaw::ByLowerBound)
        .expect("the by-lower-bound order is admissible");
    let reading = persistence(filtration, &order, &Coefficients::Rational, 1_000_000)
        .expect("the rational reduction returns");
    (order, reading)
}

// ---------------------------------------------------------------------------------------------
// 1. the filtration and its readings
// ---------------------------------------------------------------------------------------------

#[test]
fn the_square_births_a_cycle_at_the_side_and_kills_it_at_the_diagonal() {
    let filtration = square_filtration(2);
    assert!(filtration.order_is_determinate());
    assert!(open_order_pairs(&filtration).is_empty());
    // Four vertices, six one-cells, four two-cells: every triple's largest edge is a diagonal.
    assert_eq!(filtration.complex.f_vector()[&0], 4);
    assert_eq!(filtration.complex.f_vector()[&1], 6);
    assert_eq!(filtration.complex.f_vector()[&2], 4);

    let (order, reading) = rational_reading(&filtration);

    // The one-skeleton at the diagonal is the complete graph on four vertices, whose first Betti
    // number is three; two of those cycles are born and die at the same exact value, when the
    // diagonals and the triangles arrive together. Exactly one cycle lives at an aperture.
    let cycles = reading.pairs_at_grade(1);
    assert_eq!(cycles.len(), 3);
    assert_eq!(
        cycles.iter().filter(|pair| pair.is_exactly_trivial()).count(),
        2,
        "the two diagonal cycles are born and killed at squared aperture eight together"
    );
    let living = cycles
        .iter()
        .filter(|pair| !pair.is_exactly_trivial())
        .collect::<Vec<_>>();
    assert_eq!(living.len(), 1, "one cycle lives at an aperture: the square");
    let cycle = living[0];
    assert_eq!(cycle.birth_value, ExactInterval::point(integer(4)));
    assert_eq!(
        cycle.death_value,
        Some(ExactInterval::point(integer(8))),
        "the cycle dies exactly when the diagonal arrives, at squared aperture eight"
    );
    assert!(!cycle.is_exactly_trivial());

    // Three components die at the side, one is essential.
    let components = reading.pairs_at_grade(0);
    assert_eq!(components.len(), 4);
    assert_eq!(reading.essential_count(0), 1);
    assert_eq!(
        components
            .iter()
            .filter(|pair| pair.death_value == Some(ExactInterval::point(integer(4))))
            .count(),
        3
    );

    // At the side aperture the square is a circle; at the diagonal it is a filled sphere shell.
    let cut_at_four = order
        .order
        .iter()
        .take_while(|cell| filtration.value_of(**cell).expect("a value").upper <= integer(4))
        .count();
    assert_eq!(reading.betti_at(0, cut_at_four), 1);
    assert_eq!(reading.betti_at(1, cut_at_four), 1);
    let whole = order.order.len();
    assert_eq!(reading.betti_at(0, whole), 1);
    assert_eq!(reading.betti_at(1, whole), 0);
    assert_eq!(
        reading.betti_at(2, whole),
        1,
        "the two-skeleton of a tetrahedron is a sphere, so a cavity stands at the top grade"
    );
}

#[test]
fn the_three_cell_kills_the_cavity_at_the_same_exact_value() {
    let filtration = square_filtration(3);
    assert_eq!(filtration.complex.f_vector()[&3], 1);
    let (_, reading) = rational_reading(&filtration);
    let cavities = reading.pairs_at_grade(2);
    assert_eq!(cavities.len(), 1);
    assert!(
        cavities[0].is_exactly_trivial(),
        "the cavity is born and dies at squared aperture eight: it lives at no aperture at all, \
         and that is an exact statement and not a tolerance"
    );
    assert_eq!(reading.betti_at(2, filtration.cell_count()), 0);
}

#[test]
fn an_interval_position_makes_the_order_open_and_the_reading_a_family() {
    // One occurrence carries a coordinate box of width, so its squared distances are intervals.
    let mut boxes = positions(&SQUARE);
    boxes.insert(
        ConstraintVertexId(4),
        CoordinateBox3 {
            x: ExactInterval::new(Rat::zero(), integer(1)).expect("a forward interval"),
            y: ExactInterval::point(integer(2)),
            z: ExactInterval::point(Rat::zero()),
        },
    );
    let filtration = ApertureFiltration::found(
        "open-square",
        EventId(1),
        &boxes,
        &one_component(&SQUARE),
        integer(16),
        2,
        256,
    )
    .expect("the filtration stands over interval positions");

    assert!(!filtration.order_is_determinate());
    let open = open_order_pairs(&filtration);
    assert!(
        !open.is_empty(),
        "an interval position leaves at least one comparison undecided"
    );
    for pair in &open {
        assert_eq!(
            compare_values(&pair.left_value, &pair.right_value),
            ValueOrder::Open
        );
    }

    // Both bounds of the family are admissible orders, and they are different orders.
    let lower = FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound)
        .expect("the lower bound is admissible");
    let upper = FiltrationOrder::found(&filtration, &OrderLaw::ByUpperBound)
        .expect("the upper bound is admissible");
    assert_ne!(
        lower.order, upper.order,
        "the two bounds of the family are two different orders, which is what makes the reading \
         plural rather than a tie-break"
    );
    for order in [&lower, &upper] {
        let reading = persistence(&filtration, order, &Coefficients::Rational, 1_000_000)
            .expect("each member of the family reduces");
        assert_eq!(reading.open_order_pairs, open.len());
        assert_eq!(reading.betti_at(0, filtration.cell_count()), 1);
    }
}

#[test]
fn a_declared_order_contradicting_a_decided_comparison_is_refused() {
    let filtration = square_filtration(1);
    let lower = FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound).expect("admissible");
    // The last one-cell is a diagonal at eight; a vertex is at zero. Putting the diagonal first
    // contradicts a decided comparison and is refused by name.
    let mut reversed = lower.order.clone();
    reversed.reverse();
    let refusal = FiltrationOrder::found(&filtration, &OrderLaw::Declared(reversed))
        .expect_err("a reversed order is not a filtration order");
    assert!(
        matches!(
            refusal,
            TopologicalError::OrderIsNotAFiltration { .. }
                | TopologicalError::OrderContradictsExactValues { .. }
        ),
        "{refusal}"
    );

    let mut doubled = lower.order.clone();
    doubled[1] = doubled[0];
    assert!(matches!(
        FiltrationOrder::found(&filtration, &OrderLaw::Declared(doubled))
            .expect_err("naming a cell twice is refused"),
        TopologicalError::OrderNamesCellTwice(_)
    ));

    let short = lower.order[..2].to_vec();
    assert!(matches!(
        FiltrationOrder::found(&filtration, &OrderLaw::Declared(short))
            .expect_err("an incomplete order is refused"),
        TopologicalError::OrderPopulationDisagrees { .. }
    ));
}

// ---------------------------------------------------------------------------------------------
// 2. field dependence, made visible
// ---------------------------------------------------------------------------------------------

/// The six-vertex triangulation of the real projective plane: ten triangles, fifteen edges,
/// Euler characteristic one. Its integral first homology is `ℤ/2`, so the rational reading and
/// the `𝔽₂` reading **must** disagree — which is the whole point of reporting torsion beside a
/// field reading.
const PROJECTIVE_PLANE: [[usize; 3]; 10] = [
    [0, 1, 2],
    [0, 2, 3],
    [0, 3, 4],
    [0, 4, 5],
    [0, 1, 5],
    [1, 2, 4],
    [2, 3, 5],
    [1, 3, 4],
    [2, 4, 5],
    [1, 3, 5],
];

fn simplicial_filtration(
    lineage: &str,
    vertex_count: usize,
    maximal: &[[usize; 3]],
) -> ApertureFiltration {
    let mut faces: BTreeSet<Vec<usize>> = BTreeSet::new();
    for face in maximal {
        for size in 1..=3 {
            for chosen in super::combinations(3, size) {
                let mut simplex = chosen.iter().map(|at| face[*at]).collect::<Vec<_>>();
                simplex.sort_unstable();
                faces.insert(simplex);
            }
        }
    }
    let mut ordered = faces.into_iter().collect::<Vec<_>>();
    ordered.sort_by_key(|simplex| (simplex.len(), simplex.clone()));

    let source_events = BTreeSet::from([EventId(1)]);
    let mut complex = GradedCausalComplex::default();
    let mut cells_by_simplex: BTreeMap<Vec<usize>, CausalCellId> = BTreeMap::new();
    let mut entry = BTreeMap::new();
    for simplex in &ordered {
        let mut boundary = CausalChain::default();
        if simplex.len() > 1 {
            for removed in 0..simplex.len() {
                let mut face = simplex.clone();
                face.remove(removed);
                boundary.add_term(
                    cells_by_simplex[&face],
                    ComparativeMultiplicity::from_hand(
                        if removed % 2 == 0 { 1 } else { -1 },
                        1_u8,
                    )
                    .expect("a unit hand"),
                );
            }
        }
        let cell = complex
            .found_cell(
                format!("{simplex:?}"),
                source_events.clone(),
                u32::try_from(simplex.len() - 1).expect("a small grade"),
                boundary,
            )
            .expect("the simplex stands");
        cells_by_simplex.insert(simplex.clone(), cell);
        entry.insert(
            cell,
            ExactInterval::point(integer(simplex.len() as i64 - 1)),
        );
    }
    let occurrences = (0..vertex_count)
        .map(|at| ConstraintVertexId(at as u64 + 1))
        .collect::<Vec<_>>();
    let component_of = occurrences
        .iter()
        .map(|id| (*id, ConstraintComponentId(1)))
        .collect();
    ApertureFiltration::found_declared(DeclaredFiltration {
        lineage: lineage.to_owned(),
        source_event: EventId(1),
        complex,
        occurrences,
        component_of,
        cells_by_simplex,
        entry,
        ceiling: integer(2),
    })
    .expect("the declared filtration stands")
}

#[test]
fn the_projective_plane_separates_the_rational_reading_from_the_field_two_reading() {
    let filtration = simplicial_filtration("projective-plane", 6, &PROJECTIVE_PLANE);
    assert_eq!(filtration.complex.f_vector()[&0], 6);
    assert_eq!(filtration.complex.f_vector()[&1], 15);
    assert_eq!(filtration.complex.f_vector()[&2], 10);

    let order = FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound).expect("admissible");
    let whole = filtration.cell_count();

    let rational = persistence(&filtration, &order, &Coefficients::Rational, 1_000_000)
        .expect("the rational reduction returns");
    assert_eq!(
        [
            rational.betti_at(0, whole),
            rational.betti_at(1, whole),
            rational.betti_at(2, whole)
        ],
        [1, 0, 0],
        "over the rationals the projective plane looks like a point"
    );

    let field_two = persistence(
        &filtration,
        &order,
        &Coefficients::PrimeField(BigUint::from(2_u8)),
        1_000_000,
    )
    .expect("the field-two reduction returns");
    assert_eq!(
        [
            field_two.betti_at(0, whole),
            field_two.betti_at(1, whole),
            field_two.betti_at(2, whole)
        ],
        [1, 1, 1],
        "over F_2 a cycle and a cavity stand where the rational reading saw nothing"
    );

    let field_three = persistence(
        &filtration,
        &order,
        &Coefficients::PrimeField(BigUint::from(3_u8)),
        1_000_000,
    )
    .expect("the field-three reduction returns");
    assert_eq!(
        [
            field_three.betti_at(0, whole),
            field_three.betti_at(1, whole),
            field_three.betti_at(2, whole)
        ],
        [1, 0, 0],
        "three does not divide the torsion, so F_3 agrees with the rationals"
    );
}

#[test]
fn the_integral_profile_names_the_prime_at_which_the_fields_part() {
    let filtration = simplicial_filtration("projective-plane", 6, &PROJECTIVE_PLANE);
    let profile = integral_profile(&filtration, &[integer(0), integer(1), integer(2)], PivotRule::FirstNonzero)
        .expect("the integral profile returns");
    assert_eq!(profile.steps.len(), 3);
    assert!(!profile.is_torsion_free());
    assert_eq!(
        profile.field_dependence_primes(),
        BTreeSet::from([BigUint::from(2_u8)]),
        "the Smith normal form names two, and two is exactly the prime at which the field \
         readings part"
    );
    let top = profile.steps.last().expect("a last step");
    assert_eq!(top.refusing.betti_vector(), vec![1, 0, 0]);
    assert_eq!(top.refusing.total_torsion(), vec![BigInt::from(2)]);
    assert_eq!(
        top.refusing.euler_characteristic(),
        top.refusing.cell_euler_characteristic(),
        "the Euler characteristic is the cheapest cross-check and it holds"
    );
    assert_eq!(top.refusing.cell_euler_characteristic(), 1);
    assert!(
        top.open_cells.is_empty(),
        "a point-valued filtration leaves no cell open at any aperture it carries"
    );
}

#[test]
fn the_rational_persistence_agrees_with_the_integral_betti_numbers_at_every_aperture() {
    let filtration = square_filtration(2);
    let (order, reading) = rational_reading(&filtration);
    for aperture in [integer(0), integer(4), integer(8)] {
        let (refusing, _, open) = sublevel_family(&filtration, &aperture);
        assert!(open.is_empty());
        let cut = order
            .order
            .iter()
            .take_while(|cell| refusing.contains(*cell))
            .count();
        assert_eq!(cut, refusing.len());
        let invariants =
            rebase_invariants_on(&filtration.complex, Some(&refusing), PivotRule::FirstNonzero)
                .expect("the integral invariants return");
        for (grade, betti) in invariants.betti_vector().iter().enumerate() {
            assert_eq!(
                reading.betti_at(grade as u32, cut),
                *betti,
                "the field reduction and the integer Smith normal form disagree at grade {grade} \
                 and squared aperture {aperture}"
            );
        }
    }
}

#[test]
fn a_composite_modulus_is_refused_because_it_is_not_a_field() {
    let filtration = square_filtration(1);
    let order = FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound).expect("admissible");
    let refusal = persistence(
        &filtration,
        &order,
        &Coefficients::PrimeField(BigUint::from(6_u8)),
        1_000,
    )
    .expect_err("six is not prime");
    assert!(matches!(refusal, TopologicalError::ModulusIsNotPrime(_)));
}

/// **A large composite modulus is named composite, not trial-divided to its square root.**
///
/// `2³² + 1 = 641 · 6700417`, the fifth Fermat number. The smallest factor is 641, so trial
/// division would find it quickly; the point of the test is that the deterministic decision
/// returns the same refusal.
#[test]
fn a_large_composite_modulus_is_refused_by_name() {
    let refusal = PrimeField::declared(&BigUint::from(4_294_967_297_u64))
        .expect_err("the fifth Fermat number is 641 times 6700417");
    assert!(
        matches!(refusal, TopologicalError::ModulusIsNotPrime(_)),
        "{refusal}"
    );
}

/// **A hard sixty-four-bit composite is decided, not searched for a factor.**
///
/// `(2³² − 5)(2³² − 17) = 18_446_743_979_220_271_189`. Both factors are prime and both are above
/// `4 × 10⁹`, so trial division to the square root is over four billion `BigUint` divisions and
/// would not return inside a test. The deterministic Miller–Rabin decision refuses it in twelve
/// modular exponentiations.
#[test]
fn a_hard_sixty_four_bit_composite_is_refused_without_searching_for_its_factor() {
    let started = Instant::now();
    let refusal = PrimeField::declared(&BigUint::from(18_446_743_979_220_271_189_u64))
        .expect_err("a product of two thirty-two bit primes is not prime");
    assert!(
        matches!(refusal, TopologicalError::ModulusIsNotPrime(_)),
        "{refusal}"
    );
    assert!(
        started.elapsed().as_secs() < 5,
        "the decision is twelve modular exponentiations; a wait here is trial division"
    );
}

/// **A modulus past the bit ceiling is refused by name, immediately.**
///
/// `2¹²⁷ − 1` is a genuine Mersenne prime, so no factor exists to be found: trial division to its
/// square root is `2⁶³` divisions and never returns. The receiver refuses the *declaration*
/// instead, and says so by name rather than accepting it on a probabilistic test.
#[test]
fn a_modulus_past_the_bit_ceiling_is_refused_rather_than_trial_divided() {
    let modulus = (BigUint::from(1_u8) << 127) - BigUint::from(1_u8);
    let started = Instant::now();
    let refusal = PrimeField::declared(&modulus).expect_err("one hundred and twenty-seven bits");
    assert!(
        matches!(
            refusal,
            TopologicalError::ModulusExceedsPrimalityCeiling {
                bits: 127,
                ceiling: MODULUS_BIT_CEILING
            }
        ),
        "{refusal}"
    );
    assert!(
        started.elapsed().as_secs() < 5,
        "the ceiling is read off the bit length; a wait here is the unbounded trial division"
    );

    // The same refusal reaches a caller who declared the field for a reading.
    let filtration = square_filtration(1);
    let order = FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound).expect("admissible");
    assert!(matches!(
        persistence(
            &filtration,
            &order,
            &Coefficients::PrimeField(modulus),
            1_000
        )
        .expect_err("the reading refuses the modulus before it reduces"),
        TopologicalError::ModulusExceedsPrimalityCeiling { .. }
    ));
}

/// **A genuine prime inside the ceiling is accepted, and the reading over it runs.**
///
/// `18_446_744_073_709_551_557` is the largest prime below `2⁶⁴`. Trial division would be over
/// four billion divisions; the deterministic base set decides it exactly.
#[test]
fn a_large_genuine_prime_inside_the_ceiling_is_accepted() {
    let started = Instant::now();
    PrimeField::declared(&BigUint::from(18_446_744_073_709_551_557_u64))
        .expect("the largest prime below two to the sixty-fourth is a field");
    assert!(
        started.elapsed().as_secs() < 5,
        "the decision is twelve modular exponentiations"
    );

    // And it is a field the reduction actually runs over: the six-vertex real projective plane
    // reads `(1,0,0)` over every field of odd characteristic, this one included.
    let filtration = simplicial_filtration("projective-plane", 6, &PROJECTIVE_PLANE);
    let order = FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound).expect("admissible");
    let reading = persistence(
        &filtration,
        &order,
        // 2³¹ − 1, a Mersenne prime, which the trial-division route would have taken 46,341
        // `BigUint` divisions to admit.
        &Coefficients::PrimeField(BigUint::from(2_147_483_647_u64)),
        1_000_000,
    )
    .expect("the reduction over a thirty-one bit prime returns");
    let whole = filtration.cell_count();
    assert_eq!(
        [
            reading.betti_at(0, whole),
            reading.betti_at(1, whole),
            reading.betti_at(2, whole)
        ],
        [1, 0, 0],
        "the projective plane's torsion is at two, so every odd characteristic reads as the \
         rationals do"
    );
}

// ---------------------------------------------------------------------------------------------
// 3. persistent rank and the pairing
// ---------------------------------------------------------------------------------------------

#[test]
fn the_persistent_rank_shrinks_along_the_order() {
    let filtration = square_filtration(2);
    let (order, reading) = rational_reading(&filtration);
    let extent = order.order.len();
    for grade in 0..=2u32 {
        for early in 0..=extent {
            for late in early..extent {
                assert!(
                    persistent_rank(&reading, grade, early, late + 1)
                        <= persistent_rank(&reading, grade, early, late),
                    "the rank of a longer transport never exceeds the rank of a shorter one"
                );
                assert!(
                    persistent_rank(&reading, grade, early, late)
                        <= persistent_rank(&reading, grade, early + 1, late),
                    "admitting an earlier birth never lowers the rank"
                );
            }
            assert_eq!(
                persistent_rank(&reading, grade, early, early),
                reading.betti_at(grade, early),
                "the rank of the identity transport is the Betti number at that index"
            );
        }
    }
}

#[test]
fn the_pairing_multiplicity_is_determined_by_the_persistent_ranks() {
    // The Lean theorem `multiplicity_eq`, replayed on the executable reading: the number of bars
    // born at one position and dying at another is an inclusion–exclusion of four persistent
    // ranks, so two pairings with equal persistent ranks are the same pairing.
    let filtration = square_filtration(2);
    let (order, reading) = rational_reading(&filtration);
    let extent = order.order.len();
    for grade in 0..=2u32 {
        for birth in 0..extent {
            for death in birth..extent {
                let direct = reading
                    .pairs
                    .iter()
                    .filter(|pair| {
                        pair.grade == grade
                            && pair.birth_position == birth
                            && pair.death_position == Some(death)
                    })
                    .count();
                let inverted = persistent_rank(&reading, grade, birth + 1, death) as i64
                    - persistent_rank(&reading, grade, birth, death) as i64
                    - persistent_rank(&reading, grade, birth + 1, death + 1) as i64
                    + persistent_rank(&reading, grade, birth, death + 1) as i64;
                assert_eq!(
                    direct as i64, inverted,
                    "grade {grade}, birth {birth}, death {death}"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// 4. contact-community persistence
// ---------------------------------------------------------------------------------------------

#[test]
fn the_community_persistence_agrees_with_the_grade_zero_pairs() {
    // Two chains of two occurrences each, far apart along x, joined only at the widest aperture.
    let places = [
        (1, [0, 0, 0]),
        (2, [1, 0, 0]),
        (3, [5, 0, 0]),
        (4, [6, 0, 0]),
    ];
    let boxes = positions(&places);
    let mut component_of = BTreeMap::new();
    component_of.insert(ConstraintVertexId(1), ConstraintComponentId(1));
    component_of.insert(ConstraintVertexId(2), ConstraintComponentId(1));
    component_of.insert(ConstraintVertexId(3), ConstraintComponentId(2));
    component_of.insert(ConstraintVertexId(4), ConstraintComponentId(2));

    let filtration = ApertureFiltration::found(
        "two-chains",
        EventId(1),
        &boxes,
        &component_of,
        integer(36),
        1,
        256,
    )
    .expect("the filtration stands");
    let (order, reading) = rational_reading(&filtration);
    // The **library** holds the two computations to agreement: `grade_zero_agreement` runs both
    // and refuses if they part. The test asks for the reading, it does not perform the comparison
    // itself.
    let agreement =
        grade_zero_agreement(&filtration, &order, &reading).expect("the two computations agree");
    let communities = &agreement.communities;
    assert_eq!(agreement.standing, reading.essential_count(0));
    assert_eq!(agreement.merge_values, communities.merge_values);

    let junction = communities.component_junction
        [&(ConstraintComponentId(1), ConstraintComponentId(2))]
        .clone()
        .expect("the two chains do join below the ceiling");
    assert_eq!(
        junction,
        ExactInterval::point(integer(16)),
        "the nearest cross-chain pair is at squared distance sixteen, and that exact value is \
         when the two presented chains become one contact community"
    );
}

/// **A disagreement between the two grade-zero computations is a refusal, in the library.**
///
/// The plan says the matrix reduction's grade-0 deaths and the union–find's community merges are
/// *required to agree*. That is a claim about the library, so this test corrupts one reading and
/// asks the library — not the test — to notice: one death value is moved, and
/// [`grade_zero_agreement`] must refuse by name rather than prefer a route. Without the
/// comparison in the library the corrupted reading would be returned as a reading.
#[test]
fn a_grade_zero_reading_that_disagrees_with_the_communities_is_refused() {
    let filtration = square_filtration(1);
    let (order, reading) = rational_reading(&filtration);
    grade_zero_agreement(&filtration, &order, &reading).expect("the honest reading agrees");

    let mut corrupted = reading.clone();
    let moved = corrupted
        .pairs
        .iter_mut()
        .find(|pair| pair.grade == 0 && pair.death_value.is_some())
        .expect("the square kills three components");
    moved.death_value = Some(ExactInterval::point(integer(999)));
    let refusal = grade_zero_agreement(&filtration, &order, &corrupted)
        .expect_err("a moved death value is a disagreement between the two computations");
    assert!(
        matches!(refusal, TopologicalError::GradeZeroReadingsDisagree(_)),
        "{refusal}"
    );

    // And dropping a grade-zero death outright parts the two multisets by length.
    let mut truncated = reading.clone();
    let dropped = truncated
        .pairs
        .iter()
        .position(|pair| pair.grade == 0 && pair.death_value.is_some())
        .expect("the square kills three components");
    truncated.pairs.remove(dropped);
    assert!(matches!(
        grade_zero_agreement(&filtration, &order, &truncated)
            .expect_err("a dropped grade-zero pair is a disagreement"),
        TopologicalError::GradeZeroReadingsDisagree(_)
    ));

    // A reading taken under a different order law is not a reading of this one and is refused by
    // name rather than compared, because a disagreement would then say nothing.
    let upper = FiltrationOrder::found(&filtration, &OrderLaw::ByUpperBound).expect("admissible");
    let elsewhere = persistence(&filtration, &upper, &Coefficients::Rational, 1_000_000)
        .expect("the upper-bound reading returns");
    assert!(matches!(
        grade_zero_agreement(&filtration, &order, &elsewhere)
            .expect_err("that reading is of another order"),
        TopologicalError::ReadingIsNotOfThisFiltration { .. }
    ));
}

// ---------------------------------------------------------------------------------------------
// 5. crossings, linking, writhe
// ---------------------------------------------------------------------------------------------

/// A polygonal Hopf link: a diamond in the plane `z = 0` about the origin, and a diamond in the
/// plane `y = 0` about `(2,0,0)`. The second crosses the first's disc exactly once.
fn hopf() -> (ClosedPolygon, ClosedPolygon) {
    let left = ClosedPolygon::declared(
        "hopf-left",
        vec![
            place(2, 0, 0),
            place(0, 2, 0),
            place(-2, 0, 0),
            place(0, -2, 0),
        ],
    )
    .expect("the left curve stands");
    let right = ClosedPolygon::declared(
        "hopf-right",
        vec![
            place(4, 0, 0),
            place(2, 0, 2),
            place(0, 0, 0),
            place(2, 0, -2),
        ],
    )
    .expect("the right curve stands");
    (left, right)
}

fn candidate_directions() -> Vec<[Rat; 3]> {
    vec![
        place(1, 2, 3),
        place(2, 3, 5),
        place(3, 5, 7),
        place(1, 1, 2),
        place(5, 7, 11),
        place(-1, 2, -3),
        place(7, 3, 2),
    ]
}

#[test]
fn the_hopf_link_returns_plus_or_minus_one_under_every_admissible_direction() {
    let (left, right) = hopf();
    let across = linking_under_directions(&left, &right, &candidate_directions())
        .expect("at least one candidate is admissible");
    assert!(
        across.readings.len() >= 3,
        "only {} of the declared candidates were admissible",
        across.readings.len()
    );
    assert!(
        across.agree(),
        "the linking number is projection invariant and the readings disagree: {:?}",
        across
            .readings
            .iter()
            .map(|reading| reading.linking_number)
            .collect::<Vec<_>>()
    );
    assert_eq!(across.value().expect("a value").abs(), 1);
    for reading in &across.readings {
        assert_eq!(reading.left_over_right, reading.right_over_left);
        assert_eq!(reading.total_signed, 2 * reading.linking_number);
        assert!(!reading.crossings.is_empty());
    }
}

/// The first declared candidate this pair admits, so no test hard-codes a direction whose
/// admissibility it has not checked.
fn first_admissible(left: &ClosedPolygon, right: &ClosedPolygon) -> [Rat; 3] {
    for candidate in candidate_directions() {
        let Ok(direction) = ProjectionDirection::declared(candidate.clone()) else {
            continue;
        };
        if linking_number(left, right, &direction).is_ok() {
            return candidate;
        }
    }
    panic!("no declared candidate direction is admissible for this pair");
}

#[test]
fn the_linking_number_is_symmetric_in_its_two_curves() {
    let (left, right) = hopf();
    let direction =
        ProjectionDirection::declared(first_admissible(&left, &right)).expect("admissible");
    let forward = linking_number(&left, &right, &direction).expect("the reading returns");
    let backward = linking_number(&right, &left, &direction).expect("the reading returns");
    assert_eq!(forward.linking_number, backward.linking_number);
    assert_eq!(forward.total_signed, backward.total_signed);
}

#[test]
fn the_linking_number_is_unmoved_by_reversing_the_direction() {
    let (left, right) = hopf();
    let candidate = first_admissible(&left, &right);
    let direction = ProjectionDirection::declared(candidate.clone()).expect("admissible");
    let reversed = direction.reversed().expect("the reverse is admissible");
    let forward = linking_number(&left, &right, &direction).expect("the reading returns");
    let backward = linking_number(&left, &right, &reversed).expect("the reading returns");
    assert_eq!(
        forward.linking_number, backward.linking_number,
        "reversing the direction swaps every over and under and negates every determinant, so \
         each sign is unmoved"
    );

    let scaled = ProjectionDirection::declared([
        &candidate[0] * &integer(3),
        &candidate[1] * &integer(3),
        &candidate[2] * &integer(3),
    ])
    .expect("admissible");
    let scaled_reading = linking_number(&left, &right, &scaled).expect("the reading returns");
    assert_eq!(forward.linking_number, scaled_reading.linking_number);
}

#[test]
fn the_unlink_returns_a_decided_zero() {
    let left = ClosedPolygon::declared(
        "far-left",
        vec![place(0, 0, 0), place(1, 0, 0), place(1, 1, 0)],
    )
    .expect("stands");
    let right = ClosedPolygon::declared(
        "far-right",
        vec![place(50, 0, 0), place(51, 0, 0), place(51, 1, 1)],
    )
    .expect("stands");
    let across = linking_under_directions(&left, &right, &candidate_directions())
        .expect("some candidate is admissible");
    assert!(across.agree());
    assert_eq!(
        across.value(),
        Some(0),
        "two curves that exist and do not link return a decided zero; that is a reading, not a \
         refusal"
    );
}

/// One closed polygon, two admissible directions, two different projected writhes.
#[test]
fn the_projected_writhe_is_not_projection_invariant() {
    let curve = ClosedPolygon::declared(
        "skew-quadrilateral",
        vec![
            place(0, 0, 0),
            place(2, 0, 1),
            place(2, 2, 0),
            place(0, 2, 1),
        ],
    )
    .expect("stands");
    let along_y = ProjectionDirection::declared(place(0, 1, 0)).expect("admissible");
    let along_z = ProjectionDirection::declared(place(0, 0, 1)).expect("admissible");
    let seen_from_y = projected_writhe(&curve, &along_y).expect("the reading returns");
    let seen_from_z = projected_writhe(&curve, &along_z).expect("the reading returns");
    assert_eq!(seen_from_y.projected_writhe, 1);
    assert_eq!(seen_from_z.projected_writhe, 0);
    assert_ne!(
        seen_from_y.projected_writhe, seen_from_z.projected_writhe,
        "the projected writhe is a reading of a declared direction and is not an invariant of the \
         curve. The averaged writhe is a different object and this module does not claim it"
    );
}

// ---------------------------------------------------------------------------------------------
// 6. degenerate geometry, refused rather than perturbed
// ---------------------------------------------------------------------------------------------

#[test]
fn a_coincident_step_is_refused_before_any_projection() {
    let refusal = ClosedPolygon::declared(
        "coincident",
        vec![place(0, 0, 0), place(0, 0, 0), place(1, 1, 1)],
    )
    .expect_err("a zero-length step is not a step");
    assert!(matches!(
        refusal,
        TopologicalError::Degenerate(ProjectionDegeneracy::ZeroLengthSegment { .. })
    ));

    let short = ClosedPolygon::declared("short", vec![place(0, 0, 0), place(1, 0, 0)])
        .expect_err("two vertices are not a closed curve");
    assert!(matches!(short, TopologicalError::PolygonTooShort { .. }));
}

#[test]
fn a_segment_parallel_to_the_projection_is_refused_by_name() {
    let curve = ClosedPolygon::declared(
        "along-z",
        vec![place(0, 0, 0), place(0, 0, 4), place(3, 0, 2)],
    )
    .expect("stands");
    let other = ClosedPolygon::declared(
        "elsewhere",
        vec![place(1, 1, 1), place(2, 1, 1), place(2, 3, 1)],
    )
    .expect("stands");
    let direction = ProjectionDirection::declared(place(0, 0, 1)).expect("admissible");
    let refusal = linking_number(&curve, &other, &direction)
        .expect_err("a segment parallel to the direction has no projected direction");
    assert!(
        matches!(
            refusal,
            TopologicalError::Degenerate(ProjectionDegeneracy::SegmentParallelToProjection {
                curve: 0,
                segment: 0
            })
        ),
        "{refusal}"
    );
    assert!(matches!(
        ProjectionDirection::declared(place(0, 0, 0))
            .expect_err("the zero direction is not a direction"),
        TopologicalError::Degenerate(ProjectionDegeneracy::ZeroProjectionDirection)
    ));
}

#[test]
fn overlapping_collinear_projections_are_refused_by_name() {
    // Both curves carry a segment on the x axis; projected along z they lie on one line and
    // overlap, so no transversal crossing exists and none is invented.
    let left = ClosedPolygon::declared(
        "on-the-axis",
        vec![place(0, 0, 0), place(4, 0, 0), place(2, 3, 0)],
    )
    .expect("stands");
    let right = ClosedPolygon::declared(
        "above-the-axis",
        vec![place(1, 0, 1), place(3, 0, 1), place(2, -3, 1)],
    )
    .expect("stands");
    let direction = ProjectionDirection::declared(place(0, 0, 1)).expect("admissible");
    let refusal = linking_number(&left, &right, &direction)
        .expect_err("overlapping collinear projections are not a generic diagram");
    assert!(
        matches!(
            refusal,
            TopologicalError::Degenerate(ProjectionDegeneracy::ProjectedSegmentsCollinear { .. })
        ),
        "{refusal}"
    );
}

#[test]
fn two_curves_sharing_a_place_are_refused_by_name() {
    let left = ClosedPolygon::declared(
        "left",
        vec![place(0, 0, 0), place(4, 0, 0), place(2, 3, 1)],
    )
    .expect("stands");
    let right = ClosedPolygon::declared(
        "right",
        vec![place(0, 0, 0), place(1, 5, 2), place(3, 4, 6)],
    )
    .expect("stands");
    let direction = ProjectionDirection::declared(place(1, 2, 3)).expect("admissible");
    let refusal = linking_number(&left, &right, &direction)
        .expect_err("two curves sharing a place are not two disjoint curves");
    assert!(
        matches!(
            refusal,
            TopologicalError::Degenerate(ProjectionDegeneracy::CurvesTouch { .. })
        ),
        "{refusal}"
    );
}

#[test]
fn two_curves_touching_in_space_are_refused_at_equal_height() {
    // The two triangles meet at the point (2,0,0), which is interior to a segment of each.
    let left = ClosedPolygon::declared(
        "horizontal",
        vec![place(0, 0, 0), place(4, 0, 0), place(2, 4, 0)],
    )
    .expect("stands");
    let right = ClosedPolygon::declared(
        "vertical",
        vec![place(2, -4, 0), place(2, 3, 0), place(6, 0, 4)],
    )
    .expect("stands");
    let direction = ProjectionDirection::declared(place(0, 0, 1)).expect("admissible");
    let refusal = linking_number(&left, &right, &direction)
        .expect_err("two strands at equal height have no over and no under");
    assert!(
        matches!(
            refusal,
            TopologicalError::Degenerate(ProjectionDegeneracy::EqualHeightAtCrossing { .. })
        ),
        "{refusal}"
    );
}

#[test]
fn a_crossing_at_an_endpoint_is_refused() {
    // The right curve's vertex (2,1,1) projects, along z, exactly onto the interior of the left
    // curve's first segment.
    let left = ClosedPolygon::declared(
        "base",
        vec![place(0, 1, 0), place(4, 1, 0), place(2, 5, 0)],
    )
    .expect("stands");
    let right = ClosedPolygon::declared(
        "touching",
        vec![place(2, 1, 3), place(2, -4, 3), place(6, -4, 5)],
    )
    .expect("stands");
    let direction = ProjectionDirection::declared(place(0, 0, 1)).expect("admissible");
    let refusal = linking_number(&left, &right, &direction)
        .expect_err("a crossing at a segment endpoint is not generic");
    assert!(
        matches!(
            refusal,
            TopologicalError::Degenerate(ProjectionDegeneracy::CrossingAtEndpoint { .. })
        ),
        "{refusal}"
    );
}

// ---------------------------------------------------------------------------------------------
// 7. the claim discipline
// ---------------------------------------------------------------------------------------------

#[test]
fn an_interval_position_returns_no_embedding_rather_than_a_curve() {
    let mut boxes = positions(&SQUARE);
    boxes.insert(
        ConstraintVertexId(3),
        CoordinateBox3 {
            x: ExactInterval::point(integer(2)),
            y: ExactInterval::new(integer(2), integer(3)).expect("a forward interval"),
            z: ExactInterval::point(Rat::zero()),
        },
    );
    let refusal = embedding_of(&boxes).expect_err("a box with width is not a place");
    assert!(
        matches!(
            refusal,
            TopologicalError::NoEmbedding {
                occurrence: ConstraintVertexId(3),
                axis: 1
            }
        ),
        "{refusal}"
    );
    // The filtration still stands over the same positions: persistence needs only comparisons.
    assert!(
        ApertureFiltration::found(
            "widened",
            EventId(1),
            &boxes,
            &one_component(&SQUARE),
            integer(16),
            2,
            256,
        )
        .is_ok()
    );
}

#[test]
fn a_structure_with_no_closing_contact_returns_no_cycle() {
    // A straight chain: no contact closes anything at any aperture below the ceiling.
    let places = [
        (1, [0, 0, 0]),
        (2, [3, 0, 0]),
        (3, [6, 0, 0]),
        (4, [9, 0, 0]),
    ];
    let filtration = ApertureFiltration::found(
        "straight-chain",
        EventId(1),
        &positions(&places),
        &one_component(&places),
        integer(100),
        1,
        256,
    )
    .expect("stands");
    let configuration = embedding_of(&positions(&places)).expect("every place is a point");
    let refusal = contact_loops(&filtration, &configuration, &integer(9), 3)
        .expect_err("a straight chain closes no loop at the bond aperture");
    assert!(
        matches!(refusal, TopologicalError::NoCycle { .. }),
        "{refusal}"
    );
}

#[test]
fn a_backbone_closed_by_a_contact_is_a_loop_and_two_loops_carry_an_entanglement() {
    // A hexagonal ring: occurrence one and occurrence six are a contact apart, so the chain closes.
    let places = [
        (1, [2, 0, 0]),
        (2, [1, 2, 0]),
        (3, [-1, 2, 0]),
        (4, [-2, 0, 0]),
        (5, [-1, -2, 0]),
        (6, [1, -2, 0]),
    ];
    let filtration = ApertureFiltration::found(
        "hexagon",
        EventId(1),
        &positions(&places),
        &one_component(&places),
        integer(16),
        1,
        256,
    )
    .expect("stands");
    let configuration = embedding_of(&positions(&places)).expect("points");
    let loops = contact_loops(&filtration, &configuration, &integer(5), 5)
        .expect("the ring closes at squared aperture five");
    assert_eq!(loops.len(), 1);
    assert_eq!(loops[0].occurrences.len(), 6);
    assert_eq!(loops[0].closing_squared, ExactInterval::point(integer(5)));

    // A second ring, threaded through the first, gives a real entanglement reading.
    let threaded = ClosedPolygon::declared(
        "threaded",
        vec![
            place(4, 0, 0),
            place(2, 0, 2),
            place(0, 0, 0),
            place(2, 0, -2),
        ],
    )
    .expect("stands");
    let across = linking_under_directions(&loops[0].polygon, &threaded, &candidate_directions())
        .expect("some candidate is admissible");
    assert!(across.agree());
    assert_eq!(
        across.value().expect("a value").abs(),
        1,
        "the second ring threads the backbone loop exactly once"
    );
}

#[test]
fn the_knot_like_gate_refuses_where_no_structure_stands() {
    let places = [
        (1, [0, 0, 0]),
        (2, [3, 0, 0]),
        (3, [6, 0, 0]),
        (4, [9, 0, 0]),
    ];
    let filtration = ApertureFiltration::found(
        "straight-chain",
        EventId(1),
        &positions(&places),
        &one_component(&places),
        integer(100),
        2,
        1024,
    )
    .expect("stands");
    let (_, reading) = rational_reading(&filtration);
    let refusal = knot_like_reading(&filtration, &reading, 4, &[], &candidate_directions())
        .expect_err("no loop, so no knot-like claim");
    assert!(
        matches!(refusal, TopologicalError::NoCycle { .. }),
        "{refusal}"
    );
}

// ---------------------------------------------------------------------------------------------
// 8. hostile declarations
// ---------------------------------------------------------------------------------------------

#[test]
fn a_filtration_past_its_declared_bound_refuses_rather_than_exponentiating() {
    let places = (0..12)
        .map(|at: i64| (at as u64 + 1, [at, (at * at) % 5, 0]))
        .collect::<Vec<_>>();
    // Twelve occurrences, sixty-six candidate pairs: the pairwise pass fits a bound of two
    // hundred, so the construction runs and the bound is passed inside the coface expansion —
    // the two hundred and first cell is refused as it is founded.
    let refusal = ApertureFiltration::found(
        "wide",
        EventId(1),
        &positions(&places),
        &one_component(&places),
        integer(10_000),
        3,
        200,
    )
    .expect_err("a bound of two hundred cells is passed inside the expansion");
    assert!(
        matches!(
            refusal,
            TopologicalError::FiltrationTooWide {
                founded: 201,
                bound: 200
            }
        ),
        "{refusal}"
    );
}

/// **The pairwise pass is itself work sized by the declaration, and is refused before it runs.**
///
/// Three thousand occurrences present 4,498,500 candidate 1-cells. Under the subset enumeration
/// this construction used to run, the whole pairwise pass ran first and `combinations(3000, 2)`
/// then materialized every one of those pairs as its own `Vec<usize>` before a single cell was
/// founded — and `combinations(3000, 3)` after it, which is 4.5 × 10⁹ vectors and does not
/// return. The admission rule refuses the declaration instead: the candidate pair count is formed
/// with checked arithmetic and compared against the declared bound before anything is read.
#[test]
fn a_population_whose_pairwise_pass_exceeds_the_declared_bound_is_refused_before_it_runs() {
    let places = (0..3_000_i64)
        .map(|at| (at as u64 + 1, [at % 50, at / 50, 0]))
        .collect::<Vec<_>>();
    let boxes = positions(&places);
    let components = one_component(&places);
    let started = Instant::now();
    let refusal = ApertureFiltration::found(
        "wide-population",
        EventId(1),
        &boxes,
        &components,
        integer(10_000),
        3,
        4_000,
    )
    .expect_err("the pairwise pass of three thousand occurrences is not four thousand cells");
    assert!(
        matches!(
            refusal,
            TopologicalError::PairPopulationTooWide {
                occurrences: 3_000,
                candidates: 4_498_500,
                bound: 4_000
            }
        ),
        "{refusal}"
    );

    // And a population that cannot even be founded as vertices is refused before the pass too.
    let refusal = ApertureFiltration::found(
        "wide-vertices",
        EventId(1),
        &boxes,
        &components,
        integer(10_000),
        3,
        100,
    )
    .expect_err("three thousand occurrences are three thousand grade-zero cells");
    assert!(
        matches!(
            refusal,
            TopologicalError::FiltrationTooWide {
                founded: 3_000,
                bound: 100
            }
        ),
        "{refusal}"
    );
    let elapsed = started.elapsed();
    assert!(
        elapsed.as_secs() < 30,
        "both refusals are decided from the declared counts, so they are immediate; this took {} \
         seconds, which means the construction is doing work the declaration did not admit",
        elapsed.as_secs()
    );
}

/// **The declared cell bound refuses inside the coface expansion, with nothing materialized.**
///
/// Two hundred occurrences: a twenty-eight member clique and a hundred and seventy-two
/// occurrences too far away to be in contact with anything. The candidate pair population is
/// 19,900, which the declared bound admits. The founded population is 200 vertices, 378 edges,
/// 3,276 triangles and 20,475 tetrahedra, so the bound is passed partway through grade three.
///
/// Under the subset enumeration this construction used to run, reaching grade three meant first
/// materializing `combinations(200, 4)` — 64,684,950 index vectors, several gigabytes — **before**
/// founding a single grade-three cell, so the bound could not fire until after it. The clique
/// expansion founds cofaces one at a time out of the contact graph, so the refusal is immediate
/// and the sparse part of the population costs nothing at all.
#[test]
fn the_cell_bound_refuses_inside_the_coface_expansion_rather_than_after_a_list_is_built() {
    let mut places = (0..28_i64)
        .map(|at| (at as u64 + 1, [at, 0, 0]))
        .collect::<Vec<_>>();
    places.extend((0..172_i64).map(|at| (at as u64 + 29, [10_000 + 1_000 * at, 0, 0])));
    let started = Instant::now();
    let refusal = ApertureFiltration::found(
        "clique-and-dust",
        EventId(1),
        &positions(&places),
        &one_component(&places),
        integer(1_000),
        3,
        19_900,
    )
    .expect_err("the twenty-eight clique founds more cells than the declared bound");
    assert!(
        matches!(
            refusal,
            TopologicalError::FiltrationTooWide {
                founded: 19_901,
                bound: 19_900
            }
        ),
        "{refusal}"
    );
    let elapsed = started.elapsed();
    assert!(
        elapsed.as_secs() < 60,
        "the expansion refuses at the cell that passes the bound; this took {} seconds, which is \
         the signature of an enumeration materialized ahead of the check",
        elapsed.as_secs()
    );
}

/// The clique expansion founds exactly the Vietoris–Rips population the subset enumeration did.
///
/// A sparse contact graph is where the two constructions part in cost and must not part in
/// content: here five occurrences in a line where only neighbours are in contact, so the complex
/// is a path with no triangle at all, and separately the complete four-point case where every
/// subset is a simplex.
#[test]
fn the_clique_expansion_founds_the_same_population_the_subset_enumeration_did() {
    let line = (0..5_i64)
        .map(|at| (at as u64 + 1, [10 * at, 0, 0]))
        .collect::<Vec<_>>();
    let sparse = ApertureFiltration::found(
        "line",
        EventId(1),
        &positions(&line),
        &one_component(&line),
        integer(100),
        3,
        256,
    )
    .expect("the sparse filtration stands");
    let founded = sparse
        .cells_by_simplex
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    let expected = (0..5)
        .map(|at| vec![at])
        .chain((0..4).map(|at| vec![at, at + 1]))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        founded, expected,
        "only neighbours are within a squared aperture of a hundred, so the Rips complex is the \
         path and carries no triangle"
    );

    let dense = square_filtration(3);
    let all = (1..=4usize)
        .flat_map(|size| super::combinations(4, size))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        dense.cells_by_simplex.keys().cloned().collect::<BTreeSet<_>>(),
        all,
        "the square at a ceiling admitting its diagonal is the full three-simplex"
    );
    // And in the same order the subset enumeration founded in, so cell addresses — the tie-break
    // every declared order carries — are unmoved.
    let mut expected = all.into_iter().collect::<Vec<_>>();
    expected.sort_by(|left, right| left.len().cmp(&right.len()).then(left.cmp(right)));
    assert_eq!(dense.simplex_by_cell.values().cloned().collect::<Vec<_>>(), expected);
}

#[test]
fn a_reduction_past_its_declared_bound_refuses() {
    let filtration = square_filtration(3);
    let order = FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound).expect("admissible");
    let refusal = persistence(&filtration, &order, &Coefficients::Rational, 1)
        .expect_err("one column addition is not enough");
    assert!(
        matches!(refusal, TopologicalError::ReductionTooWide { bound: 1, .. }),
        "{refusal}"
    );
}

#[test]
fn an_empty_population_and_an_impossible_grade_are_refused_by_name() {
    assert!(matches!(
        ApertureFiltration::found(
            "empty",
            EventId(1),
            &BTreeMap::new(),
            &BTreeMap::new(),
            integer(1),
            1,
            16,
        )
        .expect_err("an empty population is not a filtration"),
        TopologicalError::EmptyPopulation
    ));
    assert!(matches!(
        ApertureFiltration::found(
            "too-tall",
            EventId(1),
            &positions(&SQUARE),
            &one_component(&SQUARE),
            integer(8),
            9,
            256,
        )
        .expect_err("grade nine is outside the founded range"),
        TopologicalError::TopGradeOutsideRange(9)
    ));
    assert!(matches!(
        ApertureFiltration::found(
            "negative",
            EventId(1),
            &positions(&SQUARE),
            &one_component(&SQUARE),
            integer(-1),
            1,
            256,
        )
        .expect_err("a negative squared aperture is not an aperture"),
        TopologicalError::NegativeCeiling
    ));
}

// ---------------------------------------------------------------------------------------------
// the measured M5 structures
// ---------------------------------------------------------------------------------------------

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The RBX1 chain is the one component present in all three presentations.
const RBX1_RESIDUES: usize = 108;
/// The residue window the topological receiver is measured on, declared rather than inferred.
const WINDOW: usize = 20;
/// Eight angstroms, squared: the contact aperture the constraint receivers already use.
const CONTACT_SQUARED: i64 = 64;

/// **The founding as the subset enumeration did it**, kept as the reference the clique expansion
/// is held to on the measured material.
///
/// Every `C(n, k)` subset of the population, lexicographically, kept when every one of its edges
/// is within the declared ceiling. This is the construction [`ApertureFiltration::found`] replaced
/// — it was `C(n, k)` index vectors materialized before any refusal could fire — and the two must
/// found exactly the same simplices with exactly the same entry values.
fn rips_by_subset_enumeration(
    positions: &BTreeMap<ConstraintVertexId, CoordinateBox3>,
    ceiling: &Rat,
    top_grade: usize,
) -> BTreeMap<Vec<usize>, ExactInterval> {
    let places = positions.values().cloned().collect::<Vec<_>>();
    let count = places.len();
    let mut pair_value: BTreeMap<(usize, usize), ExactInterval> = BTreeMap::new();
    for left in 0..count {
        for right in (left + 1)..count {
            let value = places[left].squared_distance(&places[right]);
            if value.lower > *ceiling {
                continue;
            }
            pair_value.insert((left, right), value);
        }
    }
    let mut founded = BTreeMap::new();
    for at in 0..count {
        founded.insert(vec![at], ExactInterval::point(integer(0)));
    }
    for grade in 1..=top_grade {
        for simplex in super::combinations(count, grade + 1) {
            let Some(value) = super::simplex_entry_value(&simplex, &pair_value) else {
                continue;
            };
            if value.lower > *ceiling {
                continue;
            }
            founded.insert(simplex, value);
        }
    }
    founded
}

/// The founded simplices in cell-address order, which is the order they were founded in and the
/// tie-break every declared filtration order carries.
fn founding_order(filtration: &ApertureFiltration) -> Vec<Vec<usize>> {
    filtration.simplex_by_cell.values().cloned().collect()
}

/// The order the subset enumeration founded in: grade by grade, lexicographically inside a grade.
fn subset_founding_order(reference: &BTreeMap<Vec<usize>, ExactInterval>) -> Vec<Vec<usize>> {
    let mut ordered = reference.keys().cloned().collect::<Vec<_>>();
    ordered.sort_by(|left, right| left.len().cmp(&right.len()).then(left.cmp(right)));
    ordered
}

/// The founded simplices of a filtration with the entry value each carries.
fn founded_with_values(filtration: &ApertureFiltration) -> BTreeMap<Vec<usize>, ExactInterval> {
    filtration
        .cells_by_simplex
        .iter()
        .map(|(simplex, cell)| {
            (
                simplex.clone(),
                filtration.value_of(*cell).expect("a founded value").clone(),
            )
        })
        .collect()
}

struct MeasuredStructure {
    centres: BTreeMap<ConstraintVertexId, CoordinateBox3>,
    enclosures: BTreeMap<ConstraintVertexId, CoordinateBox3>,
    components: BTreeMap<ConstraintVertexId, ConstraintComponentId>,
}

fn read_window(path: &Path) -> Result<MeasuredStructure, String> {
    let presentation =
        StructurePresentation::read(path).map_err(|refusal| refusal.to_string())?;
    let chains = presentation
        .chains
        .iter()
        .filter(|chain| chain.residues.len() == RBX1_RESIDUES)
        .collect::<Vec<_>>();
    if chains.len() != 1 {
        return Err(format!(
            "{} carries {} chains of {RBX1_RESIDUES} residues, not one",
            path.display(),
            chains.len()
        ));
    }
    let mut centres = BTreeMap::new();
    let mut enclosures = BTreeMap::new();
    let mut components = BTreeMap::new();
    for (at, residue) in chains[0].residues.iter().take(WINDOW).enumerate() {
        let alpha = residue
            .labelled_atom("CA")
            .map_err(|refusal| refusal.to_string())?
            .ok_or_else(|| format!("residue {} carries no CA", residue.source_ordinal))?;
        let atom = &residue.atoms[alpha];
        let id = ConstraintVertexId(at as u64 + 1);
        centres.insert(
            id,
            CoordinateBox3::point(
                atom.x.exact_centre().map_err(|e| e.to_string())?,
                atom.y.exact_centre().map_err(|e| e.to_string())?,
                atom.z.exact_centre().map_err(|e| e.to_string())?,
            ),
        );
        enclosures.insert(id, atom.source_box().map_err(|e| e.to_string())?);
        components.insert(id, ConstraintComponentId(1));
    }
    if centres.len() != WINDOW {
        return Err(format!(
            "{} supplied {} alpha carbons for a window of {WINDOW}",
            path.display(),
            centres.len()
        ));
    }
    Ok(MeasuredStructure {
        centres,
        enclosures,
        components,
    })
}

/// **The measured return on the authenticated M5 release.**
///
/// Absent the release this test refuses. Every law this module owns is checked above on synthetic
/// exact material, so nothing here is the only check of anything.
#[test]
fn the_topological_receiver_measures_the_m5_structures() {
    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured topological reading \
         cannot be taken, and this test refuses to report success without taking it. Place the \
         authenticated release at that path, or set {STRUCTURE_ROOT_ENV} to the directory \
         carrying designed-free-rbx1.cif, ptxv2-free-rbx1-seed2.cif and \
         ptxv2-cul1-rbx1-seed0.cif.",
        root.display()
    );

    let files = [
        ("designed-free", "designed-free-rbx1.cif"),
        ("protenix-free-seed2", "ptxv2-free-rbx1-seed2.cif"),
        ("protenix-cul1-seed0", "ptxv2-cul1-rbx1-seed0.cif"),
    ];
    let ceiling = integer(CONTACT_SQUARED);
    for (lineage, file) in files {
        let measured =
            read_window(&root.join(file)).unwrap_or_else(|error| panic!("{lineage}: {error}"));

        // (a) The enclosure filtration: the deposited coordinates are last-place intervals, so the
        // order carries `Open` comparisons and the reading is a family.
        let enclosed = ApertureFiltration::found(
            format!("{lineage}/enclosure"),
            EventId(1),
            &measured.enclosures,
            &measured.components,
            ceiling.clone(),
            2,
            4096,
        )
        .expect("the enclosure filtration stands");
        let reference = rips_by_subset_enumeration(&measured.enclosures, &ceiling, 2);
        assert_eq!(
            founded_with_values(&enclosed),
            reference,
            "{lineage}/enclosure: the clique expansion founds exactly what the subset enumeration \
             founded, with exactly the same entry intervals"
        );
        assert_eq!(
            founding_order(&enclosed),
            subset_founding_order(&reference),
            "{lineage}/enclosure: and in the same order, so every cell carries the same address \
             and every order tie-break below decides the same way"
        );
        assert!(
            !enclosed.order_is_determinate(),
            "a deposited decimal is an enclosure, not a place, so its filtration order is not \
             determinate"
        );
        let open_pairs = open_order_pairs(&enclosed).len();
        let lower_order =
            FiltrationOrder::found(&enclosed, &OrderLaw::ByLowerBound).expect("admissible");
        let upper_order =
            FiltrationOrder::found(&enclosed, &OrderLaw::ByUpperBound).expect("admissible");
        let lower_reading =
            persistence(&enclosed, &lower_order, &Coefficients::Rational, 20_000_000)
                .expect("the lower bound of the family reduces");
        let upper_reading =
            persistence(&enclosed, &upper_order, &Coefficients::Rational, 20_000_000)
                .expect("the upper bound of the family reduces");
        let family_separates = lower_reading.pairs != upper_reading.pairs;

        // (b) The centre filtration: the declared deposited centres, a named representative of the
        // enclosure. The order is determinate and every reading below is on it.
        // Top grade three, so a grade-two class is a **cavity** of the Rips complex and not merely
        // a two-cycle of a two-skeleton that no three-cell was ever founded to fill.
        let filtration = ApertureFiltration::found(
            lineage,
            EventId(1),
            &measured.centres,
            &measured.components,
            ceiling.clone(),
            3,
            8192,
        )
        .expect("the centre filtration stands");
        assert!(filtration.order_is_determinate());
        let reference = rips_by_subset_enumeration(&measured.centres, &ceiling, 3);
        assert_eq!(
            founded_with_values(&filtration),
            reference,
            "{lineage}: the clique expansion founds exactly what the subset enumeration founded, \
             at every grade up to three, so every measured reading below is unchanged"
        );
        assert_eq!(
            founding_order(&filtration),
            subset_founding_order(&reference),
            "{lineage}: and in the same order, so every cell address and every order tie-break is \
             what it was"
        );
        let order = FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound)
            .expect("the by-lower-bound order is admissible");
        let rational = persistence(&filtration, &order, &Coefficients::Rational, 20_000_000)
            .expect("the rational reduction returns");
        let field_two = persistence(
            &filtration,
            &order,
            &Coefficients::PrimeField(BigUint::from(2_u8)),
            20_000_000,
        )
        .expect("the field-two reduction returns");
        let whole = filtration.cell_count();

        // The two computations of the grade-zero reading, held to agreement by the library.
        let agreement = grade_zero_agreement(&filtration, &order, &rational)
            .expect("the matrix reduction and the union-find agree on the measured structure");
        let communities = &agreement.communities;
        assert_eq!(rational.betti_at(0, whole), 1, "one chain, one community");

        // The integral profile beside the field reading.
        let profile = integral_profile(
            &filtration,
            &[integer(16), integer(36), ceiling.clone()],
            PivotRule::FirstNonzero,
        )
        .expect("the integral profile returns");
        let primes = profile.field_dependence_primes();
        for step in &profile.steps {
            assert_eq!(
                step.refusing.euler_characteristic(),
                step.refusing.cell_euler_characteristic()
            );
        }
        for grade in 0..=2u32 {
            let cut = order
                .order
                .iter()
                .take_while(|cell| {
                    filtration.value_of(**cell).expect("a value").upper <= ceiling
                })
                .count();
            let integral = profile
                .steps
                .last()
                .expect("a top step")
                .refusing
                .betti_vector();
            let expected = integral.get(grade as usize).copied().unwrap_or(0);
            assert_eq!(
                rational.betti_at(grade, cut),
                expected,
                "{lineage}: the rational reduction and the integer Smith normal form disagree at \
                 grade {grade}"
            );
        }

        // The loops the backbone actually carries, and the entanglement between them.
        let configuration = embedding_of(&measured.centres).expect("the centres are places");
        assert!(
            matches!(
                embedding_of(&measured.enclosures),
                Err(TopologicalError::NoEmbedding { .. })
            ),
            "the deposited enclosure admits no curve and the receiver says so rather than \
             choosing a representative silently"
        );
        let loops = contact_loops(&filtration, &configuration, &ceiling, 4);
        let (loop_count, entangled, longest_loop) = match &loops {
            Ok(found) => {
                let mut entangled = 0usize;
                let mut disjoint = 0usize;
                for (at, left) in found.iter().enumerate() {
                    for right in found.iter().skip(at + 1) {
                        if left.shares_occurrence(right) {
                            continue;
                        }
                        disjoint += 1;
                        if let Ok(reading) =
                            loop_entanglement(left, right, &candidate_directions())
                            && reading.threaded
                        {
                            entangled += 1;
                        }
                    }
                }
                let longest = found
                    .iter()
                    .map(|one| one.occurrences.len())
                    .max()
                    .unwrap_or(0);
                assert!(entangled <= disjoint);
                (found.len(), entangled, longest)
            }
            Err(TopologicalError::NoCycle { .. }) => (0, 0, 0),
            Err(other) => panic!("{lineage}: {other}"),
        };

        let bars = |grade: u32| -> String {
            let mut live = rational
                .pairs_at_grade(grade)
                .into_iter()
                .filter(|pair| !pair.is_exactly_trivial())
                .map(|pair| {
                    let death = pair
                        .death_value
                        .as_ref()
                        .map(|value| value.lower.to_string())
                        .unwrap_or_else(|| "essential".to_owned());
                    (
                        pair.death_value
                            .as_ref()
                            .map(|value| &value.lower - &pair.birth_value.lower)
                            .unwrap_or_else(|| &ceiling - &pair.birth_value.lower),
                        format!("[{},{death})", pair.birth_value.lower),
                    )
                })
                .collect::<Vec<_>>();
            live.sort_by(|left, right| right.0.cmp(&left.0));
            live.into_iter()
                .map(|(_, bar)| bar)
                .collect::<Vec<_>>()
                .join(" ")
        };

        println!(
            "topological_receiver M5 | {lineage} | cells {} (v {} e {} f {} t {}) | open-order \
             pairs {open_pairs} | family separates {family_separates} | column ops Q {} F2 {} | \
             beta_Q {:?} | beta_F2 {:?} | H1 bars {} | H2 bars {} | torsion primes {:?} | \
             communities merging {} | loops {loop_count} (longest {longest_loop}) | entangled \
             pairs {entangled}",
            whole,
            filtration.complex.f_vector().get(&0).copied().unwrap_or(0),
            filtration.complex.f_vector().get(&1).copied().unwrap_or(0),
            filtration.complex.f_vector().get(&2).copied().unwrap_or(0),
            filtration.complex.f_vector().get(&3).copied().unwrap_or(0),
            rational.column_operations,
            field_two.column_operations,
            [
                rational.betti_at(0, whole),
                rational.betti_at(1, whole),
                rational.betti_at(2, whole)
            ],
            [
                field_two.betti_at(0, whole),
                field_two.betti_at(1, whole),
                field_two.betti_at(2, whole)
            ],
            bars(1),
            bars(2),
            primes,
            communities.merge_values.len(),
        );
    }
}

/// A remounted [`ApertureFiltration`] is re-checked: `Deserialize` routes through `TryFrom`, so a
/// forged schema, a simplex label outside the occurrence population, or derived fields that are
/// not the ones the declaration produces are refused rather than carried. Without the gate a
/// forged simplex label reached [`contact_loops`], which indexed a map with it and panicked.
#[test]
fn a_remounted_filtration_is_rechecked_and_contact_loops_never_indexes_unchecked() {
    let filtration = square_filtration(2);
    let wire = ron::to_string(&filtration).expect("serializes");
    let remounted: ApertureFiltration = ron::from_str(&wire).expect("a coherent filtration remounts");
    assert_eq!(remounted, filtration);

    let forged = wire.replace(APERTURE_FILTRATION_SCHEMA, "holonic-engine.not-this.v1");
    assert!(
        ron::from_str::<ApertureFiltration>(&forged).is_err(),
        "a foreign schema is refused"
    );

    // A simplex naming an occurrence position outside the population. `found_declared` refuses it,
    // and the wire route now runs `found_declared`.
    let mut declared = DeclaredFiltration {
        lineage: filtration.lineage.clone(),
        source_event: filtration.source_event,
        complex: filtration.complex.clone(),
        occurrences: filtration.occurrences.clone(),
        component_of: filtration.component_of.clone(),
        cells_by_simplex: filtration.cells_by_simplex.clone(),
        entry: filtration.entry.clone(),
        ceiling: filtration.ceiling.clone(),
    };
    let (simplex, cell) = declared
        .cells_by_simplex
        .iter()
        .find(|(simplex, _)| simplex.len() == 2)
        .map(|(simplex, cell)| (simplex.clone(), *cell))
        .expect("a 1-cell stands");
    declared.cells_by_simplex.remove(&simplex);
    declared.cells_by_simplex.insert(vec![0, 9_999], cell);
    assert!(matches!(
        ApertureFiltration::found_declared(declared).expect_err("refused"),
        TopologicalError::SimplexLabelDisagrees(_)
    ));

    // And `contact_loops` itself no longer indexes: on a filtration whose occurrences carry no
    // declared component the lookup still succeeds, and on any filtration it returns a typed
    // refusal rather than panicking.
    let configuration = ExactConfiguration::declared(
        3,
        SQUARE.iter().map(|(at, place)| {
            (
                ConstraintVertexId(*at),
                place.iter().copied().map(integer).collect::<Vec<_>>(),
            )
        }),
    )
    .expect("a three-dimensional configuration");
    let reading = contact_loops(&filtration, &configuration, &integer(4), 2);
    assert!(
        reading.is_ok() || matches!(reading, Err(TopologicalError::NoCycle { .. })),
        "a loop reading returns or refuses by name, never panics: {reading:?}"
    );
}
