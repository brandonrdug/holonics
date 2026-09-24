use super::*;
use holonics_cuda::section_layout::{ScatterReceipt, ScatterRequest, SectionLayout};

/// The engine's own scatter material, small enough to read by eye: four source rows of six real
/// coordinates (three complex), the window `[2, 6)`, scattered onto five destination rows.
const WIDTH: usize = 6;
const START: usize = 2;
const COUNT: usize = 4;
const DESTINATIONS: [usize; 4] = [3, 0, 4, 1];
const OUTPUT_ROWS: usize = 5;
/// Exactly the numerators `section_scatters_the_window_the_generated_triple_reproduces` mounts.
/// Every value is non-negative, which is the stated scope of the cross-check: the generated ring
/// represents a word exactly while it is in `[0, 2^61 - 1)`.
const SOURCE: [i64; 24] = [
    7, 1, 5, 9, 2, 4, //
    3, 3, 11, 6, 8, 1, //
    2, 10, 4, 7, 5, 5, //
    6, 13, 9, 2, 1, 12, //
];
/// A denominator that is not a power of two, so every enclosure carries a positive radius and the
/// radius seam below is observable rather than vacuous.
const DENOMINATOR: i64 = 3;

fn declaration() -> SectionLayout {
    let incidence =
        enclosure_scatter_incidence(WIDTH, START, COUNT, &DESTINATIONS, OUTPUT_ROWS).expect("lawful");
    SectionLayout::generate(incidence, ScatterRequest::Injective).expect("injective")
}

#[test]
fn the_engine_scatter_is_an_injective_incidence_with_a_placement_block() {
    let layout = declaration();
    assert_eq!(layout.regions(), DESTINATIONS.len());
    assert_eq!(layout.slots(), DESTINATIONS.len() * 2 * COUNT);
    // The common field is the flat source section followed by the flat destination field; no
    // address is reserved for the enclosure radius, which is the seam this module documents.
    assert_eq!(
        layout.global_extent(),
        DESTINATIONS.len() * WIDTH + OUTPUT_ROWS * COUNT
    );
    assert_eq!(layout.receipt(), ScatterReceipt::Injective);
    let operator = window_placement_operator(COUNT, 4 * COUNT * COUNT).expect("canonical");
    assert_eq!(operator.width(), layout.tile().max_width());
    assert_eq!(operator.width(), 2 * COUNT);
    // One coefficient per placed coordinate and no others: the block is a permutation, so nothing
    // but `x * 1 + 0` reaches a gathered word and the ring cannot change one.
    assert_eq!(operator.entries().iter().filter(|v| **v != 0).count(), COUNT);
    // The block is built from the declared window, so it takes the caller's ceiling and refuses
    // past it before it reserves anything.
    assert!(window_placement_operator(COUNT, 4 * COUNT * COUNT - 1).is_err());
}

#[test]
fn the_declaration_refuses_the_duplicate_destination_the_kernel_refuses_at_run_time() {
    let refusal = enclosure_scatter_incidence(WIDTH, START, COUNT, &[2, 0, 2], OUTPUT_ROWS)
        .expect_err("a repeated destination is not injective");
    assert!(
        refusal.to_string().contains("repeat destination 2"),
        "{refusal}"
    );
    // The window clause is the kernel's `start + count > source_width` refusal, at construction.
    assert!(enclosure_scatter_incidence(WIDTH, 4, COUNT, &DESTINATIONS, OUTPUT_ROWS).is_err());
    assert!(enclosure_scatter_incidence(WIDTH, START, 3, &DESTINATIONS, OUTPUT_ROWS).is_err());
    assert!(enclosure_scatter_incidence(WIDTH, START, COUNT, &DESTINATIONS, 3).is_err());
}

/// The generated triple's own exact reference places each source window at its declared
/// destination and leaves everything else zero — the hand-written kernel's coordinate result,
/// computed here without any device.
#[test]
fn the_generated_reference_places_each_window_at_its_destination() {
    let layout = declaration();
    let operator = window_placement_operator(COUNT, 4 * COUNT * COUNT).expect("canonical");
    let ring = ModularWords::MERSENNE61;
    let source_words = DESTINATIONS.len() * WIDTH;
    let mut field = vec![0u64; layout.global_extent()];
    for (at, slot) in field.iter_mut().enumerate().take(source_words) {
        *slot = (at as u64 + 1) * 1_000;
    }
    let produced = layout
        .apply_reference(&ring, &operator, &field)
        .expect("the placement is exact");
    let mut expected = vec![0u64; layout.global_extent()];
    for (row, destination) in DESTINATIONS.iter().enumerate() {
        for j in 0..COUNT {
            expected[source_words + destination * COUNT + j] = field[row * WIDTH + START + j];
        }
    }
    assert_eq!(produced, expected);
}




// ---------------------------------------------------------------------------------------------
// Issue #50: the two obstacles, exhibited rather than asserted
// ---------------------------------------------------------------------------------------------

/// **`SharedLocalOperator`, exhibited.** Two bar faces on one joint chart, with different
/// directions and therefore different local blocks. `SectionLayout::assemble_dense` assembles
/// `Σ_r P_rᵀ L P_r` with one shared `L`, and the test shows that **neither** face's own block,
/// used as that shared `L`, produces the true `Σ_f L_f` — which is what `SharedLocalOperator`
/// says and is why the sparse contact assembly cannot be placed through this boundary as it
/// stands.
///
/// The ring is `Z/(2^61 - 1)`, the one `SectionKernels` realizes; the two blocks are built from
/// small nonnegative integers, so every coefficient is its own canonical residue and the
/// comparison is a comparison of integers rather than of folds.
#[test]
fn the_shared_local_operator_cannot_carry_two_faces_with_different_blocks() {
    use holonics::ratio::ring::{AccumulationLaw, CheckedIntegers, ExactRing};
    use holonics_cuda::section_layout::{
        IncidenceDeclaration, LocalOperator, ScatterRequest, SectionLayout,
    };

    // A joint chart of three coordinates; face 0 reaches coordinates {0, 1}, face 1 reaches
    // {1, 2}. One region per face, each two slots wide.
    const EXTENT: usize = 3;
    const WIDTH: usize = 2;
    let incidence = IncidenceDeclaration::uniform(EXTENT, WIDTH, vec![0, 1, 1, 2])
        .expect("a lawful two-region incidence");
    let layout = SectionLayout::generate(
        incidence,
        ScatterRequest::Accumulated(AccumulationLaw::IntegerAdd),
    )
    .expect("the layout generates");
    let ring = CheckedIntegers;

    // `L_0 = J_0ᵀ J_0` for the slip covector `J_0 = (1, -1)` on its support, and `L_1` for
    // `J_1 = (2, 3)` on its own. They are different tables, which is the whole point.
    let block_zero = LocalOperator::dense(WIDTH, vec![1, -1, -1, 1]).expect("a 2x2 block");
    let block_one = LocalOperator::dense(WIDTH, vec![4, 6, 6, 9]).expect("a 2x2 block");

    // The true assembly `Σ_f P_fᵀ L_f P_f`, written out by hand at the three joint coordinates.
    //   face 0 at {0,1}: [[1,-1],[-1,1]]      face 1 at {1,2}: [[4,6],[6,9]]
    let truth: Vec<i64> = vec![
        1, -1, 0, //
        -1, 1 + 4, 6, //
        0, 6, 9,
    ];

    let with_zero = layout
        .assemble_dense(&ring, &block_zero, EXTENT * EXTENT)
        .expect("the shared assembly returns");
    let with_one = layout
        .assemble_dense(&ring, &block_one, EXTENT * EXTENT)
        .expect("the shared assembly returns");
    assert_ne!(
        with_zero, truth,
        "one shared operator taken from face 0 does not assemble the two-face form"
    );
    assert_ne!(
        with_one, truth,
        "and neither does one taken from face 1"
    );

    // And the obstacle is *only* the sharing: with one region the generated assembly is exact.
    let single = IncidenceDeclaration::uniform(EXTENT, WIDTH, vec![0, 1])
        .expect("a lawful one-region incidence");
    let single = SectionLayout::generate(single, ScatterRequest::Injective).expect("the layout generates");
    assert_eq!(
        single
            .assemble_dense(&ring, &block_zero, EXTENT * EXTENT)
            .expect("assembled"),
        vec![1, -1, 0, -1, 1, 0, 0, 0, 0],
        "one face is an instance of the generated assembly identity exactly"
    );
    let _ = ring.law();

    let (operation, clause) = GeneratedTileObstacle::SharedLocalOperator.declared();
    assert!(operation.contains("ContactDissipation::assemble"));
    assert!(clause.contains("shared by every region"));
}

/// **`PivotSweepIsBilinear`, stated against the signature that makes it true.**
///
/// The claim is about a *type*, not about a value: `apply_local_reference` takes the operator by
/// reference before the call and the tile by mutable reference, so the coefficient the apply
/// multiplies by cannot depend on the field. The test below holds that shape: applying any fixed
/// local operator to a gathered tile is linear in the tile, so it maps zero to zero and respects
/// addition — and a pivot update does neither, because `a_ij − a_ik · a_kj` is quadratic in the
/// field it reads.
#[test]
fn a_fixed_local_apply_is_linear_in_the_field_and_a_pivot_update_is_not() {
    use holonics::ratio::ring::{AccumulationLaw, CheckedIntegers};
    use holonics_cuda::section_layout::{
        IncidenceDeclaration, LocalOperator, ScatterRequest, SectionLayout,
    };

    const EXTENT: usize = 4;
    const WIDTH: usize = 2;
    let incidence = IncidenceDeclaration::uniform(EXTENT, WIDTH, vec![0, 1, 2, 3])
        .expect("a lawful incidence");
    let layout = SectionLayout::generate(
        incidence,
        ScatterRequest::Accumulated(AccumulationLaw::IntegerAdd),
    )
    .expect("the layout generates");
    let ring = CheckedIntegers;
    let operator = LocalOperator::dense(WIDTH, vec![1, -1, 0, 1]).expect("a 2x2 block");

    let left: Vec<i64> = vec![3, 5, 7, 11];
    let right: Vec<i64> = vec![-2, 4, 1, 0];
    let sum: Vec<i64> = left.iter().zip(&right).map(|(a, b)| a + b).collect();

    let apply = |x: &[i64]| {
        layout
            .apply_reference(&ring, &operator, x)
            .expect("the reference apply returns")
    };
    let zeros = vec![0i64; EXTENT];
    assert_eq!(apply(&zeros), zeros, "a fixed local apply maps zero to zero");
    let additive: Vec<i64> = apply(&left)
        .iter()
        .zip(apply(&right))
        .map(|(a, b)| a + b)
        .collect();
    assert_eq!(apply(&sum), additive, "and it respects addition: it is linear");

    // The pivot update the modular elimination performs, on the same field: `x_1 -= x_0 * x_1`
    // is the shape of `a_ij -= m_i * a_kj`, and it is neither of the two.
    let pivot = |x: &[i64]| -> Vec<i64> {
        let mut out = x.to_vec();
        out[1] -= x[0] * x[1];
        out
    };
    assert_eq!(pivot(&zeros), zeros);
    let pivot_additive: Vec<i64> = pivot(&left)
        .iter()
        .zip(pivot(&right))
        .map(|(a, b)| a + b)
        .collect();
    assert_ne!(
        pivot(&sum),
        pivot_additive,
        "the pivot update is bilinear in the field it reads, so no fixed local operator is it"
    );

    let (operation, clause) = GeneratedTileObstacle::PivotSweepIsBilinear.declared();
    assert!(operation.contains("PrimeImage::reduce"));
    assert!(clause.contains("linear in one gathered operand"));
}
