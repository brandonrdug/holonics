//! Tests for [`crate::receiver_atlas`]. Every test names the Lean declaration of
//! `Foundation/ReceiverAtlas.lean` it mirrors, and none depends on an exterior fixture.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::Zero;

use super::*;
use crate::grain_tower::{Grain, GrainAddress, GrainFace, GrainPair, GrainSelection};
use crate::physical_constraint_complex::{ConstraintEdge, ConstraintVertexId, ContactClass};
use crate::physical_constraint_grading::EdgeProvenance;
use crate::rigidity_receiver::{rigidity_reading, ExactConfiguration, RigidityJacobian};
use relational_geometry::Rat;

// -------------------------------------------------------------------------------------------
// Capability: supplied, never conferred
// -------------------------------------------------------------------------------------------

fn weights(a: i64, b: i64) -> (BigInt, BigInt) {
    (BigInt::from(a), BigInt::from(b))
}

fn point(a: i64, b: i64) -> (BigInt, BigInt) {
    (BigInt::from(a), BigInt::from(b))
}

/// Lean: `operation_is_supplied_not_conferred`. One carrier, one capability, two admissible
/// parameters, two different operations — so no function of the carrier produced either.
#[test]
fn supplied_metric_is_not_conferred_by_the_carrier() {
    let isotropic = SuppliedCapability::supply(WeightedSquareMetric, weights(1, 1))
        .expect("(1,1) is admissible and the identity holds");
    let anisotropic = SuppliedCapability::supply(WeightedSquareMetric, weights(1, 2))
        .expect("(1,2) is admissible and the identity holds");

    let left = point(0, 0);
    let right = point(0, 1);
    assert_eq!(isotropic.operation(&left, &right), BigInt::from(1));
    assert_eq!(anisotropic.operation(&left, &right), BigInt::from(2));
    assert_ne!(
        isotropic.operation(&left, &right),
        anisotropic.operation(&left, &right),
        "two admissible parameters over one carrier must give two different operations"
    );
    assert_eq!(isotropic.kind(), CapabilityKind::Metric);
}

/// Lean: the `admitted` field of `Constituted`. A weight the capability does not admit is refused
/// by name; it is not clamped, defaulted or accepted with a warning.
#[test]
fn capability_refuses_parameters_it_does_not_admit() {
    for bad in [weights(0, 1), weights(1, 0), weights(-3, 2)] {
        let refusal = SuppliedCapability::supply(WeightedSquareMetric, bad.clone())
            .expect_err("a non-positive weight is not an admissible metric parameter");
        assert_eq!(
            refusal,
            CapabilityRefusal::ParametersNotAdmitted {
                parameter: bad,
                kind: CapabilityKind::Metric,
            }
        );
    }
}

/// The identity a metric owes is checked, not assumed: `laws_hold` is asked on every supply.
#[test]
fn capability_checks_its_own_identity() {
    let supplied = SuppliedCapability::supply(WeightedSquareMetric, weights(5, 7))
        .expect("positive weights are admissible");
    let p = point(11, -4);
    assert!(
        supplied.operation(&p, &p).is_zero(),
        "a point is at distance zero from itself"
    );
}

// -------------------------------------------------------------------------------------------
// LocalChart
// -------------------------------------------------------------------------------------------

/// Lean: `reading_none_of_metric_none`. Asking a capability-less chart for a reading returns
/// `None` — not a zero and not a default.
#[test]
fn chart_without_a_supplied_structure_has_no_reading() {
    let chart: LocalChart<u32, (BigInt, BigInt), WeightedSquareMetric> = LocalChart::founded(
        "placement-only",
        [(0u32, point(0, 0)), (1u32, point(3, 4))],
        None,
    );
    assert!(chart.supplied().is_none());
    assert!(chart.reading(&point(0, 0), &point(3, 4)).is_none());
}

/// Lean: `reading_isSome_of_metric_isSome`. A chart whose structure was supplied has a reading, and
/// the reading is the exact integer the supplied parameters define.
#[test]
fn chart_with_a_supplied_structure_reads_exactly() {
    let metric = SuppliedCapability::supply(WeightedSquareMetric, weights(1, 1))
        .expect("positive weights are admissible");
    let chart = LocalChart::founded(
        "euclidean-square",
        [(0u32, point(0, 0)), (1u32, point(3, 4))],
        Some(metric),
    );
    assert_eq!(chart.supplied(), Some(CapabilityKind::Metric));
    assert_eq!(
        chart.reading(&point(0, 0), &point(3, 4)),
        Some(BigInt::from(25))
    );
}

/// Lean: `preimageFibre_subset_fibre`. The population behind a face is retained whole.
#[test]
fn preimage_fibre_retains_the_whole_population() {
    let chart: LocalChart<u32, u32> =
        LocalChart::founded("blind", [(0u32, 7u32), (1u32, 7u32), (2u32, 9u32)], None);
    let fibre = chart.preimage_fibre(&7);
    assert_eq!(fibre.len(), 2, "both occurrences behind the face are kept");
    assert!(fibre.contains(&0) && fibre.contains(&1));
    assert_eq!(chart.preimage_fibre(&9).len(), 1);
    assert!(chart.preimage_fibre(&11).is_empty());
    assert!(chart.reads(&0) && !chart.reads(&5));
}

// -------------------------------------------------------------------------------------------
// The shift atlas: the embedding is not one vector
// -------------------------------------------------------------------------------------------

/// Lean: `ChartTransition.residual_reopens`, which is `Transition.reopen_apply`. The transition is
/// lossy where it truncates and the residual restores the source exactly anyway.
#[test]
fn shift_transition_residual_reopens_exactly() {
    for from in 0u64..6 {
        for to in 0u64..6 {
            let map = ShiftChartMap::new(from, to);
            for y in 0u64..12 {
                map.check_reopen(&y)
                    .expect("the retained residual reopens the source with no remainder");
            }
        }
    }
}

/// Lean: `shiftAtlas_not_invertible` and `shiftAtlas_residual_separates`. The transition merges two
/// coordinates and the residual is exactly what still separates them.
#[test]
fn shift_transition_is_lossy_and_its_residual_separates() {
    let map = ShiftChartMap::new(0, 1);
    assert_eq!(map.apply(&0).unwrap(), map.apply(&1).unwrap());
    assert_ne!(map.residual(&0).unwrap(), map.residual(&1).unwrap());
}

/// Lean: `ChartCocycle.placementEquiv` — an atlas whose transitions agree on a triple and whose
/// candidate is above the declared aperture glues to exactly one global coordinate.
#[test]
fn shift_atlas_glues_uniquely_above_the_aperture() {
    let occurrences: Vec<u64> = (0..12).collect();
    let atlas = shift_atlas(3, &occurrences);
    match atlas
        .glue("tail:0", &[9u64])
        .expect("tail:0 is an admitted chart")
    {
        AtlasGluing::Unique(placement) => {
            assert_eq!(placement.value("tail:0"), Some(&9));
            assert_eq!(placement.value("tail:3"), Some(&6));
            assert_eq!(
                placement.charts().len(),
                4,
                "every declared chart is reached"
            );
            assert_eq!(
                placement.checked().len(),
                12,
                "every ordered pair of the four charts was checked"
            );
        }
        other => panic!("expected a unique global placement, got {other:?}"),
    }
}

/// Lean: `ShiftAtlas.theEmbeddingIsNotOneVector`. Every chart reads a nonempty region into an
/// inhabited coordinate, every transition is lawful and carries its residual — and no single global
/// coordinate reading is consistent with the atlas's own transitions once the declared aperture is
/// wider than the candidate. Lean proves emptiness over the whole infinite index by citing
/// `shiftTower_obstructed`; this is that argument made finite, and widening the aperture refutes
/// every candidate in turn.
#[test]
fn the_embedding_is_not_one_vector() {
    let occurrences: Vec<u64> = (0..24).collect();
    for candidate in 0u64..6 {
        let atlas = shift_atlas(candidate + 1, &occurrences);
        for base in 0..=(candidate + 1) {
            assert!(
                atlas.chart(&format!("tail:{base}")).is_some(),
                "chart tail:{base} is admitted"
            );
            assert!(
                !atlas
                    .chart(&format!("tail:{base}"))
                    .expect("admitted")
                    .region()
                    .is_empty(),
                "chart tail:{base} reads a nonempty region"
            );
        }
        match atlas
            .glue("tail:0", &[candidate])
            .expect("tail:0 is an admitted chart")
        {
            AtlasGluing::Obstructed(AtlasObstruction::Incoherent { from, to, .. }) => {
                assert_ne!(from, to);
            }
            other => panic!(
                "candidate {candidate} under aperture {} must be obstructed, got {other:?}",
                candidate + 1
            ),
        }
    }
}

/// An empty candidate population is `Obstructed(NoCandidate)`, never an error and never a
/// fabricated placement.
#[test]
fn empty_candidate_population_is_obstructed_not_an_error() {
    let atlas = shift_atlas(2, &[0, 1, 2, 3]);
    assert!(matches!(
        atlas.glue("tail:0", &[]).expect("admitted chart"),
        AtlasGluing::Obstructed(AtlasObstruction::NoCandidate)
    ));
}

/// Lean: `atlasGluing_total` — several coherent placements are returned whole and never collapsed.
#[test]
fn a_plural_family_is_returned_whole() {
    let occurrences: Vec<u64> = (0..24).collect();
    let atlas = shift_atlas(2, &occurrences);
    match atlas
        .glue("tail:0", &[7u64, 9u64, 11u64])
        .expect("admitted chart")
    {
        AtlasGluing::Plural(family) => {
            assert_eq!(family.len(), 3, "the plurality is the content");
            assert_eq!(family[0].value("tail:0"), Some(&7));
            assert_eq!(family[2].value("tail:0"), Some(&11));
        }
        other => panic!("expected a plural family, got {other:?}"),
    }
}

/// Lean: `AtlasGluing.unique`, whose `Subsingleton` hypothesis is about the *placements* and not
/// about the caller's list. A candidate offered twice propagates to the same placement twice, which
/// is one placement: the return is `Unique`, never `Plural` of two copies. Before the
/// deduplication this returned `Plural(vec![p, p])` and reported a plurality the atlas does not
/// have.
#[test]
fn a_repeated_candidate_is_one_placement_not_a_plurality() {
    let occurrences: Vec<u64> = (0..24).collect();
    let atlas = shift_atlas(2, &occurrences);
    match atlas
        .glue("tail:0", &[7u64, 7u64])
        .expect("admitted chart")
    {
        AtlasGluing::Unique(placement) => {
            assert_eq!(placement.value("tail:0"), Some(&7));
            assert_eq!(placement.value("tail:2"), Some(&5));
        }
        other => panic!("one candidate offered twice is one placement, got {other:?}"),
    }
    // And a candidate offered many times is still one placement.
    assert!(matches!(
        atlas
            .glue("tail:0", &[9u64, 9u64, 9u64, 9u64])
            .expect("admitted chart"),
        AtlasGluing::Unique(_)
    ));
}

/// Lean: `AtlasGluing.plural`, which asks for placements that are provably distinct. Duplicates
/// inside a genuinely plural population are counted once each, so the returned family is the
/// atlas's own plurality and its length is the number of distinct placements.
#[test]
fn duplicates_inside_a_plural_population_are_counted_once() {
    let occurrences: Vec<u64> = (0..24).collect();
    let atlas = shift_atlas(2, &occurrences);
    match atlas
        .glue("tail:0", &[7u64, 9u64, 7u64, 11u64, 9u64, 11u64, 7u64])
        .expect("admitted chart")
    {
        AtlasGluing::Plural(family) => {
            assert_eq!(
                family.len(),
                3,
                "three distinct placements, however often each was offered"
            );
            assert_eq!(family[0].value("tail:0"), Some(&7));
            assert_eq!(family[1].value("tail:0"), Some(&9));
            assert_eq!(family[2].value("tail:0"), Some(&11));
            for (at, left) in family.iter().enumerate() {
                for right in family.iter().skip(at + 1) {
                    assert_ne!(
                        left.value("tail:0"),
                        right.value("tail:0"),
                        "the returned family is an antichain of distinct placements"
                    );
                }
            }
        }
        other => panic!("expected a plural family, got {other:?}"),
    }
}

// -------------------------------------------------------------------------------------------
// The cocycle, with residuals
// -------------------------------------------------------------------------------------------

/// Lean: `Cocycle` and `cocycle_iff_isEmpty_defect` — the shift atlas's own triples satisfy the
/// cocycle.
#[test]
fn shift_atlas_satisfies_the_cocycle() {
    let atlas = shift_atlas(3, &(0..12).collect::<Vec<_>>());
    let sources: Vec<u64> = (0..10).collect();
    let checked = atlas
        .check_cocycle("tail:0", "tail:2", "tail:3", &sources)
        .expect("all three transitions are declared")
        .expect("the routes agree");
    assert_eq!(checked, sources.len());
}

/// Lean: `coarseGrainDefect`, `coarseGrain_not_cocycle` and `defect_is_holonomy_not_loss`. A
/// declared direct transition that is not the composite returns a defect **as content**, and both
/// routes still reopen their source with no remainder — the disagreement is holonomy, not loss.
#[test]
fn a_cocycle_defect_is_returned_as_content_and_both_routes_reopen() {
    let mut atlas: ReceiverAtlas<u64, ShiftCoordinate, u64> =
        ReceiverAtlas::found("holonics.receiver_atlas.defect.v1");
    for base in [0u64, 2, 3] {
        atlas.admit(LocalChart::founded(
            format!("tail:{base}"),
            (0u64..12).filter(|x| *x >= base).map(|x| (x, x - base)),
            None,
        ));
    }
    atlas
        .declare_transition("tail:0", "tail:2", Box::new(ShiftChartMap::new(0, 2)))
        .expect("both charts admitted");
    atlas
        .declare_transition("tail:2", "tail:3", Box::new(ShiftChartMap::new(2, 3)))
        .expect("both charts admitted");
    // The direct passage declared here is *wrong*: it re-bases from 0 to 1, not from 0 to 3.
    atlas
        .declare_transition("tail:0", "tail:3", Box::new(ShiftChartMap::new(0, 1)))
        .expect("both charts admitted");

    let defect = atlas
        .check_cocycle("tail:0", "tail:2", "tail:3", &[8u64])
        .expect("all three transitions are declared")
        .expect_err("the routes disagree");
    assert_eq!(defect.source, 8);
    assert_eq!(defect.routed, 5);
    assert_eq!(defect.direct, 7);
    assert_eq!(
        defect.charts,
        ["tail:0".to_string(), "tail:2".to_string(), "tail:3".to_string()]
    );

    defect
        .both_routes_reopen(
            &ShiftChartMap::new(0, 2),
            &ShiftChartMap::new(2, 3),
            &ShiftChartMap::new(0, 1),
        )
        .expect("a cocycle defect is holonomy, not loss: both routes reopen exactly");
}

/// Lean: `TransitionUndeclared` is the executable form of "a chart with no declared relation to
/// another chart is incomparable, and the type says so" — not a denial and not a default route.
#[test]
fn an_undeclared_transition_is_incomparable_not_false() {
    let atlas = shift_atlas(2, &(0..8).collect::<Vec<_>>());
    let refusal = atlas
        .check_cocycle("tail:0", "tail:1", "tail:9", &[3u64])
        .expect_err("tail:9 is not an admitted chart, so no transition reaches it");
    assert!(matches!(refusal, AtlasRefusal::TransitionUndeclared { .. }));
}

// -------------------------------------------------------------------------------------------
// Hostile input against the atlas constructors
// -------------------------------------------------------------------------------------------

/// A transition between names the atlas does not carry is refused by name, with no allocation and
/// no panic.
#[test]
fn atlas_refuses_a_transition_between_absent_charts() {
    let mut atlas: ReceiverAtlas<u64, ShiftCoordinate, u64> = ReceiverAtlas::found("hostile");
    atlas.admit(LocalChart::founded("tail:0", [(0u64, 0u64)], None));
    assert_eq!(
        atlas.declare_transition("tail:0", "tail:404", Box::new(ShiftChartMap::new(0, 404))),
        Err(AtlasRefusal::ChartAbsent {
            name: "tail:404".to_string()
        })
    );
    assert_eq!(
        atlas.declare_transition("tail:404", "tail:0", Box::new(ShiftChartMap::new(404, 0))),
        Err(AtlasRefusal::ChartAbsent {
            name: "tail:404".to_string()
        })
    );
}

/// One ordered pair of charts carries at most one declared transition; a second declaration is
/// refused rather than silently replacing the first.
#[test]
fn atlas_refuses_a_duplicate_transition() {
    let mut atlas: ReceiverAtlas<u64, ShiftCoordinate, u64> = ReceiverAtlas::found("hostile");
    atlas.admit(LocalChart::founded("a", [(0u64, 0u64)], None));
    atlas.admit(LocalChart::founded("b", [(0u64, 0u64)], None));
    atlas
        .declare_transition("a", "b", Box::new(ShiftChartMap::new(0, 1)))
        .expect("first declaration is admitted");
    assert_eq!(
        atlas.declare_transition("a", "b", Box::new(ShiftChartMap::new(0, 2))),
        Err(AtlasRefusal::TransitionAlreadyDeclared {
            from: "a".to_string(),
            to: "b".to_string()
        })
    );
}

/// Gluing from a chart the atlas does not carry is refused by name.
#[test]
fn glue_refuses_an_absent_base_chart() {
    let atlas = shift_atlas(1, &[0, 1, 2]);
    assert_eq!(
        atlas.glue("tail:404", &[0u64]),
        Err(AtlasRefusal::ChartAbsent {
            name: "tail:404".to_string()
        })
    );
}

/// A chart map asked for a coordinate arm it does not read refuses by name rather than defaulting.
#[test]
fn a_chart_map_refuses_a_coordinate_it_does_not_read() {
    let map = ContactComplexChartMap::new();
    let refusal = map
        .apply(&ProteinCoordinate::Sequence(vec![1, 2, 3]))
        .expect_err("the contact-complex map reads only the alpha-carbon grain");
    assert!(matches!(
        refusal,
        AtlasRefusal::CoordinateNotInChart {
            expected: "AlphaCarbonGrain",
            ..
        }
    ));
}

// -------------------------------------------------------------------------------------------
// The protein atlas
// -------------------------------------------------------------------------------------------

fn atom_cell(residue: u32, atom: u32) -> crate::grain_tower::GrainCell {
    GrainAddress::new(0, residue, atom).cell(Grain::Atom)
}

fn atom_pair(r1: u32, a1: u32, r2: u32, a2: u32) -> GrainPair {
    GrainPair::new(atom_cell(r1, a1), atom_cell(r2, a2)).expect("distinct atom cells at one grain")
}

/// Three residues, each with two atoms; atom `0` of each residue is its alpha carbon.
fn presented_atom_face() -> GrainFace {
    GrainFace::founded(
        Grain::Atom,
        [
            // a pair of alpha carbons: the selection sees this one
            (atom_pair(0, 0, 1, 0), ContactClass::Inside),
            // a pair of side-chain atoms: the selection never looks at it
            (atom_pair(0, 1, 2, 1), ContactClass::Inside),
            // a pair of alpha carbons the aperture could not decide: `Open` stays `Open`
            (atom_pair(1, 0, 2, 0), ContactClass::Open),
        ],
    )
    .expect("no reading is Outside and every pair is at the atom grain")
}

fn alpha_carbon_selection() -> GrainSelection {
    GrainSelection::declare(
        "label_atom_id == CA",
        Grain::Residue,
        Grain::Atom,
        [
            GrainAddress::new(0, 0, 0),
            GrainAddress::new(0, 1, 0),
            GrainAddress::new(0, 2, 0),
        ],
    )
    .expect("one representative per residue, each inside the residue it represents")
}

/// The exact rigidity reading of a 2-dimensional triangle, over exact rationals. It exists to give
/// the rigidity chart a coordinate that was actually *read*, not fabricated.
fn triangle_maxwell() -> MaxwellCount {
    let zero = Rat::from_integer(BigInt::from(0));
    let one = Rat::from_integer(BigInt::from(1));
    let configuration = ExactConfiguration::declared(
        2,
        [
            (ConstraintVertexId(0), vec![zero.clone(), zero.clone()]),
            (ConstraintVertexId(1), vec![one.clone(), zero.clone()]),
            (ConstraintVertexId(2), vec![zero.clone(), one.clone()]),
        ],
    )
    .expect("three places, each with two exact rational coordinates");
    let mut constraints = BTreeMap::new();
    for (left, right) in [(0u64, 1u64), (1, 2), (0, 2)] {
        let (edge, _) = ConstraintEdge::new(ConstraintVertexId(left), ConstraintVertexId(right))
            .expect("distinct vertices");
        constraints.insert(edge, EdgeProvenance::Polygonal);
    }
    let jacobian = RigidityJacobian::found("tests::triangle", &configuration, &constraints)
        .expect("the Jacobian of three distance constraints at an exact configuration");
    rigidity_reading(&jacobian)
        .expect("the exact rank, kernel and cokernel of that Jacobian")
        .maxwell
}

fn placements() -> (Vec<(PresentationId, ProteinPlacement)>, GrainSelection) {
    let selection = alpha_carbon_selection();
    let atom_face = presented_atom_face();
    let coarse = selection.apply(&atom_face);

    // The second presentation differs from the first **only** in a contact the alpha-carbon
    // selection never looked at. Its coarse face is therefore identical.
    let thinned = atom_face.without([atom_pair(0, 1, 2, 1)]);
    let thinned_coarse = selection.apply(&thinned);
    assert_eq!(
        coarse, thinned_coarse,
        "deleting a fine-only contact leaves the coarse face unchanged"
    );

    (
        vec![
            (
                PresentationId(0),
                ProteinPlacement {
                    sequence: vec![7, 11, 13],
                    all_atom: atom_face,
                    alpha_carbon: coarse,
                    rigidity: Some(triangle_maxwell()),
                },
            ),
            (
                PresentationId(1),
                ProteinPlacement {
                    sequence: vec![7, 11, 13],
                    all_atom: thinned,
                    alpha_carbon: thinned_coarse,
                    rigidity: None,
                },
            ),
        ],
        selection,
    )
}

/// The five charts the plan names, and the two transitions the atlas actually declares.
#[test]
fn protein_atlas_admits_five_charts_and_declares_two_transitions() {
    let (population, selection) = placements();
    let atlas = protein_atlas(&population, selection).expect("the atlas is well formed");
    assert_eq!(atlas.charts().len(), 5);
    for name in PROTEIN_CHARTS {
        assert!(atlas.chart(name).is_some(), "chart {name} is admitted");
    }
    assert!(atlas.comparable("allAtomFrames", "alphaCarbonGrain"));
    assert!(atlas.comparable("alphaCarbonGrain", "contactComplex"));
    assert!(
        !atlas.comparable("sequence", "allAtomFrames"),
        "no transition out of the sequence chart is declared: the relation is undiscovered, not \
         denied"
    );
    assert!(
        !atlas.comparable("contactComplex", "rigidityReading"),
        "the rigidity reading needs a supplied configuration; the atlas declares no route to it"
    );
}

/// **The deliverable equation.** Lean: `GrainRestriction.grain_residual_reopens_the_source`, which
/// is `Transition.reopen_apply` at the grain transition. The alpha-carbon selection is a genuinely
/// lossy chart transition and its residual reopens the atom-grain face exactly.
#[test]
fn the_grain_restriction_is_lossy_and_its_round_trip_is_exact() {
    let selection = alpha_carbon_selection();
    let map = AlphaCarbonChartMap::new(selection);
    let source = ProteinCoordinate::AllAtomFrame(presented_atom_face());

    let transported = map.apply(&source).expect("the map reads the atom grain");
    let residual = map.residual(&source).expect("the map reads the atom grain");

    let ProteinResidual::Selection(retained) = &residual else {
        panic!("the grain transition retains a selection residual");
    };
    assert_eq!(
        retained.retained(),
        1,
        "exactly the one fine-only contact the selection never looked at is retained"
    );

    let ProteinCoordinate::AlphaCarbonGrain(coarse) = &transported else {
        panic!("the grain transition transports to the alpha-carbon grain");
    };
    assert_eq!(coarse.grain(), Grain::Residue);
    assert_eq!(coarse.inside(), 1, "one alpha-carbon contact is transported");
    assert_eq!(coarse.open(), 1, "and the Open reading stays Open");

    map.check_reopen(&source)
        .expect("the coarse face together with the residual reopens the atom face exactly");
    assert_eq!(
        map.reopen(&transported, &residual)
            .expect("the reopening reads both arms"),
        source,
        "the round trip through the residual is exact, not approximate"
    );
}

/// The second transition is lossy too, and `Open` is never rounded: the pairs the contact complex
/// drops travel in the residual with their exact class.
#[test]
fn the_contact_complex_forgets_open_and_retains_it_whole() {
    let selection = alpha_carbon_selection();
    let coarse = ProteinCoordinate::AlphaCarbonGrain(selection.apply(&presented_atom_face()));
    let map = ContactComplexChartMap::new();

    let transported = map.apply(&coarse).expect("reads the alpha-carbon grain");
    let residual = map.residual(&coarse).expect("reads the alpha-carbon grain");
    let ProteinCoordinate::ContactComplex(inside) = &transported else {
        panic!("the contact complex is a set of Inside pairs");
    };
    assert_eq!(inside.len(), 1);
    let ProteinResidual::OpenClass(dropped) = &residual else {
        panic!("the retained residual is the forgotten class");
    };
    assert_eq!(dropped.len(), 1);
    assert_eq!(
        dropped.values().next(),
        Some(&ContactClass::Open),
        "an Open reading is retained as Open, never rounded"
    );
    map.check_reopen(&coarse)
        .expect("the contact complex together with the retained class reopens the coarse face");
}

/// Lean: `SeparatingAtlas.coarse_cannot_separate` and `rich_separates`, together with
/// `GrainRestriction.residual_separates_fineOnly`. Two presentations agreeing on every coarse chart
/// are indistinguishable to the coarse atlas; the all-atom chart reopens exactly that collapse.
#[test]
fn a_richer_chart_reopens_what_the_coarse_atlas_cannot_separate() {
    let (population, selection) = placements();
    let atlas = protein_atlas(&population, selection).expect("the atlas is well formed");

    let separating = atlas.separating_charts(&PresentationId(0), &PresentationId(1));
    assert_eq!(
        separating,
        vec!["allAtomFrames".to_string()],
        "only the finest chart separates them"
    );
    assert!(!atlas.indistinguishable(&PresentationId(0), &PresentationId(1)));

    // The same population read by a coarse atlas that admits only the charts below the atom grain.
    let mut coarse: ProteinAtlas = ReceiverAtlas::found("holonics.receiver_atlas.protein.coarse.v1");
    for name in ["sequence", "alphaCarbonGrain", "contactComplex"] {
        coarse.admit(
            atlas
                .chart(name)
                .expect("the chart is admitted by the full atlas")
                .clone(),
        );
    }
    assert!(
        coarse.indistinguishable(&PresentationId(0), &PresentationId(1)),
        "the coarse atlas cannot separate them, which is a fact about that atlas and not about \
         the presentations"
    );
    assert!(coarse
        .separating_charts(&PresentationId(0), &PresentationId(1))
        .is_empty());
}

/// The rigidity chart reads only the presentations that supplied an exact configuration. A reading
/// that was not supplied is **absent**, never zero.
#[test]
fn the_rigidity_chart_reads_only_what_supplied_a_configuration() {
    let (population, selection) = placements();
    let atlas = protein_atlas(&population, selection).expect("the atlas is well formed");
    let chart = atlas.chart("rigidityReading").expect("admitted");
    assert!(chart.reads(&PresentationId(0)));
    assert!(!chart.reads(&PresentationId(1)));
    let Some(ProteinCoordinate::RigidityReading(count)) = chart.place(&PresentationId(0)) else {
        panic!("the rigidity chart places the first presentation at its Maxwell count");
    };
    assert_eq!(count.coordinate_freedoms, 6);
    assert_eq!(count.constraints, 3);
    assert_eq!(count.rank, 3);
    assert_eq!(count.self_stress_dimension, 0);
    assert_eq!(count.counted_freedom, 3, "d·n − m for a rigid 2D triangle");
    assert!(!count.count_is_a_bound_only);
}

/// Gluing the protein atlas from the all-atom chart propagates through both declared transitions
/// and returns exactly the presented coarse readings — the atlas is coherent where it is declared.
#[test]
fn protein_atlas_glues_from_the_all_atom_chart() {
    let (population, selection) = placements();
    let presented = population[0].1.clone();
    let atlas = protein_atlas(&population, selection).expect("the atlas is well formed");

    match atlas
        .glue(
            "allAtomFrames",
            &[ProteinCoordinate::AllAtomFrame(presented.all_atom.clone())],
        )
        .expect("allAtomFrames is admitted")
    {
        AtlasGluing::Unique(placement) => {
            assert_eq!(
                placement.value("alphaCarbonGrain"),
                Some(&ProteinCoordinate::AlphaCarbonGrain(
                    presented.alpha_carbon.clone()
                ))
            );
            assert!(placement.value("contactComplex").is_some());
            assert!(
                placement.value("sequence").is_none(),
                "no transition reaches the sequence chart, so the placement does not invent one"
            );
            assert_eq!(placement.checked().len(), 2);
        }
        other => panic!("expected a unique placement, got {other:?}"),
    }
}

// ===========================================================================================
// R7 — the separating atlas theorem
// ===========================================================================================

use std::collections::BTreeSet;

use num_traits::One;

use crate::algebraic::{CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex};
use crate::causal::EventId;
use crate::causal_chord::{Linearization, separate_under_probe, transfer_function};
use crate::exact_linear::ExactRatMatrix;
use crate::exact_value::ExactInterval;
use crate::hodge_receiver::{
    BoundaryCondition, HodgeOperator, MetricDeclaration, hodge_reading,
};
use crate::physical_constraint_complex::{ConstraintComponentId, CoordinateBox3};
use crate::rational_polynomial::RationalPolynomial;
use crate::topological_receiver::{
    ApertureFiltration, Coefficients, DeclaredFiltration, FiltrationOrder, OrderLaw, persistence,
    persistence_with_grade_zero_agreement,
};

fn rational(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn exact_matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().copied().map(rational).collect())
            .collect(),
    )
    .expect("a rectangular exact matrix")
}

fn matrix_power(state: &ExactRatMatrix, exponent: usize) -> ExactRatMatrix {
    let mut accumulated =
        ExactRatMatrix::identity(state.rows()).expect("a square operator has an identity");
    for _ in 0..exponent {
        accumulated = accumulated.multiply(state).expect("the powers stay square");
    }
    accumulated
}

/// **The full coordinate probe atlas over a declared bounded class of exact linear systems.**
///
/// One chart per (excitation coordinate `i`, readout coordinate `j`, time `k`), reading the exact
/// Markov parameter `(A^k)[j][i]`: the response of readout `j` to an impulse at excitation `i`,
/// `k` steps later. This is the atlas of
/// `Foundation/ReceiverAtlas.lean::SeparatingAtlas.fullProbeAtlas`.
fn full_probe_atlas(class: &[ExactRatMatrix], horizon: usize) -> ReceiverAtlas<u32, Rat, ()> {
    let extent = class[0].rows();
    let mut atlas = ReceiverAtlas::found("holonics.receiver_atlas.full-probe.v1");
    // `by_time[k][id]` is `A_id^k`, assembled once so the chart loop indexes nothing.
    let by_time = (0..=horizon)
        .map(|exponent| {
            class
                .iter()
                .map(|state| matrix_power(state, exponent))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    for (time, per_member) in by_time.iter().enumerate() {
        for probe in 0..extent {
            for readout in 0..extent {
                let placements = per_member
                    .iter()
                    .enumerate()
                    .map(|(id, power)| {
                        (
                            id as u32,
                            power
                                .get(readout, probe)
                                .expect("the coordinate is inside the operator")
                                .clone(),
                        )
                    })
                    .collect::<Vec<_>>();
                atlas.admit_at(
                    LocalChart::founded(
                        format!("markov@t{time}/probe{probe}/readout{readout}"),
                        placements,
                        None,
                    ),
                    time,
                );
            }
        }
    }
    atlas
}

/// Lean: `SeparatingAtlas.fullProbeAtlas_separates` and
/// `SeparatingAtlas.identity_probe_determines_the_operator`.
///
/// **R7(a): the full probe atlas separates the whole declared class, and the separating time is
/// one.** Two of the three members are isospectral — the nilpotent Jordan block and the zero
/// operator share the characteristic polynomial `s²` — and the atlas still tells them apart.
#[test]
fn the_full_probe_atlas_separates_the_declared_linear_class() {
    let class = vec![
        exact_matrix(&[&[0, 1], &[0, 0]]),
        exact_matrix(&[&[0, 0], &[0, 0]]),
        exact_matrix(&[&[1, 0], &[0, 2]]),
    ];
    let atlas = full_probe_atlas(&class, 1);
    match atlas
        .is_separating(&[0u32, 1, 2], 1)
        .expect("the search returns")
    {
        SeparatingVerdict::Separating {
            members,
            pairs_checked,
            horizon_bound,
        } => assert_eq!((members, pairs_checked, horizon_bound), (3, 3, 1)),
        other => panic!("the full probe atlas is separating, got {other:?}"),
    }

    // At time zero every chart reads the identity, so nothing separates and the charts the bound
    // excluded are **named** rather than silently skipped.
    match atlas.separate(&0u32, &1u32, 0) {
        SeparationOutcome::IndistinguishableToThisAtlas {
            charts_read,
            charts_beyond_bound,
            horizon_bound,
            ..
        } => {
            assert_eq!(charts_read.len(), 4);
            assert_eq!(charts_beyond_bound.len(), 4);
            assert_eq!(horizon_bound, 0);
        }
        other => panic!("time zero reads the identity, got {other:?}"),
    }

    // At time one the `k = 1` Markov parameter is the operator itself, so the `(0,1)` entry
    // separates them exactly.
    match atlas.separate(&0u32, &1u32, 1) {
        SeparationOutcome::Separated(separator) => {
            assert_eq!(separator.chart, "markov@t1/probe1/readout0");
            assert_eq!(separator.time, 1);
            assert_eq!(separator.left, Rat::one());
            assert!(separator.right.is_zero());
        }
        other => panic!("the k=1 Markov parameter separates them, got {other:?}"),
    }
}

/// Lean: `Foundation/CausalChord.lean::spectrum_does_not_determine_response`, stated in the
/// atlas's own vocabulary. **The spectral atlas alone is not separating**, and the richer
/// receiver that does separate the pair is named.
#[test]
fn the_spectral_atlas_alone_does_not_separate_the_isospectral_pair() {
    let class = vec![
        exact_matrix(&[&[0, 1], &[0, 0]]),
        exact_matrix(&[&[0, 0], &[0, 0]]),
    ];
    let mut spectral: ReceiverAtlas<u32, Rat, ()> =
        ReceiverAtlas::found("holonics.receiver_atlas.spectrum-only.v1");
    // Trace and determinant are the whole characteristic polynomial of a 2×2 operator.
    spectral.admit(LocalChart::founded(
        "characteristic/determinant",
        class.iter().enumerate().map(|(id, state)| {
            (
                id as u32,
                state.get(0, 0).expect("entry") * state.get(1, 1).expect("entry")
                    - state.get(0, 1).expect("entry") * state.get(1, 0).expect("entry"),
            )
        }),
        None,
    ));
    spectral.admit(LocalChart::founded(
        "characteristic/trace",
        class.iter().enumerate().map(|(id, state)| {
            (
                id as u32,
                state.get(0, 0).expect("entry") + state.get(1, 1).expect("entry"),
            )
        }),
        None,
    ));
    match spectral
        .is_separating(&[0u32, 1], 8)
        .expect("the search returns")
    {
        SeparatingVerdict::NotSeparating(insufficiency) => {
            assert_eq!((insufficiency.left, insufficiency.right), (0, 1));
            assert_eq!(
                insufficiency.charts_read,
                vec![
                    "characteristic/determinant".to_owned(),
                    "characteristic/trace".to_owned()
                ]
            );
        }
        other => panic!("the spectrum cannot separate them, got {other:?}"),
    }

    // The richer receiver: the Markov parameter at time one.
    let richer = full_probe_atlas(&class, 1);
    assert!(matches!(
        richer.separate(&0u32, &1u32, 1),
        SeparationOutcome::Separated(_)
    ));
}

/// Lean: `SeparatingAtlas.pow_eq_aeval_modByMonic_charpoly` and
/// `SeparatingAtlas.markov_truncation`.
///
/// **The Cayley–Hamilton truncation, computed.** Every power of a generator is the evaluation at
/// that generator of the remainder of `X^k` modulo its characteristic polynomial, a polynomial of
/// degree strictly below the dimension — so every Markov parameter above time `n − 1` is an exact
/// rational combination of the first `n`, and the atlas gains nothing past that time from *this*
/// operator. The `2n` bound of realization theory is a different statement and is **not** proved
/// here; `MarkovTwoNSuffices` names it open in the Lean owner.
#[test]
fn every_markov_parameter_is_a_combination_of_the_first_n() {
    let state = exact_matrix(&[&[0, 1, 0], &[0, 0, 1], &[2, -3, 4]]);
    let extent = 3usize;
    let characteristic = state
        .characteristic_polynomial()
        .expect("the exact characteristic polynomial");
    assert_eq!(characteristic.degree(), Some(extent));
    let readout = exact_matrix(&[&[1, 0, 0]]);
    let excitation = exact_matrix(&[&[0], &[0], &[1]]);

    let mut monomial = RationalPolynomial::one();
    for exponent in 0..=8usize {
        let (_, remainder) = monomial
            .divided_by(&characteristic)
            .expect("a monic divisor divides");
        assert!(
            remainder.degree().unwrap_or(0) < extent,
            "the truncated remainder has degree below the dimension"
        );
        let mut evaluated =
            ExactRatMatrix::zero(extent, extent).expect("a zero operator of the extent");
        let mut combined = ExactRatMatrix::zero(1, 1).expect("a one-by-one zero");
        for degree in 0..extent {
            let coefficient = remainder.coefficient(degree);
            if coefficient.is_zero() {
                continue;
            }
            let power = matrix_power(&state, degree);
            evaluated = evaluated
                .add(&power.scaled(&coefficient))
                .expect("the shapes agree");
            let parameter = readout
                .multiply(&power)
                .expect("shapes")
                .multiply(&excitation)
                .expect("shapes");
            combined = combined
                .add(&parameter.scaled(&coefficient))
                .expect("the shapes agree");
        }
        assert_eq!(
            matrix_power(&state, exponent),
            evaluated,
            "A^{exponent} is the truncated remainder evaluated at A"
        );
        let markov = readout
            .multiply(&matrix_power(&state, exponent))
            .expect("shapes")
            .multiply(&excitation)
            .expect("shapes");
        assert_eq!(
            markov, combined,
            "the Markov parameter at time {exponent} is that same combination of the first \
             {extent}"
        );
        monomial = monomial.times(&RationalPolynomial::variable());
    }
}

// -------------------------------------------------------------------------------------------
// R7(b) — the finite complexes, under the R3 + R5 atlas: **not** separating
// -------------------------------------------------------------------------------------------

/// A finite one-dimensional complex on a declared occurrence population and a declared contact
/// set, with the simplex labels the persistence filtration needs.
struct GraphComplex {
    complex: GradedCausalComplex,
    cells_by_simplex: BTreeMap<Vec<usize>, CausalCellId>,
    entry: BTreeMap<CausalCellId, ExactInterval>,
}

fn graph_complex(occurrences: usize, contacts: &[(usize, usize)]) -> GraphComplex {
    let events = BTreeSet::from([EventId(1)]);
    let mut complex = GradedCausalComplex::default();
    let mut cells_by_simplex = BTreeMap::new();
    let mut entry = BTreeMap::new();
    let mut vertices = Vec::new();
    for at in 0..occurrences {
        let cell = complex
            .found_cell(format!("v{at}"), events.clone(), 0, CausalChain::default())
            .expect("a vertex founds");
        vertices.push(cell);
        cells_by_simplex.insert(vec![at], cell);
        entry.insert(
            cell,
            ExactInterval {
                lower: Rat::zero(),
                upper: Rat::zero(),
            },
        );
    }
    for (lower, upper) in contacts {
        assert!(lower < upper, "a contact is written in ascending order");
        let mut boundary = CausalChain::default();
        boundary.add_term(vertices[*upper], ComparativeMultiplicity::positive(1_u8));
        boundary.add_term(vertices[*lower], ComparativeMultiplicity::negative(1_u8));
        let cell = complex
            .found_cell(format!("e{lower}_{upper}"), events.clone(), 1, boundary)
            .expect("a contact founds");
        cells_by_simplex.insert(vec![*lower, *upper], cell);
        entry.insert(
            cell,
            ExactInterval {
                lower: Rat::one(),
                upper: Rat::one(),
            },
        );
    }
    complex.validate().expect("the founded complex stands");
    GraphComplex {
        complex,
        cells_by_simplex,
        entry,
    }
}

/// **The declared R3 + R5 reading of a finite one-dimensional complex**: what the two receivers
/// together actually return when no configuration is supplied. Mirrors
/// `Foundation/ReceiverAtlas.lean::SeparatingAtlas.SpectralTopologicalReading`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct SpectralTopologicalReading {
    occurrences: usize,
    contacts: usize,
    grade_zero_spectrum: Vec<Rat>,
    grade_one_spectrum: Vec<Rat>,
    betti: Vec<usize>,
    torsion: Vec<Vec<BigInt>>,
    /// The persistence **diagram**: the multiset of exact `(grade, birth, death)` *values*. The
    /// positions of the reduction are deliberately not recorded — every occurrence enters at `0`
    /// and every contact at `1`, so the order's tie-break is an artifact and the two graphs' pair
    /// *positions* differ while their diagrams agree exactly.
    persistence: Vec<(u32, Rat, Option<Rat>)>,
}

fn read_spectral_topological(
    lineage: &str,
    occurrences: usize,
    contacts: &[(usize, usize)],
) -> SpectralTopologicalReading {
    let built = graph_complex(occurrences, contacts);
    let metric = MetricDeclaration::unit(format!("{lineage}|unit"));
    let operator = HodgeOperator::found(
        lineage,
        &built.complex,
        &metric,
        &BoundaryCondition::Free,
    )
    .expect("the operator founds");
    let mut spectra = Vec::new();
    let mut betti = Vec::new();
    let mut torsion = Vec::new();
    for grade in 0..=1u32 {
        let laplacian = operator.laplacian(grade).expect("the Laplacian");
        spectra.push(
            laplacian
                .characteristic_polynomial()
                .expect("the exact characteristic polynomial")
                .coefficients()
                .to_vec(),
        );
        let reading = hodge_reading(&operator, grade).expect("the reading");
        betti.push(reading.betti);
        torsion.push(reading.torsion.clone());
    }

    // R5, over the declared dimension filtration: every occurrence enters at 0, every contact at 1.
    let filtration = ApertureFiltration::found_declared(DeclaredFiltration {
        lineage: format!("{lineage}|dimension-filtration"),
        source_event: EventId(1),
        complex: built.complex.clone(),
        occurrences: (0..occurrences)
            .map(|at| ConstraintVertexId(at as u64 + 1))
            .collect(),
        component_of: (0..occurrences)
            .map(|at| (ConstraintVertexId(at as u64 + 1), ConstraintComponentId(1)))
            .collect(),
        cells_by_simplex: built.cells_by_simplex.clone(),
        entry: built.entry.clone(),
        ceiling: Rat::one(),
    })
    .expect("the declared filtration stands");
    let order = FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound)
        .expect("the lower-bound order is admissible");
    let reading = persistence(&filtration, &order, &Coefficients::Rational, 100_000)
        .expect("the reduction returns");
    let mut pairs = reading
        .pairs
        .iter()
        .map(|pair| {
            (
                pair.grade,
                pair.birth_value.lower.clone(),
                pair.death_value.as_ref().map(|value| value.lower.clone()),
            )
        })
        .collect::<Vec<_>>();
    pairs.sort();

    SpectralTopologicalReading {
        occurrences,
        contacts: contacts.len(),
        grade_zero_spectrum: spectra[0].clone(),
        grade_one_spectrum: spectra[1].clone(),
        betti,
        torsion,
        persistence: pairs,
    }
}

/// The two Laplacian-cospectral non-isomorphic graphs of
/// `causal_chord::cospectral_graphs_are_separated_by_the_response_atlas`, as declared
/// one-dimensional complexes.
const FIRST_GRAPH: [(usize, usize); 7] = [(0, 2), (0, 3), (0, 4), (0, 5), (1, 4), (1, 5), (2, 3)];
const SECOND_GRAPH: [(usize, usize); 7] = [(0, 2), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3)];

/// Lean: `SeparatingAtlas.readings_agree`, `SeparatingAtlas.spectralTopologicalInsufficiency` and
/// `SeparatingAtlas.no_transformer_from_the_spectral_topological_reading`.
///
/// **R7(b): the R3 + R5 atlas is not separating, and that is the result.**
///
/// The two graphs are not isomorphic — their degree sequences are `(4,2,2,2,2,2)` and
/// `(3,3,3,2,2,1)` — and the whole declared R3 + R5 atlas returns the *same* reading for both:
/// the same grade-0 and grade-1 Hodge spectra under the unit metric, the same integral Betti
/// numbers and torsion, and the same persistence of the dimension filtration.
///
/// The grade-1 agreement is not a coincidence. For a one-dimensional complex `Δ₁ = d₀ d₀*` and
/// `Δ₀ = d₀* d₀` share every nonzero eigenvalue with multiplicity, so the grade-1 characteristic
/// polynomial is `X^{E−V}` times the grade-0 one and adds no information at all. That is checked
/// below as an identity, not asserted.
#[test]
fn the_spectral_and_topological_atlas_cannot_separate_two_non_isomorphic_complexes() {
    let first = read_spectral_topological("cospectral-a", 6, &FIRST_GRAPH);
    let second = read_spectral_topological("cospectral-b", 6, &SECOND_GRAPH);

    // Not isomorphic: the degree sequences differ.
    let degrees = |contacts: &[(usize, usize)]| {
        let mut found = vec![0usize; 6];
        for (lower, upper) in contacts {
            found[*lower] += 1;
            found[*upper] += 1;
        }
        found.sort_unstable();
        found
    };
    assert_ne!(degrees(&FIRST_GRAPH), degrees(&SECOND_GRAPH));

    assert_eq!(
        first, second,
        "the whole R3 + R5 atlas returns one reading for two non-isomorphic complexes"
    );
    assert_eq!(first.occurrences, 6);
    assert_eq!(first.contacts, 7);
    assert_eq!(first.betti, vec![1, 2], "connected, with two independent cycles");
    assert!(first.torsion.iter().all(Vec::is_empty), "a graph carries no torsion");

    // The grade-1 spectrum is `X^{E−V}` times the grade-0 one: the singular-value duality, as an
    // exact polynomial identity rather than an assertion.
    let grade_zero = RationalPolynomial::new(first.grade_zero_spectrum.clone());
    let grade_one = RationalPolynomial::new(first.grade_one_spectrum.clone());
    let shift = {
        let mut coefficients = vec![Rat::zero(); first.contacts - first.occurrences];
        coefficients.push(Rat::one());
        RationalPolynomial::new(coefficients)
    };
    assert_eq!(grade_one, grade_zero.times(&shift));

    // The richer receiver that **does** separate them: R1's driving-point response at occurrence
    // zero. This is the whole content of the insufficiency — it names the missing receiver.
    let negative_laplacian = |contacts: &[(usize, usize)]| {
        let mut rows = vec![vec![Rat::zero(); 6]; 6];
        for (lower, upper) in contacts {
            rows[*lower][*lower] = &rows[*lower][*lower] - Rat::one();
            rows[*upper][*upper] = &rows[*upper][*upper] - Rat::one();
            rows[*lower][*upper] = &rows[*lower][*upper] + Rat::one();
            rows[*upper][*lower] = &rows[*upper][*lower] + Rat::one();
        }
        ExactRatMatrix::shaped(6, 6, rows).expect("a Laplacian is square")
    };
    let left = Linearization::single_probe("cospectral-a", negative_laplacian(&FIRST_GRAPH), 0, 0)
        .expect("declared");
    let right =
        Linearization::single_probe("cospectral-b", negative_laplacian(&SECOND_GRAPH), 0, 0)
            .expect("declared");
    let separation =
        separate_under_probe(&left, &right).expect("the R1 response atlas separates them");
    assert_ne!(separation.left_numerator, separation.right_numerator);

    println!(
        "R7(b) | R3+R5 reading shared by two non-isomorphic complexes | V {} | E {} | \
         grade-0 charpoly {:?} | grade-1 charpoly {:?} | betti {:?} | torsion {:?} | \
         persistence pairs {} | separated by R1 driving-point numerators {:?} vs {:?}",
        first.occurrences,
        first.contacts,
        first
            .grade_zero_spectrum
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        first
            .grade_one_spectrum
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        first.betti,
        first.torsion,
        first.persistence.len(),
        separation
            .left_numerator
            .coefficients()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        separation
            .right_numerator
            .coefficients()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
    );
}

// -------------------------------------------------------------------------------------------
// the contracts that make an atlas credible
// -------------------------------------------------------------------------------------------

/// Every `Satisfied` row of the ledger is **recomputed**, and the enumeration is generic: the
/// rows are read off [`ledger_entries`] rather than named one by one, so no `Satisfied` row can be
/// added without a verifier behind it.
///
/// Two things make the claim structural rather than a convention this test happens to check:
/// [`ContractStatus::Satisfied`] carries a [`Recomputed`] token whose only constructor is private
/// to `receiver_atlas`, so the arm has no literal anywhere; and a
/// [`ContractEntry::Standing`] row carries a [`StandingStatus`], which has no `Satisfied` arm at
/// all. A `Satisfied` row is therefore necessarily the return of a
/// [`ContractEntry::Recomputed`] verifier, and this test checks that every one of them really is.
#[test]
fn the_contract_ledger_recomputes_every_satisfied_row() {
    let entries = ledger_entries();
    let ledger = contract_ledger();
    assert_eq!(ledger.len(), 30);
    assert_eq!(entries.len(), ledger.len());

    let mut satisfied = 0usize;
    let mut unproved = 0usize;
    let mut failed = 0usize;
    let mut inapplicable = 0usize;
    for ((receiver, contract, entry), row) in entries.iter().zip(&ledger) {
        assert_eq!(*receiver, row.receiver);
        assert_eq!(*contract, row.contract);
        // The row's status is what its entry produces, and producing it twice produces the same
        // thing: a recomputed row is recomputed, not memoized.
        assert_eq!(entry.status(), row.status);
        assert_eq!(entry.status(), entry.status());
        match &row.status {
            ContractStatus::Satisfied(recomputed) => {
                satisfied += 1;
                assert!(
                    entry.is_recomputed(),
                    "{receiver} {contract:?} is Satisfied without a verifier behind it"
                );
                assert!(
                    !recomputed.witness().is_empty(),
                    "{receiver} {contract:?} returns an empty witness"
                );
                assert_eq!(row.status.witness(), Some(recomputed.witness()));
            }
            ContractStatus::Unproved { missing } => {
                unproved += 1;
                assert!(!missing.is_empty());
            }
            ContractStatus::Failed { counterexample } => {
                failed += 1;
                assert!(!counterexample.is_empty());
            }
            ContractStatus::NotApplicable { reason } => {
                inapplicable += 1;
                assert!(!reason.is_empty());
            }
        }
    }
    assert_eq!(satisfied + unproved + failed + inapplicable, ledger.len());
    assert_eq!(
        satisfied,
        entries.iter().filter(|(_, _, entry)| entry.is_recomputed()).count(),
        "every recomputed row is Satisfied and every Satisfied row is recomputed"
    );
    assert_eq!(satisfied, 10, "the ten recomputed rows");

    // The ten rows that are verified by computation, named — and each one is a
    // `ContractEntry::Recomputed` in the table, not a literal.
    for (receiver, contract) in [
        ("R1", AtlasContract::RebaseEquivariance),
        ("R1", AtlasContract::SourceAccountability),
        ("R3", AtlasContract::DeclarationIndependence),
        ("R3", AtlasContract::EnergyBalance),
        ("R4", AtlasContract::RebaseEquivariance),
        ("R4", AtlasContract::SourceAccountability),
        ("R5", AtlasContract::SourceAccountability),
        ("B7phys", AtlasContract::RebaseEquivariance),
        ("B7phys", AtlasContract::SourceAccountability),
        ("B7phys", AtlasContract::EnergyBalance),
    ] {
        let row = ledger
            .iter()
            .find(|row| row.receiver == receiver && row.contract == contract)
            .unwrap_or_else(|| panic!("{receiver} carries a {contract:?} row"));
        assert!(
            matches!(row.status, ContractStatus::Satisfied(_)),
            "{receiver} {contract:?} is verified by computation, got {:?}",
            row.status
        );
        let entry = entries
            .iter()
            .find(|(name, kind, _)| *name == receiver && *kind == contract)
            .map(|(_, _, entry)| entry)
            .expect("the entry stands");
        assert!(entry.is_recomputed());
    }

    // R5's rebase equivariance **fails**, and the ledger says so rather than omitting the row:
    // the projected writhe is provably not projection-invariant.
    let writhe = ledger
        .iter()
        .find(|row| row.receiver == "R5" && row.contract == AtlasContract::RebaseEquivariance)
        .expect("R5 carries a rebase row");
    assert!(matches!(writhe.status, ContractStatus::Failed { .. }));

    // Nothing claims the gluing law with interface coupling anywhere.
    for row in ledger
        .iter()
        .filter(|row| row.contract == AtlasContract::GluingWithInterfaceCoupling)
    {
        assert!(
            matches!(row.status, ContractStatus::Unproved { .. }),
            "{} must not claim the gluing contract",
            row.receiver
        );
    }
    for row in &ledger {
        println!("contract ledger | {} | {:?} | {:?}", row.receiver, row.contract, row.status);
    }
}

/// **R5's source-accountability witness really runs.** The row is the return of
/// [`verify_r5_source_accountability`], which takes a persistence reading on synthetic exact
/// material and runs [`crate::topological_receiver::grade_zero_agreement`] on it; and the witness
/// text is true of the production path, because
/// [`crate::topological_receiver::persistence`] runs the same agreement before returning any
/// reading at all.
#[test]
fn the_r5_source_accountability_row_runs_a_reading_and_the_production_path_enforces_it() {
    let row = contract_ledger()
        .into_iter()
        .find(|row| row.receiver == "R5" && row.contract == AtlasContract::SourceAccountability)
        .expect("R5 carries a source-accountability row");
    let witness = row.status.witness().expect("the row is Satisfied");
    assert!(
        witness.contains("grade_zero_agreement"),
        "the witness names the cross-check it ran: {witness}"
    );

    // The production path itself: a reading whose grade-zero routes would disagree never leaves
    // `persistence`. The forged-reading route is exercised in
    // `topological_receiver::tests::a_grade_zero_reading_that_disagrees_with_the_communities_is_refused`;
    // here the point is that the honest path runs the check at all, which it does by returning the
    // agreement beside the reading.
    let mut positions = BTreeMap::new();
    let mut component_of = BTreeMap::new();
    for (at, (x, y)) in [(0i64, 0i64), (2, 0), (1, 2), (9, 0), (11, 0), (10, 2)]
        .into_iter()
        .enumerate()
    {
        let id = ConstraintVertexId(at as u64 + 1);
        positions.insert(
            id,
            CoordinateBox3::point(
                Rat::from_integer(BigInt::from(x)),
                Rat::from_integer(BigInt::from(y)),
                Rat::zero(),
            ),
        );
        component_of.insert(id, ConstraintComponentId(if at < 3 { 1 } else { 2 }));
    }
    let filtration = ApertureFiltration::found(
        "atlas|r5|accountability",
        EventId(1),
        &positions,
        &component_of,
        Rat::from_integer(BigInt::from(200)),
        2,
        4096,
    )
    .expect("the filtration stands");
    let order = FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound)
        .expect("the lower-bound order is admissible");
    let (reading, agreement) = persistence_with_grade_zero_agreement(
        &filtration,
        &order,
        &Coefficients::Rational,
        1_000_000,
    )
    .expect("the reduction returns and the two grade-zero routes agree");
    assert_eq!(agreement.merge_values.len(), reading.pairs_at_grade(0).len() - agreement.standing);
    for pair in &reading.pairs {
        assert!(filtration.complex.cell(pair.birth_cell).is_ok());
        assert_eq!(pair.death_cell.is_some(), pair.death_value.is_some());
    }
}

// -------------------------------------------------------------------------------------------
// hostile input to the separating search
// -------------------------------------------------------------------------------------------

/// A declared class cannot size the pair scan: the declaration is checked against the ceiling and
/// the pair count is formed with checked arithmetic before any pair is formed.
#[test]
fn a_hostile_declared_class_is_refused_before_the_scan() {
    let class = vec![exact_matrix(&[&[0, 1], &[0, 0]])];
    let atlas = full_probe_atlas(&class, 1);
    let too_wide = vec![0u32; DECLARED_CLASS_CEILING + 1];
    let refusal = atlas
        .is_separating(&too_wide, 1)
        .expect_err("a class past the ceiling is refused");
    assert_eq!(
        refusal,
        AtlasRefusal::DeclaredClassTooWide {
            declared: DECLARED_CLASS_CEILING + 1,
            ceiling: DECLARED_CLASS_CEILING,
        }
    );
    // A repeated member is not an inequivalence, so it is not a pair.
    match atlas
        .is_separating(&[0u32, 0, 0], 1)
        .expect("the search returns")
    {
        SeparatingVerdict::Separating { pairs_checked, .. } => assert_eq!(pairs_checked, 0),
        other => panic!("a repeated member is not a pair, got {other:?}"),
    }
}

/// A chart that does not read both occurrences separates nothing and is not counted as read.
#[test]
fn a_chart_that_reads_only_one_occurrence_separates_nothing() {
    let mut atlas: ReceiverAtlas<u32, Rat, ()> =
        ReceiverAtlas::found("holonics.receiver_atlas.partial.v1");
    atlas.admit(LocalChart::founded(
        "reads-only-the-first",
        vec![(0u32, Rat::one())],
        None,
    ));
    match atlas.separate(&0u32, &1u32, 0) {
        SeparationOutcome::IndistinguishableToThisAtlas { charts_read, .. } => {
            assert!(charts_read.is_empty());
        }
        other => panic!("a one-sided chart separates nothing, got {other:?}"),
    }
    assert_eq!(atlas.chart_time("reads-only-the-first"), Some(0));
    assert_eq!(atlas.chart_time("absent"), None);
}

// ===========================================================================================
// The M5 measurement: width of the R1 chord response over the RBX1 family, and which receiver
// separates which presentation.
// ===========================================================================================

use std::path::{Path, PathBuf};

use crate::causal_chord::{NetworkForm, elastic_network};
use crate::receiver_release::{
    CompatibleFamily, DiameterNorm, ExactFace, Reading, WidthRefusal, width_enumerated,
};

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The RBX1 chain is the one component present in all three presentations.
const RBX1_RESIDUES: usize = 108;
/// The residue window, declared here and not inferred. It is the same five-residue window
/// `causal_chord::the_causal_chord_measures_one_m5_presentation` measures, so the two readings are
/// comparable.
const M5_WINDOW: usize = 5;
/// Eight angstroms, squared.
const M5_CONTACT_SQUARED: i64 = 64;
/// The declared rational probe point of the chord response. `A = −JᵀJ` is negative semidefinite,
/// so every eigenvalue is `≤ 0` and `s = 1` is never a pole: the reading is total on this family
/// by the receiver's own algebra and not by luck.
const M5_PROBE_POINT: i64 = 1;

/// The three presentations of the M5 release, in the order the plan names them.
const M5_PRESENTATIONS: [(&str, &str); 3] = [
    ("designed", "designed-free-rbx1.cif"),
    ("free-prediction", "ptxv2-free-rbx1-seed2.cif"),
    ("cul1-bound-prediction", "ptxv2-cul1-rbx1-seed0.cif"),
];

/// One deposited decimal, exactly: the token is a rational and is used as one.
fn m5_decimal(token: &str) -> Result<Rat, String> {
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
    let numerator = digits.parse::<BigInt>().map_err(|error| error.to_string())?;
    let denominator = BigInt::from(10_u8).pow(fraction.len() as u32);
    let value = Rat::new(numerator, denominator);
    Ok(if negative { -value } else { value })
}

/// The alpha carbons of every chain, in residue order, as exact rational places.
fn m5_alpha_carbons(path: &Path) -> Result<BTreeMap<String, Vec<Vec<Rat>>>, String> {
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
        let mut place = Vec::with_capacity(3);
        for axis in [x, y, z] {
            place.push(m5_decimal(entry[axis])?);
        }
        chains.entry(entry[chain].to_owned()).or_default().push(place);
    }
    Ok(chains)
}

fn m5_squared_distance(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter().zip(right).fold(Rat::zero(), |sum, (a, b)| {
        let difference = a - b;
        sum + &difference * &difference
    })
}

/// One presentation's declared window, as an exact configuration and a declared contact set.
fn m5_window(
    lineage: &str,
    path: &Path,
) -> Result<(RigidityJacobian, Vec<(usize, usize)>), String> {
    let chains = m5_alpha_carbons(path)?;
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
    let window = &rbx1[0][..M5_WINDOW];
    let configuration = ExactConfiguration::declared(
        3,
        window
            .iter()
            .enumerate()
            .map(|(at, place)| (ConstraintVertexId(at as u64 + 1), place.clone())),
    )
    .map_err(|error| error.to_string())?;
    let aperture = Rat::from_integer(BigInt::from(M5_CONTACT_SQUARED));
    let mut constraints = BTreeMap::new();
    let mut contacts = Vec::new();
    for lower in 0..M5_WINDOW {
        for upper in (lower + 1)..M5_WINDOW {
            let backbone = upper == lower + 1;
            if !backbone && m5_squared_distance(&window[lower], &window[upper]) > aperture {
                continue;
            }
            let (edge, _) = ConstraintEdge::new(
                ConstraintVertexId(lower as u64 + 1),
                ConstraintVertexId(upper as u64 + 1),
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
            contacts.push((lower, upper));
        }
    }
    let jacobian = RigidityJacobian::found(lineage, &configuration, &constraints)
        .map_err(|error| error.to_string())?;
    Ok((jacobian, contacts))
}

/// The four receiver readings of one presentation, exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
struct M5Readings {
    /// R1: the exact rational value of the reduced chord response `H(s₀)` at the declared probe
    /// point, through the overdamped elastic network `A = −JᵀJ`.
    chord_response: Rat,
    /// R3: the characteristic polynomial of the grade-0 Hodge Laplacian of the contact complex
    /// under the unit metric.
    hodge_grade_zero: Vec<Rat>,
    /// R4: `(rank J, dim ker J, dim ker Jᵀ)`.
    rigidity: (usize, usize, usize),
    /// R5: the contact population and the integral Betti numbers of the contact complex.
    topology: (usize, Vec<usize>),
}

fn m5_readings(lineage: &str, jacobian: &RigidityJacobian, contacts: &[(usize, usize)]) -> M5Readings {
    let rigidity = rigidity_reading(jacobian).expect("the rigidity reading returns");
    let network = elastic_network(
        format!("{lineage}|window{M5_WINDOW}|-JtJ"),
        &jacobian.matrix,
        NetworkForm::OverdampedRelaxation,
        0,
        3 * (M5_WINDOW - 1),
    )
    .expect("the network returns");
    let transfer = transfer_function(&network).expect("the transfer object returns");
    let entry = transfer.entry(0, 0).expect("the single declared probe/readout pair");
    let probe = Rat::from_integer(BigInt::from(M5_PROBE_POINT));
    let denominator = entry.reduced_denominator.evaluate(&probe);
    assert!(
        !denominator.is_zero(),
        "s = {M5_PROBE_POINT} is not a pole of a negative semidefinite network"
    );
    let chord_response = entry.reduced_numerator.evaluate(&probe) / denominator;

    let built = graph_complex(M5_WINDOW, contacts);
    let operator = HodgeOperator::found(
        lineage,
        &built.complex,
        &MetricDeclaration::unit(format!("{lineage}|unit")),
        &BoundaryCondition::Free,
    )
    .expect("the Hodge operator founds");
    let hodge_grade_zero = operator
        .laplacian(0)
        .expect("the grade-0 Laplacian")
        .characteristic_polynomial()
        .expect("its exact characteristic polynomial")
        .coefficients()
        .to_vec();
    let betti = (0..=1u32)
        .map(|grade| {
            hodge_reading(&operator, grade)
                .expect("the reading")
                .betti
        })
        .collect::<Vec<_>>();

    M5Readings {
        chord_response,
        hodge_grade_zero,
        rigidity: (
            rigidity.rank,
            rigidity.motion_dimension,
            rigidity.self_stress_dimension,
        ),
        topology: (contacts.len(), betti),
    }
}

/// The chord response as a width reading over the three-presentation family.
#[derive(Clone, Debug)]
struct ChordResponseReading;

impl Reading for ChordResponseReading {
    fn name(&self) -> &str {
        "R1|chord-response"
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        Ok(ExactFace::Vector(state.to_vec()))
    }
}

/// Assemble the four-chart receiver atlas over the three presentations, one chart per receiver.
fn m5_atlas(readings: &[(u32, M5Readings)]) -> ReceiverAtlas<u32, String, ()> {
    let mut atlas = ReceiverAtlas::found("holonics.receiver_atlas.m5-rbx1.v1");
    atlas.admit_at(
        LocalChart::founded(
            "R1|chord-response",
            readings
                .iter()
                .map(|(id, reading)| (*id, reading.chord_response.to_string())),
            None,
        ),
        0,
    );
    atlas.admit_at(
        LocalChart::founded(
            "R3|hodge-grade-zero",
            readings.iter().map(|(id, reading)| {
                (
                    *id,
                    reading
                        .hodge_grade_zero
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(","),
                )
            }),
            None,
        ),
        0,
    );
    atlas.admit_at(
        LocalChart::founded(
            "R4|maxwell",
            readings
                .iter()
                .map(|(id, reading)| (*id, format!("{:?}", reading.rigidity))),
            None,
        ),
        0,
    );
    atlas.admit_at(
        LocalChart::founded(
            "R5|contacts-and-betti",
            readings
                .iter()
                .map(|(id, reading)| (*id, format!("{:?}", reading.topology))),
            None,
        ),
        0,
    );
    atlas
}

/// **The M5 measurement.**
///
/// The width of the R1 chord response over the designed-versus-predicted RBX1 family, and whether
/// the three presentations are separated by each receiver **alone** and by the atlas.
///
/// `#[ignore]`d because it is a measurement, not a law: it reads three authenticated mmCIF
/// presentations off disk and runs three exact fifteen-coordinate Faddeev–LeVerrier recurrences
/// over rationals. **Absent the release this test refuses** rather than reporting success.
/// The synthetic twin below runs by default and exercises exactly the same pipeline.
///
/// Run it with
/// `cargo test -p holonic-engine --lib receiver_atlas::tests::the_m5_rbx1_family_measures -- --ignored --nocapture`.
#[test]
#[ignore = "an exact measurement on the authenticated M5 release, not a law"]
fn the_m5_rbx1_family_measures_its_width_and_its_separations() {
    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the width and the separations \
         cannot be measured, and this test refuses to report success without measuring them. \
         Place the authenticated release at that path, or set {STRUCTURE_ROOT_ENV} to the \
         directory carrying the three presentations. The synthetic twin \
         the_m5_pipeline_runs_on_a_synthetic_family checks the same pipeline with no fixture.",
        root.display()
    );

    let mut readings = Vec::new();
    for (at, (lineage, file)) in M5_PRESENTATIONS.iter().enumerate() {
        let (jacobian, contacts) = m5_window(lineage, &root.join(file))
            .unwrap_or_else(|error| panic!("{lineage}: {error}"));
        readings.push((at as u32, m5_readings(lineage, &jacobian, &contacts)));
    }

    // The width of the R1 chord response over the family: an exact rational diameter.
    let family = CompatibleFamily::enumerated(
        "m5|rbx1|designed-vs-predicted",
        readings
            .iter()
            .map(|(_, reading)| vec![reading.chord_response.clone()])
            .collect(),
    )
    .expect("three compatible presentations");
    let width = width_enumerated(&ChordResponseReading, &family, DiameterNorm::Supremum)
        .expect("the width returns");

    // Which receiver separates which pair, alone.
    let atlas = m5_atlas(&readings);
    let mut alone: BTreeMap<String, Vec<(u32, u32)>> = BTreeMap::new();
    for left in 0..readings.len() as u32 {
        for right in (left + 1)..readings.len() as u32 {
            for chart in atlas.separating_charts(&left, &right) {
                alone.entry(chart).or_default().push((left, right));
            }
        }
    }
    let verdict = atlas
        .is_separating(&[0u32, 1, 2], 0)
        .expect("the search returns");

    println!(
        "R6/R7 M5 | RBX1 window {M5_WINDOW} residues | probe s = {M5_PROBE_POINT} | \
         chord responses {:?} | width {} | receivers separating each pair {:?} | atlas verdict {:?}",
        readings
            .iter()
            .map(|(_, reading)| reading.chord_response.to_string())
            .collect::<Vec<_>>(),
        width.diameter(),
        alone,
        verdict
    );
    for (at, reading) in &readings {
        println!(
            "  presentation {at} ({}) | R1 H(1) = {} | R3 grade-0 charpoly {:?} | R4 (rank, ker J, \
             ker J^T) = {:?} | R5 (contacts, betti) = {:?}",
            M5_PRESENTATIONS[*at as usize].0,
            reading.chord_response,
            reading
                .hodge_grade_zero
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            reading.rigidity,
            reading.topology
        );
    }

    assert!(
        matches!(verdict, SeparatingVerdict::Separating { .. }),
        "the four-chart atlas separates the three presentations"
    );
    assert!(
        !width.is_zero(),
        "the three presentations do not share one chord response"
    );
}

/// The synthetic twin of the measurement above: no fixture, the same pipeline, and it runs by
/// default so the mechanism is never silently untested.
#[test]
fn the_m5_pipeline_runs_on_a_synthetic_family() {
    // Three five-occurrence configurations in the plane of `z = 0`, differing in one place.
    let family = [
        ("synthetic-a", 0i64),
        ("synthetic-b", 1),
        ("synthetic-c", 2),
    ];
    let mut readings = Vec::new();
    for (at, (lineage, offset)) in family.iter().enumerate() {
        let places = (0..M5_WINDOW)
            .map(|index| {
                vec![
                    rational(index as i64 * 3),
                    rational(if index == M5_WINDOW - 1 { *offset } else { 0 }),
                    Rat::zero(),
                ]
            })
            .collect::<Vec<_>>();
        let configuration = ExactConfiguration::declared(
            3,
            places
                .iter()
                .enumerate()
                .map(|(index, place)| (ConstraintVertexId(index as u64 + 1), place.clone())),
        )
        .expect("a declared configuration");
        let mut constraints = BTreeMap::new();
        let mut contacts = Vec::new();
        for lower in 0..M5_WINDOW - 1 {
            let (edge, _) = ConstraintEdge::new(
                ConstraintVertexId(lower as u64 + 1),
                ConstraintVertexId(lower as u64 + 2),
            )
            .expect("an ascending edge");
            constraints.insert(edge, EdgeProvenance::Polygonal);
            contacts.push((lower, lower + 1));
        }
        let jacobian = RigidityJacobian::found(*lineage, &configuration, &constraints)
            .expect("the Jacobian founds");
        readings.push((at as u32, m5_readings(lineage, &jacobian, &contacts)));
    }

    let compatible = CompatibleFamily::enumerated(
        "synthetic|family",
        readings
            .iter()
            .map(|(_, reading)| vec![reading.chord_response.clone()])
            .collect(),
    )
    .expect("three compatible presentations");
    let width = width_enumerated(&ChordResponseReading, &compatible, DiameterNorm::Supremum)
        .expect("the width returns");
    assert!(!width.is_zero(), "the three synthetic chords differ");

    let atlas = m5_atlas(&readings);
    // R3, R4 and R5 read the same contact complex for all three — same contacts, same Betti
    // numbers, same Laplacian — so **only R1 separates them**, which is the whole point of the
    // atlas: a receiver that reads geometry through a response sees what a combinatorial receiver
    // cannot.
    assert_eq!(
        atlas.separating_charts(&0u32, &1u32),
        vec!["R1|chord-response".to_owned()]
    );
    match atlas
        .is_separating(&[0u32, 1, 2], 0)
        .expect("the search returns")
    {
        SeparatingVerdict::Separating { pairs_checked, .. } => assert_eq!(pairs_checked, 3),
        other => panic!("R1 separates all three, got {other:?}"),
    }
}
