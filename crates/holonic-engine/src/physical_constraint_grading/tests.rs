//! The adapter's tests, and the three receiver demonstrations that are its proof of use.
//!
//! The fixture is one presentation carrying an open class that is not decorative: the two bounding
//! members of its family have *different* homology, so a resolution of the open set is a genuine
//! change of topology and not a bookkeeping detail.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;

use super::*;
use crate::EventId;
use crate::algebraic::GradedCausalComplex;
use crate::exact_linear::ExactRatMatrix;
use crate::lattice_gauge::exact_spectrum;
use crate::physical_constraint_complex::{
    ComponentMaterial, ContactFamily, CoordinateBox3, DistanceAperture, PairUncertainty,
    ResidueMaterial,
};
use crate::rebase_invariants::{PivotRule, invariants_agree, rebase_invariants};
use crate::sheaf_diffusion::{CellularRestriction, ExactCellularSheaf};

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn int(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn point(x: i64, y: i64) -> CoordinateBox3 {
    CoordinateBox3::point(int(x), int(y), Rat::zero())
}

/// One occurrence whose `y` is known only to a band. This is where the open class comes from: a
/// genuine width in the presented position, never a hedge inside the classifier.
fn banded(x: i64) -> CoordinateBox3 {
    CoordinateBox3 {
        x: ExactInterval::point(int(x)),
        y: ExactInterval {
            lower: rat(11, 10),
            upper: rat(3, 2),
        },
        z: ExactInterval::point(Rat::zero()),
    }
}

fn residue(source_ordinal: i32, monomer: &str, position: CoordinateBox3) -> ResidueMaterial {
    ResidueMaterial {
        source_ordinal,
        monomer: monomer.to_owned(),
        position,
    }
}

fn uncertainty(left: u32, right: u32) -> BTreeMap<(u32, u32), PairUncertainty> {
    let mut result = BTreeMap::new();
    for a in 1..=left {
        for b in 1..=right {
            result.insert(
                (a, b),
                PairUncertainty {
                    source_lineage: "exact-testimony".to_owned(),
                    row_given_column_bits: 0x3c00,
                    column_given_row_bits: 0x3c00,
                    row_given_column: ExactInterval::point(int(1)),
                    column_given_row: ExactInterval::point(int(1)),
                    row_given_column_ulp: rat(1, 1024),
                    column_given_row_ulp: rat(1, 1024),
                },
            );
        }
    }
    result
}

fn aperture() -> DistanceAperture {
    DistanceAperture {
        lineage: "squared distance at or below two".to_owned(),
        squared: int(2),
    }
}

fn exact_classes(
    complex: &PhysicalConstraintComplex,
    left: ConstraintComponentId,
    right: ConstraintComponentId,
    aperture: &DistanceAperture,
) -> Vec<ContactClass> {
    let left = complex.component(left).unwrap().vertices.clone();
    let right = complex.component(right).unwrap().vertices.clone();
    left.iter()
        .flat_map(|a| {
            right.iter().map(|b| {
                aperture.classify(
                    &complex.vertices[a]
                        .position
                        .squared_distance(&complex.vertices[b].position),
                )
            })
        })
        .collect::<Vec<_>>()
}

/// Three presented components in one plane, read at squared aperture two.
///
/// ```text
///   c1 = (0, [11/10, 3/2])          c2 = (2, [11/10, 3/2])      component 3, banded
///   b1 = (0, 1) ------------------- b2 = (3, 1)                 component 2, exact
///   a1 = (0, 0) -- a2 = (1, 0) -- a3 = (2, 0) -- a4 = (3, 0)    component 1, exact
/// ```
///
/// Component 1 against component 2 decides every pair: `(a1,b1)`, `(a2,b1)`, `(a3,b2)`, `(a4,b2)`
/// are inside at squared distances 1, 2, 2, 1, and the other four are outside. Component 1 against
/// component 3 decides six pairs outside and leaves exactly two open: `(a1,c1)` and `(a3,c2)`,
/// whose exact squared-distance interval is `[121/100, 9/4]` and straddles `2`.
fn presentation() -> PhysicalConstraintComplex {
    let material = vec![
        ComponentMaterial {
            lineage: "component one".to_owned(),
            residues: vec![
                residue(1, "A", point(0, 0)),
                residue(2, "B", point(1, 0)),
                residue(3, "C", point(2, 0)),
                residue(4, "D", point(3, 0)),
            ],
        },
        ComponentMaterial {
            lineage: "component two".to_owned(),
            residues: vec![residue(1, "E", point(0, 1)), residue(2, "F", point(3, 1))],
        },
        ComponentMaterial {
            lineage: "component three".to_owned(),
            residues: vec![residue(1, "G", banded(0)), residue(2, "H", banded(2))],
        },
    ];
    let mut complex =
        PhysicalConstraintComplex::found("three-component presentation", EventId(7), material)
            .expect("the presentation is nonempty");
    for right in [ConstraintComponentId(2), ConstraintComponentId(3)] {
        let declared = aperture();
        let enacted = exact_classes(&complex, ConstraintComponentId(1), right, &declared);
        complex
            .found_contact_family(
                ConstraintComponentId(1),
                right,
                declared,
                &enacted,
                &uncertainty(4, 2),
            )
            .expect("the recomputation agrees with the enacted classification");
    }
    complex
}

fn class_census(family: &ContactFamily) -> BTreeMap<u8, usize> {
    let mut census = BTreeMap::new();
    for reading in &family.readings {
        *census.entry(reading.class.wire()).or_default() += 1;
    }
    census
}

/// The rank-one constant sheaf: one rational coordinate per cell and the identity along every
/// incidence. Every composite is the identity, so path independence holds and
/// `ExactCellularSheaf::new` accepts.
fn constant_sheaf(graded: &GradedCausalComplex) -> ExactCellularSheaf {
    let stalks = graded
        .cells()
        .keys()
        .map(|cell| (*cell, 1_usize))
        .collect::<BTreeMap<_, _>>();
    let mut restrictions = Vec::new();
    for cell in graded.cells().values() {
        for lower in cell.boundary.support() {
            restrictions.push(CellularRestriction {
                lower,
                upper: cell.id,
                map: ExactRatMatrix::identity(1).expect("a unit stalk"),
            });
        }
    }
    ExactCellularSheaf::new(graded.clone(), stalks, restrictions).expect(
        "the constant rank-one sheaf is path independent and its coboundary squares to zero",
    )
}

fn carrier(map: &ExactRatMatrix) -> ExactRatMatrix {
    map.clone()
}

/// The dimension of `ker Delta_k`, read from the exact rank and never from a tolerance.
fn harmonic_dimension(sheaf: &ExactCellularSheaf, grade: u32) -> usize {
    let laplacian = sheaf
        .hodge_laplacian(grade)
        .expect("the Hodge operator is assembled from the complex's own incidence");
    let extent = laplacian.rows();
    extent - carrier(&laplacian).rank().expect("the rank is exact")
}

// -------------------------------------------------------------------------------------------------
// the open class
// -------------------------------------------------------------------------------------------------

#[test]
fn the_presentation_leaves_exactly_two_contacts_open() {
    let complex = presentation();
    // Inside four, outside four, open none.
    assert_eq!(
        class_census(&complex.contact_families[0]),
        BTreeMap::from([(0, 4), (1, 4)])
    );
    // Outside six, open two.
    assert_eq!(
        class_census(&complex.contact_families[1]),
        BTreeMap::from([(0, 6), (2, 2)])
    );
}

#[test]
fn the_adapter_returns_a_family_and_decides_no_open_contact() {
    let complex = presentation();
    let family = graded_constraint_family(&complex).unwrap();

    assert!(!family.is_determinate());
    assert_eq!(family.open_contacts.len(), 2);
    assert_eq!(family.cardinality(), BigUint::from(4_u8));
    assert!(family.open_subsumed_by_inside.is_empty());

    // The open set is the two cross-component pairs whose exact interval straddles the aperture,
    // and each is retained with the interval that could not be decided.
    assert_eq!(
        family.open_edges(),
        vec![
            ConstraintEdge {
                lower: ConstraintVertexId(1),
                upper: ConstraintVertexId(7),
            },
            ConstraintEdge {
                lower: ConstraintVertexId(3),
                upper: ConstraintVertexId(8),
            },
        ]
    );
    for open in &family.open_contacts {
        assert_eq!(open.aperture_squared, int(2));
        assert_eq!(open.squared_distance.lower, rat(121, 100));
        assert_eq!(open.squared_distance.upper, rat(9, 4));
        assert!(open.squared_distance.lower <= open.aperture_squared);
        assert!(open.squared_distance.upper > open.aperture_squared);
    }
}

#[test]
fn the_refusing_member_reproduces_the_presented_incidence_exactly() {
    let complex = presentation();
    let family = graded_constraint_family(&complex).unwrap();
    let refusing = &family.refusing;

    let presented_one_cells = complex
        .polygonal_edges
        .iter()
        .chain(complex.contact_edges.iter())
        .copied()
        .collect::<BTreeSet<_>>();
    assert_eq!(
        refusing.edge_cells.keys().copied().collect::<BTreeSet<_>>(),
        presented_one_cells
    );
    let presented_two_cells = complex
        .faces
        .values()
        .map(|face| face.vertices)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        refusing.face_cells.keys().copied().collect::<BTreeSet<_>>(),
        presented_two_cells
    );
    assert_eq!(
        refusing.f_vector(),
        BTreeMap::from([(0, 8), (1, 9), (2, 2)])
    );
    assert!(
        refusing
            .resolved_open_cells()
            .expect("the refusing member's two maps agree")
            .is_empty()
    );
    assert_eq!(refusing.resolution.admitted_edges().len(), 0);
    assert_eq!(refusing.resolution.refused_edges().len(), 2);
}

#[test]
fn the_admitting_member_founds_the_open_cells_and_names_them_as_resolved() {
    let complex = presentation();
    let family = graded_constraint_family(&complex).unwrap();
    let admitting = &family.admitting;

    assert_eq!(
        admitting.f_vector(),
        BTreeMap::from([(0, 8), (1, 11), (2, 2)])
    );
    let resolved = admitting
        .resolved_open_cells()
        .expect("the admitting member's two maps agree");
    assert_eq!(resolved.len(), 2);
    for (edge, _) in resolved {
        assert_eq!(
            admitting.edge_provenance[&edge],
            EdgeProvenance::ResolvedOpenContact
        );
    }
    // Nothing that the aperture decided changed provenance.
    assert_eq!(
        admitting
            .edge_provenance
            .values()
            .filter(|provenance| **provenance == EdgeProvenance::AdmittedContact)
            .count(),
        4
    );
    assert_eq!(
        admitting
            .edge_provenance
            .values()
            .filter(|provenance| **provenance == EdgeProvenance::Polygonal)
            .count(),
        5
    );
}

#[test]
fn a_declared_resolution_must_name_every_open_contact_and_nothing_else() {
    let complex = presentation();
    let family = graded_constraint_family(&complex).unwrap();
    let open = family.open_edges();

    let short = OpenResolution::declared([(open[0], true)]);
    assert!(matches!(
        graded_constraint_member(&complex, &OpenContactLaw::Declared(short)),
        Err(ConstraintGradingError::UnresolvedOpenContact(edge)) if edge == open[1]
    ));

    let decided = ConstraintEdge {
        lower: ConstraintVertexId(1),
        upper: ConstraintVertexId(5),
    };
    let wide = OpenResolution::declared([(open[0], true), (open[1], false), (decided, true)]);
    assert!(matches!(
        graded_constraint_member(&complex, &OpenContactLaw::Declared(wide)),
        Err(ConstraintGradingError::ResolutionNamesNonOpenContact(edge)) if edge == decided
    ));
}

#[test]
fn enumeration_refuses_rather_than_exponentiating_quietly() {
    let complex = presentation();
    assert!(matches!(
        enumerate_family(&complex, 3),
        Err(ConstraintGradingError::OpenFamilyTooWide { open: 2, bound: 3 })
    ));
    assert_eq!(enumerate_family(&complex, 4).unwrap().len(), 4);
}

/// A presentation whose open set is `left * right` wide: every residue of component one sits at
/// the exact origin and every residue of component two carries the same `y` band, so every cross
/// pair straddles the aperture and none is decided.
fn wide_open_presentation(left: usize, right: usize) -> PhysicalConstraintComplex {
    let material = vec![
        ComponentMaterial {
            lineage: "left component, every residue at the exact origin".to_owned(),
            residues: (0..left)
                .map(|at| residue(at as i32 + 1, "A", point(0, 0)))
                .collect(),
        },
        ComponentMaterial {
            lineage: "right component, every residue on the same band".to_owned(),
            residues: (0..right)
                .map(|at| residue(at as i32 + 1, "B", banded(0)))
                .collect(),
        },
    ];
    let mut complex = PhysicalConstraintComplex::found(
        "a presentation whose whole cross population is open",
        EventId(11),
        material,
    )
    .expect("the presentation is nonempty");
    let declared = aperture();
    let enacted = exact_classes(
        &complex,
        ConstraintComponentId(1),
        ConstraintComponentId(2),
        &declared,
    );
    assert!(
        enacted.iter().all(|class| *class == ContactClass::Open),
        "the fixture only means anything if every cross pair is genuinely undecided"
    );
    complex
        .found_contact_family(
            ConstraintComponentId(1),
            ConstraintComponentId(2),
            declared,
            &enacted,
            &uncertainty(left as u32, right as u32),
        )
        .expect("the recomputation agrees with the enacted classification");
    complex
}

/// The `width >= usize::BITS` arm of the enumeration guard, which is what keeps `1 << width` from
/// being evaluated at all. Exercised with `usize::MAX` as the bound, so the second disjunct could
/// never refuse: only the short circuit stands between this call and a shift overflow.
#[test]
fn an_open_set_at_least_as_wide_as_a_usize_refuses_before_the_shift_is_taken() {
    let complex = wide_open_presentation(8, 8);
    let (open, subsumed) = open_contacts(&complex).expect("the open set reads");
    assert_eq!(open.len(), usize::BITS as usize, "64 undecided cross pairs");
    assert!(
        subsumed.is_empty(),
        "no aperture decided any of them Inside"
    );

    assert!(matches!(
        enumerate_family(&complex, usize::MAX),
        Err(ConstraintGradingError::OpenFamilyTooWide {
            open: 64,
            bound: usize::MAX
        })
    ));
    assert!(matches!(
        enumerate_family(&complex, 1),
        Err(ConstraintGradingError::OpenFamilyTooWide { open: 64, bound: 1 })
    ));

    // The count itself is never lost to the refusal: the family really does have 2^64 members and
    // says so exactly.
    let family = graded_constraint_family(&complex).expect("the two bounding members are built");
    assert_eq!(family.cardinality(), BigUint::from(1_u8) << 64_usize);
    assert!(!family.is_determinate());
}

/// [`GradedConstraintComplex`] is public and `Deserialize`, so its `edge_provenance` and
/// `edge_cells` can arrive disagreeing. The disagreement is a named refusal, not an index panic.
#[test]
fn a_member_whose_provenance_and_cell_maps_disagree_is_a_typed_refusal() {
    let complex = presentation();
    let family = graded_constraint_family(&complex).unwrap();
    let mut hostile = family.admitting.clone();
    let resolved = hostile
        .resolved_open_cells()
        .expect("the constructed member's maps agree");
    assert_eq!(resolved.len(), 2);

    let (orphaned, _) = resolved[0];
    assert!(hostile.edge_cells.remove(&orphaned).is_some());
    assert_eq!(
        hostile.edge_provenance[&orphaned],
        EdgeProvenance::ResolvedOpenContact,
        "the provenance still names an edge that no longer carries a cell"
    );
    assert!(matches!(
        hostile.resolved_open_cells(),
        Err(ConstraintGradingError::ProvenanceWithoutCell(edge)) if edge == orphaned
    ));

    // The same value reached through the wire, rather than by hand, refuses identically.
    let remounted: GradedConstraintComplex =
        ron::from_str(&ron::to_string(&hostile).expect("the member serializes"))
            .expect("the member remounts");
    assert!(matches!(
        remounted.resolved_open_cells(),
        Err(ConstraintGradingError::ProvenanceWithoutCell(edge)) if edge == orphaned
    ));
}

#[test]
fn boundary_of_boundary_is_zero_for_every_member_of_the_family() {
    let complex = presentation();
    for member in enumerate_family(&complex, 4).unwrap() {
        // `found_cell` refuses a nonzero `∂∂` at every founding, and `validate` re-derives it for
        // every cell already standing. Both are re-run here on the returned body.
        member.complex.validate().unwrap();
        let mut two_cells = 0;
        for cell in member.complex.cells().values() {
            let squared = member.complex.boundary_of_chain(&cell.boundary).unwrap();
            assert!(
                squared.difference_is_zero(),
                "∂∂ is nonzero on {} under resolution {:?}",
                cell.name,
                member.resolution
            );
            if cell.grade == 2 {
                two_cells += 1;
            }
        }
        assert_eq!(two_cells, 2);
    }
}

// -------------------------------------------------------------------------------------------------
// demonstration one: exact homology, Betti numbers and torsion
// -------------------------------------------------------------------------------------------------

/// `rebase_invariants.rs:723` over `:601`'s Smith normal form, reached through the adapter.
///
/// The four members of the family return three distinct Betti vectors, so the open class is not a
/// bookkeeping detail: refusing both open contacts leaves component three detached and the complex
/// carries two pieces and one hole; admitting both attaches it at two non-adjacent occurrences and
/// founds no filling two-cell, so the complex carries one piece and two holes.
///
/// Torsion is empty and provably so: every two-cell is a simplex on three distinct occurrences
/// whose one-faces are distinct one-cells, so no two-cell is attached along a multiple of a cycle
/// and `H_1` is free. The receiver returns that emptiness rather than the test assuming it.
#[test]
fn the_family_reaches_exact_homology_with_torsion() {
    let complex = presentation();
    let members = enumerate_family(&complex, 4).unwrap();
    let mut betti = Vec::new();
    for member in &members {
        let invariants = rebase_invariants(&member.complex, PivotRule::SmallestMagnitude).unwrap();
        assert!(
            invariants.total_torsion().is_empty(),
            "a simplicial contact complex carries no torsion"
        );
        assert_eq!(
            invariants.euler_characteristic(),
            invariants.cell_euler_characteristic()
        );
        // The invariants are a property of the incidence and not of the reduction that read them.
        for rule in PivotRule::ALL {
            let again = rebase_invariants(&member.complex, rule).unwrap();
            assert!(invariants_agree(&invariants, &again));
        }
        betti.push(invariants.betti_vector());
    }

    assert_eq!(
        betti,
        vec![
            vec![2, 1, 0], // refuse both
            vec![1, 1, 0], // admit (a1,c1)
            vec![1, 1, 0], // admit (a3,c2)
            vec![1, 2, 0], // admit both
        ]
    );
    // The two bounding members, with the ranks the Smith normal form actually read.
    let family = graded_constraint_family(&complex).unwrap();
    let refusing = rebase_invariants(&family.refusing.complex, PivotRule::FirstNonzero).unwrap();
    assert_eq!(refusing.cell_euler_characteristic(), 1);
    assert_eq!(refusing.euler_characteristic(), 1);
    assert_eq!(
        refusing
            .grades
            .iter()
            .map(|grade| (
                grade.grade,
                grade.cells,
                grade.boundary_rank,
                grade.filling_rank
            ))
            .collect::<Vec<_>>(),
        vec![(0, 8, 0, 6), (1, 9, 6, 2), (2, 2, 2, 0)]
    );
    let admitting = rebase_invariants(&family.admitting.complex, PivotRule::FirstNonzero).unwrap();
    assert_eq!(admitting.cell_euler_characteristic(), -1);
    assert_eq!(admitting.euler_characteristic(), -1);
    assert_eq!(
        admitting
            .grades
            .iter()
            .map(|grade| (
                grade.grade,
                grade.cells,
                grade.boundary_rank,
                grade.filling_rank
            ))
            .collect::<Vec<_>>(),
        vec![(0, 8, 0, 7), (1, 11, 7, 2), (2, 2, 2, 0)]
    );
}

// -------------------------------------------------------------------------------------------------
// demonstration two: the exact Hodge Laplacian
// -------------------------------------------------------------------------------------------------

/// `sheaf_diffusion.rs:274` coboundary and `:307` Hodge operator, reached through the adapter.
///
/// `ExactCellularSheaf::new` validates on construction: it re-derives `delta_{k+1} delta_k = 0`
/// from the adapter's incidence, so the sheaf existing at all is already a second, independent
/// check of the boundary law.
///
/// The harmonic dimensions are an independent cross-check of demonstration one. Smith normal form
/// reads the homology over `Z` by integer row and column operations; `dim ker Delta_k` reads it
/// over `Q` by exact rank. The two receivers share no code path and agree.
#[test]
fn the_family_reaches_the_exact_hodge_laplacian() {
    let complex = presentation();
    let family = graded_constraint_family(&complex).unwrap();

    let refusing = constant_sheaf(&family.refusing.complex);
    assert_eq!(refusing.coboundary(0).unwrap().rows(), 9);
    assert_eq!(refusing.coboundary(0).unwrap().columns(), 8);
    assert_eq!(refusing.coboundary(1).unwrap().rows(), 2);
    assert_eq!(refusing.coboundary(1).unwrap().columns(), 9);
    assert_eq!(refusing.hodge_laplacian(0).unwrap().rows(), 8);
    assert_eq!(refusing.hodge_laplacian(1).unwrap().rows(), 9);
    assert_eq!(refusing.hodge_laplacian(2).unwrap().rows(), 2);
    assert_eq!(harmonic_dimension(&refusing, 0), 2);
    assert_eq!(harmonic_dimension(&refusing, 1), 1);
    assert_eq!(harmonic_dimension(&refusing, 2), 0);

    let admitting = constant_sheaf(&family.admitting.complex);
    assert_eq!(admitting.hodge_laplacian(0).unwrap().rows(), 8);
    assert_eq!(admitting.hodge_laplacian(1).unwrap().rows(), 11);
    assert_eq!(admitting.hodge_laplacian(2).unwrap().rows(), 2);
    assert_eq!(harmonic_dimension(&admitting, 0), 1);
    assert_eq!(harmonic_dimension(&admitting, 1), 2);
    assert_eq!(harmonic_dimension(&admitting, 2), 0);
}

// -------------------------------------------------------------------------------------------------
// demonstration three: the exact spectrum
// -------------------------------------------------------------------------------------------------

/// `lattice_gauge.rs:1039` exact spectrum, reached through the adapter and the Hodge operator.
///
/// The characteristic polynomial is Faddeev–LeVerrier over exact rationals and the rational
/// eigenvalues come from a complete census, so the multiplicity of zero is the exact harmonic
/// dimension and not an eigenvalue below a threshold. Whatever the census cannot place rationally
/// is returned as a named factor rather than approximated, and the module makes no gap claim: an
/// interval here is a measurement of this operator on this member.
///
/// The refusing member's operators happen to be completely rational at every grade, so the whole
/// spectrum is pinned below. The admitting member's grade-zero operator is not, and its degree-six
/// unresolved factor is returned by name rather than approximated — which is the behaviour being
/// demonstrated, not a shortfall.
#[test]
fn the_family_reaches_the_exact_spectrum() {
    let complex = presentation();
    let family = graded_constraint_family(&complex).unwrap();

    let refusing = constant_sheaf(&family.refusing.complex);
    let zero_grade = exact_spectrum(&carrier(&refusing.hodge_laplacian(0).unwrap())).unwrap();
    assert_eq!(zero_grade.extent, 8);
    assert!(zero_grade.is_completely_rational());
    assert_eq!(zero_grade.accounted(), 8);
    assert_eq!(
        zero_grade.rational_eigenvalues,
        vec![
            (int(0), 2),
            (int(1), 1),
            (int(2), 1),
            (int(3), 2),
            (int(4), 1),
            (int(5), 1),
        ]
    );
    // The zero multiplicity is the harmonic dimension, which is the Betti number.
    assert_eq!(
        zero_grade.rational_eigenvalues[0].1,
        harmonic_dimension(&refusing, 0)
    );

    let one_grade = exact_spectrum(&carrier(&refusing.hodge_laplacian(1).unwrap())).unwrap();
    assert_eq!(one_grade.extent, 9);
    assert!(one_grade.is_completely_rational());
    assert_eq!(
        one_grade.rational_eigenvalues,
        vec![
            (int(0), 1),
            (int(1), 1),
            (int(2), 1),
            (int(3), 4),
            (int(4), 1),
            (int(5), 1),
        ]
    );
    assert_eq!(
        one_grade.rational_eigenvalues[0].1,
        harmonic_dimension(&refusing, 1)
    );

    let two_grade = exact_spectrum(&carrier(&refusing.hodge_laplacian(2).unwrap())).unwrap();
    assert_eq!(two_grade.extent, 2);
    assert_eq!(two_grade.rational_eigenvalues, vec![(int(3), 2)]);
    assert!(
        two_grade
            .rational_eigenvalues
            .iter()
            .all(|(value, _)| !value.is_zero()),
        "the top grade carries no harmonic direction, matching Betti two of zero"
    );

    let admitting = constant_sheaf(&family.admitting.complex);
    let admitting_zero = exact_spectrum(&carrier(&admitting.hodge_laplacian(0).unwrap())).unwrap();
    assert_eq!(admitting_zero.extent, 8);
    assert_eq!(
        admitting_zero.rational_eigenvalues,
        vec![(int(0), 1), (int(4), 1)]
    );
    assert!(!admitting_zero.is_completely_rational());
    assert_eq!(admitting_zero.unresolved.degree(), Some(6));
    assert_eq!(
        admitting_zero.rational_eigenvalues[0].1,
        harmonic_dimension(&admitting, 0)
    );
}

// =============================================================================================
// the within-component (intra-chain) family, the covalent backbone, and the cycle it closes
// =============================================================================================

/// One folded chain of five occurrences. `banded` makes the closing pair's squared distance an
/// interval that straddles the aperture, so the chain's own fold is the `Open` contact.
///
/// At squared aperture three every other within-component pair is decidedly outside:
/// `(1,3) = 13`, `(1,4) = 10`, `(2,4) = 10`, `(2,5) ⊆ [10.21, 11.25]`, `(3,5) ⊆ [16.25, 16.81]`.
fn folded_chain(closing: CoordinateBox3) -> PhysicalConstraintComplex {
    PhysicalConstraintComplex::found(
        "one folded chain",
        EventId(7),
        vec![ComponentMaterial {
            lineage: "chain".to_owned(),
            residues: vec![
                residue(1, "A", point(0, 0)),
                residue(2, "B", point(2, 0)),
                residue(3, "C", point(3, 2)),
                residue(4, "D", point(1, 3)),
                residue(5, "E", closing),
            ],
        }],
    )
    .expect("the chain stands")
}

fn chain_aperture() -> DistanceAperture {
    DistanceAperture {
        lineage: "squared distance at or below three".to_owned(),
        squared: int(3),
    }
}

fn found_within(complex: &mut PhysicalConstraintComplex, separation: u32) {
    let component = ConstraintComponentId(1);
    let aperture = chain_aperture();
    let vertices = complex.component(component).unwrap().vertices.clone();
    let pairs = complex
        .within_component_pairs(component, separation)
        .unwrap();
    let enacted = pairs
        .iter()
        .map(|(left, right)| {
            let a = vertices[*left as usize - 1];
            let b = vertices[*right as usize - 1];
            aperture.classify(
                &complex.vertices[&a]
                    .position
                    .squared_distance(&complex.vertices[&b].position),
            )
        })
        .collect::<Vec<_>>();
    let one = uncertainty(1, 1).get(&(1, 1)).expect("one reading").clone();
    let carrier = pairs
        .iter()
        .map(|pair| (*pair, one.clone()))
        .collect::<BTreeMap<_, _>>();
    complex
        .found_within_component_contact_family(component, separation, aperture, &enacted, &carrier)
        .expect("the within-component family stands");
}

/// **The intra-chain contact is the whole difference between `b₁ = 0` and `b₁ = 1`.**
///
/// The covalent chain steps stand in both members. The fold is `Open`, so one member refuses it
/// and reads a path, and one admits it and reads a cycle of `j − i + 1 = 5` one-cells. No default
/// picks between them.
#[test]
fn an_open_intra_chain_contact_is_the_difference_between_a_path_and_a_cycle() {
    let mut complex = folded_chain(banded(-1));
    found_within(&mut complex, 2);
    let family = graded_constraint_family(&complex).expect("the family stands");

    assert_eq!(family.open_contacts.len(), 1, "the fold, and nothing else");
    assert_eq!(family.cardinality(), BigUint::from(2_u8));
    assert!(!family.is_determinate());
    let open = &family.open_contacts[0];
    assert_eq!(open.left_component, ConstraintComponentId(1));
    assert_eq!(open.right_component, ConstraintComponentId(1));
    assert_eq!((open.left_ordinal, open.right_ordinal), (1, 5));

    // The covalent class stands in both members, unconditionally.
    for member in [&family.refusing, &family.admitting] {
        let covalent = member
            .edge_provenance
            .values()
            .filter(|provenance| provenance.is_covalent_backbone())
            .count();
        assert_eq!(covalent, 4, "four chain steps over five occurrences");
        assert_eq!(member.vertex_cells.len(), 5);
        assert!(
            member.face_cells.is_empty(),
            "one contact founds no triangle"
        );
    }
    assert_eq!(family.refusing.edge_cells.len(), 4);
    assert_eq!(
        family.admitting.edge_cells.len(),
        5,
        "the cycle has j − i + 1 = 5 one-cells: four covalent steps and one contact"
    );
    assert_eq!(
        family.admitting.edge_provenance[&open.edge],
        EdgeProvenance::ResolvedOpenContact
    );
    assert!(family.admitting.edge_provenance[&open.edge].is_contact());

    let refusing = rebase_invariants(&family.refusing.complex, PivotRule::FirstNonzero).unwrap();
    let admitting = rebase_invariants(&family.admitting.complex, PivotRule::FirstNonzero).unwrap();
    assert_eq!(refusing.betti_vector(), vec![1, 0], "a path");
    assert_eq!(
        admitting.betti_vector(),
        vec![1, 1],
        "backbone plus one contact is one cycle"
    );
    for rule in PivotRule::ALL {
        let again = rebase_invariants(&family.admitting.complex, rule).unwrap();
        assert!(invariants_agree(&admitting, &again));
    }
}

/// The same chain with the fold decided `Inside`: the family is a singleton and `b₁ = 1` stands
/// with no resolution at all.
#[test]
fn a_decided_intra_chain_contact_closes_the_cycle_in_a_singleton_family() {
    let mut complex = folded_chain(point(-1, 1));
    found_within(&mut complex, 2);
    let family = graded_constraint_family(&complex).expect("the family stands");
    assert!(family.is_determinate());
    assert_eq!(family.cardinality(), BigUint::from(1_u8));
    assert_eq!(family.refusing.edge_cells.len(), 5);
    assert_eq!(
        family
            .refusing
            .edge_provenance
            .values()
            .filter(|provenance| provenance.is_contact())
            .count(),
        1
    );
    let invariants = rebase_invariants(&family.refusing.complex, PivotRule::FirstNonzero).unwrap();
    assert_eq!(invariants.betti_vector(), vec![1, 1]);
}

/// A within-component family whose junction meets its own chain step founds no triangle — and a
/// pair of intra-chain contacts sharing a step does found one.
#[test]
fn the_within_component_two_cell_law_skips_its_own_step_endpoints() {
    // Five occurrences where 1 is within the aperture of both 3 and 4, so the step [3,4] and the
    // junction 1 found one two-cell, and no collapsed triple is ever reached.
    let mut complex = PhysicalConstraintComplex::found(
        "one tight chain",
        EventId(11),
        vec![ComponentMaterial {
            lineage: "chain".to_owned(),
            residues: vec![
                residue(1, "A", point(0, 0)),
                residue(2, "B", point(3, 0)),
                residue(3, "C", point(1, 1)),
                residue(4, "D", point(0, 1)),
                residue(5, "E", point(4, 4)),
            ],
        }],
    )
    .unwrap();
    found_within(&mut complex, 2);
    let family = complex
        .within_component_family(ConstraintComponentId(1), 2)
        .unwrap();
    let inside = family
        .readings
        .iter()
        .filter(|reading| reading.class == ContactClass::Inside)
        .map(|reading| (reading.left_ordinal, reading.right_ordinal))
        .collect::<Vec<_>>();
    assert_eq!(inside, vec![(1, 3), (1, 4)]);
    assert_eq!(complex.faces.len(), 1, "step [3,4] with junction 1");
    let member = graded_constraint_member(&complex, &OpenContactLaw::RefuseEveryOpen).unwrap();
    assert_eq!(member.face_cells.len(), 1);
    assert_eq!(
        member.face_cells.keys().next().unwrap(),
        &[
            ConstraintVertexId(3),
            ConstraintVertexId(4),
            ConstraintVertexId(1)
        ]
    );
    member.complex.validate().expect("∂∘∂ = 0 on the member");
}

/// **The consumers gain the intra-chain family through the entry points they already have.**
///
/// `rigidity_family` and `hodge_family` take the presented complex and go through
/// `graded_constraint_family`, so a within-component family founded on that complex is in the
/// member's 1-skeleton with no change to either receiver's signature.
#[test]
fn the_within_component_family_reaches_the_rigidity_and_hodge_receivers_unchanged() {
    use crate::hodge_receiver::{BoundaryLaw, MetricDeclaration, hodge_family};
    use crate::rigidity_receiver::{ExactConfiguration, rigidity_family};

    let mut complex = folded_chain(point(-1, 1));
    let configuration = ExactConfiguration::from_presented(&complex).unwrap();

    let before = rigidity_family(&complex, &configuration).unwrap();
    assert_eq!(
        before.refusing.constraint_count, 4,
        "the chain steps alone"
    );
    let hodge_before = hodge_family(
        &complex,
        &MetricDeclaration::unit("unit"),
        &BoundaryLaw::Free,
        1,
        64,
    )
    .unwrap();
    assert_eq!(hodge_before.refusing.cells, 4);

    found_within(&mut complex, 2);

    let after = rigidity_family(&complex, &configuration).unwrap();
    assert_eq!(
        after.refusing.constraint_count, 5,
        "the intra-chain contact is a constraint of the rigidity receiver"
    );
    assert!(
        after.refusing.motion_dimension < before.refusing.motion_dimension,
        "closing the chain removes a motion"
    );
    let hodge_after = hodge_family(
        &complex,
        &MetricDeclaration::unit("unit"),
        &BoundaryLaw::Free,
        1,
        64,
    )
    .unwrap();
    assert_eq!(hodge_after.refusing.cells, 5);
    assert_eq!(
        hodge_after.refusing.harmonic_dimension, 1,
        "the closed chain carries one harmonic 1-form, and it had none"
    );
    assert_eq!(hodge_before.refusing.harmonic_dimension, 0);
}

#[test]
fn a_remounted_member_with_a_provenance_without_its_edge_is_refused() {
    let complex = folded_chain(point(-1, 1));
    let mut member = graded_constraint_member(&complex, &OpenContactLaw::RefuseEveryOpen)
        .expect("the refusing member founds");
    let edge = *member
        .edge_provenance
        .keys()
        .next()
        .expect("the chain has an edge");
    member.edge_cells.remove(&edge);
    assert!(matches!(
        member.validate_structure(),
        Err(ConstraintGradingError::ProvenanceWithoutCell(found)) if found == edge
    ));
}

#[test]
fn dropping_both_edge_maps_cannot_change_the_complex_seen_by_rigidity() {
    let complex = folded_chain(point(-1, 1));
    let mut member = graded_constraint_member(&complex, &OpenContactLaw::RefuseEveryOpen).unwrap();
    member.validate_structure().unwrap();
    let edge = *member.edge_cells.keys().next().unwrap();
    member.edge_cells.remove(&edge);
    member.edge_provenance.remove(&edge);
    // Hodge would still see this edge in `complex`, while rigidity formerly read just the map.
    assert!(matches!(member.validate_structure(), Err(ConstraintGradingError::MemberInvariant(_))));
}
