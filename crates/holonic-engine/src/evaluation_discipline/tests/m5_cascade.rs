//! **B10 — one real cost cascade, measured end to end on the M5 material, CPU only.**
//!
//! [definition] The cascade is four stages over the 10,368 addressed `binder × RBX1` residue pairs
//! of the designed M5 structure:
//!
//! 1. **the cheap coarse contact filter** — the alpha-carbon receiver at the *inflated* aperture;
//! 2. **the all-atom contact complex** — every atom pair of a surviving residue pair at 8 Å;
//! 3. **the rigidity receiver** — `J_eta`, its kernel and its cokernel over the surviving interface;
//! 4. **the Hodge spectrum** — grade zero over the same interface.
//!
//! The cheap stage's discard is **certified**: `Foundation/GrainRestriction.lean::coarse_distance_le_fine_aperture_add_radii`
//! bounds the coarse (alpha-carbon) separation of two residues by the fine aperture plus their two
//! measured grain radii, so a coarse reading *outside* the inflated aperture certifies that no atom
//! pair of those two residues is inside the fine one. The inflated aperture is computed here from
//! the **measured** maximum grain radius of this structure through
//! `grain_tower::certified_coarse_aperture_squared`; it is never a constant.
//!
//! At the **equal** aperture the same discard is unsound, and this measurement counts by how much:
//! the plan's B0 reading — 1,096 of 1,397 fine contacts invisible to the coarse receiver at an
//! equal 8 Å aperture — is the same fact at a different scope, and the number this test prints is
//! its residue-pair form on the designed structure alone.
//!
//! The measurement is `#[ignore]`d because it reads the authenticated release and runs the
//! expensive receivers. Run it with:
//!
//! ```text
//! PATH=/opt/cuda/bin:$PATH cargo test -p holonic-engine --lib \
//!   evaluation_discipline::tests::m5_cascade::the_m5_cost_cascade_is_measured_end_to_end \
//!   -- --ignored --nocapture --test-threads=1
//! ```
//!
//! It is CPU only: no CUDA path is touched.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use holonics::geometry::Rat;

use super::super::*;
use crate::EventId;
use crate::grain_tower::{certified_coarse_aperture_squared, rational_root_upper_bound};
use crate::hodge_receiver::{BoundaryLaw, MetricDeclaration, hodge_member};
use holonics::exact_value::ExactInterval;
use crate::physical_constraint_complex::{
    ComponentMaterial, ConstraintComponentId, ContactClass, CoordinateBox3, DistanceAperture,
    PairUncertainty, ResidueMaterial,
};
use crate::physical_constraint_grading::OpenContactLaw;
use crate::physical_intake::mmcif::StructurePresentation;
use crate::physical_intake::{PresentedFamily, found_constraint_complex};
use crate::physical_occurrence::fixture;
use crate::rigidity_receiver::{ExactConfiguration, rigidity_member};

/// **The uncertainty every addressed pair of the interface complex is founded with.**
///
/// [definition] The designed M5 structure carries **no uncertainty array at all** — B3 records
/// that, and its environment index says so with a stated ground. `found_contact_family` requires one
/// reading per addressed pair, so this declares a point reading at `1` for every pair with its
/// source lineage naming the declaration rather than a predictor. It is testimony that no predictor
/// uncertainty was presented, never a fabricated confidence: no stage of this cascade reads it.
fn declared_absent_uncertainty(left: usize, right: usize) -> BTreeMap<(u32, u32), PairUncertainty> {
    let one = Rat::from_integer(BigInt::from(1));
    let ulp = Rat::new(BigInt::from(1), BigInt::from(1024));
    let mut table = BTreeMap::new();
    for row in 1..=left as u32 {
        for column in 1..=right as u32 {
            table.insert(
                (row, column),
                PairUncertainty {
                    source_lineage: "declared by the M5 cascade measurement: the designed \
                                     structure presents no uncertainty array, and no stage of this \
                                     cascade reads this coordinate"
                        .to_owned(),
                    row_given_column_bits: 0x3c00,
                    column_given_row_bits: 0x3c00,
                    row_given_column: ExactInterval::point(one.clone()),
                    column_given_row: ExactInterval::point(one.clone()),
                    row_given_column_ulp: ulp.clone(),
                    column_given_row_ulp: ulp.clone(),
                },
            );
        }
    }
    table
}

/// The exact squared-distance aperture of the fine (all-atom) receiver: 8 angstroms.
fn fine_aperture() -> DistanceAperture {
    fixture::eight_angstrom_aperture()
}

/// One residue's atom positions on the resident decimal grain, with its alpha carbon marked.
///
/// [definition] Two alpha-carbon readings are carried because they answer two different questions.
/// `alpha_carbon` is the **enclosure** `projected_box` returns — the coordinate's own last written
/// decimal place — and it is what the contact law is read against, so an undecided reading stays
/// undecided. `alpha_carbon_centre` is the **declared centre** `DecimalToken::exact_centre`
/// returns, an exact rational point, and it is what the rigidity and Hodge stages read: a
/// coordinate box with width is a precision question and not a place, and
/// `rigidity_receiver::ExactConfiguration::from_presented` refuses one by name rather than
/// collapsing it to a midpoint. The B7 measurement of these same receivers on the M5 material read
/// the declared centres for exactly this reason.
struct ResidueAtoms {
    ordinal: i32,
    monomer: String,
    alpha_carbon: CoordinateBox3,
    alpha_carbon_centre: CoordinateBox3,
    atoms: Vec<CoordinateBox3>,
}

/// Read one chain's residues as atom populations on the resident grain.
fn residue_atoms(chain: &crate::physical_intake::mmcif::ChainOccurrence) -> Vec<ResidueAtoms> {
    chain
        .residues
        .iter()
        .filter_map(|residue| {
            let mut alpha_carbon = None;
            let mut atoms = Vec::with_capacity(residue.atoms.len());
            for atom in &residue.atoms {
                let position = atom
                    .projected_box(fixture::RESIDENT_DECIMAL_PLACES)
                    .expect("a deposited coordinate projects onto the resident grain");
                if atom.label == fixture::REPRESENTATIVE {
                    let centre = |token: &crate::physical_intake::mmcif::DecimalToken| {
                        token.exact_centre().expect("a deposited decimal token")
                    };
                    alpha_carbon = Some((
                        position.clone(),
                        CoordinateBox3::point(centre(&atom.x), centre(&atom.y), centre(&atom.z)),
                    ));
                }
                atoms.push(position);
            }
            alpha_carbon.map(|(alpha_carbon, alpha_carbon_centre)| ResidueAtoms {
                ordinal: residue.source_ordinal,
                monomer: residue.monomer.clone(),
                alpha_carbon,
                alpha_carbon_centre,
                atoms,
            })
        })
        .collect()
}

/// The exact maximum grain radius of a residue population: the largest distance from a residue's
/// alpha carbon to one of its own atoms, as an exact rational upper bound on the square root of the
/// largest squared distance actually measured.
fn measured_grain_radius(residues: &[ResidueAtoms]) -> Rat {
    let mut largest_squared = Rat::from_integer(BigInt::from(0));
    for residue in residues {
        for atom in &residue.atoms {
            let separation = residue.alpha_carbon.squared_distance(atom);
            if separation.upper > largest_squared {
                largest_squared = separation.upper;
            }
        }
    }
    rational_root_upper_bound(&largest_squared, &BigUint::from(1_000_000_u32))
        .expect("a nonnegative square with a nonzero denominator")
}

/// Whether two residues carry an all-atom contact at the fine aperture, and how many atom pairs
/// were classified to decide it. Every atom pair is read: the count is the exact work.
fn all_atom_contact(
    left: &ResidueAtoms,
    right: &ResidueAtoms,
    aperture: &DistanceAperture,
) -> (bool, usize) {
    let mut carries = false;
    let mut work = 0usize;
    for a in &left.atoms {
        for b in &right.atoms {
            work += 1;
            if aperture.classify(&a.squared_distance(b)) != ContactClass::Outside {
                carries = true;
            }
        }
    }
    (carries, work)
}

/// **The measured cascade.** Per-stage exact work counts and wall times, the soundness of the
/// certified cheap discard, the unsoundness of the same discard at the equal aperture, and the
/// cumulative cost saved against running the expensive receiver on everything.
#[test]
#[ignore = "reads the authenticated M5 release and runs the expensive receivers; CPU only"]
fn the_m5_cost_cascade_is_measured_end_to_end() {
    let root = fixture::structure_root();
    assert!(
        root.is_dir(),
        "{}",
        fixture::absent_structure_root_message(
            &root,
            "The synthetic laws of this module are checked by the other tests in this file, which \
             depend on no file."
        )
    );

    let end_to_end = Stopwatch::start();
    let mut recorder = RunRecorder::start(
        "holonic-engine::evaluation_discipline::m5_cascade",
        "CPU only; exact rational contact law; no CUDA path is touched",
        "exact BigInt/BigRational throughout on a 10^7 resident decimal grain; every aperture, \
         radius and squared distance is a holonics::geometry::Rat and no float decides anything",
    )
    .expect("a stated recorder");

    // ---------------------------------------------------------------------------------------
    // Setup: the all-atom intake of the designed structure.
    // ---------------------------------------------------------------------------------------
    let setup = Stopwatch::start();
    let designed = StructurePresentation::read(&root.join("designed-free-rbx1.cif"))
        .expect("the designed structure reads");
    let binder = designed
        .chain_with_residue_count(96)
        .expect("the 96-residue binder");
    let target = designed
        .chain_with_residue_count(108)
        .expect("the 108-residue RBX1");
    let left = residue_atoms(binder);
    let right = residue_atoms(target);
    let left_atoms: usize = left.iter().map(|residue| residue.atoms.len()).sum();
    let right_atoms: usize = right.iter().map(|residue| residue.atoms.len()).sum();

    let fine = fine_aperture();
    // The certified inflation, from the *measured* grain radii of this structure.
    let radius = measured_grain_radius(&left).max(measured_grain_radius(&right));
    let fine_root = rational_root_upper_bound(&fine.squared, &BigUint::from(1_000_000_u32))
        .expect("the fine aperture has a rational root bound");
    let inflated = DistanceAperture {
        lineage: "the coarse alpha-carbon receiver at the certified inflated aperture \
                  (√64 + 2·r_max)², with r_max the measured maximum grain radius of this structure"
            .to_owned(),
        squared: certified_coarse_aperture_squared(&fine_root, &radius, &radius),
    };
    let setup_ns = recorder
        .record(ClockName::Setup, &setup)
        .expect("a fresh clock");

    // ---------------------------------------------------------------------------------------
    // Stage 1 — the cheap coarse contact filter, at the inflated aperture.
    // ---------------------------------------------------------------------------------------
    let resident = Stopwatch::start();
    let mut stage_one_work = 0usize;
    let mut survivors: Vec<(usize, usize)> = Vec::new();
    let mut discarded: Vec<(usize, usize)> = Vec::new();
    let mut equal_aperture_discarded: Vec<(usize, usize)> = Vec::new();
    for (at, a) in left.iter().enumerate() {
        for (bt, b) in right.iter().enumerate() {
            stage_one_work += 1;
            let coarse = a.alpha_carbon.squared_distance(&b.alpha_carbon);
            if inflated.classify(&coarse) == ContactClass::Outside {
                discarded.push((at, bt));
            } else {
                survivors.push((at, bt));
            }
            // The same cheap reading at the EQUAL aperture, which is the unsound filter.
            if fine.classify(&coarse) == ContactClass::Outside {
                equal_aperture_discarded.push((at, bt));
            }
        }
    }

    // ---------------------------------------------------------------------------------------
    // Stage 2 — the all-atom contact complex, on the survivors only.
    // ---------------------------------------------------------------------------------------
    let mut stage_two_work = 0usize;
    let mut fine_contacts: Vec<(usize, usize)> = Vec::new();
    for (at, bt) in &survivors {
        let (carries, work) = all_atom_contact(&left[*at], &right[*bt], &fine);
        stage_two_work += work;
        if carries {
            fine_contacts.push((*at, *bt));
        }
    }

    // The work the full evaluation would have done: the expensive receiver on every candidate.
    let full_stage_two_work: usize = left
        .iter()
        .map(|a| right.iter().map(|b| a.atoms.len() * b.atoms.len()).sum::<usize>())
        .sum();

    // **The certified discard is sound on this material**: no discarded residue pair carries an
    // all-atom contact. This is the certificate exercised rather than asserted.
    let mut unsound_certified = 0usize;
    for (at, bt) in &discarded {
        let (carries, _) = all_atom_contact(&left[*at], &right[*bt], &fine);
        if carries {
            unsound_certified += 1;
        }
    }
    assert_eq!(
        unsound_certified, 0,
        "the inflated aperture is a certified bound: a coarse Outside reading there must certify \
         that no atom pair of those two residues is inside the fine aperture"
    );

    // **The same discard at the equal aperture is unsound**, and this counts by how much.
    let equal: BTreeSet<(usize, usize)> = equal_aperture_discarded.iter().copied().collect();
    let lost_at_the_equal_aperture = fine_contacts
        .iter()
        .filter(|pair| equal.contains(pair))
        .count();
    let resident_ns = recorder
        .record(ClockName::ResidentExecution, &resident)
        .expect("a fresh clock");

    // ---------------------------------------------------------------------------------------
    // Stages 3 and 4 — the rigidity receiver and the Hodge spectrum, over the surviving interface.
    // ---------------------------------------------------------------------------------------
    let readout = Stopwatch::start();
    let interface_left: BTreeSet<i32> = fine_contacts
        .iter()
        .map(|(at, _)| left[*at].ordinal)
        .collect();
    let interface_right: BTreeSet<i32> = fine_contacts
        .iter()
        .map(|(_, bt)| right[*bt].ordinal)
        .collect();
    // The rigidity and Hodge stages read the **declared centres**: an enclosure with width is a
    // precision question and not a place, and `ExactConfiguration::from_presented` refuses one.
    let restrict = |residues: &[ResidueAtoms], keep: &BTreeSet<i32>, lineage: &str| {
        ComponentMaterial {
            lineage: lineage.to_owned(),
            residues: residues
                .iter()
                .filter(|residue| keep.contains(&residue.ordinal))
                .map(|residue| ResidueMaterial {
                    source_ordinal: residue.ordinal,
                    monomer: residue.monomer.clone(),
                    position: residue.alpha_carbon_centre.clone(),
                })
                .collect(),
        }
    };
    let left_material = restrict(&left, &interface_left, "binder");
    let right_material = restrict(&right, &interface_right, "RBX1");
    let uncertainty =
        declared_absent_uncertainty(left_material.residues.len(), right_material.residues.len());
    let complex = found_constraint_complex(
        "the designed M5 interface, alpha-carbon representatives of the residues the all-atom \
         stage found in contact",
        EventId(1),
        vec![left_material, right_material],
        vec![PresentedFamily {
            left: ConstraintComponentId(1),
            right: ConstraintComponentId(2),
            aperture: fine.clone(),
            uncertainty,
        }],
    )
    .expect("the interface complex founds");

    let configuration =
        ExactConfiguration::from_presented(&complex).expect("the presented positions are exact");
    let rigidity = rigidity_member(&complex, &configuration, &OpenContactLaw::RefuseEveryOpen)
        .expect("the rigidity receiver reads the refusing member");
    let hodge = hodge_member(
        &complex,
        &OpenContactLaw::RefuseEveryOpen,
        &MetricDeclaration::unit("the unit metric declared by the M5 cascade measurement"),
        &BoundaryLaw::Free,
        0,
    )
    .expect("the grade-zero Hodge reading");
    let readout_ns = recorder
        .record(ClockName::Readout, &readout)
        .expect("a fresh clock");

    let end_to_end_ns = recorder
        .record(ClockName::EndToEnd, &end_to_end)
        .expect("a fresh clock");
    let receipt = recorder
        .finish(&|| ToolVersion::Unavailable {
            why: "this cascade runs inside holonic-engine itself and calls no external kit; the \
                  crate's own version is its Cargo manifest's and is not a tool version"
                .to_owned(),
        })
        .expect("the end-to-end clock was recorded");

    // ---------------------------------------------------------------------------------------
    // The report. Every count is an exact integer; the decimals are prose.
    // ---------------------------------------------------------------------------------------
    let saved = full_stage_two_work - stage_two_work;
    println!("--- the measured M5 cost cascade (designed structure, CPU only) ---");
    println!("{}", receipt.render());
    println!(
        "material: binder {} residues / {left_atoms} atoms, RBX1 {} residues / {right_atoms} atoms",
        left.len(),
        right.len()
    );
    println!(
        "certified inflated coarse aperture squared = {} (measured max grain radius {})",
        inflated.squared, radius
    );
    println!(
        "stage 1 (cheap coarse filter, inflated aperture): {stage_one_work} exact residue-pair \
         classifications, {} survivors, {} discarded",
        survivors.len(),
        discarded.len()
    );
    println!(
        "stage 2 (all-atom contact complex, survivors only): {stage_two_work} exact atom-pair \
         classifications, {} residue pairs carrying a fine contact",
        fine_contacts.len()
    );
    println!(
        "stage 2 on everything (the full evaluation): {full_stage_two_work} exact atom-pair \
         classifications"
    );
    println!(
        "cumulative cost saved by the certified cheap filter: {saved} atom-pair classifications \
         of {full_stage_two_work}"
    );
    println!(
        "the certified discard is sound: {unsound_certified} of {} discarded pairs carry a fine \
         contact",
        discarded.len()
    );
    println!(
        "the same discard at the EQUAL 8 Å aperture would have lost {lost_at_the_equal_aperture} \
         of {} fine contacts ({} pairs discarded there)",
        fine_contacts.len(),
        equal.len()
    );
    println!(
        "stage 3 (rigidity receiver): {} occurrences, {} constraints, rank J = {}, dim ker J = {}, \
         dim ker Jᵀ = {}",
        rigidity.occurrences, rigidity.constraint_count, rigidity.rank, rigidity.motion_dimension,
        rigidity.self_stress_dimension
    );
    println!(
        "stage 4 (grade-zero Hodge): {} cells, dim ker Δ₀ = {}, β₀ = {}",
        hodge.cells, hodge.harmonic_dimension, hodge.betti
    );
    println!(
        "clocks (exact ns): setup={} resident_execution={} readout={} end_to_end={}",
        setup_ns.count(),
        resident_ns.count(),
        readout_ns.count(),
        end_to_end_ns.count()
    );

    // The recorded measurement, pinned: the plan states these numbers, so the run asserts them.
    assert_eq!(
        (survivors.len(), discarded.len()),
        (3_941, 6_427),
        "stage 1 survivors and discards at the certified inflated aperture"
    );
    assert_eq!(
        (stage_two_work, full_stage_two_work),
        (156_658, 405_361),
        "all-atom classifications on the survivors against the full evaluation"
    );
    assert_eq!(saved, 248_703, "atom-pair classifications saved by the certified filter");
    assert_eq!(fine_contacts.len(), 304, "residue pairs carrying a fine contact");
    assert_eq!(unsound_certified, 0, "the certified discard loses no fine contact");
    assert_eq!(
        (equal.len(), lost_at_the_equal_aperture),
        (10_303, 239),
        "the equal-aperture discard and the fine contacts it would lose"
    );

    // The measurement is not vacuous.
    assert_eq!(
        stage_one_work,
        left.len() * right.len(),
        "the cheap stage reads every addressed residue pair exactly once"
    );
    assert!(
        stage_two_work < full_stage_two_work,
        "the cheap filter must actually discard something on this material"
    );
    assert!(
        !fine_contacts.is_empty(),
        "the designed structure has an interface"
    );
    assert!(
        lost_at_the_equal_aperture > 0,
        "the equal-aperture filter is unsound on this material, and the measurement must show it"
    );
    assert!(rigidity.constraint_count > 0 && hodge.cells > 0);
}
