use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::exact_linear::ExactRatMatrix;
use num_traits::Zero;

pub(super) fn row_space(rows: Vec<Vec<Rat>>) -> Vec<Vec<Rat>> {
    ExactRatMatrix::new(rows)
        .unwrap()
        .reduced_row_echelon()
        .unwrap()
        .0
        .to_rows()
        .into_iter()
        .filter(|row| row.iter().any(|x| !x.is_zero()))
        .collect()
}

fn unique(value: ConstitutiveFibreReturn) -> Vec<Rat> {
    match value.predecessor_reading {
        ConstitutiveReading::Unique { current } => current,
        other => panic!("expected a unique admitted current, got {other:?}"),
    }
}

#[test]
#[ignore = "requires CUDA; native exact local constitutive formation"]
fn native_fibre_develops_its_domain_and_reuses_the_formed_relation() {
    let readout = ResidentReadout::new().expect("CUDA apparatus required");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found(&surface, 2, 1).unwrap();
    let empty = body.advance(&[1, 0], None).unwrap();
    assert!(matches!(
        empty.predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    assert_eq!(empty.successor_rank, 0);
    let first = body.advance(&[2, 0], Some(&[6])).unwrap();
    assert_eq!(first.formed_pivot, Some(0));
    assert_eq!(
        unique(body.advance(&[1, 0], None).unwrap()),
        vec![Rat::from_integer(3.into())]
    );
    assert!(matches!(
        body.advance(&[0, 1], None).unwrap().predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    let second = body.advance(&[0, 2], Some(&[5])).unwrap();
    assert_eq!(second.formed_pivot, Some(1));
    assert_eq!(
        unique(body.advance(&[3, 4], None).unwrap()),
        vec![Rat::from_integer(19.into())]
    );
    assert_eq!(
        unique(body.advance(&[0, 1], None).unwrap()),
        vec![Rat::new(5.into(), 2.into())]
    );
    let matched = body.advance(&[-2, 0], Some(&[-6])).unwrap();
    assert_eq!(matched.formed_pivot, None);
    assert_eq!(matched.successor_rank, 2);
    assert_eq!(body.occurrences(), 8);
}

#[test]
#[ignore = "requires CUDA; retain vertical and absent-source fibres"]
fn conflicting_returns_are_plural_not_averaged_or_overwritten() {
    let readout = ResidentReadout::new().expect("CUDA apparatus required");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found(&surface, 2, 1).unwrap();
    body.advance(&[1, 0], Some(&[3])).unwrap();
    let contrast = body.advance(&[1, 0], Some(&[4])).unwrap();
    assert_eq!(unique(contrast), vec![Rat::from_integer(3.into())]);
    match body.advance(&[2, 0], None).unwrap().predecessor_reading {
        ConstitutiveReading::Plural {
            particular,
            directions,
        } => {
            assert_eq!(particular, vec![Rat::from_integer(6.into())]);
            assert_eq!(directions, vec![vec![Rat::from_integer(1.into())]]);
        }
        other => panic!("conflicting local evidence must remain plural: {other:?}"),
    }
    assert!(matches!(
        body.advance(&[0, 1], None).unwrap().predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    let zero = body.advance(&[0, 0], Some(&[0])).unwrap();
    assert_eq!(zero.formed_pivot, None);
    assert_eq!(zero.successor_rank, 2);
}

#[test]
#[ignore = "requires CUDA; exact covariance of a bounded linear current family"]
fn source_and_receiver_recharting_preserve_the_qualified_relation() {
    let readout = ResidentReadout::new().expect("CUDA apparatus required");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut original = ResidentConstitutiveFibre::found(&surface, 2, 2).unwrap();
    let mut reversed = ResidentConstitutiveFibre::found(&surface, 2, 2).unwrap();
    let mut recharted = ResidentConstitutiveFibre::found(&surface, 2, 2).unwrap();
    // Source shear (x,y)->(x+y,y); receiver quarter-turn (u,v)->(-v,u).
    // Each body is independently founded by the actual paired currents, not cloned for rollback.
    for (x, y) in [([2, 1], [7, 2]), ([1, -1], [-1, 3])] {
        original.advance(&x, Some(&y)).unwrap();
        recharted
            .advance(&[x[0] + x[1], x[1]], Some(&[-y[1], y[0]]))
            .unwrap();
    }
    for (x, y) in [([1, -1], [-1, 3]), ([2, 1], [7, 2])] {
        reversed.advance(&x, Some(&y)).unwrap();
    }
    let expected = vec![Rat::from_integer(23.into()), Rat::from_integer(0.into())];
    assert_eq!(unique(original.advance(&[4, 5], None).unwrap()), expected);
    assert_eq!(unique(reversed.advance(&[4, 5], None).unwrap()), expected);
    assert_eq!(
        unique(recharted.advance(&[9, 5], None).unwrap()),
        vec![Rat::from_integer(0.into()), Rat::from_integer(23.into())]
    );
    assert_ne!(
        unique(recharted.advance(&[4, 5], None).unwrap()),
        vec![Rat::from_integer(0.into()), Rat::from_integer(23.into())]
    );
}

#[test]
#[ignore = "requires CUDA; staged local formation refuses atomically"]
fn arithmetic_refusal_preserves_the_basis_and_does_not_replay_a_deposit() {
    let readout = ResidentReadout::new().expect("CUDA apparatus required");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found(&surface, 2, 1).unwrap();
    body.advance(&[i64::MAX, 1], Some(&[i64::MAX])).unwrap();
    let before = body.inspect_relation().unwrap();
    assert!(matches!(
        body.advance(&[1, i64::MAX], Some(&[0])),
        Err(ConstitutiveFibreError::Arithmetic(_))
    ));
    assert_eq!(body.inspect_relation().unwrap(), before);
    assert_eq!(body.occurrences(), 1);
    assert_eq!(
        unique(body.advance(&[0, 0], None).unwrap()),
        vec![Rat::from_integer(0.into())]
    );
    assert_eq!(body.occurrences(), 2);
}

#[test]
#[ignore = "requires CUDA; zero-source discrepancy is a genuine vertical fibre"]
fn zero_source_nonzero_return_opens_the_receiver() {
    let readout = ResidentReadout::new().expect("CUDA apparatus required");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found(&surface, 1, 2).unwrap();
    let first = body.advance(&[0], Some(&[2, -3])).unwrap();
    assert_eq!(first.formed_pivot, Some(1));
    match body.advance(&[0], None).unwrap().predecessor_reading {
        ConstitutiveReading::Plural {
            particular,
            directions,
        } => {
            assert_eq!(particular, vec![Rat::from_integer(0.into()); 2]);
            assert_eq!(
                directions,
                vec![vec![
                    Rat::from_integer(2.into()),
                    Rat::from_integer((-3).into())
                ]]
            );
        }
        other => panic!("zero-source discrepancy was erased: {other:?}"),
    }
}

#[test]
#[ignore = "requires CUDA; exact-rational observer compares all formed relation rows"]
fn native_row_formation_matches_the_complete_presented_span() {
    let readout = ResidentReadout::new().expect("CUDA apparatus required");
    let surface = ResidentSurface::on(&readout).unwrap();
    // The observer's arbitrary-precision RREF reads full row spaces; it is not called by the body.
    // Include rational pivots, negative hands, dependence, zero sources and contradictory returns.
    for offset in -2..=2 {
        let mut body = ResidentConstitutiveFibre::found(&surface, 3, 2).unwrap();
        let mut presented = Vec::new();
        for row in [
            [2, 1, 0, 3, offset],
            [1, -1, 1, 5, 2],
            [0, 2, -1, -1, 3],
            [4, 2, 0, 6, 2 * offset],
            [0, 0, 0, offset, 1],
            [2, 1, 0, -3, 2],
        ] {
            body.advance(&row[..3], Some(&row[3..])).unwrap();
            presented.push(
                row.into_iter()
                    .map(|v| Rat::from_integer(v.into()))
                    .collect(),
            );
            let native = body.inspect_relation().unwrap();
            let actual = native
                .intervals
                .chunks_exact(5)
                .map(|row| {
                    row.iter()
                        .map(|(lo, hi)| {
                            assert_eq!(lo, hi);
                            Rat::from_integer((*lo).into())
                        })
                        .collect()
                })
                .collect();
            assert_eq!(row_space(actual), row_space(presented.clone()));
        }
    }
}

#[test]
#[ignore = "requires CUDA; source-only recurrence keeps the relation resident"]
fn ordinary_reading_does_not_reupload_or_read_back_the_relation() {
    let readout = ResidentReadout::new().expect("CUDA apparatus required");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found(&surface, 2, 1).unwrap();
    body.advance(&[2, 0], Some(&[3])).unwrap();
    let before = body.census();
    assert_eq!(
        unique(body.advance(&[1, 0], None).unwrap()),
        vec![Rat::new(3.into(), 2.into())]
    );
    let after = body.census();
    assert_eq!(after.ingress_octets - before.ingress_octets, 3 * 16);
    assert_eq!(
        after.egress_section_octets - before.egress_section_octets,
        7 * 16
    );
    assert_eq!(after.deed_launches - before.deed_launches, 1);
    assert_eq!(after.section_read_outs - before.section_read_outs, 1);
}

#[test]
#[ignore = "requires CUDA; physical scratch admission precedes basis allocation"]
fn physical_scratch_aperture_is_read_before_allocating_a_relation() {
    let readout = ResidentReadout::new().expect("CUDA apparatus required");
    let surface = ResidentSurface::on(&readout).unwrap();
    let before = surface.census();
    let beyond = surface.declaration().max_sectiond_bytes as usize / 32 + 1;
    assert!(matches!(
        ResidentConstitutiveFibre::found(&surface, beyond, 1),
        Err(ConstitutiveFibreError::ScratchAperture { .. })
    ));
    assert_eq!(surface.census(), before);
}
