//! Tests for **the chaser's release through the one law** (THE_REBUILD U3, the second loop): the
//! certified capture is `Released` at tolerance zero on the capture reading, the probe is `Ask` with
//! its partition, and the cornering commit is the declared separate arm whose separating term is the
//! price. The pre-U3 selector runs beside the law on small fixtures and agrees on every one.

use super::*;
use crate::receiver::release::partition_product;

fn worth(capture: Option<usize>, cornering: usize, nearness: i64, classes: &[usize]) -> Worth {
    Worth {
        capture,
        expected: None,
        cornering,
        nearness,
        classes: classes.to_vec(),
        information: partition_product(classes),
    }
}

/// The pre-U3 selector, as `MachineChaser::decide` ran it before the second loop (commit
/// `c10acca9`): the release it returned and the motion it emitted.
fn pre_u3(worths: &[Worth], fibre: usize, price: u64) -> (Release, usize) {
    let commit_key = |w: &Worth| (w.capture.is_none(), w.capture, w.cornering, w.nearness);
    let commit = (0..worths.len())
        .min_by_key(|&i| commit_key(&worths[i]))
        .expect("a nonempty admitted set");
    let mut release = if worths[commit].capture.is_some() {
        Release::Certified
    } else {
        Release::Commit
    };
    let mut chosen = commit;
    if fibre > 1 && release == Release::Commit {
        let probe = (0..worths.len())
            .min_by(|&a, &b| {
                let (wa, wb) = (&worths[a], &worths[b]);
                (&wa.information, wa.cornering, wa.nearness).cmp(&(
                    &wb.information,
                    wb.cornering,
                    wb.nearness,
                ))
            })
            .expect("a nonempty admitted set");
        let concession = worths[probe]
            .cornering
            .saturating_sub(worths[commit].cornering);
        let affordable = (concession as u128) <= u128::from(price) * (fibre as u128);
        if worths[probe].information < worths[commit].information && affordable {
            release = Release::Probe;
            chosen = probe;
        }
    }
    (release, chosen)
}

/// **Parity: the one law reproduces the pre-U3 selector** on every fixture of three admitted
/// motions over a fibre of four (captures none or two ticks, cornering `0` or `3`, the partitions
/// `{4}`, `{2, 2}`, `{3, 1}`, `{1, 1, 1, 1}`) and of one member, at the prices `0` and `1`; and each
/// return is the arm it names: `Released` at width and tolerance zero exactly where the commit is
/// certified, an `Ask` carrying the probe's classes against the commit's, and the cornering arm
/// carrying `Hold` where no probe is offered and the refused `Ask` with a concession above its price.
#[test]
fn the_chasers_release_is_the_pre_u3_rule_through_the_one_law() {
    let captures = [None, Some(2)];
    let cornerings = [0, 3];
    let partitions: [&[usize]; 4] = [&[4], &[2, 2], &[3, 1], &[1, 1, 1, 1]];
    let mut plural_moves = Vec::new();
    let mut single_moves = Vec::new();
    for &capture in &captures {
        for &cornering in &cornerings {
            single_moves.push((capture, cornering, &[][..]));
            for &classes in &partitions {
                plural_moves.push((capture, cornering, classes));
            }
        }
    }
    let mut decided = [0usize; 3];
    for (fibre, moves) in [(4usize, &plural_moves), (1, &single_moves)] {
        for a in moves.iter() {
            for b in moves.iter() {
                for c in moves.iter() {
                    let worths: Vec<Worth> = [a, b, c]
                        .iter()
                        .enumerate()
                        .map(|(i, &&(capture, cornering, classes))| {
                            worth(capture, cornering, i as i64 % 2, classes)
                        })
                        .collect();
                    for price in [0u64, 1] {
                        let (released, chosen) = release_among(&worths, Plan::Robust, fibre, price)
                            .expect("a lawful release");
                        assert_eq!(
                            (released.kind(), chosen),
                            pre_u3(&worths, fibre, price),
                            "{released:?}"
                        );
                        match &released {
                            MachineRelease::Law(ReleaseReturn::Released { width, tolerance }) => {
                                assert!(width.is_zero() && tolerance.is_zero());
                                assert!(worths[chosen].capture.is_some());
                                decided[0] += 1;
                            }
                            MachineRelease::Law(ReleaseReturn::Ask { probe }) => {
                                let ProbeSeparation::Counted(counted) = &probe.partition else {
                                    panic!("the chaser offers a counted partition, got {probe:?}");
                                };
                                assert_eq!(counted.classes(), &worths[chosen].classes[..]);
                                assert!(counted.product() < counted.against_product());
                                decided[1] += 1;
                            }
                            MachineRelease::Commit { law, price: cost } => {
                                assert!(worths[chosen].capture.is_none());
                                match (law, cost) {
                                    (ReleaseReturn::Hold, None) => {}
                                    (ReleaseReturn::Ask { .. }, Some(cost)) => {
                                        assert!(!cost.affordable());
                                        assert_eq!(cost.bound, u128::from(price) * fibre as u128);
                                    }
                                    other => panic!("a cornering commit beside {other:?}"),
                                }
                                decided[2] += 1;
                            }
                            other => panic!("the capture rule returned {other:?}"),
                        }
                    }
                }
            }
        }
    }
    assert!(decided.iter().all(|&count| count > 0), "{decided:?}");
}

/// **The price separates the cornering arm.** The commit corners to `0` and splits nothing; the
/// probe splits the fibre of four in halves and concedes five tube states. At the price one
/// (`d·|Θ| = 4 < 5`) the law's `Ask` is refused by the price and the machine corners; at the price two
/// (`8 ≥ 5`) the probe is emitted. Certify the commit and the law releases it at tolerance zero,
/// though the probe still separates more.
#[test]
fn the_price_is_the_separating_term_of_the_cornering_arm() {
    let worths = vec![worth(None, 0, 0, &[4]), worth(None, 5, 0, &[2, 2])];
    let expected_probe = ObservationProbe {
        observation: "admitted motion 1 of 2".to_owned(),
        partition: ProbeSeparation::Counted(
            ProbePartition::new(vec![2, 2], vec![4]).expect("a separating partition"),
        ),
    };
    assert_eq!(
        release_among(&worths, Plan::Robust, 4, 1).expect("a lawful release"),
        (
            MachineRelease::Commit {
                law: ReleaseReturn::Ask {
                    probe: expected_probe.clone()
                },
                price: Some(ProbePrice {
                    concession: 5,
                    bound: 4
                }),
            },
            0
        )
    );
    assert_eq!(
        release_among(&worths, Plan::Robust, 4, 2).expect("a lawful release"),
        (
            MachineRelease::Law(ReleaseReturn::Ask {
                probe: expected_probe
            }),
            1
        )
    );
    let certified = vec![worth(Some(3), 0, 0, &[4]), worth(None, 5, 0, &[2, 2])];
    assert_eq!(
        release_among(&certified, Plan::Robust, 4, 2).expect("a lawful release"),
        (
            MachineRelease::Law(ReleaseReturn::Released {
                width: Rat::zero(),
                tolerance: Rat::zero()
            }),
            0
        )
    );
    assert!(release_among(&[], Plan::Robust, 4, 0).is_err());
}

fn expected(uncaptured: usize, ticks: usize, worst: usize) -> Option<ExpectedCapture> {
    Some(ExpectedCapture {
        uncaptured,
        ticks,
        worst,
    })
}

/// **The released bound is the plan's own** (module header, the pledge). Two moves certify capture
/// of a fibre of two within `4` ticks: the first by the minimax strategy (captures at `4` and `4`,
/// `E = (0, 8, 4)`), the second by a strategy of a lesser sum and a later worst case (captures at
/// `1` and `6`, `E = (0, 7, 6)`). The robust plan releases the first within its certificate `4`; the
/// pledged expected plan releases the second within its own strategy's worst case `6`, not the
/// certificate `4` it would not keep. An uncertified commit has no bound, and a pledged expected
/// reading that leaves a member uncaptured, or reads a worst case below the certificate, beside a
/// certified commit is refused: the two readings disagree.
#[test]
fn the_released_bound_is_the_plans_own() {
    let mut worths = vec![worth(Some(4), 5, 0, &[2]), worth(Some(4), 0, 0, &[2])];
    worths[0].expected = expected(0, 8, 4);
    worths[1].expected = expected(0, 7, 6);
    let released = MachineRelease::Law(ReleaseReturn::Released {
        width: Rat::zero(),
        tolerance: Rat::zero(),
    });
    let robust = release_among(&worths, Plan::Robust, 2, 0).expect("a lawful release");
    assert_eq!(robust, (released.clone(), 1));
    assert_eq!(
        released_bound(Plan::Robust, &worths[1]).expect("a bound"),
        4
    );
    worths[1].cornering = 9;
    assert_eq!(
        release_among(&worths, Plan::Robust, 2, 0).expect("a lawful release"),
        (released.clone(), 0)
    );
    assert_eq!(
        release_among(&worths, Plan::CertifiedExpected, 2, 0).expect("a lawful release"),
        (released.clone(), 1)
    );
    assert_eq!(
        released_bound(Plan::CertifiedExpected, &worths[1]).expect("a bound"),
        4
    );
    let pledged = release_among(&worths, Plan::Expected, 2, 0).expect("a lawful release");
    assert_eq!(pledged, (released, 1));
    assert_eq!(
        released_bound(Plan::Expected, &worths[1]).expect("a bound"),
        6
    );
    assert!(released_bound(Plan::Robust, &worth(None, 0, 0, &[2])).is_err());
    let mut disagreeing = worth(Some(4), 0, 0, &[2]);
    for reading in [expected(1, 3, 3), expected(0, 6, 3), None] {
        disagreeing.expected = reading;
        assert!(released_bound(Plan::Expected, &disagreeing).is_err());
    }
}
