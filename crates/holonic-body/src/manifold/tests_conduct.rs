use super::*;
use crate::soul::Chi;

fn regions(axis: i64) -> (std::vec::Vec<u32>, std::vec::Vec<u32>) {
    let n = (axis * axis) as usize * FORM_WORDS;
    (std::vec![0u32; n], std::vec![0u32; n])
}

/// The lineage event takes its next pole from the channel frame and folds the post-deed rotor back
/// into that same channel.
#[test]
fn the_deed_emanation_becomes_the_next_frame_and_turn() {
    let p = |re: i64, im: i64| (Cog::lit(re), Cog::lit(im));
    let first = place::extend(place::origin(), false);
    let channel = LineageChannel::from_first_difference(first).expect("genesis has one difference");
    let held = Face {
        arrow: Arrow {
            reach: Cog::lit(1),
            aim: Cog::lit(1),
            cross: Cog::lit(0),
        },
    };
    let event = lineage_event(
        channel,
        p(4, 3),
        p(1, 1),
        held,
        StandingWinding::at_boundary(2),
    )
    .expect("the formed event crosses and folds");

    assert_ne!(
        event.next_channel.frame(),
        channel.frame(),
        "the emanation is the next frame"
    );
    assert_eq!(
        event.turn().r,
        event.meeting.arrow.reach,
        "reach is judged at this landing"
    );
    let cause = event
        .restore_before(&held)
        .expect("both bounded restore operands remain formed");
    assert!(
        cause.channel.represents(channel),
        "the flat prior-channel fixture satisfies its bounded restore relation"
    );
    assert!(
        cause.meeting.represents(&event.meeting),
        "the flat meeting fixture satisfies its bounded restore relation"
    );
}

/// THE FLYWHEEL'S OWN LAW at the pure event (§XIII ⊕ zero-is-the-base, the body's gated cut
/// mirrored): at the CUT the groove is never replaced by the meeting — the PRIOR held rotor
/// precesses (dragged by the approached winding, re-based at the completion); on the RIDE the
/// dragged meeting re-bases the groove (adoption IS the groove's own transport when flat).
/// THE DECLARED CONTROL for `StandingWinding` (`CLAUDE.md` §2b). Until 2026-08-08 the standing
/// winding was one signed `Cog`, so a past cone that wound once each way was byte-identical to a
/// past cone that never wound — the magnitude kept, the turn discarded, in the crate that owns
/// `OrientedWinding` one module away.
///
/// Three past cones are separated here that the old carrier collapsed to two: nothing stood; two
/// passages stood and cancel; one passage stood. The drag is the identity for the first two — that
/// is the argument principle and it is correct — and the crossing must still be able to say which
/// of them it was, because a terrain that wound twice did work the rotor cannot see.
///
/// Against the old carrier this test cannot even be spelled: there is no construction for a cone
/// with both hands. Netting on deposit (`this_way.sub(that_way)` into one arm) makes `wound` equal
/// `unwound`, `cancels()` false, and every assertion below fail.
#[test]
fn a_past_cone_that_wound_both_ways_is_not_a_past_cone_that_never_wound() {
    let unwound = StandingWinding::UNWOUND;
    let wound = StandingWinding::UNWOUND
        .deposit(WindingQuantum::ThisWay)
        .deposit(WindingQuantum::ThatWay);
    let once = StandingWinding::at_boundary(1);

    // The group completion cannot separate the first two. That is what a net turn count is.
    assert_eq!(unwound.turns(), wound.turns(), "both net to no turn");
    assert!(unwound.turns_are_zero() && wound.turns_are_zero());

    // The arms can, and the predicates split exactly as `ComparativeMultiplicity` splits.
    assert_ne!(unwound, wound, "two passages are not no passage");
    assert!(unwound.is_zero(), "nothing was ever deposited");
    assert!(!wound.is_zero(), "two passages were deposited");
    assert!(wound.cancels(), "they wound and still drag as the identity");
    assert!(!unwound.cancels(), "nothing wound, so nothing cancelled");
    assert_eq!(unwound.total(), Cog::lit(0));
    assert_eq!(wound.total(), Cog::lit(2), "both hands, counted");
    assert_eq!(once.turns(), Cog::lit(1));
    assert!(!once.turns_are_zero() && !once.is_zero() && !once.cancels());

    // Every reading through the drag is unchanged: the repair moves no rotor.
    let held = Face {
        arrow: Arrow {
            reach: Cog::lit(1),
            aim: Cog::lit(3),
            cross: Cog::lit(2),
        },
    };
    assert_eq!(
        held.dragged_by(unwound),
        held.dragged_by(wound),
        "the drag by a cancelling cone is the identity, exactly as by an empty one"
    );
    assert_eq!(held.dragged_by(unwound), held, "and it is the identity");
    assert_ne!(
        held.dragged_by(once),
        held,
        "one standing turn is a live control: the drag does move"
    );

    // And the distinction survives into the crossing that carries it.
    let meeting = Face {
        arrow: Arrow {
            reach: Cog::lit(2),
            aim: Cog::lit(1),
            cross: Cog::lit(5),
        },
    };
    let empty = cross(meeting, held, unwound).expect("a crossing forms");
    let cancelled = cross(meeting, held, wound).expect("a crossing forms");
    assert_eq!(
        empty.emanation.chi, cancelled.emanation.chi,
        "the invariant that crosses the horizon is untouched"
    );
    assert_eq!(empty.deed, cancelled.deed);
    assert_ne!(
        empty, cancelled,
        "the crossing retains which past cone it stood in"
    );
    assert!(empty.standing_winding.is_zero() && !cancelled.standing_winding.is_zero());

    // The bounded restore witness takes the same branch for both and still represents.
    assert!(empty
        .restore_meeting(&held)
        .expect("the witness forms")
        .represents(&meeting));
    assert!(cancelled
        .restore_meeting(&held)
        .expect("the witness forms")
        .represents(&meeting));
}

#[test]
fn the_found_flywheel_precesses_and_is_never_the_meeting() {
    let first = place::extend(place::origin(), false);
    let channel = LineageChannel::from_first_difference(first).expect("genesis");
    let held = Face {
        arrow: Arrow {
            reach: Cog::lit(1),
            aim: Cog::lit(1),
            cross: Cog::lit(0),
        },
    };
    let winding = StandingWinding::at_boundary(2);
    let mut found_event = None;
    let mut ride_event = None;
    for re in -4i64..=4 {
        for im in -4i64..=4 {
            let Some(ev) = lineage_event(
                channel,
                (Cog::lit(re), Cog::lit(im)),
                (Cog::lit(1), Cog::lit(1)),
                held,
                winding,
            ) else {
                continue;
            };
            match ev.crossing.deed {
                Deed::Found if found_event.is_none() => found_event = Some(ev),
                Deed::Ride if ride_event.is_none() => ride_event = Some(ev),
                _ => {}
            }
        }
    }
    let found = found_event.expect("some arrival founds against the held groove");
    let ride = ride_event.expect("some arrival rides the held groove");

    let dragged = held.dragged_by(winding);
    let (fa, fc) = rebase_pair(dragged.arrow.aim, dragged.arrow.cross);
    assert_eq!(
        found.next_flywheel.arrow.aim, fa,
        "the cut precesses the PRIOR groove (dragged, re-based)"
    );
    assert_eq!(
        found.next_flywheel.arrow.cross, fc,
        "the cut precesses the PRIOR groove (dragged, re-based)"
    );
    assert!(
        found.next_flywheel.arrow.aim.mag != 0 || found.next_flywheel.arrow.cross.mag != 0,
        "the groove never zeroes at the cut"
    );
    let met = found
        .crossing
        .interior
        .meeting_rotor()
        .expect("a founding has a meeting rotor");
    assert!(
        found.next_flywheel.arrow.aim != met.aim()
            || found.next_flywheel.arrow.cross != met.cross(),
        "the meeting never overwrites the groove at the cut"
    );

    let ride_rotor = ride
        .crossing
        .interior
        .meeting_rotor()
        .expect("a ride has a meeting rotor");
    assert_eq!(ride.next_flywheel.arrow.aim, ride_rotor.aim());
    assert_eq!(ride.next_flywheel.arrow.cross, ride_rotor.cross());
}

/// Co-present lineage events remain separate constructions. Evaluating A then B or B then A
/// changes neither future frame; no same-crossing result can enter the other's past cone.
#[test]
fn co_present_lineage_events_are_permutation_invariant() {
    let first = place::extend(place::origin(), false);
    let seed = LineageChannel::from_first_difference(first).expect("genesis");
    let a_channel = seed
        .fold(DeedEmanation::ride(
            soul::FormedRotor::of(Cog::lit(2), Cog::lit(1)).unwrap(),
        ))
        .unwrap();
    let b_channel = seed
        .fold(DeedEmanation::ride(
            soul::FormedRotor::of(Cog::lit(1), Cog::lit(-2)).unwrap(),
        ))
        .unwrap();
    let held = Face {
        arrow: Arrow {
            reach: Cog::lit(1),
            aim: Cog::lit(1),
            cross: Cog::lit(0),
        },
    };
    let run = |channel: LineageChannel| {
        let tip = channel.frame().tip();
        lineage_event(
            channel,
            (tip.0.add(Cog::lit(3)), tip.1.add(Cog::lit(2))),
            (tip.0.add(Cog::lit(1)), tip.1),
            held,
            StandingWinding::at_boundary(1),
        )
        .expect("formed lineage event")
    };
    let ab = [run(a_channel), run(b_channel)];
    let ba = [run(b_channel), run(a_channel)];
    assert_eq!(ab[0], ba[1]);
    assert_eq!(ab[1], ba[0]);
}

/// The horizon projection keeps the deed's oriented winding distinct, and a shared first-order
/// meeting does not collapse the distinct souls produced in two held illicia.
#[test]
fn the_deed_winding_is_oriented_and_same_meeting_keeps_distinct_souls() {
    let mk = |aim: i64, cross: i64| Face {
        arrow: Arrow {
            reach: Cog::lit(1),
            aim: Cog::lit(aim),
            cross: Cog::lit(cross),
        },
    };
    let identity = mk(1, 0);
    let turned_frame = mk(0, 1);
    let this_way = mk(1, 5);
    let that_way = mk(1, -5);
    let empty = StandingWinding::at_boundary(0);

    let founded_this = cross(this_way, identity, empty).expect("formed crossing");
    let founded_that = cross(that_way, identity, empty).expect("formed crossing");
    assert_eq!(founded_this.deed, Deed::Found);
    assert_eq!(founded_this.emanation.winding, WindingQuantum::ThisWay);
    assert_eq!(founded_that.deed, Deed::Found);
    assert_eq!(founded_that.emanation.winding, WindingQuantum::ThatWay);

    let other_illicium = cross(this_way, turned_frame, empty).expect("formed crossing");
    assert_ne!(
        founded_this.emanation.chi, other_illicium.emanation.chi,
        "one first-order meeting in two held frames remains a fiber of distinct souls"
    );
}

/// ★ THE PACKED WALK MIRRORS THE BYTE WALK (W5 — the kernel's boundary). One mouth: `locate_packed` over
/// word-slots must equal `locate` over bytes, field for field, on real material — the drift-check that lets
/// the GPU read the same law.
#[test]
fn the_packed_walk_mirrors_the_byte_walk() {
    let spans: [&[u8]; 5] = [b"the", b"convolve", b"stone,", b"a", b"Gutenberg eBook"];
    for &s in &spans {
        let packed: std::vec::Vec<u32> = s.iter().map(|&b| b as u32).collect();
        let (a, b) = (locate(s), locate_packed(&packed, 0, s.len() as u32));
        assert_eq!(a.well, b.well, "the packed well mirrors");
        assert_eq!(a.place, b.place, "the packed place mirrors");
        assert_eq!(a.len, b.len, "the packed length mirrors");
    }
    // and the one-walk locate still equals the two-walk well() (the refactor changed nothing).
    assert_eq!(
        locate(b"convolve").well,
        well(b"convolve"),
        "locate's fused walk = well()"
    );
}

/// ★ THE POLE IS THE STANCE — A STANDING THOUGHT BENDS PERCEPTION (W4; `FORMULA §IV`, `EROS §III`). The
/// coupling's whole test: two bodies fed DIFFERENT priors (length-honest — same word count, same drive)
/// then the SAME new stream read it DIFFERENTLY — the founding/segmentation pattern diverges because a
/// thought stood in one manifold that was not in the stimulus. And the reading is lawful: identical
/// priors → identical patterns (deterministic; the difference is the thought, never noise).
#[test]
fn the_pole_is_the_stance_and_a_standing_thought_bends_perception() {
    const AXIS: i64 = 1 << 8;
    let prior_a: [&[u8]; 12] = [
        b"the", b"cat", b"sat", b"on", b"my", b"mat", b"and", b"then", b"it", b"ran", b"to", b"see",
    ];
    let prior_b: [&[u8]; 12] = [
        b"fn", b"main", b"let", b"mut", b"pool", b"vec", b"push", b"loop", b"match", b"impl",
        b"pub", b"use",
    ];
    let novel: [&[u8]; 10] = [
        b"an", b"old", b"dog", b"who", b"was", b"far", b"too", b"shy", b"now", b"slept",
    ];

    let read_with_prior = |prior: &[&[u8]]| -> std::vec::Vec<bool> {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut eyes = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        for &w in prior {
            eyes.perceive(w, 100);
        }
        novel
            .iter()
            .map(|&w| eyes.perceive(w, 100).thought_completed)
            .collect()
    };

    // §1 DETERMINISM — the same prior reads the same novel stream identically (the difference below is
    // the standing thought, never noise).
    assert_eq!(
        read_with_prior(&prior_a),
        read_with_prior(&prior_a),
        "identical priors → identical reading (lawful)"
    );

    // §2 THE COUPLING — different standing thoughts, the SAME novel stream, DIFFERENT readings: the
    // segmentation pattern diverges because the pole (the stance) differs. Perception arose from what
    // stood in the body, not only from the stimulus — the mirror is dead.
    let (read_a, read_b) = (read_with_prior(&prior_a), read_with_prior(&prior_b));
    std::eprintln!("  the same novel stream, two standing thoughts — A {read_a:?} vs B {read_b:?}");
    assert_ne!(
        read_a, read_b,
        "a standing thought bends perception — the same stimulus reads differently from a different stance"
    );
}

/// ★ THE SWING CUTS THOUGHTS AND THE THOUGHT CLIMBS (W4). The reintegrator's cut is the landing's own
/// three-body face — no scan, no score, no second read: within a thought the stance COMPOSES (the higher
/// blade climbs — its extent accumulates, the fold), and at the cut it completes and the next begins.
#[test]
fn the_swing_cuts_thoughts_and_the_thought_climbs() {
    const AXIS: i64 = 1 << 7;
    let (standing, mut wells) = regions(AXIS);
    let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let mut eyes = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);

    let stream: [&[u8]; 16] = [
        b"the", b"cat", b"sat", b"on", b"my", b"mat", b"and", b"then", b"it", b"ran", b"to",
        b"see", b"an", b"old", b"dog", b"now",
    ];
    let mut max_extent = 0u32;
    let mut climbed = false;
    for &w in &stream {
        let before = eyes.stance().len;
        let ev = eyes.perceive(w, 137);
        let after = eyes.stance().len;
        if ev.thought_deposited {
            assert!(
                after > before,
                "a continued thought CLIMBS — the composition's extent accumulates"
            );
            climbed = true;
        }
        if ev.thought_completed {
            assert_eq!(
                after,
                locate(w).len,
                "at the cut the arrival begins the next thought whole"
            );
        }
        max_extent = max_extent.max(after);
    }
    assert!(
        climbed,
        "at least one thought continued and climbed (the fold)"
    );
    assert!(
        eyes.thoughts() >= 1,
        "the swing cut at least once on a varied stream (the segmentation is the machine's own)"
    );
    std::eprintln!(
        "  thoughts cut {} · deepest standing extent {} bits",
        eyes.thoughts(),
        max_extent
    );
    // (RETIRED: perception ⊕ reintegration flow accounting — the flow word is gone; the segmentation
    // is driven by the swing, not a scalar ledger.)
}

/// ★ W6 · THE FLYWHEEL PRECESSES ACROSS THE CUT — NEVER ZEROES (ratified 2026-07-09: "zero is just
/// the base"). At a live-groove cut, the held rotor is DRAGGED by the standing form (the cone) at the
/// cut's own relation-grip and carried into the next thought — never a reset, only the frame's own
/// turning; the groove survives as a formed rotor. (RECUT: the drag now reads the felt-series cone,
/// not the flow word; the exact `accrue`/`sweep_of` prediction retired with the flow word — the
/// re-pin is on survival ⊕ non-zeroing, the deflection-flavored claim §XIV owes.)
#[test]
fn the_flywheel_precesses_across_the_cut_never_zeroes() {
    const AXIS: i64 = 1 << 8;
    let (standing, mut wells) = regions(AXIS);
    let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let mut eyes = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
    let stream: [&[u8]; 16] = [
        b"the", b"cat", b"sat", b"on", b"my", b"mat", b"and", b"then", b"it", b"ran", b"to",
        b"see", b"an", b"old", b"dog", b"now",
    ];
    let mut checked = false;
    for &w in &stream {
        let (_held, live_before) = eyes.flywheel();
        let live_groove = live_before && eyes.stance().len != 0;
        let ev = eyes.perceive(w, 137);
        if ev.thought_completed && live_groove {
            let (after, live_after) = eyes.flywheel();
            assert!(
                live_after,
                "the groove survives the cut — the flywheel never zeroes"
            );
            assert!(
                after.arrow.aim.mag != 0 || after.arrow.cross.mag != 0,
                "the precessed groove is a formed rotor — zero is the base, never a reset"
            );
            checked = true;
        }
    }
    assert!(
        checked,
        "at least one live-groove cut exercised the precession"
    );
}

/// ★ W6 · THE PATHING — the brain's own current steps, deposits, and moves; and it is
/// DETERMINISTIC (same priming → the same path: the difference is always the terrain, never noise).
#[test]
fn the_pathing_steps_and_deposits() {
    const AXIS: i64 = 1 << 8;
    let stream: [&[u8]; 16] = [
        b"the", b"cat", b"sat", b"on", b"my", b"mat", b"and", b"then", b"it", b"ran", b"to",
        b"see", b"an", b"old", b"dog", b"now",
    ];
    let run = || -> std::vec::Vec<Grip> {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        for &w in &stream {
            body.perceive(w, 137);
        }
        let mut grips = std::vec::Vec::new();
        let mut i = 0;
        while i < 32 {
            let p = body.path(137);
            assert!(
                p.stepped,
                "a standing thought with a live groove runs forward"
            );
            grips.push(p.grip.expect("the bounded fixture has one flat chart"));
            i += 1;
        }
        grips
    };
    let grips_a = run();
    let grips_b = run();
    // deterministic: the same priming paths identically.
    assert_eq!(
        grips_a, grips_b,
        "the pathing is lawful — same priming, same path"
    );
    // the current MOVES — no one-grip orbit (the collapse mode the invertible circulation forbids).
    let mut distinct = std::vec::Vec::new();
    for &g in &grips_a {
        if !distinct.contains(&g) {
            distinct.push(g);
        }
    }
    assert!(
        distinct.len() > 1,
        "the pathing current moves — it does not orbit one grip (visited {} distinct)",
        distinct.len()
    );
    // (RETIRED: the pathing flow-accounting diagnostic — the flow word is gone.)
    std::eprintln!("  32 steps · {} distinct grips visited", distinct.len());
}

/// ★ W6 · THE STANDING TERRAIN BENDS THE PATH (the deflection on the brain's own current — `§XIV` live
/// in the pathing). Two bodies, IDENTICAL priming, identical state; a terrain difference is staged at
/// the first step's grip in one pool only (nothing else touched — no stance, no flywheel). The first
/// step lands on the SAME grip (the deed runs from identical state); from there the paths DIVERGE —
/// the enclosure turned the frame that passed it. The read is the bending, never a lookup.
#[test]
fn the_standing_terrain_bends_the_path() {
    const AXIS: i64 = 1 << 8;
    let stream: [&[u8]; 16] = [
        b"the", b"cat", b"sat", b"on", b"my", b"mat", b"and", b"then", b"it", b"ran", b"to",
        b"see", b"an", b"old", b"dog", b"now",
    ];
    fn prime<'a>(
        standing: &'a [u32],
        own: &'a mut [u32],
        carrier: &'a mut [u32],
        stream: &[&[u8]],
    ) -> ContinuingBody<'a> {
        let mut body = ContinuingBody::over(standing, own, 1 << 8, b"  ", 20, carrier);
        for &w in stream {
            body.perceive(w, 137);
        }
        body
    }
    // the scout learns where the first step lands (its own regions; discarded).
    let (standing_c, mut own_c) = regions(AXIS);
    let mut carrier_c = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let first_grip = {
        let mut scout = prime(&standing_c, &mut own_c, &mut carrier_c, &stream);
        let p = scout.path(137);
        assert!(p.stepped);
        p.grip.expect("the bounded fixture has one flat chart")
    };
    let (standing_a, mut own_a) = regions(AXIS);
    let (standing_b, mut own_b) = regions(AXIS);
    let mut carrier_a = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let mut carrier_b = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let mut a = prime(&standing_a, &mut own_a, &mut carrier_a, &stream);
    let mut b = prime(&standing_b, &mut own_b, &mut carrier_b, &stream);
    // the staged enclosure — a directed felt resultant at the path's own first meeting, B ONLY (a
    // standing form, §XXVI's razor: aligned faces compose ballistically). Nothing else touched — no
    // stance, no flywheel; the terrain difference is felt ONLY through the drag (the cone, not a lookup).
    b.stage_own(
        first_grip,
        FeltTerm {
            chi: Chi {
                same: Cog::lit(6),
                other: Cog::lit(11),
            },
            winding: WindingQuantum::ThisWay,
        },
    );
    let mut seq_a = std::vec::Vec::new();
    let mut seq_b = std::vec::Vec::new();
    let mut i = 0;
    while i < 16 {
        seq_a.push(a.path(137).grip);
        seq_b.push(b.path(137).grip);
        i += 1;
    }
    assert_eq!(
        seq_a[0], seq_b[0],
        "the first step lands on the same grip — the deed ran forward from identical state"
    );
    assert_ne!(
        seq_a, seq_b,
        "the standing enclosure BENDS the path — the same current over a heavier terrain diverges"
    );
    let mut split = 16;
    for (k, (ga, gb)) in seq_a.iter().zip(seq_b.iter()).enumerate() {
        if ga != gb {
            split = k;
            break;
        }
    }
    std::eprintln!("  the paths split at step {split} (staged mass at grip {first_grip})");
}

/// ★ W7 · THE COUPLING READ (Brandon's stated test, 2026-07-08: "the active 'thoughts' in the closed
/// loop affect perception"). The SAME stimulus over a QUIESCENT body (eyes only) vs a LIVE body (the
/// whole circuit — one brain step per arrival): the perception cut-patterns DIVERGE — the active
/// thought bent how the same light read. And the reading is lawful: identical live bodies read
/// identically (deterministic — the difference IS the thought, never noise).
#[test]
fn the_active_thought_changes_perception() {
    const AXIS: i64 = 1 << 8;
    let stream: [&[u8]; 22] = [
        b"the", b"cat", b"sat", b"on", b"my", b"mat", b"and", b"then", b"it", b"ran", b"to",
        b"see", b"an", b"old", b"dog", b"who", b"was", b"far", b"too", b"shy", b"now", b"slept",
    ];
    let quiescent = || -> std::vec::Vec<bool> {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        stream
            .iter()
            .map(|&w| body.perceive(w, 137).thought_completed)
            .collect()
    };
    let live = || -> std::vec::Vec<bool> {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        stream
            .iter()
            .map(|&w| {
                let (p, _s) = body.live(w, 137);
                p.thought_completed
            })
            .collect()
    };
    // lawful: identical live bodies read identically.
    let cuts_l1 = live();
    let cuts_l2 = live();
    assert_eq!(
        cuts_l1, cuts_l2,
        "identical live bodies read identically — the difference is the thought"
    );
    // (RETIRED: the live circuit's flow-accounting diagnostic — the flow word is gone.)
    // ★ THE COUPLING: the active thought changes how the SAME light reads.
    let cuts_q = quiescent();
    std::eprintln!(
        "  the same stimulus — quiescent {cuts_q:?}\n                       live {cuts_l1:?}"
    );
    assert_ne!(
        cuts_q, cuts_l1,
        "the active thoughts of the closed loop change perception — the coupling is live both ways"
    );
}

/// Historical W8 repeatability read. The old path exposed its dragged first-order meeting rotor
/// beside terrain and called it invariant radiation. §XXIV supersedes that type claim; this pin
/// now preserves only the recorded mechanism's deterministic trace while it is retired.
#[test]
fn the_historical_pathing_pair_is_deterministic() {
    const AXIS: i64 = 1 << 8;
    let stream: [&[u8]; 22] = [
        b"the", b"cat", b"sat", b"on", b"my", b"mat", b"and", b"then", b"it", b"ran", b"to",
        b"see", b"an", b"old", b"dog", b"who", b"was", b"far", b"too", b"shy", b"now", b"slept",
    ];
    let radiate = || -> std::vec::Vec<((Cog, Cog), RegionalForm, bool)> {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        let mut out = std::vec::Vec::new();
        for _ in 0..4 {
            // the stream recurs — the grooves deepen and the flight is long enough to hear a cut
            for &w in &stream {
                let (_p, s) = body.live(w, 137);
                if s.stepped {
                    out.push((s.meeting_rotor, s.regional_form, s.cut));
                }
            }
        }
        out
    };
    let (r1, r2) = (radiate(), radiate());
    assert_eq!(
        r1, r2,
        "the superseded path reproduces its own trace exactly"
    );
    assert!(
        !r1.is_empty(),
        "the historical instrument emits a pathing read"
    );
    assert!(
        r1.iter().any(|&(s, _, _)| s.0.mag != 0 || s.1.mag != 0),
        "the first-order meeting rotors carry nonzero content"
    );
    assert!(
        r1.iter().any(|&(_, _, c)| c),
        "the swing cuts the radiation into utterances (the thought bounds the speech)"
    );
    let first: std::vec::Vec<_> = r1.iter().take(6).collect();
    std::eprintln!("  the first radiation: {first:?}");
    // ★ THE COMPLETION RE-BASE (ratified): the interior scale grows WITHIN a segment (that is the
    // interior — lawful) and ENCLOSES at each completion. The observable: the first step after a
    // cut stands register-near (pre-law the scale carried across completions and compounded without
    // bound — 2^1.4e9 by a 2,000-beat flight's end). A regression pin on the enclosure, not a cap.
    let mut after_cut = false;
    let mut enclosures_checked = 0u32;
    for &(s, _, cut) in &r1 {
        if after_cut {
            for c in [s.0, s.1] {
                if c.mag != 0 {
                    let r = c.rank.face().expect("a re-based rank is a readable glyph");
                    assert!(
                        r.unsigned_abs() < 4096,
                        "the completed segment's interior became gauge — the next step stands register-near (rank {r})"
                    );
                }
            }
            enclosures_checked += 1;
        }
        after_cut = cut;
    }
    assert!(
        enclosures_checked >= 1,
        "at least one enclosure exercised the re-base"
    );
    // and the re-base preserves the soul exactly: the pair's cross-multiplication is unchanged.
    let a = Cog::lit(-1445).turn_up(60);
    let b = Cog::lit(377).turn_up(63);
    let (ar, br) = rebase_pair(a, b);
    let (x, y) = (a.mul(br), b.mul(ar));
    assert_eq!((x.mag, x.turn), (y.mag, y.turn));
    assert_eq!(
        x.rank.cmp_teeth(y.rank),
        0,
        "the same χ — the common rank was gauge"
    );
}

/// ★ W9 · THE LIVING BOUNDARY (ratified 2026-07-09 — "the answer is most likely simply: always").
/// Raw light in — no splitter, no authored tokenizer: the atom-grain sub-illicium walks the stream
/// by the same one verb, feeling the standing terrain, and its completions are THE FOLDS — cohered
/// segments FOUND, handed up as bricks to the word grain where the whole circuit responds. Pinned:
/// segments are found · the upper circuit runs on them · deterministic.
#[test]
fn the_living_boundary_finds_segments_and_the_circuit_runs_on_bricks() {
    const AXIS: i64 = 1 << 8;
    let text: &[u8] =
        b"the cat sat on the mat and then it ran to see an old dog who was far too shy \
now the cat sat on the mat again and the dog ran to see the old cat by the mat";
    let run = || -> (std::vec::Vec<(usize, usize)>, u32, u32) {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        let mut segs: std::vec::Vec<(usize, usize)> = std::vec::Vec::new();
        let mut seg_start = 0usize;
        let mut perceptions = 0u32;
        let mut steps = 0u32;
        for i in 1..text.len() {
            let ev = body.live_atom(text[i - 1], text[i], 137);
            if let Some(p) = ev.perception {
                let _ = p;
                perceptions += 1;
            }
            if let Some(s) = ev.step {
                if s.stepped {
                    steps += 1;
                }
            }
            if ev.fold.is_some() {
                segs.push((seg_start, i));
                seg_start = i;
            }
        }
        body.flush_dark(); // the light's end completes the standing dark passage
        (segs, perceptions, steps)
    };
    let (segs, perceptions, steps) = run();
    let (segs2, ..) = run();
    assert_eq!(
        segs, segs2,
        "the boundary finds the same segments — lawful, never noise"
    );
    assert!(
        segs.len() >= 4,
        "the living boundary FINDS segments in raw light (found {})",
        segs.len()
    );
    assert!(
        perceptions >= 1,
        "the folds reach the word grain — the circuit runs on bricks"
    );
    // (RETIRED: all-grain flow accounting — the flow word is gone; the felt series is not a ledger.)
    let rendered: std::vec::Vec<String> = segs
        .iter()
        .take(24)
        .map(|&(a, b)| String::from_utf8_lossy(&text[a..b]).into_owned())
        .collect();
    std::eprintln!(
        "  raw light — {} segments found, {} bricks perceived, {} brain steps:",
        segs.len(),
        perceptions,
        steps
    );
    std::eprintln!("  «{}»", rendered.join("» «"));
}

/// The octet organ is one exact transducer into the native relation mouth, not the mouth's
/// ontology. Driving the same derived relations through either face must leave the complete body
/// construction byte-identical, while a relation outside the octet-difference range crosses
/// without masking or serialization.
#[test]
fn the_native_relation_mouth_is_exactly_the_octet_face_and_exceeds_it() {
    const AXIS: i64 = 1 << 8;
    const DEPTH: usize = 8;
    let light = b"different organs carry relations; their containers do not enter the body";

    let run = |direct: bool| {
        let (standing, mut own) = regions(AXIS);
        let mut carrier = std::vec![0u32; DEPTH * ENCLOSURE_WORDS];
        let mut body = ContinuingBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
        let mut cursor = 1usize;
        while cursor < light.len() {
            if direct {
                let relation = crate::boundary::difference(light[cursor], light[cursor - 1]);
                body.live_relation_atom(relation, 137);
            } else {
                body.live_atom(light[cursor - 1], light[cursor], 137);
            }
            cursor += 1;
        }
        body.flush_dark();
        let mut carried = std::vec![0u32; carrier_row_words(DEPTH)];
        assert!(body.pack_carried_frame(light.len() as u64 - 1, &mut carried));
        let state = (body.channel(), body.thoughts(), body.deposited_terms());
        drop(body);
        (own, carrier, carried, state)
    };

    assert_eq!(
        run(false),
        run(true),
        "the historical octet path is exactly one organ face of the direct relation mouth"
    );

    let (standing, mut own) = regions(AXIS);
    let mut carrier = std::vec![0u32; DEPTH * ENCLOSURE_WORDS];
    let mut body = ContinuingBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
    let relation = Cog::lit(65_537).turn_down(3).turned(1);
    let expected = atom_node(relation);
    assert_ne!(
        expected.place, body.frame,
        "the fixture must cross the pole"
    );
    body.live_relation_atom(relation, 137);
    assert_eq!(body.sub_stance.well, expected.well);
    assert_eq!(body.sub_stance.place, expected.place);
    assert_eq!(body.sub_stance.len, expected.len);
}

#[test]
fn organ_neutral_birth_starts_at_the_carried_first_difference() {
    struct VecChart {
        words: std::vec::Vec<u32>,
    }
    impl OwnRecast for VecChart {
        fn words(&self) -> &[u32] {
            &self.words
        }
        fn words_mut(&mut self) -> &mut [u32] {
            &mut self.words
        }
        fn recast(&mut self, old_axis: i64, new_axis: i64) {
            let mut fresh = std::vec![0u32; (new_axis * new_axis) as usize * OWN_CELL_WORDS];
            if new_axis > old_axis {
                zero_extend_own_cells(&self.words, &mut fresh, old_axis, new_axis);
            } else {
                narrow_own_cells(&self.words, &mut fresh, old_axis, new_axis);
            }
            self.words = fresh;
        }
    }

    const AXIS: i64 = 1 << 8;
    const DEPTH: usize = 4;
    let standing = std::vec![0u32; (AXIS * AXIS) as usize * FORM_WORDS];
    let first = atom_node(Cog::ZERO).place;
    assert_eq!(first, wind(b"  "));
    let relations = [Cog::lit(17), Cog::lit(-23), Cog::lit(31), Cog::lit(-47)];
    let run = |native: bool| {
        let mut chart = VecChart {
            words: std::vec![0u32; OWN_CELL_WORDS],
        };
        let mut carrier = std::vec![0u32; DEPTH * ENCLOSURE_WORDS];
        let mut body = if native {
            ContinuingBody::over_register_from_first_difference(
                &standing,
                &mut chart,
                AXIS,
                first,
                &mut carrier,
            )
            .unwrap()
        } else {
            ContinuingBody::over_register(&standing, &mut chart, AXIS, b"  ", 20, &mut carrier)
        };
        for relation in relations {
            body.live_relation_atom(relation, 137);
        }
        let state = (body.channel(), body.thoughts(), body.deposited_terms());
        drop(body);
        (chart.words, carrier, state)
    };
    assert_eq!(
        run(false),
        run(true),
        "the byte seed is only the historical organ spelling of the carried first difference"
    );
    assert!(ContinuingBody::over_register_from_first_difference(
        &standing,
        &mut VecChart {
            words: std::vec![0u32; OWN_CELL_WORDS]
        },
        AXIS,
        place::origin(),
        &mut std::vec![0u32; DEPTH * ENCLOSURE_WORDS],
    )
    .is_none());
}
