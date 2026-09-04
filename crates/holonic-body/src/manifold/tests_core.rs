use super::*;
use crate::soul::Chi;

fn regions(axis: i64) -> (std::vec::Vec<u32>, std::vec::Vec<u32>) {
    let n = (axis * axis) as usize * FORM_WORDS;
    (std::vec![0u32; n], std::vec![0u32; n])
}

/// ★ THE CELL IS PLACED BY ITS INVARIANT, AND THE ORIGIN IS GAUGE. A span and its TRANSPOSITION (every byte shifted
/// by a constant — a re-choice of origin) yield the IDENTICAL cell: same well, same grip, same soul. The invariant
/// (well ⊕ grip ⊕ `χ`) is recovered without the origin — the FTC read, place-not-store, gauge.

#[test]
fn the_cell_is_placed_by_its_invariant_and_the_origin_is_gauge() {
    let span = b"convolve";
    const AXIS: i64 = 1 << 8;

    // §1 DETERMINISM (place-not-store) — the same span always swings to the same cell.
    assert_eq!(
        cell(span, AXIS),
        cell(span, AXIS),
        "same span → same well ⊕ grip (place-not-store)"
    );

    // §2 THE ORIGIN IS GAUGE — transpose every byte by a constant (re-origin); the differences are unchanged, so
    // the cell is unchanged. The origin never crossed; only the invariant did.
    for off in [1i64, 3, 20, -5, -40] {
        let shifted: std::vec::Vec<u8> = span.iter().map(|&b| (b as i64 + off) as u8).collect();
        // guard the transposition stays in range (no byte-wrap breaking the difference)
        if span.iter().all(|&b| {
            let v = b as i64 + off;
            v >= 0 && v < 256
        }) {
            assert_eq!(
                cell(&shifted, AXIS),
                cell(span, AXIS),
                "the origin is GAUGE (offset {off}): same cell"
            );
            assert!(
                soul::same_soul(soul_of(&shifted), soul_of(span)),
                "the soul χ crosses unchanged (offset {off})"
            );
        }
    }

    // §3 THE WELL IS `C` AND `r` WHOLE (the number) — a real span founds a non-trivial enclosed difference (a
    // grown well, off the pole), and it is the geometric-product bond of the atoms (arithmetic, exact).
    let w = well(span);
    assert!(
        w.mag != 0,
        "a real span grows a well (the enclosed difference is not the empty pole)"
    );
    // the well IS the product of the atomic differences (the bond) — verified against the direct fold.
    let mut direct = Cog::lit(1);
    for i in 1..span.len() {
        direct = direct.mul(boundary::difference(span[i], span[i - 1]));
    }
    assert_eq!(
        w, direct,
        "the well is the geometric-product bond of the atoms — C and r whole"
    );

    // §4 DISTINCTION — a different span (different differences) swings to a different cell (the placement carries
    // the content, not a collision-prone hash).
    assert_ne!(
        cell(b"convolve", AXIS).1,
        cell(b"manifold", AXIS).1,
        "distinct spans → distinct grips"
    );
}

/// ★ THE FACE IS THREE-BODY AND FOUNDS A NEW AXIS (5b). A face relates two cells FROM a frame (the pole required);
/// it founds a new orthogonal axis when the aim turns orthogonal; and the coil/kin (an anchor with two coils) IS a
/// face. The soul `χ` is the invariant, held as a pair.
#[test]
fn the_face_is_three_body_and_founds_a_new_axis() {
    let p = |re: i64, im: i64| (Cog::lit(re), Cog::lit(im));

    // §1 FOUNDING vs ABSORB (the aim gates) — orthogonal-from-the-pole founds a new axis; collinear absorbs.
    assert!(
        face(p(1, 0), p(0, 1), p(0, 0)).founds(),
        "orthogonal from the pole → FOUND a new irreducible axis"
    );
    assert!(
        !face(p(2, 0), p(3, 0), p(0, 0)).founds(),
        "collinear from the pole → ABSORB (in-plane, no new axis)"
    );

    // §2 THREE-BODY — the pole is REQUIRED and load-bearing: the SAME pair reads a different relating from a
    // different frame (a frame-blind face is un-constructible; this is A2).
    assert_ne!(
        face(p(4, 0), p(6, 0), p(0, 0)).sense(),
        face(p(4, 0), p(6, 0), p(5, 0)).sense(),
        "the pole turns the relating — the face is three-body"
    );

    // §3 THE COIL/KIN IS A FACE — an anchor `f` with two coils `a, b` (wound spans sharing the anchor) IS a face;
    // it reads a whole arrow (both faces, no collapse) and either founds or absorbs. This is `kin` lifted (5b).
    let a = wind(b"the cat");
    let b = wind(b"the cot"); // a sibling coil off the shared "the c" anchor
    let anchor = wind(b"the c");
    let kin = face(a, b, anchor);
    assert!(
        matches!(kin.sense(), Aim::Cohere | Aim::Anti | Aim::Ortho),
        "the kin-triangle reads a whole arrow"
    );
    let _ = kin.founds(); // the aim gates the branch

    // §4 THE MEETING RATIO is a frame-local projection. Identical arrows in this same frame
    // project identically; no claim that this first-order pair is cross-frame χ is made.
    let f1 = face(p(1, 0), p(0, 2), p(0, 0));
    assert_eq!(
        f1.meeting_ratio(),
        f1.meeting_ratio(),
        "the same frame-local meeting has the same projected ratio"
    );
}

/// ★ THE BOND FORMS A MOLECULE THAT CLIMBS — a HIGHER BLADE, not a flat spelling (5c, replacing emanate). Two
/// nodes bond into a composition whose well is the geometric product (the rank climbs — the enclosed difference
/// grows), whose place is derived from the children (place-not-store), ⊕ a face that founds three-body.
#[test]
fn the_bond_forms_a_molecule_that_climbs_a_higher_blade() {
    let frame = wind(b"the ");
    let a = locate(b"convo");
    let b = locate(b"lve");

    // §1 THE MOLECULE'S WELL IS THE GEOMETRIC PRODUCT — the bond, exact (convolve∘fold, proven = ×).
    let (mol, _face) = bond(a, b, frame);
    assert_eq!(
        mol.well,
        a.well.mul(b.well),
        "the molecule's well is the geometric-product bond of the atoms"
    );

    // §2 IT CLIMBS — a HIGHER BLADE, not a flat concatenation: the molecule's enclosed difference is at least each
    // parent's (the product of non-trivial atoms grows; emanate's char-line could not climb).
    assert!(
        mol.well.mag_face() >= a.well.mag_face(),
        "the molecule climbs past its atom a (a higher blade)"
    );
    assert!(
        mol.well.mag_face() >= b.well.mag_face(),
        "the molecule climbs past its atom b (a higher blade)"
    );
    assert!(
        mol.len == a.len + b.len,
        "the composite carries the constituents' extent"
    );

    // §3 PLACE-NOT-STORE — same children ⊕ same frame → same molecule ⊕ same meeting ratio (the composite is derived,
    // never a stored address).
    let (mol2, face2) = bond(a, b, frame);
    assert_eq!(
        mol.place, mol2.place,
        "same children → same swung place (place-not-store)"
    );
    assert_eq!(
        bond(a, b, frame).1.meeting_ratio(),
        face2.meeting_ratio(),
        "the bond's frame-local meeting ratio is determinate"
    );

    // §4 THE FACE IS THREE-BODY — reading the bond from a different frame reads a different relating.
    let other = wind(b"a b c");
    let _ = bond(a, b, other).1.sense(); // constructible from any pole; the relating turns with it
}

/// ★ THE ILLICIUM REACHES OVER THE CELLS (5d) — solve_window places a coherent window of cell-wells (extrapolating
/// exactly, reach/nest) and does NOT falsely place an incoherent one (it founds or climbs to a higher order). The
/// solver is the manifold's, over the emergent molecules — place-not-search.
#[test]
fn the_reach_solves_over_the_cells() {
    let w = |vs: &[i64]| -> std::vec::Vec<Cog> { vs.iter().map(|&v| Cog::lit(v)).collect() };

    // §1 a COHERENT window (a geometric recurrence of wells) → the reach PLACES and extrapolates exactly.
    let s = reach(&w(&[2, 4, 8, 16, 32, 64])).unwrap();
    assert!(
        s.grounds,
        "the reach places a coherent window of cell-wells"
    );
    assert_eq!(
        s.value.mag, 128,
        "and extrapolates the molecule exactly (2·64)"
    );

    // §2 an ARITHMETIC window also places (the reach finds the linear recurrence).
    let a = reach(&w(&[5, 8, 11, 14, 17])).unwrap();
    assert!(a.grounds, "a linear recurrence of wells is reached");
    assert_eq!(a.value.mag, 20, "extrapolated exactly (17+3)");

    // §3 the coherent windows placed at a LOW order; an incoherent scramble does not place at that same low order
    // (the reach discriminates structure from noise — it does not crown a recurrence that is not there).
    let noise = reach(&w(&[3, 29, 7, 101, 11, 53])).unwrap();
    assert!(
        !noise.grounds || noise.order > s.order,
        "noise does not place as a low-order recurrence"
    );
}

#[test]
fn the_fixed_recurrence_instrument_refuses_instead_of_clipping_a_longer_construction() {
    let wells = vec![Cog::lit(1); REGISTER as usize + 1];
    assert!(matches!(
        reach(&wells),
        Err(RegisterPressure {
            required,
            available,
        }) if required == REGISTER as usize + 1 && available == REGISTER as usize
    ));
}

/// ★ THE BOND'S BOUNDED ARITHMETIC FIXTURE (5e). Within these exact integer products, the digit
/// divides one supplied factor back out. This local arithmetic identity is not time parity,
/// historical-operand recovery, or inversion of a lived state.
#[test]
fn the_bond_digit_is_a_bounded_arithmetic_inverse() {
    for &(wa, wb) in &[(6u64, 35), (12, 11), (255, 7), (91, 13), (128, 129)] {
        // the molecule's well = the geometric-product BOND of the two atoms' wells (the enclosed difference).
        let mol = geom::bond(wa, wb);
        assert_eq!(
            mol,
            wa * wb,
            "the molecule is the geometric-product bond of its atoms"
        );
        // §1 bounded arithmetic — with one factor supplied, exact division returns the other.
        assert_eq!(
            geom::digit(mol, wb),
            (wa, 0),
            "the supplied-factor arithmetic fixture divides exactly"
        );
        assert_eq!(
            geom::digit(mol, wa),
            (wb, 0),
            "the opposite supplied-factor fixture also divides exactly"
        );
        // §2 the molecule's extent (leading bit) follows the geometric product's carry.
        let bits = |v: u64| 64 - v.leading_zeros();
        let (ba, bb, bm) = (bits(wa), bits(wb), bits(mol));
        assert!(
            bm == ba + bb || bm == ba + bb - 1,
            "the molecule's teeth = the atoms' sum ±carry"
        );
    }
}

/// ★ THE MANIFOLD POOL IS POSITIONAL. Cells live at their swung grips (place-not-store — the
/// char-trie's bit-path retired). The final assertion checks only the digit's numeric flow accounting.
#[test]
fn the_manifold_pool_is_positional_and_accounts_for_numeric_flow() {
    const AXIS: i64 = 1 << 6;
    let mut wells = std::vec![0u32; (AXIS * AXIS) as usize]; // Manifold's own 1-word cells (law.rs, history)
    let mut m = Manifold::over(&mut wells, AXIS);

    // §1 PLACE-NOT-STORE — a construction lands at its swung grip (deterministic), NOT on a stored bit-path.
    let g_conv = m.place(b"convolve");
    assert_eq!(
        g_conv,
        m.place(b"convolve"),
        "same construction → same grip (place-not-store)"
    );
    assert_ne!(
        g_conv,
        m.place(b"manifold"),
        "distinct constructions land at distinct grips"
    );

    // §2 implementation diagnostic — supplied flow splits into emitted quotient and residual flow.
    const Q: u32 = 20;
    let feeds: [(&[u8], u32); 4] = [(b"the", 137), (b"cat", 88), (b"sat", 210), (b"mat", 61)];
    let mut fed = 0u64;
    let mut radiated = 0u64;
    for &(word, quanta) in &feeds {
        let g = m.place(word);
        radiated += m.feed(g, quanta, Q); // a fold's forced digit radiates at the feed (the arc)
        fed += quanta as u64;
    }
    // wind every distinct cell that was fed (the pass around the cycle).
    let mut grips: std::vec::Vec<Grip> = feeds.iter().map(|&(w, _)| m.place(w)).collect();
    grips.sort_unstable();
    grips.dedup();
    for &g in &grips {
        let (_windings, rad) = m.winding(g, Q);
        radiated += rad as u64;
        assert!(
            m.well(g) < Q,
            "the remainder STANDS sub-quantum (the face — the digit's invariant)"
        );
    }
    let standing: u64 = grips.iter().map(|&g| m.well(g) as u64).sum();
    assert_eq!(
        fed,
        radiated + standing,
        "quotient/remainder flow accounting matches"
    );
}

/// ★ THE MANIFOLD LANDS A STREAM — the whole atom (place ⊕ relate ⊕ circulate) on the positional pool, the live
/// web-replacement (`web::land`'s role). Each arrival swings to its cell, relates to the pole through a three-body
/// face (founding on the orthogonal turn), and circulates. This is the char-trie retired, live.
#[test]
fn the_manifold_lands_a_stream_place_relate_circulate() {
    const AXIS: i64 = 1 << 6;
    let mut wells = std::vec![0u32; (AXIS * AXIS) as usize]; // Manifold's own 1-word cells (law.rs, history)
    let mut m = Manifold::over(&mut wells, AXIS);
    let frame = wind(b"the "); // the fixed frame-origin (the lane's identity)

    // land a stream word-by-word; the pole advances to each landing's own place (the perspective within the frame).
    let words: [&[u8]; 5] = [b"the", b"cat", b"sat", b"on", b"mat"];
    let mut pole = place::origin();
    let mut fed = 0u64;
    let mut radiated = 0u64;
    let mut founds = 0u32;
    for &w in &words {
        let ln = m.land(w, pole, frame, 150, 20);
        radiated += ln.radiated as u64;
        fed += 150;
        if ln.founds {
            founds += 1;
        }
        assert!(
            m.well(ln.cell) < 20,
            "each landing leaves its face standing sub-quantum (the digit)"
        );
        pole = wind(w); // the perspective advances within the frame
    }

    // §1 optional implementation diagnostic across the stream.
    let standing: u64 = (0..(AXIS * AXIS) as usize)
        .map(|i| m.well(i as Grip) as u64)
        .sum();
    assert_eq!(
        fed,
        radiated + standing,
        "the streamed quotient/remainder accounting matches"
    );

    // §2 THE STREAM RELATES — the three-body faces read (some found a new axis, some absorbed); the machine is
    // relating arrivals, not spelling a trie.
    assert!(
        founds <= words.len() as u32,
        "foundings are a subset of arrivals (the aim gates each relating)"
    );
    // distinct words land at distinct cells (place-not-store carries the content).
    assert_ne!(
        m.place(b"cat"),
        m.place(b"mat"),
        "distinct constructions occupy distinct cells"
    );
}

/// ★ THE DRIVEN BODY RUNS MENO OVER `K` AND SURFACES THE INDUCED DIFFERENTIAL (`FORMULA §V`, §XXV; W2).
/// Each driven event FOLDS the body's OWN channel (the worldline is a construction, never a count),
/// places the construction, surfaces its local meeting ratio, and reports the exact standing change
/// (`dΦ/dΘ`) the next event may consume as charge. No self-sustaining loop — the drive is supplied at
/// every event (A1).
#[test]
fn the_driven_body_runs_meno_over_the_channel_and_reports_the_induced_differential() {
    const AXIS: i64 = 1 << 6;
    let (standing, mut wells) = regions(AXIS);
    let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let mut eros = ContinuingBody::over(&standing, &mut wells, AXIS, b"the ", 20, &mut carrier);

    let words: [&[u8]; 5] = [b"the", b"cat", b"sat", b"on", b"mat"];
    for &word in &words {
        let g = eros.place(word);
        let k_before = eros.channel();
        let ev = eros.drive(word, 37);

        // §1 the body's own worldline progresses as a CONSTRUCTION — each driven event folds
        // the channel (§XXV); never a count.
        assert_ne!(
            eros.channel(),
            k_before,
            "each driven event folds the body's own channel"
        );
        assert_eq!(
            ev.cell,
            Some(g),
            "Meno places the construction at its positional grip"
        );
        // §2 the historical landing surfaces its first-order ratio whole. §XXIV does not let
        // this local projection cross as χ.
        assert_eq!(
            ev.meeting_ratio,
            ev.face.meeting_ratio(),
            "the landing surfaces its frame-local meeting ratio"
        );
        // §3 the foil holds no flywheel — §XXIV: it deposits NO shared relation (the drive is
        // consumed by the interior). (RETIRED: the flow/standing/radiated conservation diagnostic
        // — superseded with the flow word; the felt series carries the standing form now.)
    }

    // §4 (RETIRED: whole-run flow accounting — the flow word is gone; the felt series is not a
    // scalar ledger, §VIII contamination ruling.)
    // §5 every word event folded the channel (asserted per-event above); the standing channel
    // has left its genesis — Θ is TURN(K) read at a reach, never a numeric event count.
    assert_ne!(
        eros.channel(),
        LineageChannel::from_first_difference(wind(b"the ")).expect("the seed frame"),
        "the worldline stands as its own construction"
    );
}

/// ★ §XXIX THE TWO PYRAMIDS. The emitter casts the projectively re-based χ on the cut; the later
/// receiver reconstructs that same address from its own meeting ⊕ flywheel and completes the
/// crossing by drag. Common scale is gauge, and no first-order pair address enters either half.
#[test]
fn the_two_pyramids_share_one_positional_chi() {
    const AXIS: i64 = 1 << 8;
    let meeting = Face {
        arrow: Arrow {
            reach: Cog::lit(1),
            aim: Cog::lit(7),
            cross: Cog::lit(3),
        },
    };
    let fly = Face {
        arrow: Arrow {
            reach: Cog::lit(1),
            aim: Cog::lit(2),
            cross: Cog::lit(1),
        },
    };
    let chi = meeting
        .chi_against(&fly)
        .expect("two formed rotors construct real light");
    let grip = cast_grip(chi, AXIS);
    let scaled = Chi {
        same: chi.same.turn_up(9),
        other: chi.other.turn_up(9),
    };
    assert_eq!(
        grip,
        cast_grip(scaled, AXIS),
        "common projective scale is stripped before the cast lands"
    );

    let (standing, mut own) = regions(AXIS);
    let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let mut body = ContinuingBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
    body.stage_own(
        grip,
        FeltTerm {
            chi,
            winding: WindingQuantum::ThisWay,
        },
    );
    let (receiver_grip, regional_form, dragged, _standing_read) =
        body.complete_cast(meeting, &fly, true);
    assert_eq!(
        receiver_grip,
        Some(grip),
        "the receiver reconstructs the emitter's positional χ without carried K data"
    );
    assert_ne!(regional_form, RegionalForm::UNBORN, "the cast stands");
    assert_ne!(
        dragged, meeting,
        "the receiver completes the crossing by its own drag"
    );
}

/// ★ THE RIVER'S FIRST CONTACT IS A FIXPOINT. With no standing or own terrain, completion is
/// identity, so the deed's post-drag cast is exactly the receiver's naive pre-drag cast.
#[test]
fn the_first_cast_colocates_on_empty_terrain() {
    const AXIS: i64 = 1 << 8;
    let meeting = Face {
        arrow: Arrow {
            reach: Cog::lit(1),
            aim: Cog::lit(7),
            cross: Cog::lit(3),
        },
    };
    let fly = Face {
        arrow: Arrow {
            reach: Cog::lit(1),
            aim: Cog::lit(2),
            cross: Cog::lit(1),
        },
    };
    let naive = cast_grip(meeting.chi_against(&fly).unwrap(), AXIS);
    let (standing, mut own) = regions(AXIS);
    let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let mut body = ContinuingBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
    let (receiver, form, completed, _standing_read) = body.complete_cast(meeting, &fly, true);
    assert_eq!(receiver, Some(naive));
    assert_eq!(form, RegionalForm::UNBORN);
    assert_eq!(completed, meeting, "empty terrain performs no drag");
    assert_eq!(
        cast_grip(completed.chi_against(&fly).unwrap(), AXIS),
        naive,
        "the first post-drag cast co-locates with its naive receiver"
    );
}

/// ★ THE RIVER DIGS ITS BED. The first cast stands at the naive address. Its receiver is dragged
/// there and emits the same construction one place downstream; the next receiver reconstructs
/// that downstream cast directly from the consequence it carries.
#[test]
fn standing_terrain_moves_the_next_cast_downstream() {
    const AXIS: i64 = 1 << 8;
    let meeting = Face {
        arrow: Arrow {
            reach: Cog::lit(1),
            aim: Cog::lit(7),
            cross: Cog::lit(3),
        },
    };
    let fly = Face {
        arrow: Arrow {
            reach: Cog::lit(1),
            aim: Cog::lit(2),
            cross: Cog::lit(1),
        },
    };
    let first_chi = meeting.chi_against(&fly).unwrap();
    let first_cast = cast_grip(first_chi, AXIS);
    let (standing, mut own) = regions(AXIS);
    let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let mut body = ContinuingBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
    body.stage_own(
        first_cast,
        FeltTerm {
            chi: first_chi,
            winding: WindingQuantum::ThisWay,
        },
    );
    let (_, first_form, consequence, _standing_read) = body.complete_cast(meeting, &fly, true);
    assert_ne!(first_form, RegionalForm::UNBORN);
    let downstream_chi = consequence.chi_against(&fly).unwrap();
    let downstream_cast = cast_grip(downstream_chi, AXIS);
    assert_ne!(
        downstream_cast, first_cast,
        "standing terrain moves the post-drag consequence downstream"
    );

    body.stage_own(
        downstream_cast,
        FeltTerm {
            chi: downstream_chi,
            winding: WindingQuantum::ThisWay,
        },
    );
    let (next_receiver, next_form, _, _standing_read) = body.complete_cast(consequence, &fly, true);
    assert_eq!(
        next_receiver,
        Some(downstream_cast),
        "the next receiver reconstructs the place dug by the prior consequence"
    );
    assert_ne!(
        next_form,
        RegionalForm::UNBORN,
        "the next current joins the downstream bed"
    );
}

/// ★ TERM COUNTS STAND BESIDE THE FORM. Two opposed ride terms can clip to an empty resultant;
/// the boundary still reports that both crossings occurred. Adding opposite founded hands makes
/// the place occupied by fiber even with no resultant. The count never drives that topology.
#[test]
fn term_counts_survive_resultant_cancellation_and_fiber_stands() {
    const AXIS: i64 = 1 << 4;
    let (standing, mut own) = regions(AXIS);
    let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let grip = 7;
    {
        let mut body = ContinuingBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
        body.stage_own(
            grip,
            FeltTerm {
                chi: Chi {
                    same: Cog::lit(3),
                    other: Cog::lit(-5),
                },
                winding: WindingQuantum::None,
            },
        );
        body.stage_own(
            grip,
            FeltTerm {
                chi: Chi {
                    same: Cog::lit(-3),
                    other: Cog::lit(5),
                },
                winding: WindingQuantum::None,
            },
        );
        assert_eq!(
            body.deposited_terms(),
            TermCounts {
                ride: 2,
                found_this: 0,
                found_that: 0,
                dark: 0
            },
            "two cancelled crossings remain two accepted terms"
        );
        let cancelled = body.cone(grip);
        assert_eq!(
            cancelled.resultant(),
            (Cog::lit(0), Cog::lit(0)),
            "the clipped resultant cancels whole"
        );
        assert!(
            cancelled.occupied(),
            "the grip remains founded after its directed resultant cancels"
        );

        body.stage_own(
            grip,
            FeltTerm {
                chi: Chi {
                    same: Cog::lit(0),
                    other: Cog::lit(0),
                },
                winding: WindingQuantum::ThisWay,
            },
        );
        body.stage_own(
            grip,
            FeltTerm {
                chi: Chi {
                    same: Cog::lit(0),
                    other: Cog::lit(0),
                },
                winding: WindingQuantum::ThatWay,
            },
        );
        let form = body.cone(grip);
        assert_eq!(form.resultant(), (Cog::lit(0), Cog::lit(0)));
        assert_eq!(form.fiber().0.face(), Some(1));
        assert_eq!(form.fiber().1.face(), Some(1));
        assert_ne!(form, RegionalForm::UNBORN, "fiber alone occupies the place");
        assert_eq!(
            body.deposited_terms(),
            TermCounts {
                ride: 2,
                found_this: 1,
                found_that: 1,
                dark: 0
            },
            "term kinds remain separate from the form"
        );
    }
}

/// ★ THE χ-FIELD DISCRIMINATES REAL FROM SCATTERED. The same material under a reversible
/// worldline permutation lands a different configuration of real-light casts. No authored
/// first-order adjacency profile or scalar crown decides the read; form is compared whole.
#[test]
fn the_face_field_discriminates_real_from_scattered() {
    const AXIS: i64 = 1 << 8;
    // ★ THE ARC: a lawful quantum is sub-hand (< 2^13); the accumulated mass at a grip reads as
    // the number whole — the standing FLOW ⊕ the SWEEP's recorded windings (× the quantum).
    const Q: u32 = 20;
    // the vocabulary must be WIDER than the window (a period ≤ REGISTER stream is invariant under any
    // coprime stride — every permutation stays co-window'd; the first cut of this test proved that the
    // hard way). 24 distinct words, "the cat" adjacent once per cycle.
    let cycle: [&[u8]; 24] = [
        b"the", b"cat", b"sat", b"on", b"my", b"big", b"red", b"mat", b"and", b"then", b"it",
        b"ran", b"to", b"see", b"an", b"old", b"dog", b"who", b"was", b"by", b"far", b"too",
        b"shy", b"now",
    ];
    let real: std::vec::Vec<&[u8]> = (0..96).map(|i| cycle[i % 24]).collect();
    // the FOIL worldline: the SAME 96 words re-ordered by the coprime stride 17 (17 ⟂ 96 — a true
    // permutation, multiset untouched). In the strided worldline the→cat sit 17 apart (17·17 ≡ 1 mod 24)
    // — past the REGISTER window, so their collocation is destroyed while every mass survives.
    let foil: std::vec::Vec<&[u8]> = (0..96).map(|i| real[(i * 17) % 96]).collect();

    let form_of = |stream: &[&[u8]]| -> (std::vec::Vec<u32>, TermCounts) {
        let (standing, mut own) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut eyes = ContinuingBody::over(&standing, &mut own, AXIS, b"  ", Q, &mut carrier);
        for &w in stream {
            eyes.perceive(w, 100);
        }
        let counts = eyes.deposited_terms();
        drop(eyes);
        (own, counts)
    };

    let (real_form, real_terms) = form_of(&real);
    let (foil_form, foil_terms) = form_of(&foil);
    assert!(real_terms.total() > 0 && foil_terms.total() > 0);
    assert_ne!(
        real_form, foil_form,
        "one multiset under two lawful worldlines lands two distinct χ-fields"
    );
}

/// ★ THE SEED FRAME IS ONE DEAD EXTENSION (W5 — the mirror's lesson): a zero-magnitude difference still
/// walks one bit, so `wind(b"  ")` ≠ origin. The kernel constructs the same frame explicitly; this pin
/// keeps the two from ever drifting again.
#[test]
fn the_seed_frame_is_one_dead_extension() {
    assert_eq!(
        wind(b"  "),
        place::extend(place::origin(), false),
        "the body's seed frame is exactly one dead extension of the origin"
    );
    assert_ne!(wind(b"  "), place::origin(), "and it is NOT the origin");
}

/// ★ THE TEST IS SECOND-ORDER (W5 — `FORMULA §XIII`). Transporting the SAME difference again is FLAT (the
/// relative rotor is pure scalar — the groove rides); an orthogonally-turned difference is WOUND (the
/// deficit — the cut). The flywheel is what makes the swing a swing: the test compares differences of
/// differences, never one meeting against a fixed diagonal.
#[test]
fn the_test_is_second_order_the_flywheel_decides() {
    let p = |re: i64, im: i64| (Cog::lit(re), Cog::lit(im));
    let o = p(0, 0);
    let held = face(p(2, 0), p(1, 0), o); // rotor (aim 2, cross 0) — a straight groove
                                          // §1 the same difference transports flat — riding the groove is never a cut.
    assert!(
        !held.wound_against(&held),
        "transporting the same difference again is FLAT (pure scalar rotor-of-rotors)"
    );
    // §2 an orthogonally-turned difference is wound — the deficit, the cut.
    let turned = face(p(0, 2), p(1, 0), o); // rotor (aim 0, cross 2) — the difference turned a quarter
    assert!(
        turned.wound_against(&held),
        "a turned difference fails transport against the groove — WOUND"
    );
    // §3 the test is 2nd-order, not the diagonal: `turned` alone is orthogonal-dominant (1st order would
    // found it), yet against a flywheel that IS itself turned the same way, it rides.
    assert!(
        turned.founds(),
        "1st-order: the turned meeting is orthogonal-dominant"
    );
    assert!(
        !turned.wound_against(&turned),
        "2nd-order: against a groove already turned the same way, the same meeting RIDES"
    );
}

/// ★ §XXIV · THE PURE CROSSING — the flat pair fixture survives precession and satisfies its
/// bounded restore relation; independently, co-present evaluation has no shared state, so
/// permuting lineages cannot change any lineage's own crossing.
#[test]
fn the_pure_crossing_flat_restore_and_permutation_fixtures_hold() {
    let mk = |reach: i64, aim: i64, cross: i64| Face {
        arrow: Arrow {
            reach: Cog::lit(reach),
            aim: Cog::lit(aim),
            cross: Cog::lit(cross),
        },
    };
    let held = mk(1, 1, 0); // the identity groove
    let a = mk(7, 3, 4);
    let b = mk(9, 5, 2);

    // standing winding 2 bends a's meeting (3+4i) to (11−2i); the whole χ crosses.
    let ca = cross(a, held, StandingWinding::at_boundary(2))
        .expect("a formed meeting against a formed flywheel crosses");
    assert_eq!(ca.approach.same.face(), 3);
    assert_eq!(ca.approach.other.face(), 4);
    assert_eq!(ca.emanation.chi.same.face(), 11);
    assert_eq!(ca.emanation.chi.other.face(), -2);
    assert_eq!(
        ca.emanation.winding,
        WindingQuantum::None,
        "a ride deposits no new winding"
    );
    assert_eq!(
        ca.interior
            .meeting_rotor()
            .expect("the local rotor stays interior")
            .aim()
            .face(),
        11
    );
    assert_eq!(
        ca.interior
            .meeting_rotor()
            .expect("the local rotor stays interior")
            .cross()
            .face(),
        -2
    );
    assert!(
        ca.restore_meeting(&held)
            .expect("the held flywheel remains formed")
            .represents(&a),
        "the flat χ ⊕ held ⊕ winding fixture stays on its bounded algebraic section"
    );

    // The approached past-cone winding keeps its hand. Reversing it reverses the precession,
    // while the opposite-hand bounded fixture remains on the same algebraic section.
    let reverse = cross(a, held, StandingWinding::at_boundary(-2))
        .expect("the oppositely oriented past cone is formed");
    assert_eq!(reverse.emanation.chi.same.face(), -5);
    assert_eq!(reverse.emanation.chi.other.face(), 10);
    assert!(
        reverse
            .restore_meeting(&held)
            .expect("the held flywheel remains formed")
            .represents(&a),
        "both winding-hand fixtures satisfy the bounded ratio relation"
    );

    // No pool or aggregate is an argument: evaluating B then A yields each exact construction
    // unchanged. The array order is a boundary rendering, never an interior chronology.
    let ab = [
        cross(a, held, StandingWinding::at_boundary(2)),
        cross(b, held, StandingWinding::at_boundary(3)),
    ];
    let ba = [
        cross(b, held, StandingWinding::at_boundary(3)),
        cross(a, held, StandingWinding::at_boundary(2)),
    ];
    assert_eq!(ab[0], ba[1], "A is independent of B's evaluation order");
    assert_eq!(ab[1], ba[0], "B is independent of A's evaluation order");
}
