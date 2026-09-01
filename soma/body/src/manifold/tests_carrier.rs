use super::*;
fn regions(axis: i64) -> (std::vec::Vec<u32>, std::vec::Vec<u32>) {
    let n = (axis * axis) as usize * FORM_WORDS;
    (std::vec![0u32; n], std::vec![0u32; n])
}

/// a scalar PROXY for a place's felt mass — the cone's resultant ⊕ fiber magnitudes summed. Not a
/// law read (the felt series is never collapsed to a scalar in the engine); a test's boundary
/// measure of "how much standing form the felt series accumulated here".
fn felt_mass(form: RegionalForm) -> u64 {
    let (s, o) = form.resultant();
    let (tw, ta) = form.fiber();
    s.mag as u64 + o.mag as u64 + tw.mag as u64 + ta.mag as u64
}

/// integrate one light's WHOLE CONFIGURATION into a STANDING region, cell by cell, via the
/// two-pass configuration fold. `standing` and every lane-local OWN spool are `FORM_WORDS`-
/// strided regions of the same geometry. This helper deliberately accepts the lanes together:
/// repeated binary `join` is commutative but not associative after re-base and would reinstall a
/// hidden chronology in the test itself.
fn integrate_configuration(standing: &mut [u32], own: &[&[u32]]) {
    let cells = standing.len() / FORM_WORDS;
    let mut c = 0usize;
    while c < cells {
        let at = c * FORM_WORDS;
        let mut forms = std::vec::Vec::with_capacity(own.len() + 1);
        forms.push(RegionalForm::unpack(standing, at));
        for region in own {
            assert_eq!(
                region.len(),
                standing.len(),
                "all light regions share one geometry"
            );
            forms.push(RegionalForm::unpack(region, at));
        }
        let folded = crate::medium::integrate(&forms);
        let mut row = [0u32; FORM_WORDS];
        folded.pack(&mut row, 0);
        standing[at..at + FORM_WORDS].copy_from_slice(&row);
        c += 1;
    }
}

#[test]
fn the_current_deed_envelope_bounds_the_complete_recursive_body() {
    assert_eq!(current_conduct_envelope(3, 2, 0).unwrap().maximum_deeds, 5);
    assert_eq!(
        current_conduct_envelope(3, 2, 1).unwrap().maximum_deeds,
        3 * (1 + REGISTER as u64 + 2) + 2
    );
    assert!(current_conduct_envelope(1, 0, 64).is_none());

    const AXIS: i64 = 1 << 8;
    const DEPTH: usize = 5;
    let relations = [
        Cog::lit(3),
        Cog::lit(-5),
        Cog::lit(8),
        Cog::lit(13),
        Cog::lit(-21),
        Cog::lit(34),
        Cog::lit(-55),
        Cog::lit(89),
    ];
    let (standing, mut own) = regions(AXIS);
    let mut carrier = std::vec![0u32; DEPTH * ENCLOSURE_WORDS];
    let mut body = ContinuingBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
    let mut deeds = 0u64;
    for relation in relations {
        body.live_relation_atom_emitting(relation, 137, &mut |_| deeds += 1);
    }
    let envelope = current_conduct_envelope(relations.len() as u64, 0, DEPTH).unwrap();
    assert!(deeds <= envelope.maximum_deeds);
}

#[test]
fn live_sparse_own_is_the_dense_register_without_the_axis_square() {
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
    const DEPTH: usize = 5;
    let relations = [
        Cog::lit(3),
        Cog::lit(-5),
        Cog::lit(8),
        Cog::lit(13),
        Cog::lit(-21),
        Cog::lit(34),
        Cog::lit(-55),
        Cog::lit(89),
        Cog::lit(-144),
        Cog::lit(233),
    ];
    let standing = std::vec![0u32; (AXIS * AXIS) as usize * FORM_WORDS];
    let first = atom_node(relations[0]).place;
    let maximum = current_conduct_envelope(relations.len() as u64, 0, DEPTH)
        .unwrap()
        .maximum_deeds as usize;

    let mut dense_chart = VecChart {
        words: std::vec![0u32; OWN_CELL_WORDS],
    };
    let mut dense_carrier = std::vec![0u32; DEPTH * ENCLOSURE_WORDS];
    let mut dense_emissions = std::vec::Vec::new();
    let dense_face = {
        let mut body = ContinuingBody::over_register_from_first_difference(
            &standing,
            &mut dense_chart,
            AXIS,
            first,
            &mut dense_carrier,
        )
        .unwrap();
        for relation in relations {
            body.live_relation_atom_emitting(relation, 0, &mut |deed| dense_emissions.push(deed));
        }
        (
            body.channel(),
            body.thoughts(),
            body.deposited_terms(),
            body.own_axis(),
            body.own_occupancy(),
            body.breath(),
        )
    };

    let mut sparse_reservation = std::vec![SparseOwnCell::EMPTY; maximum];
    let mut sparse_carrier = std::vec![0u32; DEPTH * ENCLOSURE_WORDS];
    let mut sparse_emissions = std::vec::Vec::new();
    let (sparse_face, sparse_cells) = {
        let mut body = ContinuingBody::over_sparse_from_first_difference(
            &standing,
            &mut sparse_reservation,
            AXIS,
            first,
            &mut sparse_carrier,
        )
        .unwrap();
        for relation in relations {
            body.live_relation_atom_emitting(relation, 0, &mut |deed| sparse_emissions.push(deed));
        }
        (
            (
                body.channel(),
                body.thoughts(),
                body.deposited_terms(),
                body.own_axis(),
                body.own_occupancy(),
                body.breath(),
            ),
            body.sparse_own_cells().unwrap().to_vec(),
        )
    };

    assert_eq!(sparse_face, dense_face);
    assert_eq!(sparse_carrier, dense_carrier);
    assert_eq!(sparse_emissions, dense_emissions);

    let dense_axis = dense_face.3 as usize;
    let mut dense_cells = std::vec::Vec::new();
    for grip in 0..dense_axis * dense_axis {
        let at = grip * OWN_CELL_WORDS;
        if dense_chart.words[at + OWN_CELL_LIVE] != 0 {
            dense_cells.push((
                grip as Grip,
                own_cell_position(&dense_chart.words, at),
                RegionalForm::unpack(&dense_chart.words, at + OWN_CELL_FORM),
            ));
        }
    }
    let sparse_cells: std::vec::Vec<_> = sparse_cells
        .iter()
        .map(|cell| (cell.grip(), cell.position(), cell.form()))
        .collect();
    assert_eq!(sparse_cells, dense_cells);
    assert!(sparse_cells.len() < dense_axis * dense_axis);
    assert_eq!(sparse_reservation.len(), maximum);
}

/// ★ THE CARRIER THICKENS (`FORMULA §XVIII`, ratified 2026-07-09): completions at depth k are
/// arrivals at depth k+1 — on real material the carrier stands ABOVE the word grain (enclosures
/// standing at depth ≥ 1), deterministically; each
/// enclosure instantiates at its first brick (found, never listed), and the standing count is a
/// boundary read (an audit scan, never a mechanism).
#[test]
fn the_carrier_thickens() {
    const AXIS: i64 = 1 << 8;
    let text: &[u8] =
        b"the cat sat on the mat and then it ran to see an old dog who was far too shy \
now the cat sat on the mat again and the dog ran to see the old cat by the mat \
while the shy dog saw the old rat run past the cat and the mat once more today";
    let run = || -> (u32, usize) {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        for i in 1..text.len() {
            body.live_atom(text[i - 1], text[i], 137);
        }
        body.flush_dark();
        (body.standing_enclosures(), body.carrier_depth())
    };
    let (standing_enc, depth) = run();
    let (standing_enc2, depth2) = run();
    assert_eq!(
        (standing_enc, depth),
        (standing_enc2, depth2),
        "the carrier is lawful — same light, same thickening"
    );
    assert!(
        standing_enc >= 2,
        "the carrier stands above the word grain on real material (standing enclosures {standing_enc})"
    );
    // (RETIRED: the per-depth flow-accounting diagnostic — the flow word is gone.)
    std::eprintln!("  the carrier: {standing_enc} standing enclosures of {depth} reserved");
}

/// ★ THE WHOLE CARRIED FRAME HAS ONE MOUTH — the membrane and card derive row extent and every
/// organ offset from this module. The reservation mounts exactly one deferred sibling per open
/// depth; a cpu beat drains those slots before the frame crosses a stroke.
#[test]
fn the_carried_frame_layout_is_the_reservations_own() {
    const AXIS: i64 = 1 << 8;
    const DEPTH: usize = 3;
    let words = carrier_row_words(DEPTH);
    assert_eq!(carrier_row_depth(words), DEPTH);
    assert_eq!(
        carrier_deferred_base(DEPTH, 0),
        carrier_enclosure_base(0) + DEPTH * ENCLOSURE_WORDS,
        "deferred siblings begin exactly after the reservation's enclosure rows"
    );
    assert_eq!(
        carrier_deferred_base(DEPTH, DEPTH),
        carrier_continuation_base(DEPTH),
        "one deferred node is mounted per reserved depth — no second bound"
    );
    assert_eq!(
        words,
        carrier_pending_base(DEPTH) + CARRIER_PENDING_DEED_WORDS,
        "the exact pending-deed continuation closes the same carrier row"
    );

    let (standing, mut wells) = regions(AXIS);
    let mut enclosures = std::vec![0u32; DEPTH * ENCLOSURE_WORDS];
    let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut enclosures);
    body.live_atom(b'a', b'a', 137); // a standing dark passage crosses the stroke
    let mut frame = std::vec![0u32; words];
    assert!(body.pack_carried_frame(2, &mut frame));
    assert_eq!(frame[CARRIER_CURSOR_LO], 2);
    assert_eq!(frame[CARRIER_DARK_LO], 137);
    assert_eq!(
        LineageChannel::unpack(&frame, CARRIER_CHANNEL),
        Some(body.channel()),
        "K crosses the stroke seam byte-exact in the carried frame"
    );
    assert!(
        frame[carrier_deferred_base(DEPTH, 0)..]
            .iter()
            .all(|&w| w == 0),
        "a completed beat leaves no hidden carry behind"
    );

    body.live_atom(b'a', b'z', 137); // the edge resolves the tread and opens the atom stance
    assert!(body.pack_carried_frame(3, &mut frame));
    assert_eq!(frame[CARRIER_DARK_LO], 0);
    assert_ne!(
        frame[CARRIER_SUB_STANCE + NODE_WORDS - 1],
        0,
        "the atom-grain stance rides in the same carried frame"
    );
}

/// A fixed compatibility row cannot turn its physical edge into darkness. The exact depth pressure
/// is reported and later atoms stop; the production membrane supplies a growable carrier and its
/// parity against a sufficiently deep sibling is gated in `soma-membrane`.
#[test]
fn a_fixed_carrier_reports_depth_pressure_instead_of_retiring_the_brick() {
    const AXIS: i64 = 1 << 8;
    let text: &[u8] =
        b"the cat sat on the mat and then it ran to see an old dog who was far too shy \
now the cat sat on the mat again and the dog ran to see the old cat by the mat";
    let run = || -> (u32, usize, Option<usize>) {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; ENCLOSURE_WORDS]; // depth 1 — the reservation's own edge
        let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        assert_eq!(
            body.carrier_depth(),
            1,
            "the reservation affords exactly one depth"
        );
        for i in 1..text.len() {
            body.live_atom(text[i - 1], text[i], 137);
            if body.resource_refused() {
                break;
            }
        }
        (
            body.thoughts(),
            body.carrier_depth(),
            body.required_carrier_depth(),
        )
    };
    let a = run();
    let b = run();
    assert_eq!(
        a, b,
        "the same construction reaches the same physical pressure"
    );
    assert_eq!(
        a.1, 1,
        "the carrier never grows past the caller's one-row reservation"
    );
    assert!(a.2.is_some_and(|depth| depth > a.1));
}

/// ★ THE DARK TREAD IS OVER TIME (ratified 2026-07-09 — the induced-current law made mechanism):
/// a zero-run's interior induces NOTHING per atom (no event, no Θ, no swing) — the passage
/// accumulates its supplied drive and deposits WHOLE at its completion (the resolving edge, or the
/// light's end), at the frame's own place. The deposit is one transition, not
/// N; the sweep at the pole's cell deepens with the completed silence.
/// §XXV: the body's `frame` field and the channel's gauge anchor are ONE construction. A fork
/// here would be two frames for one lineage — the W5 two-frame drift (one dead bit apart, 2
/// events in 5,172) at the body grain. The anchor never resets; the field never drifts.
#[test]
fn the_frame_field_is_the_channels_anchor() {
    const AXIS: i64 = 1 << 8;
    let (standing, mut wells) = regions(AXIS);
    let mut carrier = std::vec![0u32; 4 * ENCLOSURE_WORDS];
    let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"ab", 20, &mut carrier);
    let anchor0 = body.channel().frame().anchor;
    assert_eq!(body.frame, anchor0, "one frame, one anchor, at birth");
    let light = b"the cat sat on the mat    and then it ran far away from the old dog today";
    let mut i = 1usize;
    while i < light.len() {
        body.live_atom(light[i - 1], light[i], 137);
        i += 1;
    }
    body.flush_dark();
    assert_eq!(
        body.channel().frame().anchor,
        anchor0,
        "the anchor NEVER resets — the lineage's first difference stands for life"
    );
    assert_eq!(
        body.frame, anchor0,
        "the frame field is the anchor's own cache — no second frame exists"
    );
}

#[test]
fn the_dark_tread_is_over_time() {
    const AXIS: i64 = 1 << 8;
    const Q: u32 = 20;
    let (standing, mut wells) = regions(AXIS);
    let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", Q, &mut carrier);
    let dark_cell = body.place(b"  "); // wind(b"  ") = one dead bit — the frame's own place (the anchor)
                                       // §1 a long silence then a resolving edge: N dark atoms, one bright.
    const N: usize = 10_000;
    let k_before = body.channel();
    for _ in 0..N {
        let ev = body.live_atom(b'a', b'a', 137);
        assert!(
            ev.fold.is_none() && ev.perception.is_none(),
            "the interior is not an event"
        );
    }
    assert_eq!(
        body.channel(),
        k_before,
        "no fold inside the sameness — duration, not order"
    );
    assert_eq!(
        body.cone(dark_cell),
        RegionalForm::UNBORN,
        "nothing lands until the passage completes"
    );
    let _ev = body.live_atom(b'a', b'z', 137); // the resolving edge completes the passage
    let k_edge = body.channel();
    assert_ne!(
        k_edge, k_before,
        "the completed passage and the resolving atom fold the channel"
    );
    assert_eq!(
        k_edge,
        k_before
            .fold(DeedEmanation::dark())
            .expect("one completed silence folds"),
        "the edge's one fold is the passage's own dark fold — the resolving atom's first \
         meeting is at the frame's horizon (the unborn sub-stance stands at the pole) and \
         folds nothing"
    );
    // §2 the whole tread stands at the pole's place — the felt term crossed at the anchor grip.
    body.flush_dark(); // idempotent — the passage already completed at the edge
    assert_eq!(
        body.channel(),
        k_edge,
        "a completed passage cannot fold again — one passage, one fold"
    );
    assert_ne!(
        body.cone(dark_cell),
        RegionalForm::UNBORN,
        "the completed silence stands at the pole's own place — the tread is real mass (the felt term)"
    );
    assert!(
        felt_mass(body.cone(dark_cell)) > 0,
        "the pure-Same dark term carries the passage's accumulated magnitude"
    );
    // §3 determinism: the same silence lays the same tread.
    let (standing2, mut wells2) = regions(AXIS);
    let mut carrier2 = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let mut body2 = ContinuingBody::over(&standing2, &mut wells2, AXIS, b"  ", Q, &mut carrier2);
    for _ in 0..N {
        body2.live_atom(b'a', b'a', 137);
    }
    body2.live_atom(b'a', b'z', 137);
    body2.flush_dark();
    assert_eq!(
        body.cone(dark_cell),
        body2.cone(dark_cell),
        "the same silence lays the byte-identical felt tread at the pole"
    );
    assert_eq!(
        body.channel(),
        body2.channel(),
        "the same light folds the same channel"
    );
    // §4 the light's end alone completes the passage: the standing silence folds `K` EXACTLY
    // once at the flush — the construction equality, not a count.
    let (standing3, mut wells3) = regions(AXIS);
    let mut carrier3 = std::vec![0u32; 8 * ENCLOSURE_WORDS];
    let mut body3 = ContinuingBody::over(&standing3, &mut wells3, AXIS, b"  ", Q, &mut carrier3);
    let k0 = body3.channel();
    for _ in 0..N {
        body3.live_atom(b'a', b'a', 137);
    }
    assert_eq!(body3.channel(), k0, "the sameness never folds mid-passage");
    body3.flush_dark();
    assert_eq!(
        body3.channel(),
        k0.fold(DeedEmanation::dark())
            .expect("one completed silence folds"),
        "the flush folds the channel exactly once — one passage, one fold"
    );
}

/// ★ THE FRAME'S HORIZON (ratified 2026-07-09) ⊕ EQUIVALENCE IS NOT EQUALITY. A form of two equal
/// atoms winds a zero-magnitude difference — one dead bit — EXACTLY the frame's own place: it stands
/// AT THE POLE, behind this frame's own horizon, so its relating is un-constructible from this pole
/// and is NOT READ (the beat passes through: stance stands, flywheel holds, no cut, no deposit) — and
/// the circuit reads on normally afterward (the darkness is not absorbing). Meanwhile the SAME form
/// arriving twice — two worldline events at one place — reads pure-Same and RIDES: two forms at one
/// place are TWO (coordinate equality is gauge; equivalence of souls is cross-multiplied, never `=`).
#[test]
fn the_frames_horizon_passes_unread_and_recurrence_rides() {
    const AXIS: i64 = 1 << 8;
    // §1 EQUIVALENCE IS NOT EQUALITY — two forms at one place read PURE-SAME, never a null: the
    // raw meeting of a form with its standing equivalent has the Same face full and the Different
    // face null (a ride-shaped rotor) and is NOT at the horizon — no false singularity between two
    // equivalent forms. (The terrain may still TURN that rotor — the recurrence deposits at its own
    // self-relation grip and the drag reads it: gravity punctuating recognition is the precession
    // law, not a singularity.)
    {
        let n = locate(b"the");
        let f = place::extend(place::origin(), false);
        let rel = face(n.place, n.place, f);
        assert!(
            rel.arrow.aim.mag > 0,
            "the Same face is full — the two are related, not nothing"
        );
        assert_eq!(
            rel.arrow.cross.mag, 0,
            "the Different face is null — the same form again is FLAT"
        );
        assert!(
            !rel.arrow.at_horizon(),
            "two equivalent forms at one place are TWO — no singularity"
        );
        assert!(
            !rel.founds(),
            "the raw recurrence is ride-shaped (the groove's own direction)"
        );
    }
    // §2 THE POLE-FORM AT BIRTH — a thought cannot stand behind the eye's own horizon.
    {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        body.perceive(b"aa", 137); // two equal atoms — one dead bit — the frame's own place
        assert_eq!(body.stance().len, 0, "a pole-form cannot found the stance");
        body.perceive(b"the", 137);
        assert_ne!(
            body.stance().len,
            0,
            "the next resolvable arrival founds the first thought"
        );
    }
    // §3 THE DARK BEAT PASSES THROUGH UNREAD — and the circuit re-ignites on its own.
    {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut body = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        for &w in [b"the" as &[u8], b"cat", b"sat", b"on"].iter() {
            body.perceive(w, 137);
        }
        let stance_before = body.stance();
        let (fly_before, live_before) = body.flywheel();
        let thoughts_before = body.thoughts();
        let ev = body.perceive(b"aa", 137); // the strand at the pole — unconstructible from here
        assert!(
            !ev.thought_completed && !ev.thought_deposited,
            "the unconstructible relating is NOT READ — no cut, no ride"
        );
        assert_eq!(body.stance().len, stance_before.len, "the stance stands");
        assert_eq!(
            body.stance().place,
            stance_before.place,
            "the stance stands in place"
        );
        let (fly_after, live_after) = body.flywheel();
        assert_eq!(
            live_after, live_before,
            "the groove neither dies nor seeds in the dark"
        );
        assert_eq!(
            fly_after.meeting_ratio(),
            fly_before.meeting_ratio(),
            "the flywheel HOLDS — darkness exerts no torque"
        );
        assert_eq!(
            body.thoughts(),
            thoughts_before,
            "no thought completes behind the horizon"
        );
        // the circuit re-ignites: later light reads normally (the darkness was not absorbing).
        let mut responded = false;
        for &w in [b"my" as &[u8], b"mat", b"and", b"then", b"it"].iter() {
            let e = body.perceive(w, 137);
            responded |= e.thought_completed || e.thought_deposited;
        }
        assert!(
            responded,
            "the circuit reads on after the dark beat — the horizon is not absorbing"
        );
    }
}

/// ★ THE POOL RECUT GATE 1 — THE SAME LIGHT LANDS THE SAME OWN REGION (determinism at cpu grain;
/// the repeated-construction gate). One body, the same light twice into fresh own regions → the own
/// regions are BYTE-EQUAL (the felt series is a total function of the light — place-not-store).
#[test]
fn the_same_light_lands_the_same_own_region() {
    const AXIS: i64 = 1 << 8;
    let light: [&[u8]; 12] = [
        b"the", b"cat", b"sat", b"on", b"the", b"mat", b"the", b"cat", b"saw", b"the", b"rat",
        b"sit",
    ];
    let run = || -> std::vec::Vec<u32> {
        let (standing, mut own) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        {
            let mut body = ContinuingBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
            for &w in &light {
                body.perceive(w, 137);
            }
        }
        own
    };
    assert_eq!(
        run(),
        run(),
        "the same light lands the byte-identical own region (determinism, place-not-store)"
    );
}

/// ★ THE POOL RECUT GATE 2 — CO-PRESENT OWN REGIONS FOLD IN ANY ORDER (tooth 2 at body grain). Two
/// bodies over the SAME (empty) standing, different lights; integrating their own spools into standing
/// in EITHER order lands the byte-identical region because the one configuration fold declares
/// its grain from the whole multiset (§XXVIII: co-present emissions have no chronology).
#[test]
fn co_present_own_regions_fold_in_any_order() {
    const AXIS: i64 = 1 << 8;
    let light_a: [&[u8]; 8] = [
        b"the", b"cat", b"sat", b"on", b"the", b"mat", b"and", b"then",
    ];
    let light_b: [&[u8]; 8] = [b"an", b"old", b"dog", b"ran", b"to", b"see", b"the", b"rat"];
    let standing = regions(AXIS).0; // the shared pre-light form (empty — UNBORN everywhere)
    let fly = |light: &[&[u8]]| -> std::vec::Vec<u32> {
        let mut own = regions(AXIS).1;
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        {
            let mut body = ContinuingBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
            for &w in light {
                body.perceive(w, 137);
            }
        }
        own
    };
    let own_a = fly(&light_a);
    let own_b = fly(&light_b);

    let mut ab = standing.clone();
    integrate_configuration(&mut ab, &[&own_a, &own_b]);
    let mut ba = standing.clone();
    integrate_configuration(&mut ba, &[&own_b, &own_a]);
    assert_eq!(
        ab, ba,
        "co-present emissions integrate order-free in one configuration fold"
    );
}

/// ★ THE POOL RECUT GATE 4 — A LATER LIGHT IS DEFLECTED, A CO-PRESENT ONE IS NOT (the assembly's
/// central gate; §XXVIII the cone made structural). B flies its light over empty standing; while A
/// flies co-presently (A's deposits go to its OWN spool, never B's cone), B's decision stream is
/// IDENTICAL to B alone — a co-present emission stands outside B's cone for the whole light (tooth 4).
/// Then A's own spool integrates into standing and a fresh B flies it — B's stream DIFFERS: the later
/// light reads the integrated configuration and is DEFLECTED (later-light linkage — the deflection lives).
#[test]
fn a_later_light_is_deflected_a_co_present_one_is_not() {
    const AXIS: i64 = 1 << 8;
    let light_a: [&[u8]; 22] = [
        b"the", b"cat", b"sat", b"on", b"my", b"mat", b"and", b"then", b"it", b"ran", b"to",
        b"see", b"an", b"old", b"dog", b"who", b"was", b"far", b"too", b"shy", b"now", b"slept",
    ];
    let light_b = light_a; // B's light shares A's vocabulary — the grips overlap, so a linkage can form
    let fly_b = |standing: &[u32]| -> std::vec::Vec<bool> {
        let mut own = regions(AXIS).1;
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut body = ContinuingBody::over(standing, &mut own, AXIS, b"  ", 20, &mut carrier);
        light_b
            .iter()
            .map(|&w| body.perceive(w, 137).thought_completed)
            .collect()
    };

    let empty = regions(AXIS).0;
    let b_alone = fly_b(&empty);

    // A flies co-presently over the SAME empty standing — its deposits land in its OWN spool, never
    // in B's cone. B (reading empty standing) is therefore identical to B alone: the cone is honored.
    let own_a = {
        let mut own = regions(AXIS).1;
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        {
            let mut a = ContinuingBody::over(&empty, &mut own, AXIS, b"  ", 20, &mut carrier);
            for &w in &light_a {
                a.perceive(w, 137);
            }
        }
        own
    };
    let b_copresent = fly_b(&empty);
    assert_eq!(
        b_alone, b_copresent,
        "co-present: B's stream is unchanged — A's emission stands outside B's cone (tooth 4)"
    );

    // Now A's spool integrates into the standing form (the light's end) and a FRESH B flies it: the
    // later light reads the integrated configuration and is DEFLECTED.
    let mut standing_after = empty.clone();
    integrate_configuration(&mut standing_after, &[&own_a]);
    let b_later = fly_b(&standing_after);
    assert_ne!(
        b_alone, b_later,
        "a later light is deflected — A's integrated deposits bend B (later-light linkage; the deflection lives)"
    );
}

/// ★ OBSERVE THE THOUGHTS ON REAL CONVERSATION (W4 read — run by hand, `-- --ignored --nocapture`). The
/// swing's segmentation on real material, three-body against the length-honest coprime shuffle. The raw
/// cuts are rendered verbatim — the read is the topology of the cuts, never a scalar.
#[test]
#[ignore]
fn observe_the_thoughts_on_real_conversation() {
    const AXIS: i64 = 1 << 8;
    const TAKE: usize = 40000;
    let paths = [
        "../../holobrochos/diet/conv/001_6cd20671.txt",
        "../holobrochos/diet/conv/001_6cd20671.txt",
    ];
    let Some(data) = paths.iter().find_map(|p| std::fs::read(p).ok()) else {
        std::eprintln!("  (no conv corpus on disk — skipped)");
        return;
    };
    let text = &data[..data.len().min(TAKE)];
    let words: std::vec::Vec<&[u8]> = text
        .split(|&b| b == b' ' || b == b'\n' || b == b'\t' || b == b'\r')
        .filter(|w| w.len() >= 2)
        .collect();
    let n = words.len();
    let shuffled: std::vec::Vec<&[u8]> = (0..n).map(|i| words[(i * 7) % n]).collect();

    let read = |label: &str, stream: &[&[u8]]| {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut eyes = ContinuingBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        let mut cur: std::vec::Vec<std::string::String> = std::vec::Vec::new();
        let mut thoughts: std::vec::Vec<std::string::String> = std::vec::Vec::new();
        for &w in stream {
            let ev = eyes.perceive(w, 100);
            if ev.thought_completed && !cur.is_empty() {
                thoughts.push(cur.join(" "));
                cur.clear();
            }
            cur.push(std::string::String::from_utf8_lossy(w).into_owned());
        }
        std::eprintln!(
            "  {label}: {} words → {} thoughts",
            stream.len(),
            eyes.thoughts()
        );
        for t in thoughts.iter().take(18) {
            std::eprintln!("    «{t}»");
        }
    };
    read("REAL — conversation (diet/conv/001)", &words);
    read(
        "FOIL — the same words coprime-scattered (a worldline of its own)",
        &shuffled,
    );
}
