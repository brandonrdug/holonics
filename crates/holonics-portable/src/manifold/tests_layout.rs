use super::*;
use crate::soul::Chi;

struct MirrorWordSeam;

unsafe impl WordSeam for MirrorWordSeam {
    unsafe fn read_u32_unchecked(words: &[u32], at: usize) -> u32 {
        *words.get_unchecked(at)
    }

    unsafe fn store_u32_unchecked(_words: &mut [u32], _at: usize, _value: u32) {
        panic!("the node/face fixtures never store through their read face")
    }
}

struct TrapWordSeam;

unsafe impl WordSeam for TrapWordSeam {
    unsafe fn read_u32_unchecked(_words: &[u32], _at: usize) -> u32 {
        panic!("a short node/face row must not enter the seam")
    }

    unsafe fn store_u32_unchecked(_words: &mut [u32], _at: usize, _value: u32) {
        panic!("a short node/face row must not enter the seam")
    }
}

#[test]
fn the_live_header_is_exact_without_claiming_the_carrier_projection() {
    const AXIS: i64 = 1 << 6;
    let (standing, mut own) = regions(AXIS);
    let mut carrier = std::vec![0u32; 2 * ENCLOSURE_WORDS];
    let header;
    {
        let mut body = ContinuingBody::over(&standing, &mut own, AXIS, b"ab", 0, &mut carrier);
        for value in [13, 29, 17, 31] {
            body.live_relation_atom(Cog::lit(value), 0);
        }
        header = body.live_header(4);
    }
    assert_eq!(header.cursor(), 4);
    assert!(live_body_header_is_canonical(header.words()));
    assert_eq!(
        LiveBodyHeader::from_words_checked(header.words()),
        Some(header)
    );

    let mut malformed = *header.words();
    malformed[CARRIER_SUB_FLY_LIVE] = 2;
    assert!(LiveBodyHeader::from_words_checked(&malformed).is_none());
}

#[test]
#[should_panic(expected = "pending co-present checkpoint fits")]
fn the_pending_contact_hand_is_exactly_the_derived_register() {
    let _ = pending_control(PENDING_ENCLOSURE_CO_PRESENT, REGISTER + 1);
}

#[test]
fn node_and_face_cross_one_read_face_or_are_wholly_absent() {
    let node = Node {
        well: Cog::lit(-17),
        place: (Cog::lit(23), Cog::lit(-31)),
        len: 47,
    };
    let mut node_row = [9u32; NODE_WORDS + 2];
    let mut word = 0usize;
    while word < NODE_WORDS {
        node_row[1 + word] = node_packed_word(node, word);
        word += 1;
    }
    let read_node = unpack_node_with::<MirrorWordSeam>(&node_row, 1);
    assert_eq!(read_node.well, node.well);
    assert_eq!(read_node.place, node.place);
    assert_eq!(read_node.len, node.len);

    let face = Face {
        arrow: Arrow {
            reach: Cog::lit(5),
            aim: Cog::lit(-7),
            cross: Cog::lit(11),
        },
    };
    let mut face_row = [13u32; FACE_WORDS + 2];
    let mut face_word = 0usize;
    while face_word < FACE_WORDS {
        face_row[1 + face_word] = face_packed_word(face, face_word);
        face_word += 1;
    }
    assert_eq!(unpack_face_with::<MirrorWordSeam>(&face_row, 1), face);

    let short_node = [u32::MAX; NODE_WORDS - 1];
    let absent = unpack_node_with::<TrapWordSeam>(&short_node, 0);
    assert_eq!(absent.well, Cog::ZERO);
    assert_eq!(absent.place, (Cog::ZERO, Cog::ZERO));
    assert_eq!(absent.len, 0);
    let wrapped = unpack_node_with::<TrapWordSeam>(&short_node, usize::MAX);
    assert_eq!(wrapped.len, 0);

    let short_face = [u32::MAX; FACE_WORDS - 1];
    assert_eq!(
        unpack_face_with::<TrapWordSeam>(&short_face, 0),
        absent_face()
    );
    assert_eq!(
        unpack_face_with::<TrapWordSeam>(&short_face, usize::MAX),
        absent_face()
    );
}

/// §XXXII-c gate: the zero-extension moves every live cell byte-whole to its even-even fine
/// grip, leaves every other fine cell UNBORN, and re-grounds no founder.
#[test]
fn the_local_recast_moves_cells_by_zero_extension_byte_whole() {
    let old_axis = 2i64;
    let new_axis = 4i64;
    let mut old = std::vec![0u32; 4 * OWN_CELL_WORDS];
    // two live cells at grips 1 ⊕ 3 with distinct construction bytes
    for (grip, fill) in [(1usize, 0xA1u32), (3usize, 0xB7u32)] {
        let at = grip * OWN_CELL_WORDS;
        let mut word = 0usize;
        while word < OWN_CELL_WORDS {
            old[at + word] = fill.wrapping_add(word as u32);
            word += 1;
        }
        old[at + OWN_CELL_LIVE] = 1;
    }
    let mut new = std::vec![0u32; 16 * OWN_CELL_WORDS];
    zero_extend_own_cells(&old, &mut new, old_axis, new_axis);
    for old_grip in [1u32, 3u32] {
        let moved = crate::chart::zero_extend_grip(old_grip, 2, 4) as usize;
        let from = old_grip as usize * OWN_CELL_WORDS;
        let to = moved * OWN_CELL_WORDS;
        assert_eq!(
            &new[to..to + OWN_CELL_WORDS],
            &old[from..from + OWN_CELL_WORDS],
            "the moved cell crosses byte-whole"
        );
    }
    let moved: std::vec::Vec<usize> = [1u32, 3u32]
        .iter()
        .map(|&g| crate::chart::zero_extend_grip(g, 2, 4) as usize)
        .collect();
    let mut grip = 0usize;
    while grip < 16 {
        if !moved.contains(&grip) {
            let at = grip * OWN_CELL_WORDS;
            assert!(
                new[at..at + OWN_CELL_WORDS].iter().all(|&w| w == 0),
                "an unmoved fine cell stays UNBORN"
            );
        }
        grip += 1;
    }
}

#[test]
fn the_reserved_local_recast_is_the_fresh_chart_without_making_capacity_a_gauge() {
    const CAPACITY: usize = 8 * 8;
    let mut active = std::vec![0u32; CAPACITY * OWN_CELL_WORDS];
    for (grip, fill) in [(0usize, 0x31u32), (1, 0x57), (3, 0x9b)] {
        let at = grip * OWN_CELL_WORDS;
        let mut word = 0usize;
        while word < OWN_CELL_WORDS {
            active[at + word] = fill.wrapping_add(word as u32);
            word += 1;
        }
        active[at + OWN_CELL_LIVE] = 1;
    }
    let birth = active.clone();

    let mut expected_four = std::vec![0u32; CAPACITY * OWN_CELL_WORDS];
    zero_extend_own_cells(
        &birth[..4 * OWN_CELL_WORDS],
        &mut expected_four[..16 * OWN_CELL_WORDS],
        2,
        4,
    );
    assert!(zero_extend_own_cells_in_place_with::<SliceWordSeam>(
        &mut active,
        0,
        CAPACITY,
        2,
        4,
    ));
    assert_eq!(
        active, expected_four,
        "unused reservation words have no face on the accepted axis-four chart"
    );

    let mut expected_eight = std::vec![0u32; CAPACITY * OWN_CELL_WORDS];
    zero_extend_own_cells(
        &expected_four[..16 * OWN_CELL_WORDS],
        &mut expected_eight,
        4,
        8,
    );
    assert!(zero_extend_own_cells_in_place_with::<SliceWordSeam>(
        &mut active,
        0,
        CAPACITY,
        4,
        8,
    ));
    assert_eq!(
        active, expected_eight,
        "successive carries compose byte-whole"
    );

    let mut expected_narrow = std::vec![0u32; CAPACITY * OWN_CELL_WORDS];
    narrow_own_cells(
        &expected_eight,
        &mut expected_narrow[..16 * OWN_CELL_WORDS],
        8,
        4,
    );
    assert!(narrow_own_cells_in_place_with::<SliceWordSeam>(
        &mut active,
        0,
        CAPACITY,
        8,
        4,
    ));
    assert_eq!(
        active, expected_narrow,
        "the borrow is the exact in-place inverse section"
    );

    let before_wall = active.clone();
    assert!(!zero_extend_own_cells_in_place_with::<SliceWordSeam>(
        &mut active,
        0,
        16,
        4,
        8,
    ));
    assert_eq!(
        active, before_wall,
        "a reservation wall rejects before mutation"
    );

    let mut off_section = std::vec![0u32; CAPACITY * OWN_CELL_WORDS];
    off_section[OWN_CELL_WORDS + OWN_CELL_LIVE] = 1;
    let malformed = off_section.clone();
    assert!(!narrow_own_cells_in_place_with::<SliceWordSeam>(
        &mut off_section,
        0,
        CAPACITY,
        4,
        2,
    ));
    assert_eq!(
        off_section, malformed,
        "an off-section survivor rejects before any inverse row moves"
    );
}

/// §XXXII-c gate: the register posture is born at rank zero, widens only at its own carry
/// events, never consults the light's extent, and keeps merged history merged — a founded
/// coarse cell continues to deepen at its zero-extended grip while a genuinely new arrival
/// after the carry grounds at the accepted finer hand.
#[test]
fn the_register_chart_is_born_at_zero_and_carries_on_its_own_arrivals() {
    struct VecChart {
        words: std::vec::Vec<u32>,
        recasts: usize,
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
            self.recasts += 1;
        }
    }
    let standing = std::vec![0u32; 64 * 64 * FORM_WORDS];
    let mut chart = VecChart {
        words: std::vec![0u32; OWN_CELL_WORDS],
        recasts: 0,
    };
    let mut carrier = std::vec![0u32; 4 * ENCLOSURE_WORDS];
    let mut body =
        ContinuingBody::over_register(&standing, &mut chart, 64, b"  ", 20, &mut carrier);
    assert_eq!(
        body.own_axis(),
        1,
        "the chart is born at the rank-zero seed"
    );
    let light = b"the register widens only at its own carry events, never at a chosen extent";
    let mut cursor = 1usize;
    while cursor < light.len() {
        body.live_atom(light[cursor - 1], light[cursor], 3);
        cursor += 1;
    }
    body.flush_dark();
    let final_axis = body.own_axis();
    drop(body);
    assert!(
        final_axis > 1 && (final_axis & (final_axis - 1)) == 0,
        "arrivals carried the chart to a wider dyadic hand"
    );
    assert_eq!(
        chart.words.len(),
        (final_axis * final_axis) as usize * OWN_CELL_WORDS,
        "the boundary supplied exactly the accepted rank's words"
    );
    assert!(chart.recasts > 0, "the digit crossed the boundary seam");
    // every live cell's grip is its founder's grounding at one dyadic rank, zero-extended —
    // merged coarse history stays merged; nothing was re-grounded.
    let cells = (final_axis * final_axis) as usize;
    let mut live = 0usize;
    let mut local = 0usize;
    while local < cells {
        let at = local * OWN_CELL_WORDS;
        if chart.words[at + OWN_CELL_LIVE] != 0 {
            live += 1;
            let position = own_cell_position(&chart.words, at);
            let mut holds = false;
            let mut rank_axis = 1i64;
            while rank_axis <= final_axis {
                let grounded = place::ground(position, rank_axis);
                if crate::chart::zero_extend_grip(grounded, rank_axis as u32, final_axis as u32)
                    == local as u32
                {
                    holds = true;
                    break;
                }
                rank_axis <<= 1;
            }
            assert!(
                holds,
                "a live cell is one founding grounding zero-extended whole"
            );
        }
        local += 1;
    }
    assert!(live > 1, "the light founded plural distinct grips");
}

/// THE BREATH (Brandon's ruling, 2026-07-10): the register chart shrinks as well as grows.
/// A pure-ride deposit grows the chart at its arrive/carry; the exact opposite deposit
/// annihilates the cell (no fiber stands — nothing winds), the register departs, the borrow
/// retires the digit, and the fully-vacated chart returns to the rank-zero seed BYTE-IDENTICAL
/// to birth. Growth after annihilation repeats exactly — no ratchet, no knob.
#[test]
fn the_register_chart_breathes_grow_and_shrink_are_one_law() {
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
    let ride = |same: i64, other: i64| FeltTerm {
        chi: Chi {
            same: Cog::lit(same),
            other: Cog::lit(other),
        },
        winding: WindingQuantum::None,
    };
    let standing = std::vec![0u32; 16 * 16 * FORM_WORDS];
    let mut chart = VecChart {
        words: std::vec![0u32; OWN_CELL_WORDS],
    };
    let born = chart.words.clone();
    let position = wind(b"the breath");
    {
        let mut medium = Medium::over_register(&standing, &mut chart, 16);
        // GROW: the first arrival carries the rank-zero seed (occupancy 0→1 walks hand(1)).
        assert!(medium.deposit_at(position, ride(3, 4)));
        assert_eq!(
            medium.own_axis, 2,
            "the first arrival births the first digit"
        );
        assert_eq!(medium.register.occupancy, 1);
        let grown = medium.own().to_vec();
        // SHRINK: the exact opposite ride annihilates the cell — resultant cancels, no
        // fiber stands. The register departs, occupancy 1→0 walks OUT of hand(1) at axis 2,
        // the digit retires, and the vacated chart narrows to the rank-zero seed.
        assert!(medium.deposit_at(position, ride(-3, -4)));
        assert_eq!(
            medium.own_axis, 1,
            "full annihilation returns the chart to rank zero"
        );
        assert_eq!(medium.register.occupancy, 0);
        assert_ne!(
            grown,
            medium.own(),
            "the grown chart was wider than the seed"
        );
        // THE GAUGE: the post-annihilation chart is byte-identical to birth, and growth
        // repeats exactly — the same next deposit cannot tell the chart ever lived.
        assert_eq!(medium.own(), born.as_slice());
        assert!(medium.deposit_at(position, ride(3, 4)));
        assert_eq!(medium.own_axis, 2);
        assert_eq!(
            medium.own(),
            grown.as_slice(),
            "regrowth is exact — no ratchet"
        );
        assert_eq!(
            (medium.releases, medium.narrows),
            (1, 1),
            "the breath's boundary face counts the release and the retired digit"
        );
    }
    // A cell with ANY standing fiber can never release: winding cannot be un-deposited.
    let mut wound = VecChart {
        words: std::vec![0u32; OWN_CELL_WORDS],
    };
    {
        let mut medium = Medium::over_register(&standing, &mut wound, 16);
        assert!(medium.deposit_at(
            position,
            FeltTerm {
                chi: Chi {
                    same: Cog::lit(3),
                    other: Cog::lit(4),
                },
                winding: WindingQuantum::ThisWay,
            }
        ));
        assert!(medium.deposit_at(
            position,
            FeltTerm {
                chi: Chi {
                    same: Cog::lit(-3),
                    other: Cog::lit(-4),
                },
                winding: WindingQuantum::ThatWay,
            }
        ));
        assert_eq!(
            medium.register.occupancy, 1,
            "a wound cell stands through cancellation"
        );
        assert_eq!(medium.own_axis, 2, "the fiber holds the chart open");
        assert_eq!(
            (medium.releases, medium.narrows),
            (0, 0),
            "a wound cell's cancellation is no release — the face stays silent"
        );
    }
}

/// THE BREATH'S CASCADE (`FORMULA §XXXVI` — the width changes at the events; the borrow
/// completes when the barrier clears). The named shape from the safety audit: a departure
/// crosses the retiring tooth while an off-section survivor stands — the narrow is lawfully
/// blocked (the excited compound configuration: wide axis ⊕ low occupancy, standing state,
/// no flag anywhere) — and the LATER departure that clears the barrier cascades the
/// retirement through every digit the configuration affords, in ONE event, even though that
/// departure's own transition produces no borrow (the lost borrow of the old single-shot
/// law). The narrowed chart is PATH-INDEPENDENT: emptiness arriving by different departure
/// orders lands byte-identical standing — the state decides, so the path must not matter.
#[test]
fn the_borrow_cascades_at_the_event_that_clears_the_barrier() {
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
    let ride = |same: i64, other: i64| FeltTerm {
        chi: Chi {
            same: Cog::lit(same),
            other: Cog::lit(other),
        },
        winding: WindingQuantum::None,
    };
    let standing = std::vec![0u32; 16 * 16 * FORM_WORDS];
    let born = std::vec![0u32; OWN_CELL_WORDS];

    // The three positions, located by their section faces (wind is a pure construction —
    // the loops merely find candidates whose banding realizes the named shape):
    //   p1 — founds at axis 2 and re-grounds COINCIDENT with its own zero-extension at
    //        axis 4, so its later annihilator lands on the moved cell (the banding law puts
    //        every such position at the one axis-2 grip whose extension is even-even);
    //   p2 — founds fresh THROUGH the carry, landing OFF the retiring section (the banding
    //        law makes every fresh post-carry founder off-section): THE BARRIER;
    //   p3 — founds fresh at the standing axis 4 ON the section (a direct axis-4 arrival).
    let find = |tag: &[u8], want: &dyn Fn(Place) -> bool| -> Place {
        let mut salt = 0u32;
        while salt < 65536 {
            let mut bytes = std::vec::Vec::from(tag);
            bytes.extend_from_slice(&salt.to_le_bytes());
            let p = wind(&bytes);
            if want(p) {
                return p;
            }
            salt += 1;
        }
        panic!(
            "no position with the needed banding within the search: {}",
            core::str::from_utf8(tag).unwrap_or("?")
        );
    };
    let p1 = find(b"cascade p1 ", &|p| {
        place::ground(p, 4) == crate::chart::zero_extend_grip(place::ground(p, 2), 2, 4)
    });
    let g1 = place::ground(p1, 2);
    let e1 = crate::chart::zero_extend_grip(g1, 2, 4);
    let p2 = find(b"cascade p2 ", &|p| {
        place::ground(p, 2) != g1
            && crate::chart::zero_extended_source(place::ground(p, 4), 2, 4).is_none()
    });
    let p3 = find(b"cascade p3 ", &|p| {
        place::ground(p, 4) != e1
            && crate::chart::zero_extended_source(place::ground(p, 4), 2, 4).is_some()
    });

    // ORDER A — the audit's named shape, end to end.
    {
        let mut chart = VecChart {
            words: born.clone(),
        };
        let mut medium = Medium::over_register(&standing, &mut chart, 16);
        assert!(medium.deposit_at(p1, ride(3, 4)));
        assert!(medium.deposit_at(p2, ride(3, 4)));
        assert!(medium.deposit_at(p3, ride(3, 4)));
        assert_eq!((medium.own_axis, medium.register.occupancy), (4, 3));
        // A departure that crosses no tooth: the cascade's register face declines cheaply.
        assert!(medium.deposit_at(p1, ride(-3, -4)));
        assert_eq!((medium.own_axis, medium.register.occupancy), (4, 2));
        assert_eq!(medium.narrows, 0);
        // The borrow's own crossing (2 -> 1 walks out of the retiring tooth) — BLOCKED by
        // the off-section survivor: the excited compound configuration, no flag anywhere.
        assert!(medium.deposit_at(p3, ride(-3, -4)));
        assert_eq!(
            (medium.own_axis, medium.register.occupancy),
            (4, 1),
            "the off-section survivor is the barrier — the chart lawfully keeps its width"
        );
        assert_eq!(medium.narrows, 0);
        // The barrier clears. THIS transition (1 -> 0) produces no borrow of its own — the
        // old single-shot law lost it forever — and the cascade completes the relaxation
        // through BOTH standing digits in one event.
        assert!(medium.deposit_at(p2, ride(-3, -4)));
        assert_eq!(
            (medium.own_axis, medium.register.occupancy),
            (1, 0),
            "the event that clears the barrier cascades the retirement"
        );
        assert_eq!(
            (medium.releases, medium.narrows),
            (3, 2),
            "one event retired two digits — the cascade, not a second borrow"
        );
        assert_eq!(
            medium.own(),
            born.as_slice(),
            "the vacated chart is the seed again"
        );
    }

    // ORDERS B and C — the same emptiness by different departure orders: the standing
    // configuration decides, so the surviving charts are byte-identical (and each carries
    // p1's cell back at its own axis-2 grip — the narrowing is the exact inverse).
    let survivor = |first: Place, second: Place| -> std::vec::Vec<u32> {
        let mut chart = VecChart {
            words: born.clone(),
        };
        let mut medium = Medium::over_register(&standing, &mut chart, 16);
        assert!(medium.deposit_at(p1, ride(3, 4)));
        assert!(medium.deposit_at(p2, ride(3, 4)));
        assert!(medium.deposit_at(p3, ride(3, 4)));
        assert!(medium.deposit_at(first, ride(-3, -4)));
        assert!(medium.deposit_at(second, ride(-3, -4)));
        assert_eq!((medium.own_axis, medium.register.occupancy), (2, 1));
        assert_eq!(medium.narrows, 1);
        let at = g1 as usize * OWN_CELL_WORDS;
        assert_eq!(
            medium.own()[at + OWN_CELL_LIVE],
            1,
            "the survivor rode home whole"
        );
        let standing_survivor = medium.own().to_vec();
        // Finish: the survivor's own release cascades the chart to the seed.
        assert!(medium.deposit_at(p1, ride(-3, -4)));
        assert_eq!((medium.own_axis, medium.register.occupancy), (1, 0));
        assert_eq!(medium.own(), born.as_slice());
        standing_survivor
    };
    let b = survivor(p3, p2);
    let c = survivor(p2, p3);
    assert_eq!(b, c, "emptiness by different orders lands byte-identical");
}

/// A fresh founder can land on the wider chart's zero section without being the
/// zero-extension of its OWN narrower grounding. Retirement therefore owes the whole
/// construction, not section membership alone. `wind(&[0, 2])` is a deterministic
/// 4→8 witness: it grounds at grip 10 in axis 4 and grip 48 in axis 8, while grip 48's section
/// source is 12. The first later departure must keep axis 8 so the founder remains meetable at
/// grip 48; only that founder's own annihilation clears the construction barrier.
#[test]
fn retirement_requires_the_founder_to_rederive_its_section_source() {
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
    let ride = |same: i64, other: i64| FeltTerm {
        chi: Chi {
            same: Cog::lit(same),
            other: Cog::lit(other),
        },
        winding: WindingQuantum::None,
    };
    let standing = std::vec![0u32; 16 * 16 * FORM_WORDS];
    let mut chart = VecChart {
        words: std::vec![0u32; 4 * 4 * OWN_CELL_WORDS],
    };

    // Seven construction-clean axis-4 founders make a lawful pre-carry configuration. Their
    // common nonzero base and four turns furnish distinct lawful places whose axis-8 grips are
    // the zero-extensions of their axis-4 grips. Grips 10 and 12 stay empty for the witness.
    let base = Cog::lit(1).turn_up(5);
    let supports = [
        (base, base.turned(1)),
        (base, base.turned(2)),
        (base, base.turned(3)),
        (base.turned(1), base),
        (base.turned(1), base.turned(1)),
        (base.turned(1), base.turned(3)),
        (base.turned(2), base),
    ];
    let support_form = RegionalForm::UNBORN.deposit(ride(3, 4));
    let mut occupied = [false; 16];
    for &position in &supports {
        let grip = place::ground(position, 4);
        assert_ne!(grip, 10);
        assert_ne!(grip, 12);
        assert!(
            !occupied[grip as usize],
            "each support founds a distinct axis-4 grip"
        );
        occupied[grip as usize] = true;
        assert_eq!(
            place::ground(position, 8),
            crate::chart::zero_extend_grip(grip, 4, 8),
            "each support founder crosses the 4→8 section construction-whole"
        );
        let at = grip as usize * OWN_CELL_WORDS;
        chart.words[at + OWN_CELL_LIVE] = 1;
        let mut word = 0usize;
        while word < COG_WORDS {
            chart.words[at + OWN_CELL_POSITION + word] = cog_packed_word(position.0, word);
            chart.words[at + OWN_CELL_POSITION + COG_WORDS + word] =
                cog_packed_word(position.1, word);
            word += 1;
        }
        support_form.pack(&mut chart.words, at + OWN_CELL_FORM);
    }

    let witness = wind(&[0, 2]);
    let narrow_grip = place::ground(witness, 4);
    let wide_grip = place::ground(witness, 8);
    let section_source = crate::chart::zero_extended_source(wide_grip, 4, 8);
    assert_eq!((narrow_grip, wide_grip, section_source), (10, 48, Some(12)));
    assert_ne!(section_source, Some(narrow_grip));

    let mut medium = Medium {
        standing: StandingStore::Dense {
            words: &standing,
            axis: 16,
        },
        own: OwnStore::Register(&mut chart),
        own_axis: 4,
        founded_cells: true,
        register: crate::chart::Register {
            axis: 4,
            occupancy: supports.len() as u64,
        },
        releases: 0,
        narrows: 0,
        resource_refused: false,
    };

    // The eighth founder forces 4→8, then remains fresh at the wider grip because its section
    // source (12) was empty. This is the reachable configuration the former section-only read
    // narrowed incorrectly.
    assert!(medium.deposit_at(witness, ride(5, 6)));
    assert_eq!((medium.own_axis, medium.register.occupancy), (8, 8));
    let witness_at = wide_grip as usize * OWN_CELL_WORDS;
    assert_eq!(medium.own()[witness_at + OWN_CELL_LIVE], 1);
    assert_eq!(own_cell_position(medium.own(), witness_at), witness);

    // A support departure walks occupancy below hand(4), but the witness's construction is the
    // barrier: narrowing it to section source 12 would make its own grip-10 founder unreachable.
    assert!(medium.deposit_at(supports[0], ride(-3, -4)));
    assert_eq!((medium.own_axis, medium.register.occupancy), (8, 7));
    assert_eq!((medium.releases, medium.narrows), (1, 0));
    let rederived = place::ground(witness, medium.own_axis) as usize * OWN_CELL_WORDS;
    assert_eq!(rederived, witness_at);
    assert_eq!(medium.own()[rederived + OWN_CELL_LIVE], 1);
    assert_eq!(own_cell_position(medium.own(), rederived), witness);

    // The witness meets its own founder at the re-derived wider grip and annihilates there.
    // With that construction barrier gone, the six surviving support founders retire 8→4
    // losslessly in the same departure event.
    assert!(medium.deposit_at(witness, ride(-5, -6)));
    assert_eq!((medium.own_axis, medium.register.occupancy), (4, 6));
    assert_eq!((medium.releases, medium.narrows), (2, 1));
    assert_eq!(
        medium.own()[narrow_grip as usize * OWN_CELL_WORDS + OWN_CELL_LIVE],
        0,
        "the annihilated founder leaves no orphan at its narrower re-derived grip"
    );
}

/// TWO zeroed felt-series regions — pre-light STANDING ⊕ this body's OWN spool, each
/// `FORM_WORDS`-strided over the axis' square (`§XXVIII`, the two-region cone). The standing
/// region is empty (UNBORN everywhere) unless a gate integrates deposits into it.

fn regions(axis: i64) -> (std::vec::Vec<u32>, std::vec::Vec<u32>) {
    let n = (axis * axis) as usize * FORM_WORDS;
    (std::vec![0u32; n], std::vec![0u32; n])
}
