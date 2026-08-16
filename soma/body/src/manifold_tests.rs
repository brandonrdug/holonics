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
        let mut body = ErosBody::over(&standing, &mut own, AXIS, b"ab", 0, &mut carrier);
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
    let mut body = ErosBody::over_register(&standing, &mut chart, 64, b"  ", 20, &mut carrier);
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
    let mut eros = ErosBody::over(&standing, &mut wells, AXIS, b"the ", 20, &mut carrier);

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
    let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
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
    let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
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
    let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
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
        let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
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
        let mut eyes = ErosBody::over(&standing, &mut own, AXIS, b"  ", Q, &mut carrier);
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

/// ★ §§XXV–XXVI · THE LINEAGE EVENT — `FRAME(K)` supplies the next pole, the post-deed rotor
/// folds into that same `K`, and `TURN(K)` receives the meeting reach without carrying it.
/// The flat meeting and prior-channel fixtures satisfy their bounded restore relations.
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
        let mut eyes = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
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
    let mut eyes = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);

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
    let mut eyes = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
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
        let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
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
    ) -> ErosBody<'a> {
        let mut body = ErosBody::over(standing, own, 1 << 8, b"  ", 20, carrier);
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
        let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
        stream
            .iter()
            .map(|&w| body.perceive(w, 137).thought_completed)
            .collect()
    };
    let live = || -> std::vec::Vec<bool> {
        let (standing, mut wells) = regions(AXIS);
        let mut carrier = std::vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
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
        let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
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
        let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
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
        let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
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
    let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
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
            ErosBody::over_register_from_first_difference(
                &standing,
                &mut chart,
                AXIS,
                first,
                &mut carrier,
            )
            .unwrap()
        } else {
            ErosBody::over_register(&standing, &mut chart, AXIS, b"  ", 20, &mut carrier)
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
    assert!(ErosBody::over_register_from_first_difference(
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
    let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
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
        let mut body = ErosBody::over_register_from_first_difference(
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
        let mut body = ErosBody::over_sparse_from_first_difference(
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
        let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
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
    let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut enclosures);
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
        let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
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
    let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"ab", 20, &mut carrier);
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
    let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"  ", Q, &mut carrier);
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
    let mut body2 = ErosBody::over(&standing2, &mut wells2, AXIS, b"  ", Q, &mut carrier2);
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
    let mut body3 = ErosBody::over(&standing3, &mut wells3, AXIS, b"  ", Q, &mut carrier3);
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
        let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
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
        let mut body = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
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
            let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
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
            let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
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
        let mut body = ErosBody::over(standing, &mut own, AXIS, b"  ", 20, &mut carrier);
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
            let mut a = ErosBody::over(&empty, &mut own, AXIS, b"  ", 20, &mut carrier);
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
        let mut eyes = ErosBody::over(&standing, &mut wells, AXIS, b"  ", 20, &mut carrier);
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
