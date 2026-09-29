//! Holonic Encoding (`hnn::encoding`, THE_REBUILD U6, the pins of September 29): the squares
//! `D E = ρ`, `E T = U E` and the injection square, exact on the known-truth terrains, with the
//! founded dimension equal to the emission's Hankel rank on the reached orbit (acceptance 1); the
//! moment chart's reduced recurrence joined to `SourceMoment`; the separator; the passage's own
//! transports (the terrains read as passages with no transport declared, the moment of the passage
//! chart, the charged founding); the founded port chart, placed at first arrival and blind to the
//! codec's values, and every reader of it stepping by the founded classes.

use std::collections::BTreeSet;

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::support::{Draw, contact, ring};
use crate::compression::landmark::context::StopPrior;
use crate::hnn::encoding::{
    ContextClasses, Encoding, EncodingError, PassageChart, PassageFounding, found_passage,
    found_ports,
};
use crate::hnn::field::{
    CribDeclaration, Current, Field, FieldDeclaration, ReceiverDeclaration, ring_digit,
};
use crate::hnn::moment::SourceMoment;
use crate::holarchy::terrain::{Grating, Moire, MoireClass, RotorCrib};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::dot;
use crate::ratio::{Rat, integer, rat};
use crate::receiver::population::Closure;

/// **The emission's observable dimension, computed from the terrain's own cells**: the rank of the
/// block Hankel matrix `[y_(i+j)]` over `blocks` block rows and columns, `y_t` the one-hot of cell
/// `t` over `classes` classes (the cells hold at least `2 blocks − 1` ticks).
fn hankel_rank(cells: &[usize], classes: usize, blocks: usize) -> usize {
    assert!(cells.len() + 1 >= 2 * blocks, "the emission covers the Hankel window");
    let rows = (0..blocks)
        .flat_map(|i| {
            (0..classes).map(move |class| {
                (0..blocks)
                    .map(|j| {
                        if cells[i + j] == class {
                            Rat::one()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect::<Vec<_>>()
            })
        })
        .collect();
    ExactRatMatrix::new(rows).unwrap().rank().unwrap()
}

/// The one-hot of a class.
fn one_hot(classes: usize, class: usize) -> Vec<Rat> {
    (0..classes)
        .map(|c| if c == class { Rat::one() } else { Rat::zero() })
        .collect()
}

/// **The encoding reads the emission**: from the opening, `D E Tᵗ x_0` is the one-hot of cell `t`
/// for every emitted cell (Lean `Birth.founded_reads_iterate`), carried in the founded chart alone
/// by `U` (`E Tᵗ = Uᵗ E`).
fn reads_the_emission(chart: &PassageChart, encoding: &Encoding, cells: &[usize]) {
    let classes = chart.coupling().len();
    let transport = &chart.transports()[0];
    let mut state = chart.openings()[0].clone();
    let mut founded = encoding.encode(&state).unwrap();
    let u = encoding.transport(0).unwrap();
    for (t, &cell) in cells.iter().enumerate() {
        assert_eq!(encoding.encode(&state).unwrap(), founded, "E Tᵗ = Uᵗ E at tick {t}");
        assert_eq!(
            encoding.readout().apply(&founded).unwrap(),
            one_hot(classes, cell),
            "D E Tᵗ x_0 reads cell {t}"
        );
        state = transport.apply(&state).unwrap();
        founded = u.apply(&founded).unwrap();
    }
}

/// **The founding on the whole chart alone** (Birth's observability, no reached restriction): the
/// receiving forms closed under the adjoints on the whole chart.
fn observability_only(chart: &PassageChart) -> usize {
    let forms: Vec<Vec<Rat>> = chart
        .coupling()
        .iter()
        .filter(|form| form.iter().any(|value| !value.is_zero()))
        .cloned()
        .collect();
    let (separator, held) = forms.split_last().unwrap();
    Closure::found(chart.chart(), chart.transports(), held, separator)
        .unwrap()
        .dimension()
}

/// **Acceptance 1, the moiré.** Rates `1/3, 1/4` (one orbit of the joint torus) and `1/4, 1/6`
/// (two orbits) read by their parity color: the squares close exactly, the founded dimension is the
/// emission's Hankel rank, and the encoding reads every emitted cell. On the two-orbit torus the
/// observability-only founding is read beside it.
#[test]
fn the_moire_founds_its_hankel_rank_on_the_reached_orbit() {
    for (rates, phases) in [
        (vec![(1u64, 3u64), (1, 4)], vec![2u64, 1]),
        (vec![(1, 4), (1, 6)], vec![1, 5]),
        (vec![(1, 4), (3, 5)], vec![3, 0]),
    ] {
        let gratings: Vec<Grating> = rates
            .iter()
            .zip(&phases)
            .map(|(&(p, q), &c)| Grating::new(p, q, c).unwrap())
            .collect();
        let moire = Moire::new(gratings.clone(), MoireClass::Parity).unwrap();
        let chart = PassageChart::moire(&gratings, MoireClass::Parity).unwrap();
        let encoding = Encoding::found(&chart).unwrap();
        let squares = encoding.squares(&chart).unwrap();
        assert_eq!(squares.states, encoding.reached());
        let blocks = chart.chart() + 1;
        let cells = moire.emit(2 * blocks);
        assert_eq!(
            encoding.dimension(),
            hankel_rank(&cells, 2, blocks),
            "the founded dimension is the emission's Hankel rank at rates {rates:?}"
        );
        reads_the_emission(&chart, &encoding, &cells);
        assert!(observability_only(&chart) >= encoding.dimension());
        if rates == [(1, 4), (1, 6)] {
            // Two orbits of the joint torus of 24 states: the reached orbit is one of 12.
            assert_eq!(encoding.reached(), 12);
        }
    }
}

/// **Acceptance 1, the copy terrain.** A closing rotor ring of period 8 whose nodes hold drawn cells
/// over `|A| = 4`, and one whose stored word repeats with period 4: the squares close exactly, the
/// founded dimension is the emission's Hankel rank, and the encoding reads every emitted cell.
#[test]
fn the_copy_ring_founds_its_hankel_rank_on_the_reached_orbit() {
    let mut draw = Draw::new(20260929);
    let drawn: Vec<usize> = (0..8).map(|_| draw.below(4)).collect();
    let repeated: Vec<usize> = [0usize, 2, 1, 2].repeat(2);
    for stored in [drawn, repeated] {
        let chart = PassageChart::copy(&stored, 4).unwrap();
        let encoding = Encoding::found(&chart).unwrap();
        encoding.squares(&chart).unwrap();
        let blocks = chart.chart() + 1;
        let cells: Vec<usize> = (0..2 * blocks).map(|t| stored[t % stored.len()]).collect();
        assert_eq!(
            encoding.dimension(),
            hankel_rank(&cells, 4, blocks),
            "the founded dimension is the copy's Hankel rank for {stored:?}"
        );
        assert!(encoding.reached() <= stored.len());
        // The whole chart is observable (32); the reached orbit is what the founding keeps.
        assert!(observability_only(&chart) > encoding.dimension());
        reads_the_emission(&chart, &encoding, &cells);
    }
}

/// A declared field of rings of periods 5 and 7 (locks `{0, 1, 2}` and `{0, 3, 5}`, so a crib's
/// cells step its rings), one contact, `|A| = 7`: the crib's field, with the codec's residue chart
/// (its codes are the second ring's ports).
fn crib_field() -> Field {
    Field::declare(
        FieldDeclaration {
            rings: vec![ring(5, vec![0, 1, 2]), ring(7, vec![0, 3, 5])],
            contacts: vec![contact(0, 1, 5, 2)],
            loops: Vec::new(),
            sources: vec![0],
            offsets: vec![1],
            alphabet: 7,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 1,
                aperture: 1,
                tolerance: rat(1, 16),
                depth: 2,
                prior: StopPrior::half(),
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

/// **Acceptance 1, the rotor crib.** On ring 0 (`d = 5`) and on ring 1 (`d = 7`, read under ring 0's
/// carries) of a declared field, under four drawn keys and plugboards each: the squares close
/// exactly, the founded dimension is the Hankel rank of the crib `holarchy::terrain::rotor_crib`
/// produced, and the encoding reads every crib cell.
#[test]
fn the_rotor_crib_founds_its_hankel_rank_on_the_reached_orbit() {
    let field = crib_field();
    let mut draw = Draw::new(29);
    let draws = [(0usize, vec![0u64, 0]), (1, vec![3, 2])]
        .into_iter()
        .flat_map(|draw| std::iter::repeat_n(draw, 4));
    for (ring, configurations) in draws {
        let chart_states = 5 * 7usize.pow(u32::from(ring == 1)) * [5usize, 7][ring];
        let crib = RotorCrib::draw(&field, ring, &configurations, 2 * chart_states + 2, &mut draw)
            .unwrap();
        let chart = PassageChart::crib(
            &field,
            ring,
            crib.truth.key,
            &crib.truth.board,
            &configurations,
            crib.truth.start,
        )
        .unwrap();
        assert_eq!(chart.chart(), chart_states);
        let encoding = Encoding::found(&chart).unwrap();
        encoding.squares(&chart).unwrap();
        let classes = field.ring(ring).period() as usize;
        assert_eq!(
            encoding.dimension(),
            hankel_rank(&crib.cells, classes, chart.chart() + 1),
            "the founded dimension is the crib's Hankel rank on ring {ring}"
        );
        reads_the_emission(&chart, &encoding, &crib.cells);
        // Birth's observability alone exceeds the emission here; the reached restriction meets it.
        assert!(observability_only(&chart) > encoding.dimension());
    }
}

/// **The moment chart carries the injection square and the reduced recurrence** (Lean
/// `HNN/Encoding.{injection_square, encoding_reduced_recurrence}`): on a source ring's moment chart
/// the squares hold for every admitted advance and every cell, and a drawn passage's moment, stepped
/// by the field's own selective clock, is the founded chart's reduced recurrence `z ← U_t z + J e_x`;
/// the chart's rotating-frame counts are `SourceMoment`'s phase counts carried to the lift.
#[test]
fn the_moment_chart_runs_the_reduced_recurrence_of_the_source_moment() {
    let field = crib_field();
    let chart = PassageChart::moment(&field, 0).unwrap();
    let encoding = Encoding::found(&chart).unwrap();
    let squares = encoding.squares(&chart).unwrap();
    assert_eq!(squares.cells, field.alphabet());
    assert_eq!(squares.transports, 3);
    assert_eq!(encoding.dimension(), chart.chart());
    let mut draw = Draw::new(5);
    let cells: Vec<usize> = (0..200).map(|_| draw.below(field.alphabet())).collect();
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    let mut state = vec![Rat::zero(); chart.chart()];
    let mut driven = Vec::new();
    for &cell in &cells {
        let mut probe = current.clone();
        let ticks = usize::from(probe.step(&field, cell).unwrap().ticks[0]);
        moment.ingest(&field, &mut current, &[cell]).unwrap();
        assert_eq!(current.lift(), probe.lift());
        state = chart.transports()[ticks].apply(&state).unwrap();
        for (entry, injected) in state.iter_mut().zip(&chart.injection()[cell]) {
            *entry += injected;
        }
        driven.push((ticks, cell));
    }
    assert_eq!(
        encoding.encode(&state).unwrap(),
        encoding.reduced_moment(&driven).unwrap()
    );
    // The rotating frame is the source frame carried to the lift: m[j, x] = M[τ − j, x].
    let d = field.ring(0).period() as usize;
    let a = field.alphabet();
    let tau = ring_digit(&field.ring(0).clock_at(&current.lift()[0]).unwrap()) as usize;
    for j in 0..d {
        let counts = moment.phase_counts(0, (tau + d - j) % d).unwrap();
        for x in 0..a {
            assert_eq!(state[j * a + x], Rat::from_integer(BigInt::from(counts[x])));
        }
    }
}

/// **A separator where a reading does not factor** (Lean `HNN/Encoding.encoding_separator`): on the
/// repeated copy word, a state indicator of the chart is no founded reading, and the separator is a
/// reached direction the encoding merges on which it reads nonzero; a founded reading has none.
#[test]
fn a_reading_that_does_not_factor_returns_its_separator() {
    let stored: Vec<usize> = [0usize, 2, 1, 2].repeat(2);
    let chart = PassageChart::copy(&stored, 4).unwrap();
    let encoding = Encoding::found(&chart).unwrap();
    let fibre = encoding.fibre().unwrap();
    assert_eq!(encoding.reached() - encoding.dimension(), fibre.len());
    for direction in &fibre {
        assert!(encoding.encode(direction).unwrap().iter().all(Zero::is_zero));
    }
    assert!(encoding.separator(&chart.coupling()[2]).unwrap().is_none());
    // Node 1's cell 2: the reached orbit carries it, and the founded readings may merge it.
    let mut indicator = vec![Rat::zero(); chart.chart()];
    indicator[4 + 2] = Rat::one();
    match encoding.separator(&indicator).unwrap() {
        Some(direction) => {
            assert!(!dot(&indicator, &direction).is_zero());
            assert!(encoding.encode(&direction).unwrap().iter().all(Zero::is_zero));
        }
        None => assert!(fibre.iter().all(|v| dot(&indicator, v).is_zero())),
    }
}

// -------------------------------------------------------------------------------------------
// the passage's own transports

/// **The periodic part of an emission**: the least start and, from it, the least period `p` with
/// `cells[t + p] = cells[t]` at every `t` inside the emission (two periods at least).
fn periodic_part(cells: &[usize]) -> (usize, usize) {
    for start in 0..cells.len() {
        let rest = cells.len() - start;
        for period in 1..=rest / 2 {
            if (start..cells.len() - period).all(|t| cells[t + period] == cells[t]) {
                return (start, period);
            }
        }
    }
    panic!("the emission covers two periods of its periodic part");
}

/// **The count Hankel rank of a closed cycle, by counting** (independent of the founding): the
/// matrix `[N(ps)]` over every context `p` of at most `depth` cells and every future `s` of `1 …
/// depth` cells, `N(ps)` the positions of the cycle where `p` ends and `s` begins.
fn count_hankel_rank(cycle: &[usize], depth: usize) -> usize {
    let n = cycle.len();
    let context = |end: usize, length: usize| -> Vec<usize> {
        (0..length)
            .map(|k| cycle[(end + n * (length / n + 1) - length + k) % n])
            .collect()
    };
    let future =
        |start: usize, length: usize| -> Vec<usize> { (0..length).map(|k| cycle[(start + k) % n]).collect() };
    let contexts: BTreeSet<Vec<usize>> = (0..n)
        .flat_map(|end| (0..=depth).map(move |length| (end, length)))
        .map(|(end, length)| context(end, length))
        .collect();
    let futures: BTreeSet<Vec<usize>> = (0..n)
        .flat_map(|start| (1..=depth).map(move |length| (start, length)))
        .map(|(start, length)| future(start, length))
        .collect();
    let rows: Vec<Vec<Rat>> = contexts
        .iter()
        .map(|p| {
            futures
                .iter()
                .map(|s| {
                    let count = (0..n)
                        .filter(|&e| &context(e, p.len()) == p && &future(e, s.len()) == s)
                        .count();
                    Rat::from_integer(BigInt::from(count))
                })
                .collect()
        })
        .collect();
    ExactRatMatrix::new(rows).unwrap().rank().unwrap()
}

/// The least length at which a cycle's words starting at its positions are pairwise distinct.
fn determining_depth(cycle: &[usize]) -> usize {
    let n = cycle.len();
    (1..=n)
        .find(|&length| {
            let words: BTreeSet<Vec<usize>> = (0..n)
                .map(|start| (0..length).map(|k| cycle[(start + k) % n]).collect())
                .collect();
            words.len() == n
        })
        .unwrap_or(n)
}

/// **One terrain's exact checks with no transports declared** (the pin's acceptance 1): the
/// emission's periodic part read as a closed cycle; (a) the letters' right actions found the count
/// Hankel rank, the squares exact; (b) the unconditioned tick, opened at one period read from the
/// opening, founds the declared chart's dimension and the cycle's block Hankel rank, the squares
/// exact. Returns `(transient, period, letters' dimension, tick's dimension)`.
fn passage_checks(cells: &[usize], classes: usize, declared: usize) -> (usize, usize, usize, usize) {
    let (start, period) = periodic_part(cells);
    let cycle = &cells[start..start + period];
    let context = ContextClasses::cycle(cycle).unwrap();
    // (a) the letters' right actions.
    let chart = PassageChart::passage(&context).unwrap();
    let encoding = Encoding::found(&chart).unwrap();
    let squares = encoding.squares(&chart).unwrap();
    assert_eq!(squares.states, encoding.reached());
    assert_eq!(squares.cells, context.letters().len());
    let depth = determining_depth(cycle) + 1;
    assert_eq!(
        encoding.dimension(),
        count_hankel_rank(cycle, depth),
        "the letters' founding is the count Hankel rank on {cycle:?}"
    );
    // (b) the unconditioned tick, opened at one period read from the opening.
    let opening = context.read(cycle).unwrap();
    assert_eq!(context.ends(opening).len(), 1, "a primitive cycle read once fixes its phase");
    let tick = PassageChart::unconditioned(&context, opening).unwrap();
    let founded = Encoding::found(&tick).unwrap();
    founded.squares(&tick).unwrap();
    let blocks = period + 1;
    let repeated: Vec<usize> = cycle.iter().cycle().take(2 * blocks).copied().collect();
    assert_eq!(founded.dimension(), hankel_rank(&repeated, classes, blocks));
    if start == 0 {
        assert_eq!(
            founded.dimension(),
            declared,
            "the tick founds the declared rotor's rank on {cycle:?}"
        );
    }
    (start, period, encoding.dimension(), founded.dimension())
}

/// **Acceptance 1 of the pin of the passage's own transports, the moiré**: with no transports
/// declared, the letters' founding is the count Hankel rank (the cycle's period, 12, 12 and 20), and
/// the unconditioned tick founds the declared rotor's ranks 7, 7 and 11.
#[test]
fn the_moire_read_as_a_passage_founds_its_ranks_with_no_transports_declared() {
    let mut read = Vec::new();
    for (rates, phases) in [
        (vec![(1u64, 3u64), (1, 4)], vec![2u64, 1]),
        (vec![(1, 4), (1, 6)], vec![1, 5]),
        (vec![(1, 4), (3, 5)], vec![3, 0]),
    ] {
        let gratings: Vec<Grating> = rates
            .iter()
            .zip(&phases)
            .map(|(&(p, q), &c)| Grating::new(p, q, c).unwrap())
            .collect();
        let moire = Moire::new(gratings.clone(), MoireClass::Parity).unwrap();
        let declared = Encoding::found(&PassageChart::moire(&gratings, MoireClass::Parity).unwrap())
            .unwrap()
            .dimension();
        let cells = moire.emit(64);
        read.push(passage_checks(&cells, 2, declared));
    }
    assert_eq!(read, vec![(0, 12, 12, 7), (0, 12, 12, 7), (0, 20, 20, 11)]);
}

/// **Acceptance 1 of the pin of the passage's own transports, the rotor crib**: on the four draws
/// on ring 0 and the four on ring 1 of `the_rotor_crib_founds_its_hankel_rank_on_the_reached_orbit`,
/// every emission falls after a transient into one fixed cell, so its closed cycle is that cell: the
/// letters' founding is its count Hankel rank and the unconditioned tick's its block Hankel rank,
/// both one, while the declared chart's dimension counts the transient and the fixed cell (the
/// record of September 29 reports the pinned reading (b) failing here).
#[test]
fn the_rotor_crib_read_as_a_passage_founds_its_ranks_with_no_transports_declared() {
    let field = crib_field();
    let mut draw = Draw::new(29);
    let draws = [(0usize, vec![0u64, 0]), (1, vec![3, 2])]
        .into_iter()
        .flat_map(|draw| std::iter::repeat_n(draw, 4));
    let mut read = Vec::new();
    for (ring, configurations) in draws {
        let chart_states = 5 * 7usize.pow(u32::from(ring == 1)) * [5usize, 7][ring];
        let crib = RotorCrib::draw(&field, ring, &configurations, 2 * chart_states + 2, &mut draw)
            .unwrap();
        let chart = PassageChart::crib(
            &field,
            ring,
            crib.truth.key,
            &crib.truth.board,
            &configurations,
            crib.truth.start,
        )
        .unwrap();
        let declared = Encoding::found(&chart).unwrap().dimension();
        let classes = field.ring(ring).period() as usize;
        let (start, period, letters, tick) = passage_checks(&crib.cells, classes, declared);
        read.push((ring, declared, start, period, letters, tick));
    }
    assert_eq!(
        read,
        vec![
            (0, 4, 3, 1, 1, 1),
            (0, 4, 3, 1, 1, 1),
            (0, 3, 2, 1, 1, 1),
            (0, 6, 5, 1, 1, 1),
            (1, 32, 31, 1, 1, 1),
            (1, 16, 15, 1, 1, 1),
            (1, 40, 39, 1, 1, 1),
            (1, 16, 15, 1, 1, 1),
        ]
    );
}

/// **The passage chart runs its moment in the founded chart** (Lean
/// `HNN/Encoding.encoding_reduced_recurrence`): on the moiré's cycle, the chart's moment of a driven
/// passage, `m ← T_u m + B e_u`, is the sum of the passage's suffix contexts' classes, and its
/// encoding is the founded chart's own recurrence `z ← U_u z + J e_u`, run without the chart.
#[test]
fn the_passage_chart_runs_its_moment_in_the_founded_chart() {
    let gratings = vec![Grating::new(1, 3, 2).unwrap(), Grating::new(1, 4, 1).unwrap()];
    let moire = Moire::new(gratings, MoireClass::Parity).unwrap();
    let cells = moire.emit(24);
    let classes = ContextClasses::cycle(&cells[..12]).unwrap();
    let chart = PassageChart::passage(&classes).unwrap();
    let encoding = Encoding::found(&chart).unwrap();
    let passage: Vec<usize> = cells.iter().cycle().skip(5).take(30).copied().collect();
    let mut state = vec![Rat::zero(); chart.chart()];
    let mut driven = Vec::new();
    for &cell in &passage {
        let letter = classes.letter(cell).unwrap();
        state = chart.transports()[letter].apply(&state).unwrap();
        for (entry, injected) in state.iter_mut().zip(&chart.injection()[letter]) {
            *entry += injected;
        }
        driven.push((letter, letter));
    }
    let mut suffixes = vec![Rat::zero(); chart.chart()];
    for start in 0..passage.len() {
        suffixes[classes.read(&passage[start..]).unwrap()] += Rat::one();
    }
    assert_eq!(state, suffixes, "the moment is the sum of the suffix contexts");
    assert_eq!(
        encoding.encode(&state).unwrap(),
        encoding.reduced_moment(&driven).unwrap()
    );
}

/// **Founded exactly, a passage is its own index** (the second clause): a drawn word's exact
/// realization has the word's length as its dimension, while the charged founding keeps no class
/// beyond the opening on it; on a recurring word it founds exactly the contexts that recur and
/// stops.
#[test]
fn the_charged_founding_keeps_what_recurs_and_founds_no_index() {
    let mut draw = Draw::new(20260929);
    let short: Vec<usize> = (0..10).map(|_| draw.below(4)).collect();
    let exact = Encoding::found(
        &PassageChart::passage(&ContextClasses::linear(&short).unwrap()).unwrap(),
    )
    .unwrap();
    assert_eq!(exact.dimension(), short.len(), "the exact realization is an index");
    let drawn: Vec<usize> = (0..400).map(|_| draw.below(4)).collect();
    let founding = found_passage(&drawn, 7).unwrap();
    assert_eq!(founding.classes().len(), 1, "no context of a drawn word pays its charge");
    // A recurring word: each cell's one-cell context determines its successor.
    let word: Vec<usize> = [3usize, 1, 4, 0, 2].repeat(60);
    let founding = found_passage(&word, 7).unwrap();
    // The opening already reads the cell after `2` (and the first cell), each `3`: that context
    // pays no charge and stays in the opening's class, its fibre.
    assert_eq!(founding.classes().len(), 5);
    assert!(founding.classes()[1..].iter().all(|class| class.shortest == 1));
    assert_eq!(
        founding
            .classes()
            .iter()
            .map(|class| class.word.clone())
            .collect::<Vec<_>>(),
        vec![vec![], vec![3], vec![3, 1], vec![3, 1, 4], vec![3, 1, 4, 0]]
    );
    assert_eq!(
        founding
            .rungs()
            .iter()
            .map(|rung| (rung.candidates, rung.born, rung.undecided))
            .collect::<Vec<_>>(),
        vec![(5, 4, 0), (1, 0, 0)]
    );
    let [before, after] = founding.code();
    assert!(&after.upper + &founding.description().upper < before.lower);
    let encoding = Encoding::found(&PassageChart::founded(&founding).unwrap()).unwrap();
    assert_eq!(encoding.dimension(), 5);
    // The ladder is myopic: on `0 1 0 2` repeated, `10` and `20` would read the alternation after
    // `0` exactly, but they are reached only from `1` and `2`, which add nothing alone once the
    // opening reads their successor (`0`), so the founding keeps `0` and stops.
    let pattern: Vec<usize> = [0usize, 1, 0, 2].repeat(40);
    let founding = found_passage(&pattern, 7).unwrap();
    assert_eq!(
        founding
            .classes()
            .iter()
            .map(|class| class.word.clone())
            .collect::<Vec<_>>(),
        vec![vec![], vec![0]]
    );
    assert_eq!(
        founding
            .rungs()
            .iter()
            .map(|rung| (rung.candidates, rung.born, rung.undecided))
            .collect::<Vec<_>>(),
        vec![(3, 1, 0), (2, 0, 0)]
    );
    assert_eq!(founding.counts(), &[vec![80, 0, 0], vec![0, 40, 40]]);
    let mut state = PassageFounding::OPENING;
    let reached: Vec<Option<usize>> = pattern
        .iter()
        .map(|&cell| founding.step(&mut state, cell).unwrap())
        .collect();
    assert!(reached.iter().all(Option::is_some));
    assert_eq!(founding.step(&mut state, 5).unwrap(), None, "a cell never met is the fibre");
    assert_eq!(state, PassageFounding::OPENING);
}

/// **The founded port chart** (module header, "The field's port chart"): each founded class sits on
/// each ring at the ring's phase class at its first arrival on the field's own clock as the source
/// moment reads the founding passage; the moment's founded class is the machine's; the fibre sits
/// outside every lock; the recurrence counts the machine's classes; and relabeling the exterior
/// codes relabels the chart and nothing else (no codec value enters).
#[test]
fn the_port_chart_places_founded_classes_at_first_arrival_and_is_blind_to_codec_values() {
    let field = crib_field();
    let passage: Vec<usize> = [0usize, 1, 0, 2, 0, 1, 0, 2, 3].repeat(12);
    let founded = found_ports(&field, &passage).unwrap();
    assert!(founded.constituents.len() > 1);
    assert_eq!(founded.fibre, vec![4, 5, 6]);
    let reading = field.clone().with_port_chart(founded.chart.clone()).unwrap();
    let steps = reading.step_codes(&passage).unwrap();
    let mut current = Current::at_rest(&reading);
    let mut moment = SourceMoment::open(&reading, &current);
    let mut seen = vec![false; reading.steps()];
    for (&cell, &step) in passage.iter().zip(&steps) {
        if !seen[step] {
            seen[step] = true;
            for g in 0..reading.rings().len() {
                assert_eq!(
                    current.phase(&reading, g).unwrap() as usize,
                    founded.placements[step][g],
                    "class {step} sits at its first arrival's phase on ring {g}"
                );
            }
        }
        moment.ingest(&reading, &mut current, &[cell]).unwrap();
    }
    assert_eq!(moment.founded(), {
        let mut state = reading.founded_opening();
        for &cell in &passage {
            reading.step_code(&mut state, cell).unwrap();
        }
        state
    });
    for (g, ring) in reading.rings().iter().enumerate() {
        let fibre = reading.port_chart().machine().unwrap().fibre();
        assert!(!ring.fits(ring.port(fibre)), "the fibre steps ring {g} by no lock");
    }
    let recurrence = founded.recurrence(&passage).unwrap();
    assert_eq!(recurrence.iter().sum::<u64>(), passage.len() as u64);
    assert_eq!(*recurrence.last().unwrap(), 0);
    // Relabel the codes by a permutation: the chart is relabeled, and nothing else changes.
    let relabel = [6usize, 4, 2, 0, 5, 3, 1];
    let moved: Vec<usize> = passage.iter().map(|&cell| relabel[cell]).collect();
    let refounded = found_ports(&field, &moved).unwrap();
    assert_eq!(refounded.placements, founded.placements);
    assert_eq!(refounded.constituents, founded.constituents);
    let rereading = field.clone().with_port_chart(refounded.chart.clone()).unwrap();
    assert_eq!(rereading.step_codes(&moved).unwrap(), steps);
    for (cell, &image) in relabel.iter().enumerate() {
        assert_eq!(
            refounded.chart.injection()[image],
            founded.chart.injection()[cell]
        );
    }
}

/// **A founded field opens `E` at the founded injection**: each cell's column is one half at the
/// placement node of the class it reaches from the opening, on the source ring (the real
/// quadrature), where the residue chart's field opens at the sign sequence; a chart of the wrong
/// shape is refused; and the description codes which chart the field reads.
#[test]
fn a_founded_field_opens_its_source_port_at_the_founded_injection() {
    use crate::hnn::constitution::{Constitution, Steps};
    use crate::hnn::field::{ConstitutionRead, FoundedMachine, PortChart, PortChartKind};
    let field = crib_field();
    let passage: Vec<usize> = [3usize, 1, 3, 4, 3, 1, 1, 4, 3].repeat(6);
    let founded = found_ports(&field, &passage).unwrap();
    let reading = field.clone().with_port_chart(founded.chart.clone()).unwrap();
    assert!(reading.port_chart().is_founded() && !field.port_chart().is_founded());
    let theta = Constitution::initial(&reading, Steps::campaign_one(), 1 << 40).unwrap();
    let port = theta.source_port(0).unwrap();
    let ring = reading.ring(0);
    for x in 0..reading.alphabet() {
        for i in 0..ring.width() {
            let expected = if i == 2 * ring.port(reading.port_chart().injection()[x]) {
                rat(1, 2)
            } else {
                Rat::zero()
            };
            assert_eq!(port.get(i, x).unwrap(), &expected);
        }
    }
    let residue = Constitution::initial(&field, Steps::campaign_one(), 1 << 40).unwrap();
    assert!(
        residue
            .source_port(0)
            .unwrap()
            .entries()
            .iter()
            .all(|entry| entry == &rat(1, 2) || entry == &rat(-1, 2))
    );
    let steps = reading.steps();
    assert_eq!(steps, founded.constituents.len() + 1);
    let kind = founded.chart.kind();
    assert_eq!(
        kind,
        PortChartKind::Passage {
            passage: passage.len() as u64,
            classes: founded.constituents.len() as u64,
            fibre: 4
        }
    );
    let machine = founded.chart.machine().unwrap().clone();
    let injection = founded.chart.injection().to_vec();
    let ports = founded.chart.ports().to_vec();
    let short = PortChart::passage(vec![ports[0].clone()], injection.clone(), machine.clone(), kind);
    assert!(field.clone().with_port_chart(short).is_err());
    let narrow = PortChart::passage(
        ports.iter().map(|row| row[1..].to_vec()).collect(),
        injection.clone(),
        machine.clone(),
        kind,
    );
    assert!(field.clone().with_port_chart(narrow).is_err());
    let outside = PortChart::passage(
        vec![vec![5; steps], ports[1].clone()],
        injection.clone(),
        machine.clone(),
        kind,
    );
    assert!(field.clone().with_port_chart(outside).is_err());
    let unread = PortChart::passage(ports.clone(), injection[1..].to_vec(), machine, kind);
    assert!(field.clone().with_port_chart(unread).is_err());
    assert!(FoundedMachine::new(Vec::new(), 0).is_err());
    assert!(FoundedMachine::new(vec![vec![0, 1], vec![0]], 0).is_err());
    assert!(FoundedMachine::new(vec![vec![3, 0]], 0).is_err());
    let described = Steps::campaign_one();
    assert_ne!(
        reading.describe(&described, 1 << 40, 64),
        field.describe(&described, 1 << 40, 64)
    );
}

/// **The receiving letters' reader and the keys step by the founded classes**: on campaign 1's field
/// with a chart founded on a recurring passage, a register reading rings 0 and 1's phase letters
/// keeps its clock with the lift point at every cell (the reader carries its own copy of the
/// founded machine), and a crib's opening is recovered from its step codes (`keys::crib_opening`).
#[test]
fn the_letters_reader_and_the_keys_step_by_the_founded_classes() {
    use crate::hnn::keys::crib_opening;
    use crate::hnn::receiving::{ActiveAddress, Feature, FeatureFamily, LetterReader};
    let campaign = Field::declare(FieldDeclaration::campaign_one(6_148)).unwrap();
    let mut draw = Draw::new(7);
    let words: [&[usize]; 3] = [&[116, 104, 101, 32], &[97, 110, 100, 32], &[111, 102, 32]];
    let passage: Vec<usize> = (0..160)
        .flat_map(|_| words[draw.below(3)].iter().copied())
        .collect();
    let founded = found_ports(&campaign, &passage[..300]).unwrap();
    assert!(founded.founding.classes().len() > 1);
    let field = campaign.with_port_chart(founded.chart).unwrap();
    let family = FeatureFamily::new(vec![
        Feature::Phase { ring: 0, grain: 5 },
        Feature::Phase { ring: 1, grain: 7 },
    ])
    .unwrap();
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    let mut register =
        ActiveAddress::of_reader(3, LetterReader::of(&field, family, &current).unwrap());
    let rest = current.lift().to_vec();
    for &cell in &passage {
        moment.ingest(&field, &mut current, &[cell]).unwrap();
        register.receive(cell).unwrap();
        assert!(register.reader().agrees(&field, &current, current.lift()));
    }
    assert_ne!(current.lift(), &rest[..], "the founded chart steps the rings");
    // A crib's step codes carry the lift from its opening to its end, and back.
    let steps = field.step_codes(&passage).unwrap();
    let (from, to) = (200usize, 260usize);
    let mut opening = Current::at_rest(&field);
    for &step in &steps[..from] {
        opening.step(&field, step).unwrap();
    }
    let mut end = opening.clone();
    for &step in &steps[from..to] {
        end.step(&field, step).unwrap();
    }
    assert_eq!(
        crib_opening(&field, end.lift(), &steps[from..to]).unwrap(),
        opening.lift().to_vec()
    );
}

/// Refusals are typed: an empty chart, a transport off the chart, openings that reach nothing,
/// forms that read nothing on the reached span, and a founding passage that is empty or leaves the
/// exterior chart.
#[test]
fn the_passage_chart_refuses_what_it_cannot_found() {
    let identity = ExactRatMatrix::identity(2).unwrap();
    assert!(matches!(
        PassageChart::new(0, vec![], vec![], vec![], vec![]),
        Err(EncodingError::Chart { .. })
    ));
    assert!(matches!(
        PassageChart::new(
            2,
            vec![ExactRatMatrix::identity(3).unwrap()],
            vec![],
            vec![vec![Rat::one(), Rat::zero()]],
            vec![]
        ),
        Err(EncodingError::Chart { .. })
    ));
    let silent = PassageChart::new(
        2,
        vec![identity.clone()],
        vec![],
        vec![vec![Rat::one(), Rat::zero()]],
        vec![vec![Rat::zero(), Rat::zero()]],
    )
    .unwrap();
    assert!(matches!(
        Encoding::found(&silent),
        Err(EncodingError::Chart { .. })
    ));
    let blind = PassageChart::new(
        2,
        vec![identity],
        vec![],
        vec![vec![Rat::one(), Rat::zero()]],
        vec![vec![Rat::zero(), Rat::one()]],
    )
    .unwrap();
    assert_eq!(Encoding::found(&blind), Err(EncodingError::Blind));
    let field = crib_field();
    assert!(found_ports(&field, &[]).is_err());
    assert!(found_ports(&field, &[7]).is_err());
    assert!(found_passage(&[], 7).is_err());
    assert!(ContextClasses::cycle(&[]).is_err());
    assert!(
        PassageChart::unconditioned(&ContextClasses::linear(&[1, 2]).unwrap(), 9).is_err()
    );
}
