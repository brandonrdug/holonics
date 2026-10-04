//! Holonic Encoding (`hnn::encoding`, THE_REBUILD U6, the pins of September 29): the squares
//! `D E = ρ`, `E T = U E` and the injection square, exact on the known-truth terrains' declared
//! charts, with the founded dimension equal to the emission's Hankel rank on the reached orbit
//! (acceptance 1); the moment chart's reduced recurrence joined to `SourceMoment`; the separator.
//! The passage's own transports, the charged founding and the founded port chart were retired on
//! September 29 (the lessons record); their tests are at `96d8940b`.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::support::{Draw, contact, ring};
use crate::compression::landmark::context::StopPrior;
use crate::hnn::encoding::{Encoding, EncodingError, PassageChart};
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
    assert!(cells.len() + 1 >= 2 * blocks, "the emission fills the Hankel matrix");
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
                mass: 1,
                base: crate::compression::landmark::context::BaseMeasure::Even,
                receiving_prior: crate::hnn::field::ReceivingPrior::Held(0),
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

/// Refusals are typed: an empty chart, a transport off the chart, openings that reach nothing, and
/// forms that read nothing on the reached span.
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
}
