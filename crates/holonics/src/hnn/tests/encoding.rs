//! Holonic Encoding (`hnn::encoding`, THE_REBUILD U6, the pin of September 29): the squares
//! `D E = ρ`, `E T = U E` and the injection square, exact on the known-truth terrains, with the
//! founded dimension equal to the emission's Hankel rank on the reached orbit (acceptance 1); the
//! moment chart's reduced recurrence joined to `SourceMoment`; the separator; the founded port
//! chart, placed at first arrival and blind to the codec's values.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::support::{Draw, contact, ring};
use crate::compression::landmark::context::StopPrior;
use crate::hnn::encoding::{Encoding, EncodingError, PassageChart, found_ports};
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

/// **The founded port chart** (module header, "The field's port chart"): each founded constituent
/// sits on each ring at the ring's phase class at its first arrival on the field's own clock; the
/// field that reads the chart steps the founding passage exactly as the founding did; the plural
/// fibre sits outside every lock; and relabeling the exterior codes relabels the chart and nothing
/// else (no codec value enters).
#[test]
fn the_port_chart_is_founded_at_first_arrival_and_blind_to_codec_values() {
    let field = crib_field();
    let passage: Vec<usize> = vec![3, 1, 3, 3, 4, 1, 3, 1, 3, 4, 3, 3, 1, 1, 3, 4, 4, 3, 3, 1];
    let founded = found_ports(&field, &passage).unwrap();
    assert_eq!(founded.constituents, vec![vec![3], vec![1], vec![4]]);
    assert_eq!(founded.fibre, vec![0, 2, 5, 6]);
    let reading = field.clone().with_port_chart(founded.chart.clone()).unwrap();
    let mut current = Current::at_rest(&reading);
    let mut seen = vec![false; field.alphabet()];
    for &cell in &passage {
        if !seen[cell] {
            seen[cell] = true;
            let constituent = founded.constituent_of[cell].unwrap();
            for g in 0..reading.rings().len() {
                assert_eq!(
                    current.phase(&reading, g).unwrap() as usize,
                    founded.placements[constituent][g],
                    "cell {cell} sits at its first arrival's phase on ring {g}"
                );
            }
        }
        current.step(&reading, cell).unwrap();
    }
    for &cell in &founded.fibre {
        for (g, ring) in reading.rings().iter().enumerate() {
            assert!(!ring.fits(ring.port(cell)), "the fibre steps ring {g} by no lock");
        }
    }
    assert_eq!(founded.recurrence(&passage), vec![10, 6, 4, 0]);
    // Relabel the codes by a permutation: the chart is relabeled, and nothing else changes.
    let relabel = [6usize, 4, 2, 0, 5, 3, 1];
    let moved: Vec<usize> = passage.iter().map(|&cell| relabel[cell]).collect();
    let refounded = found_ports(&field, &moved).unwrap();
    assert_eq!(refounded.placements, founded.placements);
    for g in 0..field.rings().len() {
        for (cell, &image) in relabel.iter().enumerate() {
            assert_eq!(
                refounded.chart.ports()[g][image],
                founded.chart.ports()[g][cell]
            );
        }
    }
    // The chart founds the exterior cells: each reached cell its own founded injection.
    let cells = founded.encoding.cells();
    assert_eq!(cells.len(), 4);
    assert!(cells.last().unwrap().native.is_none());
    assert!(cells[..3].iter().all(|class| class.members.len() == 1));
}

/// **A founded field opens `E` at the founded injection**: each cell's column is one half at its
/// constituent's placement node on the source ring (the real quadrature), where the residue chart's
/// field opens at the sign sequence; a chart of the wrong shape is refused; and the description
/// codes which chart the field reads.
#[test]
fn a_founded_field_opens_its_source_port_at_the_founded_injection() {
    use crate::hnn::constitution::{Constitution, Steps};
    use crate::hnn::field::{ConstitutionRead, PortChart, PortChartKind};
    let field = crib_field();
    let passage = [3usize, 1, 3, 4, 3, 1, 1, 4, 3];
    let founded = found_ports(&field, &passage).unwrap();
    let reading = field.clone().with_port_chart(founded.chart.clone()).unwrap();
    assert!(reading.port_chart().is_founded() && !field.port_chart().is_founded());
    let theta = Constitution::initial(&reading, Steps::campaign_one(), 1 << 40).unwrap();
    let port = theta.source_port(0).unwrap();
    let ring = reading.ring(0);
    for x in 0..reading.alphabet() {
        for i in 0..ring.width() {
            let expected = if i == 2 * ring.port(x) {
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
    let kind = founded.chart.kind();
    assert_eq!(
        kind,
        PortChartKind::Founded {
            passage: 9,
            constituents: 3,
            fibre: 4
        }
    );
    let short = PortChart::founded(vec![vec![0; 7]], kind);
    assert!(field.clone().with_port_chart(short).is_err());
    let narrow = PortChart::founded(vec![vec![0; 6], vec![0; 6]], kind);
    assert!(field.clone().with_port_chart(narrow).is_err());
    let outside = PortChart::founded(vec![vec![5; 7], vec![0; 7]], kind);
    assert!(field.clone().with_port_chart(outside).is_err());
    let steps = Steps::campaign_one();
    assert_ne!(
        reading.describe(&steps, 1 << 40, 64),
        field.describe(&steps, 1 << 40, 64)
    );
}

/// **The receiving letters' reader steps by the field's own chart**: on campaign 1's field with a
/// chart founded on a drawn passage, a register reading rings 0 and 1's phase letters keeps its
/// clock with the lift point at every cell (the reader reads `Ring::port`, one owner of the chart).
#[test]
fn the_letters_reader_steps_by_the_founded_chart() {
    use crate::hnn::receiving::{ActiveAddress, Feature, FeatureFamily, LetterReader};
    let campaign = Field::declare(FieldDeclaration::campaign_one(6_148)).unwrap();
    let mut draw = Draw::new(7);
    let passage: Vec<usize> = (0..400).map(|_| 60 + draw.below(40)).collect();
    let founded = found_ports(&campaign, &passage[..200]).unwrap();
    let field = campaign.with_port_chart(founded.chart).unwrap();
    let family = FeatureFamily::new(vec![
        Feature::Phase { ring: 0, grain: 5 },
        Feature::Phase { ring: 1, grain: 7 },
    ])
    .unwrap();
    let mut current = Current::at_rest(&field);
    let mut register =
        ActiveAddress::of_reader(3, LetterReader::of(&field, family, &current).unwrap());
    let rest = current.lift().to_vec();
    for &cell in &passage {
        current.step(&field, cell).unwrap();
        register.receive(cell).unwrap();
        assert!(register.reader().agrees(&field, &current, current.lift()));
    }
    assert_ne!(current.lift(), &rest[..], "the founded chart steps the rings");
}

/// Refusals are typed: an empty chart, a transport off the chart, openings that reach nothing and
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
    let field = crib_field();
    assert!(found_ports(&field, &[]).is_err());
    assert!(found_ports(&field, &[7]).is_err());
}
