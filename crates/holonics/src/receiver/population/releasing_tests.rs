use super::tests::Fixed;
use super::{Family, Population, PopulationRelease, Relation, RelationKind, ReleaseRefusal};
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::{Rat, rat};
use crate::receiver::release::ReleaseReturn;
use num_traits::{One, Zero};

#[test]
fn release_is_the_scored_face_and_includes_the_designated_class() {
    let family = Fixed::new(vec![rat(1, 2), rat(1, 3), rat(1, 6)], 0);
    let population = Population::new(vec![Box::new(family)]).expect("population");
    let scored = population.face().expect("scored face");

    let release = PopulationRelease::from_scored_face(&population, 2).expect("release");
    assert_eq!(release.face(), scored.as_slice());
    assert_eq!(release.selected_class(), 2);
    assert!(release.face()[2].lower <= rat(1, 6));
    assert!(release.face()[2].upper >= rat(1, 6));
}

#[test]
fn release_refuses_a_class_outside_the_scored_alphabet() {
    let family = Fixed::new(vec![rat(1, 2), rat(1, 2)], 0);
    let population = Population::new(vec![Box::new(family)]).expect("population");
    assert_eq!(
        PopulationRelease::from_scored_face(&population, 2).unwrap_err(),
        ReleaseRefusal::ClassOutsideAlphabet {
            class: 2,
            alphabet: 2,
        }
    );
}

#[test]
fn a_relation_without_a_living_receiver_owner_is_refused() {
    let family = Fixed::new(vec![rat(1, 2), rat(1, 2)], 0);
    let mut population = Population::new(vec![Box::new(family)]).expect("population");
    assert!(
        population
            .plan_relation(Relation {
                target: 0,
                letter: 1,
                kind: RelationKind::Request,
            })
            .is_err(),
        "a keyless family cannot claim to condition a response on a request"
    );
}

// -------------------------------------------------------------------------------------------
// the family draw (the receipts `population::family_release` carried, through the one law)

/// A family whose posterior is a point mass is drawn at every key.
#[test]
fn point_mass_family_choice_is_certified() {
    let mut population = Population::new(vec![
        Box::new(Fixed::new(vec![Rat::one(), Rat::zero()], 0)) as Box<dyn Family>,
    ])
    .unwrap();
    population.receive(0).unwrap();
    let face = population.family_posterior_face().unwrap();
    assert_eq!(face, vec![ExactInterval::point(Rat::one())]);
    let drawn = population.select_family(&rat(1, 2)).unwrap();
    assert_eq!(drawn.drawn_class(), Some(0));
}

/// The posterior enclosure is the two families' charged mixture: `2/3` and `1/3` at descriptions
/// one and two bits.
#[test]
fn posterior_bounds_use_the_two_families_charged_mixture() {
    let population = Population::new(vec![
        Box::new(Fixed::new(vec![rat(1, 1), rat(0, 1)], 1)) as Box<dyn Family>,
        Box::new(Fixed::new(vec![rat(0, 1), rat(1, 1)], 2)),
    ])
    .unwrap();
    let posterior = population.family_posterior_face().unwrap();
    assert_eq!(posterior.len(), 2);
    assert!(posterior[0].lower <= rat(2, 3) && posterior[0].upper >= rat(2, 3));
    assert!(posterior[1].lower <= rat(1, 3) && posterior[1].upper >= rat(1, 3));
}

/// A key the posterior enclosure leaves plural is held: the family draw is `Unresolved`, with the
/// crossing families, and nothing is drawn.
#[test]
fn interval_posterior_holds_an_unresolved_family_crossing() {
    let population = Population::new(vec![
        Box::new(Fixed::new(vec![Rat::one(), Rat::zero()], 1)) as Box<dyn Family>,
        Box::new(Fixed::new(vec![Rat::zero(), Rat::one()], 2)),
    ])
    .unwrap();
    match population.select_family(&rat(2, 3)).unwrap() {
        ReleaseReturn::Unresolved(held) => {
            assert_eq!(held.key, rat(2, 3));
            assert_eq!(
                held.crossings.iter().map(|c| c.class).collect::<Vec<_>>(),
                vec![0, 1]
            );
        }
        other => panic!("expected an unresolved family draw, got {other:?}"),
    }
}

// -------------------------------------------------------------------------------------------
// release checks on known-truth terrain (the notebook's retired `hnn_release_terrain`, whose
// receipt these fixtures reproduce exactly)

mod terrain {
    use num_traits::{One, Zero};

    use crate::compression::landmark::context::{
        Capacity, LandmarkDeclaration, LetterFamily, StopPrior,
    };
    use crate::holarchy::terrain::{
        Draw, Moire, MoireClass, MoireFamily, MoireTruth, TreeSource, TreeSourceFamily,
    };
    use crate::ratio::{Rat, rat};
    use crate::receiver::population::composition_tests::{
        drawn_sheets, horizon, ring_survivors, sheet_tuple_egg, two_rings,
    };
    use crate::receiver::population::{
        Family, KeyFamily, Population, PopulationRelease, TreeFamily,
    };
    use crate::receiver::release::{ReleaseReturn, draw_exact};

    const SEED: u64 = 20_260_927;

    /// The one-member population's exact conditional face, read inside the release view's face
    /// (`P_release = P_scored`: the enclosure must contain it, class by class).
    fn enclosed_member_face(population: &Population) -> Vec<Rat> {
        let exact = population
            .families()
            .next()
            .expect("the declared one-family population")
            .face()
            .expect("the member's exact conditional face");
        let view = PopulationRelease::from_scored_face(population, 0).expect("the release view");
        let enclosure = view.face();
        assert_eq!(exact.len(), enclosure.len());
        assert!(
            exact
                .iter()
                .zip(enclosure)
                .all(|(p, bounds)| bounds.lower <= *p && *p <= bounds.upper)
        );
        exact
    }

    /// **The face determines `class` at every key**: the certified draw of the key zero lands in
    /// `class` with the whole key interval `[0, 1)` as its cell. For a normalized exact face this
    /// is exactly the face being one-hot on `class`, read through the one law.
    fn one_hot(face: &[Rat], class: usize) -> bool {
        match draw_exact(face, &Rat::zero()).expect("a normalized exact face") {
            ReleaseReturn::Drawn(cell) => {
                cell.class == class && cell.prior_upper.is_zero() && cell.through_lower.is_one()
            }
            _ => false,
        }
    }

    /// The moiré's cell at `tick`, read from the terrain's returned rate/phase keys alone.
    fn truth_cell(truth: &MoireTruth, tick: u64, class: MoireClass) -> usize {
        let sheets: Vec<bool> = truth
            .gratings
            .iter()
            .map(|grating| {
                let d = grating.denominator();
                let port = (grating.phase() + (tick * grating.numerator()) % d) % d;
                2 * port >= d
            })
            .collect();
        match class {
            MoireClass::Parity => sheets.iter().filter(|sheet| **sheet).count() % 2,
            MoireClass::Sheets => sheets
                .iter()
                .enumerate()
                .map(|(ring, sheet)| usize::from(*sheet) << ring)
                .sum(),
        }
    }

    /// **A one-hot present face does not certify the future** (the full-future check). On a
    /// declared moiré's grating keys (two rings over `ℤ/5`, sheet tuples), the population's face is
    /// one-hot on the truth at tick 4, yet within the joint period (20) the surviving keys part at
    /// tick 5, where the exact face is `(2/3, 1/3, 0, 0)` against truth class 0. A candidate key
    /// counts as future-equivalent only once every face of a whole joint period is one-hot on the
    /// truth; the first face that is not is the separator.
    #[test]
    fn a_one_hot_face_is_checked_across_the_joint_period() {
        let family = MoireFamily {
            rings: 2,
            denominator: 5,
        };
        let class = MoireClass::Sheets;
        let moire = Moire::draw(&family, class, &mut Draw::new(SEED)).unwrap();
        let truth = moire.truth(&family).unwrap();
        let description = u64::from(family.gratings()).ilog2() as u64 * family.rings as u64 + 1;
        let keys = KeyFamily::gratings(&family, class, 1 << 20, description).unwrap();
        let mut population = Population::new(vec![Box::new(keys) as Box<dyn Family>]).unwrap();
        let period = usize::try_from(truth.joint_period.clone()).unwrap();
        assert_eq!(period, 20);
        let cells = moire.emit(2 * period);
        assert!(
            cells
                .iter()
                .enumerate()
                .all(|(tick, cell)| *cell == truth_cell(&truth, tick as u64, class))
        );
        // The first one-hot face on the truth.
        let mut start = None;
        for (tick, &cell) in cells.iter().enumerate().take(period) {
            population.receive(cell).unwrap();
            if one_hot(&enclosed_member_face(&population), cells[tick + 1]) {
                start = Some(tick + 1);
                break;
            }
        }
        let start = start.expect("a one-hot face within the joint period");
        assert_eq!(start, 4);
        // Across the joint period from the candidate, the first face that is not one-hot.
        let mut separator = None;
        for tick in start..start + period {
            let face = enclosed_member_face(&population);
            if !one_hot(&face, cells[tick]) {
                separator = Some((tick, cells[tick], face));
                break;
            }
            population.receive(cells[tick]).unwrap();
        }
        assert_eq!(
            separator,
            Some((5, 0, vec![rat(2, 3), rat(1, 3), Rat::zero(), Rat::zero()]))
        );
    }

    /// **The composed grating key predicts every cell once its survivors are one species** (the
    /// full-future check above, on a composed egg): on the drawn sheet tuple composed at its first
    /// ring (`composition_tests::sheet_tuple_egg`), each ring's species is the gratings emitting
    /// its drawn word forever (its survivors over the horizon), and the tick from which both rings'
    /// survivors are their species is read by brute force. From that tick every face is one-hot on
    /// the truth through the one law, and the first one-hot face comes no later. On the drawn
    /// `3/5 @ 0/5, 1/4 @ 0/4` each species is the ring's grating and its mirror; the first one-hot
    /// face is at tick 4, before the survivors are their species at tick 7.
    #[test]
    fn the_composed_grating_key_holds_once_its_survivors_are_one_species() {
        let family = two_rings();
        let reach = horizon(&family);
        let cells = drawn_sheets().emit(3 * reach);
        let species = [0, 1].map(|ring| ring_survivors(&family, &cells[..reach], ring));
        let settled = (0..=cells.len())
            .find(|&t| {
                (0..2).all(|ring| ring_survivors(&family, &cells[..t], ring) == species[ring])
            })
            .expect("the survivors reach their species by the horizon");
        assert!(settled <= reach);
        let composed = sheet_tuple_egg(&family, 1);
        let mut population = Population::new(vec![Box::new(composed) as Box<dyn Family>]).unwrap();
        let mut located = None;
        for (tick, &cell) in cells.iter().enumerate() {
            let exact = one_hot(&enclosed_member_face(&population), cell);
            if exact && located.is_none() {
                located = Some(tick);
            }
            if tick >= settled {
                assert!(exact, "a face past the species at {tick}");
            }
            population.receive(cell).unwrap();
        }
        assert!(located.is_some_and(|tick| tick <= settled));
        assert_eq!((located, settled), (Some(4), 7));
    }

    /// **A learned face is compared with the identified source face by exact separators**: the
    /// receiving tree (cell letters, `D = 3`, the `½` stop prior) at the drawn binary tree source's
    /// initial address reads 1,024 cells; every face lies inside the population's enclosure and is
    /// normalized, none equals the identified conditional truth face, and each separator is an
    /// exact difference summing to zero. The first, at tick 0, is `±223696213/2^30`.
    #[test]
    fn the_learned_face_is_separated_from_the_source_face_exactly() {
        let family = TreeSourceFamily {
            alphabet: 2,
            depth: 3,
            grid: 16,
        };
        let ticks = 1usize << 10;
        let source = TreeSource::draw(&family, &mut Draw::new(SEED)).unwrap();
        let truth = source.truth().unwrap();
        let cells = source.emit(ticks, &mut Draw::new(SEED ^ 0xF4));
        let declaration = LandmarkDeclaration {
            alphabet: 2,
            depth: family.depth,
            forced: 0,
            population: (ticks + family.depth) as u64,
            grain: 16,
            family: LetterFamily::cells(),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        };
        let tree = TreeFamily::new(declaration, 1).unwrap();
        let mut population = Population::new(vec![Box::new(tree) as Box<dyn Family>]).unwrap();
        population.receive_passage(source.initial()).unwrap();
        let mut history: Vec<usize> = source.initial().iter().rev().copied().collect();
        let (mut equal, mut first) = (0usize, None);
        for (tick, cell) in cells.into_iter().enumerate() {
            let leaf = source.tree().leaf(history.iter().rev().copied()).unwrap();
            let expected = &truth.faces[leaf];
            let face = enclosed_member_face(&population);
            assert_eq!(face.iter().sum::<Rat>(), Rat::one());
            if face == *expected {
                equal += 1;
            } else {
                let difference: Vec<Rat> = face.iter().zip(expected).map(|(a, b)| a - b).collect();
                assert!(difference.iter().sum::<Rat>().is_zero());
                first.get_or_insert((tick, difference));
            }
            population.receive(cell).unwrap();
            history.push(cell);
        }
        assert_eq!(equal, 0);
        let unit = Rat::from_integer(num_bigint::BigInt::from(1u64 << 30));
        let separation = Rat::from_integer(num_bigint::BigInt::from(223_696_213u64)) / unit;
        assert_eq!(first, Some((0, vec![separation.clone(), -separation])));
    }
}
