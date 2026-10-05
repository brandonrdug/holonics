//! Native generation (`hnn::prediction`): the continuing word, the passage's placement of the
//! section, the partition law, the receiving bank's placement and its locks, and the release of a
//! located pair on equal material.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::learning::{chain, generic, moment};
use crate::hnn::tests::support::encoded;
use super::support::Draw;
use crate::hnn::constitution::Constitution;
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::moment::SourceMoment;
use crate::hnn::prediction::{BankPlacement, Refinement, generate_by_bank};
use crate::hnn::propagation::Operands;
use crate::hnn::ring::{PumpDeclaration, PumpStep, ReceivingBank, ResonatorMaterial};
use crate::hnn::word::{EndChange, Word};
use crate::holon::parametron::{Carrier, Parametron};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};


/// A cycle parametron of `d` nodes (unit branches), the ring's resonator base.
pub(super) fn cycle(d: usize) -> Parametron {
    let incidence = crate::ratio::linear::vector::matrix(d, d, |branch, node| {
        if node == branch {
            -Rat::one()
        } else if node == (branch + 1) % d {
            Rat::one()
        } else {
            Rat::zero()
        }
    })
    .unwrap();
    Parametron::new(incidence, vec![Rat::one(); d], vec![integer(2); d]).unwrap()
}

/// The constitution with a pumped resonator declared on every ring.
pub(super) fn resonant(field: &Field, theta: Constitution) -> Constitution {
    (0..field.rings().len()).fold(theta, |theta, ring| pumped_at(field, theta, ring))
}

/// The constitution with ring `ring`'s pumped cycle resonator, as [`resonant`] declares it.
pub(super) fn pumped_at(field: &Field, theta: Constitution, ring: usize) -> Constitution {
    let period = field.ring(ring).period() as usize;
    let pump = PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half).unwrap();
    theta
        .with_ring_resonator(
            field,
            ring,
            ResonatorMaterial::of_parametron(&cycle(period), &rat(1, 8), Some(pump)).unwrap(),
        )
        .unwrap()
}

fn storage(field: &Field, seed: u64) -> Vec<Vec<Rat>> {
    let mut draw = Draw::new(seed);
    field
        .rings()
        .iter()
        .map(|ring| draw.half_vector(ring.width()))
        .collect()
}

/// A word opened at rest is the continuing word opened on the rest change at tick zero.
#[test]
fn a_word_at_rest_is_the_continuing_word_on_the_rest_change() {
    let field = chain();
    let theta = resonant(&field, generic(&field, 71));
    let current = Current::at_rest(&field);
    let operands = Operands::at_cut(&field, &theta, &current).unwrap();
    let injected = storage(&field, 72);
    let mut rest = Word::on_operands(&field, operands.clone(), injected.clone()).unwrap();
    rest.run(3).unwrap();
    let mut continuing = Word::continuing(
        &field,
        operands.clone(),
        &EndChange::rest(&field, &operands),
        &injected,
        0,
    )
    .unwrap();
    continuing.run(3).unwrap();
    assert_eq!(rest.change().unwrap(), continuing.change().unwrap());
    assert_eq!(rest.field_balances(), continuing.field_balances());
}

/// **Continuing motion carries the whole change** (`hnn::word`, "Continuing motion within a
/// refinement"): under the exact law, two words of two ticks, the second opened on the first's
/// change with nothing injected, end on the change one word of four ticks ends on, the pumped
/// resonators' states and phases included; each word's ticks close and the second's first tick
/// opens at the first's last energy.
#[test]
fn continuing_words_carry_waves_contact_and_resonator_states() {
    use super::contact_residual::{ContactCut, CutKind, Refusal};
    let field = chain().with_exact_word();
    let theta = resonant(&field, generic(&field, 73));
    let current = Current::at_rest(&field);
    let operands = Operands::exact_at_cut(&field, &theta, &current).unwrap();
    let injected = storage(&field, 74);
    let mut whole = Word::on_operands(&field, operands.clone(), injected.clone()).unwrap();
    whole.run(4).unwrap();
    let mut first = Word::on_operands(&field, operands.clone(), injected).unwrap();
    first.run(2).unwrap();
    let carried = first.change().unwrap();
    let nothing: Vec<Vec<Rat>> = carried
        .storage
        .iter()
        .map(|wave| vec![Rat::zero(); wave.len()])
        .collect();
    let cut = ContactCut::read(&first, &theta, &current).unwrap();
    assert!(matches!(cut.continuing(&field,&theta,&current,&nothing,3),Err(Refusal::Clock)));
    let mut wrong_phase = cut.clone();
    wrong_phase.change.resonator_phases[0] = Some(1-cut.change.resonator_phases[0].unwrap());
    assert!(matches!(wrong_phase.continuing(&field,&theta,&current,&nothing,2),Err(Refusal::Phase)));
    let mut wrong_cut = cut.clone();
    wrong_cut.kind = CutKind::AfterJunction;
    assert!(matches!(wrong_cut.continuing(&field,&theta,&current,&nothing,2),Err(Refusal::Cut(CutKind::AfterJunction))));
    let mut second = cut.continuing(&field, &theta, &current, &nothing, 2).unwrap();
    let second_open = ContactCut::read(&second,&theta,&current).unwrap();
    second.run(2).unwrap();
    let receipt = second_open.first_step(&second,&theta,&current,0).unwrap();
    assert!(receipt.boundary_advanced);
    if let Some(remainder) = receipt.remainder {
        assert!(remainder.iter().all(Zero::is_zero));
    } // A singular stationary chart keeps its fibre; motion and the complete opening were checked.
    assert_eq!(second.change().unwrap(), whole.change().unwrap());
    assert!(
        carried
            .resonators
            .iter()
            .flatten()
            .flatten()
            .flatten()
            .any(|x| !x.is_zero()),
        "the resonator states carried are not at rest"
    );
    let (last, next) = (
        first.field_balances().last().unwrap(),
        &second.field_balances()[0],
    );
    assert_eq!(last.after, next.before);
    assert_eq!(last.resonator_after, next.resonator_before);
    for tick in first.field_balances().iter().chain(second.field_balances()) {
        assert!(tick.closes(), "{tick:?}");
    }
    assert_eq!(second.field_balances(), &whole.field_balances()[2..]);
}

/// **A reception carries the motion from its last crossing** (record B §2.4): a junction is a
/// crossing, the clock's tick, and the hop after it runs the elements, the pumped resonators at that
/// tick's phase and the transits. A word that ends at a last junction has scattered crossing `T`
/// for its reading and has not run hop `T`, so its carry is the change arriving at `T`, every
/// resonator state and phase as hop `T − 1` left them, at tick `T`. Under the exact law the word
/// opened there with nothing injected continues the uninterrupted word exactly, pumped resonators
/// included: the same change and the same balances tick for tick. The change after the last
/// junction, opened one tick later, does not: on a pumped field its phase misses the clock (the
/// refusal the carry first had), and on an unpumped field crossing `T` is scattered twice, which
/// the junction's involution undoes (Lean `HNN/Propagation.junctionScattering_involutive`), so hop
/// `T` would run on the unscattered waves.
#[test]
fn the_reception_carry_continues_from_the_last_crossing() {
    let field = chain().with_exact_word();
    let nothing = |field: &Field| -> Vec<Vec<Rat>> {
        field.rings().iter().map(|ring| vec![Rat::zero(); ring.width()]).collect()
    };
    for (theta, pumped) in [
        (resonant(&field, generic(&field, 75)), true),
        (generic(&field, 75), false),
    ] {
        let current = Current::at_rest(&field);
        let operands = Operands::exact_at_cut(&field, &theta, &current).unwrap();
        let injected = storage(&field, 76);
        let mut whole = Word::on_operands(&field, operands.clone(), injected.clone()).unwrap();
        whole.run(5).unwrap();
        let mut first = Word::on_operands(&field, operands.clone(), injected).unwrap();
        first.run(3).unwrap();
        first.last_junction().unwrap();
        let carry = first.reception_end().unwrap();
        assert_eq!(carry.ticks, 3, "the last crossing's tick, its hop not run");
        for (ring, resonator) in operands.resonators().iter().enumerate() {
            let phase = resonator.as_ref().map(|resonator| resonator.phase_at(2));
            assert_eq!(carry.change.resonator_phases[ring], phase);
            assert_eq!(carry.change.resonators[ring].is_some(), pumped);
        }
        let mut second =
            Word::continuing(&field, operands.clone(), &carry.change, &nothing(&field), carry.ticks)
                .unwrap();
        second.run(2).unwrap();
        assert_eq!(second.change().unwrap(), whole.change().unwrap());
        assert_eq!(second.field_balances(), &whole.field_balances()[3..]);
        let after = first.released().unwrap().end;
        let late = Word::continuing(&field, operands.clone(), &after, &nothing(&field), 4);
        if pumped {
            assert!(matches!(late, Err(crate::hnn::HnnError::Resonator { .. })));
        } else {
            let mut late = late.unwrap();
            late.run(2).unwrap();
            assert_ne!(late.change().unwrap(), whole.change().unwrap());
        }
    }
}

// -------------------------------------------------------------------------------------------
// the order repair: the joint residue class, the section's placement and the lock

/// **A joint-residue field**: three rings of period `6 = 2·3` in a chain `0 — 1 — 2`, joined node to
/// node on every node at exponent 0; ring 0 the source and receiving ring, stepping every cell (its
/// lock every port), rings 1 and 2 stepping by carries; no pair offset; `|A| = 3`, the last class
/// the termination.
pub(super) fn joint() -> Field {
    Field::declare(
        crate::hnn::field::FieldDeclaration {
            rings: vec![
                super::support::ring(6, (0..6).collect()),
                super::support::ring(6, Vec::new()),
                super::support::ring(6, Vec::new()),
            ],
            contacts: vec![
                super::support::contact(0, 1, 6, 0),
                super::support::contact(1, 2, 6, 0),
            ],
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: 3,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![crate::hnn::field::ReceiverDeclaration {
                ring: 0,
                aperture: 3,
                tolerance: rat(1, 16),
                depth: 1,
                prior: crate::compression::landmark::context::StopPrior::half(),
                mass: 1,
                base: crate::compression::landmark::context::BaseMeasure::Even,
                receiving_prior: 0,
            }],
            crib: crate::hnn::field::CribDeclaration {
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

/// **A placed datum is read at its station's residue, in the passage's one population**
/// (`SourceMoment::continued`; Lean `HNN/IndexedOpen.{passage_population, passage_read}`): the
/// datum locked at station `j` is counted into the request's phase counts at the receiving ring's
/// residue `τ + 1 + j`, the passage's population is the request's `n` plus the placed data, and the
/// open storage is the request's counts and the datum's column of `E`, rotated to station `j`'s
/// frame by `P^(1+j)`, together over `ν̂(n + 1)`.
#[test]
fn a_placed_datum_is_read_at_its_station_residue() {
    let field = joint();
    let theta = generic(&field, 91);
    let (current, request) = moment(&field, 92, 7);
    let phase = current.phase(&field, 0).unwrap() as usize;
    let n = request.population(0).unwrap();
    let nu = crate::hnn::moment::PopulationChart::of(&field).value(n + 1);
    let port = theta.source_port(0).unwrap();
    let ring = field.ring(0);
    let (reads, pairs) = request.open_parts(&field, &theta, &current, 0).unwrap();
    assert!(pairs.iter().all(Rat::is_zero));
    let mut marginal = vec![Rat::zero(); ring.width()];
    for (_, read) in &reads {
        for (value, add) in marginal.iter_mut().zip(read) {
            *value += add;
        }
    }
    for station in 0..4 {
        for code in 0..field.alphabet() {
            let mut cells = vec![None; 4];
            cells[station] = Some(code);
            let passage = request.continued(&field, &current, 0, &cells).unwrap();
            assert_eq!(passage.cells(), request.cells() + 1);
            assert_eq!(passage.population(0).unwrap(), n + 1);
            let residue = (phase + 1 + station) % 6;
            assert_eq!(
                passage.phase_counts(0, residue).unwrap()[code],
                request.phase_counts(0, residue).unwrap()[code] + 1
            );
            let open = passage.open_storage(&field, &theta, &current).unwrap();
            let read = ring.rotate(&open[0], &BigInt::from(station as u64 + 1));
            let column: Vec<Rat> = (0..ring.width())
                .map(|row| port.get(row, code).unwrap().clone())
                .collect();
            let request_read = ring.rotate(&marginal, &BigInt::from(station as u64 + 1));
            let expected: Vec<Rat> = request_read
                .iter()
                .zip(&column)
                .map(|(r, c)| (r + c) * &nu)
                .collect();
            assert_eq!(read, expected);
        }
    }
}

/// **One passage weighs every datum alike** (the September 30 located cause, repaired; Lean
/// `HNN/IndexedOpen.{passage_weight_one_population, separate_populations_ratio}`): in the passage's
/// open, a request cell and a section datum at the same class and residue class enter with the
/// same weight `ν̂(n + v)`, so moving a crossing from the request to the section moves nothing but
/// its tick; read over separate populations, the section's datum weighed `n/v` times the request's.
#[test]
fn one_passage_weighs_every_datum_alike() {
    let field = joint();
    let theta = generic(&field, 91);
    // Seven cells ingested and their continuation by one placed datum, against eight cells
    // ingested: the same passage, split at a different tick.
    let cells = [2usize, 0, 1, 1, 0, 2, 1, 0];
    let (whole_current, whole) = {
        let mut current = Current::at_rest(&field);
        let mut moment = SourceMoment::open(&field, &current);
        moment.ingest(&field, &mut current, &encoded(&field, &cells)).unwrap();
        (current, moment)
    };
    let (current, request) = {
        let mut current = Current::at_rest(&field);
        let mut moment = SourceMoment::open(&field, &current);
        moment.ingest(&field, &mut current, &encoded(&field, &cells[..7])).unwrap();
        (current, moment)
    };
    // The joint field's receiving ring steps every cell, so the continuation's station 0 is the
    // eighth cell's tick.
    let passage = request
        .continued(&field, &current, 0, &[Some(cells[7]), None, None, None])
        .unwrap();
    assert_eq!(passage.population(0).unwrap(), whole.population(0).unwrap());
    for c in 0..6 {
        assert_eq!(passage.phase_counts(0, c).unwrap(), whole.phase_counts(0, c).unwrap());
    }
    // The same counts and population: the same open, read at the request's frame (the whole
    // passage's frame is one tick on, the rotation between them).
    let open = passage.open_storage(&field, &theta, &current).unwrap();
    let whole_open = whole.open_storage(&field, &theta, &whole_current).unwrap();
    assert_eq!(field.ring(0).rotate(&open[0], &BigInt::one()), whole_open[0]);
}

/// **The partition law** (`prediction::mask`): at least one station is always compared, and every
/// number of locked stations `0 … m − 1` is drawn.
#[test]
fn the_mask_compares_a_station_and_reaches_every_level() {
    let mut draw = crate::holarchy::terrain::Draw::new(95);
    let mut levels = [0usize; 8];
    for _ in 0..512 {
        let locked = crate::hnn::prediction::mask(&mut draw, 8);
        let count = locked.iter().filter(|&&lock| lock).count();
        assert!(count < 8);
        levels[count] += 1;
    }
    assert!(levels.iter().all(|&count| count > 0), "{levels:?}");
}

/// **The bank's placement is the section's injection** (`prediction::BankPlacement`): at a
/// transport of modulus one the receiving ring's storage with any set of stations placed, read from
/// any station, equals the open storage of the passage (the request's moment continued by the
/// section, `SourceMoment::continued`), exactly, every datum at `ν̂(n + v)` in every frame; with
/// nothing placed it is the request's own.
#[test]
fn the_bank_placement_is_the_sections_injection() {
    let field = joint();
    let theta = generic(&field, 91);
    let (current, request) = moment(&field, 92, 7);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let placement =
        BankPlacement::of(&field, &theta, &current, &request, &refinement).unwrap();
    let patterns: [[Option<usize>; 4]; 5] = [
        [None; 4],
        [Some(1), None, None, None],
        [None, Some(2), None, Some(0)],
        [Some(0), Some(0), Some(1), None],
        [Some(2), Some(1), Some(0), Some(1)],
    ];
    for cells in &patterns {
        let passage = request.continued(&field, &current, 0, cells).unwrap();
        let injected = passage.open_storage(&field, &theta, &current).unwrap();
        let placed = cells.iter().filter(|cell| cell.is_some()).count() as u64;
        let nu = crate::hnn::moment::PopulationChart::of(&field)
            .value(request.population(0).unwrap() + placed);
        for station in 0..4 {
            assert_eq!(placement.storage(station, cells), injected[0]);
            let (request_weights, station_weights) = placement.weights(station, cells);
            assert!(request_weights.iter().all(|w| *w == nu));
            for (cell, weight) in cells.iter().zip(&station_weights) {
                assert_eq!(weight.as_ref(), cell.map(|_| &nu));
            }
        }
    }
    let open = request.open_storage(&field, &theta, &current).unwrap();
    assert_eq!(placement.storage(0, &[None; 4]), open[0]);
}

/// **Under a dissipative transport a candidate reads the span from its own station**
/// (`prediction::BankPlacement`, the station-framed law; Lean
/// `HNN/IndexedOpen.{framed_weight_mass, framed_weight_one_sided, framed_weight_ratio,
/// framed_weight_symmetric}`): at a transport modulus `ρ = 3/4`, read from station `j`,
/// - every datum weighs `ρ^|τ_j − τ_k|` over the span's transported mass read from `j`, on the
///   population chart: the weights carry unit mass within the chart's residual;
/// - when no placed datum lies after `j`, the storage equals the continued passage's open (read
///   at the span's last datum) exactly: the one-way law on past data;
/// - a placed datum `r` ticks from `j`, on either side, weighs `ρ^r` times `j`'s own candidate
///   (within the chart's residual), so two data at equal distance on either side weigh alike, and a
///   lock after `j` weighs less than the candidate, where the one-way law read at the span's end
///   weighs it `ρ^(−r)` times the candidate;
/// - the modulus's derivative matches the exact weights' central difference to the second order;
/// - a request whose span with the stations exceeds one turn is refused, as is a modulus outside
///   `(0, 1]`.
#[test]
fn the_bank_placement_under_a_dissipative_transport() {
    use crate::hnn::HnnError;
    use crate::hnn::moment::{PopulationChart, modulus_power};
    let field = joint();
    let theta = generic(&field, 91);
    assert_eq!(theta.transport(0), Rat::one());
    assert!(matches!(
        theta.clone().with_transport(0, Rat::zero()),
        Err(HnnError::Transport { .. })
    ));
    assert!(matches!(
        theta.clone().with_transport(0, rat(5, 4)),
        Err(HnnError::Transport { .. })
    ));
    let modulus = rat(3, 4);
    let theta = theta.with_transport(0, modulus.clone()).unwrap();
    assert_eq!(theta.transport(0), modulus);
    // Two cells and four stations fill the ring's turn of six ticks.
    let (current, request) = moment(&field, 92, 2);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let placement = BankPlacement::of(&field, &theta, &current, &request, &refinement).unwrap();
    let chart = PopulationChart::of(&field);
    let near = |a: &Rat, b: &Rat, slack: &Rat| (a - b).abs() <= *slack;
    let patterns: [[Option<usize>; 4]; 6] = [
        [None; 4],
        [Some(1), None, None, None],
        [None, Some(2), None, Some(0)],
        [Some(0), Some(0), Some(1), None],
        [Some(2), Some(1), Some(0), Some(1)],
        [Some(0), Some(1), Some(2), Some(0)],
    ];
    let mut two_sided = 0usize;
    for cells in &patterns {
        let passage = request.continued(&field, &current, 0, cells).unwrap();
        let injected = passage.open_storage(&field, &theta, &current).unwrap();
        let last = cells.iter().rposition(Option::is_some);
        for station in 0..4 {
            let (request_weights, station_weights) = placement.weights(station, cells);
            // Every datum's weight within the chart's residual of its exact transported weight, the
            // exact weights summing to one: so the charted mass lies within one residual a datum.
            let data: Vec<Rat> = request_weights
                .iter()
                .cloned()
                .chain(station_weights.iter().flatten().cloned())
                .collect();
            let counted: Rat = data.iter().sum();
            let slack = chart.residual() * Rat::from_integer(BigInt::from(data.len() as u64 + 2));
            assert!((&counted - Rat::one()).abs() <= slack, "{counted}");
            // On past data the one-way law, read at the span's last datum, exactly.
            if last.is_none_or(|last| last <= station) {
                assert_eq!(placement.storage(station, cells), injected[0]);
            } else {
                two_sided += 1;
            }
            // A placed datum r ticks away, on either side, weighs ρ^r times the station's own
            // candidate (every weight within the chart's residual of its exact value).
            if let Some(own) = &station_weights[station] {
                let residual = chart.residual() * integer(2);
                for (placed, weight) in station_weights.iter().enumerate() {
                    let Some(weight) = weight else { continue };
                    let r = placed.abs_diff(station) as u64;
                    let power = modulus_power(&modulus, r);
                    assert!(near(weight, &(own * &power), &residual), "ρ^{r} of the candidate");
                    if placed > station {
                        assert!(weight < own, "a later lock weighs less than the candidate");
                    }
                }
                // Two data at equal distance on either side weigh alike.
                if station >= 1 && station + 1 < 4 {
                    if let (Some(before), Some(after)) =
                        (&station_weights[station - 1], &station_weights[station + 1])
                    {
                        assert_eq!(before, after);
                    }
                }
            }
            // The modulus's derivative against the exact weights' central difference: second order.
            if cells.iter().any(Option::is_some) {
                let derivative = placement.modulus_derivative(station, cells);
                // Each datum's reach slope rebuilds it, datum by datum, within the held grain.
                let grain = Rat::new(1.into(), BigInt::from(1) << 160usize);
                for (rebuilt, d) in placement.reach_derivative(station, cells).iter().zip(&derivative) {
                    assert!((rebuilt - d).abs() <= grain, "the reach slopes rebuild ∂z/∂ρ");
                }
                let residual = |h: &Rat| -> Rat {
                    let up = placement.exact_storage(station, cells, &(&modulus + h));
                    let down = placement.exact_storage(station, cells, &(&modulus - h));
                    up.iter()
                        .zip(&down)
                        .zip(&derivative)
                        .map(|((u, d), g)| ((u - d) / (integer(2) * h) - g).abs())
                        .max()
                        .unwrap()
                };
                let (wide, narrow) = (residual(&rat(1, 64)), residual(&rat(1, 128)));
                assert!(narrow * integer(3) <= wide, "the central difference is second order");
            }
        }
    }
    assert!(two_sided > 0, "some reading holds a lock after its station");
    // The one-way law read at the span's end against the framed law, from station 0 with a lock at
    // station 3: the end frame weighs the lock ρ^(−3) times station 0's candidate, the framed law
    // ρ^3 times.
    let cells = [Some(1), None, None, Some(0)];
    let passage = request.continued(&field, &current, 0, &cells).unwrap();
    let oneway = passage.phase_weights(&field, 0, &modulus).unwrap();
    let phase = current.phase(&field, 0).unwrap() as usize;
    let (at0, at3) = (&oneway[(phase + 1) % 6], &oneway[(phase + 4) % 6]);
    let power = modulus_power(&modulus, 3);
    let residual = chart.residual() * integer(2);
    assert!(near(at0, &(at3 * &power), &residual));
    let (_, framed) = placement.weights(0, &cells);
    let (own, lock) = (framed[0].clone().unwrap(), framed[3].clone().unwrap());
    assert!(near(&lock, &(&own * &power), &residual));
    assert!(lock < own && at3 > at0);
    // Seven cells and four stations span more than the turn of six: refused below modulus one.
    let (long_current, long_request) = moment(&field, 92, 7);
    assert!(matches!(
        BankPlacement::of(&field, &theta, &long_current, &long_request, &refinement),
        Err(HnnError::AliasedAges { .. })
    ));
}

/// **The transport is founded off the lossless boundary** (`Constitution::founding_transport`;
/// Lean `HNN/IndexedOpen.{IsFounding, founded_modulus_pow_le, founded_modulus_greatest,
/// founded_modulus_lt_one, order_founding}`): the founding modulus is the greatest on the source
/// port's lattice whose one-turn transport is at most one unit of the weights' chart,
/// `ρ₀^d ≤ 2^(−L_ν) < (ρ₀ + 2^(−L_s))^d`, strictly between zero and one; the order-2 declaration
/// (`d = 60`, `L_ν = L_s = 21`) founds at `102837/131072`; on the joint field's ring of period 6 the
/// founded constitution carries it, and a ring with no source port refuses it.
#[test]
fn the_transport_is_founded_off_the_lossless_boundary() {
    use crate::hnn::HnnError;
    use crate::hnn::constitution::{Locus, founding_modulus};
    use crate::hnn::moment::PopulationChart;
    let check = |lattice: u32, period: u64, chart: u32| -> Rat {
        let modulus = founding_modulus(lattice, period, chart).unwrap();
        let unit = Rat::new(BigInt::one(), BigInt::one() << lattice as usize);
        let grain = Rat::new(BigInt::one(), BigInt::one() << chart as usize);
        let power = |x: &Rat| (0..period).fold(Rat::one(), |p, _| p * x);
        assert!(modulus.is_positive() && modulus < Rat::one());
        assert!((&modulus / &unit).is_integer());
        assert!(power(&modulus) <= grain);
        assert!(power(&(&modulus + &unit)) > grain);
        modulus
    };
    assert_eq!(check(21, 60, 21), rat(102837, 131072));
    assert_eq!(check(21, 35, 21), rat(345901, 524288));
    assert_eq!(founding_modulus(2, 3, 7), None);
    let field = joint();
    let theta = generic(&field, 91);
    let lattice = theta.lattice(Locus::SourcePort(0)).unwrap().exponent();
    let chart = PopulationChart::of(&field).exponent();
    let founded = theta.clone().founded_transport(&field, 0).unwrap();
    assert_eq!(
        founded.transport(0),
        check(lattice, field.ring(0).period(), chart)
    );
    assert_eq!(founded.transport(0), theta.founding_transport(&field, 0).unwrap());
    assert!(matches!(
        theta.founding_transport(&field, 1),
        Err(HnnError::MissingSourcePort { ring: 1 })
    ));
}

/// **The bank generates by its locks** (`prediction::generate_by_bank`): on the joint field's ring of
/// period 6, a bank of the members whose period divides the turn (standing and half-turn) reads
/// every unlocked station's candidates, locks the stations of the largest gap, each lock certified
/// on both members with every executed tick closed and its growth above the runner-up's; a
/// released section is released at width zero with every station locked once.
#[test]
fn the_bank_generates_by_its_certified_locks() {
    let field = joint();
    let theta = generic(&field, 94);
    let (current, request) = moment(&field, 95, 9);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let identity = ExactRatMatrix::identity(2).unwrap();
    let axis = Carrier::new(Rat::one(), Rat::zero()).unwrap();
    let bank = ReceivingBank::new(
        ResonatorMaterial::new(
            identity.clone(),
            identity,
            ExactRatMatrix::zero(2, 2).unwrap(),
            None,
        )
        .unwrap(),
        [PumpStep::Stand, PumpStep::Half]
            .into_iter()
            .map(|step| PumpDeclaration::new(rat(5, 8), axis.clone(), step).unwrap())
            .collect(),
        integer(16),
        Rat::one(),
        6,
    )
    .unwrap();
    let generated =
        generate_by_bank(&field, &theta, &current, &request, &refinement, &bank, 12).unwrap();
    let locked: usize = generated.locks.iter().map(Vec::len).sum();
    assert!(generated.contacts.is_empty());
    assert_eq!(generated.decisions.len(), locked);
    assert_eq!(generated.members, 2 * locked);
    assert_eq!(generated.certified, generated.members);
    assert_eq!(generated.ticks_closed, generated.ticks);
    for (_, _, growth, runner) in &generated.decisions {
        assert!(growth.exceeds(runner) && growth.is_locked());
    }
    if generated.release.released() {
        assert!(generated.release.width.is_zero());
        let mut stations: Vec<usize> = generated.locks.iter().flatten().copied().collect();
        stations.sort_unstable();
        assert_eq!(stations, vec![0, 1, 2, 3]);
        assert_eq!(generated.refinements, generated.locks.len());
    } else {
        assert_eq!(generated.refinements, generated.locks.len() + 1);
        assert!(!generated.release.plural.is_empty());
    }
}

/// [definition; agent-inferred, October 2; the
/// [contact loop record](../../../../../research/records/2026-10-02_THE_CONTACT_LOOP_THE_RETURN_REACHES_EVERY_CONTACT_AND_ITS_CHANGE_IS_RELEASED_BEFORE_THE_LATER_CUT.md)
/// §5, Astra's second unit] **A contact's change is read by the continued word, with its work**:
/// under the exact law, one word's retained change `x` continues at the predecessor and at a
/// successor whose contact 0 storage factor moved (a control chart until the deposit's own contact
/// moves land), with the same later drive (nothing injected, four ticks) and clock. The successor's continued
/// word opens on `x` at exactly the predecessor's power plus the deposition work `½⟨x, ΔΘ x⟩`
/// (`PowerForm::deposition_work`); every tick of both closes; and the moved contact's states, its
/// outgoing waves and the receiving ring's storage differ at the end.
#[test]
fn a_contact_change_has_a_unique_reflected_storage_receipt() {
    use super::contact_residual::{ContactCut, Read, Refusal};
    use crate::hnn::word::PowerForm;
    let field = chain().with_exact_word();
    // Declare the stationary chart's domain; the singular cases keep their fibres separately.
    let theta = generic(&field, 73);
    let theta = theta.clone().with_channel(0, theta.contact_storage(0).clone(),
        ExactRatMatrix::identity(field.contact(0).width()).unwrap(),
        theta.contact_dissipation(0).clone()).unwrap();
    let current = Current::at_rest(&field);
    let operands = Operands::exact_at_cut(&field, &theta, &current).unwrap();
    let mut first = Word::on_operands(&field, operands, storage(&field, 74)).unwrap();
    first.run(2).unwrap();
    let x = first.change().unwrap();
    let cut = ContactCut::read(&first, &theta, &current).unwrap();
    let mut factor = theta.contact_storage(0).to_rows();
    factor[0][0] += rat(1, 2);
    let next = theta
        .clone()
        .with_channel(
            0,
            ExactRatMatrix::new(factor).unwrap(),
            theta.contact_stiffness(0).clone(),
            theta.contact_dissipation(0).clone(),
        )
        .unwrap();
    let nothing: Vec<Vec<Rat>> = x.storage.iter().map(|w| vec![Rat::zero(); w.len()]).collect();
    assert!(matches!(cut.continuing(&field,&theta,&current,&nothing,3),Err(Refusal::Clock)));
    assert!(matches!(ContactCut::read(&first,&next,&current),Err(Refusal::Producer)));
    let continued = |constitution: &Constitution| {
        let mut word = cut.continuing(&field, constitution, &current, &nothing, 2).unwrap();
        let open = ContactCut::read(&word,constitution,&current).unwrap();
        word.run(1).unwrap();
        let receipt = open.first_step(&word,constitution,&current,0).unwrap();
        assert!(!receipt.boundary_advanced);
        assert!(receipt.remainder.as_ref().unwrap().iter().all(Zero::is_zero));
        for read in [&receipt.before,&receipt.next] {
            let Read::Unique(read) = read else { panic!("declared nonsingular stiffness") };
            assert!(read.closes());
        }
        let mut wrong_open = open.clone();
        wrong_open.change.storage[0][0] += Rat::one();
        assert!(matches!(wrong_open.first_step(&word,constitution,&current,0),Err(Refusal::Step)));
        word.run(1).unwrap();
        let advanced = open.first_step(&word,constitution,&current,0).unwrap();
        assert!(advanced.boundary_advanced);
        assert!(advanced.remainder.as_ref().unwrap().iter().all(Zero::is_zero));
        let (Read::Unique(a),Read::Unique(b)) = (&advanced.before,&advanced.next) else {panic!("unique chart")};
        assert_ne!(a.boundary,b.boundary,"the actual next junction moved the boundary");
        assert!(a.closes() && b.closes());
        word.run(2).unwrap();
        word
    };
    let (before, after) = (continued(&theta), continued(&next));
    let (old, new) = (
        PowerForm::read(&field, &theta, &current).unwrap(),
        PowerForm::read(&field, &next, &current).unwrap(),
    );
    let work = old.deposition_work(&new, &x).unwrap();
    let declared = field.contact(0);
    let (from,to) = declared.ends();
    let boundary = [(from,crate::hnn::field::End::From),(to,crate::hnn::field::End::To)]
        .map(|(ring,end)| declared.selection(end).into_iter().map(|i|
            integer(2)*&before.anchor(0,ring).unwrap()[i]-&x.arrivals[0][usize::from(ring!=from)][i]
        ).collect());
    let deposition = cut.control_deposit(&next,0,&boundary).unwrap();
    assert!(deposition.closes());
    assert_eq!(deposition.work,work);
    assert!(!work.is_zero());
    assert_eq!(before.field_balances()[0].before, old.power(&x).unwrap());
    assert_eq!(after.field_balances()[0].before, new.power(&x).unwrap());
    assert_eq!(new.power(&x).unwrap() - old.power(&x).unwrap(), work);
    for tick in before.field_balances().iter().chain(after.field_balances()) {
        assert!(tick.closes(), "{tick:?}");
    }
    let (a, b) = (before.change().unwrap(), after.change().unwrap());
    assert_ne!(a.states[0], b.states[0]);
    assert_ne!(a.arrivals[0], b.arrivals[0]);
    let receiver = field.receivers()[0].ring;
    assert_ne!(a.storage[receiver], b.storage[receiver]);
    // Campaign one's unloaded contact fixture has no inherited resonator storage term.
    for word in [before,after] {
        let balance = crate::hnn::word::WordBalance::of(&word.release().unwrap());
        assert!(balance.resonator_end.is_zero());
        assert!(balance.closes());
    }
}

/// A post-junction release is a different cut, never silently resumed as a full-tick cut.
#[test]
fn the_private_contact_cut_refuses_a_terminal_junction() {
    use super::contact_residual::{ContactCut,CutKind,Refusal};
    let field = chain().with_exact_word();
    let theta = generic(&field,73);
    let current = Current::at_rest(&field);
    let mut word = Word::on_operands(&field,Operands::exact_at_cut(&field,&theta,&current).unwrap(),storage(&field,74)).unwrap();
    word.run(1).unwrap();
    word.last_junction().unwrap();
    assert!(matches!(ContactCut::read(&word,&theta,&current),Err(Refusal::Cut(CutKind::AfterJunction))));
}

/// Join the existing native deposited return, including its clocks, statistics and carries, to
/// the same-state reflected chart and work. This is a staged-material control, not a claim that
/// the hand-built factor covector came from an HNN comparison.
#[test]
fn a_native_contact_successor_carries_its_publication_and_reflected_work() {
    use super::contact_residual::{ContactCut,Read,Refusal};
    use super::learning::{OPEN_BUDGET,chain_reach};
    use crate::hnn::constitution::{FactorGradient,FactorStep,Locus};
    use crate::hnn::port::Deposit;
    let field = chain().with_exact_word();
    let theta = Constitution::initial(&field,OPEN_BUDGET).unwrap();
    let current = Current::at_rest(&field);
    let mut first = Word::on_operands(&field,Operands::exact_at_cut(&field,&theta,&current).unwrap(),storage(&field,74)).unwrap();
    first.run(2).unwrap();
    let cut = ContactCut::read(&first,&theta,&current).unwrap();
    let deposit = Deposit::new(theta.commit(),Vec::new(),vec![FactorStep {
        gradient:FactorGradient::Storage {contact:0,
            gradient:ExactRatMatrix::identity(field.contact(0).width()).unwrap()},
        energy:Rat::zero(),covector:Rat::one(),
    }],vec![Locus::Channel(0)]).with_reach(chain_reach());
    let (next,publication) = theta.deposited(&deposit).unwrap();
    assert_eq!(next.commit(),theta.commit()+1);
    assert_eq!(next.clock(Locus::Channel(0)),theta.clock(Locus::Channel(0))+1);
    assert!(publication.stepped>0);
    assert_ne!(next.contact_storage(0),theta.contact_storage(0));
    let nothing:Vec<_> = cut.change.storage.iter().map(|v|vec![Rat::zero();v.len()]).collect();
    let mut continued = cut.continuing(&field,&next,&current,&nothing,2).unwrap();
    let opening = ContactCut::read(&continued,&next,&current).unwrap();
    continued.run(2).unwrap();
    let movement = opening.first_step(&continued,&next,&current,0).unwrap();
    assert!(movement.boundary_advanced);
    assert!(movement.remainder.as_ref().unwrap().iter().all(Zero::is_zero));
    let Read::Unique(read) = &movement.before else {panic!("initial stiffness is nonsingular")};
    let width = field.contact(0).width();
    let x = [read.boundary[..width].to_vec(),read.boundary[width..].to_vec()];
    let receipt = cut.deposited_return(&deposit,&next,&publication,0,&x).unwrap();
    assert!(receipt.closes());
    assert!(!receipt.work.is_zero());
    assert_eq!(receipt.publication.as_ref(),Some(&publication));
    let replacement = theta.clone().with_channel(0,next.contact_storage(0).clone(),
        next.contact_stiffness(0).clone(),next.contact_dissipation(0).clone()).unwrap();
    assert!(matches!(cut.deposited_return(&deposit,&replacement,&publication,0,&x),Err(Refusal::Producer)));
    let mut wrong_publication = publication.clone();
    wrong_publication.commit += 1;
    assert!(matches!(cut.deposited_return(&deposit,&next,&wrong_publication,0,&x),Err(Refusal::Producer)));
}

/// Original generic-stiffness continuation control, retained verbatim alongside the unique chart.
#[test]
fn a_contact_change_is_read_by_the_continued_word_with_its_work() {
    use crate::hnn::word::PowerForm;
    let field = chain().with_exact_word();
    let theta = generic(&field, 73);
    let current = Current::at_rest(&field);
    let operands = Operands::exact_at_cut(&field, &theta, &current).unwrap();
    let mut first = Word::on_operands(&field, operands, storage(&field, 74)).unwrap();
    first.run(2).unwrap();
    let x = first.change().unwrap();
    let mut factor = theta.contact_storage(0).to_rows();
    factor[0][0] += rat(1, 2);
    let next = theta
        .clone()
        .with_channel(
            0,
            ExactRatMatrix::new(factor).unwrap(),
            theta.contact_stiffness(0).clone(),
            theta.contact_dissipation(0).clone(),
        )
        .unwrap();
    let nothing: Vec<Vec<Rat>> = x.storage.iter().map(|w| vec![Rat::zero(); w.len()]).collect();
    let continued = |constitution: &Constitution| {
        let operands = Operands::exact_at_cut(&field, constitution, &current).unwrap();
        let mut word = Word::continuing(&field, operands, &x, &nothing, 2).unwrap();
        word.run(4).unwrap();
        word
    };
    let (before, after) = (continued(&theta), continued(&next));
    let (old, new) = (
        PowerForm::read(&field, &theta, &current).unwrap(),
        PowerForm::read(&field, &next, &current).unwrap(),
    );
    let work = old.deposition_work(&new, &x).unwrap();
    assert!(!work.is_zero());
    assert_eq!(before.field_balances()[0].before, old.power(&x).unwrap());
    assert_eq!(after.field_balances()[0].before, new.power(&x).unwrap());
    assert_eq!(new.power(&x).unwrap() - old.power(&x).unwrap(), work);
    for tick in before.field_balances().iter().chain(after.field_balances()) {
        assert!(tick.closes(), "{tick:?}");
    }
    let (a, b) = (before.change().unwrap(), after.change().unwrap());
    assert_ne!(a.states[0], b.states[0]);
    assert_ne!(a.arrivals[0], b.arrivals[0]);
    let receiver = field.receivers()[0].ring;
    assert_ne!(a.storage[receiver], b.storage[receiver]);
}

/// Native production receipts include the actual inherited storage at both endpoints.
#[test]
fn inherited_resonator_opening_closes_native_balances() {
    use crate::hnn::word::{ResonatorBalance,WordBalance};
    let field=chain().with_exact_word();
    let theta=resonant(&field,generic(&field,73));
    let current=Current::at_rest(&field);
    let operands=Operands::exact_at_cut(&field,&theta,&current).unwrap();
    let mut first=Word::on_operands(&field,operands.clone(),storage(&field,74)).unwrap();
    first.run(2).unwrap();
    let carried=first.change().unwrap();
    let nothing:Vec<_>=carried.storage.iter().map(|v|vec![Rat::zero();v.len()]).collect();
    let mut next=Word::continuing(&field,operands,&carried,&nothing,2).unwrap();
    next.run(2).unwrap();
    let mut opening=Rat::zero();
    for (ring,resonance) in next.resonances().iter().enumerate() {
        if let Some(resonance)=resonance {
            let b=ResonatorBalance::of(ring,resonance);
            assert_eq!(b.open,resonance.steps[0].before);
            assert!(!b.open.is_zero());
            assert!(b.closes());
            opening+=b.open;
        }
    }
    let balance=WordBalance::of(&next.release().unwrap());
    assert_eq!(balance.resonator_open,opening);
    assert!(balance.closes());
    assert!(WordBalance::of(&first.release().unwrap()).closes());
}

#[test]
fn a_zero_tick_native_word_keeps_inherited_resonator_storage() {
    use crate::hnn::word::{PowerForm,WordBalance};
    let field=chain().with_exact_word();
    let theta=resonant(&field,generic(&field,73));
    let current=Current::at_rest(&field);
    let operands=Operands::exact_at_cut(&field,&theta,&current).unwrap();
    let mut first=Word::on_operands(&field,operands.clone(),storage(&field,74)).unwrap();
    first.run(2).unwrap();
    let carried=first.change().unwrap();
    let energy=PowerForm::read(&field,&theta,&current).unwrap().resonator_power(&carried).unwrap();
    assert!(!energy.is_zero());
    let nothing:Vec<_>=carried.storage.iter().map(|v|vec![Rat::zero();v.len()]).collect();
    let next=Word::continuing(&field,operands,&carried,&nothing,2).unwrap();
    let released=next.release().unwrap();
    for b in &released.resonators {assert_eq!(b.open,b.end);assert!(b.closes());}
    let balance=WordBalance::of(&released);
    assert_eq!(balance.resonator_open,energy);
    assert_eq!(balance.resonator_end,energy);
    assert!(balance.closes());
}

/// A native refusal certifies phase compatibility; it does not prove an absolute carried clock.
#[test]
fn native_continuing_refuses_an_incompatible_carried_phase() {
    let field=chain().with_exact_word();
    let theta=resonant(&field,generic(&field,73));
    let current=Current::at_rest(&field);
    let operands=Operands::exact_at_cut(&field,&theta,&current).unwrap();
    let mut first=Word::on_operands(&field,operands.clone(),storage(&field,74)).unwrap();
    first.run(2).unwrap();
    let mut carried=first.change().unwrap();
    let nothing:Vec<_>=carried.storage.iter().map(|v|vec![Rat::zero();v.len()]).collect();
    carried.resonator_phases[0]=Some(1-carried.resonator_phases[0].unwrap());
    assert!(matches!(Word::continuing(&field,operands,&carried,&nothing,2),
        Err(crate::hnn::HnnError::Resonator{ring:0,..})));
    let unpumped=Constitution::initial(&field,super::learning::OPEN_BUDGET).unwrap();
    let bare=Operands::exact_at_cut(&field,&unpumped,&current).unwrap();
    let mut absent=EndChange::rest(&field,&bare);
    absent.resonator_phases[0]=Some(0);
    assert!(matches!(Word::continuing(&field,bare,&absent,&nothing,0),
        Err(crate::hnn::HnnError::Resonator{ring:0,..})));
}

#[test]
fn native_absent_state_and_supplied_phase_follow_the_opening_contract() {
    let field=chain().with_exact_word();
    let theta=resonant(&field,generic(&field,73));
    let current=Current::at_rest(&field);
    let operands=Operands::exact_at_cut(&field,&theta,&current).unwrap();
    let mut carried=EndChange::rest(&field,&operands);
    for (ring,r) in operands.resonators().iter().enumerate() {
        carried.resonator_phases[ring]=r.as_ref().map(|r|r.phase_at(1));
    }
    let expected=carried.resonator_phases[0].unwrap();
    carried.resonators[0]=None;
    let nothing:Vec<_>=carried.storage.iter().map(|v|vec![Rat::zero();v.len()]).collect();
    for phase in [None,Some(expected)] {
        carried.resonator_phases[0]=phase;
        let word=Word::continuing(&field,operands.clone(),&carried,&nothing,2).unwrap();
        let resonator=word.resonances()[0].as_ref().unwrap();
        assert!(resonator.state.iter().flatten().all(Zero::is_zero));
        assert!(resonator.open.is_zero());
        assert_eq!(word.change().unwrap().resonator_phases[0],Some(expected));
    }
    carried.resonator_phases[0]=Some(1-expected);
    assert!(matches!(Word::continuing(&field,operands.clone(),&carried,&nothing,2),
        Err(crate::hnn::HnnError::Resonator{ring:0,..})));
    carried.resonators[0]=Some([vec![Rat::zero();field.ring(0).width()],vec![Rat::zero();field.ring(0).width()]]);
    carried.resonator_phases[0]=None;
    assert!(matches!(Word::continuing(&field,operands,&carried,&nothing,2),
        Err(crate::hnn::HnnError::Resonator{ring:0,..})));
}

/// The opening energy uses the scheduled previous form, not the material's unpumped form or
/// the first newly executed phase. The native owner keeps the nonzero pump work of that change.
#[test]
fn native_opening_uses_the_scheduled_previous_phase() {
    use crate::hnn::ring::{PumpSchedule,ResonatorOperands};
    use crate::hnn::word::{ResonatorBalance,WordBalance};
    let field=chain().with_exact_word();
    let material=ResonatorMaterial::of_parametron(&cycle(4),&rat(1,8),None).unwrap();
    let theta=Constitution::initial(&field,super::learning::OPEN_BUDGET).unwrap()
        .with_ring_resonator(&field,0,material.clone()).unwrap();
    let current=Current::at_rest(&field);
    let mut operands=Operands::exact_at_cut(&field,&theta,&current).unwrap();
    let carrier=|a,b|Carrier::new(integer(a),integer(b)).unwrap();
    let schedule=PumpSchedule::modulated(
        &PumpDeclaration::new(rat(1,16),carrier(1,0),PumpStep::Quarter).unwrap(),
        &[carrier(0,1),carrier(-1,0),carrier(1,0)]).unwrap();
    let scheduled=ResonatorOperands::scheduled(0,&material,&schedule,field.ring(0).admittance(),field.step(),None).unwrap();
    *operands.resonators_mut().get_mut(0).unwrap()=Some(scheduled.clone());
    let mut carried=EndChange::rest(&field,&operands);
    let width=field.ring(0).width();
    let unit=|at:usize,value:Rat|(0..width).map(|j|if j==at{value.clone()}else{Rat::zero()}).collect::<Vec<_>>();
    let input=[unit(0,rat(1,2)),unit(2,rat(1,4))];
    carried.resonators[0]=Some(input.clone());
    carried.resonator_phases[0]=Some(scheduled.phase_at(1));
    let expected=scheduled.energy_at(scheduled.phase_at(1),&input[0],&input[1]).unwrap();
    let first_form=scheduled.energy_at(scheduled.phase_at(2),&input[0],&input[1]).unwrap();
    assert_ne!(expected,first_form);
    let nothing:Vec<_>=carried.storage.iter().map(|v|vec![Rat::zero();v.len()]).collect();
    let mut word=Word::continuing(&field,operands,&carried,&nothing,2).unwrap();
    assert_eq!(word.resonances()[0].as_ref().unwrap().open,expected);
    word.run(1).unwrap();
    let resonance=word.resonances()[0].as_ref().unwrap();
    assert_eq!(resonance.steps[0].before,expected);
    assert!(!resonance.steps[0].pump.is_zero());
    assert!(ResonatorBalance::of(0,resonance).closes());
    assert!(WordBalance::of(&word.release().unwrap()).closes());
}

/// **The lock rule locks every station the readings do not certify below the largest gap**: a
/// near tie within the enclosures locks together, a gap certified below stays open, and on exact
/// readings (reach equal to the certain gap) it is the largest gap with its ties.
#[test]
fn a_gap_the_readings_do_not_order_below_the_largest_locks_with_it() {
    use crate::hnn::prediction::uncertified_largest;
    // Station 4's certain gap 5/8 is the largest; station 2's reaches 3/4 ≥ 5/8 (a near tie inside
    // the cells); station 7's reach 1/2 is certified below.
    let gaps = vec![(2, 0, rat(1, 2)), (4, 1, rat(5, 8)), (7, 0, rat(1, 4))];
    let reaches = vec![rat(3, 4), rat(7, 8), rat(1, 2)];
    assert_eq!(uncertified_largest(&gaps, &reaches), vec![2, 4]);
    // A reach just below the largest certain gap is certified below: the leader locks alone.
    let reaches = vec![rat(5, 8) - rat(1, 1024), rat(7, 8), rat(1, 2)];
    assert_eq!(uncertified_largest(&gaps, &reaches), vec![4]);
    // Exact readings: the reach is the gap, and the rule is the largest gap with its ties.
    let gaps = vec![(0, 0, rat(1, 2)), (1, 0, rat(1, 3)), (3, 2, rat(1, 2))];
    let exact: Vec<Rat> = gaps.iter().map(|(_, _, gap)| gap.clone()).collect();
    assert_eq!(uncertified_largest(&gaps, &exact), vec![0, 3]);
    // No eligible station: nothing locks.
    assert!(uncertified_largest(&[], &[]).is_empty());
}

// -------------------------------------------------------------------------------------------
// the release reads the located pair on equal material (lane C, October 5)

/// A request of `n` cells over the four symbols of `pair_field(5)` (the termination `4` never
/// drawn), ingested from rest, with its cells.
fn symbols_request(field: &Field, seed: u64, n: usize) -> (Current, SourceMoment, Vec<usize>) {
    let mut draw = Draw::new(seed);
    let cells: Vec<usize> = (0..n).map(|_| draw.below(4)).collect();
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    let mut fed = 0;
    while fed < cells.len() {
        fed += moment.ingest(field, &mut current, &encoded(field, &cells[fed..])).unwrap().cells;
    }
    (current, moment, cells)
}

/// The order-2 deposit on `pair_field(5)`'s declared opening, at a declared distance.
fn deposited(field: &Field, offset: usize) -> Constitution {
    use crate::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    let opening = Constitution::initial(field, CAMPAIGN_ONE_BUDGET).unwrap();
    let prior = opening.source_port(0).unwrap().clone();
    let pair = crate::hnn::keys::LocatedPair {
        offset,
        ..super::executed::order_two_pair()
    };
    crate::hnn::executed::pair_deposit(field, &opening, &prior, 0, &pair).unwrap().0
}

/// [implemented-exact] **The closed pair contacts are read from the material**
/// (`prediction::closed_pairs`): the declared opening closes none; after the located pair's deposit
/// at distance `δ` the source port closes exactly `δ`, whatever `δ` the key carried (2 and 3 here),
/// so the release's distance is the deposit's, never a caller's; the field's declared port is the
/// opening's.
#[test]
fn the_closed_pair_contacts_are_the_deposits_distance() {
    use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, declared_source_port};
    use crate::hnn::prediction::closed_pairs;
    let field = super::executed::pair_field(5);
    let opening = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
    assert_eq!(
        declared_source_port(&field, 0).unwrap().as_ref(),
        opening.source_port(0)
    );
    assert!(closed_pairs(&field, &opening, 0).unwrap().is_empty());
    for offset in [2usize, 3] {
        assert_eq!(closed_pairs(&field, &deposited(&field, offset), 0).unwrap(), vec![offset]);
    }
}

/// [implemented-exact] **A candidate's pair storage is its datum and the crossings its closed
/// contact joins to it, at the contact's own weight, beside its column alone**
/// (`prediction::BankPlacement::pair_storage`): at station 0 the contact at `δ = 2` joins the
/// request's cell `τ − 1` (lag 1), so `z_pair = ν̂(2) (P^(λ−c_0) E e_x + P^(λ−c_0+2) E e_a)` and
/// `z_alone = ν̂(2) P^(λ−c_0) E e_x` exactly; the candidate that fits, `x = f(a)`, carries the
/// antecedent's prior image a second time,
/// `z_pair = ν̂(2) (P^(λ−c_0) B e_x + 2 P^(λ−c_0+2) B e_a + P^(λ−c_0+2) (E − B) e_a)`. Station 3 is
/// joined to no placed crossing until station 1 (or 5) is placed, and then to it.
#[test]
fn a_candidates_pair_storage_joins_its_antecedent_at_the_contacts_weight() {
    use crate::hnn::constitution::declared_source_port;
    use crate::hnn::moment::PopulationChart;
    let field = super::executed::pair_field(5);
    let theta = deposited(&field, 2);
    let prior = declared_source_port(&field, 0).unwrap().unwrap();
    let (current, moment, cells) = symbols_request(&field, 41, 8);
    let refinement = Refinement::declare(&field, 0, 2, 1, 6, 4).unwrap();
    let placement = BankPlacement::of(&field, &theta, &current, &moment, &refinement).unwrap();
    assert_eq!(placement.contacts(), &[2]);
    let ring = field.ring(0);
    let lift = current.lift()[0].clone();
    let phase = current.phase(&field, 0).unwrap();
    let column = |m: &ExactRatMatrix, c: usize| -> Vec<Rat> {
        (0..m.rows()).map(|r| m.get(r, c).unwrap().clone()).collect()
    };
    let port = theta.source_port(0).unwrap();
    let placed_at = |v: &[Rat], residue: u64| ring.rotate(v, &(&lift - BigInt::from(residue)));
    let nu = PopulationChart::of(&field).value(2);
    let scale = |v: Vec<Rat>| -> Vec<Rat> { v.iter().map(|x| x * &nu).collect() };
    let add = |a: &[Rat], b: &[Rat]| -> Vec<Rat> { a.iter().zip(b).map(|(x, y)| x + y).collect() };
    let antecedent = cells[cells.len() - 2];
    let (c0, ca) = ((phase + 1) % 16, (phase + 15) % 16);
    let open = vec![None; 6];
    for x in 0..5 {
        let (pair, alone) = placement.pair_storage(0, x, &open).unwrap();
        let own = placed_at(&column(port, x), c0);
        assert_eq!(alone, scale(own.clone()));
        assert_eq!(pair, scale(add(&own, &placed_at(&column(port, antecedent), ca))));
    }
    let fits = (antecedent + 1) % 4;
    let (pair, _) = placement.pair_storage(0, fits, &open).unwrap();
    let learned: Vec<Rat> = column(port, antecedent)
        .iter()
        .zip(column(&prior, antecedent))
        .map(|(e, b)| e - b)
        .collect();
    let doubled: Vec<Rat> = placed_at(&column(&prior, antecedent), ca).iter().map(|x| x + x).collect();
    let expected = add(
        &add(&placed_at(&column(&prior, fits), c0), &doubled),
        &placed_at(&learned, ca),
    );
    assert_eq!(pair, scale(expected));
    // Station 3: its residues c_3 ± 2 hold station 1 and station 5, neither placed.
    assert!(!placement.joins(3, &open));
    assert!(placement.pair_storage(3, 0, &open).is_none());
    let mut one = open.clone();
    one[1] = Some(2);
    assert!(placement.joins(3, &one));
    let (pair, _) = placement.pair_storage(3, 0, &one).unwrap();
    let own = placed_at(&column(port, 0), (phase + 4) % 16);
    assert_eq!(pair, scale(add(&own, &placed_at(&column(port, 2), (phase + 2) % 16))));
}

/// One closing ring of the harness's period `60 = 2²·3·5` (its lock every port, quarter-turn
/// placements), source and receiving ring, over `|A| = 5` (four symbols and the termination): the
/// order-2 field's receiving ring without its carry rings, which the release does not read.
fn sixty_field() -> Field {
    use crate::hnn::field::{CribDeclaration, FieldDeclaration, ReceiverDeclaration, RingDeclaration};
    let ring = RingDeclaration {
        period: 60,
        placements: (0..60).map(|node| FieldDeclaration::quarter_turn(node, 60)).collect(),
        ..super::support::ring(16, (0..60).collect())
    };
    Field::declare(
        FieldDeclaration {
            rings: vec![RingDeclaration {
                reflector: (0..60).map(|p| ((60 - p) % 60) as usize).collect(),
                ..ring
            }],
            contacts: Vec::new(),
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: 5,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 0,
                aperture: 3,
                tolerance: rat(1, 16),
                depth: 1,
                prior: crate::compression::landmark::context::StopPrior::half(),
                mass: 1,
                base: crate::compression::landmark::context::BaseMeasure::Even,
                receiving_prior: 0,
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

/// [implemented-exact; the consumer equation] **The release reads the located pair: the released
/// class at `t` is `f` of the class at `t − δ`** (`prediction::generate_by_bank` on a material
/// holding the order-2 contact closed; `ρ(F^K(I_h)) = T(request)`): on a ring of the harness's
/// period 60 with the order-2 pair deposited at `δ = 2`, each drawn request's six stations are
/// released whole at width zero, each released class the located map of its antecedent (the
/// request's last two cells, then the section's own locks), every lock certified on all four
/// members with every executed tick closed; the first refinement locks only among stations 0 and 1
/// (the only stations a closed contact joins to a placed crossing). The declared opening closes no
/// contact, so it reads the span's law (`the_bank_generates_by_its_certified_locks`). [measured, lane
/// C's record §5.4] On a ring of period 16 the bank's growths sit near one, and lane C's least member
/// did not separate the fit from the antecedent's copy there; the law is read here in the harness's
/// regime.
#[test]
fn the_release_reads_the_located_pair_and_its_consumer_holds() {
    use crate::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    let field = sixty_field();
    let theta = deposited(&field, 2);
    let bank = super::executed::declared_bank();
    let refinement = Refinement::declare(&field, 0, 2, 1, 6, 4).unwrap();
    for seed in [41u64, 42] {
        let (current, moment, cells) = symbols_request(&field, seed, 8);
        let generated =
            generate_by_bank(&field, &theta, &current, &moment, &refinement, &bank, 12).unwrap();
        assert_eq!(generated.contacts, vec![2]);
        assert!(generated.release.released(), "seed {seed}: {:?}", generated.release);
        assert!(generated.release.width.is_zero());
        let mut passage = cells.clone();
        passage.extend(&generated.release.classes);
        for t in 0..6 {
            let at = cells.len() + t;
            assert_eq!(passage[at], (passage[at - 2] + 1) % 4, "seed {seed}, station {t}");
        }
        assert!(generated.locks[0].iter().all(|&station| station < 2));
        let locked: usize = generated.locks.iter().map(Vec::len).sum();
        assert_eq!(generated.members, 4 * locked);
        assert_eq!(generated.certified, generated.members);
        assert_eq!(generated.ticks_closed, generated.ticks);
    }
    let opening = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
    assert!(crate::hnn::prediction::closed_pairs(&field, &opening, 0).unwrap().is_empty());
}

/// [implemented-exact; proved-derived, the joint gain's record §3] **The gain on equal material is
/// the joined bank's determinant over its members** (`prediction::gain`): the product of the
/// members' ratios, enclosed exactly (`[∏ L_pair/U_alone, ∏ U_pair/L_alone]`); joining two banks
/// multiplies their gains (the direct sum's `log det` is the sum, the loss law's additive chart);
/// a neutral member (its two storages turning alike) leaves the gain unchanged, where the least
/// member it would join is capped at one by it; refused, typed, on a reading alone whose lower end
/// is not positive and on two readings of different banks.
#[test]
fn the_pair_gain_is_the_joined_banks_determinant_and_a_neutral_member_does_not_move_it() {
    use crate::hnn::HnnError;
    use crate::hnn::prediction::gain;
    use crate::hnn::ring::{Growth, TurnReading};
    let growth = |lower: Rat, upper: Rat| Growth { lower, upper };
    let reading = |members: Vec<Growth>| TurnReading {
        joint: members
            .iter()
            .max_by(|a, b| a.upper.cmp(&b.upper))
            .cloned()
            .unwrap(),
        members,
    };
    let exact = |x: Rat| growth(x.clone(), x);
    // Two members, exact: Γ = (3/1)·(10/5) = 6.
    let pair = reading(vec![exact(integer(3)), exact(integer(10))]);
    let alone = reading(vec![exact(integer(1)), exact(integer(5))]);
    assert_eq!(gain(&pair, &alone).unwrap(), exact(integer(6)));
    // Enclosures: [1, 2] over [1/2, 1] is [1, 4]; with the exact member, [3, 12].
    let pair_wide = reading(vec![growth(integer(1), integer(2))]);
    let alone_wide = reading(vec![growth(rat(1, 2), integer(1))]);
    assert_eq!(gain(&pair_wide, &alone_wide).unwrap(), growth(integer(1), integer(4)));
    let joined = |a: &TurnReading, b: &TurnReading| {
        reading(a.members.iter().chain(&b.members).cloned().collect())
    };
    let (pair_joined, alone_joined) = (joined(&pair, &pair_wide), joined(&alone, &alone_wide));
    let product = gain(&pair_joined, &alone_joined).unwrap();
    assert_eq!(product, growth(integer(6), integer(24)));
    // A neutral member: its two storages read alike, so it moves nothing; the least member's ratio
    // over the same three members would be capped at one by it.
    let neutral = reading(vec![growth(rat(5, 16), rat(6, 16))]);
    let quiet = reading(vec![growth(rat(5, 16), rat(5, 16))]);
    let exact_neutral = reading(vec![exact(rat(5, 16))]);
    assert_eq!(
        gain(&joined(&pair, &exact_neutral), &joined(&alone, &exact_neutral)).unwrap(),
        exact(integer(6))
    );
    let widened = gain(&joined(&pair, &neutral), &joined(&alone, &quiet)).unwrap();
    assert_eq!(widened, growth(integer(6), integer(6) * rat(6, 5)));
    // Refusals: a reading alone at zero, and two banks of different membership.
    let silent = reading(vec![growth(Rat::zero(), rat(1, 16)), exact(integer(5))]);
    assert!(matches!(gain(&pair, &silent), Err(HnnError::NonpositiveDeclaration)));
    assert!(matches!(gain(&pair, &alone_wide), Err(HnnError::NonpositiveDeclaration)));
}

/// [implemented-exact; the consumer equation] **The release reads a located map that fixes its
/// antecedent** (`prediction::generate_by_bank`, the gain read by the joined bank): on the ring of
/// the harness's period 60 with the identity deposited at `δ = 2` (the alternation's key, every
/// column `(E − B) e_x = P^2 B e_x`), each drawn request's six stations are released whole at width
/// zero, each released class its antecedent's (`x_t = x_(t−2)`: the request's last two cells
/// continued), every lock certified on all four members. [measured, the joint gain's record §4]
/// Under lane C's least member this test fails (seed 41: station 0 is not its antecedent): on the
/// members where `P^2` half-turns the contact's line every candidate's two storages vanish in the
/// first-order chart, and the least member read what remained (the regressions' record §5, §8).
#[test]
fn the_release_reads_a_located_map_that_fixes_its_antecedent() {
    use crate::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    let field = sixty_field();
    let opening = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
    let prior = opening.source_port(0).unwrap().clone();
    let identity = crate::hnn::keys::LocatedPair {
        offset: 2,
        map: (0..4).map(|class| (class, class)).collect(),
        cycle: 1,
        turns: vec![0],
    };
    let theta = crate::hnn::executed::pair_deposit(&field, &opening, &prior, 0, &identity)
        .unwrap()
        .0;
    assert_eq!(crate::hnn::prediction::closed_pairs(&field, &theta, 0).unwrap(), vec![2]);
    let bank = super::executed::declared_bank();
    let refinement = Refinement::declare(&field, 0, 2, 1, 6, 4).unwrap();
    for seed in [41u64, 42] {
        let (current, moment, cells) = symbols_request(&field, seed, 8);
        let generated =
            generate_by_bank(&field, &theta, &current, &moment, &refinement, &bank, 12).unwrap();
        assert_eq!(generated.contacts, vec![2]);
        assert!(generated.release.released(), "seed {seed}: {:?}", generated.release);
        assert!(generated.release.width.is_zero());
        let mut passage = cells.clone();
        passage.extend(&generated.release.classes);
        for t in 0..6 {
            let at = cells.len() + t;
            assert_eq!(passage[at], passage[at - 2], "seed {seed}, station {t}");
        }
        let locked: usize = generated.locks.iter().map(Vec::len).sum();
        assert_eq!(generated.members, 4 * locked);
        assert_eq!(generated.certified, generated.members);
        assert_eq!(generated.ticks_closed, generated.ticks);
    }
}
