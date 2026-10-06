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

// -------------------------------------------------------------------------------------------
// the physical repair (lane C, October 5): the damaged section through the field's own motion

mod physical_repair {
    use super::super::support::{contact, ring};
    use crate::compression::landmark::context::{BaseMeasure, StopPrior};
    use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution};
    use crate::hnn::encoding::Encoded;
    use crate::hnn::field::{
        ConstitutionRead, CribDeclaration, Current, Field, FieldDeclaration, ReceiverDeclaration,
    };
    use crate::hnn::keys::{PairLocation, station_pairs};
    use crate::hnn::moment::SourceMoment;
    use crate::hnn::prediction::{
        DamagedSection, PhysicalRepair, RepairedCell, Unresolved, repair_by_field,
    };
    use crate::hnn::receiving::ReceivingPhases;
    use crate::hnn::word::{Absorption, WordOpening};
    use crate::holarchy::terrain::{CyclicLaw, KnownTruth};
    use crate::ratio::linear::ExactRatMatrix;
    use crate::ratio::{Rat, integer, rat};
    use num_traits::Zero;

    /// The section's declared receiver: ring 0 read at `aperture` crossings from its first.
    fn section(aperture: usize) -> ReceiverDeclaration {
        ReceiverDeclaration {
            ring: 0,
            aperture,
            tolerance: rat(1, 16),
            depth: 1,
            prior: StopPrior::half(),
            mass: 1,
            base: BaseMeasure::Even,
            receiving_prior: 0,
        }
    }

    /// The source and receiving ring of period 8 (its lock every port, so it steps once a cell),
    /// joined at three nodes to a ring of period 3; four classes, no pair offset.
    fn field() -> Field {
        field_with_lock((0..8).collect())
    }

    fn field_with_lock(lock: Vec<u64>) -> Field {
        field_with_lock_and_offsets(lock, Vec::new())
    }

    fn field_with_lock_and_offsets(lock: Vec<u64>, offsets: Vec<usize>) -> Field {
        Field::declare(
            FieldDeclaration {
                rings: vec![ring(8, lock), ring(3, Vec::new())],
                contacts: vec![contact(0, 1, 3, 0)],
                loops: Vec::new(),
                sources: vec![0],
                offsets,
                alphabet: 4,
                step: integer(1),
                exponent_grain: 1,
                receivers: vec![section(1)],
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

    /// The order-2 terrain's passages of 8 cells (an opening of 2), through its declared identity.
    fn passages(field: &Field, seed: u64, count: usize) -> Vec<Encoded> {
        let truth =
            KnownTruth::cyclic(CyclicLaw::OrderTwo { opening: 2 }, 4, seed, count, 8).unwrap();
        Encoded::identity(&truth, field).unwrap()
    }

    /// The opening and the material with the pair located on seen passages deposited (lanes B/C).
    fn materials(field: &Field) -> (Constitution, Constitution) {
        let opening = Constitution::initial(field, CAMPAIGN_ONE_BUDGET).unwrap();
        let mut location = PairLocation::open(field, 0);
        for passage in passages(field, 2_026_100_971, 32) {
            for observation in station_pairs(field, 0, &passage, 2).unwrap() {
                location.observe(&observation);
            }
        }
        let located = location.survivors().located().expect("the seen pair is located");
        assert_eq!(located.offset, 2);
        let prior = opening.source_port(0).unwrap().clone();
        let (learned, deposit) =
            crate::hnn::executed::pair_deposit(field, &opening, &prior, 0, &located).unwrap();
        assert!(deposit.certificate.holds());
        (opening, learned)
    }

    fn repaired(
        field: &Field,
        theta: &Constitution,
        section: &DamagedSection,
        phases: &ReceivingPhases,
    ) -> PhysicalRepair {
        repair_by_field(
            field,
            theta,
            &Current::at_rest(field),
            section,
            &WordOpening::Rest,
            phases,
        )
        .unwrap()
    }

    #[test]
    fn the_damaged_section_runs_through_the_field_and_every_erasure_is_held_unresolved() {
        let field = field();
        let (opening, learned) = materials(&field);
        let current = Current::at_rest(&field);
        let phases = ReceivingPhases::declare(&field, &learned, &current, &section(8)).unwrap();
        // The receiver's declaration reads no source port: the deposit leaves it unchanged.
        assert_eq!(
            phases,
            ReceivingPhases::declare(&field, &opening, &current, &section(8)).unwrap()
        );
        let truth = passages(&field, 2_026_100_972, 1).remove(0);
        let erased = [2, 5, 7];
        let damaged = DamagedSection::damage(&truth, &erased).unwrap();
        assert_eq!(damaged.erased(), erased);
        let repair = repaired(&field, &learned, &damaged, &phases);
        // One imposition from rest, its work closed; every executed tick and the word close.
        assert!(repair.opening.closes());
        assert_eq!(repair.opening.before, Rat::zero());
        assert!(repair.opening.imposed > Rat::zero());
        assert_eq!(repair.balances.len(), 7);
        assert!(repair.balances.iter().all(|balance| balance.closes()));
        assert!(repair.word.closes());
        // The clock: station j is read at crossing j, the refinement's tick j; the carried end
        // stands at the last.
        assert_eq!(repair.carry.ticks, 7);
        assert_eq!(repair.reads.len(), 8);
        for (j, read) in repair.reads.iter().enumerate() {
            assert_eq!((read.station, read.crossing, read.tick), (j, j, j));
        }
        // The decoder is the opening's zero map: every class leads every read, a reading only.
        for read in &repair.reads {
            assert!(read.read.logits.iter().all(Zero::is_zero));
            assert_eq!(read.leaders(), vec![0, 1, 2, 3]);
        }
        let classes: Vec<usize> = truth.classes_read().collect();
        for (t, cell) in repair.cells.iter().enumerate() {
            if erased.contains(&t) {
                assert_eq!(
                    *cell,
                    RepairedCell::Held {
                        fibre: vec![0, 1, 2, 3],
                        unresolved: Unresolved::PluralDomain,
                    }
                );
            } else {
                assert_eq!(*cell, RepairedCell::Intact(classes[t]));
            }
        }
    }

    #[test]
    fn the_section_carries_no_erased_class_so_the_repair_cannot_read_one() {
        let field = field();
        let (_, learned) = materials(&field);
        let current = Current::at_rest(&field);
        let phases = ReceivingPhases::declare(&field, &learned, &current, &section(8)).unwrap();
        let erased = [2, 5, 7];
        // Two passages equal on the intact cells and different at every erasure.
        let first = [0, 1, 1, 2, 2, 3, 3, 0];
        let second = [0, 1, 3, 2, 2, 0, 3, 2];
        let sections: Vec<DamagedSection> = [first, second]
            .iter()
            .map(|word| {
                DamagedSection::damage(&crate::hnn::tests::support::encoded(&field, word), &erased)
                    .unwrap()
            })
            .collect();
        assert_eq!(sections[0], sections[1]);
        assert_eq!(
            repaired(&field, &learned, &sections[0], &phases),
            repaired(&field, &learned, &sections[1], &phases)
        );
        // Runs that overlap or leave the section are refused.
        let run = crate::hnn::tests::support::encoded(&field, &[0, 1]);
        assert!(DamagedSection::of_runs(8, &run, vec![(0, run.clone()), (1, run.clone())]).is_err());
        assert!(DamagedSection::of_runs(8, &run, vec![(7, run.clone())]).is_err());
        assert!(DamagedSection::of_runs(usize::MAX, &run, vec![(usize::MAX, run.clone())]).is_err());
    }

    #[test]
    fn a_point_leader_does_not_replace_a_plural_coupled_domain() {
        let field = field();
        let (_, learned) = materials(&field);
        let current = Current::at_rest(&field);
        let phases = ReceivingPhases::declare(&field, &learned, &current, &section(8)).unwrap();
        // A declared decoder that reads class 0 from the ring's first node and class 1 against it.
        let width = field.ring(0).width();
        let mut rows = vec![vec![Rat::zero(); width]; 8];
        rows[0][0] = integer(1 << 20);
        rows[2][0] = -integer(1 << 20);
        let decoder = ExactRatMatrix::shaped(8, width, rows).unwrap();
        let theta = learned.with_ports(0, None, None, Some(decoder)).unwrap();
        let truth = passages(&field, 2_026_100_972, 1).remove(0);
        let damaged = DamagedSection::damage(&truth, &[2, 5, 7]).unwrap();
        let repair = repaired(&field, &theta, &damaged, &phases);
        let single = repair
            .reads
            .iter()
            .filter(|read| read.leaders().len() == 1)
            .count();
        assert!(single > 0, "the declared decoder leads one class at some station");
        for t in [2, 5, 7] {
            assert!(matches!(
                repair.cells[t],
                RepairedCell::Held {
                    unresolved: Unresolved::PluralDomain,
                    ..
                }
            ));
        }
        assert!(repair.cells.iter().all(|cell| !matches!(cell, RepairedCell::Released(_))));
    }

    #[test]
    fn a_station_no_declared_crossing_reads_is_held_unread() {
        let field = field();
        let (_, learned) = materials(&field);
        let current = Current::at_rest(&field);
        let phases = ReceivingPhases::declare(&field, &learned, &current, &section(4)).unwrap();
        let truth = passages(&field, 2_026_100_972, 1).remove(0);
        let damaged = DamagedSection::damage(&truth, &[2, 5, 7]).unwrap();
        let repair = repaired(&field, &learned, &damaged, &phases);
        assert_eq!(repair.reads.len(), 4);
        assert_eq!(repair.carry.ticks, 3);
        let unresolved = |t: usize| match &repair.cells[t] {
            RepairedCell::Held { unresolved, .. } => Some(*unresolved),
            _ => None,
        };
        assert_eq!(unresolved(2), Some(Unresolved::PluralDomain));
        assert_eq!(unresolved(5), Some(Unresolved::Unread));
        assert_eq!(unresolved(7), Some(Unresolved::Unread));
    }

    /// The existing located partial-span control (moment.rs): its actual nonunit conduct and
    /// producing decoder are founded on the observed stepped terrain, not forged chart metadata.
    fn located_passage() -> (Field, Encoded) {
        use crate::compression::keys::transport::{CarryHelix, SteppedTerrain, TransportLocation};
        use crate::hnn::encoding::{Encoding, PassageChart};
        use crate::hnn::tests::support::Draw;
        let mut receiver = section(1);
        receiver.ring = 2;
        let field = Field::declare(FieldDeclaration {
            rings: [2, 3, 5].into_iter().map(|period| ring(period, vec![0])).collect(),
            contacts: vec![contact(0, 1, 2, 0), contact(1, 2, 3, 0)],
            loops: Vec::new(),
            sources: vec![2],
            offsets: vec![1, 3],
            alphabet: 5,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver],
            crib: CribDeclaration { window: 16, offset: 1 },
            population: 1 << 16,
            lattice: Default::default(),
        }.by_lattice_rule()).unwrap();
        let helix = CarryHelix::new(vec![2, 3, 5]).unwrap();
        let mut draw = Draw::new(2_026_100_995);
        let advances = (0..5).map(|_| 5 * (1 + draw.below(5)) as u64).collect();
        let mut left: Vec<usize> = (0..5).collect();
        let labels = (0..5).map(|_| left.remove(draw.below(left.len()))).collect();
        let terrain = SteppedTerrain::new(helix.clone(), advances, labels).unwrap();
        let passages: Vec<_> = (0..helix.period()).map(|key| terrain.passage(key, 60)).collect();
        let location = TransportLocation::locate(helix, 5, &passages).unwrap();
        let chart = PassageChart::located(&location, &passages[..1]).unwrap();
        let encoding = Encoding::found(&chart).unwrap();
        let encoded = Encoded::through(&encoding, &chart, &field, &passages[..1]).unwrap().remove(0);
        (field, encoded)
    }

    #[test]
    fn equal_class_counts_do_not_join_different_producing_charts() {
        let (field, located) = located_passage();
        let identity = crate::hnn::tests::support::encoded(&field, &[0, 1]);
        assert_eq!(identity.classes(), located.classes());
        let refusal = DamagedSection::of_runs(8, &identity, vec![(0, identity.clone()), (3, located.part(0..2).unwrap())]);
        assert!(matches!(refusal, Err(crate::hnn::HnnError::Unadmitted {
            reason: "intact runs do not share the section's complete producing chart",
        })));
    }

    #[test]
    fn total_erasure_preserves_the_producing_chart_and_refuses_located_conduct_before_opening() {
        let (field, located) = located_passage();
        let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        let phases = ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
        for erased in [vec![2, 5], (0..located.len()).collect()] {
            let damaged = DamagedSection::damage(&located, &erased).unwrap();
            assert!(damaged.chart().is_empty());
            assert_eq!(damaged.chart(), &located.part(0..0).unwrap());
            let before = theta.clone();
            let refusal = repair_by_field(&field, &theta, &current, &damaged, &WordOpening::Rest, &phases);
            assert!(matches!(refusal, Err(crate::hnn::HnnError::Unadmitted {
                reason: "the located conduct has no certified sparse station-clock chart",
            })));
            assert_eq!(theta, before);
        }
    }

    #[test]
    fn identity_conduct_must_certify_the_station_clock_even_at_erased_stations() {
        let field = field_with_lock(vec![0, 1, 2]); // Class 3 does not fit.
        let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        let phases = ReceivingPhases::declare(&field, &theta, &current, &section(1)).unwrap();
        let encoded = crate::hnn::tests::support::encoded(&field, &[0, 1]);
        let damaged = DamagedSection::damage(&encoded, &[1]).unwrap();
        assert!(matches!(repair_by_field(&field, &theta, &current, &damaged, &WordOpening::Rest, &phases),
            Err(crate::hnn::HnnError::Unadmitted {
                reason: "the identity conduct does not certify one source tick per declared station",
            })));
    }

    #[test]
    fn the_producing_decoder_and_both_physical_maps_are_joined_before_opening() {
        let field = field();
        let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        let phases = ReceivingPhases::declare(&field, &theta, &current, &section(1)).unwrap();
        let smaller = Encoded::identity(&KnownTruth::declared(3, vec![vec![0, 1]]), &field).unwrap().remove(0);
        let damaged = DamagedSection::damage(&smaller, &[1]).unwrap();
        assert!(matches!(repair_by_field(&field, &theta, &current, &damaged, &WordOpening::Rest, &phases),
            Err(crate::hnn::HnnError::Unadmitted {
                reason: "the physical source and receiver do not share the producing identity decoder's classes",
            })));
        let encoded = crate::hnn::tests::support::encoded(&field, &[0, 1]);
        let damaged = DamagedSection::damage(&encoded, &[1]).unwrap();
        let width = field.ring(0).width();
        for (source, receiving, reason) in [
            (Some(ExactRatMatrix::zero(width, 3).unwrap()), None,
                "the physical source map does not consume the producing chart's classes"),
            (None, Some(ExactRatMatrix::zero(6, width).unwrap()),
                "the physical receiving map does not return the producing chart's complex classes"),
        ] {
            let incompatible = theta.clone().with_ports(0, None, source, receiving).unwrap();
            assert!(matches!(repair_by_field(&field, &incompatible, &current, &damaged, &WordOpening::Rest, &phases),
                Err(crate::hnn::HnnError::Unadmitted { reason: found }) if found == reason));
        }
    }

    #[test]
    fn the_supported_physical_passage_continues_on_its_retained_interior_and_clock() {
        let field = field();
        let (_, learned) = materials(&field);
        let current = Current::at_rest(&field);
        let phases = ReceivingPhases::declare(&field, &learned, &current, &section(8)).unwrap();
        let truth = passages(&field, 2_026_100_972, 1).remove(0);
        let damaged = DamagedSection::damage(&truth, &[2, 5, 7]).unwrap();
        let first = repaired(&field, &learned, &damaged, &phases);
        let continued = repair_by_field(&field, &learned, &current, &damaged,
            &WordOpening::Received { carry: first.carry.clone(), absorption: Absorption::Nothing }, &phases).unwrap();
        assert!(continued.opening.before > Rat::zero(), "the carried interior is physical motion");
        assert!(continued.opening.closes());
        assert!(continued.balances.iter().all(|balance| balance.closes()));
        assert!(continued.word.closes());
        assert_eq!(continued.carry.ticks, first.carry.ticks + 7);
        for (j, read) in continued.reads.iter().enumerate() {
            assert_eq!(read.tick, first.carry.ticks + j);
        }
        assert_ne!(continued.carry.change, first.carry.change);
        assert_eq!(continued.cells, first.cells); // R=0 remains plural across either admitted tube.
    }

    #[test]
    fn physical_teaching_changes_r_and_the_later_carried_receiving_read() {
        use crate::hnn::prediction::predict_by_field;
        let field = field();
        let (_, learned) = materials(&field);
        let current = Current::at_rest(&field);
        let phases = ReceivingPhases::declare(&field, &learned, &current, &section(8)).unwrap();
        let observed = passages(&field, 2_026_100_972, 1).remove(0);
        let damaged = DamagedSection::damage(&observed, &[2, 5, 7]).unwrap();
        // No observation is an input to the blind physical prediction.
        let prediction = predict_by_field(
            &field,
            &learned,
            &current,
            &damaged,
            &WordOpening::Rest,
            &phases,
        )
        .unwrap();
        let blind = prediction.prediction().clone();
        assert!(
            blind
                .reads
                .iter()
                .all(|station| station.read.logits.iter().all(Zero::is_zero))
        );
        let compared = [false, false, true, false, false, true, false, true];
        // Teaching arrives only now, at the declared previously erased stations.
        let teaching = prediction.observe(&learned, &observed, &compared).unwrap();
        assert_eq!(teaching.prediction, blind);
        assert_eq!(teaching.constitution.commit(), learned.commit() + 1);
        assert!(teaching.publication.stepped > 0);
        assert_ne!(
            teaching.constitution.receiving_map(0),
            learned.receiving_map(0)
        );
        // R=0 had no native pullback before teaching: only the actual receiving relation changes.
        assert_eq!(teaching.constitution.source_port(0), learned.source_port(0));
        let later_word = passages(&field, 2_026_100_973, 1).remove(0);
        let later = DamagedSection::damage(&later_word, &[2, 5, 7]).unwrap();
        let opening = WordOpening::Received {
            carry: teaching.prediction.carry.clone(),
            absorption: Absorption::Nothing,
        };
        let before = repair_by_field(&field, &learned, &current, &later, &opening, &phases).unwrap();
        let after = repair_by_field(
            &field,
            &teaching.constitution,
            &current,
            &later,
            &opening,
            &phases,
        )
        .unwrap();
        assert_eq!(after.carry.change, before.carry.change);
        assert_ne!(
            after.reads, before.reads,
            "the reached R deposit changes the actual native read"
        );
        assert!(
            after
                .reads
                .iter()
                .any(|station| station.read.logits.iter().any(|x| !x.is_zero()))
        );
        assert!(after.cells.iter().enumerate().filter(|(j, _)| [2, 5, 7].contains(j))
            .all(|(_, cell)| matches!(cell, RepairedCell::Held { .. })));
        assert!(after.opening.closes() && after.word.closes());
        assert!(after.balances.iter().all(|balance| balance.closes()));
        // An exterior test perturbation changes one intact source, under the same learned R,
        // carry and clocks. It supplies no desired output and changes nothing in the learner.
        let mut changed: Vec<_> = later_word.classes_read().collect();
        changed[0] = (changed[0] + 1) % 4;
        let changed = crate::hnn::tests::support::encoded(&field, &changed);
        let changed = DamagedSection::damage(&changed, &[2, 5, 7]).unwrap();
        let changed = repair_by_field(
            &field,
            &teaching.constitution,
            &current,
            &changed,
            &opening,
            &phases,
        )
        .unwrap();
        assert_ne!(changed.carry.change, after.carry.change);
        assert_ne!(
            changed.reads, after.reads,
            "the learned physical read depends on the actual intact source"
        );
        println!(
            "physical teaching: certified receiving publication at commit {}; blind output {:?}; subsequent carried output {:?}",
            teaching.constitution.commit(),
            teaching.prediction.cells,
            after.cells
        );
    }

    #[test]
    fn physical_teaching_refuses_a_stale_material_or_foreign_chart_and_preserves_the_carry() {
        use crate::hnn::prediction::predict_by_field;
        let field = field();
        let (_, learned) = materials(&field);
        let current = Current::at_rest(&field);
        let phases = ReceivingPhases::declare(&field, &learned, &current, &section(8)).unwrap();
        let observed = passages(&field, 2_026_100_972, 1).remove(0);
        let damaged = DamagedSection::damage(&observed, &[2, 5, 7]).unwrap();
        let compared = [false, false, true, false, false, true, false, true];
        let foreign = Encoded::identity(&KnownTruth::declared(3, vec![vec![0; 8]]), &field)
            .unwrap()
            .remove(0);
        let prediction = predict_by_field(
            &field,
            &learned,
            &current,
            &damaged,
            &WordOpening::Rest,
            &phases,
        )
        .unwrap();
        let blind = prediction.prediction().clone();
        let refusal = prediction
            .observe(&learned, &foreign, &compared)
            .unwrap_err();
        assert_eq!(refusal.prediction, blind);
        assert!(matches!(
            refusal.error,
            crate::hnn::HnnError::Unadmitted {
                reason: "the observation does not share the physical source's complete producing chart",
            }
        ));
        let pending = predict_by_field(
            &field,
            &learned,
            &current,
            &damaged,
            &WordOpening::Rest,
            &phases,
        )
        .unwrap();
        let blind = pending.prediction().clone();
        let teaching = predict_by_field(
            &field,
            &learned,
            &current,
            &damaged,
            &WordOpening::Rest,
            &phases,
        )
        .unwrap()
        .observe(&learned, &observed, &compared)
        .unwrap();
        // False comparison regions carry no teaching covector or normal statistic. Their exterior
        // labels cannot alter the selected regions' target clock or the deposited constitution.
        let mut alternative: Vec<_> = observed.classes_read().collect();
        alternative[0] = (alternative[0] + 1) % 4;
        let alternative = crate::hnn::tests::support::encoded(&field, &alternative);
        let equivalent = predict_by_field(
            &field,
            &learned,
            &current,
            &damaged,
            &WordOpening::Rest,
            &phases,
        )
        .unwrap()
        .observe(&learned, &alternative, &compared)
        .unwrap();
        assert_eq!(equivalent.constitution, teaching.constitution);
        let refusal = pending
            .observe(&teaching.constitution, &observed, &compared)
            .unwrap_err();
        assert_eq!(refusal.prediction, blind);
        assert!(
            matches!(refusal.error, crate::hnn::HnnError::StaleDeposit { staged, published }
                if staged == learned.commit() && published == teaching.constitution.commit())
        );
    }

    #[test]
    fn the_actual_leaky_source_return_changes_e_before_the_next_target_free_carried_word() {
        use crate::hnn::constitution::Locus;
        use crate::hnn::moment::SourceMoment;
        use crate::hnn::prediction::predict_by_field;
        let field = field();
        let current = Current::at_rest(&field);
        // The existing constitutive law chooses rho from the source period and declared grains.
        // It is not selected from a teacher, task score or the later source.
        let initial = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
            .unwrap()
            .founded_transport(&field, 0)
            .unwrap();
        let modulus = initial.transport(0);
        assert!(modulus > Rat::zero() && modulus < integer(1));
        let period = usize::try_from(field.ring(0).period()).unwrap();
        let length = period + 1;
        let mut truth = vec![0; length];
        truth[1] = 2;
        truth[period] = 1;
        let observed = crate::hnn::tests::support::encoded(&field, &truth);
        let erased: Vec<_> = (1..period).collect();
        let damaged = DamagedSection::damage(&observed, &erased).unwrap();
        let mut swapped_truth = truth.clone();
        swapped_truth.swap(0, period);
        let swapped = crate::hnn::tests::support::encoded(&field, &swapped_truth);
        let swapped = DamagedSection::damage(&swapped, &erased).unwrap();
        // Preserve the original counterexample: the unit clock/transport loses this placement.
        let unit = SourceMoment::open(&field, &current);
        assert_eq!(
            unit.continued(&field, &current, 0, &damaged.placed())
                .unwrap(),
            unit.continued(&field, &current, 0, &swapped.placed())
                .unwrap()
        );
        // The existing Leaky owner carries their different ages, at its actual rounded grain.
        let leaky = SourceMoment::open_with(&field, &current, &initial).unwrap();
        let source = leaky
            .continued(&field, &current, 0, &damaged.placed())
            .unwrap();
        let other_source = leaky
            .continued(&field, &current, 0, &swapped.placed())
            .unwrap();
        assert_ne!(source, other_source);
        assert_ne!(
            source.open_storage(&field, &initial, &current).unwrap(),
            other_source
                .open_storage(&field, &initial, &current)
                .unwrap()
        );
        let phases =
            ReceivingPhases::declare(&field, &initial, &current, &section(length)).unwrap();
        let mut compared = vec![false; length];
        compared[1] = true;
        // R is learned by the existing post-blind observed comparison, never authored.
        let receiving = predict_by_field(
            &field,
            &initial,
            &current,
            &damaged,
            &WordOpening::Rest,
            &phases,
        )
        .unwrap()
        .observe(&initial, &observed, &compared)
        .unwrap();
        assert!(receiving.source_certificate.is_none());
        assert_eq!(receiving.constitution.source_law(0), initial.source_law(0));
        let producing = &receiving.constitution;
        let opening = WordOpening::Received {
            carry: receiving.prediction.carry.clone(),
            absorption: Absorption::Nothing,
        };
        let pending =
            predict_by_field(&field, producing, &current, &damaged, &opening, &phases).unwrap();
        let blind = pending.prediction().clone();
        // Source-swap sensitivity already belongs to the leaky encoding before E teaching.
        let untaught_swap =
            repair_by_field(&field, producing, &current, &swapped, &opening, &phases).unwrap();
        assert_ne!(blind.carry.change, untaught_swap.carry.change);
        assert_ne!(blind.reads, untaught_swap.reads);
        assert!(untaught_swap.opening.closes() && untaught_swap.word.closes());
        assert!(
            untaught_swap
                .balances
                .iter()
                .all(|balance| balance.closes())
        );
        let taught = pending
            .observe_source_ports(producing, &observed, &compared)
            .unwrap();
        assert_eq!(taught.prediction, blind);
        assert_eq!(taught.constitution.commit(), producing.commit() + 1);
        assert_ne!(taught.constitution.source_port(0), producing.source_port(0));
        assert_eq!(
            taught.constitution.receiving_law(0),
            producing.receiving_law(0)
        );
        assert_eq!(taught.constitution.transport(0), modulus);
        assert_eq!(
            taught.constitution.clock(Locus::SourcePort(0)),
            producing.clock(Locus::SourcePort(0)) + 1
        );
        for ring in 0..field.rings().len() {
            assert_eq!(
                taught.constitution.contrast_law(ring),
                producing.contrast_law(ring)
            );
            assert_eq!(
                taught.constitution.passive_factor(ring),
                producing.passive_factor(ring)
            );
            assert_eq!(
                taught.constitution.clock(Locus::Element(ring)),
                producing.clock(Locus::Element(ring))
            );
        }
        for contact in 0..field.contacts().len() {
            assert_eq!(
                taught.constitution.contact_storage(contact),
                producing.contact_storage(contact)
            );
            assert_eq!(
                taught.constitution.contact_stiffness(contact),
                producing.contact_stiffness(contact)
            );
            assert_eq!(
                taught.constitution.contact_dissipation(contact),
                producing.contact_dissipation(contact)
            );
            assert_eq!(
                taught.constitution.clock(Locus::Channel(contact)),
                producing.clock(Locus::Channel(contact))
            );
        }
        // An ignored teacher label changes neither the clock nor the actual E normal statistic.
        let mut ignored = truth.clone();
        ignored[0] = 3;
        let ignored = crate::hnn::tests::support::encoded(&field, &ignored);
        let equivalent = predict_by_field(&field, producing, &current, &damaged, &opening, &phases)
            .unwrap()
            .observe_source_ports(producing, &ignored, &compared)
            .unwrap();
        assert_eq!(equivalent.constitution, taught.constitution);
        // Re-read the declared comparison on a new contemporary Word with the same source,
        // clock and original opening. This is a training-side measurement, not an untouched test.
        let matched = repair_by_field(
            &field,
            &taught.constitution,
            &current,
            &damaged,
            &opening,
            &phases,
        )
        .unwrap();
        let matched_reads: Vec<_> = matched
            .reads
            .iter()
            .map(|station| station.read.clone())
            .collect();
        let matched_ratio = crate::hnn::ratio::HolonRatio::compare_partition(
            crate::hnn::ratio::Faces::of_reads(&matched_reads, phases.grain()).unwrap(),
            &observed.classes_read().collect::<Vec<_>>(),
            &crate::hnn::ratio::target_phases(&field, current.lift(), phases.ring(), &observed)
                .unwrap(),
            &compared,
        )
        .unwrap();
        assert_eq!(taught.ratio.stations(), matched_ratio.stations());
        assert!(matched.opening.closes() && matched.word.closes());
        assert!(matched.balances.iter().all(|balance| balance.closes()));
        // The consumer equation is checked on this physical Word, including its actual carried
        // map change: <g, logits(E')-logits(E)> = <d_E log ratio, E'-E>.
        use crate::ratio::linear::vector::dot;
        let delta_e = taught
            .constitution
            .source_port(0)
            .unwrap()
            .subtract(producing.source_port(0).unwrap())
            .unwrap();
        let gradient = taught.ratio.covector().unwrap();
        let delta_logits: Vec<Vec<Rat>> = matched
            .reads
            .iter()
            .zip(&blind.reads)
            .map(|(after, before)| {
                after
                    .read
                    .logits
                    .iter()
                    .zip(&before.read.logits)
                    .map(|(a, b)| a - b)
                    .collect()
            })
            .collect();
        let at_receiver: Rat = gradient
            .logits()
            .iter()
            .zip(&delta_logits)
            .map(|(g, delta)| dot(g, delta))
            .sum();
        let source_gradient = taught.pullback.rings[0].source.as_ref().unwrap();
        let at_source = dot(source_gradient.entries(), delta_e.entries());
        assert_eq!(
            at_receiver, at_source,
            "same executed physical Word/source adjoint"
        );
        let source_step = taught
            .publication
            .steps
            .iter()
            .find(|(at, read)| {
                *at == Locus::SourcePort(0) && read.family == crate::hnn::constitution::Family::Map
            })
            .unwrap();
        let logit_move: Rat = delta_logits
            .iter()
            .zip(&compared)
            .filter(|(_, crossed)| **crossed)
            .map(|(delta, _)| dot(delta, delta))
            .sum();
        let actual_source_moves: Rat = (0..field.ring(0).placements().len())
            .map(|phase| {
                let feature = source
                    .normalized_counts(&field, 0, phase, &modulus)
                    .unwrap();
                let moved = delta_e.apply(&feature).unwrap();
                dot(&moved, &moved)
            })
            .sum();
        assert!(
            logit_move <= &source_step.1.gain * &actual_source_moves,
            "the declared source gain must bound the actual physical Word"
        );
        let eta = &source_step.1.step.step;
        let ideal_move = eta * eta * &source_step.1.gain * &source_step.1.moves;
        let applied = taught.source_certificate.as_ref().unwrap();
        assert_eq!(applied.sources.len(), 1);
        let applied_source = &applied.sources[0];
        assert_eq!(applied_source.ring, 0);
        assert_eq!(applied_source.moves, actual_source_moves);
        assert_eq!(applied_source.alignment, -&at_source);
        assert_eq!(applied_source.gain, source_step.1.gain);
        assert!(
            &applied_source.bound * &applied_source.bound
                >= &applied_source.gain * &applied_source.moves
        );
        assert!(applied.joint.holds());
        assert_eq!(applied.joint.decrease, -&at_receiver);
        assert!(rat(1, 2) * &logit_move <= applied.joint.curvature);
        // The carried update completes eta*D with the actual old/new map remainders and release.
        // They are not the solved chart's separate prox residual and are not assumed to vanish.
        let source_law = taught.constitution.source_law(0).unwrap();
        let unit_e = source_gradient
            .scaled(&integer(-1))
            .multiply(&source_law.solved())
            .unwrap();
        let ideal_delta = unit_e.scaled(eta);
        let previous_remainder = producing.source_law(0).unwrap().map_remainder();
        let remainder = source_law.map_remainder();
        for (index, (actual, ideal)) in delta_e
            .entries()
            .iter()
            .zip(ideal_delta.entries())
            .enumerate()
        {
            let released: Rat = taught
                .publication
                .released
                .iter()
                .filter(|(at, carrier, entry, _)| {
                    *at == Locus::SourcePort(0)
                        && *carrier == crate::hnn::constitution::Carrier::Map
                        && *entry == index
                })
                .map(|(_, _, _, value)| value.clone())
                .sum();
            assert_eq!(
                actual + &remainder.entries()[index] - &previous_remainder.entries()[index]
                    + released,
                *ideal
            );
        }
        println!(
            "physical E consumer: adjoint pairing {}; actual logit move squared {}; actual source moves {}; gain {}; ideal normal-ray eta^2*kappa^2*b {}; actual carried joint certificate {:?}; source map carry {:?}; source map releases {:?}",
            at_receiver,
            logit_move,
            actual_source_moves,
            source_step.1.gain,
            ideal_move,
            applied.joint,
            taught.constitution.source_law(0).unwrap().map_remainder(),
            taught
                .publication
                .released
                .iter()
                .filter(|(at, carrier, _, _)| *at == Locus::SourcePort(0)
                    && *carrier == crate::hnn::constitution::Carrier::Map)
                .collect::<Vec<_>>()
        );
        println!(
            "matched observed station comparison: before {:?}; after {:?}; imposed source work {} -> {}; quantized strict descent is not asserted",
            taught.ratio.phases(),
            matched_ratio.phases(),
            taught.prediction.opening.imposed,
            matched.opening.imposed,
        );
        // No observation enters any of these later forwards. E changes actual motion at the next
        // imposition under the returned carry, while the fixed R reads the changed native signal.
        let later_opening = WordOpening::Received {
            carry: taught.prediction.carry.clone(),
            absorption: Absorption::Nothing,
        };
        let before = repair_by_field(
            &field,
            producing,
            &current,
            &damaged,
            &later_opening,
            &phases,
        )
        .unwrap();
        let after = repair_by_field(
            &field,
            &taught.constitution,
            &current,
            &damaged,
            &later_opening,
            &phases,
        )
        .unwrap();
        let other = repair_by_field(
            &field,
            &taught.constitution,
            &current,
            &swapped,
            &later_opening,
            &phases,
        )
        .unwrap();
        assert_ne!(before.carry.change, after.carry.change);
        assert_ne!(before.reads, after.reads);
        assert_ne!(after.carry.change, other.carry.change);
        assert_ne!(after.reads, other.reads);
        for reading in [&before, &after, &other] {
            assert!(reading.opening.closes() && reading.word.closes());
            assert!(reading.balances.iter().all(|balance| balance.closes()));
            for &station in &erased {
                let domain = reading.domains[station].as_ref().unwrap();
                assert!(domain.logits.iter().zip(&reading.reads[station].read.logits)
                    .all(|(interval, value)| &interval.lower <= value && value <= &interval.upper));
                match &reading.cells[station] {
                    RepairedCell::Held { fibre, unresolved: Unresolved::PluralDomain } => {
                        assert!(domain.classes.len() > 1);
                        assert_eq!(*fibre, domain.classes);
                    }
                    RepairedCell::Released(class) => assert_eq!(domain.classes, vec![*class]),
                    other => panic!("a supported leaky completion family has no domain decision: {other:?}"),
                }
            }
        }
        println!(
            "actual source teaching: rho {}; source clock {} -> {}; R unchanged; blind output {:?}; later target-free output {:?}; pre-teaching encoding swap logits {:?} / {:?}; post-teaching source-swap logits {:?} / {:?}",
            modulus,
            producing.clock(Locus::SourcePort(0)),
            taught.constitution.clock(Locus::SourcePort(0)),
            taught.prediction.cells,
            after.cells,
            blind.reads[1].read.logits,
            untaught_swap.reads[1].read.logits,
            after.reads[1].read.logits,
            other.reads[1].read.logits,
        );
    }

    #[test]
    fn source_teaching_refuses_a_zero_return_and_a_reached_uncertified_quartic() {
        use crate::hnn::prediction::predict_by_field;
        let field = field();
        let current = Current::at_rest(&field);
        let observed = crate::hnn::tests::support::encoded(&field, &[0, 2]);
        let damaged = DamagedSection::damage(&observed, &[1]).unwrap();
        let initial = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let phases = ReceivingPhases::declare(&field, &initial, &current, &section(2)).unwrap();
        let pending = predict_by_field(
            &field,
            &initial,
            &current,
            &damaged,
            &WordOpening::Rest,
            &phases,
        )
        .unwrap();
        let blind = pending.prediction().clone();
        let refusal = pending
            .observe_source_ports(&initial, &observed, &[false, true])
            .unwrap_err();
        assert_eq!(refusal.prediction, blind);
        assert!(matches!(
            refusal.error,
            crate::hnn::HnnError::Unadmitted {
                reason: "the physical comparison reaches no nonzero sample at the selected relation",
            }
        ));
        let nonlinear = quartic_material(&field);
        let phases = ReceivingPhases::declare(&field, &nonlinear, &current, &section(2)).unwrap();
        let pending = predict_by_field(
            &field,
            &nonlinear,
            &current,
            &damaged,
            &WordOpening::Rest,
            &phases,
        )
        .unwrap();
        let blind = pending.prediction().clone();
        let refusal = pending
            .observe_source_ports(&nonlinear, &observed, &[false, true])
            .unwrap_err();
        assert_eq!(refusal.prediction, blind);
        assert!(matches!(
            refusal.error,
            crate::hnn::HnnError::Unadmitted {
                reason: "source-port learning through a reached quartic needs the Word-Hessian certificate",
            }
        ));
    }
    fn quartic_material(field: &Field) -> Constitution {
        use crate::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
        use crate::holon::parametron::Carrier;
        (0..field.rings().len()).fold(
            Constitution::initial(field, CAMPAIGN_ONE_BUDGET).unwrap(),
            |material, ring| {
                let pump =
                    PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half)
                        .unwrap();
                let resonator = ResonatorMaterial::of_parametron(
                    &super::cycle(field.ring(ring).period() as usize),
                    &rat(1, 8),
                    Some(pump),
                )
                .unwrap()
                .with_symmetric_saturation(rat(1, 16))
                .unwrap();
                material
                    .with_ring_resonator(field, ring, resonator)
                    .unwrap()
            },
        )
    }

    fn quartic_teaching(field: &Field) -> (Constitution, crate::hnn::prediction::PhysicalTeaching) {
        let initial = quartic_material(field);
        let current = Current::at_rest(field);
        let phases = ReceivingPhases::declare(field, &initial, &current, &section(2)).unwrap();
        let observed = crate::hnn::tests::support::encoded(field, &[0, 2]);
        let damaged = DamagedSection::damage(&observed, &[1]).unwrap();
        let blind = crate::hnn::prediction::predict_by_field(
            field,
            &initial,
            &current,
            &damaged,
            &WordOpening::Rest,
            &phases,
        )
        .unwrap();
        assert!(matches!(
            blind.prediction().cells[1],
            RepairedCell::Held { .. }
        ));
        let teaching = blind.observe(&initial, &observed, &[false, true]).unwrap();
        assert_ne!(
            initial.receiving_map(0),
            teaching.constitution.receiving_map(0)
        );
        assert_eq!(initial.source_port(0), teaching.constitution.source_port(0));
        (initial, teaching)
    }

    #[test]
    fn the_coupled_quartic_tube_encloses_every_admitted_missing_class() {
        let field = field();
        let (_, teaching) = quartic_teaching(&field);
        let current = Current::at_rest(&field);
        let phases =
            ReceivingPhases::declare(&field, &teaching.constitution, &current, &section(4))
                .unwrap();
        let opening = WordOpening::Received {
            carry: teaching.prediction.carry.clone(),
            absorption: Absorption::Nothing,
        };
        let source = crate::hnn::tests::support::encoded(&field, &[1, 0, 3, 2]);
        let damaged = DamagedSection::damage(&source, &[1]).unwrap();
        let sparse = repair_by_field(
            &field,
            &teaching.constitution,
            &current,
            &damaged,
            &opening,
            &phases,
        )
        .unwrap();
        assert!(sparse.domains.iter().all(Option::is_some));
        assert!(
            sparse
                .domains
                .iter()
                .flatten()
                .any(|domain| domain.logits.iter().any(|interval| !interval.is_point()))
        );
        // Only the test oracle enumerates this tiny complete family. The production owner
        // derives its enclosure from E columns and never runs candidate completions.
        for missing in 0..field.alphabet() {
            let source = crate::hnn::tests::support::encoded(&field, &[1, missing, 3, 2]);
            let complete = DamagedSection::damage(&source, &[]).unwrap();
            let complete = repair_by_field(
                &field,
                &teaching.constitution,
                &current,
                &complete,
                &opening,
                &phases,
            )
            .unwrap();
            for (station, (domain, read)) in sparse.domains.iter().zip(&complete.reads).enumerate()
            {
                let domain = domain.as_ref().unwrap();
                for (interval, logit) in domain.logits.iter().zip(&read.read.logits) {
                    assert!(
                        &interval.lower <= logit && logit <= &interval.upper,
                        "completion {missing}, crossing {station} escaped its coupled tube"
                    );
                }
                assert!(
                    read.leaders()
                        .iter()
                        .all(|class| domain.classes.contains(class))
                );
            }
            assert!(complete.opening.closes() && complete.word.closes());
            assert!(complete.balances.iter().all(|balance| balance.closes()));
        }
        assert!(sparse.opening.closes() && sparse.word.closes());
        assert!(sparse.balances.iter().all(|balance| balance.closes()));
    }

    #[test]
    fn the_actual_leaky_completion_chart_encloses_mixed_classes_and_an_erased_age_endpoint() {
        let field = field();
        let (_, teaching) = quartic_teaching(&field);
        let theta = teaching.constitution.founded_transport(&field, 0).unwrap();
        let mut current = Current::at_rest(&field);
        current.rekey(&field, 0, 3).unwrap();
        let phases = ReceivingPhases::declare(&field, &theta, &current, &section(2)).unwrap();
        let opening = WordOpening::Received {
            carry: teaching.prediction.carry.clone(),
            absorption: Absorption::Nothing,
        };
        // The holes share a source phase, and the erased final station changes the full family's
        // age endpoint relative to the sparse point. The producing chart and nonzero lift stay
        // fixed. The envelope must consume actual per-slot chart rounding and normalization.
        let source = crate::hnn::tests::support::encoded(&field, &[1, 0, 3, 2, 1, 3, 0, 2, 2]);
        let damaged = DamagedSection::damage(&source, &[0, 8]).unwrap();
        let sparse = repair_by_field(&field, &theta, &current, &damaged, &opening, &phases).unwrap();
        assert!(sparse.domains.iter().all(Option::is_some));
        let empty = DamagedSection::damage(&source, &(0..9).collect::<Vec<_>>()).unwrap();
        let empty = repair_by_field(&field, &theta, &current, &empty, &opening, &phases).unwrap();
        assert!(empty.domains.iter().all(Option::is_some));
        let features = |cells: &[Option<usize>]| {
            let moment = crate::hnn::moment::SourceMoment::open_with(&field, &current, &theta)
                .unwrap().continued(&field, &current, 0, cells).unwrap();
            let mass = moment.transported_mass(0).unwrap().unwrap();
            assert!(mass > num_bigint::BigInt::zero());
            let features = (0..field.ring(0).placements().len())
                .flat_map(|phase| moment.normalized_counts(&field, 0, phase, &theta.transport(0)).unwrap())
                .collect::<Vec<_>>();
            (features, mass)
        };
        let monochrome: Vec<_> = (0..field.alphabet()).map(|class|
            features(&damaged.placed().iter().map(|cell| Some(cell.unwrap_or(class))).collect::<Vec<_>>())
        ).collect();
        let common_mass = monochrome[0].1.clone();
        assert!(monochrome.iter().all(|(_, mass)| *mass == common_mass));
        let monochrome: Vec<_> = monochrome.into_iter().map(|(features, _)| features).collect();
        let extrema = |rows: &[Vec<Rat>]| {
            (0..rows[0].len()).map(|coordinate| (
                rows.iter().map(|row| row[coordinate].clone()).min().unwrap(),
                rows.iter().map(|row| row[coordinate].clone()).max().unwrap(),
            )).collect::<Vec<_>>()
        };
        let mut all_features = Vec::new();
        let mut distinct = None;
        let mut changed = false;
        // This bounded test oracle runs the complete 4*4 family after the blind reception.
        // Production evaluates A source-coordinate supports and advances one actual Word.
        for first in 0..field.alphabet() {
            for last in 0..field.alphabet() {
                let actual = crate::hnn::tests::support::encoded(
                    &field, &[first, 0, 3, 2, 1, 3, 0, 2, last],
                );
                let complete = DamagedSection::damage(&actual, &[]).unwrap();
                let (feature, mass) = features(&complete.placed());
                assert_eq!(mass, common_mass, "mixed source classes changed their rounded denominator");
                all_features.push(feature);
                let complete = repair_by_field(
                    &field, &theta, &current, &complete, &opening, &phases,
                ).unwrap();
                for envelope in [&sparse, &empty] {
                    for (domain, read) in envelope.domains.iter().zip(&complete.reads) {
                        let domain = domain.as_ref().unwrap();
                        assert!(domain.logits.iter().zip(&read.read.logits)
                            .all(|(interval, value)| &interval.lower <= value && value <= &interval.upper),
                            "native mixed completion ({first},{last}) escaped its actual leaky source tube");
                        assert!(read.leaders().iter().all(|class| domain.classes.contains(class)));
                    }
                }
                if let Some(previous) = &distinct {
                    changed |= *previous != complete.reads;
                } else {
                    distinct = Some(complete.reads.clone());
                }
                assert!(complete.opening.closes() && complete.word.closes());
                assert!(complete.balances.iter().all(|balance| balance.closes()));
                println!("actual leaky completion ({first},{last}): leaders {:?}; actual complex logits {:?}",
                    complete.reads.iter().map(|read| read.leaders()).collect::<Vec<_>>(),
                    complete.reads.iter().map(|read| &read.read.logits).collect::<Vec<_>>());
            }
        }
        assert_eq!(extrema(&monochrome), extrema(&all_features),
            "the actual rounded normalized coordinate hull must equal the full two-hole hull");
        assert!(changed, "the actual completion field must be source-sensitive");
        for receipt in [&sparse, &empty] {
            assert!(receipt.opening.closes() && receipt.word.closes());
            assert!(receipt.balances.iter().all(|balance| balance.closes()));
        }
        println!("leaky source domain: rho {}; whole blind cells {:?}; actual complex bounds {:?}; total-erasure cells {:?}; no erased truth accuracy asserted",
            theta.transport(0), sparse.cells, sparse.domains, empty.cells);
    }

    #[test]
    fn a_blind_later_quartic_passage_releases_only_a_constant_learned_domain_image() {
        let field = field();
        let (initial, teaching) = quartic_teaching(&field);
        let current = Current::at_rest(&field);
        let phases =
            ReceivingPhases::declare(&field, &teaching.constitution, &current, &section(2))
                .unwrap();
        // A distinct actual intact source, independent of the former observation. The later
        // erased value is absent from its constructor, and only two crossings are requested.
        let mut later = vec![0; 64];
        later[0] = 1;
        let later = crate::hnn::tests::support::encoded(&field, &later);
        let later = DamagedSection::damage(&later, &[1]).unwrap();
        let opening = WordOpening::Received {
            carry: teaching.prediction.carry.clone(),
            absorption: Absorption::Nothing,
        };
        let after = repair_by_field(
            &field,
            &teaching.constitution,
            &current,
            &later,
            &opening,
            &phases,
        )
        .unwrap();
        let before =
            repair_by_field(&field, &initial, &current, &later, &opening, &phases).unwrap();
        assert!(matches!(
            before.cells[1],
            RepairedCell::Held {
                unresolved: Unresolved::PluralDomain,
                ..
            }
        ));
        assert_ne!(after.reads, before.reads);
        assert_eq!(after.carry.change, before.carry.change);
        let domain = after.domains[1].as_ref().unwrap();
        // Diagnose the fixed failed family after the blind output. These complete source
        // controls never enter the learner or its certificate and select no desired class.
        println!(
            "blind output {:?}; actual sparse grain leaders {:?}; actual sparse logits {:?}; enclosing image {:?}",
            after.cells,
            after.reads[1].leaders(),
            after.reads[1].read.logits,
            domain
        );
        for missing in 0..field.alphabet() {
            let mut complete = vec![0; 64];
            complete[0] = 1;
            complete[1] = missing;
            let complete = crate::hnn::tests::support::encoded(&field, &complete);
            let complete = DamagedSection::damage(&complete, &[]).unwrap();
            let complete = repair_by_field(
                &field,
                &teaching.constitution,
                &current,
                &complete,
                &opening,
                &phases,
            )
            .unwrap();
            assert!(
                complete.reads[1]
                    .read
                    .logits
                    .iter()
                    .zip(&domain.logits)
                    .all(|(value, interval)| &interval.lower <= value && value <= &interval.upper)
            );
            assert!(
                complete.reads[1]
                    .leaders()
                    .iter()
                    .all(|class| domain.classes.contains(class))
            );
            println!(
                "native source completion {missing}: grain leaders {:?}; actual logits {:?}",
                complete.reads[1].leaders(),
                complete.reads[1].read.logits
            );
        }
        assert_eq!(
            domain.classes.len(),
            1,
            "the declared later passage has no constant decoded image: {:?}",
            domain.classes
        );
        assert_eq!(after.cells[1], RepairedCell::Released(domain.classes[0]));
        // The same learned relation reads another actual intact source and a rest interior.
        let changed = crate::hnn::tests::support::encoded(&field, &vec![3; 64]);
        let changed = DamagedSection::damage(&changed, &[1]).unwrap();
        let changed = repair_by_field(
            &field,
            &teaching.constitution,
            &current,
            &changed,
            &opening,
            &phases,
        )
        .unwrap();
        assert_ne!(changed.reads, after.reads);
        assert_ne!(changed.carry.change, after.carry.change);
        let absorbed = repair_by_field(
            &field,
            &teaching.constitution,
            &current,
            &later,
            &WordOpening::Received {
                carry: teaching.prediction.carry.clone(),
                absorption: Absorption::Complete,
            },
            &phases,
        )
        .unwrap();
        assert_ne!(absorbed.reads, after.reads);
        assert_ne!(absorbed.carry.change, after.carry.change);
        // Total erasure retains the whole source-completion uncertainty, with no smaller ball
        // selected to make the formerly taught class win.
        let empty = DamagedSection::damage(
            &crate::hnn::tests::support::encoded(&field, &vec![0; 64]),
            &(0..64).collect::<Vec<_>>(),
        )
        .unwrap();
        let empty = repair_by_field(
            &field,
            &teaching.constitution,
            &current,
            &empty,
            &opening,
            &phases,
        )
        .unwrap();
        assert!(matches!(empty.cells[1], RepairedCell::Held { .. }));
        let leaky = teaching
            .constitution
            .clone()
            .with_transport(0, rat(1, 2))
            .unwrap();
        let supported =
            repair_by_field(&field, &leaky, &current, &later, &opening, &phases).unwrap();
        assert!(supported.domains.iter().all(Option::is_some));
        assert!(supported.domains.iter().zip(&supported.reads).all(|(domain, read)|
            domain.as_ref().unwrap().logits.iter().zip(&read.read.logits)
                .all(|(interval, value)| &interval.lower <= value && value <= &interval.upper)));
        assert!(supported.opening.closes() && supported.word.closes());
        assert!(supported.balances.iter().all(|balance| balance.closes()));
        assert!(after.opening.closes() && after.word.closes());
        assert!(after.balances.iter().all(|balance| balance.closes()));
        println!(
            "blind coupled quartic output: {:?}; image fibre {:?}; exact receiving bounds {:?}",
            after.cells, domain.classes, domain.logits
        );
    }

    /// A fixed behavioral read, not a task-accuracy gate: diverse observations may distinguish
    /// receiving rows that one class-2 observation leaves equal. Every observation follows its
    /// own contemporary blind Word. Probes contain no omitted class or expected output; the
    /// initial and learned materials read the same entered carry, clock, chart and intact runs.
    #[test]
    fn the_retained_physical_reader_reports_distinct_observations_and_matched_source_controls() {
        use crate::hnn::constitution::Locus;
        use crate::hnn::prediction::predict_by_field;
        let field = field();
        let initial = quartic_material(&field).founded_transport(&field, 0).unwrap();
        let mut current = Current::at_rest(&field);
        current.rekey(&field, 0, 3).unwrap();
        let mut theta = initial.clone();
        let mut opening = WordOpening::Rest;
        let closes = |receipt: &PhysicalRepair| {
            assert!(receipt.opening.closes() && receipt.word.closes());
            assert!(receipt.balances.iter().all(|balance| balance.closes()));
        };
        // Fixed before the behavioral read. These are exterior observed comparisons, not a
        // solution family installed in a source/receiver. A blind input retains only its cue.
        for (comparison, cells) in [[0, 2], [1, 1], [3, 3]].iter().enumerate() {
            let observed = crate::hnn::tests::support::encoded(&field, cells);
            let damaged = DamagedSection::damage(&observed, &[1]).unwrap();
            let phases = ReceivingPhases::declare(&field, &theta, &current, &section(2)).unwrap();
            let pending = predict_by_field(
                &field, &theta, &current, &damaged, &opening, &phases,
            ).unwrap();
            let blind = pending.prediction().clone();
            closes(&blind);
            println!("native comparison {comparison} blind whole cells {:?}; actual logits {:?}; entered word end tick {}",
                blind.cells, blind.reads.iter().map(|read| &read.read.logits).collect::<Vec<_>>(), blind.carry.ticks);
            // Only here does the teacher cross the declared station-1 comparison section.
            let taught = pending.observe(&theta, &observed, &[false, true]).unwrap();
            assert_eq!(taught.prediction, blind);
            assert_ne!(theta.receiving_map(0), taught.constitution.receiving_map(0));
            assert_eq!(theta.source_port(0), taught.constitution.source_port(0));
            assert_eq!(theta.transport(0), taught.constitution.transport(0));
            for ring in 0..field.rings().len() {
                assert_eq!(theta.contrast_law(ring), taught.constitution.contrast_law(ring));
                assert_eq!(theta.passive_factor(ring), taught.constitution.passive_factor(ring));
                assert_eq!(theta.ring_resonator(ring), taught.constitution.ring_resonator(ring));
            }
            println!("native comparison {comparison} observed receiving publication: commit {} -> {}; R clock {} -> {}; actual ratio {:?}; actual normal steps {:?}",
                theta.commit(), taught.constitution.commit(),
                theta.clock(Locus::ReceivingMap(0)), taught.constitution.clock(Locus::ReceivingMap(0)),
                taught.ratio, taught.publication.steps);
            theta = taught.constitution;
            opening = WordOpening::Received { carry: blind.carry, absorption: Absorption::Nothing };
        }
        let map = theta.receiving_map(0).unwrap();
        println!("retained receiving material: full actual R {:?}; equal real rows 0/1 {}; 0/3 {}; 1/3 {}; full source E unchanged {}; transport {}",
            map, map.row(0).unwrap() == map.row(2).unwrap(),
            map.row(0).unwrap() == map.row(6).unwrap(), map.row(2).unwrap() == map.row(6).unwrap(),
            theta.source_port(0) == initial.source_port(0), theta.transport(0));
        let phases = ReceivingPhases::declare(&field, &theta, &current, &section(2)).unwrap();
        for cue in [0, 1, 3] {
            // A different four-station passage. No value for its omitted station is ever made;
            // both controls receive this same cell-free chart plus exactly the intact runs.
            let left = crate::hnn::tests::support::encoded(&field, &[cue]);
            let chart = left.part(0..0).unwrap();
            let right = crate::hnn::tests::support::encoded(&field, &[3, 0]);
            let probe = DamagedSection::of_runs(4, &chart, vec![(0, left), (2, right)]).unwrap();
            assert_eq!(probe.placed(), vec![Some(cue), None, Some(3), Some(0)]);
            let before = repair_by_field(&field, &initial, &current, &probe, &opening, &phases).unwrap();
            let after = repair_by_field(&field, &theta, &current, &probe, &opening, &phases).unwrap();
            closes(&before);
            closes(&after);
            assert_eq!(before.carry, after.carry, "R-only teaching must leave matched native motion fixed");
            println!("target-free native probe: actual intact source {:?}; initial-R whole output {:?}; learned-R whole output {:?}; initial-R leaders {:?}; learned-R leaders {:?}; initial-R complex logits {:?}; learned-R complex logits {:?}; learned domain {:?}; returned tick {}",
                probe.placed(), before.cells, after.cells,
                before.reads.iter().map(|read| read.leaders()).collect::<Vec<_>>(),
                after.reads.iter().map(|read| read.leaders()).collect::<Vec<_>>(),
                before.reads.iter().map(|read| &read.read.logits).collect::<Vec<_>>(),
                after.reads.iter().map(|read| &read.read.logits).collect::<Vec<_>>(),
                after.domains, after.carry.ticks);
        }
        // No output class, singleton, rank increase, fidelity or description-length decrease
        // is an acceptance requirement. The whole actual behavior is the diagnostic result.
    }

    /// A tensor-basis unit chart for a declared pair port, independent of any target/answer.
    /// Its sixteen coordinates expose the four-by-four ordered pair table at a period-eight
    /// source. The receiving chart exposes its first eight physical coordinates; no class
    /// output is prescribed. This fixture tests the source-to-Word join, not learned pair material.
    fn paired_chart(field: &Field) -> Constitution {
        use crate::hnn::moment::PairPort;
        let theta = quartic_material(field);
        let a = field.alphabet();
        let n = field.ring(0).width();
        let rank = theta.pair_port(0, 1).unwrap().rank();
        assert_eq!(rank, a*a);
        assert_eq!(n, rank);
        let basis = |length: usize, coordinate: usize| {
            let mut row = vec![Rat::zero(); length];
            row[coordinate] = integer(1);
            row
        };
        let pair = PairPort::new(
            (0..rank).map(|rho| basis(n, rho)).collect(),
            (0..rank).map(|rho| basis(a, rho/a)).collect(),
            (0..rank).map(|rho| basis(a, rho%a)).collect(),
        ).unwrap();
        let receiving = ExactRatMatrix::shaped(2*a, n,
            (0..2*a).map(|coordinate| basis(n, coordinate)).collect()).unwrap();
        theta.with_pair(0, 1, pair).unwrap()
            .with_ports(0, None, None, Some(receiving)).unwrap()
    }

    #[test]
    fn the_station_pair_source_preserves_actual_offsets_and_refuses_a_reused_opening() {
        let field = field_with_lock_and_offsets((0..8).collect(), vec![1, 2]);
        let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let mut current = Current::at_rest(&field);
        current.rekey(&field, 0, 3).unwrap();
        let open = SourceMoment::open_with(&field, &current, &theta).unwrap();
        let cells = [Some(0), None, Some(1), Some(3), None];
        let source = open.station_section(&field, &current, 0, &cells).unwrap();
        let marginal = open.continued(&field, &current, 0, &cells).unwrap();
        assert_eq!(source.population(0).unwrap(), 3);
        for phase in 0..8 {
            assert_eq!(source.phase_counts(0, phase).unwrap(), marginal.phase_counts(0, phase).unwrap());
        }
        assert_eq!(source.pair_population(0, 1).unwrap(), 1);
        assert_eq!(source.pair_population(0, 2).unwrap(), 1);
        assert_eq!(source.offset_counts(0, 1, 7).unwrap()[3*4+1], 1);
        assert_eq!(source.offset_counts(0, 2, 6).unwrap()[4], 1);
        assert!(source.station_section(&field, &current, 0, &cells).is_err());
        let mut moved = current.clone();
        moved.rekey(&field, 0, 4).unwrap();
        assert!(open.station_section(&field, &moved, 0, &cells).is_err());
        // Independently executed unit identity clock: no erasure, no carry-out in these four cells.
        let full = crate::hnn::tests::support::encoded(&field, &[0, 1, 2, 3]);
        let section = open.station_section(&field, &current, 0,
            &full.cells().iter().map(|cell| Some(cell.class())).collect::<Vec<_>>()).unwrap();
        let mut ingested = open.clone();
        let mut walked = current.clone();
        assert_eq!(ingested.ingest(&field, &mut walked, &full).unwrap().cells, 4);
        for phase in 0..8 {
            assert_eq!(section.phase_counts(0, phase).unwrap(), ingested.phase_counts(0, phase).unwrap());
            for offset in [1, 2] {
                assert_eq!(section.offset_counts(0, offset, phase).unwrap(), ingested.offset_counts(0, offset, phase).unwrap());
            }
        }
        assert_eq!(section.encode(&field, &theta, 0).unwrap(), ingested.encode(&field, &theta, 0).unwrap());
        // A declared delta longer than this span has an exact empty pair feature box.
        let (lower, upper) = open.station_pair_bounds(&field, &current, 0, &[Some(0)], 2).unwrap().unwrap();
        assert!(lower.iter().chain(&upper).flatten().all(Zero::is_zero));
    }

    #[test]
    fn the_station_pair_box_contains_all_mixed_unit_and_rounded_leaky_features() {
        let field = field_with_lock_and_offsets((0..8).collect(), vec![1, 2]);
        let initial = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let mut current = Current::at_rest(&field);
        current.rekey(&field, 0, 3).unwrap();
        let placed = [Some(0), None, None, Some(3)];
        for theta in [initial.clone(), initial.founded_transport(&field, 0).unwrap()] {
            let open = SourceMoment::open_with(&field, &current, &theta).unwrap();
            for offset in [1, 2] {
                let (lower, upper) = open.station_pair_bounds(&field, &current, 0, &placed, offset).unwrap().unwrap();
                for x in 0..4 { for y in 0..4 {
                    let full = [Some(0), Some(x), Some(y), Some(3)];
                    let source = open.station_section(&field, &current, 0, &full).unwrap();
                    let table = source.offset_table(&field, 0, offset).unwrap().unwrap();
                    assert_eq!(table.population, (4-offset) as u64);
                    for phase in 0..8 {
                        let mut row = vec![Rat::zero(); 16];
                        for (slot, value) in table.normalized(phase, 4) { row[slot] = value }
                        for slot in 0..16 {
                            assert!(lower[phase][slot] <= row[slot] && row[slot] <= upper[phase][slot]);
                        }
                    }
                }}
            }
            // Monochrome hole completions miss this heterotypic edge at station2, phase6.
            let (_, upper) = open.station_pair_bounds(&field, &current, 0, &placed, 1).unwrap().unwrap();
            assert!(upper[6][4] > Rat::zero());
            for class in 0..4 {
                let mono = open.station_section(&field, &current, 0,
                    &[Some(0), Some(class), Some(class), Some(3)]).unwrap();
                assert_eq!(mono.offset_counts(0, 1, 6).unwrap()[4], 0);
            }
        }
    }

    #[test]
    fn a_declared_station_pair_reaches_the_native_word_and_separates_a_marginal_alias() {
        let field = field_with_lock_and_offsets((0..8).collect(), vec![1]);
        let theta = paired_chart(&field);
        let mut current = Current::at_rest(&field);
        current.rekey(&field, 0, 3).unwrap();
        let mut left = vec![2; 9];
        left[0] = 0; left[8] = 1;
        let mut right = left.clone(); right.swap(0, 8);
        let open = SourceMoment::open_with(&field, &current, &theta).unwrap();
        let left_cells: Vec<_> = left.iter().copied().map(Some).collect();
        let right_cells: Vec<_> = right.iter().copied().map(Some).collect();
        assert_eq!(open.continued(&field, &current, 0, &left_cells).unwrap(),
            open.continued(&field, &current, 0, &right_cells).unwrap());
        let l = open.station_section(&field, &current, 0, &left_cells).unwrap();
        let r = open.station_section(&field, &current, 0, &right_cells).unwrap();
        assert_ne!(l.encode(&field, &theta, 0).unwrap(), r.encode(&field, &theta, 0).unwrap());
        let phases = ReceivingPhases::declare(&field, &theta, &current, &section(2)).unwrap();
        let mut receipts = Vec::new();
        for cells in [left, right] {
            let encoded = crate::hnn::tests::support::encoded(&field, &cells);
            let section = DamagedSection::damage(&encoded, &[]).unwrap();
            let repair = repair_by_field(&field, &theta, &current, &section, &WordOpening::Rest, &phases).unwrap();
            assert!(repair.opening.closes() && repair.word.closes());
            assert!(repair.balances.iter().all(|b| b.closes()));
            receipts.push(repair);
        }
        assert_ne!(receipts[0].carry.change, receipts[1].carry.change);
        assert_ne!(receipts[0].reads, receipts[1].reads);
        println!("declared tensor-pair chart separates the source alias: actual native reads {:?} / {:?}",
            receipts[0].reads, receipts[1].reads);
    }

    #[test]
    fn the_joint_pair_physical_tube_contains_every_mixed_completed_word_read() {
        let field = field_with_lock_and_offsets((0..8).collect(), vec![1]);
        let initial = paired_chart(&field);
        let mut current = Current::at_rest(&field);
        current.rekey(&field, 0, 3).unwrap();
        let chart = crate::hnn::tests::support::encoded(&field, &[]);
        let left = crate::hnn::tests::support::encoded(&field, &[0]);
        let right = crate::hnn::tests::support::encoded(&field, &[3]);
        let damaged = DamagedSection::of_runs(4, &chart, vec![(0,left),(3,right)]).unwrap();
        for theta in [initial.clone(), initial.founded_transport(&field, 0).unwrap()] {
            let phases = ReceivingPhases::declare(&field, &theta, &current, &section(2)).unwrap();
            let blind = repair_by_field(&field, &theta, &current, &damaged, &WordOpening::Rest, &phases).unwrap();
            assert!(blind.domains.iter().all(Option::is_some));
            assert!(blind.opening.closes() && blind.word.closes());
            for x in 0..4 { for y in 0..4 {
                let full = crate::hnn::tests::support::encoded(&field, &[0,x,y,3]);
                let full = DamagedSection::damage(&full, &[]).unwrap();
                let read = repair_by_field(&field, &theta, &current, &full, &WordOpening::Rest, &phases).unwrap();
                assert!(read.opening.closes() && read.word.closes());
                assert!(read.balances.iter().all(|b| b.closes()));
                for (domain, read) in blind.domains.iter().zip(&read.reads) {
                    for (bound, value) in domain.as_ref().unwrap().logits.iter().zip(&read.read.logits) {
                        assert!(&bound.lower <= value && value <= &bound.upper);
                    }
                }
            }}
            println!("joint station-pair physical tube: rho {}; blind whole cells {:?}; actual complex bounds {:?}",
                theta.transport(0), blind.cells, blind.domains);
        }
    }

    /// Twelve fixed Words separate material checkpoint, entered interior and absent-source
    /// controls. Checkpoints are exterior counterfactual operands, never a retained event tape.
    /// No label, diversity, singleton or accuracy is required of the readouts.
    #[test]
    fn the_retained_reader_reports_matched_material_carry_and_absent_source_controls() {
        use crate::hnn::prediction::predict_by_field;
        let field = field();
        let mut theta = quartic_material(&field).founded_transport(&field, 0).unwrap();
        let mut current = Current::at_rest(&field);
        current.rekey(&field, 0, 3).unwrap();
        let mut opening = WordOpening::Rest;
        let mut materials = vec![theta.clone()];
        let mut carries = Vec::new();
        for cells in [[0,2], [1,1], [3,3]] {
            let observed = crate::hnn::tests::support::encoded(&field, &cells);
            let damaged = DamagedSection::damage(&observed, &[1]).unwrap();
            let phases = ReceivingPhases::declare(&field, &theta, &current, &section(2)).unwrap();
            let pending = predict_by_field(&field, &theta, &current, &damaged, &opening, &phases).unwrap();
            let blind = pending.prediction().clone();
            let taught = pending.observe(&theta, &observed, &[false,true]).unwrap();
            assert_eq!(blind, taught.prediction);
            assert!(blind.opening.closes() && blind.word.closes());
            assert!(blind.balances.iter().all(|b| b.closes()));
            theta = taught.constitution;
            materials.push(theta.clone());
            carries.push(blind.carry.clone());
            opening = WordOpening::Received { carry: blind.carry, absorption: Absorption::Nothing };
        }
        let left = crate::hnn::tests::support::encoded(&field, &[0]);
        let chart = left.part(0..0).unwrap();
        let right = crate::hnn::tests::support::encoded(&field, &[3,0]);
        let probe = DamagedSection::of_runs(4, &chart, vec![(0,left),(2,right)]).unwrap();
        let absent = DamagedSection::of_runs(4, &chart, Vec::new()).unwrap();
        let phases = ReceivingPhases::declare(&field, &theta, &current, &section(2)).unwrap();
        let read = |label: &str, material: &Constitution, opening: &WordOpening, probe: &DamagedSection| {
            let receipt = repair_by_field(&field, material, &current, probe, opening, &phases).unwrap();
            assert!(receipt.opening.closes() && receipt.word.closes());
            assert!(receipt.balances.iter().all(|b| b.closes()));
            println!("matched retained-reader control {label}: R commit {}; actual intact source {:?}; whole cells {:?}; leaders {:?}; complex logits {:?}; carry tick {}",
                material.commit(), probe.placed(), receipt.cells,
                receipt.reads.iter().map(|r| r.leaders()).collect::<Vec<_>>(),
                receipt.reads.iter().map(|r| &r.read.logits).collect::<Vec<_>>(), receipt.carry.ticks);
            receipt
        };
        let mut common_motion = None;
        for (index, material) in materials.iter().enumerate() {
            let receipt = read(&format!("material{index}/enteredC3"), material, &opening, &probe);
            if let Some(carry) = &common_motion { assert_eq!(carry, &receipt.carry) }
            else { common_motion = Some(receipt.carry) }
        }
        read("R3/rest", &theta, &WordOpening::Rest, &probe);
        for (index, carry) in carries.iter().take(2).enumerate() {
            read(&format!("R3/enteredC{}",index+1), &theta,
                &WordOpening::Received { carry: carry.clone(), absorption: Absorption::Nothing }, &probe);
        }
        read("R3/absent-source/rest", &theta, &WordOpening::Rest, &absent);
        read("R3/absent-source/enteredC3", &theta, &opening, &absent);
    }

}
