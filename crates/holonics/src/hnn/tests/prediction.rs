//! Native generation (`hnn::prediction`): the continuing word, the passage's placement of the
//! section, the partition law, the receiving bank's placement and its locks, and the release's own
//! comparison (`hnn::executed`).

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::learning::{chain, generic, moment};
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
fn cycle(d: usize) -> Parametron {
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
fn resonant(field: &Field, theta: Constitution) -> Constitution {
    let mut resonant = theta;
    for ring in 0..field.rings().len() {
        let period = field.ring(ring).period() as usize;
        let pump =
            PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half).unwrap();
        resonant = resonant
            .with_ring_resonator(
                field,
                ring,
                ResonatorMaterial::of_parametron(&cycle(period), &rat(1, 8), Some(pump)).unwrap(),
            )
            .unwrap();
    }
    resonant
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
        moment.ingest(&field, &mut current, &cells).unwrap();
        (current, moment)
    };
    let (current, request) = {
        let mut current = Current::at_rest(&field);
        let mut moment = SourceMoment::open(&field, &current);
        moment.ingest(&field, &mut current, &cells[..7]).unwrap();
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

// -------------------------------------------------------------------------------------------
// the joint field's bank

/// The bank of the joint field's tests: one node `C = I`, `K = I`, `Y = 16`, `h = 1`, the members
/// whose period divides the ring's 6 (standing and half-turn), at `p = 5/8`.
pub(super) fn joint_bank() -> ReceivingBank {
    let identity = ExactRatMatrix::identity(2).unwrap();
    let axis = Carrier::new(Rat::one(), Rat::zero()).unwrap();
    ReceivingBank::new(
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
    .unwrap()
}

// -------------------------------------------------------------------------------------------
// the release's own comparison (`hnn::executed`)

/// The joint field's requests at drawn moments, with their targets and context.
pub(super) fn executed_requests(
    field: &Field,
    cases: &[(u64, [usize; 4])],
    context: crate::hnn::executed::Context,
) -> Vec<crate::hnn::executed::Request> {
    cases
        .iter()
        .map(|&(seed, targets)| {
            let (current, moment) = moment(field, seed, 8);
            crate::hnn::executed::Request {
                current,
                moment,
                targets: targets.to_vec(),
                context: context.clone(),
            }
        })
        .collect()
}

/// **The release's own comparison reads the release** (`hnn::executed::compare`): on an open
/// context its release is `generate_by_bank`'s exactly, every refinement's open stations are
/// compared, each station's class and threshold predicates agree with its target's and leading
/// rival's enclosures, a refinement's lock is safe exactly when every station it locked reads its
/// target, and `F` is the sum of the stations' positive parts.
#[test]
fn the_release_comparison_reads_the_bank_release() {
    use crate::hnn::executed::{Comparison, Context, Predicate, compare};
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests = executed_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])], Context::Open);
    let batch = compare(&field, &theta, &requests, &refinement, &bank, 12, Comparison::HINGE_EVERY).unwrap();
    let mut total = Rat::zero();
    for (request, compared) in requests.iter().zip(&batch.requests) {
        let generated = generate_by_bank(
            &field,
            &theta,
            &request.current,
            &request.moment,
            &refinement,
            &bank,
            12,
        )
        .unwrap();
        assert_eq!(compared.generation.as_ref(), Some(&generated));
        assert_eq!(compared.orders.len(), generated.refinements);
        for station in &compared.stations {
            let (t, r) = (&station.target_growth, &station.rival_growth);
            assert_eq!(station.class == Predicate::Holds, t.exceeds(r));
            assert_eq!(station.threshold == Predicate::Holds, t.is_locked());
            assert!(station.value.lower <= station.value.upper);
            total += station.value.lower.clone().max(Rat::zero());
        }
        for order in &compared.orders {
            if let Some(safe) = order.safe {
                let right = order
                    .locked
                    .iter()
                    .all(|&s| generated.release.classes[s] == request.targets[s]);
                assert_eq!(safe, right);
            }
        }
    }
    assert_eq!(batch.value.lower, total);
}

/// **The proposal's returns are its pullback to `E`** (`hnn::executed`, "The covector"): for a drawn
/// move `ΔE` of the source port, the returns pair with it as the contributions' storage covectors
/// (at their dyadic faces, with their signs) pair with the storage moves `ΔE` places, exactly:
/// `Σ w ⟨g, ΔE f⟩ = −Σ_c sign_c ⟨ĝ_c, δz_c⟩`, each `δz_c` the section's storage read from the
/// contribution's station with `ΔE` at the source port (the storage is linear in `E` at fixed
/// weights). At a transport of modulus one (every weight `ν̂(n + v)`) and at `3/4`, where each
/// contribution's weights are read from its own station (the station-framed law): the returns keep
/// their form, and some contribution's section holds a placed datum after its station, so a
/// two-sided weight enters the identity.
#[test]
fn the_proposals_returns_are_its_pullback_to_e() {
    use crate::hnn::executed::{Comparison, Context, Request, proposal_returns};
    let field = joint();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let cases: [(u64, [usize; 4]); 3] = [(95, [0, 1, 2, 1]), (97, [2, 0, 1, 1]), (96, [1, 1, 0, 2])];
    for (modulus, cells) in [(Rat::one(), 8usize), (rat(3, 4), 2)] {
        let theta = generic(&field, 94).with_transport(0, modulus.clone()).unwrap();
        let requests: Vec<Request> = cases
            .iter()
            .map(|&(seed, targets)| {
                let (current, moment) = moment(&field, seed, cells);
                Request {
                    current,
                    moment,
                    targets: targets.to_vec(),
                    context: Context::Open,
                }
            })
            .collect();
        let (samples, contributions) =
            proposal_returns(&field, &theta, &requests, &refinement, &bank, 12, Comparison::HINGE_EVERY).unwrap();
        assert!(!contributions.is_empty());
        if !modulus.is_one() {
            assert!(
                contributions
                    .iter()
                    .any(|(_, station, cells, ..)| cells[*station + 1..].iter().any(Option::is_some)),
                "a contribution reads a placed datum after its station"
            );
        }
        let port = theta.source_port(0).unwrap().clone();
        let direction = Draw::new(98).matrix(port.rows(), port.columns());
        let moved = theta
            .clone()
            .with_ports(0, None, Some(direction.clone()), None)
            .unwrap();
        let mut paired = Rat::zero();
        for sample in &samples {
            let image = direction.apply(&sample.feature).unwrap();
            paired += &sample.weight
                * sample
                    .covector
                    .iter()
                    .zip(&image)
                    .map(|(g, m)| g * m)
                    .sum::<Rat>();
        }
        let mut expected = Rat::zero();
        for (request, station, cells, covector, sign) in &contributions {
            let r = &requests[*request];
            let placement =
                BankPlacement::of(&field, &moved, &r.current, &r.moment, &refinement).unwrap();
            let storage = placement.storage(*station, cells);
            expected -= sign * covector.iter().zip(&storage).map(|(g, z)| g * z).sum::<Rat>();
        }
        assert_eq!(paired, expected, "at modulus {modulus}");
    }
}

/// **The committed move descends the release's comparison, or refuses by type**
/// (`hnn::executed::executed_move`): on two requests along the machine's own trajectory the move
/// is adopted, and its successor reads `F` strictly lower by disjoint enclosures, holds every entry
/// of `E` within the bound, certifies its first order, admits every crossing, certifies every lock
/// and counts one commit; every trial before the adopted one names the guard that refused it.
#[test]
fn the_committed_move_descends_or_refuses_by_type() {
    use crate::hnn::executed::{Comparison, Context, entry_bound, executed_move};
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests = executed_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])], Context::Open);
    let moved = executed_move(&field, &theta, &requests, &refinement, &bank, 12, Comparison::HINGE_EVERY).unwrap();
    for trial in &moved.trials[..moved.trials.len().saturating_sub(1)] {
        assert!(trial.refusal.is_some());
    }
    match &moved.adopted {
        Some((successor, step)) => {
            let last = moved.trials.last().unwrap();
            assert!(last.refusal.is_none());
            let after = last.after.as_ref().unwrap();
            // The descent account is read on the fixed incumbent mask (the pin §13.1).
            assert!(last.value.as_ref().unwrap().upper < moved.before.value.lower);
            assert!(last.first_order.as_ref().unwrap().upper.is_negative());
            assert!(step.largest <= entry_bound());
            assert_eq!(
                &step.largest,
                &successor
                    .source_port(0)
                    .unwrap()
                    .entries()
                    .iter()
                    .map(|x| x.abs())
                    .max()
                    .unwrap()
            );
            assert!(after
                .requests
                .iter()
                .all(|r| r.generation.as_ref().unwrap().uncertified.is_none()));
            assert_eq!(successor.commit(), theta.commit() + 1);
        }
        None => panic!("the move on this instance is adopted: {:?}", moved.refusal),
    }
}

/// **The move's receipts read its certificate** (`hnn::executed::{FirstOrderReading, TermSite}`;
/// receipts only, the
/// [two counts' pin](../../../../../research/records/2026-09-30_THE_TWO_COUNTS_PINNED_BEFORE_ITS_RUNS.md)
/// §5): on the committed move's instance, every trial that read its first order carries one bound
/// per term of the proposal, aligned with the move's sites, and their sum is the certificate
/// exactly (a straddling term's bound hinged at zero); every site names a request of the batch and
/// a station of the section; the leading branches' pairing on the carried move lies at or below the
/// certificate's upper end (each leading branch is one of its term's active branches, paired with
/// the same exact storage moves); the unit move's largest entry is read, and the adopted trial
/// carries the adopted source step's reading.
#[test]
fn the_moves_receipts_read_its_certificate() {
    use crate::hnn::executed::{Comparison, Context, executed_move};
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests = executed_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])], Context::Open);
    let moved = executed_move(&field, &theta, &requests, &refinement, &bank, 12, Comparison::HINGE_EVERY).unwrap();
    assert!(moved.unit_largest.as_ref().is_some_and(|u| u.is_positive()));
    assert_eq!(moved.sites.len(), moved.terms);
    for site in &moved.sites {
        assert!(site.request < requests.len());
        assert!(site.station < 4);
    }
    let mut read = 0;
    for trial in &moved.trials {
        let Some(bound) = &trial.first_order else {
            continue;
        };
        read += 1;
        let terms = trial.terms.as_ref().expect("each term's bound");
        assert_eq!(terms.len(), moved.sites.len());
        let (mut lower, mut upper) = (Rat::zero(), Rat::zero());
        for (term, site) in terms.iter().zip(&moved.sites) {
            let Some(term) = term else { continue };
            let kind = moved.before.requests[site.request]
                .terms
                .iter()
                .find(|t| &t.site == site)
                .expect("each site is a term of the incumbent's reading")
                .kind;
            if kind != crate::hnn::executed::Excess::Above {
                assert!(!term.lower.is_negative());
            }
            lower += &term.lower;
            upper += &term.upper;
        }
        assert_eq!(lower, bound.lower);
        assert_eq!(upper, bound.upper);
        let leading = trial.leading.as_ref().expect("the leading branches' pairing");
        assert!(leading.lower <= leading.upper);
        assert!(leading.upper <= bound.upper);
        assert!(trial.source.is_some());
    }
    assert!(read > 0);
    let (_, step) = moved.adopted.as_ref().expect("the move on this instance is adopted");
    assert_eq!(moved.trials.last().unwrap().source.as_ref(), Some(step));
}

/// **The committed move carries the transport modulus** (`hnn::executed`, "The committed move";
/// `hnn::moment`, "One passage, its transported weights"): from a transport of modulus `3/4` on
/// requests whose span with the stations fills one turn, the move reads the modulus's slope, and an
/// adopted successor keeps a passive modulus on the source port's lattice (the trial's), lowers the
/// comparison by disjoint enclosures with its first order certified negative on the carried move,
/// and holds every lock's certificate; every earlier trial names its guard.
#[test]
fn the_committed_move_carries_the_transport_modulus() {
    use crate::hnn::executed::{Comparison, Context, Request, executed_move};
    let field = joint();
    let theta = generic(&field, 94).with_transport(0, rat(3, 4)).unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests: Vec<Request> = [(95u64, [0usize, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]
        .iter()
        .map(|&(seed, targets)| {
            let (current, moment) = moment(&field, seed, 2);
            Request {
                current,
                moment,
                targets: targets.to_vec(),
                context: Context::Open,
            }
        })
        .collect();
    let moved = executed_move(&field, &theta, &requests, &refinement, &bank, 12, Comparison::HINGE_EVERY).unwrap();
    assert!(moved.modulus_slope.is_some() || moved.refusal.is_some());
    for trial in &moved.trials[..moved.trials.len().saturating_sub(1)] {
        assert!(trial.refusal.is_some());
    }
    let Some((successor, _)) = &moved.adopted else {
        panic!("the move on this instance is adopted: {:?}", moved.refusal);
    };
    // The modulus's unit move is its least-squares step `−γ_ρ/G_ρ` (Lean
    // `HNN/ExecutedComparison.modulus_least_squares`), proportional to its slope, and its
    // first-order share `γ_ρΔρ = −γ_ρ²/G_ρ` is negative; the adopted trial carries `ρ + ηΔρ`
    // on the port's lattice, nearest.
    {
        let gamma = moved.modulus_slope.clone().unwrap();
        let curvature = moved.modulus_curvature.clone().unwrap();
        let unit = moved.modulus_unit.clone().unwrap();
        assert!(curvature.is_positive());
        assert!(!gamma.is_zero());
        assert_eq!(unit, -&gamma / &curvature);
        assert!((&gamma * &unit).is_negative());
        let last = moved.trials.last().unwrap();
        let lattice = theta
            .lattice(crate::hnn::constitution::Locus::SourcePort(0))
            .unwrap()
            .unit();
        let target = (rat(3, 4) + &last.step * &unit).max(rat(3, 8)).min(Rat::one());
        let carried = ((&target / &lattice) + rat(1, 2)).floor() * &lattice;
        assert_eq!(last.modulus.as_ref(), Some(&carried));
    }
    {
        let last = moved.trials.last().unwrap();
        assert!(last.refusal.is_none());
        let modulus = successor.transport(0);
        assert!(modulus.is_positive() && modulus <= Rat::one());
        // On this instance the modulus moves with `E`: the comparison falls with a newer
        // frontier (the carried modulus below `3/4`).
        assert_eq!(Some(&modulus), last.modulus.as_ref());
        assert!(modulus < rat(3, 4));
        let after = last.after.as_ref().unwrap();
        assert!(last.value.as_ref().unwrap().upper < moved.before.value.lower);
        assert!(last.first_order.as_ref().unwrap().upper.is_negative());
        assert!(after
            .requests
            .iter()
            .all(|r| r.generation.as_ref().unwrap().uncertified.is_none()));
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
    let material=ResonatorMaterial::of_parametron(&cycle(2),&rat(1,8),None).unwrap();
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
    let input=[vec![rat(1,2),Rat::zero(),Rat::zero(),Rat::zero()],
               vec![Rat::zero(),Rat::zero(),rat(1,4),Rat::zero()]];
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
