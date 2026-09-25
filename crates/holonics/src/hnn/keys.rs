//! **Keys lead learning: the data → menu map, key location per ring, and gauge fixing.**
//!
//! [definition] Learning is locating keys (Brandon, September 22; design Decision 10, (d) "Data →
//! menu"). A ring's key is its initial configuration, its clock at an aeon's opening. It is located
//! per ring, in carry order `g = 0, …, G−1`, from a crib of cells (at the port, the crib that
//! closed the previous aeon, carried to the boundary; below), with the existing [`Menu`],
//! [`Candidate`], [`crate::compression::Gauge`] and [`crate::compression::ReflectorMachine`] owners
//! and the new menu edges with their propagation ([`Menu::propagate`]):
//!
//! - **ports** are `ℤ/d_g`, and the port chart `port_g(x) = code(x) mod d_g` is known before any key;
//! - **edges**: every pair `(x_k, x_(k+δ))` of the crib at the declared offset `δ` is an edge
//!   `port_g(x_k) — port_g(x_(k+δ))`, labelled by its position `k` from the crib's opening. No
//!   admission depends on the key; a pair the machine does not carry shows as a failing loop;
//! - **one stage per edge**: the reflected return at the earlier cell's position,
//!   `stage(position(key_g, steps_g(k)))`, with `steps_g(k)` ring `g`'s ticks on the cells before
//!   `k`. By selective stepping it depends only on the cells, the locks and the earlier rings'
//!   configurations (through their carries), never on ring `g`'s own key (Lean
//!   `HNN/Moment.selective_position`), so the menu is evaluated per candidate and never fixed in
//!   advance;
//! - **candidates**: `key_g ∈ ℤ/d_g` with the plugboard images at the menu's ports; ring `g` is
//!   located under the earlier rings' published or fallen-back configurations, and a plural earlier
//!   fibre is not branched over;
//! - **the gauge**: the machine's rotor gauge `(k, s) ↦ (k + 1, ρ⁻¹ ∘ s)`, checked on the ring's own
//!   menu by [`crate::compression::Gauge::new`]. The fibre is a union of its orbits;
//! - **publication**: when the fibre is one orbit, its member with `S_g(p_0) = 0` at the least port
//!   `p_0` the menu visits is published. Exactly one member of each orbit satisfies it (Lean
//!   `HNN/Keys.gauge_fix_unique`). It is a declared symmetry-breaking convention (R3 K2), recorded in
//!   [`crate::hnn::Field::describe`], not a finding;
//! - **fallback**: an empty fibre (reported with its shortest failing loop) or a plural one leaves
//!   the ring at its current configuration;
//! - **re-keying** ([`KeyLocation::rekey`]) sets each published ring's phase class in `λ`, keeping
//!   its winding. It is never applied to a past cell: the open moment is untouched (R3 K1).
//!
//! [definition; agent-inferred] **The crib is already seen** (review D1). The port locates keys only
//! at an aeon boundary, from the crib that **closed** the aeon: the last cells the resident
//! ingested, which every compare has already read ([`locate_closing`]). Reading the cells that open
//! the next aeon would learn keys from cells later scored as targets. The configurations at the
//! crib's opening are the boundary's lift stepped back over the crib ([`crib_opening`]: ring `g`'s
//! advances over the crib depend only on the cells, the locks and the earlier rings' trajectories,
//! so they are recovered ring by ring). Each ring is located there as in [`locate_keys`], and a
//! published key is carried over the crib, under the configurations it was located with, to the
//! boundary where it re-keys `λ`. Before the first boundary no cell has been seen, so the rings run
//! on their declared initial configuration.
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Keys.contact_menu_closes`, `field_loop_fibre`; `Compression/Core/Keys.fibre_eq_bombe` | [`locate_ring`] |
//! | `HNN/Keys.propagation_eq_edge_fibre` | [`Menu::propagate`] |
//! | `HNN/Keys.gauge_fix_unique`; `Keys.Machine.rotorGauge`, `fibre_eq_orbit` | [`RingKeys::published`] |
//! | `HNN/Moment.selective_position` | [`ring_steps`], [`crib_opening`] |
//! | `HNN/Keys.rekey_keeps_winding` | [`KeyLocation::rekey`] |

use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

use crate::compression::{Candidate, Menu};
use crate::hnn::HnnError;
use crate::hnn::field::{Current, Field};
use crate::navigator::Clock;

/// [definition] **One ring's key location**: its menu's ports and edges, the fibre of consistent
/// candidates, the count of its gauge orbits, the published gauge-fixed key when the fibre is one
/// orbit (the ring's configuration at the crib's opening), that key carried to the lift point
/// where it is applied, the configuration the ring runs on at the crib's opening, whether it fell
/// back, the shortest failing loop (edge indices) when propagation met one, and the seeds and edge
/// traversals it took. Its fibre holds clocks as keyed candidates, the design's sanctioned
/// exception to guard 6 (design (d), "Candidates").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingKeys {
    pub ring: usize,
    pub menu_ports: Vec<usize>,
    pub edges: usize,
    pub fibre: Vec<Candidate<Clock>>,
    pub orbits: usize,
    pub published: Option<u64>,
    pub carried: Option<u64>,
    pub configuration: u64,
    pub fell_back: bool,
    pub failing_loop: Option<Vec<usize>>,
    pub seeds: u64,
    pub work: u64,
}

/// [definition] **Key location over the field**, per ring in carry order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyLocation {
    pub rings: Vec<RingKeys>,
}

impl KeyLocation {
    /// The configurations the rings run on, in carry order.
    pub fn configurations(&self) -> Vec<u64> {
        self.rings.iter().map(|ring| ring.configuration).collect()
    }

    /// **Re-key the lift point**: each ring with a published key takes its carried key as its
    /// phase class, keeping its winding; every other ring keeps its configuration. Returns each
    /// ring's jump in phase classes (zero where nothing was published).
    pub fn rekey(&self, field: &Field, current: &mut Current) -> Result<Vec<i64>, HnnError> {
        self.rings
            .iter()
            .map(|ring| match ring.carried {
                Some(key) => current.rekey(field, ring.ring, key),
                None => Ok(0),
            })
            .collect()
    }
}

/// **`steps_g(k)`**: ring `g`'s ticks on the crib's cells before cell `k`, from the aeon's opening
/// under the declared configurations (phase classes) of the rings before it. Ring `g`'s own and the
/// later rings' configurations do not enter.
pub fn ring_steps(
    field: &Field,
    ring: usize,
    crib: &[usize],
    configurations: &[u64],
) -> Result<Vec<u64>, HnnError> {
    if configurations.len() != field.rings().len() {
        return Err(HnnError::Shape {
            what: "ring configurations",
            expected: field.rings().len(),
            found: configurations.len(),
        });
    }
    let mut lift: Vec<BigInt> = configurations.iter().map(|c| BigInt::from(*c)).collect();
    let mut steps = Vec::with_capacity(crib.len());
    let mut taken = 0u64;
    for &code in crib {
        steps.push(taken);
        let step = field.selective_step(&mut lift, code)?;
        taken += u64::from(step.ticks[ring]);
    }
    Ok(steps)
}

/// **Ring `g`'s ticks over the whole crib** under the declared configurations of the rings before
/// it: `steps_g(W)`, the count [`ring_steps`] reaches after its last cell.
pub fn crib_ticks(
    field: &Field,
    ring: usize,
    crib: &[usize],
    configurations: &[u64],
) -> Result<u64, HnnError> {
    let mut lift: Vec<BigInt> = configurations.iter().map(|c| BigInt::from(*c)).collect();
    let mut taken = 0u64;
    for &code in crib {
        taken += u64::from(field.selective_step(&mut lift, code)?.ticks[ring]);
    }
    Ok(taken)
}

/// **The lift point at a crib's opening**: the lift `now`, reached by selective stepping over the
/// crib, stepped back over it. Ring `g`'s advance on a cell is its lock's fit plus the carry out of
/// ring `g − 1`, which ring `g − 1`'s recovered trajectory fixes, so the opening is recovered ring
/// by ring in carry order, exactly (Lean `HNN/Moment.selective_position`). Refused when a ring
/// would open below zero: the crib is not what reached `now`.
pub fn crib_opening(
    field: &Field,
    now: &[BigInt],
    crib: &[usize],
) -> Result<Vec<BigInt>, HnnError> {
    if now.len() != field.rings().len() {
        return Err(HnnError::Shape {
            what: "lift point",
            expected: field.rings().len(),
            found: now.len(),
        });
    }
    if let Some(&code) = crib.iter().find(|&&code| code >= field.alphabet()) {
        return Err(HnnError::CellOutside {
            code,
            alphabet: field.alphabet(),
        });
    }
    let mut carries = vec![0u64; crib.len()];
    let mut opening = Vec::with_capacity(now.len());
    for (g, ring) in field.rings().iter().enumerate() {
        let advances: Vec<u64> = crib
            .iter()
            .zip(&carries)
            .map(|(&code, carry)| u64::from(ring.fits(ring.port(code))) + carry)
            .collect();
        let start = &now[g] - BigInt::from(advances.iter().sum::<u64>());
        if start.sign() == num_bigint::Sign::Minus {
            return Err(HnnError::NegativeLift { ring: g });
        }
        let period = ring.period();
        let mut phase = (&start % BigInt::from(period))
            .to_u64()
            .expect("a nonnegative lift's phase lies below its period");
        for (carry, advance) in carries.iter_mut().zip(&advances) {
            *carry = u64::from(phase + advance >= period);
            phase = (phase + advance) % period;
        }
        opening.push(start);
    }
    Ok(opening)
}

/// **The data → menu map for one ring**: one edge per crib pair at the offset, its stage the
/// reflected return at the earlier cell's position.
pub fn crib_menu(
    field: &Field,
    ring: usize,
    crib: &[usize],
    offset: usize,
    configurations: &[u64],
) -> Result<Menu<Clock>, HnnError> {
    if offset == 0 || crib.len() <= offset {
        return Err(HnnError::Crib {
            cells: crib.len(),
            offset,
        });
    }
    let steps = ring_steps(field, ring, crib, configurations)?;
    let geometry = field.ring(ring);
    let machine = geometry.machine()?;
    let edges = (0..crib.len() - offset)
        .map(|k| {
            machine.edge_at(
                geometry.port(crib[k]),
                geometry.port(crib[k + offset]),
                BigUint::from(steps[k]),
            )
        })
        .collect();
    Ok(Menu::of_edges(geometry.placements().len(), edges)?)
}

/// The candidate keys of a ring: its navigator's clock at each phase class `0 … d_g − 1`.
pub fn candidate_keys(field: &Field, ring: usize) -> Result<Vec<Clock>, HnnError> {
    let declared = field.ring(ring);
    (0..declared.period())
        .map(|key| declared.clock_at(&BigInt::from(key)))
        .collect()
}

/// A candidate's key read as its phase class, with its images, so orbit members compare by class.
fn class(candidate: &Candidate<Clock>, period: u64) -> (u64, Vec<Option<usize>>) {
    let key = (candidate.key.ticks() % BigUint::from(period))
        .to_u64()
        .expect("a phase class lies below its period");
    let ports = candidate.images.ports();
    (
        key,
        (0..ports)
            .map(|port| candidate.images.image(port))
            .collect(),
    )
}

/// **Locate one ring's key** under the declared configurations of the rings before it, falling back
/// to `fallback` (its current configuration) unless the fibre is one gauge orbit.
pub fn locate_ring(
    field: &Field,
    ring: usize,
    crib: &[usize],
    offset: usize,
    configurations: &[u64],
    fallback: u64,
) -> Result<RingKeys, HnnError> {
    let menu = crib_menu(field, ring, crib, offset, configurations)?;
    let keys = candidate_keys(field, ring)?;
    let propagation = menu.propagate(&keys)?;
    let period = field.ring(ring).period();
    let gauge = field.ring(ring).machine()?.gauge(&menu, &keys)?;
    let menu_ports = menu.menu_ports();
    let classes: Vec<_> = propagation
        .candidates
        .iter()
        .map(|candidate| class(candidate, period))
        .collect();
    let mut assigned = vec![false; classes.len()];
    let mut orbits = 0;
    let mut one_orbit = !classes.is_empty();
    for start in 0..classes.len() {
        if assigned[start] {
            continue;
        }
        orbits += 1;
        let orbit = gauge.orbit(
            &propagation.candidates[start],
            usize::try_from(period).expect("a period fits"),
        )?;
        let mut members: Vec<_> = orbit.iter().map(|member| class(member, period)).collect();
        members.sort();
        members.dedup();
        for (index, known) in classes.iter().enumerate() {
            if members.contains(known) {
                assigned[index] = true;
            }
        }
        one_orbit &=
            members.len() == classes.len() && classes.iter().all(|known| members.contains(known));
    }
    let published = if one_orbit && orbits == 1 {
        let least = menu_ports[0];
        classes
            .iter()
            .filter(|(_, images)| images[least] == Some(0))
            .map(|(key, _)| *key)
            .next()
    } else {
        None
    };
    Ok(RingKeys {
        ring,
        menu_ports,
        edges: menu.edges().len(),
        fibre: propagation.candidates,
        orbits,
        published,
        carried: published,
        configuration: published.unwrap_or(fallback),
        fell_back: published.is_none(),
        failing_loop: propagation.failing_loop,
        seeds: propagation.seeds,
        work: propagation.work,
    })
}

/// **Locate every ring's key** at a crib's opening (the lift `current`), per ring in carry order:
/// ring `g` is located under the published or fallen-back configurations of rings `0 … g−1`, and a
/// ring whose fibre is not one orbit keeps the current configuration.
pub fn locate_keys(
    field: &Field,
    current: &Current,
    crib: &[usize],
    offset: usize,
) -> Result<KeyLocation, HnnError> {
    let mut configurations: Vec<u64> = (0..field.rings().len())
        .map(|ring| current.phase(field, ring))
        .collect::<Result<_, _>>()?;
    let mut rings = Vec::with_capacity(configurations.len());
    for ring in 0..field.rings().len() {
        let located = locate_ring(
            field,
            ring,
            crib,
            offset,
            &configurations,
            configurations[ring],
        )?;
        configurations[ring] = located.configuration;
        rings.push(located);
    }
    Ok(KeyLocation { rings })
}

/// **Locate every ring's key from the crib that closed an aeon** (module header, review D1): the
/// crib is the last cells the resident ingested before `current`, already seen. The rings are
/// located at the crib's opening ([`crib_opening`], then [`locate_keys`]); each published key is
/// then carried over the crib, under the configurations it was located with, to `current`, where
/// [`KeyLocation::rekey`] applies it.
pub fn locate_closing(
    field: &Field,
    current: &Current,
    crib: &[usize],
    offset: usize,
) -> Result<KeyLocation, HnnError> {
    let opening = Current::at(field, crib_opening(field, current.lift(), crib)?)?;
    let mut location = locate_keys(field, &opening, crib, offset)?;
    let configurations = location.configurations();
    for ring in &mut location.rings {
        ring.carried = match ring.published {
            Some(key) => {
                let period = field.ring(ring.ring).period();
                let ticks = crib_ticks(field, ring.ring, crib, &configurations)?;
                Some((key + ticks % period) % period)
            }
            None => None,
        };
    }
    Ok(location)
}
