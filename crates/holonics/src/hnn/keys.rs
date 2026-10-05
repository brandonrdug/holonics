//! **Keys lead learning: the data → menu map, key location per ring, and gauge fixing.**
//!
//! [definition] Learning is locating keys (Brandon, September 22; THE_REBUILD's design (d), "Data →
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
//! [definition; agent-inferred, October 5; the
//! [record](../../../../research/records/2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md)]
//! **The pair menu over the span's distances, and the turn machine** (lane B of U6 step 1). The
//! reflector machine's stage moves with the rotor between two readings, so a stationary relation
//! between a station and an earlier cell of its span fails every loop of it. The ring's own
//! stationary transports are its rotor's turns `ρ^c`, and the **turn machine** (its library owner
//! `compression::keys::TurnMenu`, the library spine's S2) reads an edge `u → v` as
//! `S(v) = S(u) + c`: the rotor gauge keeps every turn, so the fibre's gauge-invariant reading is
//! the menu relation itself, and the surviving turns are read from its components (cycles of length
//! `ord(c)`, shorter paths, disjoint cosets). This module keeps the boundary adapter: the data → menu map
//! reads each seen station against every earlier cell of its passage at every distance below the
//! period ([`station_pairs`]); no distance is declared, and [`PairLocation`] keeps one turn menu a
//! distance and locates the pair when the read distances that survive are the windings of the
//! least one ([`LocatedPair`]; one surviving distance is its own only winding). The crib is seen
//! cells only: a request and the stations already read. Its consumer is
//! `hnn::executed::pair_deposit`, which makes the located pair the source port's pair component,
//! `(E − B) T = P^δ B` on the menu's classes.
//!
//! [definition; agent-inferred, October 5; the
//! [regressions record](../../../../research/records/2026-10-05_THE_REGRESSIONS_LOCATE_THE_LEAST_WINDING_AND_ARE_READ_BY_THE_PAIR_RELEASE.md)]
//! **A class of windings is one key.** Contacts compose along the ring's clock: `k` contacts at
//! `δ₀`, each `y ↦ f₀(y)`, joined end to end, are one contact at `k δ₀` with the map `f₀^k`, and its
//! holonomy is the sum of theirs (`Σ c = k c₀`). When every surviving distance is such a winding of
//! the least survivor, `δ = k δ₀` with its published map `f₀^k` on its ports, the survivors are one
//! cyclic family and its generator `(δ₀, f₀)` is the key; each winding adds no reading the generator
//! lacks on the passage, so retention (a quotient sufficient for the admitted future) keeps the
//! generator alone. The alternation's even distances `2k` with the identity and the line's `4k`
//! with the identity are such families; a plural survivor set with any distance that is not a
//! winding of the least (two coprime distances, or a map other than `f₀^k`) stays plural, never a
//! key.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Keys.fibre_cons` (a distance's menu only shrinks; the turn menu's law is `compression::keys::TurnMenu`'s) | [`PairLocation::observe`] |
//! | `HNN/Keys.contact_menu_closes`, `field_loop_fibre`; `Compression/Core/Keys.fibre_eq_bombe` | [`locate_ring`] |
//! | `HNN/Keys.propagation_eq_edge_fibre` | [`Menu::propagate`] |
//! | `HNN/Keys.gauge_fix_unique`; `Keys.Machine.rotorGauge`, `fibre_eq_orbit` | [`RingKeys::published`] |
//! | `HNN/Moment.selective_position` | [`ring_steps`], [`crib_opening`] |
//! | `HNN/Keys.rekey_keeps_winding` | [`KeyLocation::rekey`] |

use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

use crate::compression::{Candidate, Menu, TurnMenu, TurnReading};
use crate::hnn::HnnError;
use crate::hnn::field::{Current, Field, ring_digit};
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
        // The carries ring `g` sends are its clock's jumps over its advances (`Ring::clock_at`).
        let mut clock = ring.clock_at(&start)?;
        for (carry, advance) in carries.iter_mut().zip(&advances) {
            *carry = clock.advance(&BigUint::from(*advance)).to_u64().expect(
                "a ring of period at least 2 advanced at most two ticks jumps at most once",
            );
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
                // The key carried over the crib: the ring's clock at the key advanced by the
                // crib's ticks, read as its phase class.
                let ticks = crib_ticks(field, ring.ring, crib, &configurations)?;
                let mut clock = field.ring(ring.ring).clock_at(&BigInt::from(key))?;
                clock.advance(&BigUint::from(ticks));
                Some(ring_digit(&clock))
            }
            None => None,
        };
    }
    Ok(location)
}

// -------------------------------------------------------------------------------------------
// the pair menu over the span's distances, and the turn machine

/// [definition; agent-inferred, October 5] **A pair reading**: a seen station's cell read against
/// an earlier cell of its span at the tick distance `offset` on the source ring, as the menu edge
/// `from = port(x_(t−δ)) → to = port(x_t)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PairReading {
    pub offset: usize,
    pub from: usize,
    pub to: usize,
}

/// **The data → menu map at every distance of the span** (module section "The pair menu"): for a
/// seen passage (a request and the stations that continued it, every cell already read) and the
/// index `opening` of its first station, each station `t ≥ opening` is one observation, read
/// against every earlier cell of its passage at its distance `δ = t − s ∈ [1, t]`, held below the
/// ring's period so each distance is one residue of the ring's clock. No distance is selected: the
/// survivors decide. Refused when the passage holds a cell outside the exterior chart or opens no
/// station.
pub fn station_pairs(
    field: &Field,
    ring: usize,
    passage: &[usize],
    opening: usize,
) -> Result<Vec<Vec<PairReading>>, HnnError> {
    if let Some(&code) = passage.iter().find(|&&code| code >= field.alphabet()) {
        return Err(HnnError::CellOutside {
            code,
            alphabet: field.alphabet(),
        });
    }
    if opening == 0 || opening > passage.len() {
        return Err(HnnError::Crib {
            cells: passage.len(),
            offset: opening,
        });
    }
    let geometry = field.ring(ring);
    let period = usize::try_from(geometry.period()).expect("a period fits");
    Ok((opening..passage.len())
        .map(|t| {
            (1..=t.min(period - 1))
                .map(|offset| PairReading {
                    offset,
                    from: geometry.port(passage[t - offset]),
                    to: geometry.port(passage[t]),
                })
                .collect()
        })
        .collect())
}

/// [definition; agent-inferred, October 5] **A located pair**: the generator of the surviving
/// distances (the one survivor, or the least survivor when every other is its winding; module
/// section "A class of windings is one key"), its published map on its menu ports, its cycles'
/// length and the surviving turns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocatedPair {
    pub offset: usize,
    pub map: Vec<(usize, usize)>,
    pub cycle: u64,
    pub turns: Vec<u64>,
}

/// [definition; agent-inferred, October 5] **Pair location over the span's distances**: one turn
/// menu per distance `δ ∈ [1, d − 1]`, each observation (a seen station) reading its edge at every
/// distance its span reaches ([`station_pairs`]). A distance whose menu read no edge is unread, not
/// a survivor. The pair is **located** when the least surviving distance has its map published
/// ([`TurnMenu`]) and every other survivor is its winding (`δ = k δ₀`, map `f₀^k`); several surviving
/// distances that are not one family of windings are a plural class, never a key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairLocation {
    menus: Vec<TurnMenu>,
    observations: u64,
}

/// [definition] **The survivors after an observation**: each read distance still alive with its
/// reading, and the observations read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairSurvivors {
    pub observations: u64,
    pub alive: Vec<(usize, TurnReading)>,
    pub read: usize,
}

impl PairSurvivors {
    /// **The located pair**: the least surviving distance `δ₀` with its published map `f₀`, when
    /// every other survivor `δ` is its winding: `δ = k δ₀` and its published map is `f₀^k` on its
    /// ports (module section "A class of windings is one key"). One survivor is located alone.
    pub fn located(&self) -> Option<LocatedPair> {
        let ((least, generator), others) = self.alive.split_first()?;
        let map = generator.map.clone()?;
        let image = |port: usize| map.iter().find(|(from, _)| *from == port).map(|(_, to)| *to);
        let wound = others.iter().all(|(offset, reading)| {
            offset % least == 0
                && reading.map.as_ref().is_some_and(|pairs| {
                    pairs.iter().all(|&(from, to)| {
                        (0..offset / least).try_fold(from, |port, _| image(port)) == Some(to)
                    })
                })
        });
        if !wound {
            return None;
        }
        Some(LocatedPair {
            offset: *least,
            cycle: generator.cycle?,
            turns: generator.turns.clone(),
            map,
        })
    }

    /// The surviving distances with a nonempty turn set.
    pub fn distances(&self) -> Vec<usize> {
        self.alive.iter().map(|(offset, _)| *offset).collect()
    }
}

impl PairLocation {
    /// The location opened on a source ring: every distance's menu empty.
    pub fn open(field: &Field, ring: usize) -> Self {
        let period = field.ring(ring).period();
        Self {
            menus: (1..period).map(|_| TurnMenu::open(period)).collect(),
            observations: 0,
        }
    }

    /// **Read one observation**: its edge at every distance it reaches.
    pub fn observe(&mut self, readings: &[PairReading]) {
        self.observations += 1;
        for reading in readings {
            self.menus[reading.offset - 1].observe(reading.from, reading.to);
        }
    }

    /// The menu at a distance.
    pub fn menu(&self, offset: usize) -> &TurnMenu {
        &self.menus[offset - 1]
    }

    /// **The survivors**: each read distance whose menu admits a turn.
    pub fn survivors(&self) -> PairSurvivors {
        let read: Vec<(usize, &TurnMenu)> = self
            .menus
            .iter()
            .enumerate()
            .filter(|(_, menu)| menu.edges() > 0)
            .map(|(index, menu)| (index + 1, menu))
            .collect();
        PairSurvivors {
            observations: self.observations,
            read: read.len(),
            alive: read
                .into_iter()
                .filter(|(_, menu)| menu.alive())
                .map(|(offset, menu)| (offset, menu.reading()))
                .filter(|(_, reading)| !reading.turns.is_empty())
                .collect(),
        }
    }
}
