//! **The turn machine: a menu whose stages are the rotor's turns, read by the holonomy of its
//! loops** (lane B of THE_REBUILD U6 step 1, the library spine's S2; the
//! [record](../../../../../research/records/2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md)).
//!
//! [definition; agent-inferred, October 5] The reflector machine's stage moves with its rotor between
//! two readings ([`super::ReflectorMachine`]), so a stationary relation between two readings fails
//! every loop of it. A ring's stationary transports are its rotor's own turns `ρ^c`, `c ∈ ℤ/d`, and
//! a **turn menu** reads each edge `u → v` as `S(v) = S(u) + c` for the boundary images `S` at the
//! menu's ports, injective (the diagonal board). It is the Bombe's loop closure with the turn as the
//! stage: a closed walk `ℓ` closes exactly when its turns sum to zero, `Σ_(uv ∈ ℓ) ± c ≡ 0 (mod d)`,
//! the cell holonomy of a `ℤ/d` connection on the menu. Its multiplicative chart at `d = 2`, with a
//! turn `s_ij` read on each contact, is the sheet law `∏_(ij ∈ ℓ) σ_i σ_j s_ij = 1` up to the global
//! half-turn; here one unknown turn is shared by every edge and the images are injective.
//!
//! Every turn commutes with the rotor, so the rotor gauge `S ↦ ρ^k ∘ S` keeps each turn, and the
//! reflector's gauge `(c, S) ↦ (−c, F ∘ S)` pairs `c` with `−c`: the fibre's gauge-invariant reading
//! is the **menu relation** `R` (each port's consequence), and the surviving turns are read from
//! its components [proved-derived; Lean owed, #62; held to the brute-force fibre of [`super::Menu`]
//! by the owner's test]:
//!
//! - `R` must be a partial injection: two consequences of one port force `S(v) = S(v')`, two
//!   antecedents of one port `S(u) = S(u')` (a failing loop of two edges);
//! - a cycle of `R` of length `k` closes exactly when `k c ≡ 0` and its ports stay apart exactly
//!   when `j c ≢ 0` for `0 < j < k`, so every cycle has length `ord(c) = d/gcd(c, d)`;
//! - a path of `p` edges keeps its `p + 1` ports apart exactly when `ord(c) > p`;
//! - the components take disjoint images: each cycle a whole coset of `⟨c⟩`, the paths' runs packed
//!   into the cosets left, each of `ord(c)` slots.
//!
//! The map is **published** when every menu port has its consequence (`R` a permutation of the menu
//! ports) and some turn survives: then every surviving candidate reads `R` at every menu port.
//! Publication reads only consequences that were read: a port whose consequence was not read is
//! left plural, even where the surviving turns force it (a path of `ord(c) − 1` edges closes by the
//! turn; runs that tile a coset abut), so a published map is always the survivors' common reading
//! and never more.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | the turn menu's fibre read from the relation's components, up to the rotor gauge | owed (#62) | [`TurnMenu::reading`] |
//! | a failed menu stays failed | `Keys.fibre_cons` | [`TurnMenu::observe`] |

/// [definition] **A turn menu** (module header) on a ring of period `d`: the read relation `R`, its
/// edges and its first failing pair.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TurnMenu {
    period: u64,
    image: Vec<Option<usize>>,
    source: Vec<Option<usize>>,
    edges: u64,
    failing: Option<[(usize, usize); 2]>,
}

/// [definition] **A turn menu's reading**: the surviving turns `c` (empty when the menu failed),
/// the cycles' common length when `R` has a cycle, the published map (`R` on its menu ports, when
/// it is total there), and the edges read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TurnReading {
    pub turns: Vec<u64>,
    pub cycle: Option<u64>,
    pub map: Option<Vec<(usize, usize)>>,
    pub edges: u64,
}

impl TurnMenu {
    /// An empty menu on a ring of period `d`: no edge read, every turn alive.
    pub fn open(period: u64) -> Self {
        let ports = usize::try_from(period).expect("a period fits");
        Self {
            period,
            image: vec![None; ports],
            source: vec![None; ports],
            edges: 0,
            failing: None,
        }
    }

    /// Whether the menu still admits a partial injection (no failing loop of two edges met).
    pub fn alive(&self) -> bool {
        self.failing.is_none()
    }

    /// The first failing pair of edges (two consequences of one port, or two antecedents of one
    /// port), when one was met.
    pub fn failing(&self) -> Option<&[(usize, usize); 2]> {
        self.failing.as_ref()
    }

    /// The edges read.
    pub fn edges(&self) -> u64 {
        self.edges
    }

    /// **Read one edge** `from → to`. An edge that repeats a read one changes nothing; one that gives
    /// a port a second consequence or a second antecedent fails the menu (kept with its witness).
    /// Adding an edge only shrinks the fibre (Lean `Keys.fibre_cons`): a failed menu stays failed.
    pub fn observe(&mut self, from: usize, to: usize) {
        self.edges += 1;
        if self.failing.is_some() {
            return;
        }
        match (self.image[from], self.source[to]) {
            (Some(known), _) if known != to => {
                self.failing = Some([(from, known), (from, to)]);
            }
            (_, Some(known)) if known != from => {
                self.failing = Some([(known, to), (from, to)]);
            }
            _ => {
                self.image[from] = Some(to);
                self.source[to] = Some(from);
            }
        }
    }

    /// The menu's ports: every port an edge reached, sorted.
    pub fn menu_ports(&self) -> Vec<usize> {
        (0..self.image.len())
            .filter(|&port| self.image[port].is_some() || self.source[port].is_some())
            .collect()
    }

    /// `R`'s components: the cycles' lengths and the paths' edge counts.
    fn components(&self) -> (Vec<u64>, Vec<u64>) {
        let ports = self.menu_ports();
        let mut seen = vec![false; self.image.len()];
        let (mut cycles, mut paths) = (Vec::new(), Vec::new());
        // Paths start at a port with no antecedent.
        for &start in &ports {
            if self.source[start].is_some() {
                continue;
            }
            let (mut port, mut edges) = (start, 0u64);
            seen[port] = true;
            while let Some(next) = self.image[port] {
                port = next;
                seen[port] = true;
                edges += 1;
            }
            paths.push(edges);
        }
        // Every port left lies on a cycle.
        for &start in &ports {
            if seen[start] {
                continue;
            }
            let (mut port, mut length) = (start, 0u64);
            loop {
                seen[port] = true;
                length += 1;
                port = self.image[port].expect("a port on a cycle has its consequence");
                if port == start {
                    break;
                }
            }
            cycles.push(length);
        }
        (cycles, paths)
    }

    /// Whether the turn `c` survives the menu (the type's header): every cycle of length `ord(c)`,
    /// every path shorter, and the components packed into disjoint cosets of `⟨c⟩`.
    fn admits(&self, turn: u64, cycles: &[u64], paths: &[u64]) -> bool {
        let order = self.period / gcd(turn % self.period, self.period);
        if cycles.iter().any(|&length| length != order) || paths.iter().any(|&p| p >= order) {
            return false;
        }
        let cosets = self.period / order;
        let Some(free) = cosets.checked_sub(cycles.len() as u64) else {
            return false;
        };
        let mut runs: Vec<u64> = paths.iter().map(|p| p + 1).collect();
        runs.sort_unstable_by(|a, b| b.cmp(a));
        packs(&runs, &mut vec![order; usize::try_from(free).expect("a coset count fits")])
    }

    /// **The menu's reading** (the type's header).
    pub fn reading(&self) -> TurnReading {
        if self.failing.is_some() {
            return TurnReading {
                turns: Vec::new(),
                cycle: None,
                map: None,
                edges: self.edges,
            };
        }
        let (cycles, paths) = self.components();
        let turns: Vec<u64> = (0..self.period)
            .filter(|&turn| self.admits(turn, &cycles, &paths))
            .collect();
        let ports = self.menu_ports();
        let map = (!turns.is_empty() && !ports.is_empty() && paths.is_empty()).then(|| {
            ports
                .iter()
                .map(|&port| (port, self.image[port].expect("a cycle port's consequence")))
                .collect()
        });
        TurnReading {
            turns,
            cycle: cycles.first().copied(),
            map,
            edges: self.edges,
        }
    }
}

/// Whether the runs pack into the bins (each run within one bin's free slots), by exact search
/// over the runs in decreasing order (the menu ports are few: the search is over at most their
/// count).
fn packs(runs: &[u64], bins: &mut [u64]) -> bool {
    let Some((&run, rest)) = runs.split_first() else {
        return true;
    };
    for index in 0..bins.len() {
        // Bins with equal free slots are interchangeable: try the first of each.
        if bins[..index].contains(&bins[index]) || bins[index] < run {
            continue;
        }
        bins[index] -= run;
        let fits = packs(rest, bins);
        bins[index] += run;
        if fits {
            return true;
        }
    }
    false
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compression::{Edge, Menu};
    use crate::holarchy::terrain::Draw;
    use crate::holon::contact::menu::PortPermutation;

    /// The turn `c` on `ℤ/d`: `p ↦ p + c`.
    fn turn(period: usize, c: usize) -> PortPermutation {
        PortPermutation::new((0..period).map(|p| (p + c) % period).collect()).unwrap()
    }

    /// The brute-force fibre of a menu of turn stages (the existing owner [`Menu`], every injective
    /// image of the menu's ports, each edge read by [`Edge::holds`]): the surviving turns, and the
    /// gauge-invariant map when every survivor reads the same consequence at every menu port.
    #[allow(clippy::type_complexity)]
    fn turn_fibre(period: usize, edges: &[(usize, usize)]) -> (Vec<u64>, Option<Vec<(usize, usize)>>) {
        let menu = Menu::of_edges(
            period,
            edges
                .iter()
                .map(|&(from, to)| Edge::new(from, to, move |c: &usize| Ok(turn(period, *c))))
                .collect(),
        )
        .unwrap();
        let keys: Vec<usize> = (0..period).collect();
        let ports = menu.menu_ports();
        let mut turns = Vec::new();
        let mut maps = Vec::new();
        for candidate in menu.candidates(&keys).unwrap() {
            if !menu.edges().iter().all(|edge| edge.holds(&candidate).unwrap()) {
                continue;
            }
            turns.push(candidate.key as u64);
            let map: Vec<Option<(usize, usize)>> = ports
                .iter()
                .map(|&port| {
                    let image = (candidate.images.image(port).unwrap() + candidate.key) % period;
                    ports
                        .iter()
                        .find(|&&other| candidate.images.image(other) == Some(image))
                        .map(|&other| (port, other))
                })
                .collect();
            maps.push(map);
        }
        turns.sort_unstable();
        turns.dedup();
        let published = match maps.split_first() {
            Some((first, rest))
                if first.iter().all(Option::is_some) && rest.iter().all(|m| m == first) =>
            {
                Some(first.iter().map(|entry| entry.unwrap()).collect())
            }
            _ => None,
        };
        (turns, published)
    }

    /// [implemented-exact] **The turn menu's reading equals the brute-force fibre** of the menu
    /// owner on every drawn menu of up to four edges over four ports of a ring of period 6 or 8: the
    /// surviving turns read from the relation's components (cycles of length `ord(c)`, shorter
    /// paths, disjoint cosets) are exactly the keys of the injective images that satisfy every
    /// edge, and a published map is exactly the consequence every survivor reads at every menu port.
    #[test]
    fn the_turn_menu_equals_the_brute_force_fibre() {
        let mut draw = Draw::new(2_026_100_501);
        let mut published_count = 0;
        for period in [6usize, 8] {
            for trial in 0..120 {
                let count = 1 + trial % 4;
                let edges: Vec<(usize, usize)> = (0..count)
                    .map(|_| (draw.below(4), draw.below(4)))
                    .collect();
                let mut menu = TurnMenu::open(period as u64);
                for &(from, to) in &edges {
                    menu.observe(from, to);
                }
                let reading = menu.reading();
                let (turns, map) = turn_fibre(period, &edges);
                assert_eq!(reading.turns, turns, "period {period}, edges {edges:?}");
                // Publication reads only consequences that were read: a published map is the one
                // every survivor reads; a path's end that the surviving turns force closed is left
                // plural.
                if let Some(published) = &reading.map {
                    assert_eq!(Some(published), map.as_ref(), "period {period}, edges {edges:?}");
                    published_count += 1;
                }
            }
        }
        assert!(published_count > 0);
    }

    /// [implemented-exact] **A failed menu stays failed** (adding an edge only shrinks the fibre,
    /// Lean `Keys.fibre_cons`): two consequences of one port fail it with their witness, and no
    /// later edge revives it.
    #[test]
    fn a_failed_turn_menu_stays_failed() {
        let mut menu = TurnMenu::open(8);
        menu.observe(0, 1);
        menu.observe(0, 2);
        assert!(!menu.alive());
        assert_eq!(menu.failing(), Some(&[(0, 1), (0, 2)]));
        menu.observe(1, 2);
        assert!(!menu.alive());
        assert!(menu.reading().turns.is_empty());
        assert_eq!(menu.edges(), 3);
    }

    /// [implemented-exact] **A 4-cycle on a ring of period 60 survives exactly the turns of order
    /// 4**, `15` and `45`, and publishes its relation; a self-loop admits only the turn `0`.
    #[test]
    fn a_four_cycle_keeps_the_turns_of_order_four() {
        let mut menu = TurnMenu::open(60);
        for (from, to) in [(0, 1), (1, 2), (2, 3), (3, 0)] {
            menu.observe(from, to);
        }
        let reading = menu.reading();
        assert_eq!(reading.turns, vec![15, 45]);
        assert_eq!(reading.cycle, Some(4));
        assert_eq!(reading.map, Some(vec![(0, 1), (1, 2), (2, 3), (3, 0)]));
        let mut fixed = TurnMenu::open(60);
        fixed.observe(2, 2);
        assert_eq!(fixed.reading().turns, vec![0]);
    }
}
