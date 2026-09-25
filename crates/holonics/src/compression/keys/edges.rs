//! **Menu edges and propagation: the Bombe's diagonal board over the open paths of a menu.**
//!
//! [definition] Addition 7 of the step-4 design ([THE_REBUILD](../../../../../docs/plans/THE_REBUILD.md),
//! "The additions outside `hnn`"). An [`Edge`] is a one-stage open path of a [`Menu`]: two ports
//! and, per key, a stage `W_k` read as `S(to) = W_k S(from)`. The stage is an involution, so the
//! edge is traversed either way, `S(from) = W_k S(to)`; a stage that is not an involution is
//! refused with its edge and key. A [`super::Loop`] is a closed path of edges.
//!
//! [definition] **`propagate(keys)`.** For each key and each image of one seed port per connected
//! component of the menu's edge graph, it sets `S(v) = W_k S(u)` along the edges, refusing a
//! conflict (an edge whose two ends disagree: a failing loop) or a repeated image (the diagonal
//! board's injectivity). Components join by disjoint images, and any loops of the menu must then
//! close. Its work is `keys × d × edges` edge traversals, against `keys × d!/(d − m)!` candidates
//! for enumeration.
//!
//! ```text
//! survivors = { (k, s) : s injective on the menu ports, s(to) = W_k s(from) for every edge }     the edge fibre
//! ```
//!
//! [implemented-exact; formal for one component] Its law: the survivors are exactly the candidates
//! whose images satisfy every edge. Lean `HNN/Keys.propagation_eq_edge_fibre` proves it for one
//! component from one seed; the join of components by disjoint images, and its equality with the
//! fundamental-cycle fibre, are owed (#62), and the brute-force tests below check them. On one
//! component, an assignment satisfying the edges is fixed by its seed image (each
//! reached port's image is forced along a path), so propagating from every seed image of every
//! component enumerates the fibre without enumerating the images. The tests compare it with the
//! brute-force filter of [`Menu::candidates`] on every menu below the image ceiling.

use std::rc::Rc;

use super::{Candidate, Menu, PortImages};
use crate::compression::CompressionError;
use crate::holon::contact::menu::{MenuError, PortPermutation};

/// [definition] **A menu edge**: a one-stage open path `from — to`, whose stage under each key is
/// read as `S(to) = W_k S(from)`.
pub struct Edge<Key> {
    from: usize,
    to: usize,
    stage: Rc<dyn Fn(&Key) -> Result<PortPermutation, MenuError>>,
}

impl<Key> std::fmt::Debug for Edge<Key> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Edge")
            .field("from", &self.from)
            .field("to", &self.to)
            .finish_non_exhaustive()
    }
}

impl<Key> Edge<Key> {
    /// The edge `from — to` whose stage under each key is `stage(key)`.
    pub fn new(
        from: usize,
        to: usize,
        stage: impl Fn(&Key) -> Result<PortPermutation, MenuError> + 'static,
    ) -> Self {
        Self {
            from,
            to,
            stage: Rc::new(stage),
        }
    }

    /// The earlier port.
    pub fn from(&self) -> usize {
        self.from
    }

    /// The later port.
    pub fn to(&self) -> usize {
        self.to
    }

    /// The stage under a key.
    pub fn stage(&self, key: &Key) -> Result<PortPermutation, MenuError> {
        (self.stage)(key)
    }

    /// **Whether a candidate satisfies the edge**: `S(to) = W_k S(from)`. Both ports must carry an
    /// image.
    pub fn holds(&self, candidate: &Candidate<Key>) -> Result<bool, CompressionError> {
        let image = |port: usize| {
            candidate
                .images
                .image(port)
                .ok_or(CompressionError::MissingImage { port })
        };
        let (from, to) = (image(self.from)?, image(self.to)?);
        Ok(self.stage(&candidate.key)?.apply(from)? == to)
    }
}

/// [definition] **What propagation returns**: the surviving candidates (the edge fibre), the edge
/// traversals it performed, the seeds it tried, and the shortest failing loop it met (a closed walk
/// of edge indices through a component's seed), when any seed was refused by a conflict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Propagation<Key> {
    pub candidates: Vec<Candidate<Key>>,
    pub work: u64,
    pub seeds: u64,
    pub failing_loop: Option<Vec<usize>>,
}

impl<Key: Clone> Menu<Key> {
    /// **Propagation over the menu's edges** (addition 7): the candidates over `keys` whose images
    /// at the menu ports are injective, satisfy every edge and close every loop, found by setting
    /// `S(v) = W_k S(u)` from one seed image per component. See the module header for its law and
    /// work.
    pub fn propagate(&self, keys: &[Key]) -> Result<Propagation<Key>, CompressionError> {
        let ports = self.menu_ports();
        let components = self.components(&ports);
        // The undirected adjacency: (neighbour, edge index, traversed forward).
        let mut adjacency: Vec<Vec<(usize, usize, bool)>> = vec![Vec::new(); self.ports];
        for (index, edge) in self.edges.iter().enumerate() {
            adjacency[edge.from()].push((edge.to(), index, true));
            adjacency[edge.to()].push((edge.from(), index, false));
        }
        let mut result = Propagation {
            candidates: Vec::new(),
            work: 0,
            seeds: 0,
            failing_loop: None,
        };
        for (key_index, key) in keys.iter().enumerate() {
            let stages = self
                .edges
                .iter()
                .enumerate()
                .map(|(edge, current)| {
                    let stage = current.stage(key)?;
                    if stage.multiply(&stage)? != PortPermutation::identity(stage.ports()) {
                        return Err(CompressionError::StageNotInvolution { edge, key_index });
                    }
                    Ok(stage)
                })
                .collect::<Result<Vec<_>, CompressionError>>()?;
            // Each component's surviving assignments, as (port, image) lists.
            let mut joined: Vec<Vec<(usize, usize)>> = vec![Vec::new()];
            for component in &components {
                let mut survivors = Vec::new();
                for seed_image in 0..self.ports {
                    result.seeds += 1;
                    match self.propagate_seed(
                        &adjacency,
                        &stages,
                        component[0],
                        seed_image,
                        &mut result.work,
                    )? {
                        Ok(assignment) => survivors.push(assignment),
                        Err(Some(failing)) => {
                            let shorter = result
                                .failing_loop
                                .as_ref()
                                .is_none_or(|known| failing.len() < known.len());
                            if shorter {
                                result.failing_loop = Some(failing);
                            }
                        }
                        Err(None) => {}
                    }
                }
                joined = joined
                    .iter()
                    .flat_map(|earlier| {
                        survivors.iter().filter_map(move |later| {
                            let disjoint = later
                                .iter()
                                .all(|(_, image)| earlier.iter().all(|(_, known)| known != image));
                            disjoint.then(|| {
                                let mut both = earlier.clone();
                                both.extend(later.iter().copied());
                                both
                            })
                        })
                    })
                    .collect();
            }
            for assignment in joined {
                let candidate = Candidate {
                    key: key.clone(),
                    images: PortImages::new(self.ports, assignment)?,
                };
                let mut closes = true;
                for current in &self.loops {
                    closes &= current.closes(&candidate)?;
                }
                if closes {
                    result.candidates.push(candidate);
                }
            }
        }
        Ok(result)
    }

    /// The connected components of the edge graph on the menu ports, each sorted, in order of
    /// their least port.
    fn components(&self, ports: &[usize]) -> Vec<Vec<usize>> {
        let mut component_of: Vec<Option<usize>> = vec![None; self.ports];
        let mut components: Vec<Vec<usize>> = Vec::new();
        for &start in ports {
            if component_of[start].is_some() {
                continue;
            }
            let index = components.len();
            let mut members = vec![start];
            component_of[start] = Some(index);
            let mut cursor = 0;
            while cursor < members.len() {
                let port = members[cursor];
                cursor += 1;
                for edge in &self.edges {
                    for (here, there) in [(edge.from(), edge.to()), (edge.to(), edge.from())] {
                        if here == port && component_of[there].is_none() {
                            component_of[there] = Some(index);
                            members.push(there);
                        }
                    }
                }
            }
            members.sort_unstable();
            components.push(members);
        }
        components
    }

    /// One seed's propagation through its component. The inner `Err(Some(walk))` is a conflict,
    /// with the closed walk (edge indices) that witnesses it; `Err(None)` is a repeated image.
    #[allow(clippy::type_complexity)]
    fn propagate_seed(
        &self,
        adjacency: &[Vec<(usize, usize, bool)>],
        stages: &[PortPermutation],
        seed: usize,
        seed_image: usize,
        work: &mut u64,
    ) -> Result<Result<Vec<(usize, usize)>, Option<Vec<usize>>>, CompressionError> {
        let mut image: Vec<Option<usize>> = vec![None; self.ports];
        // The tree edge that first reached each port, for the failing loop's walk.
        let mut parent: Vec<Option<(usize, usize)>> = vec![None; self.ports];
        image[seed] = Some(seed_image);
        let mut reached = vec![seed];
        let mut cursor = 0;
        while cursor < reached.len() {
            let here = reached[cursor];
            cursor += 1;
            let here_image = image[here].expect("a reached port carries its image");
            for &(there, edge, _) in &adjacency[here] {
                *work += 1;
                // The stage is an involution, so the same permutation carries either direction.
                let forced = stages[edge].apply(here_image)?;
                match image[there] {
                    Some(known) if known == forced => {}
                    Some(_) => {
                        let mut walk = path_to_seed(&parent, here);
                        walk.reverse();
                        walk.push(edge);
                        walk.extend(path_to_seed(&parent, there));
                        return Ok(Err(Some(walk)));
                    }
                    None => {
                        image[there] = Some(forced);
                        parent[there] = Some((here, edge));
                        reached.push(there);
                    }
                }
            }
        }
        let mut assignment: Vec<(usize, usize)> = reached
            .iter()
            .map(|port| (*port, image[*port].expect("reached")))
            .collect();
        assignment.sort_unstable();
        let mut images: Vec<usize> = assignment.iter().map(|(_, image)| *image).collect();
        images.sort_unstable();
        images.dedup();
        if images.len() != assignment.len() {
            return Ok(Err(None));
        }
        Ok(Ok(assignment))
    }
}

/// The tree edges from a port back to its component's seed.
fn path_to_seed(parent: &[Option<(usize, usize)>], mut port: usize) -> Vec<usize> {
    let mut walk = Vec::new();
    while let Some((previous, edge)) = parent[port] {
        walk.push(edge);
        port = previous;
    }
    walk
}

#[cfg(test)]
mod tests {
    use super::*;

    /// SplitMix64, for deterministic menus.
    struct Draw(u64);

    impl Draw {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        fn below(&mut self, bound: usize) -> usize {
            (self.next() % bound as u64) as usize
        }

        /// A random involution of `ports` ports: a random partial matching.
        fn involution(&mut self, ports: usize) -> PortPermutation {
            let mut images: Vec<usize> = (0..ports).collect();
            let mut free: Vec<usize> = (0..ports).collect();
            while free.len() >= 2 {
                let a = free.swap_remove(self.below(free.len()));
                if self.next() & 1 == 0 {
                    continue;
                }
                let b = free.swap_remove(self.below(free.len()));
                images.swap(a, b);
            }
            PortPermutation::new(images).unwrap()
        }
    }

    /// A menu of `edges` random edges on `ports` ports whose stage under key `k` is a fixed random
    /// involution per (edge, key).
    fn random_menu(draw: &mut Draw, ports: usize, edges: usize, keys: usize) -> Menu<usize> {
        let menu_edges = (0..edges)
            .map(|_| {
                let (from, to) = (draw.below(ports), draw.below(ports));
                let stages: Vec<PortPermutation> =
                    (0..keys).map(|_| draw.involution(ports)).collect();
                Edge::new(from, to, move |key: &usize| Ok(stages[*key].clone()))
            })
            .collect();
        Menu::of_edges(ports, menu_edges).unwrap()
    }

    fn brute(menu: &Menu<usize>, keys: &[usize]) -> Vec<(usize, PortImages)> {
        let mut kept: Vec<(usize, PortImages)> = menu
            .candidates(keys)
            .unwrap()
            .into_iter()
            .filter(|candidate| {
                menu.edges()
                    .iter()
                    .all(|edge| edge.holds(candidate).unwrap())
            })
            .map(|candidate| (candidate.key, candidate.images))
            .collect();
        kept.sort();
        kept
    }

    fn propagated(menu: &Menu<usize>, keys: &[usize]) -> Vec<(usize, PortImages)> {
        let mut kept: Vec<(usize, PortImages)> = menu
            .propagate(keys)
            .unwrap()
            .candidates
            .into_iter()
            .map(|candidate| (candidate.key, candidate.images))
            .collect();
        kept.sort();
        kept
    }

    /// Lean `HNN/Keys.propagation_eq_edge_fibre`: on every random
    /// menu below the image ceiling, with several components and self-edges, the propagated
    /// survivors are exactly the injective candidates satisfying every edge.
    #[test]
    fn propagation_equals_the_brute_force_edge_fibre() {
        let mut draw = Draw(7);
        for trial in 0..60 {
            let ports = 3 + trial % 4;
            let edges = 1 + draw.below(6);
            let keys: Vec<usize> = (0..3).collect();
            let menu = random_menu(&mut draw, ports, edges, keys.len());
            assert_eq!(
                propagated(&menu, &keys),
                brute(&menu, &keys),
                "trial {trial}"
            );
        }
    }

    /// Lean `Keys.fibre_cons`: adding an edge only shrinks the fibre, restricted to the earlier
    /// ports; a conflict is reported as a failing loop through its seed.
    #[test]
    fn adding_an_edge_only_shrinks_the_propagated_fibre() {
        let mut draw = Draw(11);
        let keys: Vec<usize> = (0..2).collect();
        for _ in 0..20 {
            let full = random_menu(&mut draw, 5, 5, keys.len());
            let mut menu = Menu::of_edges(5, Vec::new()).unwrap();
            let mut previous: Option<(Vec<usize>, Vec<(usize, PortImages)>)> = None;
            for edge in full.edges() {
                let stage = edge.stage.clone();
                menu = menu
                    .with_edge(Edge {
                        from: edge.from,
                        to: edge.to,
                        stage,
                    })
                    .unwrap();
                let ports = menu.menu_ports();
                let fibre = propagated(&menu, &keys);
                if let Some((earlier_ports, earlier)) = &previous {
                    for (key, images) in &fibre {
                        let restricted: Vec<_> =
                            earlier_ports.iter().map(|p| images.image(*p)).collect();
                        assert!(earlier.iter().any(|(k, e)| {
                            k == key
                                && earlier_ports
                                    .iter()
                                    .map(|p| e.image(*p))
                                    .collect::<Vec<_>>()
                                    == restricted
                        }));
                    }
                }
                previous = Some((ports, fibre));
            }
        }
        // A self-edge whose stage fixes nothing admits no image: every seed conflicts on it.
        let swap = PortPermutation::new(vec![1, 0, 3, 2]).unwrap();
        let menu =
            Menu::of_edges(4, vec![Edge::new(2, 2, move |_: &usize| Ok(swap.clone()))]).unwrap();
        let result = menu.propagate(&[0]).unwrap();
        assert!(result.candidates.is_empty());
        assert_eq!(result.failing_loop, Some(vec![0]));
        assert_eq!(result.seeds, 4);
    }

    /// A stage that is not an involution has no reverse, so propagation refuses it.
    #[test]
    fn a_non_involutive_stage_is_refused() {
        let cycle = PortPermutation::new(vec![1, 2, 0]).unwrap();
        let menu =
            Menu::of_edges(3, vec![Edge::new(0, 1, move |_: &usize| Ok(cycle.clone()))]).unwrap();
        assert_eq!(
            menu.propagate(&[0]),
            Err(CompressionError::StageNotInvolution {
                edge: 0,
                key_index: 0
            })
        );
    }
}
