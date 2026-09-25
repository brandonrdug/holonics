//! **Locating keys: navigator inference by loop closure is a fibre that pruning shrinks.**
//!
//! [definition] The key is the **initial configuration** of the navigators
//! ([keys](../../../../docs/ELEMENTARY_OBJECTS.md#keys-locks-and-navigation)). A menu is a finite
//! family of observed loops over pair contacts; each loop, under a candidate key, performs an
//! ordered stage word read through the unknown boundary map `S`. By the pair's
//! [`menu_loop_closure`] the loop at port `a` closes exactly when the stage word fixes `S a`, so a
//! candidate is a key with the **boundary images at the menu's ports** ([`PortImages`], a partial
//! injection), never a whole boundary map (Lean `fibre_depends_only_on_port_images`). The
//! consistent candidates are the fibre of the loop-closure map over the true candidate's reading
//! (Lean `Keys.fibre`, `closureMap`, `truth_mem_fibre`: a definition); for an observed menu it is
//! the Bombe's test set (`fibre_eq_bombe`).
//!
//! ```text
//! closes(k, s) :⇔ W_k(s a) = s a                         s the boundary images at the menu ports
//! fibre(loop :: menu) = fibre(menu) ∩ {c | closes(c) ⇔ closes(truth)}      pruning
//! stages(γ k) = ρ⁻¹ stages(k) ρ  ⇒  (k, s) ∈ fibre ⇔ (γ k, ρ⁻¹ ∘ s) ∈ fibre     the gauge
//! ```
//!
//! [proved-derived; implemented-exact] The content tested here: adding a loop only shrinks the
//! fibre and never discards the true key (Lean `fibre_cons`, `fibre_append_subset`), and loop
//! closure locates the key only up to a gauge. A [`Gauge`] of a menu (Lean `Keys.Gauge`) relabels
//! the keys and turns the boundary so that every loop's stage word is conjugated,
//! `stages(γ k) = ρ⁻¹ stages(k) ρ`; its constructor checks that covariance exactly at every
//! declared key. Then loop closure is gauge invariant, since `W_{γk}(ρ⁻¹ s a) = ρ⁻¹ W_k(s a)`
//! (`Gauge.closes_iff`): the fibre is a union of gauge orbits (`fibre_gauge_invariant`,
//! `iterate_mem_fibre_iff`), no menu separates the true key from its gauge image
//! (`fibre_gauge_truth`), and when the gauge reaches every key and the menu pins the boundary
//! images at each key, the fibre is exactly the gauge orbit of the true key (`fibre_eq_orbit`).
//!
//! [definition] **The reflector machine** ([`ReflectorMachine`], Lean `Keys.Machine`): the stage at
//! rotor position `m` is the reflected return `ρ^{−m} F ρ^m` through the rotor's producing operand,
//! covariant under one rotor step. The key is the initial configuration of the rotor's clock, a
//! [`Clock`] whose ticks its odometer carries; a loop reached `i` ticks after the key reads the
//! rotor position `(key + i) mod ord ρ`. Its rotor gauge `(k, s) ↦ (k + 1, ρ⁻¹ ∘ s)` is a gauge of
//! every menu of its loops (`Machine.stage_succ`, `Machine.rotorGauge`). On three ports the
//! candidates prune `18 → 6 → 3` (`Machine.pruning_counts`) and the three survivors are one gauge
//! orbit (`Machine.two_loop_fibre_is_one_orbit`); with one loop the images at an unread port are
//! not pinned and the fibre is not one orbit (`Machine.one_loop_fibre_is_not_one_orbit`).
//!
//! [open] Key inference over continuous navigator configurations (screw and phase keys), with the
//! joint description of key and gauge, is owed in #62.

use num_bigint::BigUint;

use crate::compression::CompressionError;
use crate::holon::contact::menu::{
    MenuError, PortPermutation, menu_loop_closure, reflected_return,
};
use crate::navigator::Clock;

mod edges;

pub use edges::{Edge, Propagation};

/// The ceiling on the candidate boundary images one enumeration forms.
///
/// \[definition; agent-inferred\] `n` ports take `n!/(n − m)!` injective images at `m` menu ports;
/// the count is formed with checked arithmetic and compared before any allocation, at the order of
/// the standing owner's `WORD_COUNT_CEILING`.
pub const IMAGE_FAMILY_CEILING: usize = 1 << 14;

/// [definition] **The boundary images at a set of ports**: a partial injection into a declared
/// port population. It is all of a boundary map that loop closure reads.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PortImages {
    ports: usize,
    images: Vec<(usize, usize)>,
}

impl PortImages {
    /// The images `port ↦ image`, sorted by port; refused unless every port and image lies in the
    /// population, no port repeats and no image repeats.
    pub fn new(ports: usize, mut images: Vec<(usize, usize)>) -> Result<Self, CompressionError> {
        images.sort_unstable();
        for (index, (port, image)) in images.iter().enumerate() {
            for value in [*port, *image] {
                if value >= ports {
                    return Err(MenuError::PortOutside { port: value, ports }.into());
                }
            }
            if images[..index]
                .iter()
                .any(|(earlier, earlier_image)| earlier == port || earlier_image == image)
            {
                return Err(CompressionError::NotInjective { port: *port });
            }
        }
        Ok(Self { ports, images })
    }

    /// The images a whole boundary map gives at the declared ports.
    pub fn of(boundary: &PortPermutation, at: &[usize]) -> Result<Self, CompressionError> {
        let images = at
            .iter()
            .map(|port| Ok((*port, boundary.apply(*port)?)))
            .collect::<Result<Vec<_>, MenuError>>()?;
        Self::new(boundary.ports(), images)
    }

    /// **Every injective image of the declared ports**, in lexicographic order.
    ///
    /// # Declared-size guard
    ///
    /// The count `n!/(n − m)!` is formed with checked arithmetic and refused past
    /// [`IMAGE_FAMILY_CEILING`] before any allocation.
    pub fn injections(ports: usize, at: &[usize]) -> Result<Vec<Self>, CompressionError> {
        let mut count: usize = 1;
        for taken in 0..at.len() {
            count = ports
                .checked_sub(taken)
                .and_then(|choices| count.checked_mul(choices))
                .filter(|count| *count <= IMAGE_FAMILY_CEILING)
                .ok_or(CompressionError::ImageFamilyCeiling {
                    ports,
                    at: at.len(),
                    ceiling: IMAGE_FAMILY_CEILING,
                })?;
        }
        let mut partial: Vec<Vec<usize>> = vec![Vec::new()];
        for _ in at {
            let mut extended = Vec::new();
            for chosen in &partial {
                for image in (0..ports).filter(|image| !chosen.contains(image)) {
                    let mut next = chosen.clone();
                    next.push(image);
                    extended.push(next);
                }
            }
            partial = extended;
        }
        partial
            .into_iter()
            .map(|chosen| Self::new(ports, at.iter().copied().zip(chosen).collect()))
            .collect()
    }

    /// The port population.
    pub fn ports(&self) -> usize {
        self.ports
    }

    /// The image of one port, when declared.
    pub fn image(&self, port: usize) -> Option<usize> {
        self.images
            .iter()
            .find(|(declared, _)| *declared == port)
            .map(|(_, image)| *image)
    }

    /// **The images turned by a permutation**, `σ ∘ s`: the boundary side of a gauge.
    pub fn turned(&self, turn: &PortPermutation) -> Result<Self, CompressionError> {
        let images = self
            .images
            .iter()
            .map(|(port, image)| Ok((*port, turn.apply(*image)?)))
            .collect::<Result<Vec<_>, MenuError>>()?;
        Self::new(self.ports, images)
    }
}

/// [definition] **A candidate**: a key (the navigators' initial configuration) and the boundary
/// images at the menu's ports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Candidate<Key> {
    pub key: Key,
    pub images: PortImages,
}

/// [definition] **A menu loop** (Lean `Keys.Loop`): its boundary port and, for every candidate
/// key, the ordered stage word the machine performs along the loop.
pub struct Loop<Key> {
    port: usize,
    stages: Box<dyn Fn(&Key) -> Result<Vec<PortPermutation>, MenuError>>,
}

impl<Key> std::fmt::Debug for Loop<Key> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Loop")
            .field("port", &self.port)
            .finish_non_exhaustive()
    }
}

impl<Key> Loop<Key> {
    /// A loop at `port` whose stage word under each key is `stages(key)`.
    pub fn new(
        port: usize,
        stages: impl Fn(&Key) -> Result<Vec<PortPermutation>, MenuError> + 'static,
    ) -> Self {
        Self {
            port,
            stages: Box::new(stages),
        }
    }

    /// The boundary port.
    pub fn port(&self) -> usize {
        self.port
    }

    /// The ordered stage word under a key.
    pub fn stages(&self, key: &Key) -> Result<Vec<PortPermutation>, MenuError> {
        (self.stages)(key)
    }

    /// **The loop closes at a candidate** (Lean `Loop.Closes`, read by `Loop.closes_iff`): the
    /// stage word under the candidate's key fixes the boundary image of the loop's port.
    pub fn closes(&self, candidate: &Candidate<Key>) -> Result<bool, CompressionError> {
        let image = candidate
            .images
            .image(self.port)
            .ok_or(CompressionError::MissingImage { port: self.port })?;
        let stages = self.stages(&candidate.key)?;
        Ok(menu_loop_closure(candidate.images.ports(), &stages, image)?)
    }
}

/// [definition] **A menu**: a finite family of loops, and of edges (its one-stage open paths,
/// [`Edge`]), over a declared port population.
#[derive(Debug)]
pub struct Menu<Key> {
    ports: usize,
    loops: Vec<Loop<Key>>,
    edges: Vec<Edge<Key>>,
}

impl<Key: Clone> Menu<Key> {
    /// A menu of loops on `ports` ports; a loop port outside them is refused.
    pub fn new(ports: usize, loops: Vec<Loop<Key>>) -> Result<Self, CompressionError> {
        for current in &loops {
            check_port(current.port, ports)?;
        }
        Ok(Self {
            ports,
            loops,
            edges: Vec::new(),
        })
    }

    /// **A menu of edges** on `ports` ports (addition 7 of the step-4 design): the open paths the
    /// data forms; an edge port outside them is refused. Its closed paths are its loops.
    pub fn of_edges(ports: usize, edges: Vec<Edge<Key>>) -> Result<Self, CompressionError> {
        for edge in &edges {
            check_port(edge.from(), ports)?;
            check_port(edge.to(), ports)?;
        }
        Ok(Self {
            ports,
            loops: Vec::new(),
            edges,
        })
    }

    /// The edges, in menu order.
    pub fn edges(&self) -> &[Edge<Key>] {
        &self.edges
    }

    /// **The menu with one more observed edge** at its end.
    pub fn with_edge(mut self, observed: Edge<Key>) -> Result<Self, CompressionError> {
        check_port(observed.from(), self.ports)?;
        check_port(observed.to(), self.ports)?;
        self.edges.push(observed);
        Ok(self)
    }

    /// The port population.
    pub fn ports(&self) -> usize {
        self.ports
    }

    /// The loops, in menu order.
    pub fn loops(&self) -> &[Loop<Key>] {
        &self.loops
    }

    /// The menu's ports: the distinct loop and edge ports, sorted.
    pub fn menu_ports(&self) -> Vec<usize> {
        let mut ports: Vec<usize> = self.loops.iter().map(Loop::port).collect();
        ports.extend(self.edges.iter().flat_map(|edge| [edge.from(), edge.to()]));
        ports.sort_unstable();
        ports.dedup();
        ports
    }

    /// **The menu with one more observed loop** at its head (Lean `loop :: menu`).
    pub fn extended(mut self, observed: Loop<Key>) -> Result<Self, CompressionError> {
        check_port(observed.port, self.ports)?;
        self.loops.insert(0, observed);
        Ok(self)
    }

    /// **The loop-closure map** (Lean `closureMap`): a candidate's closure reading on every loop.
    pub fn closure_map(&self, candidate: &Candidate<Key>) -> Result<Vec<bool>, CompressionError> {
        if candidate.images.ports() != self.ports {
            return Err(CompressionError::Extent {
                what: "candidate port population",
                expected: self.ports,
                found: candidate.images.ports(),
            });
        }
        self.loops
            .iter()
            .map(|current| current.closes(candidate))
            .collect()
    }

    /// Whether every loop was observed closed under the true candidate (Lean `Observed`).
    pub fn observed(&self, truth: &Candidate<Key>) -> Result<bool, CompressionError> {
        Ok(self.closure_map(truth)?.into_iter().all(|closes| closes))
    }

    /// **Every candidate over the declared keys**: each key with each injective image of the
    /// menu's ports.
    pub fn candidates(&self, keys: &[Key]) -> Result<Vec<Candidate<Key>>, CompressionError> {
        let images = PortImages::injections(self.ports, &self.menu_ports())?;
        Ok(keys
            .iter()
            .flat_map(|key| {
                images.iter().map(|images| Candidate {
                    key: key.clone(),
                    images: images.clone(),
                })
            })
            .collect())
    }

    /// **The consistent candidates** (Lean `fibre`): the declared candidates whose closure reading
    /// equals the true candidate's, in declaration order.
    pub fn fibre(
        &self,
        truth: &Candidate<Key>,
        candidates: &[Candidate<Key>],
    ) -> Result<Vec<Candidate<Key>>, CompressionError> {
        let reading = self.closure_map(truth)?;
        let mut consistent = Vec::new();
        for candidate in candidates {
            if self.closure_map(candidate)? == reading {
                consistent.push(candidate.clone());
            }
        }
        Ok(consistent)
    }
}

fn check_port(port: usize, ports: usize) -> Result<(), CompressionError> {
    if port >= ports {
        return Err(CompressionError::LoopPort { port, ports });
    }
    Ok(())
}

/// [definition] **A gauge of a menu** (Lean `Keys.Gauge`): a relabelling `γ` of the keys and a
/// boundary turn `ρ` under which every loop's stage word is conjugated elementwise,
/// `stages(γ k) = ρ⁻¹ stages(k) ρ`. It acts on candidates by `(k, s) ↦ (γ k, ρ⁻¹ ∘ s)` (Lean
/// `Gauge.act`).
pub struct Gauge<Key> {
    relabel: Box<dyn Fn(&Key) -> Key>,
    boundary: PortPermutation,
}

impl<Key> std::fmt::Debug for Gauge<Key> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Gauge")
            .field("boundary", &self.boundary)
            .finish_non_exhaustive()
    }
}

impl<Key: Clone> Gauge<Key> {
    /// **A gauge of a menu**, checked: the boundary turn acts on the menu's ports, and at every
    /// declared key every loop's stage word, and every edge's stage, under `γ k` is its word under
    /// `k` conjugated by `ρ` (Lean `Gauge.covariant`). A relabelling that breaks covariance is
    /// refused with the loop or edge and the key where it breaks.
    pub fn new(
        menu: &Menu<Key>,
        keys: &[Key],
        relabel: impl Fn(&Key) -> Key + 'static,
        boundary: PortPermutation,
    ) -> Result<Self, CompressionError> {
        if boundary.ports() != menu.ports() {
            return Err(CompressionError::Extent {
                what: "gauge boundary port population",
                expected: menu.ports(),
                found: boundary.ports(),
            });
        }
        let inverse = boundary.inverse();
        for (loop_index, current) in menu.loops().iter().enumerate() {
            for (key_index, key) in keys.iter().enumerate() {
                let conjugated = current
                    .stages(key)?
                    .iter()
                    .map(|stage| inverse.multiply(stage)?.multiply(&boundary))
                    .collect::<Result<Vec<_>, MenuError>>()?;
                if current.stages(&relabel(key))? != conjugated {
                    return Err(CompressionError::NotCovariant {
                        loop_index,
                        key_index,
                    });
                }
            }
        }
        for (edge_index, edge) in menu.edges().iter().enumerate() {
            for (key_index, key) in keys.iter().enumerate() {
                let conjugated = inverse.multiply(&edge.stage(key)?)?.multiply(&boundary)?;
                if edge.stage(&relabel(key))? != conjugated {
                    return Err(CompressionError::EdgeNotCovariant {
                        edge_index,
                        key_index,
                    });
                }
            }
        }
        Ok(Self {
            relabel: Box::new(relabel),
            boundary,
        })
    }

    /// The boundary turn `ρ`.
    pub fn boundary(&self) -> &PortPermutation {
        &self.boundary
    }

    /// **The gauge's action on a candidate**, `(k, s) ↦ (γ k, ρ⁻¹ ∘ s)` (Lean `Gauge.act`).
    pub fn act(&self, candidate: &Candidate<Key>) -> Result<Candidate<Key>, CompressionError> {
        if candidate.images.ports() != self.boundary.ports() {
            return Err(CompressionError::Extent {
                what: "candidate port population",
                expected: self.boundary.ports(),
                found: candidate.images.ports(),
            });
        }
        Ok(Candidate {
            key: (self.relabel)(&candidate.key),
            images: candidate.images.turned(&self.boundary.inverse())?,
        })
    }

    /// **The first `length` members of a candidate's gauge orbit**, `c, g·c, …, g^(length−1)·c`.
    pub fn orbit(
        &self,
        candidate: &Candidate<Key>,
        length: usize,
    ) -> Result<Vec<Candidate<Key>>, CompressionError> {
        let mut orbit: Vec<Candidate<Key>> = Vec::with_capacity(length);
        for index in 0..length {
            let next = match index {
                0 => candidate.clone(),
                _ => self.act(&orbit[index - 1])?,
            };
            orbit.push(next);
        }
        Ok(orbit)
    }
}

/// [definition] **A reflector machine** (Lean `Keys.Machine`): a rotor and a reflection on one port
/// population. The stage at rotor position `m` is the reflected return `ρ^{−m} F ρ^m`, and the rotor
/// position is the ticks of the key's clock modulo the rotor's order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReflectorMachine {
    rotor: PortPermutation,
    reflector: PortPermutation,
    period: BigUint,
}

impl ReflectorMachine {
    /// A machine on the rotor's ports; the reflector must act on the same ports.
    pub fn new(
        rotor: PortPermutation,
        reflector: PortPermutation,
    ) -> Result<Self, CompressionError> {
        if rotor.ports() != reflector.ports() {
            return Err(MenuError::PortCount {
                left: rotor.ports(),
                right: reflector.ports(),
            }
            .into());
        }
        let period = rotor.order();
        Ok(Self {
            rotor,
            reflector,
            period,
        })
    }

    /// The rotor.
    pub fn rotor(&self) -> &PortPermutation {
        &self.rotor
    }

    /// The rotor's period, its order.
    pub fn period(&self) -> &BigUint {
        &self.period
    }

    /// **The stage at rotor position `m`**: the reflected return `ρ^{−m} F ρ^m`.
    pub fn stage(&self, position: &BigUint) -> Result<PortPermutation, MenuError> {
        reflected_return(&self.rotor.power(position), &self.reflector)
    }

    /// **The rotor position `step` ticks after the key**: the key's clock advanced by `step`, its
    /// ticks read modulo the rotor's period.
    pub fn position(&self, key: &Clock, step: &BigUint) -> BigUint {
        let mut clock = key.clone();
        clock.advance(step);
        clock.ticks() % &self.period
    }

    /// **The one-stage loop at `port` reached `step` ticks after the key** (Lean `Machine.loopAt`).
    pub fn loop_at(&self, port: usize, step: BigUint) -> Loop<Clock> {
        let machine = self.clone();
        Loop::new(port, move |key: &Clock| {
            Ok(vec![machine.stage(&machine.position(key, &step))?])
        })
    }

    /// **The one-stage edge `from — to` reached `step` ticks after the key**: the reflected return
    /// at that rotor position, `S(to) = ρ^{−m} F ρ^m S(from)` with `m = key + step`. Its stage is
    /// an involution whenever the reflector is, so the edge is traversed both ways.
    pub fn edge_at(&self, from: usize, to: usize, step: BigUint) -> Edge<Clock> {
        let machine = self.clone();
        Edge::new(from, to, move |key: &Clock| {
            machine.stage(&machine.position(key, &step))
        })
    }

    /// **The rotor gauge of a menu of this machine's loops** (Lean `Machine.rotorGauge`): one tick
    /// of the key's clock with the boundary turned back one rotor step, `(k, s) ↦ (k + 1, ρ⁻¹ ∘ s)`.
    /// Every stage is covariant under it, `stage(m + 1) = ρ⁻¹ stage(m) ρ` (`Machine.stage_succ`),
    /// which [`Gauge::new`] checks at every declared key.
    pub fn gauge(
        &self,
        menu: &Menu<Clock>,
        keys: &[Clock],
    ) -> Result<Gauge<Clock>, CompressionError> {
        Gauge::new(
            menu,
            keys,
            |key: &Clock| {
                let mut advanced = key.clone();
                advanced.advance(&BigUint::from(1u32));
                advanced
            },
            self.rotor.clone(),
        )
    }
}

#[cfg(test)]
mod tests;
