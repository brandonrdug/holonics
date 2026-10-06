//! **Joining clock axes: a commuting join or its cycle defect.**
//!
//! [definition] Rebuild step 6, K4 (#75); restructure plan §3.6 at `13f8c734`: keep distinct
//! addressed clock lines — the source (generator phase), receiving (proper time), fluid (world-tube
//! time), thermal (relaxation) and observation (ticks) axes ([`ClockAxis`]). A declared unit/chart
//! map between two axes is the undivided pair `(dτ_from : dτ_to)` ([`AxisRate`]), read by the owner's
//! [`crate::aeon::rate`] of two clocks on one aeon ([`AxisRate::read`]) or declared. A **join**
//! assigns every axis one rate against a reference so that every declared map is the ratio of the
//! two ([`AxesJoin::Commuting`]); it exists exactly when the product of the declared ratios around
//! every cycle is one, and otherwise the cycle is returned with its **holonomy**, the product of its
//! ratios composed undivided by [`Presentation::follow`] ([`AxesJoin::Defect`]). Every connected
//! component of the declared maps is decided, not only the reference's: a component the reference
//! does not reach is returned joined against its own reference ([`AxisComponent`]), never against
//! the reference, and a cycle defect in it refuses the join.
//!
//! Lean `Physics/Information/ClockJoin`: `join_silent_on_cycles` (a join is silent on cycles,
//! through `Aeon/Clock/Reading.wordReading_exactForm`), `join_of_silent_on_cycles` (the potential
//! read along a spanning set of aeons joins a silent cochain), `join_iff_silent`, and the triangle
//! `2, 3, 1/5` whose loop reads `6/5` (`triangle_defect`). The rates are carried multiplicatively,
//! exact, in the chart `Additive ℚˣ` of the Lean statement.

use std::collections::{BTreeMap, VecDeque};

use num_traits::{One, Signed};

use crate::aeon::AeonError;
use crate::aeon::groupoid::{Aeon, ParametricComplex};
use crate::aeon::reading::{Clock, rate};
use crate::ratio::{Presentation, Rat};

/// [definition] **An addressed clock line** of the plural-clock return.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClockAxis {
    /// The source/generator phase.
    Source,
    /// The receiving proper time.
    Receiving,
    /// The fluid's world-tube time.
    Fluid,
    /// The thermal relaxation time.
    Thermal,
    /// The observation ticks.
    Observation,
}

/// [definition] **A declared rate between two axes**: the undivided positive pair
/// `(dτ_from : dτ_to)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxisRate {
    from: ClockAxis,
    to: ClockAxis,
    pair: Presentation,
}

impl AxisRate {
    /// A declared rate, refused when it joins an axis to itself or is not a positive ratio.
    pub fn new(from: ClockAxis, to: ClockAxis, pair: Presentation) -> Result<Self, AeonError> {
        match pair.quotient() {
            Some(quotient) if quotient.is_positive() && from != to => Ok(Self { from, to, pair }),
            _ => Err(AeonError::NotAPositiveRate),
        }
    }

    /// [definition] **The rate read on one aeon** by the owner's [`rate`] of the two axes' clocks.
    pub fn read<K, A, B>(
        from: ClockAxis,
        to: ClockAxis,
        from_clock: &A,
        to_clock: &B,
        aeon: &Aeon<K>,
    ) -> Result<Self, AeonError>
    where
        K: ParametricComplex,
        A: Clock<K>,
        B: Clock<K>,
    {
        Self::new(from, to, rate(from_clock, to_clock, aeon)?)
    }

    pub fn from(&self) -> ClockAxis {
        self.from
    }

    pub fn to(&self) -> ClockAxis {
        self.to
    }

    pub fn pair(&self) -> &Presentation {
        &self.pair
    }

    fn quotient(&self) -> Rat {
        self.pair
            .quotient()
            .expect("a constructed rate has a nonzero denominator")
    }

    /// The pair traversed from `at` to the other axis.
    fn oriented_from(&self, at: ClockAxis) -> Presentation {
        if at == self.from {
            self.pair.clone()
        } else {
            Presentation::new(
                self.pair.denominator().clone(),
                self.pair.numerator().clone(),
            )
        }
    }
}

/// [definition] **A connected component of the declared maps** outside the reference's: every axis
/// in it has one rate against the component's own local reference, and every declared map inside it
/// is the ratio of two. No rate is invented between components.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxisComponent {
    pub reference: ClockAxis,
    /// `dτ_axis / dτ_reference` for every axis of the component.
    pub ticks: BTreeMap<ClockAxis, Rat>,
}

/// [definition] **The return of a join**: either every joined axis's ticks per reference tick,
/// with the other components of the declared maps each joined against its own reference, or the
/// cycle that obstructs a join and its holonomy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AxesJoin {
    Commuting {
        reference: ClockAxis,
        /// `dτ_axis / dτ_reference` for every axis joined to the reference.
        ticks: BTreeMap<ClockAxis, Rat>,
        /// The components not connected to the reference, each verified silent on its cycles.
        unjoined: Vec<AxisComponent>,
    },
    Defect {
        /// A closed walk of axes, first equal to last.
        cycle: Vec<ClockAxis>,
        /// The product of the declared ratios around it, undivided; projectively not `(1 : 1)`.
        holonomy: Presentation,
    },
}

impl AxesJoin {
    /// [definition] **The rate `dτ_from / dτ_to`** between two axes joined to the reference, read
    /// from the join; refused for a defect or an axis outside the reference's component.
    pub fn rate(&self, from: ClockAxis, to: ClockAxis) -> Result<Rat, AeonError> {
        match self {
            AxesJoin::Commuting { ticks, .. } => {
                let a = ticks
                    .get(&from)
                    .ok_or(AeonError::AxisNotJoined { axis: from })?;
                let b = ticks
                    .get(&to)
                    .ok_or(AeonError::AxisNotJoined { axis: to })?;
                Ok(a / b)
            }
            AxesJoin::Defect { cycle, holonomy } => Err(AeonError::AxesDefect {
                cycle: cycle.clone(),
                holonomy: Box::new(holonomy.clone()),
            }),
        }
    }
}

/// One connected component of the declared maps, spread from `root` along a spanning tree.
struct Spread {
    root: ClockAxis,
    ticks: BTreeMap<ClockAxis, Rat>,
    /// The tree edge by which each axis was reached, for reading cycles back.
    parent: BTreeMap<ClockAxis, usize>,
    tree: Vec<bool>,
}

impl Spread {
    /// Breadth-first from `root`: `q = dτ_from/dτ_to`, so `ticks(to) = ticks(from)/q` and
    /// `ticks(from) = ticks(to)·q`.
    fn from_root(rates: &[AxisRate], root: ClockAxis) -> Self {
        let mut ticks = BTreeMap::from([(root, Rat::one())]);
        let mut parent = BTreeMap::new();
        let mut tree = vec![false; rates.len()];
        let mut queue = VecDeque::from([root]);
        while let Some(axis) = queue.pop_front() {
            for (index, edge) in rates.iter().enumerate() {
                let other = if edge.from == axis {
                    edge.to
                } else if edge.to == axis {
                    edge.from
                } else {
                    continue;
                };
                if ticks.contains_key(&other) {
                    continue;
                }
                let here = ticks[&axis].clone();
                let value = if edge.from == axis {
                    here / edge.quotient()
                } else {
                    here * edge.quotient()
                };
                ticks.insert(other, value);
                parent.insert(other, index);
                tree[index] = true;
                queue.push_back(other);
            }
        }
        Self {
            root,
            ticks,
            parent,
            tree,
        }
    }

    /// Every non-tree map inside the component checked against the ticks: the first that disagrees
    /// closes a cycle whose holonomy is not one.
    fn defect(&self, rates: &[AxisRate]) -> Option<AxesJoin> {
        rates.iter().enumerate().find_map(|(index, edge)| {
            if self.tree[index] {
                return None;
            }
            let (from, to) = (self.ticks.get(&edge.from)?, self.ticks.get(&edge.to)?);
            (from / to != edge.quotient()).then(|| defect(rates, &self.parent, self.root, index))
        })
    }
}

/// [proved-derived; implemented-exact] **Join the clock axes** (Lean `join_iff_silent`). The first
/// declared map's source is the reference. Every connected component of the declared maps is
/// spread from a local reference along a spanning tree (Lean `join_of_silent_on_cycles`, the
/// potential read along chosen aeons), the reference's own component first, and every other map of
/// the component is checked against its ticks. A map that disagrees closes a cycle whose holonomy
/// is not one: the defect is returned with that cycle (Lean `triangle_defect`), in whichever
/// component it lies. Components not connected to the reference are returned verified and joined
/// against their own references, never against the reference.
pub fn join_axes(rates: &[AxisRate]) -> Result<AxesJoin, AeonError> {
    let Some(first) = rates.first() else {
        return Err(AeonError::NoDeclaredRate);
    };
    let reference = first.from;
    let mut components: Vec<Spread> = Vec::new();
    let roots =
        std::iter::once(reference).chain(rates.iter().flat_map(|edge| [edge.from, edge.to]));
    for root in roots {
        if components
            .iter()
            .any(|component| component.ticks.contains_key(&root))
        {
            continue;
        }
        let component = Spread::from_root(rates, root);
        if let Some(defect) = component.defect(rates) {
            return Ok(defect);
        }
        components.push(component);
    }
    let mut components = components.into_iter();
    let main = components
        .next()
        .expect("the reference's component is spread first");
    Ok(AxesJoin::Commuting {
        reference,
        ticks: main.ticks,
        unjoined: components
            .map(|component| AxisComponent {
                reference: component.root,
                ticks: component.ticks,
            })
            .collect(),
    })
}

/// The tree path from the component's root down to `axis`, as `(axis reached, edge)` pairs in
/// order.
fn path_from_root(
    rates: &[AxisRate],
    parent: &BTreeMap<ClockAxis, usize>,
    axis: ClockAxis,
) -> Vec<(ClockAxis, usize)> {
    let mut path = Vec::new();
    let mut at = axis;
    while let Some(&edge) = parent.get(&at) {
        path.push((at, edge));
        let e = &rates[edge];
        at = if e.to == at { e.from } else { e.to };
    }
    path.reverse();
    path
}

/// The closed walk root → `from` along the tree, across the offending map to `to`, and back to the
/// root along the tree; its holonomy composes the declared pairs undivided.
fn defect(
    rates: &[AxisRate],
    parent: &BTreeMap<ClockAxis, usize>,
    root: ClockAxis,
    offending: usize,
) -> AxesJoin {
    let edge = &rates[offending];
    let mut cycle = vec![root];
    let mut holonomy = Presentation::new(Rat::one(), Rat::one());
    let mut at = root;
    for (reached, index) in path_from_root(rates, parent, edge.from) {
        holonomy = holonomy.follow(&rates[index].oriented_from(at));
        cycle.push(reached);
        at = reached;
    }
    holonomy = holonomy.follow(&edge.oriented_from(at));
    at = edge.to;
    cycle.push(at);
    let mut back = path_from_root(rates, parent, edge.to);
    back.reverse();
    for (reached, index) in back {
        let e = &rates[index];
        let next = if e.to == reached { e.from } else { e.to };
        holonomy = holonomy.follow(&e.oriented_from(at));
        cycle.push(next);
        at = next;
    }
    AxesJoin::Defect { cycle, holonomy }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aeon::{ClosedForm, FiniteComplex, Form, Step};
    use crate::ratio::{integer, rat};

    fn declared(from: ClockAxis, to: ClockAxis, num: i64, den: i64) -> AxisRate {
        AxisRate::new(from, to, Presentation::new(integer(num), integer(den))).unwrap()
    }

    /// Lean `ClockJoin.join_of_silent_on_cycles`, `join_iff_silent`: declared rates that close around
    /// every cycle join; each axis gets one rate against the reference and every declared map is the
    /// ratio of two.
    #[test]
    fn a_consistent_declaration_joins() {
        let rates = [
            declared(ClockAxis::Source, ClockAxis::Receiving, 3, 1),
            declared(ClockAxis::Receiving, ClockAxis::Fluid, 1, 2),
            declared(ClockAxis::Source, ClockAxis::Fluid, 3, 2),
        ];
        let join = join_axes(&rates).unwrap();
        let AxesJoin::Commuting {
            reference,
            ticks,
            unjoined,
        } = &join
        else {
            panic!("the declaration closes around its cycle");
        };
        assert_eq!(*reference, ClockAxis::Source);
        assert_eq!(ticks[&ClockAxis::Receiving], rat(1, 3));
        assert_eq!(ticks[&ClockAxis::Fluid], rat(2, 3));
        assert!(unjoined.is_empty());
        for rate in &rates {
            assert_eq!(
                join.rate(rate.from(), rate.to()).unwrap(),
                rate.pair().quotient().unwrap()
            );
        }
    }

    /// [counterexample] Lean `triangle_defect`: the rates `2`, `3`, `1/5` around the triangle of
    /// axes read the holonomy `6/5`, and no join exists.
    #[test]
    fn the_triangle_of_axes_returns_its_defect() {
        let rates = [
            declared(ClockAxis::Source, ClockAxis::Receiving, 2, 1),
            declared(ClockAxis::Receiving, ClockAxis::Fluid, 3, 1),
            declared(ClockAxis::Fluid, ClockAxis::Source, 1, 5),
        ];
        let AxesJoin::Defect { cycle, holonomy } = join_axes(&rates).unwrap() else {
            panic!("the triangle does not close");
        };
        assert_eq!(cycle.first(), cycle.last());
        assert!(holonomy.projectively_equal(&Presentation::new(integer(6), integer(5))));
    }

    /// Lean `join_silent_on_cycles` with the owner's `rate`: two axes' clocks read on one aeon give
    /// the declared rate by which they join.
    #[test]
    fn rates_read_from_clocks_join() {
        let complex = FiniteComplex::graph(2, &[0], &[1]).unwrap();
        let aeon = Aeon::new(&complex, 0, vec![Step::along(0)]).unwrap();
        let fluid = ClosedForm::new(&complex, Form::new(vec![rat(5, 2)])).unwrap();
        let thermal = ClosedForm::new(&complex, Form::new(vec![rat(1, 4)])).unwrap();
        let read = AxisRate::read(
            ClockAxis::Fluid,
            ClockAxis::Thermal,
            &fluid,
            &thermal,
            &aeon,
        )
        .unwrap();
        let join = join_axes(&[read]).unwrap();
        assert_eq!(
            join.rate(ClockAxis::Fluid, ClockAxis::Thermal).unwrap(),
            integer(10)
        );
    }

    /// [counterexample] An axis no declared map connects to the reference is not joined to it, and
    /// a rate to it is refused rather than invented; its own component is joined against its own
    /// reference. A rate of an axis to itself is refused.
    #[test]
    fn an_unconnected_axis_is_not_joined() {
        let rates = [
            declared(ClockAxis::Source, ClockAxis::Receiving, 2, 1),
            declared(ClockAxis::Thermal, ClockAxis::Observation, 1, 3),
        ];
        let join = join_axes(&rates).unwrap();
        let AxesJoin::Commuting { unjoined, .. } = &join else {
            panic!("no cycle is declared");
        };
        assert_eq!(
            unjoined,
            &vec![AxisComponent {
                reference: ClockAxis::Thermal,
                ticks: BTreeMap::from([
                    (ClockAxis::Thermal, integer(1)),
                    (ClockAxis::Observation, integer(3)),
                ]),
            }]
        );
        assert_eq!(
            join.rate(ClockAxis::Source, ClockAxis::Thermal),
            Err(AeonError::AxisNotJoined {
                axis: ClockAxis::Thermal
            })
        );
        assert_eq!(
            AxisRate::new(
                ClockAxis::Fluid,
                ClockAxis::Fluid,
                Presentation::new(integer(1), integer(1))
            ),
            Err(AeonError::NotAPositiveRate)
        );
    }

    /// [counterexample] Lean `join_iff_silent` holds in every component, not only the reference's:
    /// with `Source → Receiving` at `2 : 1`, the loop `Thermal → Observation → Thermal` of rates
    /// `1 : 3` and `1 : 1` reads the holonomy `1/3`, so no join exists although the reference's
    /// component closes.
    #[test]
    fn a_defect_outside_the_reference_component_is_returned() {
        let rates = [
            declared(ClockAxis::Source, ClockAxis::Receiving, 2, 1),
            declared(ClockAxis::Thermal, ClockAxis::Observation, 1, 3),
            declared(ClockAxis::Observation, ClockAxis::Thermal, 1, 1),
        ];
        let AxesJoin::Defect { cycle, holonomy } = join_axes(&rates).unwrap() else {
            panic!("the loop of the second component does not close");
        };
        assert_eq!(
            cycle,
            vec![
                ClockAxis::Thermal,
                ClockAxis::Observation,
                ClockAxis::Thermal
            ]
        );
        assert!(holonomy.projectively_equal(&Presentation::new(integer(1), integer(3))));
    }
}
