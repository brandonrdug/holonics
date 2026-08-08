//! A size-agnostic recursive cell, the schedules that expand it, and the 2-complex it grows.
//!
//! [`crate::rebase_invariants`] opens by declaring that **the expansion schedule is a receiver** and
//! that the question making a rendering mathematics rather than illustration is *what survives every
//! schedule*. Until this module there was no recursive cell in the tree and no expansion schedule:
//! every complex the crate read was **produced**, never **grown**. This is the missing material.
//!
//! ## The discipline, ported from MorphoHDL
//!
//! Mordvintsev, *MorphoHDL* (Google Paradigms of Intelligence, July 2026). The whole language core
//! is a decorator, a bus split, and a declared fallback:
//!
//! ```text
//!   @morpho(fallback=full_adder)          a rule with a declared fallback
//!   def ripple_adder(a, b, c):
//!       a0, a1 = SPLIT(a)                 refuses a bus narrower than two -- raises
//!       b0, b1 = SPLIT(b)
//!       s0, c_mid = ripple_adder(a0,b0,c) the rule recurs on its own halves
//!       s1, c_out = ripple_adder(a1,b1,c_mid)
//!       return CAT(s0, s1), c_out
//! ```
//!
//! **There is no `N`, no loop bound, and no `if`.** Width enters as the *length of the argument*.
//! The base case is not a condition the program tests — it is **the boundary of the material**. When
//! [`split`] cannot halve what it was handed, the refusal unwinds to the nearest declared
//! [`Fallback`]. That single property is what separates growth from a parameterized generator, and
//! it is what is preserved here.
//!
//! The only two refusals in this module's termination path are properties of the *operations*, not
//! sizes of a *design*: **you cannot halve fewer than two things** ([`split`]) and **you cannot take
//! a bit from nothing** ([`take_low_bit`], [`take_high_bit`]). No rule mentions a width, and the
//! same `&'static` rule table grows every width in this file.
//!
//! ## Why the schedule is a real parameter here and is not in Python
//!
//! MorphoHDL's `run_cell` is `f(*args)` — Python's own call stack is the schedule and it cannot be
//! varied. Here expansion is a **worklist**: a rule's body allocates its children's output nets and
//! *defers* their bodies, so at any moment several instances are expandable and [`Schedule`] chooses
//! among them. The deferral is paid for by one declaration, [`OutShape`], which states a rule's
//! output shape structurally — `LikeArg(i)` or `Bit`, never a number — and which is **verified
//! against what the child actually grows**, so a wrong declaration is a refusal rather than an
//! assumption ([`GrowthRefusal::OutShapeContract`]).
//!
//! Net identifiers, gate identifiers and instance identifiers are all allocated *at expansion time*.
//! Two schedules therefore produce the same circuit under **different symbols**, which is exactly the
//! sentence the invariants organ exists to answer:
//!
//! > *"the symbol does not dictate what the information contains, you could reorganize the symbols
//! > and the structure of the proof or algorithm would determine the identity of the underlying
//! > algorithmic patterns."* — Brandon, 2026-08-06
//!
//! [`canonical_netlist`] settles the netlist half of that exactly, by hash-consing rather than
//! hashing: two growths are compared by an interned canonical form, so "the same circuit" is decided
//! and not estimated.
//!
//! ## The 2-complex, and where its faces come from
//!
//! ```text
//!   0-cells   nets
//!   1-cells   conduction arcs.  For a primitive gate, one per input PIN, so a gate reading one net
//!             on two pins carries two parallel arcs.  For an instance at any lineage level, one per
//!             conducting (in-port, out-port) pair -- the instance read as a black box.
//!   2-cells   cell division.  A parent's own coarse arc, against the refinement that replaced it.
//! ```
//!
//! The division face is the point of the construction. For a parent `I` and one of its arcs
//! `p -> q`, let `k` be the number of paths from `net(p)` to `net(q)` through `I`'s children, and for
//! each child arc `e` let `w(e) = paths(net(p) -> tail(e)) * paths(head(e) -> net(q))`. Then
//!
//! ```text
//!   d F(I,p,q)  =  k * arc(I,p,q)  -  sum_e w(e) * e
//! ```
//!
//! and the sum telescopes to `k * (net(q) - net(p))`, so the face closes. **The attaching map comes
//! from the lineage — there is no embedding search and no choice**, which is what
//! `derivation_curvature.rs` had to build a scaffold to fake. `w` is computed by two dynamic-programs
//! over the local DAG, so no path is ever enumerated and the coefficients are exact `BigUint`.
//!
//! This is where multiplicity above one can enter a complex that was **grown** rather than authored.
//! `derivation_atlas.rs` establishes that under `RecruitmentCoefficient::Incidence` the boundary is a
//! graph incidence matrix, totally unimodular, so no reading under it returns torsion at any grade;
//! grade-0 torsion is recovered there only by an explicit `Multiplicity` counting coefficient. A
//! division face carries `k > 1` exactly when the parent's material **reconverges**, which is a
//! property of the circuit and of nothing the reading chose.
//!
//! [`FaceFamily::Reconvergence`] is the second, separately declared family: two paths leaving one net
//! and meeting again bound a disc. It is kept separable so a reading can be taken with either family
//! or both ([`ComplexAperture`]).
//!
//! ## Declared bounds
//!
//! - Every coefficient is an exact integer. There is no float in this module and no scalar that
//!   governs; path counts and widths **measure**.
//! - A rule whose body raises is retried at its fallback with **all** of its staged work rolled back,
//!   including the net counter. A partially grown body never survives its own refusal.
//! - The conduction relation of an instance is computed bottom-up over the lineage and is
//!   schedule-independent by construction; the **founding order** of the complex is the expansion
//!   order and is therefore fully schedule-dependent. That is deliberate: it is what makes
//!   `invariants_agree` a test rather than a tautology.
//! - [`FaceFamily::Reconvergence`] enumerates pairs of out-arcs and is quadratic in fan-out. It
//!   refuses past [`ComplexAperture::face_aperture`] rather than returning a truncated family.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use crate::algebraic::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use crate::causal::EventId;

// ===============================================================================================
// the material

/// A net. Identifiers are allocated during expansion, so they are a **receiver coordinate**: two
/// schedules number the same circuit differently and nothing that survives may depend on it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NetId(pub u64);

/// A bundle of nets. Its width is never declared — it is the length of what was handed over, and it
/// is the only place size enters this module at all.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Bus {
    nets: Vec<NetId>,
}

impl Bus {
    pub fn new(nets: Vec<NetId>) -> Self {
        Self { nets }
    }

    pub fn width(&self) -> usize {
        self.nets.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nets.is_empty()
    }

    pub fn nets(&self) -> &[NetId] {
        &self.nets
    }
}

/// Why a body stopped.
///
/// [`BodyStop::Exhausted`] is MorphoHDL's `IndexError`: the material ran out, which unwinds to the
/// nearest declared fallback and is **not** a failure. [`BodyStop::Refused`] is a defect and aborts
/// the whole growth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BodyStop {
    Exhausted,
    Refused(GrowthRefusal),
}

/// Halve a bus. Refuses fewer than two nets, because halving fewer than two is not an operation.
pub fn split(bus: &Bus) -> Result<(Bus, Bus), BodyStop> {
    let width = bus.width();
    if width < 2 {
        return Err(BodyStop::Exhausted);
    }
    let middle = width / 2;
    Ok((
        Bus::new(bus.nets[..middle].to_vec()),
        Bus::new(bus.nets[middle..].to_vec()),
    ))
}

/// Concatenate. The width of the result is the sum of what arrived and is never stated.
pub fn cat(parts: &[&Bus]) -> Bus {
    let mut nets = Vec::new();
    for part in parts {
        nets.extend_from_slice(&part.nets);
    }
    Bus::new(nets)
}

/// The lowest net, and the rest. Refuses nothing at all, because a bit cannot be taken from nothing.
pub fn take_low_bit(bus: &Bus) -> Result<(Bus, Bus), BodyStop> {
    if bus.is_empty() {
        return Err(BodyStop::Exhausted);
    }
    Ok((
        Bus::new(vec![bus.nets[0]]),
        Bus::new(bus.nets[1..].to_vec()),
    ))
}

/// The rest, and the highest net. MorphoHDL's `HSLICE(x, ONE)`.
pub fn take_high_bit(bus: &Bus) -> Result<(Bus, Bus), BodyStop> {
    if bus.is_empty() {
        return Err(BodyStop::Exhausted);
    }
    let last = bus.width() - 1;
    Ok((
        Bus::new(bus.nets[..last].to_vec()),
        Bus::new(vec![bus.nets[last]]),
    ))
}

/// Take as many low nets as the reference bus is wide. MorphoHDL's `LSLICE`.
pub fn low_slice(bus: &Bus, reference: &Bus) -> Result<(Bus, Bus), BodyStop> {
    let count = reference.width();
    if bus.width() < count {
        return Err(BodyStop::Exhausted);
    }
    Ok((
        Bus::new(bus.nets[..count].to_vec()),
        Bus::new(bus.nets[count..].to_vec()),
    ))
}

// ===============================================================================================
// primitives

/// A primitive combinational element. Each is one lookup table over its pins, applied per bit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GateKind {
    Not,
    And,
    Or,
    Xor,
    /// Three-input parity. The full adder's sum.
    Xor3,
    /// Three-input majority. The full adder's carry.
    Maj3,
    /// `sel ? high : low`, pins ordered `(low, high, sel)`.
    Mux2,
}

impl GateKind {
    pub fn arity(self) -> usize {
        match self {
            Self::Not => 1,
            Self::And | Self::Or | Self::Xor => 2,
            Self::Xor3 | Self::Maj3 | Self::Mux2 => 3,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Self::Not => "not",
            Self::And => "and",
            Self::Or => "or",
            Self::Xor => "xor",
            Self::Xor3 => "xor3",
            Self::Maj3 => "maj3",
            Self::Mux2 => "mux2",
        }
    }

    /// Exact bit evaluation. Inputs are `0` or `1`; anything else is a defect in the caller.
    pub fn eval(self, pins: &[u8]) -> u8 {
        match self {
            Self::Not => 1 - pins[0],
            Self::And => pins[0] & pins[1],
            Self::Or => pins[0] | pins[1],
            Self::Xor => pins[0] ^ pins[1],
            Self::Xor3 => pins[0] ^ pins[1] ^ pins[2],
            Self::Maj3 => (pins[0] & pins[1]) | (pins[0] & pins[2]) | (pins[1] & pins[2]),
            Self::Mux2 => {
                if pins[2] == 1 {
                    pins[1]
                } else {
                    pins[0]
                }
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GateId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gate {
    pub id: GateId,
    pub kind: GateKind,
    /// One entry per pin. Two pins carrying the same net is legal and produces parallel 1-cells.
    pub inputs: Vec<NetId>,
    pub output: NetId,
    pub owner: InstanceId,
    /// The rule and label that emitted it. This is the **description**, and it does not grow.
    pub site: (RuleName, &'static str),
}

// ===============================================================================================
// rules

pub type RuleName = &'static str;

/// A rule's declared output shape, structurally. There is no numeral here and no width.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutShape {
    /// As wide as the argument at this position.
    LikeArg(usize),
    /// One net. The atom of the material, not a size.
    Bit,
}

impl OutShape {
    fn width(self, args: &[Bus]) -> Result<usize, GrowthRefusal> {
        match self {
            Self::LikeArg(index) => args
                .get(index)
                .map(Bus::width)
                .ok_or(GrowthRefusal::OutShapeArgMissing { index }),
            Self::Bit => Ok(1),
        }
    }
}

/// What is taken when a body's material is exhausted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fallback {
    /// Retry at another rule. MorphoHDL's `fallback=full_adder`.
    Rule(RuleName),
    /// Return the argument at this position unchanged. MorphoHDL's `fallback=0`. **This grows
    /// nothing**, and it is the negative pole of the whole construction.
    Identity(usize),
}

type BodyFn = fn(&mut Body<'_, '_>, &[Bus]) -> Result<Vec<Bus>, BodyStop>;

/// One recursive cell.
#[derive(Clone, Copy)]
pub struct Rule {
    pub name: RuleName,
    pub outs: &'static [OutShape],
    pub fallback: Option<Fallback>,
    body: BodyFn,
}

impl std::fmt::Debug for Rule {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Rule")
            .field("name", &self.name)
            .field("outs", &self.outs)
            .field("fallback", &self.fallback)
            .finish()
    }
}

/// The whole description. It is `&'static` in every rule and constant in every width.
#[derive(Clone, Debug, Default)]
pub struct RuleTable {
    rules: BTreeMap<RuleName, Rule>,
}

impl RuleTable {
    pub fn insert(&mut self, rule: Rule) {
        self.rules.insert(rule.name, rule);
    }

    pub fn get(&self, name: RuleName) -> Option<&Rule> {
        self.rules.get(name)
    }

    pub fn names(&self) -> Vec<RuleName> {
        self.rules.keys().copied().collect()
    }

    /// The static half of the description length: rules carried and output shapes declared.
    pub fn description(&self) -> (usize, usize) {
        (
            self.rules.len(),
            self.rules.values().map(|rule| rule.outs.len()).sum(),
        )
    }
}

// ===============================================================================================
// instances and lineage

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InstanceId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instance {
    pub id: InstanceId,
    /// The rule that was asked for.
    pub requested: RuleName,
    /// The rule that actually fired, after the fallback chain resolved.
    pub fired: RuleName,
    pub parent: Option<InstanceId>,
    pub inputs: Vec<Bus>,
    pub outputs: Vec<Bus>,
    pub children: Vec<InstanceId>,
    pub gates: Vec<GateId>,
    /// Lineage depth. A measurement, never consulted in the termination path.
    pub depth: u32,
    /// The material exhausted and a fallback was taken.
    pub fell_back: bool,
    /// The fallback was [`Fallback::Identity`], so nothing at all was grown here.
    pub grew_nothing: bool,
}

/// One line of the intermediate morphology. Two schedules differ here visibly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceStep {
    pub step: usize,
    pub instance: InstanceId,
    pub requested: RuleName,
    pub fired: RuleName,
    pub in_widths: Vec<usize>,
    pub gates: usize,
    pub children: usize,
    pub fell_back: bool,
}

impl TraceStep {
    pub fn line(&self) -> String {
        format!(
            "{:>4}  i{:<4} {:<14} -> {:<14} in {:?}  gates {:>3}  children {:>2}{}",
            self.step,
            self.instance.0,
            self.requested,
            self.fired,
            self.in_widths,
            self.gates,
            self.children,
            if self.fell_back { "  FALLBACK" } else { "" }
        )
    }
}

// ===============================================================================================
// refusals

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum GrowthRefusal {
    #[error("no rule named `{0}`")]
    UnknownRule(RuleName),
    #[error("rule `{rule}` exhausted its material and declares no fallback")]
    NoFallback { rule: RuleName },
    #[error("rule `{rule}` returned {returned} buses but declares {declared}")]
    OutShapeArity {
        rule: RuleName,
        returned: usize,
        declared: usize,
    },
    #[error(
        "rule `{rule}` output {position} is {returned} wide, its declared shape says {declared}"
    )]
    OutShapeContract {
        rule: RuleName,
        position: usize,
        returned: usize,
        declared: usize,
    },
    #[error("an output shape names argument {index}, which was not supplied")]
    OutShapeArgMissing { index: usize },
    #[error("gate `{kind}` was handed {supplied} operands and takes {arity}")]
    GateArity {
        kind: &'static str,
        supplied: usize,
        arity: usize,
    },
    #[error("gate `{kind}` was handed operands of widths {widths:?}, which do not broadcast")]
    GateBroadcast {
        kind: &'static str,
        widths: Vec<usize>,
    },
    #[error("the material supplied is {supplied} buses of widths {widths:?}, and the growth takes {expected}")]
    MaterialArity {
        supplied: usize,
        expected: usize,
        widths: Vec<usize>,
    },
    #[error("the grown net graph carries a cycle, so it is not combinational")]
    CombinationalLoop,
    #[error("net {net} carries no value, so the evaluation is incomplete")]
    UnvaluedNet { net: u64 },
    #[error("the reconvergence family would carry {faces} faces, past the declared aperture {aperture}")]
    FaceApertureExceeded { faces: usize, aperture: usize },
    #[error("founding the complex: {0}")]
    Algebraic(String),
}

impl From<CausalAlgebraicError> for GrowthRefusal {
    fn from(error: CausalAlgebraicError) -> Self {
        Self::Algebraic(error.to_string())
    }
}

// ===============================================================================================
// the schedule, which is a receiver

/// The order in which pending instances are expanded.
///
/// MorphoHDL carries two; a third is included because a two-point sweep cannot show that a
/// coincidence between two of them is a property of the material rather than of the sweep.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Schedule {
    /// Oldest pending instance first. MorphoHDL's index order.
    Instantiation,
    /// The pending instance with the most material on its inputs; ties to the earliest.
    /// MorphoHDL's largest-first.
    WidestFirst,
    /// Newest pending instance first. This is what Python's own call stack does, so it is the one
    /// schedule MorphoHDL cannot vary away from.
    Deepest,
}

impl Schedule {
    pub const ALL: [Self; 3] = [Self::Instantiation, Self::WidestFirst, Self::Deepest];

    pub fn name(self) -> &'static str {
        match self {
            Self::Instantiation => "instantiation",
            Self::WidestFirst => "widest-first",
            Self::Deepest => "deepest",
        }
    }

    fn take(self, pending: &mut Vec<InstanceId>, material: &dyn Fn(InstanceId) -> usize) -> Option<InstanceId> {
        if pending.is_empty() {
            return None;
        }
        let at = match self {
            Self::Instantiation => 0,
            Self::Deepest => pending.len() - 1,
            Self::WidestFirst => pending
                .iter()
                .enumerate()
                .max_by_key(|(_, id)| (material(**id), std::cmp::Reverse(id.0)))
                .map(|(index, _)| index)
                .expect("pending is not empty"),
        };
        Some(pending.remove(at))
    }
}

// ===============================================================================================
// the grower

struct Grower {
    next_net: u64,
    /// Union-find over nets. A rule's declared output nets are placeholders until the body that
    /// fills them returns; then they are the same net. Index is `id - 1`.
    alias: Vec<u64>,
    gates: Vec<Gate>,
    instances: Vec<Instance>,
    pending: Vec<InstanceId>,
    sites: BTreeSet<(RuleName, &'static str)>,
}

impl Grower {
    fn fresh_net(&mut self) -> NetId {
        self.next_net += 1;
        self.alias.push(self.next_net);
        NetId(self.next_net)
    }

    fn fresh_bus(&mut self, width: usize) -> Bus {
        Bus::new((0..width).map(|_| self.fresh_net()).collect())
    }

    fn root_of(&mut self, net: NetId) -> NetId {
        let mut current = net.0;
        while self.alias[(current - 1) as usize] != current {
            let grand = self.alias[(self.alias[(current - 1) as usize] - 1) as usize];
            self.alias[(current - 1) as usize] = grand;
            current = grand;
        }
        NetId(current)
    }

    fn unify(&mut self, left: NetId, right: NetId) {
        let left = self.root_of(left);
        let right = self.root_of(right);
        if left == right {
            return;
        }
        // The smaller identifier wins, so resolution is a function of the growth and not of the
        // order the aliases happened to be recorded in.
        let (keep, drop) = if left.0 < right.0 {
            (left, right)
        } else {
            (right, left)
        };
        self.alias[(drop.0 - 1) as usize] = keep.0;
    }

    fn resolve_bus(&mut self, bus: &Bus) -> Bus {
        Bus::new(bus.nets.iter().map(|net| self.root_of(*net)).collect())
    }
}

/// The context a rule body is handed. It is the only way a body can found anything.
pub struct Body<'g, 't> {
    grower: &'g mut Grower,
    table: &'t RuleTable,
    instance: InstanceId,
    rule: RuleName,
    depth: u32,
}

impl Body<'_, '_> {
    /// Found one primitive per bit, broadcasting any width-one operand across the rest.
    ///
    /// This is MorphoHDL's `run_lut`: `n = max(len(a) for a in args)`, and a width-one operand is
    /// read at index zero for every bit. It is how a carry or a select bit reaches a whole bus.
    pub fn gate(
        &mut self,
        label: &'static str,
        kind: GateKind,
        operands: &[&Bus],
    ) -> Result<Bus, BodyStop> {
        if operands.len() != kind.arity() {
            return Err(BodyStop::Refused(GrowthRefusal::GateArity {
                kind: kind.name(),
                supplied: operands.len(),
                arity: kind.arity(),
            }));
        }
        let widths: Vec<usize> = operands.iter().map(|bus| bus.width()).collect();
        let wide = widths.iter().copied().max().unwrap_or(0);
        if wide == 0 || widths.iter().any(|width| *width != wide && *width != 1) {
            return Err(BodyStop::Refused(GrowthRefusal::GateBroadcast {
                kind: kind.name(),
                widths,
            }));
        }
        self.grower.sites.insert((self.rule, label));
        let mut outputs = Vec::with_capacity(wide);
        for bit in 0..wide {
            let pins: Vec<NetId> = operands
                .iter()
                .map(|bus| {
                    if bus.width() == 1 {
                        bus.nets[0]
                    } else {
                        bus.nets[bit]
                    }
                })
                .collect();
            let output = self.grower.fresh_net();
            let id = GateId(self.grower.gates.len() as u64 + 1);
            self.grower.gates.push(Gate {
                id,
                kind,
                inputs: pins,
                output,
                owner: self.instance,
                site: (self.rule, label),
            });
            self.grower.instances[(self.instance.0 - 1) as usize]
                .gates
                .push(id);
            outputs.push(output);
        }
        Ok(Bus::new(outputs))
    }

    /// Instantiate a child. Its outputs are allocated **now**, from the rule's declared shape, and
    /// its body is deferred to the schedule. That deferral is the whole reason a schedule exists.
    pub fn call(
        &mut self,
        label: &'static str,
        rule: RuleName,
        arguments: &[&Bus],
    ) -> Result<Vec<Bus>, BodyStop> {
        let declared = self
            .table
            .get(rule)
            .ok_or(BodyStop::Refused(GrowthRefusal::UnknownRule(rule)))?
            .outs;
        self.grower.sites.insert((self.rule, label));
        let arguments: Vec<Bus> = arguments.iter().map(|bus| (*bus).clone()).collect();
        let mut outputs = Vec::with_capacity(declared.len());
        for shape in declared {
            let width = shape
                .width(&arguments)
                .map_err(|refusal| BodyStop::Refused(refusal))?;
            outputs.push(self.grower.fresh_bus(width));
        }
        let id = InstanceId(self.grower.instances.len() as u64 + 1);
        self.grower.instances.push(Instance {
            id,
            requested: rule,
            fired: rule,
            parent: Some(self.instance),
            inputs: arguments,
            outputs: outputs.clone(),
            children: Vec::new(),
            gates: Vec::new(),
            depth: self.depth + 1,
            fell_back: false,
            grew_nothing: false,
        });
        self.grower.instances[(self.instance.0 - 1) as usize]
            .children
            .push(id);
        self.grower.pending.push(id);
        Ok(outputs)
    }
}

/// Everything one growth produced.
#[derive(Clone, Debug)]
pub struct Growth {
    pub schedule: Schedule,
    pub root: InstanceId,
    pub root_outputs: Vec<Bus>,
    /// Indexed by `id - 1`.
    pub instances: Vec<Instance>,
    pub gates: Vec<Gate>,
    /// Primary inputs, in the order they were handed to the root.
    pub primary_inputs: Vec<Bus>,
    /// The order the schedule actually expanded in. This is the intermediate morphology.
    pub trace: Vec<TraceStep>,
    /// Distinct `(rule, label)` emission sites that fired. **This is the description length.**
    pub sites: BTreeSet<(RuleName, &'static str)>,
    /// Every live net, ascending.
    pub nets: Vec<NetId>,
}

impl Growth {
    pub fn gate_count(&self) -> usize {
        self.gates.len()
    }

    pub fn instance_count(&self) -> usize {
        self.instances.len()
    }

    pub fn net_count(&self) -> usize {
        self.nets.len()
    }

    pub fn trace_lines(&self) -> Vec<String> {
        self.trace.iter().map(TraceStep::line).collect()
    }

    /// The lineage depth actually reached. A measurement of shape: ripple-carry is linear in the
    /// width and Brent-Kung is logarithmic, from the same discipline.
    pub fn depth(&self) -> u32 {
        self.instances
            .iter()
            .map(|instance| instance.depth)
            .max()
            .unwrap_or(0)
    }

    /// Which rule fired on which input width, and how often. If every rule fires at exactly one
    /// width this is macro expansion and not growth.
    pub fn rule_reuse(&self) -> BTreeMap<(RuleName, usize), usize> {
        let mut table = BTreeMap::new();
        for instance in &self.instances {
            let width = instance
                .inputs
                .first()
                .map(Bus::width)
                .unwrap_or(0);
            *table.entry((instance.fired, width)).or_insert(0) += 1;
        }
        table
    }

    /// The number of distinct input widths a rule fired on.
    pub fn widths_of(&self, rule: RuleName) -> BTreeSet<usize> {
        self.instances
            .iter()
            .filter(|instance| instance.fired == rule)
            .map(|instance| instance.inputs.first().map(Bus::width).unwrap_or(0))
            .collect()
    }
}

/// Grow one cell under one schedule.
///
/// `argument_widths` supplies the **material**, not a parameter: it is the length of what the caller
/// hands over, exactly as a bus arriving at a port would be.
pub fn grow(
    table: &RuleTable,
    root_rule: RuleName,
    argument_widths: &[usize],
    schedule: Schedule,
) -> Result<Growth, GrowthRefusal> {
    let declared = table
        .get(root_rule)
        .ok_or(GrowthRefusal::UnknownRule(root_rule))?
        .outs;

    let mut grower = Grower {
        next_net: 0,
        alias: Vec::new(),
        gates: Vec::new(),
        instances: Vec::new(),
        pending: Vec::new(),
        sites: BTreeSet::new(),
    };

    let primary_inputs: Vec<Bus> = argument_widths
        .iter()
        .map(|width| grower.fresh_bus(*width))
        .collect();
    let mut root_outputs = Vec::with_capacity(declared.len());
    for shape in declared {
        let width = shape.width(&primary_inputs)?;
        root_outputs.push(grower.fresh_bus(width));
    }

    let root = InstanceId(1);
    grower.instances.push(Instance {
        id: root,
        requested: root_rule,
        fired: root_rule,
        parent: None,
        inputs: primary_inputs.clone(),
        outputs: root_outputs.clone(),
        children: Vec::new(),
        gates: Vec::new(),
        depth: 0,
        fell_back: false,
        grew_nothing: false,
    });
    grower.pending.push(root);

    let mut trace = Vec::new();
    let mut step = 0usize;
    loop {
        let material = |id: InstanceId| -> usize {
            grower.instances[(id.0 - 1) as usize]
                .inputs
                .iter()
                .map(Bus::width)
                .sum()
        };
        let Some(id) = ({
            // The closure borrows `grower` immutably; take the choice and drop the borrow.
            let mut pending = std::mem::take(&mut grower.pending);
            let chosen = schedule.take(&mut pending, &material);
            grower.pending = pending;
            chosen
        }) else {
            break;
        };
        let record = expand(&mut grower, table, id)?;
        trace.push(TraceStep {
            step,
            instance: id,
            requested: record.0,
            fired: record.1,
            in_widths: record.2,
            gates: record.3,
            children: record.4,
            fell_back: record.5,
        });
        step += 1;
    }

    // Resolve every placeholder. After this, a net identifier names one net.
    let gates: Vec<Gate> = grower
        .gates
        .clone()
        .into_iter()
        .map(|gate| Gate {
            inputs: gate
                .inputs
                .iter()
                .map(|net| grower.root_of(*net))
                .collect(),
            output: grower.root_of(gate.output),
            ..gate
        })
        .collect();
    let instances: Vec<Instance> = grower
        .instances
        .clone()
        .into_iter()
        .map(|instance| Instance {
            inputs: instance
                .inputs
                .iter()
                .map(|bus| grower.resolve_bus(bus))
                .collect(),
            outputs: instance
                .outputs
                .iter()
                .map(|bus| grower.resolve_bus(bus))
                .collect(),
            ..instance
        })
        .collect();
    let primary_inputs: Vec<Bus> = primary_inputs
        .iter()
        .map(|bus| grower.resolve_bus(bus))
        .collect();
    let root_outputs: Vec<Bus> = root_outputs
        .iter()
        .map(|bus| grower.resolve_bus(bus))
        .collect();

    let mut nets: BTreeSet<NetId> = BTreeSet::new();
    for bus in &primary_inputs {
        nets.extend(bus.nets().iter().copied());
    }
    for gate in &gates {
        nets.extend(gate.inputs.iter().copied());
        nets.insert(gate.output);
    }
    for instance in &instances {
        for bus in instance.inputs.iter().chain(&instance.outputs) {
            nets.extend(bus.nets().iter().copied());
        }
    }

    Ok(Growth {
        schedule,
        root,
        root_outputs,
        instances,
        gates,
        primary_inputs,
        trace,
        sites: grower.sites,
        nets: nets.into_iter().collect(),
    })
}

type ExpansionRecord = (RuleName, RuleName, Vec<usize>, usize, usize, bool);

/// Run one instance's body, unwinding to its fallback if the material is exhausted.
fn expand(
    grower: &mut Grower,
    table: &RuleTable,
    id: InstanceId,
) -> Result<ExpansionRecord, GrowthRefusal> {
    let index = (id.0 - 1) as usize;
    let requested = grower.instances[index].requested;
    let inputs = grower.instances[index].inputs.clone();
    let declared_outputs = grower.instances[index].outputs.clone();
    let depth = grower.instances[index].depth;
    let in_widths: Vec<usize> = inputs.iter().map(Bus::width).collect();

    let mut rule_name = requested;
    let mut fell_back = false;
    loop {
        let rule = *table
            .get(rule_name)
            .ok_or(GrowthRefusal::UnknownRule(rule_name))?;

        // The marks. A body that exhausts its material leaves nothing behind, including nets.
        let net_mark = grower.next_net;
        let gate_mark = grower.gates.len();
        let instance_mark = grower.instances.len();
        let pending_mark = grower.pending.len();
        let child_mark = grower.instances[index].children.len();
        let gate_slot_mark = grower.instances[index].gates.len();

        let outcome = {
            let mut body = Body {
                grower,
                table,
                instance: id,
                rule: rule.name,
                depth,
            };
            (rule.body)(&mut body, &inputs)
        };

        match outcome {
            Ok(returned) => {
                if returned.len() != rule.outs.len() {
                    return Err(GrowthRefusal::OutShapeArity {
                        rule: rule.name,
                        returned: returned.len(),
                        declared: rule.outs.len(),
                    });
                }
                for (position, (given, slot)) in
                    returned.iter().zip(&declared_outputs).enumerate()
                {
                    if given.width() != slot.width() {
                        return Err(GrowthRefusal::OutShapeContract {
                            rule: rule.name,
                            position,
                            returned: given.width(),
                            declared: slot.width(),
                        });
                    }
                    for (left, right) in slot.nets().iter().zip(given.nets()) {
                        grower.unify(*left, *right);
                    }
                }
                let gates = grower.instances[index].gates.len();
                let children = grower.instances[index].children.len();
                let instance = &mut grower.instances[index];
                instance.fired = rule.name;
                instance.fell_back = fell_back;
                instance.grew_nothing = gates == 0 && children == 0;
                return Ok((requested, rule.name, in_widths, gates, children, fell_back));
            }
            Err(BodyStop::Refused(refusal)) => return Err(refusal),
            Err(BodyStop::Exhausted) => {
                // Roll the staged work back whole. Nothing a refused body founded survives it.
                grower.next_net = net_mark;
                grower.alias.truncate(net_mark as usize);
                grower.gates.truncate(gate_mark);
                grower.instances.truncate(instance_mark);
                grower.pending.truncate(pending_mark);
                grower.instances[index].children.truncate(child_mark);
                grower.instances[index].gates.truncate(gate_slot_mark);

                fell_back = true;
                match rule.fallback {
                    Some(Fallback::Rule(next)) => {
                        rule_name = next;
                    }
                    Some(Fallback::Identity(position)) => {
                        let source = inputs
                            .get(position)
                            .ok_or(GrowthRefusal::OutShapeArgMissing { index: position })?
                            .clone();
                        if declared_outputs.len() != 1 {
                            return Err(GrowthRefusal::OutShapeArity {
                                rule: rule.name,
                                returned: 1,
                                declared: declared_outputs.len(),
                            });
                        }
                        if source.width() != declared_outputs[0].width() {
                            return Err(GrowthRefusal::OutShapeContract {
                                rule: rule.name,
                                position: 0,
                                returned: source.width(),
                                declared: declared_outputs[0].width(),
                            });
                        }
                        for (left, right) in
                            declared_outputs[0].nets().iter().zip(source.nets())
                        {
                            grower.unify(*left, *right);
                        }
                        let instance = &mut grower.instances[index];
                        instance.fired = rule.name;
                        instance.fell_back = true;
                        instance.grew_nothing = true;
                        return Ok((requested, rule.name, in_widths, 0, 0, true));
                    }
                    None => return Err(GrowthRefusal::NoFallback { rule: rule.name }),
                }
            }
        }
    }
}

// ===============================================================================================
// the cells

fn full_adder_body(body: &mut Body<'_, '_>, args: &[Bus]) -> Result<Vec<Bus>, BodyStop> {
    let sum = body.gate("sum", GateKind::Xor3, &[&args[0], &args[1], &args[2]])?;
    let carry = body.gate("carry", GateKind::Maj3, &[&args[0], &args[1], &args[2]])?;
    Ok(vec![sum, carry])
}

fn ripple_adder_body(body: &mut Body<'_, '_>, args: &[Bus]) -> Result<Vec<Bus>, BodyStop> {
    let (a_low, a_high) = split(&args[0])?;
    let (b_low, b_high) = split(&args[1])?;
    let low = body.call("low", "ripple-adder", &[&a_low, &b_low, &args[2]])?;
    let high = body.call("high", "ripple-adder", &[&a_high, &b_high, &low[1]])?;
    Ok(vec![cat(&[&low[0], &high[0]]), high[1].clone()])
}

fn carry_operator_body(body: &mut Body<'_, '_>, args: &[Bus]) -> Result<Vec<Bus>, BodyStop> {
    let propagated = body.gate("propagated", GateKind::And, &[&args[0], &args[2]])?;
    let carry = body.gate("carry", GateKind::Or, &[&args[1], &propagated])?;
    Ok(vec![carry])
}

fn brent_kung_base_body(body: &mut Body<'_, '_>, args: &[Bus]) -> Result<Vec<Bus>, BodyStop> {
    let propagate = body.gate("propagate", GateKind::Xor, &[&args[0], &args[1]])?;
    let generate = body.gate("generate", GateKind::And, &[&args[0], &args[1]])?;
    let sum = body.gate("sum", GateKind::Xor, &[&propagate, &args[2]])?;
    Ok(vec![sum, propagate, generate])
}

fn brent_kung_recursive_body(body: &mut Body<'_, '_>, args: &[Bus]) -> Result<Vec<Bus>, BodyStop> {
    let (a_low, a_high) = split(&args[0])?;
    let (b_low, b_high) = split(&args[1])?;
    let low = body.call("low", "brent-kung-recursive", &[&a_low, &b_low, &args[2]])?;
    let middle = body.call("middle-carry", "carry-operator", &[&low[1], &low[2], &args[2]])?;
    let high = body.call(
        "high",
        "brent-kung-recursive",
        &[&a_high, &b_high, &middle[0]],
    )?;
    let propagate = body.gate("propagate", GateKind::And, &[&low[1], &high[1]])?;
    let generate = body.call("group-carry", "carry-operator", &[&high[1], &high[2], &low[2]])?;
    Ok(vec![
        cat(&[&low[0], &high[0]]),
        propagate,
        generate[0].clone(),
    ])
}

fn brent_kung_adder_body(body: &mut Body<'_, '_>, args: &[Bus]) -> Result<Vec<Bus>, BodyStop> {
    let group = body.call(
        "group",
        "brent-kung-recursive",
        &[&args[0], &args[1], &args[2]],
    )?;
    let carry = body.call("carry-out", "carry-operator", &[&group[1], &group[2], &args[2]])?;
    Ok(vec![group[0].clone(), carry[0].clone()])
}

fn multiplexer_body(body: &mut Body<'_, '_>, args: &[Bus]) -> Result<Vec<Bus>, BodyStop> {
    let (rest, high) = take_high_bit(&args[1])?;
    let (low_half, high_half) = split(&args[0])?;
    let low = body.call("low", "multiplexer", &[&low_half, &rest])?;
    let high_side = body.call("high", "multiplexer", &[&high_half, &rest])?;
    let selected = body.gate("select", GateKind::Mux2, &[&low[0], &high_side[0], &high])?;
    Ok(vec![selected])
}

fn parity_tree_body(body: &mut Body<'_, '_>, args: &[Bus]) -> Result<Vec<Bus>, BodyStop> {
    let (low_half, high_half) = split(&args[0])?;
    let low = body.call("low", "parity-tree", &[&low_half])?;
    let high = body.call("high", "parity-tree", &[&high_half])?;
    let folded = body.gate("fold", GateKind::Xor, &[&low[0], &high[0]])?;
    Ok(vec![folded])
}

/// The cells. One `&'static` table, shared by every width in this crate.
///
/// Four shapes from one discipline: a linear-depth carry chain, a logarithmic-depth prefix adder,
/// a selection tree, and a reduction tree. Two of them declare [`Fallback::Rule`] and two declare
/// [`Fallback::Identity`], which is the pole that grows nothing.
pub fn standard_cells() -> RuleTable {
    let mut table = RuleTable::default();
    table.insert(Rule {
        name: "full-adder",
        outs: &[OutShape::LikeArg(0), OutShape::LikeArg(2)],
        fallback: None,
        body: full_adder_body,
    });
    table.insert(Rule {
        name: "ripple-adder",
        outs: &[OutShape::LikeArg(0), OutShape::LikeArg(2)],
        fallback: Some(Fallback::Rule("full-adder")),
        body: ripple_adder_body,
    });
    table.insert(Rule {
        name: "carry-operator",
        outs: &[OutShape::LikeArg(1)],
        fallback: None,
        body: carry_operator_body,
    });
    table.insert(Rule {
        name: "brent-kung-base",
        outs: &[OutShape::LikeArg(0), OutShape::LikeArg(2), OutShape::LikeArg(2)],
        fallback: None,
        body: brent_kung_base_body,
    });
    table.insert(Rule {
        name: "brent-kung-recursive",
        outs: &[OutShape::LikeArg(0), OutShape::LikeArg(2), OutShape::LikeArg(2)],
        fallback: Some(Fallback::Rule("brent-kung-base")),
        body: brent_kung_recursive_body,
    });
    table.insert(Rule {
        name: "brent-kung-adder",
        outs: &[OutShape::LikeArg(0), OutShape::LikeArg(2)],
        fallback: None,
        body: brent_kung_adder_body,
    });
    table.insert(Rule {
        name: "multiplexer",
        outs: &[OutShape::Bit],
        fallback: Some(Fallback::Identity(0)),
        body: multiplexer_body,
    });
    table.insert(Rule {
        name: "parity-tree",
        outs: &[OutShape::Bit],
        fallback: Some(Fallback::Identity(0)),
        body: parity_tree_body,
    });
    table
}

// ===============================================================================================
// the netlist, canonically

/// A canonical form of the grown netlist, independent of every identifier the schedule chose.
///
/// Built by hash-consing, not hashing: each net is interned against the tuple
/// `(gate kind, interned inputs)` processed in topological levels with the definitions sorted, so
/// two growths carry byte-identical forms exactly when their netlists are the same circuit under a
/// renaming. There is no digest and no collision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalNetlist {
    /// One entry per net, sorted. `(level, definition)`.
    pub nets: Vec<(usize, String)>,
    /// The canonical form of each root output bus, in order.
    pub outputs: Vec<Vec<String>>,
}

pub fn canonical_netlist(growth: &Growth) -> Result<CanonicalNetlist, GrowthRefusal> {
    let mut driver: BTreeMap<NetId, &Gate> = BTreeMap::new();
    for gate in &growth.gates {
        driver.insert(gate.output, gate);
    }
    let mut port: BTreeMap<NetId, String> = BTreeMap::new();
    for (position, bus) in growth.primary_inputs.iter().enumerate() {
        for (bit, net) in bus.nets().iter().enumerate() {
            port.insert(*net, format!("in{position}[{bit}]"));
        }
    }

    // Levels. A net with no driver and no port is a dangling constant and is levelled at zero.
    let mut level: BTreeMap<NetId, usize> = BTreeMap::new();
    let mut settled = 0usize;
    let total = growth.nets.len();
    let mut guard = 0usize;
    while settled < total {
        let mut progressed = false;
        for net in &growth.nets {
            if level.contains_key(net) {
                continue;
            }
            match driver.get(net) {
                None => {
                    level.insert(*net, 0);
                    settled += 1;
                    progressed = true;
                }
                Some(gate) => {
                    if gate.inputs.iter().all(|pin| level.contains_key(pin)) {
                        let deepest = gate
                            .inputs
                            .iter()
                            .map(|pin| level[pin])
                            .max()
                            .unwrap_or(0);
                        level.insert(*net, deepest + 1);
                        settled += 1;
                        progressed = true;
                    }
                }
            }
        }
        guard += 1;
        if !progressed || guard > total + 2 {
            return Err(GrowthRefusal::CombinationalLoop);
        }
    }

    let deepest = level.values().copied().max().unwrap_or(0);
    let mut form: BTreeMap<NetId, String> = BTreeMap::new();
    let mut intern: BTreeMap<String, usize> = BTreeMap::new();
    for stage in 0..=deepest {
        let mut definitions: Vec<(NetId, String)> = Vec::new();
        for net in &growth.nets {
            if level[net] != stage {
                continue;
            }
            let definition = match driver.get(net) {
                Some(gate) => {
                    let pins: Vec<String> = gate
                        .inputs
                        .iter()
                        .map(|pin| form[pin].clone())
                        .collect();
                    format!("{}({})", gate.kind.name(), pins.join(","))
                }
                None => port
                    .get(net)
                    .cloned()
                    .unwrap_or_else(|| "float".to_owned()),
            };
            definitions.push((*net, definition));
        }
        definitions.sort_by(|left, right| left.1.cmp(&right.1));
        for (net, definition) in definitions {
            let next = intern.len();
            let key = *intern.entry(definition).or_insert(next);
            form.insert(net, format!("#{key}"));
        }
    }

    let mut nets: Vec<(usize, String)> = growth
        .nets
        .iter()
        .map(|net| (level[net], form[net].clone()))
        .collect();
    nets.sort();
    let outputs = growth
        .root_outputs
        .iter()
        .map(|bus| bus.nets().iter().map(|net| form[net].clone()).collect())
        .collect();
    Ok(CanonicalNetlist { nets, outputs })
}

/// Evaluate the grown circuit on exact bits. Inputs and outputs are `0`/`1`, never a scalar that
/// governs anything: this is a measurement of what was grown.
///
/// An output net that never took a value is a refusal, not a zero. A silent default here would make
/// a mis-wired growth look like a circuit that computes zero.
pub fn evaluate(growth: &Growth, inputs: &[Vec<u8>]) -> Result<Vec<Vec<u8>>, GrowthRefusal> {
    if inputs.len() != growth.primary_inputs.len()
        || growth
            .primary_inputs
            .iter()
            .zip(inputs)
            .any(|(bus, bits)| bus.width() != bits.len())
    {
        return Err(GrowthRefusal::MaterialArity {
            supplied: inputs.len(),
            expected: growth.primary_inputs.len(),
            widths: inputs.iter().map(Vec::len).collect(),
        });
    }
    let mut value: BTreeMap<NetId, u8> = BTreeMap::new();
    for (bus, bits) in growth.primary_inputs.iter().zip(inputs) {
        for (net, bit) in bus.nets().iter().zip(bits) {
            value.insert(*net, *bit & 1);
        }
    }
    let mut remaining: Vec<&Gate> = growth.gates.iter().collect();
    // One settling round retires at least one gate, so the total number of rounds is bounded by the
    // gate count. Bounding it by the surviving count instead would refuse a deep carry chain.
    let rounds = growth.gates.len() + 1;
    let mut guard = 0usize;
    while !remaining.is_empty() {
        let before = remaining.len();
        remaining.retain(|gate| {
            if gate.inputs.iter().all(|pin| value.contains_key(pin)) {
                let pins: Vec<u8> = gate.inputs.iter().map(|pin| value[pin]).collect();
                value.insert(gate.output, gate.kind.eval(&pins));
                false
            } else {
                true
            }
        });
        guard += 1;
        if remaining.len() == before || guard > rounds {
            return Err(GrowthRefusal::CombinationalLoop);
        }
    }
    let mut returned = Vec::with_capacity(growth.root_outputs.len());
    for bus in &growth.root_outputs {
        let mut bits = Vec::with_capacity(bus.width());
        for net in bus.nets() {
            bits.push(
                value
                    .get(net)
                    .copied()
                    .ok_or(GrowthRefusal::UnvaluedNet { net: net.0 })?,
            );
        }
        returned.push(bits);
    }
    Ok(returned)
}

// ===============================================================================================
// the complex

/// Which face families a reading founds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FaceFamily {
    /// A parent's coarse arc against the refinement that replaced it. The attaching map is the
    /// lineage.
    Division,
    /// Two paths leaving one net and meeting again.
    Reconvergence,
}

/// The declared aperture of a reading.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ComplexAperture {
    pub division: bool,
    pub reconvergence: bool,
    /// The reconvergence family is quadratic in fan-out. Past this it refuses rather than truncates.
    pub face_aperture: usize,
}

impl ComplexAperture {
    pub const DIVISION: Self = Self {
        division: true,
        reconvergence: false,
        face_aperture: 65_536,
    };
    pub const RECONVERGENCE: Self = Self {
        division: false,
        reconvergence: true,
        face_aperture: 65_536,
    };
    pub const BOTH: Self = Self {
        division: true,
        reconvergence: true,
        face_aperture: 65_536,
    };
}

/// One conduction arc: a 1-cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arc {
    pub cell: CausalCellId,
    pub tail: NetId,
    pub head: NetId,
    /// The gate that carries it, if it is a pin.
    pub gate: Option<GateId>,
    /// The instance it belongs to. A pin belongs to the instance that founded its gate.
    pub owner: InstanceId,
    pub name: String,
}

/// The complex a growth founded, with the populations named.
#[derive(Clone, Debug)]
pub struct GrownComplex {
    pub complex: GradedCausalComplex,
    pub aperture: ComplexAperture,
    pub net_cells: BTreeMap<NetId, CausalCellId>,
    pub arcs: Vec<Arc>,
    pub division_faces: usize,
    pub reconvergence_faces: usize,
    /// Division faces whose parent arc carries a coefficient above one. Multiplicity that was
    /// **grown**, not authored.
    pub division_faces_with_multiplicity: usize,
    /// The largest coefficient any face carries.
    pub largest_face_coefficient: BigUint,
    /// Instance arcs that were degenerate because the instance grew nothing. The negative pole,
    /// counted.
    pub degenerate_arcs: usize,
}

/// A local DAG over nets, whose edges are already-founded 1-cells.
struct LocalGraph {
    nodes: Vec<NetId>,
    index: BTreeMap<NetId, usize>,
    /// `(tail index, head index, arc position in `arcs`)`.
    edges: Vec<(usize, usize, usize)>,
    order: Vec<usize>,
}

impl LocalGraph {
    fn build(nodes: BTreeSet<NetId>, edges: Vec<(NetId, NetId, usize)>) -> Result<Self, GrowthRefusal> {
        let nodes: Vec<NetId> = nodes.into_iter().collect();
        let index: BTreeMap<NetId, usize> = nodes
            .iter()
            .enumerate()
            .map(|(position, net)| (*net, position))
            .collect();
        let edges: Vec<(usize, usize, usize)> = edges
            .into_iter()
            .filter_map(|(tail, head, arc)| {
                Some((*index.get(&tail)?, *index.get(&head)?, arc))
            })
            .collect();
        let mut indegree = vec![0usize; nodes.len()];
        for (_, head, _) in &edges {
            indegree[*head] += 1;
        }
        let mut queue: Vec<usize> = (0..nodes.len()).filter(|node| indegree[*node] == 0).collect();
        let mut order = Vec::with_capacity(nodes.len());
        while let Some(node) = queue.pop() {
            order.push(node);
            for (tail, head, _) in &edges {
                if *tail == node {
                    indegree[*head] -= 1;
                    if indegree[*head] == 0 {
                        queue.push(*head);
                    }
                }
            }
        }
        if order.len() != nodes.len() {
            return Err(GrowthRefusal::CombinationalLoop);
        }
        Ok(Self {
            nodes,
            index,
            edges,
            order,
        })
    }

    /// Number of paths from `source` to every node.
    fn forward(&self, source: usize) -> Vec<BigUint> {
        let mut count = vec![BigUint::zero(); self.nodes.len()];
        count[source] = BigUint::one();
        for node in &self.order {
            if count[*node].is_zero() {
                continue;
            }
            for (tail, head, _) in &self.edges {
                if tail == node {
                    let carried = count[*tail].clone();
                    count[*head] += carried;
                }
            }
        }
        count
    }

    /// Number of paths from every node to `target`.
    fn backward(&self, target: usize) -> Vec<BigUint> {
        let mut count = vec![BigUint::zero(); self.nodes.len()];
        count[target] = BigUint::one();
        for node in self.order.iter().rev() {
            for (tail, head, _) in &self.edges {
                if tail == node {
                    let carried = count[*head].clone();
                    count[*tail] += carried;
                }
            }
        }
        count
    }

    fn reachable(&self, source: usize) -> BTreeSet<usize> {
        let counts = self.forward(source);
        counts
            .iter()
            .enumerate()
            .filter(|(node, count)| *node != source && !count.is_zero())
            .map(|(node, _)| node)
            .collect()
    }
}

fn event(counter: &mut u64) -> BTreeSet<EventId> {
    *counter += 1;
    BTreeSet::from([EventId(*counter)])
}

/// Found the 2-complex of a growth.
///
/// Cells are founded in **expansion order**, so the identifiers the complex carries are the ones the
/// schedule chose. That is what makes `rebase_invariants::invariants_agree` across two schedules a
/// test with material rather than a comparison of one computation with itself.
pub fn found_complex(
    growth: &Growth,
    aperture: ComplexAperture,
) -> Result<GrownComplex, GrowthRefusal> {
    let mut complex = GradedCausalComplex::default();
    let mut counter = 0u64;

    // 0-cells: nets, in identifier order, which is allocation order, which is the schedule's.
    let mut net_cells: BTreeMap<NetId, CausalCellId> = BTreeMap::new();
    for net in &growth.nets {
        let cell = complex.found_cell(
            format!("net:{}", net.0),
            event(&mut counter),
            0,
            CausalChain::default(),
        )?;
        net_cells.insert(*net, cell);
    }

    // Conduction, bottom-up over the lineage. A child always carries a larger identifier than its
    // parent, because `call` allocates during the parent's body, so descending identifier order is
    // bottom-up and needs no separate sort.
    let mut gates_of: BTreeMap<InstanceId, Vec<&Gate>> = BTreeMap::new();
    for gate in &growth.gates {
        gates_of.entry(gate.owner).or_default().push(gate);
    }
    let mut conduction: BTreeMap<InstanceId, Vec<(usize, usize)>> = BTreeMap::new();
    let mut ports_of: BTreeMap<InstanceId, (Vec<NetId>, Vec<NetId>)> = BTreeMap::new();
    for instance in &growth.instances {
        let in_ports: Vec<NetId> = instance
            .inputs
            .iter()
            .flat_map(|bus| bus.nets().iter().copied())
            .collect();
        let out_ports: Vec<NetId> = instance
            .outputs
            .iter()
            .flat_map(|bus| bus.nets().iter().copied())
            .collect();
        ports_of.insert(instance.id, (in_ports, out_ports));
    }

    let mut arcs: Vec<Arc> = Vec::new();
    let mut arc_of_gate_pin: BTreeMap<(GateId, usize), usize> = BTreeMap::new();
    let mut arc_of_instance: BTreeMap<(InstanceId, usize, usize), usize> = BTreeMap::new();
    let mut degenerate_arcs = 0usize;

    // Pass one, bottom-up: what each instance conducts. No cell is founded here.
    for instance in growth.instances.iter().rev() {
        let (in_ports, out_ports) = &ports_of[&instance.id];
        let mut nodes: BTreeSet<NetId> = BTreeSet::new();
        nodes.extend(in_ports.iter().copied());
        nodes.extend(out_ports.iter().copied());
        let mut edges: Vec<(NetId, NetId, usize)> = Vec::new();
        for gate in gates_of.get(&instance.id).into_iter().flatten() {
            nodes.extend(gate.inputs.iter().copied());
            nodes.insert(gate.output);
            for pin in &gate.inputs {
                edges.push((*pin, gate.output, usize::MAX));
            }
        }
        for child in &instance.children {
            let (child_in, child_out) = &ports_of[child];
            nodes.extend(child_in.iter().copied());
            nodes.extend(child_out.iter().copied());
            for (tail, head) in conduction.get(child).into_iter().flatten() {
                edges.push((child_in[*tail], child_out[*head], usize::MAX));
            }
        }
        let graph = LocalGraph::build(nodes, edges)?;
        let mut pairs = Vec::new();
        let mut cache: BTreeMap<NetId, BTreeSet<usize>> = BTreeMap::new();
        for (tail, source) in in_ports.iter().enumerate() {
            let reach = match cache.get(source) {
                Some(reach) => reach.clone(),
                None => {
                    let reach = graph
                        .index
                        .get(source)
                        .map(|node| graph.reachable(*node))
                        .unwrap_or_default();
                    cache.insert(*source, reach.clone());
                    reach
                }
            };
            for (head, target) in out_ports.iter().enumerate() {
                if source == target {
                    continue;
                }
                if graph.index.get(target).is_some_and(|node| reach.contains(node)) {
                    pairs.push((tail, head));
                }
            }
        }
        conduction.insert(instance.id, pairs);
    }

    // Pass two, in expansion order: found the 1-cells.
    for step in &growth.trace {
        let instance = &growth.instances[(step.instance.0 - 1) as usize];
        for gate in gates_of.get(&instance.id).into_iter().flatten() {
            for (pin, net) in gate.inputs.iter().enumerate() {
                if *net == gate.output {
                    degenerate_arcs += 1;
                    continue;
                }
                let mut boundary = CausalChain::default();
                boundary.add_term(net_cells[&gate.output], ComparativeMultiplicity::positive(1u32));
                boundary.add_term(net_cells[net], ComparativeMultiplicity::negative(1u32));
                let name = format!("pin:g{}#{pin}:{}", gate.id.0, gate.kind.name());
                let cell = complex.found_cell(name.clone(), event(&mut counter), 1, boundary)?;
                arc_of_gate_pin.insert((gate.id, pin), arcs.len());
                arcs.push(Arc {
                    cell,
                    tail: *net,
                    head: gate.output,
                    gate: Some(gate.id),
                    owner: instance.id,
                    name,
                });
            }
        }
        let (in_ports, out_ports) = &ports_of[&instance.id];
        for (tail, head) in &conduction[&instance.id] {
            let source = in_ports[*tail];
            let target = out_ports[*head];
            if source == target {
                degenerate_arcs += 1;
                continue;
            }
            let mut boundary = CausalChain::default();
            boundary.add_term(net_cells[&target], ComparativeMultiplicity::positive(1u32));
            boundary.add_term(net_cells[&source], ComparativeMultiplicity::negative(1u32));
            let name = format!("arc:i{}:{}->{}", instance.id.0, tail, head);
            let cell = complex.found_cell(name.clone(), event(&mut counter), 1, boundary)?;
            arc_of_instance.insert((instance.id, *tail, *head), arcs.len());
            arcs.push(Arc {
                cell,
                tail: source,
                head: target,
                gate: None,
                owner: instance.id,
                name,
            });
        }
    }

    // Pass three, in expansion order: the faces.
    let mut division_faces = 0usize;
    let mut division_faces_with_multiplicity = 0usize;
    let mut largest = BigUint::zero();
    if aperture.division {
        for step in &growth.trace {
            let instance = &growth.instances[(step.instance.0 - 1) as usize];
            let (in_ports, out_ports) = &ports_of[&instance.id];
            let mut nodes: BTreeSet<NetId> = BTreeSet::new();
            nodes.extend(in_ports.iter().copied());
            nodes.extend(out_ports.iter().copied());
            let mut edges: Vec<(NetId, NetId, usize)> = Vec::new();
            for gate in gates_of.get(&instance.id).into_iter().flatten() {
                nodes.insert(gate.output);
                nodes.extend(gate.inputs.iter().copied());
                for pin in 0..gate.inputs.len() {
                    if let Some(position) = arc_of_gate_pin.get(&(gate.id, pin)) {
                        edges.push((arcs[*position].tail, arcs[*position].head, *position));
                    }
                }
            }
            for child in &instance.children {
                let (child_in, child_out) = &ports_of[child];
                nodes.extend(child_in.iter().copied());
                nodes.extend(child_out.iter().copied());
                for (tail, head) in conduction.get(child).into_iter().flatten() {
                    if let Some(position) = arc_of_instance.get(&(*child, *tail, *head)) {
                        edges.push((arcs[*position].tail, arcs[*position].head, *position));
                    }
                }
            }
            if edges.is_empty() {
                continue;
            }
            let graph = LocalGraph::build(nodes, edges)?;
            for (tail, head) in &conduction[&instance.id] {
                let Some(position) = arc_of_instance.get(&(instance.id, *tail, *head)) else {
                    continue;
                };
                let source = arcs[*position].tail;
                let target = arcs[*position].head;
                let (Some(source_node), Some(target_node)) =
                    (graph.index.get(&source), graph.index.get(&target))
                else {
                    continue;
                };
                let forward = graph.forward(*source_node);
                let backward = graph.backward(*target_node);
                let paths = forward[*target_node].clone();
                if paths.is_zero() {
                    continue;
                }
                let mut boundary = CausalChain::default();
                boundary.add_term(
                    arcs[*position].cell,
                    ComparativeMultiplicity::positive(paths.clone()),
                );
                for (edge_tail, edge_head, arc) in &graph.edges {
                    let weight = &forward[*edge_tail] * &backward[*edge_head];
                    if weight.is_zero() {
                        continue;
                    }
                    if weight > largest {
                        largest = weight.clone();
                    }
                    boundary.add_term(
                        arcs[*arc].cell,
                        ComparativeMultiplicity::negative(weight),
                    );
                }
                if boundary.difference_is_zero() {
                    continue;
                }
                if paths > BigUint::one() {
                    division_faces_with_multiplicity += 1;
                }
                if paths > largest {
                    largest = paths.clone();
                }
                complex.found_cell(
                    format!("division:i{}:{}->{}", instance.id.0, tail, head),
                    event(&mut counter),
                    2,
                    boundary,
                )?;
                division_faces += 1;
            }
        }
    }

    let mut reconvergence_faces = 0usize;
    if aperture.reconvergence {
        let mut nodes: BTreeSet<NetId> = BTreeSet::new();
        let mut edges: Vec<(NetId, NetId, usize)> = Vec::new();
        for (position, arc) in arcs.iter().enumerate() {
            if arc.gate.is_none() {
                continue;
            }
            nodes.insert(arc.tail);
            nodes.insert(arc.head);
            edges.push((arc.tail, arc.head, position));
        }
        let graph = LocalGraph::build(nodes, edges)?;
        let mut founded: BTreeSet<Vec<(u64, BigInt)>> = BTreeSet::new();
        let mut proposals: Vec<(String, CausalChain)> = Vec::new();
        for branch in 0..graph.nodes.len() {
            let leaving: Vec<(usize, usize, usize)> = graph
                .edges
                .iter()
                .copied()
                .filter(|(tail, _, _)| *tail == branch)
                .collect();
            if leaving.len() < 2 {
                continue;
            }
            for left in 0..leaving.len() {
                for right in left + 1..leaving.len() {
                    let (_, left_head, left_arc) = leaving[left];
                    let (_, right_head, right_arc) = leaving[right];
                    let left_reach = {
                        let mut reach = graph.reachable(left_head);
                        reach.insert(left_head);
                        reach
                    };
                    let right_reach = {
                        let mut reach = graph.reachable(right_head);
                        reach.insert(right_head);
                        reach
                    };
                    let common: BTreeSet<usize> =
                        left_reach.intersection(&right_reach).copied().collect();
                    // The first meets: elements of the common set reachable from no other element
                    // of it. Determined by the DAG, so no choice is taken here.
                    let meets: Vec<usize> = common
                        .iter()
                        .copied()
                        .filter(|candidate| {
                            !common.iter().any(|other| {
                                other != candidate && graph.reachable(*other).contains(candidate)
                            })
                        })
                        .collect();
                    for meet in meets {
                        let left_forward = graph.forward(left_head);
                        let right_forward = graph.forward(right_head);
                        let left_back = graph.backward(meet);
                        let right_back = graph.backward(meet);
                        let left_paths = left_forward[meet].clone();
                        let right_paths = right_forward[meet].clone();
                        if left_paths.is_zero() || right_paths.is_zero() {
                            continue;
                        }
                        let mut terms: BTreeMap<usize, BigInt> = BTreeMap::new();
                        let scale_left = BigInt::from(right_paths.clone());
                        let scale_right = BigInt::from(left_paths.clone());
                        *terms.entry(left_arc).or_insert_with(BigInt::zero) +=
                            &scale_left * BigInt::from(left_paths.clone());
                        *terms.entry(right_arc).or_insert_with(BigInt::zero) -=
                            &scale_right * BigInt::from(right_paths.clone());
                        for (edge_tail, edge_head, arc) in &graph.edges {
                            let left_weight = &left_forward[*edge_tail] * &left_back[*edge_head];
                            if !left_weight.is_zero() {
                                *terms.entry(*arc).or_insert_with(BigInt::zero) +=
                                    &scale_left * BigInt::from(left_weight);
                            }
                            let right_weight = &right_forward[*edge_tail] * &right_back[*edge_head];
                            if !right_weight.is_zero() {
                                *terms.entry(*arc).or_insert_with(BigInt::zero) -=
                                    &scale_right * BigInt::from(right_weight);
                            }
                        }
                        terms.retain(|_, value| !value.is_zero());
                        if terms.is_empty() {
                            continue;
                        }
                        let content = terms
                            .values()
                            .fold(BigInt::zero(), |carried, value| gcd(carried, value.clone()));
                        let mut boundary = CausalChain::default();
                        let mut key: Vec<(u64, BigInt)> = Vec::new();
                        for (arc, value) in &terms {
                            let reduced = value / &content;
                            boundary.add_term(
                                arcs[*arc].cell,
                                ComparativeMultiplicity::from_bigint(reduced.clone()),
                            );
                            key.push((arcs[*arc].cell.0, reduced));
                        }
                        let negated: Vec<(u64, BigInt)> = key
                            .iter()
                            .map(|(cell, value)| (*cell, -value.clone()))
                            .collect();
                        if founded.contains(&key) || founded.contains(&negated) {
                            continue;
                        }
                        founded.insert(key);
                        proposals.push((
                            format!(
                                "reconvergence:{}:{}",
                                graph.nodes[branch].0, graph.nodes[meet].0
                            ),
                            boundary,
                        ));
                        if proposals.len() > aperture.face_aperture {
                            return Err(GrowthRefusal::FaceApertureExceeded {
                                faces: proposals.len(),
                                aperture: aperture.face_aperture,
                            });
                        }
                    }
                }
            }
        }
        for (name, boundary) in proposals {
            for (_, coefficient) in boundary.coefficients() {
                let magnitude = coefficient.difference().magnitude().clone();
                if magnitude > largest {
                    largest = magnitude;
                }
            }
            complex.found_cell(name, event(&mut counter), 2, boundary)?;
            reconvergence_faces += 1;
        }
    }

    Ok(GrownComplex {
        complex,
        aperture,
        net_cells,
        arcs,
        division_faces,
        reconvergence_faces,
        division_faces_with_multiplicity,
        largest_face_coefficient: largest,
        degenerate_arcs,
    })
}

/// The section a receiver holds that sees the **netlist and not the lineage**.
///
/// Nets and gate pins only: no lineage boxes, no faces. It is closed under boundary because a pin's
/// boundary is two nets, so it is a genuine subcomplex and [`rebase_invariants_on`] may read it. The
/// difference between this reading and the whole one is exactly what the lineage contributes, which
/// is the aperture axis of this construction — the analogue of `derivation_atlas`'s declared
/// apertures, which read one deposit under several declared incidences.
///
/// [`rebase_invariants_on`]: crate::rebase_invariants::rebase_invariants_on
pub fn primitive_section(grown: &GrownComplex) -> Result<BTreeSet<CausalCellId>, GrowthRefusal> {
    let mut support: BTreeSet<CausalCellId> = grown.net_cells.values().copied().collect();
    for arc in &grown.arcs {
        if arc.gate.is_some() {
            support.insert(arc.cell);
        }
    }
    if !grown.complex.is_closed_support(&support)? {
        return Err(GrowthRefusal::Algebraic(
            "the primitive section is not closed under boundary".to_owned(),
        ));
    }
    Ok(support)
}

fn gcd(left: BigInt, right: BigInt) -> BigInt {
    let mut left = left.magnitude().clone();
    let mut right = right.magnitude().clone();
    while !right.is_zero() {
        let remainder = left % &right;
        left = std::mem::replace(&mut right, remainder);
    }
    BigInt::from(left)
}

// ===============================================================================================
// tests

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rebase_invariants::{
        invariants_agree, rebase_invariants, rebase_invariants_with_schedule, PivotRule,
    };

    fn adder(width: usize, schedule: Schedule) -> Growth {
        grow(&standard_cells(), "ripple-adder", &[width, width, 1], schedule)
            .expect("the ripple adder grows")
    }

    fn bits(value: u32, width: usize) -> Vec<u8> {
        (0..width).map(|bit| ((value >> bit) & 1) as u8).collect()
    }

    fn number(bits: &[u8]) -> u32 {
        bits.iter()
            .enumerate()
            .map(|(position, bit)| u32::from(*bit) << position)
            .sum()
    }

    // --- the material's boundary -------------------------------------------------------------

    #[test]
    fn split_refuses_a_bus_narrower_than_two() {
        let one = Bus::new(vec![NetId(1)]);
        assert_eq!(split(&one), Err(BodyStop::Exhausted));
        let none = Bus::new(Vec::new());
        assert_eq!(split(&none), Err(BodyStop::Exhausted));
        let two = Bus::new(vec![NetId(1), NetId(2)]);
        let (low, high) = split(&two).expect("two halves");
        assert_eq!(low.width(), 1);
        assert_eq!(high.width(), 1);
    }

    #[test]
    fn split_halves_an_odd_bus_unequally_which_is_what_makes_widest_first_a_schedule() {
        let five = Bus::new((1..=5).map(NetId).collect());
        let (low, high) = split(&five).expect("five splits");
        assert_eq!((low.width(), high.width()), (2, 3));
    }

    #[test]
    fn a_bit_cannot_be_taken_from_nothing() {
        let none = Bus::new(Vec::new());
        assert_eq!(take_high_bit(&none), Err(BodyStop::Exhausted));
        assert_eq!(take_low_bit(&none), Err(BodyStop::Exhausted));
    }

    // --- termination by material exhaustion ---------------------------------------------------

    #[test]
    fn a_cell_whose_material_exhausts_immediately_returns_the_fallback_and_grows_nothing() {
        // The negative pole. A multiplexer with no select bits selects the only thing it has.
        let growth = grow(&standard_cells(), "multiplexer", &[1, 0], Schedule::Instantiation)
            .expect("the pole grows");
        assert_eq!(growth.gate_count(), 0);
        assert_eq!(growth.instance_count(), 1);
        assert!(growth.instances[0].grew_nothing);
        assert!(growth.instances[0].fell_back);
        assert!(growth.sites.is_empty());
        // The output net IS the input net; the identity fallback is an alias, not a wire.
        assert_eq!(growth.root_outputs[0], growth.primary_inputs[0]);
        // And it still evaluates.
        assert_eq!(evaluate(&growth, &[vec![1], vec![]]).unwrap(), vec![vec![1]]);
    }

    #[test]
    fn the_base_case_is_reached_by_refusal_and_not_by_a_test() {
        let growth = adder(1, Schedule::Instantiation);
        // One instance, which asked for the recursive rule and fired the base rule.
        assert_eq!(growth.instance_count(), 1);
        assert_eq!(growth.instances[0].requested, "ripple-adder");
        assert_eq!(growth.instances[0].fired, "full-adder");
        assert!(growth.instances[0].fell_back);
        assert_eq!(growth.gate_count(), 2);
    }

    #[test]
    fn a_refused_body_leaves_nothing_behind() {
        // `ripple-adder` at width one calls `split` first, so nothing was staged; at width three the
        // recursion reaches width one on both sides. If the roll-back leaked, the net count would
        // exceed what the surviving gates and ports need.
        let growth = adder(3, Schedule::Instantiation);
        let mut reachable: BTreeSet<NetId> = BTreeSet::new();
        for bus in &growth.primary_inputs {
            reachable.extend(bus.nets().iter().copied());
        }
        for gate in &growth.gates {
            reachable.insert(gate.output);
        }
        assert_eq!(reachable.len(), growth.net_count());
    }

    #[test]
    fn a_rule_with_no_fallback_whose_material_exhausts_is_refused() {
        let mut table = standard_cells();
        table.insert(Rule {
            name: "ripple-adder",
            outs: &[OutShape::LikeArg(0), OutShape::LikeArg(2)],
            fallback: None,
            body: ripple_adder_body,
        });
        let refusal = grow(&table, "ripple-adder", &[1, 1, 1], Schedule::Instantiation)
            .expect_err("a base case with no fallback cannot terminate");
        assert_eq!(
            refusal,
            GrowthRefusal::NoFallback {
                rule: "ripple-adder"
            }
        );
    }

    #[test]
    fn an_out_shape_contract_violation_is_refused() {
        fn wrong(body: &mut Body<'_, '_>, args: &[Bus]) -> Result<Vec<Bus>, BodyStop> {
            let (low, _) = split(&args[0])?;
            let sum = body.gate("sum", GateKind::Xor3, &[&low, &low, &args[2]])?;
            Ok(vec![sum, args[2].clone()])
        }
        let mut table = standard_cells();
        table.insert(Rule {
            name: "ripple-adder",
            outs: &[OutShape::LikeArg(0), OutShape::LikeArg(2)],
            fallback: Some(Fallback::Rule("full-adder")),
            body: wrong,
        });
        let refusal = grow(&table, "ripple-adder", &[4, 4, 1], Schedule::Instantiation)
            .expect_err("a half-width sum does not honour LikeArg(0)");
        assert!(matches!(
            refusal,
            GrowthRefusal::OutShapeContract { returned: 2, declared: 4, .. }
        ));
    }

    // --- the circuit is right ------------------------------------------------------------------

    #[test]
    fn the_grown_ripple_adder_adds() {
        for width in 1..=5usize {
            let growth = adder(width, Schedule::Instantiation);
            let modulus = 1u32 << width;
            for left in 0..modulus {
                for right in 0..modulus {
                    for carry in 0..2u32 {
                        let out = evaluate(
                            &growth,
                            &[bits(left, width), bits(right, width), bits(carry, 1)],
                        )
                        .expect("the grown adder evaluates");
                        let expected = left + right + carry;
                        assert_eq!(
                            number(&out[0]),
                            expected % modulus,
                            "sum at width {width}: {left} + {right} + {carry}"
                        );
                        assert_eq!(
                            number(&out[1]),
                            expected / modulus,
                            "carry at width {width}: {left} + {right} + {carry}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn the_brent_kung_adder_computes_the_same_function_from_a_different_shape() {
        // Exhaustive to width four; past that a declared stride, because 2^(2w+1) evaluations is a
        // cost and not a proof. The stride is coprime to every modulus in the sweep, so it visits
        // the whole residue range rather than a corner of it.
        for width in [1usize, 2, 3, 4, 6, 9] {
            let table = standard_cells();
            let ripple = grow(&table, "ripple-adder", &[width, width, 1], Schedule::Instantiation)
                .expect("ripple grows");
            let kung = grow(
                &table,
                "brent-kung-adder",
                &[width, width, 1],
                Schedule::Instantiation,
            )
            .expect("brent-kung grows");
            let modulus = 1u32 << width;
            let stride = if width <= 4 { 1 } else { 37 };
            let mut compared = 0usize;
            let mut left = 0u32;
            while left < modulus {
                let mut right = 0u32;
                while right < modulus {
                    for carry in 0..2u32 {
                        let arguments = [bits(left, width), bits(right, width), bits(carry, 1)];
                        let one = evaluate(&ripple, &arguments).expect("ripple evaluates");
                        let two = evaluate(&kung, &arguments).expect("kung evaluates");
                        assert_eq!(one, two, "width {width}: {left} + {right} + {carry}");
                        // And it is arithmetic, not merely agreement.
                        let total = left + right + carry;
                        assert_eq!(number(&one[0]), total % modulus);
                        assert_eq!(number(&one[1]), total / modulus);
                        compared += 1;
                    }
                    right += stride;
                }
                left += stride;
            }
            assert!(compared > 0, "width {width} compared nothing");
            // Same function, different shape: the two grow different netlists.
            assert_ne!(
                canonical_netlist(&ripple).unwrap(),
                canonical_netlist(&kung).unwrap(),
                "width {width}"
            );
        }
    }

    #[test]
    fn the_grown_multiplexer_selects() {
        for select in 1..=3usize {
            let width = 1usize << select;
            let growth = grow(
                &standard_cells(),
                "multiplexer",
                &[width, select],
                Schedule::Instantiation,
            )
            .expect("the multiplexer grows");
            for data in 0..(1u32 << width) {
                for index in 0..width {
                    let out = evaluate(
                        &growth,
                        &[bits(data, width), bits(index as u32, select)],
                    )
                    .expect("the multiplexer evaluates");
                    assert_eq!(out[0][0], ((data >> index) & 1) as u8, "select {index}");
                }
            }
        }
    }

    #[test]
    fn the_grown_parity_tree_reduces() {
        for width in 1..=6usize {
            let growth = grow(
                &standard_cells(),
                "parity-tree",
                &[width],
                Schedule::Instantiation,
            )
            .expect("the parity tree grows");
            for value in 0..(1u32 << width) {
                let out = evaluate(&growth, &[bits(value, width)]).expect("it evaluates");
                assert_eq!(out[0][0], (value.count_ones() % 2) as u8, "value {value}");
            }
        }
    }

    // --- the schedule is a gauge that acts ------------------------------------------------------

    #[test]
    fn the_three_schedules_expand_in_different_orders() {
        // At an odd width `split` is unbalanced, so widest-first genuinely diverges from both others.
        let traces: Vec<Vec<String>> = Schedule::ALL
            .iter()
            .map(|schedule| adder(5, *schedule).trace_lines())
            .collect();
        assert_ne!(traces[0], traces[1], "instantiation vs widest-first");
        assert_ne!(traces[0], traces[2], "instantiation vs deepest");
        assert_ne!(traces[1], traces[2], "widest-first vs deepest");
    }

    #[test]
    fn widest_first_coincides_with_instantiation_order_at_balanced_widths_and_that_is_the_material() {
        // A power-of-two bus halves evenly at every level, so every pending instance carries the
        // same material and widest-first has nothing to prefer. The gauge degenerating here is a
        // property of the CIRCUIT, and the third schedule is why the sweep still has content.
        let balanced: Vec<Vec<String>> = Schedule::ALL
            .iter()
            .map(|schedule| adder(4, *schedule).trace_lines())
            .collect();
        assert_eq!(balanced[0], balanced[1]);
        assert_ne!(balanced[0], balanced[2]);
    }

    #[test]
    fn the_three_schedules_grow_one_netlist_under_different_symbols() {
        for width in [3usize, 5, 6] {
            let forms: Vec<CanonicalNetlist> = Schedule::ALL
                .iter()
                .map(|schedule| canonical_netlist(&adder(width, *schedule)).expect("canonical"))
                .collect();
            assert_eq!(forms[0], forms[1], "width {width}");
            assert_eq!(forms[0], forms[2], "width {width}");
            // ...and the symbols really did move.
            let identifiers: Vec<Vec<NetId>> = Schedule::ALL
                .iter()
                .map(|schedule| {
                    adder(width, *schedule)
                        .gates
                        .iter()
                        .map(|gate| gate.output)
                        .collect()
                })
                .collect();
            assert_ne!(identifiers[0], identifiers[2], "width {width}");
        }
    }

    #[test]
    fn the_schedules_agree_on_what_the_circuit_computes() {
        for width in [3usize, 5] {
            let growths: Vec<Growth> = Schedule::ALL.iter().map(|s| adder(width, *s)).collect();
            let modulus = 1u32 << width;
            for left in 0..modulus {
                for right in 0..modulus {
                    let arguments = [bits(left, width), bits(right, width), bits(0, 1)];
                    let first = evaluate(&growths[0], &arguments).unwrap();
                    for growth in &growths[1..] {
                        assert_eq!(evaluate(growth, &arguments).unwrap(), first);
                    }
                }
            }
        }
    }

    #[test]
    fn a_schedule_is_deterministic() {
        for schedule in Schedule::ALL {
            assert_eq!(adder(5, schedule).trace_lines(), adder(5, schedule).trace_lines());
        }
    }

    // --- indirect encoding ----------------------------------------------------------------------

    #[test]
    fn the_description_stays_constant_while_the_gate_count_grows() {
        let table = standard_cells();
        let (rules, shapes) = table.description();
        let mut gates = Vec::new();
        let mut sites = BTreeSet::new();
        for width in 2..=9usize {
            let growth = grow(&table, "ripple-adder", &[width, width, 1], Schedule::Instantiation)
                .expect("grows");
            gates.push(growth.gate_count());
            sites.insert(growth.sites.len());
        }
        assert_eq!((rules, shapes), standard_cells().description());
        // One description length across every width that divided.
        assert_eq!(sites.len(), 1, "emission sites moved with the width");
        // And the gate count strictly grows.
        assert!(gates.windows(2).all(|pair| pair[0] < pair[1]), "{gates:?}");
    }

    #[test]
    fn the_same_rule_fires_at_several_widths_on_different_material() {
        let growth = adder(8, Schedule::Instantiation);
        let widths = growth.widths_of("ripple-adder");
        assert!(
            widths.len() >= 3,
            "ripple-adder fired at widths {widths:?}; one width would be macro expansion"
        );
        let base = growth.widths_of("full-adder");
        assert_eq!(base, BTreeSet::from([1]));
        // The reuse table carries a count above one somewhere, so the rule is genuinely re-entered.
        let reuse = growth.rule_reuse();
        assert!(reuse.values().any(|count| *count > 1), "{reuse:?}");
    }

    #[test]
    fn brent_kung_is_shallower_than_ripple_carry_from_the_same_discipline() {
        let table = standard_cells();
        let mut ripple = Vec::new();
        let mut kung = Vec::new();
        for width in [4usize, 8, 16] {
            ripple.push(
                grow(&table, "ripple-adder", &[width, width, 1], Schedule::Instantiation)
                    .unwrap()
                    .depth(),
            );
            kung.push(
                grow(
                    &table,
                    "brent-kung-adder",
                    &[width, width, 1],
                    Schedule::Instantiation,
                )
                .unwrap()
                .depth(),
            );
        }
        // Both lineages are logarithmic in the width; the difference the article names is the
        // GATE depth of the carry, which is what the complex sees as a long chain of arcs.
        assert!(ripple.windows(2).all(|pair| pair[0] < pair[1]), "{ripple:?}");
        assert!(kung.windows(2).all(|pair| pair[0] < pair[1]), "{kung:?}");
    }

    // --- the complex ----------------------------------------------------------------------------

    #[test]
    fn the_division_faces_close_which_is_what_verifies_the_path_counting() {
        // `found_cell` refuses `dd != 0`, so a wrong path count or a wrong weight cannot be founded.
        // This is the whole verification of the two dynamic programs.
        for width in 1..=4usize {
            let growth = adder(width, Schedule::Instantiation);
            let grown = found_complex(&growth, ComplexAperture::DIVISION).expect("it founds");
            grown.complex.validate().expect("the complex validates");
            assert!(grown.division_faces > 0 || width == 0);
        }
    }

    #[test]
    fn a_face_with_a_wrong_path_weight_is_refused() {
        // The previous test rests on `found_cell` having teeth. This shows it does: take a face the
        // path counting actually produced, move one weight by one, and the same founding refuses.
        let growth = grow(
            &standard_cells(),
            "brent-kung-adder",
            &[2, 2, 1],
            Schedule::Instantiation,
        )
        .unwrap();
        let grown = found_complex(&growth, ComplexAperture::DIVISION).unwrap();
        let face = grown
            .complex
            .cells()
            .values()
            .find(|cell| cell.grade == 2)
            .expect("a division face")
            .clone();
        let mut perturbed = face.boundary.clone();
        let victim = *perturbed.support().iter().next().expect("a term");
        perturbed.add_term(victim, ComparativeMultiplicity::positive(1u32));
        let mut complex = grown.complex.clone();
        let refusal = complex
            .found_cell(
                "perturbed",
                BTreeSet::from([EventId(u64::MAX)]),
                2,
                perturbed,
            )
            .expect_err("a face off by one on one weight is not a cycle");
        assert!(
            matches!(refusal, CausalAlgebraicError::BoundarySquaredNonzero(_)),
            "{refusal:?}"
        );
    }

    #[test]
    fn the_reconvergence_family_refuses_past_its_declared_aperture_rather_than_truncating() {
        let growth = grow(
            &standard_cells(),
            "brent-kung-adder",
            &[2, 2, 1],
            Schedule::Instantiation,
        )
        .unwrap();
        let tight = ComplexAperture {
            division: false,
            reconvergence: true,
            face_aperture: 1,
        };
        let refusal = found_complex(&growth, tight).expect_err("seven faces past an aperture of one");
        assert!(
            matches!(refusal, GrowthRefusal::FaceApertureExceeded { aperture: 1, .. }),
            "{refusal:?}"
        );
    }

    #[test]
    fn the_complex_carries_all_three_grades() {
        let growth = adder(3, Schedule::Instantiation);
        let grown = found_complex(&growth, ComplexAperture::DIVISION).expect("founds");
        let vector = grown.complex.f_vector();
        assert!(vector.get(&0).copied().unwrap_or(0) > 0);
        assert!(vector.get(&1).copied().unwrap_or(0) > 0);
        assert!(vector.get(&2).copied().unwrap_or(0) > 0, "no 2-cells: {vector:?}");
    }

    #[test]
    fn division_faces_carry_multiplicity_above_one_where_the_material_reconverges() {
        // A ripple-carry adder built from three-input primitives never reconverges: every net's
        // fan-out enters disjoint cones. Brent-Kung does, because the propagate and the generate of
        // one half both reach the same group carry. That difference is grown, not authored.
        let table = standard_cells();
        let ripple = grow(&table, "ripple-adder", &[4, 4, 1], Schedule::Instantiation).unwrap();
        let kung = grow(
            &table,
            "brent-kung-adder",
            &[2, 2, 1],
            Schedule::Instantiation,
        )
        .unwrap();
        let ripple_complex = found_complex(&ripple, ComplexAperture::DIVISION).unwrap();
        let kung_complex = found_complex(&kung, ComplexAperture::DIVISION).unwrap();
        assert_eq!(ripple_complex.division_faces_with_multiplicity, 0);
        assert!(
            kung_complex.division_faces_with_multiplicity > 0,
            "brent-kung grew no reconvergence"
        );
        assert!(kung_complex.largest_face_coefficient > BigUint::one());
    }

    #[test]
    fn the_reconvergence_family_is_separable_and_fires_on_reconvergent_material() {
        let table = standard_cells();
        let kung = grow(
            &table,
            "brent-kung-adder",
            &[2, 2, 1],
            Schedule::Instantiation,
        )
        .unwrap();
        let only_division = found_complex(&kung, ComplexAperture::DIVISION).unwrap();
        let only_reconvergence = found_complex(&kung, ComplexAperture::RECONVERGENCE).unwrap();
        let both = found_complex(&kung, ComplexAperture::BOTH).unwrap();
        assert_eq!(only_division.reconvergence_faces, 0);
        assert_eq!(only_reconvergence.division_faces, 0);
        assert!(only_reconvergence.reconvergence_faces > 0);
        assert_eq!(
            both.division_faces + both.reconvergence_faces,
            only_division.division_faces + only_reconvergence.reconvergence_faces
        );
    }

    #[test]
    fn the_invariants_do_not_move_with_the_schedule() {
        for width in [2usize, 3] {
            let readings: Vec<_> = Schedule::ALL
                .iter()
                .map(|schedule| {
                    let growth = adder(width, *schedule);
                    let grown = found_complex(&growth, ComplexAperture::DIVISION).unwrap();
                    rebase_invariants(&grown.complex, PivotRule::FirstNonzero).unwrap()
                })
                .collect();
            assert!(invariants_agree(&readings[0], &readings[1]), "width {width}");
            assert!(invariants_agree(&readings[0], &readings[2]), "width {width}");
        }
    }

    #[test]
    fn the_schedule_relabels_the_complex_and_the_invariants_do_not_notice() {
        // The anti-tautology check for the whole construction. If the complex were founded in a
        // canonical order the schedule could not reach, `invariants_agree` across schedules would be
        // a comparison of one object with itself. Cells are founded in EXPANSION order, so the two
        // complexes are genuinely different labelled objects carrying the same invariants.
        let complexes: Vec<Vec<(u32, String)>> = Schedule::ALL
            .iter()
            .map(|schedule| {
                let growth = adder(3, *schedule);
                let grown = found_complex(&growth, ComplexAperture::DIVISION).unwrap();
                grown
                    .complex
                    .cells()
                    .values()
                    .map(|cell| (cell.grade, cell.name.clone()))
                    .collect()
            })
            .collect();
        assert_ne!(complexes[0], complexes[2], "the labelling did not move");
        // ...but the multiset of grades is identical, so it really is a relabelling.
        let grades: Vec<Vec<u32>> = complexes
            .iter()
            .map(|cells| {
                let mut grades: Vec<u32> = cells.iter().map(|(grade, _)| *grade).collect();
                grades.sort_unstable();
                grades
            })
            .collect();
        assert_eq!(grades[0], grades[2]);
    }

    #[test]
    fn the_invariants_do_not_move_with_the_pivot_rule() {
        let growth = adder(3, Schedule::Instantiation);
        let grown = found_complex(&growth, ComplexAperture::BOTH).unwrap();
        let readings: Vec<_> = PivotRule::ALL
            .iter()
            .map(|rule| rebase_invariants(&grown.complex, *rule).unwrap())
            .collect();
        assert!(invariants_agree(&readings[0], &readings[1]));
        assert!(invariants_agree(&readings[0], &readings[2]));
    }

    #[test]
    fn the_three_pivot_rules_take_different_paths_on_grown_material() {
        // A three-rule agreement is evidence only if the three rules computed differently. Grown
        // division faces carry coefficients above one, which is exactly what makes the magnitude
        // rules diverge from the first-nonzero rule.
        let growth = grow(
            &standard_cells(),
            "brent-kung-adder",
            &[2, 2, 1],
            Schedule::Instantiation,
        )
        .unwrap();
        let grown = found_complex(&growth, ComplexAperture::DIVISION).unwrap();
        let schedules: Vec<_> = PivotRule::ALL
            .iter()
            .map(|rule| rebase_invariants_with_schedule(&grown.complex, *rule).unwrap().1)
            .collect();
        assert_ne!(schedules[0].per_grade, schedules[1].per_grade);
        assert_ne!(schedules[0].per_grade, schedules[2].per_grade);
    }

    #[test]
    fn the_primitive_section_is_a_receiver_that_sees_the_netlist_and_not_the_lineage() {
        use crate::rebase_invariants::rebase_invariants_on;
        for width in [2usize, 3] {
            let mut sections = Vec::new();
            for schedule in Schedule::ALL {
                let growth = adder(width, schedule);
                let grown = found_complex(&growth, ComplexAperture::DIVISION).unwrap();
                let support = primitive_section(&grown).expect("the section is closed");
                // It really is a section: strictly fewer cells than the whole.
                assert!(support.len() < grown.complex.cells().len());
                let section =
                    rebase_invariants_on(&grown.complex, Some(&support), PivotRule::FirstNonzero)
                        .unwrap();
                let whole =
                    rebase_invariants_on(&grown.complex, None, PivotRule::FirstNonzero).unwrap();
                // The narrower receiver genuinely sees something else; the aperture is not inert.
                assert!(
                    !invariants_agree(&section, &whole),
                    "width {width}: the lineage contributed nothing"
                );
                sections.push(section);
            }
            // ...and what it sees is still schedule-independent.
            assert!(invariants_agree(&sections[0], &sections[1]), "width {width}");
            assert!(invariants_agree(&sections[0], &sections[2]), "width {width}");
        }
    }

    #[test]
    fn the_euler_characteristic_cross_checks() {
        for width in [2usize, 3, 4] {
            let growth = adder(width, Schedule::Instantiation);
            let grown = found_complex(&growth, ComplexAperture::DIVISION).unwrap();
            let reading = rebase_invariants(&grown.complex, PivotRule::FirstNonzero).unwrap();
            assert_eq!(
                reading.euler_characteristic(),
                reading.cell_euler_characteristic(),
                "width {width}"
            );
        }
    }

    #[test]
    fn the_arc_population_separates_the_pin_level_from_the_lineage_level() {
        let growth = adder(2, Schedule::Instantiation);
        let grown = found_complex(&growth, ComplexAperture::DIVISION).unwrap();
        let pins = grown.arcs.iter().filter(|arc| arc.gate.is_some()).count();
        let boxes = grown.arcs.iter().filter(|arc| arc.gate.is_none()).count();
        assert_eq!(pins, growth.gates.iter().map(|g| g.inputs.len()).sum::<usize>());
        assert!(boxes > 0, "no lineage arcs");
    }

    #[test]
    fn the_negative_pole_founds_a_complex_with_no_arcs_at_all() {
        let growth = grow(&standard_cells(), "multiplexer", &[1, 0], Schedule::Instantiation)
            .expect("the pole grows");
        let grown = found_complex(&growth, ComplexAperture::BOTH).expect("it founds");
        assert!(grown.arcs.is_empty());
        assert_eq!(grown.division_faces, 0);
        assert_eq!(grown.reconvergence_faces, 0);
        let reading = rebase_invariants(&grown.complex, PivotRule::FirstNonzero).unwrap();
        assert!(reading.total_torsion().is_empty());
    }

    #[test]
    fn a_growth_at_a_larger_width_founds_a_strictly_larger_complex() {
        let mut sizes = Vec::new();
        for width in 1..=4usize {
            let growth = adder(width, Schedule::Instantiation);
            let grown = found_complex(&growth, ComplexAperture::DIVISION).unwrap();
            sizes.push(grown.complex.cells().len());
        }
        assert!(sizes.windows(2).all(|pair| pair[0] < pair[1]), "{sizes:?}");
    }
}
