//! **The tree source: a drawn shift-closed context tree with drawn leaf faces.**
//!
//! [definition; agent-inferred] **The Holarchy.** The shift navigator (a tick pushes its cell onto
//! the address, newest first; Lean `Compression/Landmark/Context/Standing.shift`) with a standing:
//! a pruned context tree `S` ([`ContextTree`]) whose leaf map reads the address, and at each leaf a
//! face `θ_s` on a declared grid `1/g` (positive numerators summing to `g`). The next cell is drawn
//! from the face of the leaf the address reaches. `S` is **closed under the shift** (Lean
//! `ShiftClosed`: the leaf of `b :: a` is a function of `b` and the leaf of `a`), so the leaf map
//! is itself a standing on the shift navigator's words (`leaf_standing`, the coarsest quotient that
//! reads the present face) and the source's motion is the **leaf chain**
//! `P(s → leafOf(c :: s)) = θ_s(c)` on the leaves.
//!
//! [definition; agent-inferred] **The draw** ([`ContextTree::draw`], [`TreeSource::draw`]). Below
//! the declared depth `d` each node stops or splits by a fair coin (the `½` stop prior the
//! receiving tree declares, Lean `PrunedTree.prior_half`), except along a drawn spine of `d`
//! letters, which splits to the full depth `d`; the drawn tree is then closed under the shift by
//! splitting the leaf of each witness `a, a'` with one leaf whose shifts `b :: a`, `b :: a'` reach
//! two ([`ContextTree::close`]; a split leaf lies above depth `d`, so the closure stays within `d`).
//! Each leaf's numerators are a uniform composition of `g` into `|A|` positive parts, and the
//! initial past (`d` cells, newest first) is drawn uniformly.
//!
//! [proved-standard; implemented-exact] **The truth** ([`TreeSourceTruth`]): the tree and its
//! faces; the leaf chain's stationary law `π`, solved exactly over ℚ (`aeon::MarkovChain::
//! stationary_law`, one `ratio::linear` solve; unique since every face is positive, so every leaf
//! is reached from every other); and the **entropy rate** `h = Σ_s π(s) H(θ_s)` as its exact form in
//! `log₂ p` (`ratio::surprisal::SymbolicSurprisal`) with its enclosure. Per passage: the source's
//! own code of the realized cells from its initial past ([`TreeSource::passage`]), the receiving
//! tree's weighting bound at a declared depth ([`TreeSource::weighting_bound`]) and the tree the
//! receiver's standing recovers ([`TreeSource::recovery`]).
//!
//! [proved-standard; binary] **The weighting bound** (Willems, Shtarkov and Tjalkens 1995;
//! Krichevsky and Trofimov 1981). At the `½` stop prior and a receiver of depth `D ≥ d` over the
//! letters `{Boundary} ∪ A`, the receiver's pruned tree `S′` is `S` with a boundary leaf under each
//! split. Its dominance (Lean `Compression/Landmark/Context/Tree.kraft_and_dominance`) gives
//! `code ≤ Γ(S′) − log₂ Π_(s′ ∈ S′) KT(s′)`, with `Γ(S′)` the model cost (`PrunedTree.cost`: one
//! bit a split and one a leaf above depth `D`), and a binary leaf's KT excess over any parameter is
//! at most `½ log₂ n_s + 1` (owed in Lean, #62, the module docstring of `Tree`). A cell whose
//! address meets the boundary before a leaf of `S` reaches a boundary leaf once, at a KT cost of one
//! bit. So the executed tree's code less the source's own code is at most
//! `Γ(S′) + Σ_(s: n_s ≥ 1) (½ log₂ n_s + 1) + b` plus the chart's certified drift.
//!
//! [definition; agent-inferred] **The recovered tree** ([`TreeSource::recovery`]), read against the
//! drawn tree and against the minimal one ([`TreeSource::minimal`], the coarsest tree reading the
//! same faces: a drawn split whose leaves share one face is the source's kernel). Along each
//! address of the receiver's depth the standing's stored levels are read in order
//! (`context::Landmarks::opened`); a stored chain's `β` weighs stopping within the chain against the
//! subtrees below it, and every node of a chain holds the same arrivals, so its posterior stop weight
//! `β/(1 + β)` above `½` (`β > 1`) stops the recovered tree at the chain's top, the depth where the
//! paths part. An address whose stored path ends before any stop, above the declared depth, was
//! never visited below it and is counted apart. Binary only: a wider alphabet's cell descends
//! `⌈log₂ |A|⌉` digit trees, each with its own recovered pruning.

use std::collections::{BTreeSet, HashMap, HashSet};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::{Draw, TerrainError, refuse};
use crate::aeon::MarkovChain;
use crate::compression::landmark::context::{Landmarks, Letter};
use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, interval_sum, log2_enclosure};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::surprisal::SymbolicSurprisal;

/// One node of a context tree: its context (newest first) and its children, one a letter, when it
/// splits.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Node {
    context: Vec<usize>,
    children: Option<Vec<usize>>,
}

/// [definition] **A pruned context tree** over `ℤ/|A|` (Lean `PrunedTree`): every node stops (a
/// leaf) or splits into one child a letter; its leaves in the order of their contexts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContextTree {
    alphabet: usize,
    nodes: Vec<Node>,
    leaves: Vec<usize>,
    /// Each node's index among the leaves (`usize::MAX` at a split).
    index: Vec<usize>,
}

impl ContextTree {
    /// **The tree whose leaves are the declared contexts** (newest first); refused unless every
    /// address reaches exactly one of them.
    pub fn new(alphabet: usize, leaves: Vec<Vec<usize>>) -> Result<Self, TerrainError> {
        if alphabet < 2 {
            return Err(refuse("a context tree", "its alphabet needs at least two letters"));
        }
        let declared: HashSet<Vec<usize>> = leaves.iter().cloned().collect();
        if declared.len() != leaves.len()
            || leaves.iter().flatten().any(|letter| *letter >= alphabet)
        {
            return Err(refuse(
                "a context tree",
                "its leaves are distinct contexts over its alphabet",
            ));
        }
        let deepest = leaves.iter().map(Vec::len).max().unwrap_or(0);
        let mut tree = Self {
            alphabet,
            nodes: vec![Node {
                context: Vec::new(),
                children: None,
            }],
            leaves: Vec::new(),
            index: Vec::new(),
        };
        let mut stack = vec![0usize];
        while let Some(node) = stack.pop() {
            let context = tree.nodes[node].context.clone();
            if declared.contains(&context) {
                continue;
            }
            if context.len() >= deepest {
                return Err(refuse(
                    "a context tree",
                    "an address reaches none of its leaves, or a leaf lies below another",
                ));
            }
            let children = tree.split_node(node);
            stack.extend(children);
        }
        tree.index_leaves();
        if tree.leaves.len() != leaves.len() {
            return Err(refuse(
                "a context tree",
                "a declared leaf lies below another leaf",
            ));
        }
        Ok(tree)
    }

    /// Split `node` into one leaf a letter; returns the children.
    fn split_node(&mut self, node: usize) -> Vec<usize> {
        let first = self.nodes.len();
        let context = self.nodes[node].context.clone();
        for letter in 0..self.alphabet {
            let mut child = context.clone();
            child.push(letter);
            self.nodes.push(Node {
                context: child,
                children: None,
            });
        }
        let children: Vec<usize> = (first..first + self.alphabet).collect();
        self.nodes[node].children = Some(children.clone());
        children
    }

    /// The leaves in the order of their contexts.
    fn index_leaves(&mut self) {
        let mut leaves: Vec<usize> = (0..self.nodes.len())
            .filter(|&node| self.nodes[node].children.is_none())
            .collect();
        leaves.sort_by(|a, b| self.nodes[*a].context.cmp(&self.nodes[*b].context));
        self.index = vec![usize::MAX; self.nodes.len()];
        for (position, &node) in leaves.iter().enumerate() {
            self.index[node] = position;
        }
        self.leaves = leaves;
    }

    /// **The drawn tree** (module header, "The draw"): a fair coin at each node above depth `d`, a
    /// drawn spine splitting to depth `d`, then the shift closure. Refused at `d = 0` or an
    /// alphabet of fewer than two letters.
    pub fn draw(alphabet: usize, depth: usize, draw: &mut Draw) -> Result<Self, TerrainError> {
        if alphabet < 2 || depth == 0 {
            return Err(refuse(
                "a drawn context tree",
                "it needs at least two letters and a depth of at least one",
            ));
        }
        let spine: Vec<usize> = (0..depth).map(|_| draw.below(alphabet)).collect();
        let mut tree = Self {
            alphabet,
            nodes: vec![Node {
                context: Vec::new(),
                children: None,
            }],
            leaves: Vec::new(),
            index: Vec::new(),
        };
        let mut stack = vec![0usize];
        while let Some(node) = stack.pop() {
            let context = &tree.nodes[node].context;
            let on_spine = context.len() < depth && spine.starts_with(context);
            if context.len() < depth && (on_spine || draw.coin()) {
                let children = tree.split_node(node);
                stack.extend(children.into_iter().rev());
            }
        }
        tree.index_leaves();
        tree.close();
        Ok(tree)
    }

    /// **The shift closure** (module header): split the leaf of each witness until none remains.
    pub fn close(&mut self) {
        while let Some(leaf) = self.closure_witness() {
            self.split_node(leaf);
            self.index_leaves();
        }
    }

    /// The alphabet `|A|`.
    pub fn alphabet(&self) -> usize {
        self.alphabet
    }

    /// The leaves' contexts, newest first, in order.
    pub fn leaves(&self) -> Vec<Vec<usize>> {
        self.leaves
            .iter()
            .map(|&node| self.nodes[node].context.clone())
            .collect()
    }

    /// The tree's depth: its deepest leaf's.
    pub fn depth(&self) -> usize {
        self.leaves
            .iter()
            .map(|&node| self.nodes[node].context.len())
            .max()
            .unwrap_or(0)
    }

    /// **The leaf a past reaches** (newest first), as its index among the leaves; `None` when the
    /// past ends above a leaf.
    pub fn leaf(&self, past: impl IntoIterator<Item = usize>) -> Option<usize> {
        let mut node = 0usize;
        let mut past = past.into_iter();
        loop {
            match &self.nodes[node].children {
                None => return Some(self.index[node]),
                Some(children) => node = children[past.next()?],
            }
        }
    }

    /// Every address of `depth` letters, in order.
    fn addresses(&self, depth: usize) -> Vec<Vec<usize>> {
        let mut addresses = vec![Vec::new()];
        for _ in 0..depth {
            addresses = addresses
                .into_iter()
                .flat_map(|address: Vec<usize>| {
                    (0..self.alphabet).map(move |letter| {
                        let mut next = address.clone();
                        next.push(letter);
                        next
                    })
                })
                .collect();
        }
        addresses
    }

    /// A leaf node that breaks the shift closure (module header), or `None`: over every address `a`
    /// of the tree's depth (the leaf reads no more, Lean `leafOf_take`) and every letter `b`, the
    /// leaf of `b :: a` must be one per pair (leaf of `a`, `b`).
    fn closure_witness(&self) -> Option<usize> {
        let mut shifted: HashMap<(usize, usize), usize> = HashMap::new();
        for address in self.addresses(self.depth()) {
            let leaf = self
                .leaf(address.iter().copied())
                .expect("an address of the tree's depth reaches a leaf");
            for letter in 0..self.alphabet {
                let next = self
                    .leaf(std::iter::once(letter).chain(address.iter().copied()))
                    .expect("an address of the tree's depth reaches a leaf");
                if *shifted.entry((leaf, letter)).or_insert(next) != next {
                    return Some(self.leaves[leaf]);
                }
            }
        }
        None
    }

    /// **Whether the leaves are closed under the shift** (Lean
    /// `Compression/Landmark/Context/Standing.ShiftClosed`), checked on its definition over every
    /// address of the tree's depth.
    pub fn is_shift_closed(&self) -> bool {
        self.closure_witness().is_none()
    }

    /// **The model cost `Γ(S′)` at a receiver of depth `D`** (module header, "The weighting bound";
    /// Lean `PrunedTree.cost`): over the receiver's letters `{Boundary} ∪ A`, one bit a split and one
    /// a leaf above depth `D`, each split carrying its boundary leaf. Refused below the tree's depth.
    pub fn cost(&self, receiver_depth: usize) -> Result<u64, TerrainError> {
        if receiver_depth < self.depth() {
            return Err(refuse(
                "a context tree's model cost",
                "the receiver's depth lies below the tree's",
            ));
        }
        let above = |depth: usize| u64::from(depth < receiver_depth);
        Ok(self
            .nodes
            .iter()
            .map(|node| match node.children {
                Some(_) => 1 + above(node.context.len() + 1),
                None => above(node.context.len()),
            })
            .sum())
    }
}

/// [definition] **The declared draw family** of a tree source: the alphabet, the depth `d` and the
/// faces' grid `g` (numerators on `1/g`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeSourceFamily {
    pub alphabet: usize,
    pub depth: usize,
    pub grid: u64,
}

/// [definition] **A tree source** (module header): a shift-closed tree, a face a leaf on the grid
/// `1/g`, and the declared initial past (newest first, at least the tree's depth).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeSource {
    tree: ContextTree,
    grid: u64,
    numerators: Vec<Vec<u64>>,
    initial: Vec<usize>,
}

/// [definition] **The tree source's exact truth receipt** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeSourceTruth {
    pub leaves: Vec<Vec<usize>>,
    pub faces: Vec<Vec<Rat>>,
    pub stationary: Vec<Rat>,
    pub rate: SymbolicSurprisal,
    pub rate_bits: ExactInterval,
}

/// [definition] **A realized passage read by the source**: each leaf's class counts from the
/// initial past, and the source's own code `−log₂ P_θ(x)` as its exact form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Passage {
    pub counts: Vec<Vec<u64>>,
    pub code: SymbolicSurprisal,
}

/// [definition] **The weighting bound** of a passage at a receiver of depth `D` (module header):
/// the model cost `Γ(S′)`, each leaf's arrivals `n_s` at the receiver, the boundary cells, the
/// parameter part `Σ_(n_s ≥ 1) (½ log₂ n_s + 1)`, and their total.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WeightingBound {
    pub model: u64,
    pub visits: Vec<u64>,
    pub boundary: u64,
    pub parameters: ExactInterval,
    pub total: ExactInterval,
}

/// [definition] **The recovered tree against the drawn one** (module header): the drawn leaves and
/// the minimal ones ([`TreeSource::minimal`]), the recovered leaves over the visited addresses, the
/// addresses of the receiver's depth, those whose recovered leaf is the drawn one and those whose is
/// the minimal one, those never visited below their stored path, and whether the recovery is exact
/// against each (every address visited and agreeing).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Recovery {
    pub drawn: Vec<Vec<usize>>,
    pub minimal: Vec<Vec<usize>>,
    pub recovered: Vec<Vec<usize>>,
    pub addresses: usize,
    pub agree: usize,
    pub agree_minimal: usize,
    pub unvisited: usize,
    pub exact: bool,
    pub exact_minimal: bool,
}

impl TreeSource {
    /// The declared source; refused unless the tree is shift-closed, each leaf's numerators are
    /// `|A|` positive integers summing to `g`, and the initial past covers the tree's depth.
    pub fn new(
        tree: ContextTree,
        grid: u64,
        numerators: Vec<Vec<u64>>,
        initial: Vec<usize>,
    ) -> Result<Self, TerrainError> {
        if !tree.is_shift_closed() {
            return Err(refuse(
                "a tree source",
                "its tree's leaves are not closed under the shift",
            ));
        }
        if numerators.len() != tree.leaves.len()
            || numerators.iter().any(|face| {
                face.len() != tree.alphabet
                    || face.contains(&0)
                    || face.iter().sum::<u64>() != grid
            })
        {
            return Err(refuse(
                "a tree source",
                "each leaf's face is |A| positive numerators summing to the grid",
            ));
        }
        if initial.len() < tree.depth() || initial.iter().any(|cell| *cell >= tree.alphabet) {
            return Err(refuse(
                "a tree source",
                "its initial past covers the tree's depth over its alphabet",
            ));
        }
        Ok(Self {
            tree,
            grid,
            numerators,
            initial,
        })
    }

    /// **The source drawn from its family** (module header, "The draw").
    pub fn draw(family: &TreeSourceFamily, draw: &mut Draw) -> Result<Self, TerrainError> {
        let TreeSourceFamily {
            alphabet,
            depth,
            grid,
        } = *family;
        if grid < alphabet as u64 {
            return Err(refuse(
                "a tree source family",
                "its grid holds a positive numerator for every letter",
            ));
        }
        let tree = ContextTree::draw(alphabet, depth, draw)?;
        let numerators = (0..tree.leaves.len())
            .map(|_| composition(grid, alphabet, draw))
            .collect();
        let initial = (0..depth).map(|_| draw.below(alphabet)).collect();
        Self::new(tree, grid, numerators, initial)
    }

    pub fn tree(&self) -> &ContextTree {
        &self.tree
    }

    pub fn grid(&self) -> u64 {
        self.grid
    }

    /// The initial past, newest first.
    pub fn initial(&self) -> &[usize] {
        &self.initial
    }

    /// **The face of a leaf**, exact.
    pub fn face(&self, leaf: usize) -> Vec<Rat> {
        self.numerators[leaf]
            .iter()
            .map(|n| Rat::new(BigInt::from(*n), BigInt::from(self.grid)))
            .collect()
    }

    /// The true leaf of each cell of a passage, read from the initial past.
    fn true_leaves(&self, cells: &[usize]) -> Vec<usize> {
        let mut history: Vec<usize> = self.initial.iter().rev().copied().collect();
        history.reserve(cells.len());
        let mut leaves = Vec::with_capacity(cells.len());
        for &cell in cells {
            leaves.push(
                self.tree
                    .leaf(history.iter().rev().copied())
                    .expect("the initial past covers the tree's depth"),
            );
            history.push(cell);
        }
        leaves
    }

    /// **The first `cells` cells**: each drawn from the face of the leaf its past reaches, exactly
    /// (a draw below the grid read against the face's cumulative numerators).
    pub fn emit(&self, cells: usize, draw: &mut Draw) -> Vec<usize> {
        let mut history: Vec<usize> = self.initial.iter().rev().copied().collect();
        history.reserve(cells);
        let grid = usize::try_from(self.grid).expect("a grid within a machine word");
        for _ in 0..cells {
            let leaf = self
                .tree
                .leaf(history.iter().rev().copied())
                .expect("the initial past covers the tree's depth");
            let mut point = draw.below(grid) as u64;
            let class = self.numerators[leaf]
                .iter()
                .position(|n| {
                    if point < *n {
                        true
                    } else {
                        point -= n;
                        false
                    }
                })
                .expect("the numerators sum to the grid");
            history.push(class);
        }
        history.split_off(self.initial.len())
    }

    /// **The leaf chain** (module header): `P(s → leafOf(c :: s)) = θ_s(c)`, one state a leaf. The
    /// shift closure makes the next leaf a function of `c` and `s`, whatever lies past `s`.
    pub fn chain(&self) -> Result<MarkovChain, TerrainError> {
        let leaves = self.tree.leaves();
        let n = leaves.len();
        let depth = self.tree.depth();
        let mut rows = vec![vec![Rat::zero(); n]; n];
        for (from, context) in leaves.iter().enumerate() {
            let mut padded = context.clone();
            padded.resize(depth, 0);
            for (class, probability) in self.face(from).into_iter().enumerate() {
                let to = self
                    .tree
                    .leaf(std::iter::once(class).chain(padded.iter().copied()))
                    .expect("a shifted address of the tree's depth reaches a leaf");
                rows[from][to] += probability;
            }
        }
        Ok(MarkovChain::new(ExactRatMatrix::shaped(n, n, rows)?)?)
    }

    /// **The tree source's exact truth receipt** (module header).
    pub fn truth(&self) -> Result<TreeSourceTruth, TerrainError> {
        let stationary = self.chain()?.stationary_law()?;
        let mut rate = SymbolicSurprisal::zero();
        for (leaf, weight) in stationary.iter().enumerate() {
            for probability in self.face(leaf) {
                rate = rate.plus(
                    &SymbolicSurprisal::of_probability(&probability)?
                        .scaled(&(weight * &probability)),
                );
            }
        }
        let rate_bits = rate.enclosure()?;
        Ok(TreeSourceTruth {
            leaves: self.tree.leaves(),
            faces: (0..self.tree.leaves.len()).map(|leaf| self.face(leaf)).collect(),
            stationary,
            rate,
            rate_bits,
        })
    }

    /// **A realized passage read by the source** ([`Passage`]): each leaf's class counts from the
    /// initial past, and the source's own code `Σ_(s,c) n_(s,c) (−log₂ θ_s(c))`, exact.
    pub fn passage(&self, cells: &[usize]) -> Result<Passage, TerrainError> {
        let mut counts = vec![vec![0u64; self.tree.alphabet]; self.tree.leaves.len()];
        for (leaf, &cell) in self.true_leaves(cells).into_iter().zip(cells) {
            if cell >= self.tree.alphabet {
                return Err(refuse("a passage", "a cell lies outside the alphabet"));
            }
            counts[leaf][cell] += 1;
        }
        let mut code = SymbolicSurprisal::zero();
        for (leaf, classes) in counts.iter().enumerate() {
            for (probability, count) in self.face(leaf).iter().zip(classes) {
                if *count > 0 {
                    code = code.plus(
                        &SymbolicSurprisal::of_probability(probability)?
                            .scaled(&Rat::from_integer(BigInt::from(*count))),
                    );
                }
            }
        }
        Ok(Passage { counts, code })
    }

    /// **The weighting bound of a passage at a receiver of depth `D`** (module header): binary
    /// only, and `D` at least the tree's depth.
    pub fn weighting_bound(
        &self,
        cells: &[usize],
        receiver_depth: usize,
    ) -> Result<WeightingBound, TerrainError> {
        if self.tree.alphabet != 2 {
            return Err(refuse(
                "a weighting bound",
                "the KT parameter bound is a binary leaf's",
            ));
        }
        let model = self.tree.cost(receiver_depth)?;
        let mut visits = vec![0u64; self.tree.leaves.len()];
        let mut boundary = 0u64;
        for position in 0..cells.len() {
            match self.tree.leaf(cells[..position].iter().rev().copied()) {
                Some(leaf) => visits[leaf] += 1,
                None => boundary += 1,
            }
        }
        let mut parameters = ExactInterval::point(Rat::zero());
        let half = Rat::new(BigInt::one(), BigInt::from(2));
        for &n in visits.iter().filter(|n| **n > 0) {
            let log = log2_enclosure(&Rat::from_integer(BigInt::from(n)))?;
            let term = ExactInterval {
                lower: &log.lower * &half + Rat::one(),
                upper: &log.upper * &half + Rat::one(),
            };
            parameters = interval_sum(&parameters, &term)?;
        }
        let total = interval_sum(
            &parameters,
            &ExactInterval::point(Rat::from_integer(BigInt::from(model + boundary))),
        )?;
        Ok(WeightingBound {
            model,
            visits,
            boundary,
            parameters,
            total,
        })
    }

    /// Each node's one face when every leaf below it holds that face.
    fn uniform(&self) -> Vec<Option<&[u64]>> {
        let mut uniform: Vec<Option<&[u64]>> = vec![None; self.tree.nodes.len()];
        let mut order: Vec<usize> = (0..self.tree.nodes.len()).collect();
        order.sort_by_key(|&node| std::cmp::Reverse(self.tree.nodes[node].context.len()));
        for node in order {
            uniform[node] = match &self.tree.nodes[node].children {
                None => Some(self.numerators[self.tree.index[node]].as_slice()),
                Some(children) => {
                    let first = uniform[children[0]];
                    first.filter(|face| children.iter().all(|&c| uniform[c] == Some(*face)))
                }
            };
        }
        uniform
    }

    /// The depth at which the minimal tree stops along an address of the tree's depth.
    fn minimal_depth(&self, uniform: &[Option<&[u64]>], address: &[usize]) -> usize {
        let mut node = 0usize;
        for &letter in address {
            if uniform[node].is_some() {
                break;
            }
            node = self.tree.nodes[node].children.as_ref().expect("a split node")[letter];
        }
        self.tree.nodes[node].context.len()
    }

    /// [definition; agent-inferred] **The minimal tree**: the coarsest pruned tree reading the same
    /// faces, each split whose leaves below all hold one face merged into a leaf. Two drawn trees
    /// with one minimal tree are one source; their difference is the source's kernel, which no
    /// receiver distinguishes, so a recovered tree is read against it as well as the drawn one.
    pub fn minimal(&self) -> Vec<Vec<usize>> {
        let uniform = self.uniform();
        let mut leaves = Vec::new();
        let mut stack = vec![0usize];
        while let Some(node) = stack.pop() {
            match (&self.tree.nodes[node].children, uniform[node]) {
                (Some(children), None) => stack.extend(children.iter().copied()),
                _ => leaves.push(self.tree.nodes[node].context.clone()),
            }
        }
        leaves.sort();
        leaves
    }

    /// **The tree the receiver's standing recovers** (module header): binary only, the standing
    /// declared over the cell-only family at a depth at least the tree's.
    pub fn recovery(&self, standing: &Landmarks) -> Result<Recovery, TerrainError> {
        let declaration = standing.declaration();
        let depth = declaration.depth;
        if self.tree.alphabet != 2 || declaration.alphabet != 2 || depth < self.tree.depth() {
            return Err(refuse(
                "a recovered tree",
                "the standing is binary, over the source's alphabet, at least the tree's depth",
            ));
        }
        let uniform = self.uniform();
        let mut recovered = BTreeSet::new();
        let (mut agree, mut agree_minimal, mut unvisited) = (0usize, 0usize, 0usize);
        let addresses = self.tree.addresses(depth);
        for address in &addresses {
            let letters: Vec<Letter> = address.iter().map(|&cell| Letter::Cell(cell)).collect();
            let paths = standing.opened(&letters, 0)?;
            let path = paths
                .iter()
                .find(|path| path.branch == 0)
                .ok_or_else(|| refuse("a recovered tree", "no cell path opens at the address"))?;
            let mut top = 0usize;
            let mut stop = None;
            for level in 0..path.founded {
                if top < depth && path.betas[level] > Rat::one() {
                    stop = Some(top);
                    break;
                }
                top = path.bottoms[level] + 1;
            }
            let reached = match stop {
                Some(at) => at,
                None if top >= depth => depth,
                None => {
                    unvisited += 1;
                    continue;
                }
            };
            recovered.insert(address[..reached].to_vec());
            let drawn = self
                .tree
                .leaf(address.iter().copied())
                .expect("an address of the tree's depth reaches a leaf");
            if self.tree.nodes[self.tree.leaves[drawn]].context.len() == reached {
                agree += 1;
            }
            if self.minimal_depth(&uniform, &address[..self.tree.depth()]) == reached {
                agree_minimal += 1;
            }
        }
        let (drawn, minimal) = (self.tree.leaves(), self.minimal());
        let recovered: Vec<Vec<usize>> = recovered.into_iter().collect();
        let all = addresses.len();
        let exact = unvisited == 0 && agree == all && recovered == drawn;
        let exact_minimal = unvisited == 0 && agree_minimal == all && recovered == minimal;
        Ok(Recovery {
            drawn,
            minimal,
            recovered,
            addresses: all,
            agree,
            agree_minimal,
            unvisited,
            exact,
            exact_minimal,
        })
    }
}

/// **A uniform composition of `grid` into `parts` positive parts**: `parts − 1` distinct cut points
/// among the `grid − 1` interior points, drawn by a partial Fisher–Yates shuffle.
fn composition(grid: u64, parts: usize, draw: &mut Draw) -> Vec<u64> {
    let mut points: Vec<u64> = (1..grid).collect();
    for i in 0..parts - 1 {
        let j = i + draw.below(points.len() - i);
        points.swap(i, j);
    }
    let mut cuts: Vec<u64> = points[..parts - 1].to_vec();
    cuts.sort_unstable();
    let mut previous = 0u64;
    let mut numerators = Vec::with_capacity(parts);
    for cut in cuts.into_iter().chain(std::iter::once(grid)) {
        numerators.push(cut - previous);
        previous = cut;
    }
    numerators
}
