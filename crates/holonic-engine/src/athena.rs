//! **ATHENA — the chart transition from a holonic atlas to a tensor container.**
//!
//! Brandon, 2026-08-18: *"derive the transition using holonics… between the transition mechanisms
//! and the emergent floating point collections that are tensors as they relate to I/O in embedding
//! spaces during inference"*, and the target: *"figure out how to use holonics to optimally train
//! and freeze models into safetensors using our engine in order to transfigure layers and produce
//! sophisticated complex neural networks that are not like classically pretrained transformers."*
//!
//! # The navigation reading, which is the derivation and not an analogy
//!
//! A well-built game agent does not scan world coordinates. It decomposes the world into regions in
//! which any point reaches any other directly, connects them by portals, searches the **region
//! graph**, and only then steers locally inside a region. The global coordinate is never stored; it
//! is **recovered by integrating local differences**. Landmarks are arbitrary and set by the
//! implementation — which is to say the grain is *declared*.
//!
//! A suffix automaton is that structure over material rather than over space:
//!
//! ```text
//!     navmesh region   ⟷  a transport class — an occurrence set; contexts that reach the same places
//!     portal           ⟷  a germ transition
//!     region hierarchy ⟷  the suffix-link tree; climbing is zooming out
//!     landmark grain   ⟷  the declared height climbed
//!     local steering   ⟷  the walk inside a class's length interval
//!     re-plan coarser  ⟷  the ARC: no forward portal, so fall to a shorter context
//! ```
//!
//! **So the atlas is a hierarchical navmesh over material, and generation is pathfinding on it.**
//! The path in "global coordinates" is the integral of the local differences — integration by
//! reflection, discrete, with the geometry implicit.
//!
//! # The transition, and what each part costs
//!
//! The atlas is `(S, δ, π, μ)`: classes, germ transitions, suffix links, standing. A tensor chart is
//! `R^d` with linear operators. The transition splits **exactly**, and the split is the derivation:
//!
//! | what is preserved | cost | remainder |
//! |---|---|---|
//! | ancestry and scale — the tree `π` | **2 dimensions** | **zero** |
//! | standing `μ` | 1 dimension | zero |
//! | transport `δ` as a linear operator | the cycle rank `β₁ = |E| − |S| + 1` | the cycle space, quotiented if fewer |
//!
//! **The tree part is free and this module builds it.** A depth-first interval labelling sends each
//! class to `[in, out]`, and containment of intervals is exactly suffix-link ancestry — the
//! condensation `CLAUDE.md` §11 calls *free, because the incidence is a tree*.
//!
//! **And the interval is a Minkowski point.** Writing `[a, b]` as `(t, x) = ((a+b)/2, (b−a)/2)`,
//!
//! ```text
//!     [a₁,b₁] ⊆ [a₂,b₂]   ⟺   |t₁ − t₂| ≤ x₂ − x₁
//! ```
//!
//! which is the **light-cone order** of `1+1` Minkowski space. Ancestry is causal precedence; two
//! classes neither of which contains the other are **spacelike**; classes that touch sit on the
//! **null cone**. So the declared signature of an Athena embedding is `(+, −)` and not Euclidean,
//! and the invariant between two tokens is `t² − x²`, exact over the rationals — the object
//! `clifford::Arrow` computes under `Signature::declared([1, -1])` and `exact_contact` already
//! refuses correctly on the null cone.
//!
//! **What is NOT free is `δ`**, because the transition graph is not a tree. Its departure from
//! tree-ness is the cycle rank, and that population is reconvergence: distinct contexts landing in
//! one class. A container of dimension below it has declared a receiver family that cannot separate
//! some cycles, and the collapsed population is the compression's exact loss — never an unknown.
//!
//! # A layer is a scale, not a learned depth
//!
//! Athena's layer `k` is **the atlas read at height `k` up the suffix-link tree**. The layer count
//! is the tree's height and is not chosen; each layer is the same material at a coarser grain, which
//! is the self-similarity the tree already carries. Nothing is trained to produce layer `k+1` from
//! layer `k` — the coarsening is a fact about occurrence sets.
//!
//! # Every float carries its exact preimage
//!
//! Emission rounds exact rationals into the target format through
//! [`crate::exact_value::ieee754::round_into`], which returns the **exact rational residual**, so a
//! quantisation is a certified remainder rather than an unknown error. The read side already inverts
//! it: `embedding_fiber::align_bfloat16` returns integers and a common exponent with zero remainder.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;
use thiserror::Error;

use crate::exact_value::ieee754::{BinaryFloatSpecies, round_into_bfloat16};

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum AthenaError {
    #[error("the atlas declares no classes, so there is no tree to label")]
    EmptyAtlas,
    #[error("class {state} names a suffix parent {parent} that the atlas does not declare")]
    DanglingLink { state: u32, parent: u32 },
    #[error("the emitted row population is empty")]
    EmptyRows,
    #[error("a row has width {width} against a declared {declared}")]
    RaggedRow { width: usize, declared: usize },
    #[error("the exact value {value} could not cross into {species}: {reason}")]
    MouthRefused {
        value: String,
        species: &'static str,
        reason: String,
    },
}

/// **The tree half of the transition, and it costs nothing.**
///
/// A depth-first interval per class, so containment of intervals **is** suffix-link ancestry. This
/// is the condensation that is free because the incidence is a tree; the remainder is empty.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeChart {
    /// `[entry, exit]` per class, indexed by class.
    pub intervals: Vec<(u64, u64)>,
    /// The height of the tree — **the layer count, read off the material rather than chosen.**
    pub height: u32,
}

impl TreeChart {
    /// Label a suffix-link tree by depth-first entry and exit.
    ///
    /// `parent_of(state)` returns the class's suffix parent, or `None` at the root. The traversal is
    /// an explicit stack: a tree of twenty-five thousand classes must not be walked by recursion.
    pub fn label(
        classes: usize,
        parent_of: impl Fn(u32) -> Option<u32>,
    ) -> Result<Self, AthenaError> {
        if classes == 0 {
            return Err(AthenaError::EmptyAtlas);
        }
        let mut children: Vec<Vec<u32>> = vec![Vec::new(); classes];
        let mut roots: Vec<u32> = Vec::new();
        for state in 0..classes {
            let at = state as u32;
            match parent_of(at) {
                None => roots.push(at),
                Some(parent) => {
                    let parent_at = parent as usize;
                    if parent_at >= classes {
                        return Err(AthenaError::DanglingLink { state: at, parent });
                    }
                    children[parent_at].push(at);
                }
            }
        }
        let mut intervals = vec![(0u64, 0u64); classes];
        let mut clock = 0u64;
        let mut height = 0u32;
        // (state, depth, whether its children have been pushed)
        let mut stack: Vec<(u32, u32, bool)> =
            roots.into_iter().map(|root| (root, 0, false)).collect();
        while let Some((state, depth, expanded)) = stack.pop() {
            let at = state as usize;
            if expanded {
                intervals[at].1 = clock;
                continue;
            }
            intervals[at].0 = clock;
            clock += 1;
            height = height.max(depth);
            stack.push((state, depth, true));
            for child in children[at].iter().rev() {
                stack.push((*child, depth + 1, false));
            }
        }
        Ok(Self { intervals, height })
    }

    /// **The class's Minkowski coordinate**: `(t, x) = (centre, radius)` of its interval.
    ///
    /// Ancestry is the light-cone order in this chart, so the declared signature is `(+, −)`. The
    /// halves are carried as exact rationals — a centre of an odd-width interval is a half-integer
    /// and rounding it here would be the deletion this whole carrier exists to refuse.
    pub fn minkowski(&self, state: u32) -> Option<(Rat, Rat)> {
        let (entry, exit) = self.intervals.get(state as usize).copied()?;
        let two = BigInt::from(2);
        let entry = BigInt::from(entry);
        let exit = BigInt::from(exit);
        Some((
            Rat::new(&entry + &exit, two.clone()),
            Rat::new(&exit - &entry, two),
        ))
    }

    /// Does `outer`'s interval contain `inner`'s — that is, is `outer` a suffix-link ancestor?
    ///
    /// **Checked as the causal order rather than by walking links**, which is the point of the
    /// chart: `|t₁ − t₂| ≤ x₂ − x₁`.
    pub fn contains(&self, outer: u32, inner: u32) -> Option<bool> {
        let (outer_t, outer_x) = self.minkowski(outer)?;
        let (inner_t, inner_x) = self.minkowski(inner)?;
        let separation = &inner_t - &outer_t;
        let separation = if num_traits::Signed::is_negative(&separation) {
            -separation
        } else {
            separation
        };
        Some(separation <= &outer_x - &inner_x)
    }
}

/// One emitted tensor: exact rational rows, and what crossing into the format cost.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EmittedTensor {
    pub name: String,
    pub rows: usize,
    pub width: usize,
    /// The stored `BF16` words, row-major.
    pub words: Vec<u16>,
    /// **The exact residual of every entry**, in the same order. `entry = stored + residual`,
    /// exactly, over the rationals.
    pub residuals: Vec<Rat>,
}

impl EmittedTensor {
    /// How many entries crossed with **nothing** deleted.
    pub fn exact_entries(&self) -> usize {
        self.residuals.iter().filter(|r| r.is_zero()).count()
    }

    /// The greatest residual magnitude, exhibited rather than summarised as a tolerance.
    pub fn widest_residual(&self) -> Rat {
        self.residuals
            .iter()
            .map(|residual| {
                if num_traits::Signed::is_negative(residual) {
                    -residual.clone()
                } else {
                    residual.clone()
                }
            })
            .max()
            .unwrap_or_else(Rat::zero)
    }
}

/// Round an exact rational matrix into `BF16`, keeping every residual.
pub fn emit_tensor(
    name: impl Into<String>,
    rows: &[Vec<Rat>],
) -> Result<EmittedTensor, AthenaError> {
    let name = name.into();
    let declared = rows.first().ok_or(AthenaError::EmptyRows)?.len();
    let mut words = Vec::with_capacity(rows.len() * declared);
    let mut residuals = Vec::with_capacity(rows.len() * declared);
    for row in rows {
        if row.len() != declared {
            return Err(AthenaError::RaggedRow {
                width: row.len(),
                declared,
            });
        }
        for entry in row {
            let (word, residual) =
                round_into_bfloat16(entry).map_err(|error| AthenaError::MouthRefused {
                    value: entry.to_string(),
                    species: BinaryFloatSpecies::Bfloat16.name(),
                    reason: format!("{error}"),
                })?;
            words.push(word);
            residuals.push(residual);
        }
    }
    Ok(EmittedTensor {
        name,
        rows: rows.len(),
        width: declared,
        words,
        residuals,
    })
}

/// **An integer tensor: no rounding, no residual, no float anywhere.**
///
/// **`BF16` cannot hold an index.** Eight significand bits means every integer above 256 is
/// unrepresentable, so a container whose content is *structure* — class identities, targets, offsets
/// — must carry integer dtypes. The industry's containers are `BF16` throughout because their
/// content is magnitudes; the moment the content is a graph, that choice is wrong rather than
/// merely lossy.
///
/// Measured 2026-08-18 and it is why this exists: the Hankel rank of real material does **not**
/// saturate — 1,638 of 2,048 at the widest aperture swept, against 25,030 classes — so there is no
/// small linear representation and a dense chart is an *expansion*. The transport is natively a
/// sparse partial function and it crosses as one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntegerTensor {
    pub name: String,
    pub rows: usize,
    pub width: usize,
    pub dtype: IntegerDtype,
    /// Little-endian octets, row-major.
    pub octets: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntegerDtype {
    U16,
    U32,
}

impl IntegerDtype {
    pub const fn name(self) -> &'static str {
        match self {
            Self::U16 => "U16",
            Self::U32 => "U32",
        }
    }

    pub const fn octets(self) -> usize {
        match self {
            Self::U16 => 2,
            Self::U32 => 4,
        }
    }

    /// The greatest value this carrier holds. A value past it **refuses**: a silently wrapped index
    /// addresses the wrong class, which is worse than a rounding error because nothing about it is
    /// small.
    pub const fn ceiling(self) -> u64 {
        match self {
            Self::U16 => u16::MAX as u64,
            Self::U32 => u32::MAX as u64,
        }
    }
}

/// Lay a population of integers into a tensor, refusing any value the carrier cannot hold.
pub fn emit_integers(
    name: impl Into<String>,
    values: &[u64],
    width: usize,
    dtype: IntegerDtype,
) -> Result<IntegerTensor, AthenaError> {
    if width == 0 || values.is_empty() {
        return Err(AthenaError::EmptyRows);
    }
    if values.len() % width != 0 {
        return Err(AthenaError::RaggedRow {
            width: values.len() % width,
            declared: width,
        });
    }
    let mut octets = Vec::with_capacity(values.len() * dtype.octets());
    for value in values {
        if *value > dtype.ceiling() {
            return Err(AthenaError::MouthRefused {
                value: value.to_string(),
                species: dtype.name(),
                reason: format!("past the carrier's ceiling of {}", dtype.ceiling()),
            });
        }
        match dtype {
            IntegerDtype::U16 => octets.extend_from_slice(&(*value as u16).to_le_bytes()),
            IntegerDtype::U32 => octets.extend_from_slice(&(*value as u32).to_le_bytes()),
        }
    }
    Ok(IntegerTensor {
        name: name.into(),
        rows: values.len() / width,
        width,
        dtype,
        octets,
    })
}

/// Serialise integer tensors as a `safetensors` container. Every entry crosses **exactly**.
pub fn integer_container(tensors: &[IntegerTensor]) -> Vec<u8> {
    let mut header = String::from("{");
    let mut offset = 0usize;
    for (at, tensor) in tensors.iter().enumerate() {
        if at > 0 {
            header.push(',');
        }
        let end = offset + tensor.octets.len();
        header.push_str(&format!(
            "\"{}\":{{\"dtype\":\"{}\",\"shape\":[{},{}],\"data_offsets\":[{offset},{end}]}}",
            tensor.name,
            tensor.dtype.name(),
            tensor.rows,
            tensor.width
        ));
        offset = end;
    }
    header.push('}');
    while header.len() % 8 != 0 {
        header.push(' ');
    }
    let mut octets = Vec::with_capacity(8 + header.len() + offset);
    octets.extend_from_slice(&(header.len() as u64).to_le_bytes());
    octets.extend_from_slice(header.as_bytes());
    for tensor in tensors {
        octets.extend_from_slice(&tensor.octets);
    }
    octets
}

/// Serialise emitted tensors as a `safetensors` container.
///
/// **The header is written by hand and deliberately so.** It is the whole of what the format is —
/// a length, a JSON map of `name → {dtype, shape, data_offsets}`, and a flat payload — and writing
/// it here rather than through a dependency keeps the boundary declared in one place, in the
/// project's own source, where the reader already lives.
pub fn safetensors_container(tensors: &[EmittedTensor]) -> Vec<u8> {
    let mut entries: BTreeMap<&str, (usize, usize, usize, usize)> = BTreeMap::new();
    let mut offset = 0usize;
    for tensor in tensors {
        let octets = tensor.words.len() * 2;
        entries.insert(
            tensor.name.as_str(),
            (tensor.rows, tensor.width, offset, offset + octets),
        );
        offset += octets;
    }
    let mut header = String::from("{");
    let mut first = true;
    for (name, (rows, width, start, end)) in &entries {
        if !first {
            header.push(',');
        }
        first = false;
        header.push_str(&format!(
            "\"{name}\":{{\"dtype\":\"BF16\",\"shape\":[{rows},{width}],\"data_offsets\":[{start},{end}]}}"
        ));
    }
    header.push('}');
    // The format wants the header padded to an eight-octet boundary.
    while header.len() % 8 != 0 {
        header.push(' ');
    }
    let mut octets = Vec::with_capacity(8 + header.len() + offset);
    octets.extend_from_slice(&(header.len() as u64).to_le_bytes());
    octets.extend_from_slice(header.as_bytes());
    for tensor in tensors {
        for word in &tensor.words {
            octets.extend_from_slice(&word.to_le_bytes());
        }
    }
    octets
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small tree: 0 is the root, 1 and 2 are its children, 3 is a child of 1.
    fn parent_of(state: u32) -> Option<u32> {
        match state {
            0 => None,
            1 | 2 => Some(0),
            3 => Some(1),
            _ => None,
        }
    }

    #[test]
    fn the_interval_labelling_makes_ancestry_the_causal_order() {
        let chart = TreeChart::label(4, parent_of).expect("labels");
        assert_eq!(chart.height, 2);
        // Every real ancestry holds as containment, read in the Minkowski chart rather than by
        // walking a single link.
        for (outer, inner) in [(0u32, 1u32), (0, 2), (0, 3), (1, 3)] {
            assert_eq!(
                chart.contains(outer, inner),
                Some(true),
                "{outer} should contain {inner}"
            );
        }
        // And every non-ancestry is spacelike, in both directions.
        for (left, right) in [(1u32, 2u32), (2, 3), (3, 0), (1, 0)] {
            assert_eq!(
                chart.contains(left, right),
                Some(false),
                "{left} must not contain {right}"
            );
        }
    }

    #[test]
    fn a_class_contains_itself_on_the_null_cone() {
        let chart = TreeChart::label(4, parent_of).expect("labels");
        for state in 0..4u32 {
            assert_eq!(chart.contains(state, state), Some(true));
        }
    }

    #[test]
    fn an_emitted_tensor_keeps_every_residual_and_the_container_reads_back() {
        // Two dyadic rows and one that is not representable, so both arms are exercised.
        let rows = vec![
            vec![Rat::new(1.into(), 2.into()), Rat::new(3.into(), 4.into())],
            vec![Rat::new(1.into(), 10.into()), Rat::new(0.into(), 1.into())],
        ];
        let tensor = emit_tensor("athena.probe", &rows).expect("emits");
        assert_eq!(tensor.rows, 2);
        assert_eq!(tensor.width, 2);
        assert_eq!(tensor.words.len(), 4);
        // Three of the four are exactly representable; a tenth is not.
        assert_eq!(tensor.exact_entries(), 3);
        assert!(!tensor.widest_residual().is_zero());
        // Every entry closes: stored + residual = the exact value that was asked for.
        for (at, residual) in tensor.residuals.iter().enumerate() {
            let stored = crate::exact_value::ieee754::decode_bfloat16_bits(tensor.words[at])
                .expect("decodes")
                .value();
            let wanted = &rows[at / 2][at % 2];
            assert_eq!(&(stored + residual.clone()), wanted);
        }

        let container = safetensors_container(std::slice::from_ref(&tensor));
        // The container must parse under the project's own reader, which is the only intake.
        let length = u64::from_le_bytes(container[..8].try_into().unwrap()) as usize;
        let header = core::str::from_utf8(&container[8..8 + length]).expect("utf8");
        assert!(header.contains("\"athena.probe\""));
        assert!(header.contains("\"dtype\":\"BF16\""));
        assert!(header.contains("\"shape\":[2,2]"));
        assert_eq!(container.len(), 8 + length + tensor.words.len() * 2);
    }

    #[test]
    fn a_ragged_row_population_refuses_rather_than_padding() {
        let rows = vec![
            vec![Rat::new(1.into(), 2.into())],
            vec![Rat::new(1.into(), 2.into()), Rat::new(1.into(), 4.into())],
        ];
        assert!(matches!(
            emit_tensor("athena.ragged", &rows),
            Err(AthenaError::RaggedRow { .. })
        ));
    }
}
