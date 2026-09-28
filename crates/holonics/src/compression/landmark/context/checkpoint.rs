//! Canonical durable representation of the landmark tree's contemporary standing.
//!
//! This is a state codec, not a passage archive: the arena, carried charts, registers and
//! counters are written directly. The declaration is supplied by the caller and its exact
//! canonical form is bound into the payload.

use super::*;
use std::collections::HashMap;
use thiserror::Error;

const MAGIC: &[u8; 8] = b"HLAND\0\0\x01";

/// A refusal to encode or restore a landmark standing.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum StandingCodecError {
    #[error("unsupported landmark standing format version")]
    Version,
    #[error("landmark standing declaration does not match the supplied declaration")]
    Declaration,
    #[error("malformed landmark standing at byte {offset}: {reason}")]
    Malformed { offset: usize, reason: &'static str },
    #[error("landmark standing has trailing bytes")]
    Trailing,
    #[error("landmark standing contains inconsistent topology or chart state")]
    Inconsistent,
}

struct Writer(Vec<u8>);

impl Writer {
    fn u8(&mut self, x: u8) {
        self.0.push(x);
    }
    fn u32(&mut self, x: u32) {
        self.0.extend_from_slice(&x.to_le_bytes());
    }
    fn u64(&mut self, x: u64) {
        self.0.extend_from_slice(&x.to_le_bytes());
    }
    fn i64(&mut self, x: i64) {
        self.0.extend_from_slice(&x.to_le_bytes());
    }
    fn u128(&mut self, x: u128) {
        self.0.extend_from_slice(&x.to_le_bytes());
    }
    fn len(&mut self, x: usize) {
        self.u64(u64::try_from(x).expect("usize fits the wire length"));
    }
    fn declaration(&mut self, d: &LandmarkDeclaration) {
        self.len(d.alphabet);
        self.len(d.depth);
        self.len(d.forced);
        self.u64(d.population);
        self.u64(d.grain);
        self.len(d.family.sizes.len());
        for &size in &d.family.sizes {
            self.u64(size);
        }
        self.len(d.prior.rungs.len());
        for &rung in &d.prior.rungs {
            self.u32(rung);
        }
        match d.capacity {
            Capacity::Unbounded => self.u8(0),
            Capacity::Ceiling(c) => {
                self.u8(1);
                self.u32(c);
            }
        }
    }
    fn chart(&mut self, c: Chart) {
        self.u64(c.beta.numerator);
        self.u64(c.beta.denominator);
        self.i64(c.beta.exponent);
        self.u64(c.stop);
        self.u32(c.rebases);
        self.u128(c.drift);
        self.u128(c.excess);
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn fail<T>(&self, reason: &'static str) -> Result<T, StandingCodecError> {
        Err(StandingCodecError::Malformed {
            offset: self.at,
            reason,
        })
    }
    fn take<const N: usize>(&mut self) -> Result<[u8; N], StandingCodecError> {
        let end = self
            .at
            .checked_add(N)
            .ok_or(StandingCodecError::Malformed {
                offset: self.at,
                reason: "length overflow",
            })?;
        let Some(slice) = self.bytes.get(self.at..end) else {
            return self.fail("truncated field");
        };
        self.at = end;
        Ok(slice.try_into().expect("fixed length"))
    }
    fn u8(&mut self) -> Result<u8, StandingCodecError> {
        Ok(self.take::<1>()?[0])
    }
    fn u32(&mut self) -> Result<u32, StandingCodecError> {
        Ok(u32::from_le_bytes(self.take()?))
    }
    fn u64(&mut self) -> Result<u64, StandingCodecError> {
        Ok(u64::from_le_bytes(self.take()?))
    }
    fn i64(&mut self) -> Result<i64, StandingCodecError> {
        Ok(i64::from_le_bytes(self.take()?))
    }
    fn u128(&mut self) -> Result<u128, StandingCodecError> {
        Ok(u128::from_le_bytes(self.take()?))
    }
    fn usize_value(&mut self) -> Result<usize, StandingCodecError> {
        usize::try_from(self.u64()?).map_err(|_| StandingCodecError::Malformed {
            offset: self.at,
            reason: "value does not fit this host",
        })
    }
    fn len(&mut self, minimum_item_bytes: usize) -> Result<usize, StandingCodecError> {
        let n = self.usize_value()?;
        if n > self.bytes.len().saturating_sub(self.at) / minimum_item_bytes.max(1) {
            return self.fail("length exceeds remaining input");
        }
        Ok(n)
    }
    fn chart(&mut self) -> Result<Chart, StandingCodecError> {
        Ok(Chart {
            beta: Beta {
                numerator: self.u64()?,
                denominator: self.u64()?,
                exponent: self.i64()?,
            },
            stop: self.u64()?,
            rebases: self.u32()?,
            drift: self.u128()?,
            excess: self.u128()?,
        })
    }
}

impl Landmarks {
    /// Encode the exact current tree standing in canonical little-endian form.
    pub fn encode_standing(&self) -> Vec<u8> {
        let mut w = Writer(MAGIC.to_vec());
        w.declaration(&self.law.declaration);
        let a = &self.nodes.arena;
        w.len(a.roots.len());
        for root in &a.roots {
            match root {
                None => w.u8(0),
                Some(n) => {
                    w.u8(1);
                    w.u32(*n);
                }
            }
        }
        let mut children: Vec<_> = a.children.iter().map(|(&k, &v)| (k, v)).collect();
        children.sort_unstable_by_key(|&(k, _)| k);
        w.len(children.len());
        for (k, v) in children {
            w.u64(k);
            w.u32(v);
        }
        for values in [&a.depths, &a.ends] {
            w.len(values.len());
            for &x in values {
                w.u32(x);
            }
        }
        w.len(a.halves.len());
        for h in &a.halves {
            w.u32(h[0]);
            w.u32(h[1]);
        }
        w.len(a.letters.len());
        for &x in &a.letters {
            w.u32(x);
        }
        w.len(self.nodes.charts.len());
        for &c in &self.nodes.charts {
            w.chart(c);
        }
        w.len(self.nodes.joins.len());
        for &c in &self.nodes.joins {
            w.chart(c);
        }
        w.u64(self.nodes.rebases);
        w.u64(self.nodes.releases);
        w.u64(self.nodes.passed);
        w.0
    }

    /// Restore a standing directly from its state bytes, requiring the caller's declaration.
    pub fn decode_standing(
        declaration: LandmarkDeclaration,
        bytes: &[u8],
    ) -> Result<Self, StandingCodecError> {
        if bytes.len() < MAGIC.len() || &bytes[..MAGIC.len()] != MAGIC {
            return Err(StandingCodecError::Version);
        }
        let mut r = Reader {
            bytes,
            at: MAGIC.len(),
        };
        let mut declared = Writer(Vec::new());
        declared.declaration(&declaration);
        let alphabet = r.usize_value()?;
        let depth = r.usize_value()?;
        let forced = r.usize_value()?;
        let population = r.u64()?;
        let grain = r.u64()?;
        let slots = r.len(8)?;
        let mut sizes = Vec::with_capacity(slots);
        for _ in 0..slots {
            sizes.push(r.u64()?);
        }
        let rungs_len = r.len(4)?;
        let mut rungs = Vec::with_capacity(rungs_len);
        for _ in 0..rungs_len {
            rungs.push(r.u32()?);
        }
        let capacity = match r.u8()? {
            0 => Capacity::Unbounded,
            1 => Capacity::Ceiling(r.u32()?),
            _ => return r.fail("invalid capacity tag"),
        };
        let mut actual = Writer(Vec::new());
        actual.len(alphabet);
        actual.len(depth);
        actual.len(forced);
        actual.u64(population);
        actual.u64(grain);
        actual.len(sizes.len());
        for x in sizes {
            actual.u64(x);
        }
        actual.len(rungs.len());
        for x in rungs {
            actual.u32(x);
        }
        match capacity {
            Capacity::Unbounded => actual.u8(0),
            Capacity::Ceiling(c) => {
                actual.u8(1);
                actual.u32(c);
            }
        }
        if actual.0 != declared.0 {
            return Err(StandingCodecError::Declaration);
        }
        let mut restored =
            Landmarks::new(declaration).map_err(|_| StandingCodecError::Declaration)?;
        let mut roots = Vec::new();
        let root_count = r.len(1)?;
        for _ in 0..root_count {
            roots.push(match r.u8()? {
                0 => None,
                1 => Some(r.u32()?),
                _ => return r.fail("invalid root tag"),
            });
        }
        let child_count = r.len(12)?;
        let mut children = HashMap::with_capacity(child_count);
        let mut last = None;
        for _ in 0..child_count {
            let key = r.u64()?;
            let child = r.u32()?;
            if last.is_some_and(|previous| previous >= key) || children.insert(key, child).is_some()
            {
                return r.fail("child keys are not canonical");
            }
            last = Some(key);
        }
        let read_u32s = |r: &mut Reader<'_>| -> Result<Vec<u32>, StandingCodecError> {
            let n = r.len(4)?;
            (0..n).map(|_| r.u32()).collect()
        };
        let depths = read_u32s(&mut r)?;
        let ends = read_u32s(&mut r)?;
        let halves_len = r.len(8)?;
        let mut halves = Vec::with_capacity(halves_len);
        for _ in 0..halves_len {
            halves.push([r.u32()?, r.u32()?]);
        }
        let letters = read_u32s(&mut r)?;
        let charts_len = r.len(68)?;
        let mut charts = Vec::with_capacity(charts_len);
        for _ in 0..charts_len {
            charts.push(r.chart()?);
        }
        let joins_len = r.len(68)?;
        let mut joins = Vec::with_capacity(joins_len);
        for _ in 0..joins_len {
            joins.push(r.chart()?);
        }
        let rebases = r.u64()?;
        let releases = r.u64()?;
        let passed = r.u64()?;
        if r.at != bytes.len() {
            return Err(StandingCodecError::Trailing);
        }
        let expected_roots = restored.nodes.arena.roots.len();
        let expected_joins = restored.nodes.joins.len();
        if roots.len() != expected_roots
            || depths.len() != ends.len()
            || depths.len() != halves.len()
            || charts.len() != depths.len()
            || joins.len() != expected_joins
            || passed > restored.law.declaration.population
        {
            return Err(StandingCodecError::Inconsistent);
        }
        let n = depths.len();
        if roots.iter().flatten().any(|&i| i as usize >= n)
            || children
                .iter()
                .any(|(&k, &v)| (k >> 32) as usize >= n || v as usize >= n)
        {
            return Err(StandingCodecError::Inconsistent);
        }
        if ends.iter().any(|&end| end as usize > letters.len())
            || depths.iter().any(|&word| {
                let branch = (word & BRANCH_BIT != 0) as usize;
                branch >= restored.law.branches.len()
                    || (word & !BRANCH_BIT) as usize > restored.law.branches[branch].depth
            })
        {
            return Err(StandingCodecError::Inconsistent);
        }
        if halves
            .iter()
            .any(|h| h[0] == 0 || h[1] == 0 || h[0] % 2 == 0 || h[1] % 2 == 0)
        {
            return Err(StandingCodecError::Inconsistent);
        }
        let max_face = u32::try_from(restored.law.widths.face)
            .ok()
            .and_then(|width| 1u64.checked_shl(width))
            .unwrap_or(u64::MAX);
        for c in charts.iter().chain(joins.iter()) {
            if c.beta.numerator == 0
                || c.beta.denominator == 0
                || c.beta.numerator % 2 == 0
                || c.beta.denominator % 2 == 0
                || c.stop > max_face
            {
                return Err(StandingCodecError::Inconsistent);
            }
        }
        let arena = &mut restored.nodes.arena;
        arena.roots = roots;
        arena.children = children;
        arena.depths = depths;
        arena.ends = ends;
        arena.halves = halves;
        arena.letters = letters;
        // Index the child relation once. Traversal below then examines each node and edge once,
        // even when the standing contains millions of stored landmarks.
        let mut edges = Vec::with_capacity(arena.children.len());
        for (&edge, &child) in &arena.children {
            let parent = (edge >> 32) as usize;
            let parent_branch = (arena.depths[parent] & BRANCH_BIT != 0) as usize;
            let edge_letter = edge as u32;
            let largest = if parent_branch == 0 {
                1 + restored.law.declaration.alphabet
            } else {
                1 + restored.law.declaration.alphabet
                    * restored.law.declaration.family.codes() as usize
            };
            if edge_letter as usize >= largest {
                return Err(StandingCodecError::Inconsistent);
            }
            edges.push((parent, edge_letter, child));
        }
        let mut offsets = vec![0usize; n + 1];
        for &(parent, _, _) in &edges {
            offsets[parent + 1] += 1;
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        let mut insertion = offsets[..n].to_vec();
        let mut adjacency = vec![(0u32, 0u32); edges.len()];
        for (parent, letter, child) in edges {
            let slot = insertion[parent];
            adjacency[slot] = (letter, child);
            insertion[parent] += 1;
        }
        restored.nodes.charts = charts;
        restored.nodes.joins = joins;
        restored.nodes.rebases = rebases;
        restored.nodes.releases = releases;
        restored.nodes.passed = passed;
        // Every root/child and its chart are used by the declared arena; reject disconnected or
        // cross-branch links that would otherwise make a malformed index appear plausible.
        let mut seen = vec![false; n];
        for (tree, root) in restored.nodes.arena.roots.iter().enumerate() {
            if let Some(root) = root {
                let branch = tree / restored.law.cells();
                let mut stack = vec![(*root, 0usize, tree)];
                while let Some((node, top, tree)) = stack.pop() {
                    if seen[node as usize] {
                        return Err(StandingCodecError::Inconsistent);
                    }
                    seen[node as usize] = true;
                    let index = node as usize;
                    let word = restored.nodes.arena.depths[index];
                    let node_branch = (word & BRANCH_BIT != 0) as usize;
                    let bottom = (word & !BRANCH_BIT) as usize;
                    let end = restored.nodes.arena.ends[index] as usize;
                    let run = bottom
                        .checked_sub(top)
                        .ok_or(StandingCodecError::Inconsistent)?;
                    if node_branch != branch || bottom < top || end < run {
                        return Err(StandingCodecError::Inconsistent);
                    }
                    let label = &restored.nodes.arena.letters[end - run..end];
                    let largest = if node_branch == 0 {
                        1 + restored.law.declaration.alphabet
                    } else {
                        1 + restored.law.declaration.alphabet
                            * restored.law.declaration.family.codes() as usize
                    };
                    if label.iter().any(|&letter| letter as usize >= largest) {
                        return Err(StandingCodecError::Inconsistent);
                    }
                    for &(_, child) in &adjacency[offsets[index]..offsets[index + 1]] {
                        let child_index = child as usize;
                        let child_word = restored.nodes.arena.depths[child_index];
                        let child_branch = (child_word & BRANCH_BIT != 0) as usize;
                        let child_bottom = (child_word & !BRANCH_BIT) as usize;
                        let child_end = restored.nodes.arena.ends[child_index] as usize;
                        let child_run = child_bottom.saturating_sub(bottom + 1);
                        if child_branch != branch
                            || child_bottom < bottom + 1
                            || child_end < child_run
                        {
                            return Err(StandingCodecError::Inconsistent);
                        }
                        stack.push((child, bottom + 1, tree));
                    }
                }
            }
        }
        if seen.iter().any(|seen| !seen) {
            return Err(StandingCodecError::Inconsistent);
        }
        Ok(restored)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn declaration() -> LandmarkDeclaration {
        LandmarkDeclaration {
            alphabet: 5,
            depth: 4,
            forced: 0,
            population: 64,
            grain: 16,
            family: LetterFamily::cells(),
            prior: StopPrior::half(),
            capacity: Capacity::Ceiling(4),
        }
    }

    #[test]
    fn standing_roundtrip_preserves_future_receive_and_canonical_bytes() {
        let stream = [0, 1, 4, 2, 0, 3, 1, 4];
        let mut original = Landmarks::new(declaration()).unwrap();
        for position in 0..6 {
            original
                .receive(&address(&stream, position, 4), stream[position])
                .unwrap();
        }
        let encoded = original.encode_standing();
        let mut restored = Landmarks::decode_standing(declaration(), &encoded).unwrap();
        assert_eq!(restored, original);
        let next = address(&stream, 6, 4);
        for class in 0..5 {
            assert_eq!(
                restored.probability(&next, class).unwrap(),
                original.probability(&next, class).unwrap()
            );
        }
        assert_eq!(
            restored.receive(&next, stream[6]).unwrap(),
            original.receive(&next, stream[6]).unwrap()
        );
        assert_eq!(restored.encode_standing(), original.encode_standing());
    }

    #[test]
    fn malformed_standings_refuse_without_accepting_partial_input() {
        let tree = Landmarks::new(declaration()).unwrap();
        let bytes = tree.encode_standing();
        assert!(Landmarks::decode_standing(declaration(), &bytes[..bytes.len() - 1]).is_err());
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert_eq!(
            Landmarks::decode_standing(declaration(), &trailing),
            Err(StandingCodecError::Trailing)
        );
        let mut wrong_declaration = declaration();
        wrong_declaration.depth += 1;
        assert_eq!(
            Landmarks::decode_standing(wrong_declaration, &bytes),
            Err(StandingCodecError::Declaration)
        );
    }

    #[test]
    fn multi_node_standing_roundtrips_and_invalid_edge_letters_refuse() {
        let mut declared = declaration();
        declared.depth = 8;
        declared.population = 2048;
        let stream: Vec<_> = (0..512)
            .map(|i| (i * 17 + i / 7) % declared.alphabet)
            .collect();
        let mut tree = Landmarks::new(declared.clone()).unwrap();
        for (position, &class) in stream.iter().enumerate() {
            tree.receive(&address(&stream, position, declared.depth), class)
                .unwrap();
        }
        assert!(tree.nodes() > 10);
        let bytes = tree.encode_standing();
        let restored = Landmarks::decode_standing(declared.clone(), &bytes).unwrap();
        assert_eq!(restored, tree);
        assert_eq!(restored.encode_standing(), bytes);

        let mut malformed = bytes;
        let mut reader = Reader {
            bytes: &malformed,
            at: MAGIC.len(),
        };
        let _ = reader.usize_value().unwrap();
        let _ = reader.usize_value().unwrap();
        let _ = reader.usize_value().unwrap();
        let _ = reader.u64().unwrap();
        let _ = reader.u64().unwrap();
        let slots = reader.len(8).unwrap();
        for _ in 0..slots {
            let _ = reader.u64().unwrap();
        }
        let rungs = reader.len(4).unwrap();
        for _ in 0..rungs {
            let _ = reader.u32().unwrap();
        }
        if reader.u8().unwrap() == 1 {
            let _ = reader.u32().unwrap();
        }
        let roots = reader.len(1).unwrap();
        for _ in 0..roots {
            if reader.u8().unwrap() == 1 {
                let _ = reader.u32().unwrap();
            }
        }
        let edges = reader.len(12).unwrap();
        assert!(edges > 0);
        let low_label = reader.at + 8;
        malformed[low_label..low_label + 4].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(Landmarks::decode_standing(declared, &malformed).is_err());
    }
}
