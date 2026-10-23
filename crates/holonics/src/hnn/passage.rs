//! **The passage tree: the receiving tree's counts at a second spectral placement** (#405).
//!
//! [definition; agent-inferred, October 23, from §5 of the mathematics thread's record
//! `2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ`
//! (PR #412)] Once the receiving tree
//! conditions on its context `C_t` exactly, anything else can add at most `I(u_t ; far past | C_t)`.
//! A mode driven by the symbol alone splits as `z_t = N_t + λ^D z_(t−D)` with `N_t` a function of
//! `C_t`, so a bank of modes whose memory sits inside the tree's horizon adds nothing (measured on
//! GSM8K: 0.614 against the tree's 0.613 bits a cell at depth 16). What the far past says given the
//! context is mostly the passage's own statistics: its names, numbers and units recur. That is a
//! function of (context, next class), so it lives at the tree's own nodes: a KT count `n(c, a)` is
//! the `λ = 1` mode of the indicator `[context = c, next = a]`, and the passage term is the same
//! indicator's mode at `γ = 1 − 2^(−m)`, a decayed count at every node.
//!
//! ```text
//! count       l(c, a) ← γ^(Δt) l(c, a) + [actual = a]        Δt cells since the node was last met
//! face        p_(−1) = the base face,   p_d(a) = (l_d(a) + β p_(d−1)(a)) / (L_d + β),   d = 0..=D
//!             the base is the receiving tree's own face at the cell, so the passage reads its news
//!             over what the tree already predicts
//! evidence    the deepest depth whose decayed total holds at least one occurrence
//! ```
//!
//! The decay is a dyadic release with its residue carried (`CarriedRelease.residueRun_conserves`,
//! PR #412): a count is a numerator on `2^(−COUNT_BITS)` occurrences plus a residue below it on
//! `2^(−(COUNT_BITS + 62))`, and each lazy decay multiplies both by the navigator's face of `γ^(Δt)`
//! at `2^(−62)` (the product of its resident squarings `γ^(2^i)` that `Δt`'s binary digits select).
//! A plain floor would silence every count below `2^m` (`plainTransported_silences`). A node whose
//! counts have all released below one numerator is released at that declared grain: its residue,
//! under `2^(−COUNT_BITS)` of an occurrence, dissolves with it.
//!
//! No routine looks up an earlier occurrence. The counts are the receiver's own at a second
//! placement, and copying is what they read when the passage repeats itself.
//!
//! **The node lock** ([definition; agent-inferred, October 23], §8 of the mathematics thread's
//! record, PR #412): each node also keeps the class that followed its last visit, the indicator's
//! `λ = 0` placement beside the `λ = 1` count and the `γ` count. A located equality is the pair
//! contact `(t, t − δ)` with slip `[u_t ≠ u_(t−δ)]`; a run of `ℓ` held contacts is `ℓ` closed
//! squares, so the offset `δ` is located by loop closure. The deepest node on the path with an
//! earlier visit locates it (`δ = t − last`), and its kept class `ĉ = u_(t−δ)` is the lock's
//! prediction, read without a strand of the passage. Holding `δ` past the tree's depth would read
//! a cell `δ` back that no node keeps: a strand, which retention refuses.
//!
//! ```text
//! lock        ĉ = next(deepest node with an earlier visit),  d its depth
//! deposit     next(node) ← actual, at every node on the path
//! ```
//!
//! The tree reads classes
//! of a declared alphabet and a frame phase; a text, image, acoustic or motor boundary chart
//! supplies both.
use std::collections::HashMap;

/// A face's grain, `2^(−62)`.
const UNIT_BITS: u32 = 62;
/// One occurrence is `2^16` count numerators (agent-inferred): sixteen bits below an occurrence
/// before a count's residue takes over.
const COUNT_BITS: u32 = 16;

/// [definition; agent-inferred] **The passage tree's declared law**: an alphabet of `A` classes (a
/// power of two), `phases` frame phases, contexts of up to `depth` cells, the horizon `m`
/// (`γ = 1 − 2^(−m)`) and the backoff `β` in occurrences.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PassageDeclaration {
    pub alphabet: usize,
    pub phases: usize,
    pub depth: usize,
    pub horizon: u32,
    pub backoff: u64,
}

/// Refusals of the passage tree's law.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum PassageError {
    #[error("passage tree refused: {0}")]
    Refused(&'static str),
}

/// One node's decayed counts (numerators on `2^(−COUNT_BITS)`), their carried residues (on
/// `2^(−(COUNT_BITS + 62))`), the cell at which they were last brought to the present and the
/// class that followed its last visit (the lock).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Node {
    counts: Vec<u64>,
    residues: Vec<u64>,
    last: u64,
    next: usize,
}

/// [definition; agent-inferred] **The passage tree**: its declaration, the decay navigator's
/// resident face `γ^(2^i)` on `2^(−62)`, and its live nodes keyed by (depth, phase, context).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageTree {
    pub declaration: PassageDeclaration,
    powers: Vec<u128>,
    nodes: HashMap<u128, Node>,
}

/// [definition; agent-inferred] **The passage's face at one cell**: each class's probability on
/// `2^(−62)`, the evidence depth (`0`: no node holds an occurrence; `d + 1`: depth `d` is the
/// deepest that does) and the lock: the class that followed the deepest visited node's last visit,
/// with that node's depth (`None` before any node is visited).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageFace {
    pub probabilities: Vec<u128>,
    pub evidence: usize,
    pub lock: Option<(usize, usize)>,
}

impl PassageTree {
    pub fn new(declaration: PassageDeclaration) -> Result<Self, PassageError> {
        let PassageDeclaration { alphabet, phases, depth, horizon, backoff } = declaration;
        if alphabet < 2 || !alphabet.is_power_of_two() {
            return Err(PassageError::Refused("an alphabet that is a power of two, at least two"));
        }
        let cell_bits = alphabet.trailing_zeros() as usize;
        let phase_bits = (usize::BITS - phases.saturating_sub(1).leading_zeros()) as usize;
        if phases == 0 || depth * cell_bits + phase_bits + 8 > 128 || depth > 255 {
            return Err(PassageError::Refused("a node key of depth, phase and context inside 128 bits"));
        }
        if horizon == 0 || horizon >= UNIT_BITS || backoff == 0 {
            return Err(PassageError::Refused("a horizon inside the face's grain and a positive backoff"));
        }
        // A decayed total stays below 2^(COUNT_BITS + m + 1) numerators: the u64 count fits.
        if COUNT_BITS + horizon + 1 > 63 {
            return Err(PassageError::Refused("a horizon whose decayed counts fit 64 bits"));
        }
        let one = 1u128 << UNIT_BITS;
        let mut powers = vec![one - (one >> horizon)];
        for _ in 1..64 {
            let last = *powers.last().expect("one power");
            powers.push((last * last) >> UNIT_BITS);
        }
        Ok(Self { declaration, powers, nodes: HashMap::new() })
    }

    /// The live nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// `γ^(Δt)` on `2^(−62)`.
    fn decay(&self, elapsed: u64) -> u128 {
        let mut value = 1u128 << UNIT_BITS;
        for (i, power) in self.powers.iter().enumerate() {
            if elapsed >> i == 0 {
                break;
            }
            if elapsed & (1 << i) != 0 {
                value = (value * power) >> UNIT_BITS;
            }
        }
        value
    }

    /// A count and its residue carried through `γ^(Δt)`: `x = n g + (r g ≫ 62)` on
    /// `2^(−(COUNT_BITS + 62))`, the new count its whole part and the new residue the rest.
    fn decayed(count: u64, residue: u64, g: u128) -> (u64, u64) {
        let x = count as u128 * g + ((residue as u128 * g) >> UNIT_BITS);
        ((x >> UNIT_BITS) as u64, (x & ((1u128 << UNIT_BITS) - 1)) as u64)
    }

    /// The node key at `depth` behind `context` (newest first) in `phase`.
    fn key(&self, depth: usize, phase: usize, context: &[usize]) -> u128 {
        let cell_bits = self.declaration.alphabet.trailing_zeros();
        let mut key = 0u128;
        for &class in &context[..depth] {
            key = (key << cell_bits) | class as u128;
        }
        let phase_bits = usize::BITS - self.declaration.phases.saturating_sub(1).leading_zeros();
        (((key << phase_bits) | phase as u128) << 8) | depth as u128
    }

    /// **The passage's face** at cell `now` in `phase`, behind `context` (the preceding cells,
    /// newest first; fewer than the depth before the passage reaches it).
    pub fn face(&self, phase: usize, context: &[usize], now: u64, base: &[u128]) -> Result<PassageFace, PassageError> {
        let PassageDeclaration { alphabet, phases, depth, backoff, .. } = self.declaration;
        if phase >= phases || context.iter().any(|&c| c >= alphabet) || base.len() != alphabet {
            return Err(PassageError::Refused("a phase, context and base face inside the declaration"));
        }
        let beta = (backoff as u128) << COUNT_BITS;
        let mut p: Vec<u128> = base.to_vec();
        let mut evidence = 0;
        let mut lock = None;
        for d in 0..=depth.min(context.len()) {
            let Some(node) = self.nodes.get(&self.key(d, phase, context)) else {
                continue;
            };
            lock = Some((node.next, d));
            let g = self.decay(now - node.last);
            let counts: Vec<u128> = node
                .counts
                .iter()
                .zip(&node.residues)
                .map(|(&n, &r)| Self::decayed(n, r, g).0 as u128)
                .collect();
            let total: u128 = counts.iter().sum();
            if total >= 1 << COUNT_BITS {
                evidence = d + 1;
            }
            // p_d(a) = (l(a) 2^62 + β p_(d−1)(a)) / (L + β), on 2^(−62).
            p = counts.iter().zip(&p).map(|(&l, &q)| ((l << UNIT_BITS) + beta * q) / (total + beta)).collect();
        }
        Ok(PassageFace { probabilities: p, evidence, lock })
    }

    /// **Deposit the actual class** at cell `now`: every node on the context's path is brought to
    /// the present and counts one occurrence of `actual`.
    pub fn deposit(&mut self, phase: usize, context: &[usize], actual: usize, now: u64) -> Result<(), PassageError> {
        let PassageDeclaration { alphabet, phases, depth, .. } = self.declaration;
        if phase >= phases || actual >= alphabet || context.iter().any(|&c| c >= alphabet) {
            return Err(PassageError::Refused("a phase, context and class inside the declaration"));
        }
        for d in 0..=depth.min(context.len()) {
            let key = self.key(d, phase, context);
            let g = self.nodes.get(&key).map(|node| self.decay(now - node.last));
            let node = self.nodes.entry(key).or_insert_with(|| Node {
                counts: vec![0; alphabet],
                residues: vec![0; alphabet],
                last: now,
                next: actual,
            });
            if let Some(g) = g {
                for (n, r) in node.counts.iter_mut().zip(node.residues.iter_mut()) {
                    (*n, *r) = Self::decayed(*n, *r, g);
                }
            }
            node.last = now;
            node.next = actual;
            node.counts[actual] += 1 << COUNT_BITS;
        }
        Ok(())
    }

    /// **Release the dissolved nodes** at cell `now`: every node brought to the present, and a node
    /// whose counts have all released below one numerator removed.
    pub fn release(&mut self, now: u64) {
        let powers = &self.powers;
        let decay = |elapsed: u64| {
            let mut value = 1u128 << UNIT_BITS;
            for (i, power) in powers.iter().enumerate() {
                if elapsed >> i == 0 {
                    break;
                }
                if elapsed & (1 << i) != 0 {
                    value = (value * power) >> UNIT_BITS;
                }
            }
            value
        };
        self.nodes.retain(|_, node| {
            let g = decay(now - node.last);
            for (n, r) in node.counts.iter_mut().zip(node.residues.iter_mut()) {
                (*n, *r) = Self::decayed(*n, *r, g);
            }
            node.last = now;
            // Released at the count's grain: a node whose counts are all below one numerator is
            // gone, its residue (under 2^(−COUNT_BITS) of an occurrence) dissolved with it.
            node.counts.iter().any(|&v| v != 0)
        });
    }

    /// **The passage tree at rest, as text**: the declaration line, then one line per live node
    /// (key, last, next, counts, residues), in key order.
    pub fn to_text(&self) -> String {
        let d = self.declaration;
        let mut out = format!("passage-tree-v2\n{} {} {} {} {} {}\n", d.alphabet, d.phases, d.depth, d.horizon, d.backoff, self.nodes.len());
        let mut keys: Vec<&u128> = self.nodes.keys().collect();
        keys.sort_unstable();
        for key in keys {
            let node = &self.nodes[key];
            let words: Vec<String> = [key.to_string(), node.last.to_string(), node.next.to_string()]
                .into_iter()
                .chain(node.counts.iter().chain(&node.residues).map(|v| v.to_string()))
                .collect();
            out.push_str(&words.join(" "));
            out.push('\n');
        }
        out
    }

    /// The passage tree restored from [`PassageTree::to_text`], and the lines it read.
    pub fn from_lines<'a>(lines: &mut impl Iterator<Item = &'a str>) -> Result<Self, PassageError> {
        if lines.next() != Some("passage-tree-v2") {
            return Err(PassageError::Refused("a passage tree's text"));
        }
        let head: Vec<u64> = lines
            .next()
            .ok_or(PassageError::Refused("a passage tree's declaration"))?
            .split_whitespace()
            .map(str::parse)
            .collect::<Result<_, _>>()
            .map_err(|_| PassageError::Refused("a passage tree's declaration"))?;
        let [alphabet, phases, depth, horizon, backoff, count] = head[..] else {
            return Err(PassageError::Refused("a passage tree's declaration width"));
        };
        let horizon = u32::try_from(horizon).map_err(|_| PassageError::Refused("a declared horizon"))?;
        let mut tree = Self::new(PassageDeclaration {
            alphabet: alphabet as usize,
            phases: phases as usize,
            depth: depth as usize,
            horizon,
            backoff,
        })?;
        let a = alphabet as usize;
        for _ in 0..count {
            let mut fields = lines.next().ok_or(PassageError::Refused("a passage tree's node"))?.split_whitespace();
            let key: u128 = fields
                .next()
                .and_then(|k| k.parse().ok())
                .ok_or(PassageError::Refused("a passage tree node's key"))?;
            let words: Vec<u64> = fields
                .map(str::parse)
                .collect::<Result<_, _>>()
                .map_err(|_| PassageError::Refused("a passage tree's node"))?;
            if words.len() != 2 + 2 * a || words[1] >= alphabet {
                return Err(PassageError::Refused("a passage tree node's width and lock"));
            }
            tree.nodes.insert(
                key,
                Node {
                    last: words[0],
                    next: words[1] as usize,
                    counts: words[2..2 + a].to_vec(),
                    residues: words[2 + a..].to_vec(),
                },
            );
        }
        Ok(tree)
    }
}

/// [definition; agent-inferred] **`log₂ p` on `2^(−X)`** for `p` on `2^(−62)`, `0 < p ≤ 2^62`: the
/// whole part from the numerator's width, then `X` binary digits of the mantissa's logarithm, each
/// read by squaring the mantissa (released at `2^(−62)`) and halving it when it passes two.
pub fn log2_face(p: u128, digits: u32) -> i128 {
    debug_assert!(p > 0 && p <= 1u128 << UNIT_BITS);
    let width = 128 - p.leading_zeros(); // p in [2^(width−1), 2^width)
    let whole = width as i128 - 1 - UNIT_BITS as i128; // ≤ 0
    let mut mantissa = p << (UNIT_BITS + 1 - width); // in [2^62, 2^63)
    let mut fraction = 0i128;
    for _ in 0..digits {
        mantissa = (mantissa * mantissa) >> UNIT_BITS;
        fraction <<= 1;
        if mantissa >= 2u128 << UNIT_BITS {
            fraction |= 1;
            mantissa >>= 1;
        }
    }
    (whole << digits) + fraction
}

#[cfg(test)]
mod tests {
    use super::*;

    fn declared() -> PassageDeclaration {
        PassageDeclaration { alphabet: 4, phases: 4, depth: 3, horizon: 4, backoff: 1 }
    }

    #[test]
    fn log2_face_reads_dyadic_and_halves() {
        let one = 1u128 << 62;
        assert_eq!(log2_face(one, 24), 0);
        assert_eq!(log2_face(one >> 3, 24), -3 << 24);
        // log₂(3/4) = −0.415037499…: within one digit.
        let x = log2_face(3 * (one >> 2), 24);
        let exact = -6_963_174i128; // floor(−0.415037499… · 2^24)
        assert!((x - exact).abs() <= 1, "{x}");
    }

    #[test]
    fn a_repeated_context_reads_its_own_continuation() {
        let mut tree = PassageTree::new(declared()).unwrap();
        let context = [1usize, 2, 3];
        for t in 0..6 {
            tree.deposit(0, &context, 2, t).unwrap();
        }
        let face = tree.face(0, &context, 6, &[1u128 << 60; 4]).unwrap();
        assert_eq!(face.evidence, 4);
        let top = (0..4).max_by_key(|&a| face.probabilities[a]).unwrap();
        assert_eq!(top, 2);
        // Another phase has no evidence and reads the uniform face.
        let other = tree.face(1, &context, 6, &[1u128 << 60; 4]).unwrap();
        assert_eq!(other.evidence, 0);
        assert_eq!(other.probabilities, vec![1u128 << 60; 4]);
    }

    #[test]
    fn decay_carries_its_residue_and_dissolves() {
        let mut tree = PassageTree::new(declared()).unwrap();
        tree.deposit(0, &[], 1, 0).unwrap();
        // γ^16 = (15/16)^16 = 0.356…: below one occurrence, evidence leaves depth 0.
        let face = tree.face(0, &[], 16, &[1u128 << 60; 4]).unwrap();
        assert_eq!(face.evidence, 0);
        assert!(face.probabilities[1] > face.probabilities[0]);
        // Far past the horizon every count has released below its grain: the node is gone.
        tree.release(1 << 12);
        assert!(tree.is_empty());
    }

    #[test]
    fn lazy_decay_is_the_stepped_decay() {
        // Bringing a node to the present in one move or in many reads the same count within the
        // residue's own released remainder.
        let declaration = declared();
        let mut one = PassageTree::new(declaration).unwrap();
        let mut many = PassageTree::new(declaration).unwrap();
        one.deposit(0, &[], 3, 0).unwrap();
        many.deposit(0, &[], 3, 0).unwrap();
        for t in 1..=10 {
            many.release(t);
        }
        one.release(10);
        let (a, b) = (&one.nodes.values().next().unwrap().counts[3], &many.nodes.values().next().unwrap().counts[3]);
        assert!(a.abs_diff(*b) <= 1, "{a} {b}");
    }

    #[test]
    fn a_deep_context_keeps_its_far_cells() {
        // Four classes at depth 48 key 96 context bits: past one word, inside the 128-bit key.
        let declaration = PassageDeclaration { depth: 48, ..declared() };
        let mut tree = PassageTree::new(declaration).unwrap();
        let near = [1usize; 48];
        let mut far = near;
        far[40] = 2;
        for t in 0..4 {
            tree.deposit(0, &near, 3, t).unwrap();
        }
        assert_eq!(tree.face(0, &near, 4, &[1u128 << 60; 4]).unwrap().evidence, 49);
        // The context that differs only 41 cells back meets its common suffix, not the deep node.
        assert_eq!(tree.face(0, &far, 4, &[1u128 << 60; 4]).unwrap().evidence, 41);
        let text = tree.to_text();
        assert_eq!(PassageTree::from_lines(&mut text.lines()).unwrap(), tree);
        assert!(PassageTree::new(PassageDeclaration { depth: 60, ..declared() }).is_err());
    }

    #[test]
    fn the_lock_is_the_deepest_visit_s_continuation() {
        let mut tree = PassageTree::new(declared()).unwrap();
        assert_eq!(tree.face(0, &[1, 2, 3], 0, &[1u128 << 60; 4]).unwrap().lock, None);
        // [1, 2, 3] was followed by 0; the shallower [1, 2] last by 3.
        tree.deposit(0, &[1, 2, 3], 0, 0).unwrap();
        tree.deposit(0, &[1, 2, 0], 3, 1).unwrap();
        assert_eq!(tree.face(0, &[1, 2, 3], 2, &[1u128 << 60; 4]).unwrap().lock, Some((0, 3)));
        assert_eq!(tree.face(0, &[1, 2, 2], 2, &[1u128 << 60; 4]).unwrap().lock, Some((3, 2)));
        assert_eq!(tree.face(1, &[1, 2, 3], 2, &[1u128 << 60; 4]).unwrap().lock, None);
    }

    #[test]
    fn text_restores_exactly() {
        let mut tree = PassageTree::new(declared()).unwrap();
        for (t, &c) in [0usize, 1, 2, 3, 1, 2, 2].iter().enumerate() {
            tree.deposit(t % 4, &[c, 1], c, t as u64).unwrap();
        }
        let text = tree.to_text();
        let restored = PassageTree::from_lines(&mut text.lines()).unwrap();
        assert_eq!(restored, tree);
    }
}
