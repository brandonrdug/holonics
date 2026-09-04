//! One complete live-carrier authority for the generalized host membrane.
//!
//! The snapshot keeps the canonical header and exact generalized carrier together. Its native
//! schema is the only persistence mouth.

use body::manifold::{
    node_packed_word, packed_face_is_canonical, packed_node_is_canonical, unpack_node,
    CarrierGrowth, Enclosure, LiveBodyHeader, Node, CARRIER_HEADER_WORDS, ENCLOSURE_FLY,
    ENCLOSURE_FLY_LIVE, ENCLOSURE_STANCE, ENCLOSURE_WORDS, NODE_WORDS,
};
use body::register::REGISTER;

use crate::GrowingCarrier;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiveCarrierError {
    Invalid,
    Resource,
}

const NATIVE_MAGIC: u32 = 0x4552_4f53;
const NATIVE_VERSION: u32 = 1;
const NATIVE_MAGIC_WORD: usize = 0;
const NATIVE_VERSION_WORD: usize = 1;
const NATIVE_DEPTH_LO: usize = 2;
const NATIVE_DEPTH_HI: usize = 3;
const NATIVE_CARRIER_WORDS_LO: usize = 4;
const NATIVE_CARRIER_WORDS_HI: usize = 5;
const NATIVE_OVERFLOW_NODES_LO: usize = 6;
const NATIVE_OVERFLOW_NODES_HI: usize = 7;
const NATIVE_OFFSETS_LO: usize = 8;
const NATIVE_OFFSETS_HI: usize = 9;
const NATIVE_PREAMBLE_WORDS: usize = 10;

#[inline]
fn split_u64(value: u64) -> [u32; 2] {
    [value as u32, (value >> 32) as u32]
}

#[inline]
fn join_u64(words: &[u32], lo: usize, hi: usize) -> Option<u64> {
    Some(*words.get(lo)? as u64 | ((*words.get(hi)? as u64) << 32))
}

pub struct LiveCarrierSnapshot {
    header: LiveBodyHeader,
    carrier: GrowingCarrier,
}

impl LiveCarrierSnapshot {
    pub fn new(header: LiveBodyHeader, carrier: GrowingCarrier) -> Result<Self, LiveCarrierError> {
        if !carrier_is_structurally_live(&carrier) {
            return Err(LiveCarrierError::Invalid);
        }
        Ok(Self { header, carrier })
    }

    /// Close one native substrate return from its exact header, enclosure cores, and per-depth
    /// co-presence. Structural validation is identical to every other live snapshot mouth.
    pub fn from_substrate_parts(
        header: LiveBodyHeader,
        words: Vec<u32>,
        overflow: Vec<Vec<Node>>,
    ) -> Result<Self, LiveCarrierError> {
        let carrier =
            GrowingCarrier::from_parts(words, overflow).map_err(|_| LiveCarrierError::Resource)?;
        Self::new(header, carrier)
    }

    pub fn header(&self) -> LiveBodyHeader {
        self.header
    }

    pub fn carrier(&self) -> &GrowingCarrier {
        &self.carrier
    }

    pub fn carrier_mut(&mut self) -> &mut GrowingCarrier {
        &mut self.carrier
    }

    pub fn into_carrier(self) -> GrowingCarrier {
        self.carrier
    }

    /// Canonical native persistence face for the complete live carrier.  This is a typed row,
    /// never source light: it carries the first-person header, every native enclosure word, and
    /// every dynamic co-present node with exact per-depth offsets.  No text, file, modality, or
    /// semantic identity enters the format.
    pub fn encode_native_words(&self) -> Result<Vec<u32>, LiveCarrierError> {
        let depth = u64::try_from(self.carrier.depth()).map_err(|_| LiveCarrierError::Resource)?;
        let carrier_words =
            u64::try_from(self.carrier.words().len()).map_err(|_| LiveCarrierError::Resource)?;
        let offsets = depth.checked_add(1).ok_or(LiveCarrierError::Resource)?;
        let mut overflow_nodes = 0u64;
        for row in 0..self.carrier.depth() {
            overflow_nodes = overflow_nodes
                .checked_add(
                    u64::try_from(
                        self.carrier
                            .co_present_overflow(row)
                            .ok_or(LiveCarrierError::Invalid)?
                            .len(),
                    )
                    .map_err(|_| LiveCarrierError::Resource)?,
                )
                .ok_or(LiveCarrierError::Resource)?;
        }
        let total = NATIVE_PREAMBLE_WORDS
            .checked_add(CARRIER_HEADER_WORDS)
            .and_then(|value| value.checked_add(self.carrier.words().len()))
            .and_then(|value| {
                usize::try_from(offsets)
                    .ok()?
                    .checked_mul(2)
                    .and_then(|extent| value.checked_add(extent))
            })
            .and_then(|value| {
                usize::try_from(overflow_nodes)
                    .ok()?
                    .checked_mul(NODE_WORDS)
                    .and_then(|extent| value.checked_add(extent))
            })
            .ok_or(LiveCarrierError::Resource)?;
        let mut words = Vec::new();
        words
            .try_reserve_exact(total)
            .map_err(|_| LiveCarrierError::Resource)?;
        words.resize(total, 0);
        words[NATIVE_MAGIC_WORD] = NATIVE_MAGIC;
        words[NATIVE_VERSION_WORD] = NATIVE_VERSION;
        let depth_words = split_u64(depth);
        words[NATIVE_DEPTH_LO] = depth_words[0];
        words[NATIVE_DEPTH_HI] = depth_words[1];
        let carrier_extent = split_u64(carrier_words);
        words[NATIVE_CARRIER_WORDS_LO] = carrier_extent[0];
        words[NATIVE_CARRIER_WORDS_HI] = carrier_extent[1];
        let node_extent = split_u64(overflow_nodes);
        words[NATIVE_OVERFLOW_NODES_LO] = node_extent[0];
        words[NATIVE_OVERFLOW_NODES_HI] = node_extent[1];
        let offset_extent = split_u64(offsets);
        words[NATIVE_OFFSETS_LO] = offset_extent[0];
        words[NATIVE_OFFSETS_HI] = offset_extent[1];

        let header_at = NATIVE_PREAMBLE_WORDS;
        words[header_at..header_at + CARRIER_HEADER_WORDS].copy_from_slice(self.header.words());
        let carrier_at = header_at + CARRIER_HEADER_WORDS;
        words[carrier_at..carrier_at + self.carrier.words().len()]
            .copy_from_slice(self.carrier.words());
        let offsets_at = carrier_at + self.carrier.words().len();
        let nodes_at =
            offsets_at + usize::try_from(offsets).map_err(|_| LiveCarrierError::Resource)? * 2;
        let mut node_cursor = 0u64;
        for row in 0..self.carrier.depth() {
            let encoded = split_u64(node_cursor);
            words[offsets_at + row * 2] = encoded[0];
            words[offsets_at + row * 2 + 1] = encoded[1];
            let overflow = self
                .carrier
                .co_present_overflow(row)
                .ok_or(LiveCarrierError::Invalid)?;
            for node in overflow {
                let node_index =
                    usize::try_from(node_cursor).map_err(|_| LiveCarrierError::Resource)?;
                let at = nodes_at
                    .checked_add(
                        node_index
                            .checked_mul(NODE_WORDS)
                            .ok_or(LiveCarrierError::Resource)?,
                    )
                    .ok_or(LiveCarrierError::Resource)?;
                for word in 0..NODE_WORDS {
                    words[at + word] = node_packed_word(*node, word);
                }
                node_cursor = node_cursor
                    .checked_add(1)
                    .ok_or(LiveCarrierError::Resource)?;
            }
        }
        let terminal = split_u64(node_cursor);
        let terminal_at = offsets_at + self.carrier.depth() * 2;
        words[terminal_at] = terminal[0];
        words[terminal_at + 1] = terminal[1];
        debug_assert_eq!(node_cursor, overflow_nodes);
        Ok(words)
    }

    /// Reopen one complete native snapshot. Every extent and canonical row closes before the
    /// returned construction exists; truncation, reordering, omitted overflow, or a noncanonical
    /// node refuses rather than becoming empty terrain.
    pub fn from_native_words(words: &[u32]) -> Result<Self, LiveCarrierError> {
        if words.get(NATIVE_MAGIC_WORD) != Some(&NATIVE_MAGIC)
            || words.get(NATIVE_VERSION_WORD) != Some(&NATIVE_VERSION)
        {
            return Err(LiveCarrierError::Invalid);
        }
        let depth = join_u64(words, NATIVE_DEPTH_LO, NATIVE_DEPTH_HI)
            .and_then(|value| usize::try_from(value).ok())
            .filter(|value| *value != 0)
            .ok_or(LiveCarrierError::Invalid)?;
        let carrier_words = join_u64(words, NATIVE_CARRIER_WORDS_LO, NATIVE_CARRIER_WORDS_HI)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or(LiveCarrierError::Invalid)?;
        let expected_carrier_words = depth
            .checked_mul(ENCLOSURE_WORDS)
            .ok_or(LiveCarrierError::Resource)?;
        if carrier_words != expected_carrier_words {
            return Err(LiveCarrierError::Invalid);
        }
        let overflow_nodes = join_u64(words, NATIVE_OVERFLOW_NODES_LO, NATIVE_OVERFLOW_NODES_HI)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or(LiveCarrierError::Invalid)?;
        let offsets = join_u64(words, NATIVE_OFFSETS_LO, NATIVE_OFFSETS_HI)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or(LiveCarrierError::Invalid)?;
        if offsets != depth.checked_add(1).ok_or(LiveCarrierError::Resource)? {
            return Err(LiveCarrierError::Invalid);
        }
        let header_at = NATIVE_PREAMBLE_WORDS;
        let carrier_at = header_at
            .checked_add(CARRIER_HEADER_WORDS)
            .ok_or(LiveCarrierError::Resource)?;
        let offsets_at = carrier_at
            .checked_add(carrier_words)
            .ok_or(LiveCarrierError::Resource)?;
        let nodes_at = offsets_at
            .checked_add(offsets.checked_mul(2).ok_or(LiveCarrierError::Resource)?)
            .ok_or(LiveCarrierError::Resource)?;
        let expected = nodes_at
            .checked_add(
                overflow_nodes
                    .checked_mul(NODE_WORDS)
                    .ok_or(LiveCarrierError::Resource)?,
            )
            .ok_or(LiveCarrierError::Resource)?;
        if words.len() != expected {
            return Err(LiveCarrierError::Invalid);
        }
        let header = LiveBodyHeader::from_words_checked(
            words
                .get(header_at..carrier_at)
                .ok_or(LiveCarrierError::Invalid)?,
        )
        .ok_or(LiveCarrierError::Invalid)?;
        let mut carrier_core = Vec::new();
        carrier_core
            .try_reserve_exact(carrier_words)
            .map_err(|_| LiveCarrierError::Resource)?;
        carrier_core.extend_from_slice(
            words
                .get(carrier_at..offsets_at)
                .ok_or(LiveCarrierError::Invalid)?,
        );

        let mut row_offsets = Vec::new();
        row_offsets
            .try_reserve_exact(offsets)
            .map_err(|_| LiveCarrierError::Resource)?;
        for at in 0..offsets {
            let lo = offsets_at + at * 2;
            let value = join_u64(words, lo, lo + 1)
                .and_then(|value| usize::try_from(value).ok())
                .ok_or(LiveCarrierError::Invalid)?;
            if value > overflow_nodes
                || row_offsets.last().is_some_and(|previous| *previous > value)
            {
                return Err(LiveCarrierError::Invalid);
            }
            row_offsets.push(value);
        }
        if row_offsets.first() != Some(&0) || row_offsets.last() != Some(&overflow_nodes) {
            return Err(LiveCarrierError::Invalid);
        }

        let mut overflow = Vec::new();
        overflow
            .try_reserve_exact(depth)
            .map_err(|_| LiveCarrierError::Resource)?;
        for row in 0..depth {
            let first = row_offsets[row];
            let after = row_offsets[row + 1];
            let mut nodes = Vec::new();
            nodes
                .try_reserve_exact(after - first)
                .map_err(|_| LiveCarrierError::Resource)?;
            for ordinal in first..after {
                let at = nodes_at
                    .checked_add(
                        ordinal
                            .checked_mul(NODE_WORDS)
                            .ok_or(LiveCarrierError::Resource)?,
                    )
                    .ok_or(LiveCarrierError::Resource)?;
                if !packed_node_is_canonical(words, at) {
                    return Err(LiveCarrierError::Invalid);
                }
                let node = unpack_node(words, at);
                if node.len == 0 {
                    return Err(LiveCarrierError::Invalid);
                }
                nodes.push(node);
            }
            overflow.push(nodes);
        }
        let carrier = GrowingCarrier::from_parts(carrier_core, overflow)
            .map_err(|_| LiveCarrierError::Invalid)?;
        Self::new(header, carrier)
    }
}

fn node_is_live(node: Node) -> bool {
    if node.len == 0 {
        return false;
    }
    let mut words = [0u32; NODE_WORDS];
    for (word, slot) in words.iter_mut().enumerate() {
        *slot = node_packed_word(node, word);
    }
    packed_node_is_canonical(&words, 0)
}

fn carrier_is_structurally_live(carrier: &GrowingCarrier) -> bool {
    if carrier.depth() == 0 || carrier.words().len() % ENCLOSURE_WORDS != 0 {
        return false;
    }
    for depth in 0..carrier.depth() {
        let base = depth * ENCLOSURE_WORDS;
        for slot in 0..REGISTER as usize {
            let at = base + slot * NODE_WORDS;
            if !packed_node_is_canonical(carrier.words(), at) {
                return false;
            }
        }
        if !packed_node_is_canonical(carrier.words(), base + ENCLOSURE_STANCE)
            || !packed_face_is_canonical(carrier.words(), base + ENCLOSURE_FLY)
            || carrier.words()[base + ENCLOSURE_FLY_LIVE] > 1
        {
            return false;
        }
        let enclosure = Enclosure::unpack_at(carrier.words(), base);
        if enclosure.live > REGISTER as usize
            || enclosure.head >= REGISTER as usize
            || (enclosure.live < REGISTER as usize && enclosure.head != enclosure.live)
        {
            return false;
        }
        for slot in 0..REGISTER as usize {
            let active = enclosure.live == REGISTER as usize || slot < enclosure.live;
            let at = base + slot * NODE_WORDS;
            let raw_zero = carrier.words()[at..at + NODE_WORDS]
                .iter()
                .all(|word| *word == 0);
            if (active && !node_is_live(enclosure.register[slot])) || (!active && !raw_zero) {
                return false;
            }
        }
        let stance_zero = carrier.words()[base + ENCLOSURE_STANCE..base + ENCLOSURE_FLY]
            .iter()
            .all(|word| *word == 0);
        if (enclosure.stance.len == 0 && !stance_zero)
            || (enclosure.fly_live && (enclosure.stance.len == 0 || !enclosure.fly.rotor_formed()))
            || (!enclosure.fly_live
                && carrier.words()[base + ENCLOSURE_FLY..base + ENCLOSURE_FLY_LIVE]
                    .iter()
                    .any(|word| *word != 0))
        {
            return false;
        }
        for word in 0..ENCLOSURE_WORDS {
            if enclosure.packed_word(word) != carrier.words()[base + word] {
                return false;
            }
        }
        let overflow = carrier.co_present_overflow(depth).unwrap_or(&[]);
        if !overflow.is_empty() && enclosure.live != REGISTER as usize {
            return false;
        }
        if overflow.iter().copied().any(|node| !node_is_live(node)) {
            return false;
        }
    }
    true
}

impl From<CarrierGrowth> for LiveCarrierError {
    fn from(_: CarrierGrowth) -> Self {
        Self::Resource
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::manifold::{atom_node, ErosBody};
    use body::num::Cog;

    #[test]
    fn native_snapshot_reopens_and_branches_without_changing_its_predecessor() {
        let standing = crate::SparseStandingSurface::empty(64).unwrap();
        // Repeated exact co-presence remains plural and live; no completed lower constituent is
        // retained merely to force this native-only carrier posture.
        let arrivals = vec![atom_node(Cog::lit(3)); 20];
        let mut own = crate::GrowingSparseOwn::new();
        let mut carrier = GrowingCarrier::with_depth(1).unwrap();
        let header;
        {
            let mut body = ErosBody::over_standing_world_storage_from_first_difference(
                &standing,
                &mut own,
                arrivals[0].place,
                &mut carrier,
            )
            .unwrap();
            for node in arrivals {
                body.perceive_node(node, 0);
            }
            header = body.live_header(20);
        }
        let live = LiveCarrierSnapshot::new(header, carrier).unwrap();

        let encoded = live.encode_native_words().unwrap();
        let reopened = LiveCarrierSnapshot::from_native_words(&encoded).unwrap();
        assert_eq!(reopened.header(), live.header());
        assert_eq!(reopened.carrier(), live.carrier());

        let continue_once = |snapshot: &LiveCarrierSnapshot| {
            let mut carrier = snapshot.carrier().branch_shared();
            let mut own = crate::GrowingSparseOwn::new();
            let (header, own_cells);
            {
                let mut body = ErosBody::resume_standing_world_storage_from_live_header(
                    &standing,
                    &mut own,
                    snapshot.header(),
                    &mut carrier,
                )
                .unwrap();
                body.perceive_node(atom_node(Cog::lit(89).turned(1)), 0);
                header = body.live_header(21);
                own_cells = body.sparse_own_cells().unwrap().to_vec();
            }
            (header, carrier, own_cells)
        };
        assert_eq!(continue_once(&live), continue_once(&reopened));
        assert_eq!(live.header(), header);

        let mut truncated = encoded.clone();
        truncated.pop();
        assert!(LiveCarrierSnapshot::from_native_words(&truncated).is_err());
        let mut superseded = encoded;
        superseded[NATIVE_VERSION_WORD] = 0;
        assert!(matches!(
            LiveCarrierSnapshot::from_native_words(&superseded),
            Err(LiveCarrierError::Invalid)
        ));
        superseded[NATIVE_VERSION_WORD] = NATIVE_VERSION;
        let final_node = superseded.len() - NODE_WORDS;
        superseded[final_node + 4] = 4;
        assert!(LiveCarrierSnapshot::from_native_words(&superseded).is_err());
    }
}
