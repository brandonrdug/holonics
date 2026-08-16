//! Fallible cpu carrier which re-bases only when an actual completion reaches a new depth.
//!
//! The words remain the body's native enclosure rows.  `Vec` capacity and allocation are substrate
//! concerns behind the membrane; a failed growth request refuses the disposable passage and never
//! becomes darkness, a deed, or an authored depth ceiling.

use std::sync::Arc;

use body::manifold::{CarrierGrowth, CarrierStorage, Node, ENCLOSURE_WORDS};

#[derive(Debug, Default, PartialEq, Eq)]
pub struct GrowingCarrier {
    words: Arc<Vec<u32>>,
    /// Exact live co-presence beyond each enclosure core. Branches share immutable rows and copy
    /// only a row which an actual later current changes.
    overflow: Arc<Vec<Arc<Vec<Node>>>>,
}

impl GrowingCarrier {
    /// Found an explicit plural branch over the same immutable carrier standing. Mutation uses
    /// path copying inside [`CarrierStorage`]; no complete live carrier is duplicated here.
    pub(crate) fn branch_shared(&self) -> Self {
        Self {
            words: Arc::clone(&self.words),
            overflow: Arc::clone(&self.overflow),
        }
    }

    pub fn with_depth(depth: usize) -> Result<Self, CarrierGrowth> {
        let extent = depth
            .checked_mul(ENCLOSURE_WORDS)
            .ok_or(CarrierGrowth::Refused)?;
        let mut words = Vec::new();
        words
            .try_reserve_exact(extent)
            .map_err(|_| CarrierGrowth::Refused)?;
        words.resize(extent, 0);
        let mut overflow = Vec::new();
        overflow
            .try_reserve_exact(depth)
            .map_err(|_| CarrierGrowth::Refused)?;
        overflow.resize_with(depth, || Arc::new(Vec::new()));
        Ok(Self {
            words: Arc::new(words),
            overflow: Arc::new(overflow),
        })
    }

    /// Remount exact native enclosure rows.
    pub fn from_words(words: Vec<u32>) -> Result<Self, CarrierGrowth> {
        if words.is_empty() || words.len() % ENCLOSURE_WORDS != 0 {
            return Err(CarrierGrowth::Refused);
        }
        let depth = words.len() / ENCLOSURE_WORDS;
        let mut overflow = Vec::new();
        overflow
            .try_reserve_exact(depth)
            .map_err(|_| CarrierGrowth::Refused)?;
        overflow.resize_with(depth, || Arc::new(Vec::new()));
        Ok(Self {
            words: Arc::new(words),
            overflow: Arc::new(overflow),
        })
    }

    /// Form one complete native carrier from its exact enclosure cores and dynamic co-presence.
    /// Structural validation belongs to [`crate::LiveCarrierSnapshot`]; this constructor only
    /// closes physical extents without inventing or dropping a row.
    pub(crate) fn from_parts(
        words: Vec<u32>,
        overflow: Vec<Vec<Node>>,
    ) -> Result<Self, CarrierGrowth> {
        if words.is_empty()
            || words.len() % ENCLOSURE_WORDS != 0
            || overflow.len() != words.len() / ENCLOSURE_WORDS
        {
            return Err(CarrierGrowth::Refused);
        }
        let mut shared_overflow = Vec::new();
        shared_overflow
            .try_reserve_exact(overflow.len())
            .map_err(|_| CarrierGrowth::Refused)?;
        for row in overflow {
            shared_overflow.push(Arc::new(row));
        }
        Ok(Self {
            words: Arc::new(words),
            overflow: Arc::new(shared_overflow),
        })
    }

    pub fn depth(&self) -> usize {
        self.words.len() / ENCLOSURE_WORDS
    }

    pub fn words(&self) -> &[u32] {
        &self.words
    }

    pub fn co_present_overflow(&self, depth: usize) -> Option<&[Node]> {
        self.overflow.get(depth).map(|row| row.as_slice())
    }

    pub fn has_overflow(&self) -> bool {
        self.overflow.iter().any(|row| !row.is_empty())
    }
}

impl CarrierStorage for GrowingCarrier {
    fn words(&self) -> &[u32] {
        &self.words
    }

    fn words_mut(&mut self) -> &mut [u32] {
        Arc::make_mut(&mut self.words).as_mut_slice()
    }

    fn ensure_depth(&mut self, depth: usize) -> CarrierGrowth {
        if self.depth() >= depth {
            return CarrierGrowth::Present;
        }
        let Some(extent) = depth.checked_mul(ENCLOSURE_WORDS) else {
            return CarrierGrowth::Refused;
        };
        let overflow = Arc::make_mut(&mut self.overflow);
        let additional_rows = depth - overflow.len();
        if overflow.try_reserve_exact(additional_rows).is_err() {
            return CarrierGrowth::Refused;
        }
        let words = Arc::make_mut(&mut self.words);
        let additional_words = extent - words.len();
        if words.try_reserve_exact(additional_words).is_err() {
            return CarrierGrowth::Refused;
        }
        words.resize(extent, 0);
        overflow.resize_with(depth, || Arc::new(Vec::new()));
        CarrierGrowth::Present
    }

    fn co_present_overflow_len(&self, depth: usize) -> usize {
        self.overflow.get(depth).map_or(0, |row| row.len())
    }

    fn co_present_overflow_node(&self, depth: usize, at: usize) -> Option<Node> {
        self.overflow.get(depth)?.get(at).copied()
    }

    fn append_co_present_overflow(&mut self, depth: usize, node: Node) -> CarrierGrowth {
        let Some(row) = Arc::make_mut(&mut self.overflow).get_mut(depth) else {
            return CarrierGrowth::Refused;
        };
        let row = Arc::make_mut(row);
        if row.try_reserve(1).is_err() {
            return CarrierGrowth::Refused;
        }
        row.push(node);
        CarrierGrowth::Present
    }

    fn clear_co_present_overflow(&mut self, depth: usize) -> CarrierGrowth {
        let Some(row) = Arc::make_mut(&mut self.overflow).get_mut(depth) else {
            return CarrierGrowth::Refused;
        };
        Arc::make_mut(row).clear();
        CarrierGrowth::Present
    }

    fn legacy_projection_complete(&self) -> bool {
        !self.has_overflow()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::manifold::{atom_node, Enclosure, ErosBody};
    use body::num::Cog;
    use body::register::REGISTER;

    #[derive(Debug, PartialEq, Eq)]
    struct Face {
        axis: i64,
        occupancy: u64,
        breath: (u64, u64),
        own: Vec<body::manifold::SparseOwnCell>,
        channel: body::channel::LineageChannel,
        thoughts: u32,
        terms: body::manifold::TermCounts,
        carrier: GrowingCarrier,
    }

    fn run(initial_depth: usize) -> Face {
        let standing = crate::SparseStandingSurface::empty(128).unwrap();
        let mut own = crate::GrowingSparseOwn::new();
        let mut carrier = GrowingCarrier::with_depth(initial_depth).unwrap();
        let stream: [&[u8]; 16] = [
            b"the", b"cat", b"sat", b"on", b"my", b"mat", b"and", b"then", b"it", b"ran", b"to",
            b"see", b"an", b"old", b"dog", b"now",
        ];
        let state;
        {
            let mut body = ErosBody::over_sparse_world_storage_from_first_difference(
                standing.flat_cells().unwrap(),
                &mut own,
                standing.flat_axis().unwrap() as i64,
                atom_node(Cog::ZERO).place,
                &mut carrier,
            )
            .unwrap();
            for word in stream {
                body.perceive(word, 137);
            }
            assert!(!body.resource_refused());
            state = (
                body.own_axis(),
                body.own_occupancy(),
                body.breath(),
                body.sparse_own_cells().unwrap().to_vec(),
                body.channel(),
                body.thoughts(),
                body.deposited_terms(),
            );
        }
        Face {
            axis: state.0,
            occupancy: state.1,
            breath: state.2,
            own: state.3,
            channel: state.4,
            thoughts: state.5,
            terms: state.6,
            carrier,
        }
    }

    #[test]
    fn carrier_growth_is_the_same_construction_as_sufficient_initial_depth() {
        let mut grown = run(1);
        let mut deep = run(8);
        assert!(grown.carrier.words.len() > ENCLOSURE_WORDS);
        let common = grown.carrier.depth().max(deep.carrier.depth());
        assert_eq!(grown.carrier.ensure_depth(common), CarrierGrowth::Present);
        assert_eq!(deep.carrier.ensure_depth(common), CarrierGrowth::Present);
        assert_eq!(grown, deep);
    }

    #[test]
    fn shared_branch_changes_only_its_returned_carrier() {
        let standing = crate::SparseStandingSurface::empty(64).unwrap();
        // Repeated exact co-presence remains plural but never completes the lower construction.
        // It therefore exercises live overflow without retaining constituents after a cut.
        let arrivals = vec![atom_node(Cog::lit(3)); 23];
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
            for node in &arrivals {
                body.perceive_node(*node, 0);
            }
            assert!(!body.resource_refused());
            header = body.live_header(arrivals.len() as u64);
        }

        let prefix = Enclosure::unpack_at(carrier.words(), 0);
        assert_eq!(prefix.live, REGISTER as usize);
        assert_eq!(prefix.head, 0);
        assert_eq!(prefix.register.as_slice(), &arrivals[..REGISTER as usize]);
        assert_eq!(
            carrier.co_present_overflow(0).unwrap(),
            &arrivals[REGISTER as usize..]
        );
        assert!(carrier.has_overflow());

        let predecessor_words = carrier.words().to_vec();
        let predecessor_overflow = carrier.co_present_overflow(0).unwrap().to_vec();
        let mut branch = carrier.branch_shared();
        let next = atom_node(Cog::lit(101));
        let exact_faces;
        {
            let mut exact_own = crate::GrowingSparseOwn::new();
            let mut exact = ErosBody::resume_standing_world_storage_from_live_header(
                &standing,
                &mut exact_own,
                header,
                &mut branch,
            )
            .unwrap();
            exact_faces = exact.perceive_node(next, 0).faces;
            assert!(!exact.resource_refused());
        }
        assert_eq!(exact_faces, arrivals.len() as u32);
        assert_eq!(branch.co_present_overflow(0).unwrap().len(), 9);
        assert_eq!(carrier.words(), predecessor_words);
        assert_eq!(
            carrier.co_present_overflow(0).unwrap(),
            predecessor_overflow
        );
    }
}
