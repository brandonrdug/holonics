use super::*;

impl<'a> ContinuingBody<'a> {
    /// a driven body over a caller-provided felt medium (the boundary's reservation) ⊕ a caller-provided
    /// CARRIER (the illicium's live vertical state — rows of `ENCLOSURE_WORDS`, the same one-buffer
    /// discipline as the regional form: no cap, only the reservation the caller affords).
    /// `frame_seed` founds the lineage's gauge anchor. `quantum` remains only as a pre-M4 seam
    /// compatibility input; the felt series has no shared digit or divisor.
    pub fn over(
        standing: &'a [u32],
        own: &'a mut [u32],
        axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carrier: &'a mut [u32],
    ) -> ContinuingBody<'a> {
        let frame = wind(frame_seed);
        // `quantum` stays in the pre-M4 boundary signature only; the felt series re-bases inside
        // its own Cogs and consumes no shared divisor.
        let _ = quantum;
        ContinuingBody {
            medium: Medium::over(standing, own, axis),
            frame,
            pole: place::origin(),
            // §XXV: the first difference founds the first frame — the channel seeds at the seed
            // frame's own place.
            channel: LineageChannel::from_first_difference(frame)
                .expect("the seed frame is one dead-bit difference — never the origin"),
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        }
    }

    /// Found one lineage over a resident standing chart and its own reservation-sized local chart.
    /// Both axes are boundary-declared powers of two. The OWN buffer is `axis²` founded regional
    /// cells, not a plane over every standing place; each cell carries the construction that founded
    /// it so the true edge can re-ground it in the standing frame.
    pub fn over_resident(
        standing: &'a [u32],
        own: &'a mut [u32],
        standing_axis: i64,
        own_axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carrier: &'a mut [u32],
    ) -> ContinuingBody<'a> {
        assert!(
            standing_axis > 0 && standing_axis & (standing_axis - 1) == 0,
            "the standing chart has a dyadic boundary grain"
        );
        assert!(
            own_axis > 0 && own_axis & (own_axis - 1) == 0,
            "the lineage chart has a dyadic boundary grain"
        );
        assert!(
            standing.len() >= standing_axis as usize * standing_axis as usize * FORM_WORDS,
            "standing affords its declared chart"
        );
        assert!(
            own.len() >= own_axis as usize * own_axis as usize * OWN_CELL_WORDS,
            "OWN affords its declared lineage chart"
        );
        let frame = wind(frame_seed);
        let _ = quantum;
        ContinuingBody {
            medium: Medium::over_resident(standing, own, standing_axis, own_axis),
            frame,
            pole: place::origin(),
            channel: LineageChannel::from_first_difference(frame)
                .expect("the seed frame is one dead-bit difference — never the origin"),
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        }
    }

    /// THE REGISTER POSTURE (`FORMULA §XXXII-c`): found one lineage whose local chart is BORN at
    /// the uncommitted rank-zero seed and widens at its own occupancy register's carry events.
    /// No grain is chosen and no extent of the light is consulted — a world-delivered stream has
    /// no length while it is being related. The boundary supplies growth through `OwnRecast`;
    /// the mapping is the law's (`zero_extend_own_cells`).
    pub fn over_register(
        standing: &'a [u32],
        own: &'a mut dyn OwnRecast,
        standing_axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carrier: &'a mut [u32],
    ) -> ContinuingBody<'a> {
        assert!(
            standing_axis > 0 && standing_axis & (standing_axis - 1) == 0,
            "the standing chart has a dyadic boundary grain"
        );
        assert!(
            own.words().len() >= OWN_CELL_WORDS,
            "the rank-zero chart affords its one cell"
        );
        let frame = wind(frame_seed);
        let _ = quantum;
        ContinuingBody {
            medium: Medium::over_register(standing, own, standing_axis),
            frame,
            pole: place::origin(),
            channel: LineageChannel::from_first_difference(frame)
                .expect("the seed frame is one dead-bit difference — never the origin"),
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        }
    }

    /// Organ-neutral birth at a first difference which has already crossed the source organ's
    /// positional mouth.  Unlike the historical byte-seed constructor, no container spelling is
    /// re-read here.  `first_difference` is the carried frame itself; a source membrane commonly
    /// obtains it from [`atom_node`] on the current's first canonical relation atom.
    pub fn over_register_from_first_difference(
        standing: &'a [u32],
        own: &'a mut dyn OwnRecast,
        standing_axis: i64,
        first_difference: Place,
        carrier: &'a mut [u32],
    ) -> Option<ContinuingBody<'a>> {
        if standing_axis <= 0
            || standing_axis & (standing_axis - 1) != 0
            || own.words().len() < OWN_CELL_WORDS
        {
            return None;
        }
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ContinuingBody {
            medium: Medium::over_register(standing, own, standing_axis),
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// Organ-neutral production birth over an allocation-free sparse OWN reservation.  The caller
    /// derives `cells.len()` from [`current_conduct_envelope`] for this exact current and carrier
    /// depth.  The standing chart is immutable receiver-before terrain shared lawfully by every
    /// co-present lineage; no source representation or octet grain enters this constructor.
    pub fn over_sparse_from_first_difference(
        standing: &'a [u32],
        cells: &'a mut [SparseOwnCell],
        standing_axis: i64,
        first_difference: Place,
        carrier: &'a mut [u32],
    ) -> Option<ContinuingBody<'a>> {
        if standing_axis <= 0 || standing_axis & (standing_axis - 1) != 0 {
            return None;
        }
        let axis = usize::try_from(standing_axis).ok()?;
        let required = axis.checked_mul(axis)?.checked_mul(FORM_WORDS)?;
        if standing.len() < required {
            return None;
        }
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ContinuingBody {
            medium: Medium::over_sparse(standing, cells, standing_axis)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// Growable-storage counterpart of `over_sparse_from_first_difference`.  Storage growth is a
    /// substrate act behind [`SparseOwnStorage`]; the body performs the identical sparse REGISTER
    /// transition and reports physical refusal to the enclosing transaction.
    pub fn over_sparse_storage_from_first_difference(
        standing: &'a [u32],
        storage: &'a mut dyn SparseOwnStorage,
        standing_axis: i64,
        first_difference: Place,
        carrier: &'a mut [u32],
    ) -> Option<ContinuingBody<'a>> {
        if standing_axis <= 0 || standing_axis & (standing_axis - 1) != 0 {
            return None;
        }
        let axis = usize::try_from(standing_axis).ok()?;
        let required = axis.checked_mul(axis)?.checked_mul(FORM_WORDS)?;
        if standing.len() < required {
            return None;
        }
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ContinuingBody {
            medium: Medium::over_sparse_storage(standing, storage, standing_axis)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// The fully sparse production posture: both the shared receiver-before terrain and this
    /// current's independently growing OWN surface are proportional to lived topology.  The
    /// standing slice is immutable and canonical at `standing_axis`; every co-present current may
    /// borrow that same before-face while retaining a separate cells/carrier reservation.
    pub fn over_sparse_world_from_first_difference(
        standing: &'a [SparseStandingCell],
        cells: &'a mut [SparseOwnCell],
        standing_axis: i64,
        first_difference: Place,
        carrier: &'a mut [u32],
    ) -> Option<ContinuingBody<'a>> {
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ContinuingBody {
            medium: Medium::over_sparse_standing(standing, cells, standing_axis)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    pub fn over_sparse_world_storage_from_first_difference(
        standing: &'a [SparseStandingCell],
        storage: &'a mut dyn SparseOwnStorage,
        standing_axis: i64,
        first_difference: Place,
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ContinuingBody<'a>> {
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ContinuingBody {
            medium: Medium::over_sparse_world_storage(standing, storage, standing_axis)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// General production birth over a receiver-owned standing-query surface.  The query maps the
    /// exact Soma construction into its own address species; neither a flat axis nor a storage
    /// coordinate enters the body.
    pub fn over_standing_world_storage_from_first_difference(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn SparseOwnStorage,
        first_difference: Place,
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ContinuingBody<'a>> {
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ContinuingBody {
            medium: Medium::over_standing_query_storage(standing, storage)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// Ceiling-free organ-neutral production birth. Both the receiver and current-local OWN are
    /// addressed by the complete Soma construction; source modality and flat chart words are
    /// absent from this mouth.
    pub fn over_standing_world_ranked_storage_from_first_difference(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn RankedOwnStorage,
        first_difference: Place,
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ContinuingBody<'a>> {
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ContinuingBody {
            medium: Medium::over_standing_query_ranked_storage(standing, storage)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// Continue one already-enacted organ-neutral body over a new sparse receiver-before surface.
    /// `K`, the open sub-illicium, dark passage, and carrier cross whole; the prior current-local
    /// OWN chart does not.  Its deeds have already integrated into standing and §XXXII-c requires
    /// that chart to die at the receiving edge, so this later current begins with a fresh rank-zero
    /// REGISTER. `carried` and `carrier` must still describe the same exact live body.
    pub fn resume_sparse_world_storage(
        standing: &'a [SparseStandingCell],
        storage: &'a mut dyn SparseOwnStorage,
        standing_axis: i64,
        carried: &[u32],
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ContinuingBody<'a>> {
        let carrier_words = carrier.words();
        if carrier_words.is_empty() || carrier_words.len() % ENCLOSURE_WORDS != 0 {
            return None;
        }
        let depth = carrier_words.len() / ENCLOSURE_WORDS;
        let required = carrier_row_words(depth);
        if carried.len() != required || !carried_frame_is_at_rest(carried) {
            return None;
        }
        let enclosure_base = carrier_enclosure_base(0);
        if carried.get(enclosure_base..enclosure_base + carrier_words.len())? != carrier_words {
            return None;
        }
        let channel = LineageChannel::unpack(carried, CARRIER_CHANNEL)?;
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        Some(ContinuingBody {
            medium: Medium::over_sparse_world_storage(standing, storage, standing_axis)?,
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        })
    }

    /// Continue one exact carried body over an arbitrary receiver-owned standing-query surface.
    /// The carried frame is validated before OWN reset, exactly as in the flat compatibility
    /// posture; only the terrain addressing mouth differs.
    pub fn resume_standing_world_storage(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn SparseOwnStorage,
        carried: &[u32],
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ContinuingBody<'a>> {
        let carrier_words = carrier.words();
        if carrier_words.is_empty() || carrier_words.len() % ENCLOSURE_WORDS != 0 {
            return None;
        }
        let depth = carrier_words.len() / ENCLOSURE_WORDS;
        let required = carrier_row_words(depth);
        if carried.len() != required || !carried_frame_is_at_rest(carried) {
            return None;
        }
        let enclosure_base = carrier_enclosure_base(0);
        if carried.get(enclosure_base..enclosure_base + carrier_words.len())? != carrier_words {
            return None;
        }
        let header = LiveBodyHeader::from_words_checked(carried.get(..CARRIER_HEADER_WORDS)?)?;
        Self::resume_standing_world_storage_from_live_header(standing, storage, header, carrier)
    }

    /// Continue a generalized live body from its one exact header and complete typed carrier.
    /// Unlike the historical carried-frame mouth, this path has no flat REGISTER projection and
    /// therefore cannot silently omit dynamically admitted co-presence.
    pub fn resume_standing_world_storage_from_live_header(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn SparseOwnStorage,
        header: LiveBodyHeader,
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ContinuingBody<'a>> {
        let carrier_words = carrier.words();
        if carrier_words.is_empty() || carrier_words.len() % ENCLOSURE_WORDS != 0 {
            return None;
        }
        let carried = header.words();
        let channel = header.channel();
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        Some(ContinuingBody {
            medium: Medium::over_standing_query_storage(standing, storage)?,
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        })
    }

    /// Ceiling-free continuation of one complete carried body. The predecessor's exact live
    /// carrier returns whole while this receiving event begins a fresh ranked current-local OWN
    /// population over the new standing world.
    pub fn resume_standing_world_ranked_storage_from_live_header(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn RankedOwnStorage,
        header: LiveBodyHeader,
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ContinuingBody<'a>> {
        let carrier_words = carrier.words();
        if carrier_words.is_empty() || carrier_words.len() % ENCLOSURE_WORDS != 0 {
            return None;
        }
        let carried = header.words();
        let channel = header.channel();
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        Some(ContinuingBody {
            medium: Medium::over_standing_query_ranked_storage(standing, storage)?,
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        })
    }

    /// Exact live cells of the sparse production posture.  This is a borrowed body face; callers
    /// may retain it as a carried surface only after the current has completed.
    pub fn sparse_own_cells(&self) -> Option<&[SparseOwnCell]> {
        match &self.medium.own {
            OwnStore::Sparse { cells, state } => state.cells(&**cells),
            OwnStore::SparseStorage { storage, state } => state.cells(&**storage),
            _ => None,
        }
    }

    /// Exact current-local dyadic rank. Unlike `own_axis`, this face has no scalar-axis ceiling.
    pub fn own_rank(&self) -> u64 {
        match &self.medium.own {
            OwnStore::RankedStorage { state, .. } => state.rank(),
            _ => (self.medium.own_axis as u64).trailing_zeros() as u64,
        }
    }

    /// Exact arbitrary-width occupancy words for the production ranked posture. Historical
    /// postures retain their `u64` compatibility observer instead.
    pub fn ranked_own_occupancy_words(&self) -> Option<&[u64]> {
        match &self.medium.own {
            OwnStore::RankedStorage { storage, .. } => Some(storage.occupancy_words()),
            _ => None,
        }
    }

    pub fn ranked_own_cell_count(&self) -> Option<usize> {
        match &self.medium.own {
            OwnStore::RankedStorage { storage, .. } => Some(storage.cell_count()),
            _ => None,
        }
    }

    pub fn ranked_own_cell_face(&self, at: usize) -> Option<RankedOwnCellFace> {
        match &self.medium.own {
            OwnStore::RankedStorage { storage, .. } => storage.cell_face(at),
            _ => None,
        }
    }

    /// Physical sparse-storage refusal on this disposable current-local successor.  The body never
    /// converts it into a deed or clips the event; the membrane must discard the whole uncommitted
    /// current and leave the receiver-before owner installed.
    pub fn resource_refused(&self) -> bool {
        self.medium.resource_refused
    }

    pub fn required_carrier_depth(&self) -> Option<usize> {
        (self.required_carrier_depth != 0).then_some(self.required_carrier_depth)
    }

    /// The lineage chart's current grain — the register's own axis after whatever carry events
    /// its arrivals produced. A declared-grain posture returns its declared axis unchanged.
    pub fn own_axis(&self) -> i64 {
        assert!(
            !matches!(self.medium.own, OwnStore::RankedStorage { .. }),
            "a ranked OWN chart has no necessarily representable scalar axis"
        );
        self.medium.own_axis
    }

    /// Boundary read of the current-local chart register's occupied-grip population.  It is
    /// testimony beside the exact cells and never drives a body deed.
    pub fn own_occupancy(&self) -> u64 {
        assert!(
            !matches!(self.medium.own, OwnStore::RankedStorage { .. }),
            "a ranked OWN population has no necessarily representable u64 count"
        );
        self.medium.register.occupancy
    }

    /// THE BREATH READ (instrument, off the hot path, never a body input): `(releases, narrows)`
    /// — annihilation-released cells and retired digits over this current's life.
    pub fn breath(&self) -> (u64, u64) {
        (self.medium.releases, self.medium.narrows)
    }

    /// Continue one already-carried lineage over a new light without founding a replacement body.
    /// `carried` is the exact boundary row written by `pack_carried_frame`: its header restores the
    /// open sub-illicium and K, while its enclosure extent is still only the reservation afforded by
    /// the membrane. This constructor is the cpu mirror instrument for standing-life gates; on the
    /// card the same words never leave their resident buffer.
    pub fn resume(
        standing: &'a [u32],
        own: &'a mut [u32],
        axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carried: &'a mut [u32],
    ) -> ContinuingBody<'a> {
        let depth = carrier_row_depth(carried.len());
        let required = carrier_row_words(depth);
        assert!(
            depth != 0 && carried.len() >= required,
            "a continuing lineage carries one whole reserved row"
        );
        assert!(
            carried_frame_is_at_rest(&carried[..required]),
            "the legacy cpu resume cannot cut an unfinished within-atom continuation"
        );
        // The carried channel is the continuing frame. The arriving light's seed may found only a
        // genuinely new zeroed carrier; it cannot replace a live predecessor at resume.
        let _ = frame_seed;
        let channel = LineageChannel::unpack(carried, CARRIER_CHANNEL)
            .expect("a continuing lineage carries its complete channel K");
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        let enclosure_base = carrier_enclosure_base(0);
        let enclosure_words = depth * ENCLOSURE_WORDS;
        let carrier = &mut carried[enclosure_base..enclosure_base + enclosure_words];
        let _ = quantum;
        ContinuingBody {
            medium: Medium::over(standing, own, axis),
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        }
    }

    /// Continue one already-carried lineage over its resident local chart. This is the founded-chart
    /// counterpart of `resume`: the carrier restores the same open illicium and K while standing
    /// and OWN retain their distinct boundary grains. The next light receives the standing body at
    /// `standing_axis` and deposits into the lineage's unchanged `own_axis` reservation.
    pub fn resume_resident(
        standing: &'a [u32],
        own: &'a mut [u32],
        standing_axis: i64,
        own_axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carried: &'a mut [u32],
    ) -> ContinuingBody<'a> {
        assert!(
            standing_axis > 0 && standing_axis & (standing_axis - 1) == 0,
            "the standing chart has a dyadic boundary grain"
        );
        assert!(
            own_axis > 0 && own_axis & (own_axis - 1) == 0,
            "the lineage chart has a dyadic boundary grain"
        );
        assert!(
            standing.len() >= standing_axis as usize * standing_axis as usize * FORM_WORDS,
            "standing affords its declared chart"
        );
        assert!(
            own.len() >= own_axis as usize * own_axis as usize * OWN_CELL_WORDS,
            "OWN affords its declared lineage chart"
        );
        let depth = carrier_row_depth(carried.len());
        let required = carrier_row_words(depth);
        assert!(
            depth != 0 && carried.len() >= required,
            "a continuing lineage carries one whole reserved row"
        );
        assert!(
            carried_frame_is_at_rest(&carried[..required]),
            "the legacy resident resume cannot cut an unfinished within-atom continuation"
        );
        // The carried channel is the continuing frame. The arriving light's seed may found only a
        // genuinely new zeroed carrier; it cannot replace a live predecessor at resume.
        let _ = frame_seed;
        let channel = LineageChannel::unpack(carried, CARRIER_CHANNEL)
            .expect("a continuing lineage carries its complete channel K");
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        let enclosure_base = carrier_enclosure_base(0);
        let enclosure_words = depth * ENCLOSURE_WORDS;
        let carrier = &mut carried[enclosure_base..enclosure_base + enclosure_words];
        let _ = quantum;
        ContinuingBody {
            medium: Medium::over_resident(standing, own, standing_axis, own_axis),
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        }
    }

    /// Continue one already-carried lineage while the arriving light opens a fresh event-born
    /// REGISTER. The complete carrier restores K and the open illicium; no local chart face crosses
    /// the receiving edge. Consequently the new current begins from the same uncommitted rank-zero
    /// seed as `over_register`, and only its own FOIL arrivals choose its later grain.
    pub fn resume_register(
        standing: &'a [u32],
        own: &'a mut dyn OwnRecast,
        standing_axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carried: &'a mut [u32],
    ) -> ContinuingBody<'a> {
        assert!(
            standing_axis > 0 && standing_axis & (standing_axis - 1) == 0,
            "the standing chart has a dyadic boundary grain"
        );
        assert!(
            standing.len() >= standing_axis as usize * standing_axis as usize * FORM_WORDS,
            "standing affords its declared chart"
        );
        assert!(
            own.words().len() >= OWN_CELL_WORDS,
            "the rank-zero chart affords its one cell"
        );
        let depth = carrier_row_depth(carried.len());
        let required = carrier_row_words(depth);
        assert!(
            depth != 0 && carried.len() >= required,
            "a continuing lineage carries one whole reserved row"
        );
        assert!(
            carried_frame_is_at_rest(&carried[..required]),
            "the register resume cannot cut an unfinished within-atom continuation"
        );
        // The carried channel is the continuing frame. The arriving light's seed cannot replace a
        // live predecessor; it only supplies the boundary pair already present in the raw light.
        let _ = frame_seed;
        let channel = LineageChannel::unpack(carried, CARRIER_CHANNEL)
            .expect("a continuing lineage carries its complete channel K");
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        let enclosure_base = carrier_enclosure_base(0);
        let enclosure_words = depth * ENCLOSURE_WORDS;
        let carrier = &mut carried[enclosure_base..enclosure_base + enclosure_words];
        let _ = quantum;
        ContinuingBody {
            medium: Medium::over_register(standing, own, standing_axis),
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        }
    }

    /// the carrier's own extent — the reservation's rows (`carrier.len() / ENCLOSURE_WORDS`), NEVER
    /// a constant: the boundary's reservation is the caller's, like the pool.
    #[inline]
    pub fn carrier_depth(&self) -> usize {
        self.carrier.words().len() / ENCLOSURE_WORDS
    }

    /// Retain the exact first-person header independently of any particular carrier storage
    /// projection. The generalized live snapshot pairs this with the complete typed carrier.
    pub fn live_header(&self, cursor: u64) -> LiveBodyHeader {
        let mut words = [0u32; CARRIER_HEADER_WORDS];
        words[CARRIER_CURSOR_LO] = cursor as u32;
        words[CARRIER_CURSOR_HI] = (cursor >> 32) as u32;
        words[CARRIER_DARK_LO] = self.dark_pending as u32;
        words[CARRIER_DARK_HI] = (self.dark_pending >> 32) as u32;
        if self.sub_stance.len != 0 {
            pack_node(self.sub_stance, &mut words, CARRIER_SUB_STANCE);
        }
        if self.sub_fly_live {
            pack_face(self.sub_fly, &mut words, CARRIER_SUB_FLY);
            words[CARRIER_SUB_FLY_LIVE] = 1;
        }
        self.channel.pack(&mut words, CARRIER_CHANNEL);
        debug_assert!(live_body_header_is_canonical(&words));
        LiveBodyHeader { words }
    }

    /// Pack the WHOLE CARRIED FRAME into the card's one shared row layout. This is a boundary
    /// mirror instrument: cursor is the membrane's own progress through the current worldline;
    /// every live organ comes from this body; deferred slots are empty because a beat drains its
    /// thickening before returning. The pool never consults this rendering.
    pub fn pack_carried_frame(&self, cursor: u64, out: &mut [u32]) -> bool {
        if !self.carrier.legacy_projection_complete() {
            return false;
        }
        let depth = self.carrier_depth();
        let words = carrier_row_words(depth);
        if out.len() < words {
            return false;
        }
        let mut i = 0usize;
        while i < words {
            out[i] = 0;
            i += 1;
        }
        let header = self.live_header(cursor);
        out[..CARRIER_HEADER_WORDS].copy_from_slice(header.words());
        let enclosure_base = carrier_enclosure_base(0);
        let mut j = 0usize;
        while j < self.carrier.words().len() {
            out[enclosure_base + j] = self.carrier.words()[j];
            j += 1;
        }
        true
    }

    /// an enclosure at depth `d` — unpacked from the carrier's own row. Past the reservation's own
    /// extent there is no row to read: the unborn enclosure (`Enclosure::empty()`) stands there, the
    /// same lawful birth an all-zero row already reads as.
    pub(super) fn enclosure(&self, d: usize) -> Enclosure {
        let base = d * ENCLOSURE_WORDS;
        if base + ENCLOSURE_WORDS > self.carrier.words().len() {
            return Enclosure::empty();
        }
        Enclosure::unpack_at(self.carrier.words(), base)
    }

    /// store an enclosure into the carrier's row at depth `d` (packed local, then copied — plain
    /// copies are lawful on the cpu). A depth past the reservation is never stored to (THE
    /// RETIREMENT handles it before this is ever called).
    pub(super) fn enclosure_store(&mut self, d: usize, e: &Enclosure) {
        let base = d * ENCLOSURE_WORDS;
        if base + ENCLOSURE_WORDS > self.carrier.words().len() {
            return;
        }
        let mut row = [0u32; ENCLOSURE_WORDS];
        e.pack(&mut row);
        self.carrier.words_mut()[base..base + ENCLOSURE_WORDS].copy_from_slice(&row);
    }

    /// the STANDING THOUGHT — where depth 0's circulation stands (the pole of every word-grain perception).
    #[inline]
    pub fn stance(&self) -> Node {
        self.enclosure(0).stance
    }

    /// how many enclosures stand open across the whole carrier (a boundary read — an audit, scanning
    /// the reservation): a row whose stance is born or whose register carries co-presence counts.
    pub fn standing_enclosures(&self) -> u32 {
        let mut n = 0u32;
        let mut d = 0usize;
        let depth = self.carrier_depth();
        while d < depth {
            let e = self.enclosure(d);
            if e.stance.len != 0 || e.live > 0 {
                n += 1;
            }
            d += 1;
        }
        n
    }

    /// completed thoughts — the swing's cuts so far.
    #[inline]
    pub fn thoughts(&self) -> u32 {
        self.thoughts
    }

    /// How many chi-bearing FeltTerms successfully landed in this body's lane-local spool during
    /// the present light. This is membrane instrumentation, not a transition input or scalar read
    /// of the form; cancellations remain visible through the regional fiber/resultant topology.
    #[inline]
    pub fn deposited_terms(&self) -> TermCounts {
        self.terms_deposited
    }

    /// ★ THE CONE at a grip (`§XXVIII`) — the reader's whole past cone: PRE-LIGHT STANDING ⊕ this
    /// body's OWN deposits, joined as the felt series. The terrain read the drag consumes and the reads
    /// consult; the retired flow/sweep word is gone.
    #[inline]
    pub fn cone(&self, g: Grip) -> RegionalForm {
        self.medium.cone(g)
    }

    /// boundary read of depth 0's flywheel (the held rotor) — for mirror instrumentation.
    #[inline]
    pub fn flywheel(&self) -> (Face, bool) {
        let e = self.enclosure(0);
        (e.fly, e.fly_live)
    }

    /// Capture the historical atom-event receiver before that event changes any live state. The
    /// private sub-illicium belongs to an organ event's component walk and cannot lawfully make
    /// directed incidence depend on how that event happened to be decomposed for storage.
    pub fn event_receiver(&self) -> EventReceiver {
        self.event_receiver_at_source_grain(1)
            .expect("the historical atom event has one receiving grain")
    }

    /// Capture the actual receiver for a source constituent whose boundary has already completed
    /// at `source_grain`. Grain one enters carrier enclosure zero; every greater grain enters the
    /// correspondingly enclosing row. Reading beyond the mounted carrier is the exact unborn
    /// receiver and does not allocate or create an event.
    pub fn event_receiver_at_source_grain(&self, source_grain: u32) -> Option<EventReceiver> {
        let depth = usize::try_from(source_grain.checked_sub(1)?).ok()?;
        let enclosure = self.enclosure(depth);
        Some(EventReceiver {
            channel: self.channel,
            held: enclosure.fly,
            held_live: enclosure.fly_live,
        })
    }

    /// Form one source-supplied directed A2 contact against a previously captured target receiver.
    /// The target's complete past cone drags the meeting through the same `complete_cast` law as
    /// ordinary conduct.
    ///
    /// **CORRECTED 2026-08-15.** This doc read *"this probe neither deposits into current-local OWN
    /// nor folds the lineage channel a second time"*, which described what the path happened to do
    /// and was then read as a law about what it could do. It was neither. Measured: over 1,199
    /// passages this path moved **no word of any carrier** and the ecology's frame stood at genesis
    /// in 21,070 of 21,070 contacts.
    ///
    /// **THIS PATH STILL DEPOSITS NOTHING, and an earlier form of this doc said otherwise.** The
    /// deposit was wired on 2026-08-15, moved 12 frame words and 7 carrier words, and was **reverted
    /// whole** after the carrier refused it: `soma/membrane/src/live_carrier.rs:357-368` requires a
    /// **born stance** before a flywheel may be live, and this path founds no stance. The doc was
    /// left behind describing the repair as landed — *grade the implementation, not the receipt*,
    /// committed on a doc comment, which is the same defect the paragraph above convicts. Corrected
    /// the same day it was written.
    ///
    /// What is true: nothing here prevents a deposit, the stance law is the obstruction, and
    /// `directed_event_contact_over_standing` is the read-only twin for queries.
    pub fn directed_event_contact(
        &mut self,
        receiver: EventReceiver,
        from: Place,
        to: Place,
    ) -> DirectedEventContact {
        self.directed_event_contact_at_source_grain(receiver, 1, from, to)
    }

    /// Form one directed meeting against the same pre-event enclosure which receives a completed
    /// source constituent at `source_grain`. This is not a search across scales: the source's
    /// declared boundary fixes the one enclosure, and an unborn enclosure remains an honest open
    /// fourth contact.
    pub fn directed_event_contact_at_source_grain(
        &mut self,
        receiver: EventReceiver,
        source_grain: u32,
        from: Place,
        to: Place,
    ) -> DirectedEventContact {
        // `to` is the arriving event face and `from` is the standing event face.  Their pole is
        // the target's complete pre-event lineage frame, never an event ordinal or the private
        // component-walk frame.  Reversing the supplied hand therefore reverses the actual A2
        // construction rather than merely changing listener testimony.
        let meeting = face(to, from, receiver.channel.frame().tip());
        if self.event_receiver_at_source_grain(source_grain) != Some(receiver) {
            // The receiver is not this body's at this grain, so nothing happened here and nothing
            // is deposited. This is the one branch that is genuinely a refusal rather than a stage.
            return DirectedEventContact {
                receiver,
                meeting,
                emission: None,
            };
        }
        if !receiver.held_live {
            // A three-body triangle is frame-local and is not yet a soul; the held flywheel supplies
            // the fourth contact. On a first contact there is none, so no invariant exists and no
            // emission may be manufactured.
            //
            // **NO DEPOSIT HAPPENS HERE, and an earlier comment claimed one did.** Holding this
            // meeting as the fourth body would need a born stance at this depth
            // (`live_carrier.rs:357-368`), and this path founds none — so `held_live` stays false
            // for every contact and the path reads a frame nothing advances. That is the open
            // construction, not a line that is present.
            return DirectedEventContact {
                receiver,
                meeting,
                emission: None,
            };
        }
        let (_grip, _regional_form, met, standing_read) =
            self.complete_cast(meeting, &receiver.held, true);
        if met.arrow.at_horizon() {
            // The drag took the meeting behind this pole's horizon. No deed, and nothing to hold.
            return DirectedEventContact {
                receiver,
                meeting,
                emission: None,
            };
        }
        let Some(chi) = met.chi_against(&receiver.held) else {
            return DirectedEventContact {
                receiver,
                meeting,
                emission: None,
            };
        };
        let wound = met.wound_against(&receiver.held);
        let winding = if !wound {
            WindingQuantum::None
        } else if chi.other.turn & 2 == 0 {
            WindingQuantum::ThisWay
        } else {
            WindingQuantum::ThatWay
        };
        let deed = match winding {
            WindingQuantum::None => FeltDeed::Ride,
            WindingQuantum::ThisWay => FeltDeed::FoundThis,
            WindingQuantum::ThatWay => FeltDeed::FoundThat,
        };
        DirectedEventContact {
            receiver,
            meeting,
            emission: Some(FeltEmission {
                position: cast_position(chi),
                term: FeltTerm { chi, winding },
                deed,
                standing_read,
            }),
        }
    }

    /// `K` — the body's lineage channel (§XXV): the ordered composition of its own deed emanations.
    #[inline]
    pub fn channel(&self) -> LineageChannel {
        self.channel
    }

    /// `Θ = TURN(K)` — the HOW-WOUND read of the channel, at a reach re-judged by the present
    /// landing (§XXVI — the reach is supplied at the read, never carried).
    #[inline]
    pub fn turn_at(&self, reach: Cog) -> WorldlineTurn {
        self.channel.turn_at(reach)
    }

    /// Restore `K` at a stroke resume — the membrane hands the carried frame's channel back to a
    /// freshly mounted body (`over()` seeds only the genesis channel; across a seam the worldline
    /// CONTINUES, never restarts). The membrane's stroke-resume mouth; every other advance of the
    /// channel is the body's own fold.
    #[inline]
    pub fn adopt_channel(&mut self, k: LineageChannel) {
        self.channel = k;
    }
}
