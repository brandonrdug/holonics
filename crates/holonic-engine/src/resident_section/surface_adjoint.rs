use super::*;

impl<'chart> ResidentSurface<'chart> {
    // -----------------------------------------------------------------------------------------
    // the return: the receiver return and the adjoint of every reaction, recorded onto lanes
    // -----------------------------------------------------------------------------------------

    /// Record the carry of a resident standing into `out`.
    /// The receiver return over the resident emission and reacted tiles named by `tiles` (a
    /// resident table of `4 · tile_count` addresses: `e_lo, e_hi, t_lo, t_hi` per tile) against the
    /// resident next-occurrence addresses `next` (one per row). Writes the deposit enclosure into
    /// `out`, a `[width x rows]` section in the factorized map's `u` layout.
    #[allow(clippy::too_many_arguments)]
    pub fn record_receiver_return(
        &self,
        lane: &Lane<'_, 'chart>,
        tiles: u64,
        tile_count: u32,
        tile_width: u32,
        rows: u32,
        width: u32,
        next: u64,
        grain: ResidentGrain,
        terms: SeriesAperture,
        deposit_shift: u32,
        shape: &LawShape,
        out: &ResidentSection<'chart>,
        differential: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if out.rows() != width as usize
            || out.width() != rows as usize
            || differential.rows() != rows as usize
            || differential.width() != width as usize
        {
            return Err(ResidentRefusal::RowsDisagree {
                operation: "receiver-return",
                left: out.rows() * out.width(),
                right: width as usize * rows as usize,
            });
        }
        let mut params = Params::new();
        params
            .ptr(tiles)
            .u32(tile_count)
            .u32(tile_width)
            .u32(rows)
            .u32(width)
            .ptr(next)
            .i32(grain.0 as i32)
            .u32(terms.0)
            .u32(deposit_shift)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(differential.lo.device_ptr())
            .ptr(differential.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_receiver_return",
            rows as usize,
            shape.block,
            shape.shared_octets,
            &mut params,
            "receiver-return",
        )
    }

    /// The adjoint of the contraction over one aligned tile into slots
    /// `slot_base .. slot_base + sub_splits` of a retained partial standing.
    #[allow(clippy::too_many_arguments)]
    pub fn record_contract_transposed_partial(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        map: &MountedReadout<'chart>,
        standing: &PartialStanding,
        slot_base: u32,
        sub_splits: u32,
        admitted_node_octaves: u32,
    ) -> Result<(), ResidentRefusal> {
        if input.width != map.rows()
            || standing.rows != input.rows
            || standing.out_width != map.dim()
            || slot_base + sub_splits > standing.splits
        {
            return Err(ResidentRefusal::Declaration {
                operation: "contract-transposed-partial",
                what: format!(
                    "the differential is {}x{}, the tile {} rows x {}, the standing {}x{}x{}, slots {}..{}",
                    input.rows,
                    input.width,
                    map.rows(),
                    map.dim(),
                    standing.splits,
                    standing.rows,
                    standing.out_width,
                    slot_base,
                    slot_base + sub_splits
                ),
            });
        }
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .ptr(map.raw_resident())
            .u32(map.dim() as u32)
            .u32(sub_splits)
            .u32(slot_base)
            .ptr(standing.pointer)
            .u32(admitted_node_octaves)
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_contract_transposed_partial",
            input.rows * map.dim() * sub_splits as usize,
            &mut params,
            "contract-transposed-partial",
        )
    }

    /// The single-rounding join of a retained partial standing into `out`, under the fixed
    /// ascending tree.  `map_e` is the exponent every partial was accumulated at.

    pub fn record_partial_join(
        &self,
        lane: &Lane<'_, 'chart>,
        standing: &PartialStanding,
        map_e: i32,
        admitted_node_octaves: u32,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if out.rows() != standing.rows || out.width() != standing.out_width {
            return Err(ResidentRefusal::RowsDisagree {
                operation: "partial-join",
                left: standing.rows * standing.out_width,
                right: out.rows() * out.width(),
            });
        }
        let mut params = Params::new();
        params
            .ptr(standing.pointer)
            .u32(standing.splits)
            .u32(standing.rows as u32)
            .u32(standing.out_width as u32)
            .i32(map_e)
            .i32(out.grain.0 as i32)
            .u32(admitted_node_octaves)
            .u32(LaneTree::Descending.word())
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_contract_join",
            standing.rows * standing.out_width,
            &mut params,
            "partial-join",
        )
    }

    /// The adjoint factor of the hyperbolic tangent: `g = 1 − t²` of the reacted carrier.

    /// The transposed midpoint seal: `out[o, t] = −mid(input[t, o]) · 2^-shift` as a point.
    pub fn record_transpose_seal(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        shift: u32,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if out.rows() != input.width || out.width() != input.rows {
            return Err(ResidentRefusal::RowsDisagree {
                operation: "transpose-seal",
                left: input.rows * input.width,
                right: out.rows() * out.width(),
            });
        }
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .u32(shift)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_transpose_seal",
            input.rows * input.width,
            &mut params,
            "transpose-seal",
        )
    }

    /// Record the rank-one junction as one device kernel.  The parameter order mirrors the
    /// kernel's two resident maps and keeps both factor ranges in the footprint certificate.

    pub fn record_one_minus_square(
        &self,
        lane: &Lane<'_, 'chart>,
        reacted: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(reacted.lo.device_ptr())
            .ptr(reacted.hi.device_ptr())
            .u32(reacted.count() as u32)
            .i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_one_minus_square",
            reacted.count(),
            &mut params,
            "one-minus-square",
        )
    }

    /// The derivative of the source's `gelu_pytorch_tanh` at the presented carrier.

    pub fn record_gelu_tanh_derivative(
        &self,
        lane: &Lane<'_, 'chart>,
        presented: &ResidentSection<'chart>,
        c1: Dyadic,
        c2: Dyadic,
        terms: SeriesAperture,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(presented.lo.device_ptr())
            .ptr(presented.hi.device_ptr())
            .u32(presented.count() as u32)
            .i64(c1.significand)
            .i32(c1.exponent)
            .i64(c2.significand)
            .i32(c2.exponent)
            .i32(out.grain.0 as i32)
            .u32(terms.0)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_gelu_tanh_derivative",
            presented.count(),
            &mut params,
            "gelu-tanh-derivative",
        )
    }

    /// Place a face of `span` columns at column `at` of every row of `out`, zero elsewhere: the
    /// adjoint of the column selection.

    pub fn record_place_columns(
        &self,
        lane: &Lane<'_, 'chart>,
        face: &ResidentSection<'chart>,
        at: usize,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if face.rows != out.rows() || at + face.width > out.width() {
            return Err(ResidentRefusal::RowsDisagree {
                operation: "place-columns",
                left: face.rows * face.width,
                right: out.rows() * out.width(),
            });
        }
        let mut params = Params::new();
        params
            .ptr(face.lo.device_ptr())
            .ptr(face.hi.device_ptr())
            .u32(face.rows as u32)
            .u32(face.width as u32)
            .u32(out.width() as u32)
            .u32(at as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_place_columns",
            out.count(),
            &mut params,
            "place-columns",
        )
    }

    /// The adjoint of the RMS rebase over the presented carrier and the returning differential.
    #[allow(clippy::too_many_arguments)]

    pub fn record_rms_rebase_adjoint(
        &self,
        lane: &Lane<'_, 'chart>,
        presented: &ResidentSection<'chart>,
        differential: &ResidentSection<'chart>,
        group: usize,
        gain: Option<&MountedReadout<'chart>>,
        eps: Dyadic,
        shape: &LawShape,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if presented.rows != differential.rows
            || presented.width != differential.width
            || out.rows() != presented.rows
            || out.width() != presented.width
        {
            return Err(ResidentRefusal::RowsDisagree {
                operation: "rms-rebase-adjoint",
                left: presented.rows * presented.width,
                right: differential.rows * differential.width,
            });
        }
        let mut params = Params::new();
        params
            .ptr(presented.lo.device_ptr())
            .ptr(presented.hi.device_ptr())
            .ptr(differential.lo.device_ptr())
            .ptr(differential.hi.device_ptr())
            .u32(presented.rows as u32)
            .u32(presented.width as u32)
            .u32(group as u32)
            .ptr(gain.map(MountedReadout::raw_resident).unwrap_or(0))
            .i32(gain.map(MountedReadout::exponent).unwrap_or(0))
            .i64(eps.significand)
            .i32(eps.exponent)
            .i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        let blocks = presented.rows * (presented.width / group);
        self.record_blocks(
            lane,
            "section_rms_rebase_adjoint",
            blocks,
            shape.block,
            shape.shared_octets,
            &mut params,
            "rms-rebase-adjoint",
        )
    }

    /// The adjoint of the contact at the queries.  Writes `dq` and the weight and differential
    /// scratch sections (`rows · heads` by `reach_max`), which the key and value adjoints read.
    #[allow(clippy::too_many_arguments)]

    pub fn record_contact_adjoint_queries(
        &self,
        lane: &Lane<'_, 'chart>,
        q: &ResidentSection<'chart>,
        k: &ResidentSection<'chart>,
        v: &ResidentSection<'chart>,
        differential: &ResidentSection<'chart>,
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        window: usize,
        terms: SeriesAperture,
        shape: &LawShape,
        dq: &ResidentSection<'chart>,
        weights: &ResidentSection<'chart>,
        differentials: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let reach_max = q.rows.min(window.max(1));
        if weights.rows() != q.rows * heads
            || weights.width() != reach_max
            || differentials.rows() != q.rows * heads
            || differentials.width() != reach_max
            || differential.rows != q.rows
            || differential.width != q.width
            || dq.rows() != q.rows
            || dq.width() != q.width
        {
            return Err(ResidentRefusal::RowsDisagree {
                operation: "contact-adjoint-queries",
                left: q.rows * q.width,
                right: dq.rows() * dq.width(),
            });
        }
        let mut params = Params::new();
        params
            .ptr(q.lo.device_ptr())
            .ptr(q.hi.device_ptr())
            .ptr(k.lo.device_ptr())
            .ptr(k.hi.device_ptr())
            .ptr(v.lo.device_ptr())
            .ptr(v.hi.device_ptr())
            .ptr(differential.lo.device_ptr())
            .ptr(differential.hi.device_ptr())
            .u32(q.rows as u32)
            .u32(heads as u32)
            .u32(kv_heads as u32)
            .u32(head_width as u32)
            .u32(window.max(1) as u32)
            .u32(reach_max as u32)
            .i32(dq.grain.0 as i32)
            .u32(terms.0)
            .ptr(dq.lo.device_ptr())
            .ptr(dq.hi.device_ptr())
            .ptr(weights.lo.device_ptr())
            .ptr(weights.hi.device_ptr())
            .ptr(differentials.lo.device_ptr())
            .ptr(differentials.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.slot + 4)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_contact_adjoint_queries",
            q.rows * heads,
            shape.block,
            shape.shared_octets,
            &mut params,
            "contact-adjoint-queries",
        )
    }

    /// The adjoint of the contact at the keys (`family = false`) or values (`family = true`), read
    /// from the scratch the query adjoint wrote.
    #[allow(clippy::too_many_arguments)]

    pub fn record_contact_adjoint_family(
        &self,
        lane: &Lane<'_, 'chart>,
        left: &ResidentSection<'chart>,
        scratch: &ResidentSection<'chart>,
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        window: usize,
        values: bool,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let reach_max = left.rows.min(window.max(1));
        if scratch.rows() != left.rows * heads
            || scratch.width() != reach_max
            || out.rows() != left.rows
            || out.width() != kv_heads * head_width
        {
            return Err(ResidentRefusal::RowsDisagree {
                operation: "contact-adjoint-family",
                left: left.rows * left.width,
                right: out.rows() * out.width(),
            });
        }
        let mut params = Params::new();
        params
            .ptr(left.lo.device_ptr())
            .ptr(left.hi.device_ptr())
            .ptr(scratch.lo.device_ptr())
            .ptr(scratch.hi.device_ptr())
            .u32(left.rows as u32)
            .u32(heads as u32)
            .u32(kv_heads as u32)
            .u32(head_width as u32)
            .u32(window.max(1) as u32)
            .u32(reach_max as u32)
            .i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            if values { "section_contact_adjoint_values" } else { "section_contact_adjoint_keys" },
            out.count(),
            &mut params,
            "contact-adjoint-family",
        )
    }

    #[allow(clippy::too_many_arguments)]
    /// The adjoint of the chronology: the same bands and positions, turned the other way.
    pub fn record_chronology_adjoint(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        heads: usize,
        head_width: usize,
        bands: &BandElements<'chart>,
        positions: &Positions<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(heads as u32)
            .u32(head_width as u32)
            .ptr(bands.cos_lo.device_ptr())
            .ptr(bands.cos_hi.device_ptr())
            .ptr(bands.sin_lo.device_ptr())
            .ptr(bands.sin_hi.device_ptr())
            .i32(bands.grain as i32)
            .ptr(positions.buffer.device_ptr())
            .i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_chronology_adjoint",
            input.rows * heads * (head_width / 2),
            &mut params,
            "chronology-adjoint",
        )
    }

    #[allow(clippy::too_many_arguments)]

    /// The carry of one population of words into a section of another shape with the same count:
    /// a reshape is a relabeling of the same population.
    pub fn record_carry_flat(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if input.count() != out.count() {
            return Err(ResidentRefusal::RowsDisagree {
                operation: "carry",
                left: input.count(),
                right: out.count(),
            });
        }
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(out.count() as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(lane, "section_carry", out.count(), &mut params, "carry")
    }
}
