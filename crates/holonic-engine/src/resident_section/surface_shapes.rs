use super::*;

impl<'chart> ResidentSurface<'chart> {
    // -----------------------------------------------------------------------------------------
    // the laws' shapes and prices — pure, before any launch
    // -----------------------------------------------------------------------------------------

    /// **The mouth reads its material**: entering codewords scaled by an exact dyadic and placed at
    /// the grain, admitted under the octaves THE ENTERING WORDS THEMSELVES occupy.
    ///
    /// Until 2026-08-19 this was `8 + scale octaves + grain + 8` — the significand's width, the
    /// scale's, the grain and eight more — computed without ever looking at a word. That is an
    /// authored level wearing a derivation: it is a bound on a *hypothetical* codeword of full
    /// significand at exponent zero, and it is simultaneously too generous for the real Gemma maps
    /// (whose exponents are negative) and too small for any population with a large exponent, which
    /// then refuses BOUND at the mouth and poisons every successor UPSTREAM. The H2 driver worked
    /// around it caller-side by closing the entering occurrence at
    /// `max(shape.needed, octaves computed from the words)`; that workaround is deleted and the
    /// reading is here, where the law is.
    ///
    /// The bound is the greatest, over the entering words, of the octaves of
    /// `significand · scale · 2^(ulp + scale exponent + F)` — the exact placement the kernel
    /// performs — plus one for the directed ceiling. A non-finite codeword contributes nothing to
    /// the bound; it is refused by the kernel as malformed. `[`Enter::bound_octaves`] states the same
    /// reading for the a-priori law and the two agree by construction.
    pub fn shape_enter(
        &self,
        rows: usize,
        width: usize,
        scale: Dyadic,
        grain: ResidentGrain,
        words: &[u16],
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "enter";
        let needed = entering_octaves(words, scale, grain);
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(count);
        work.entries_written = BigUint::from(2 * count);
        work.peak_bits = BigUint::from(u64::from(grain.0) + 16);
        work.cumulative_bits = BigUint::from(2 * count * (u64::from(grain.0) + 16));
        work.resident(2 * count);
        work.stepped();
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    /// Shape an entering BF16 population which is already resident and whose complete-population
    /// frame and widest aligned entry were returned by the exact BF16 mouth.  This is the same bound
    /// as [`shape_enter`](Self::shape_enter), expressed without copying the words back to the serial
    /// chart merely to read their magnitude.
    pub(crate) fn shape_enter_resident_bfloat16(
        &self,
        rows: usize,
        width: usize,
        scale: Dyadic,
        grain: ResidentGrain,
        frame_exponent: i32,
        entry_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "enter-resident-bfloat16";
        let shifted = i64::from(entry_octaves)
            + i64::from(scale.octaves())
            + i64::from(frame_exponent)
            + i64::from(scale.exponent)
            + i64::from(grain.0);
        let needed = u32::try_from(shifted + 1).unwrap_or(1).max(1);
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(count);
        work.entries_written = BigUint::from(2 * count);
        work.peak_bits = BigUint::from(u64::from(grain.0) + 16);
        work.cumulative_bits = BigUint::from(2 * count * (u64::from(grain.0) + 16));
        work.resident(2 * count);
        work.stepped();
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    pub(super) fn flat_shape(
        &self,
        operation: &'static str,
        rows: usize,
        width: usize,
        needed: u32,
        predicted: ExactWork,
        couplings: Vec<CouplingPlan>,
    ) -> Result<LawShape, ResidentRefusal> {
        let count = rows * width;
        let count32 = u32::try_from(count).map_err(|_| ResidentRefusal::GridAperture {
            operation,
            rows,
            width,
        })?;
        self.launch
            .grid_for(count32.max(1))
            .map_err(|_| ResidentRefusal::GridAperture {
                operation,
                rows,
                width,
            })?;
        Ok(LawShape {
            operation,
            rows,
            width,
            needed,
            predicted,
            couplings,
            launches: 2,
            shared_octets: 0,
            block: self.launch.block_x,
        })
    }

    /// The contraction through a mounted map: `out = section · mapᵀ`.
    pub fn shape_contract(
        &self,
        rows: usize,
        inner: usize,
        input_octaves: u32,
        map: &MountedReadout<'chart>,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "contract";
        if inner != map.dim() {
            return Err(ResidentRefusal::WidthDisagrees {
                operation: OPERATION,
                left: inner,
                right: map.dim(),
            });
        }
        let needed = input_octaves + map.entry_octaves() + ceil_log2(inner) + 1;
        Self::admit_octaves(OPERATION, needed)?;
        let out_width = map.rows();
        let mut work = ExactWork::predicted_product(
            rows,
            inner,
            out_width,
            u64::from(input_octaves.max(map.entry_octaves())),
        );
        work.entries_written = BigUint::from(2 * (rows * out_width) as u64);
        work.resident(2 * (rows * out_width) as u64);
        let peak = u64::from(input_octaves)
            + u64::from(map.entry_octaves())
            + u64::from(ceil_log2(inner))
            + 1;
        work.peak_bits = BigUint::from(peak);
        work.cumulative_bits = BigUint::from(2 * (rows * out_width) as u64 * peak);
        self.flat_shape(OPERATION, rows, out_width, needed, work, Vec::new())
    }

    /// The adjoint of the contraction over one aligned tile into the split-K partial standing:
    /// the returning differential `d` (`rows × tile_rows`) crossing the tile's rows transposed onto
    /// its `inner` columns, in `sub_splits` spans, each partial kept wide.  `admitted_node_octaves`
    /// is the bound every wide node is held to, derived from the complete population.
    pub fn shape_contract_transposed_partial(
        &self,
        rows: usize,
        tile_rows: usize,
        input_octaves: u32,
        map: &MountedReadout<'chart>,
        sub_splits: u32,
        admitted_node_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "contract-transposed-partial";
        if tile_rows != map.rows() || tile_rows == 0 || sub_splits == 0 {
            return Err(ResidentRefusal::WidthDisagrees {
                operation: OPERATION,
                left: tile_rows,
                right: map.rows(),
            });
        }
        let inner = map.dim();
        let needed = input_octaves + map.entry_octaves() + ceil_log2(tile_rows) + 1;
        Self::admit_octaves(OPERATION, needed)?;
        Self::admit_octaves(OPERATION, admitted_node_octaves)?;
        let mut work = ExactWork::predicted_product(
            rows,
            tile_rows,
            inner,
            u64::from(input_octaves.max(map.entry_octaves())),
        );
        work.entries_written = BigUint::from(4 * (rows * inner) as u64 * u64::from(sub_splits));
        work.resident(4 * (rows * inner) as u64 * u64::from(sub_splits));
        work.peak_bits = BigUint::from(u64::from(admitted_node_octaves));
        work.cumulative_bits =
            BigUint::from(4 * (rows * inner) as u64 * u64::from(admitted_node_octaves));
        self.flat_shape(
            OPERATION,
            rows,
            inner * sub_splits as usize,
            needed.max(admitted_node_octaves),
            work,
            Vec::new(),
        )
    }

    /// The adjoint factor of the hyperbolic tangent, `1 − t²`, at the grain: two words square,
    /// one subtraction, clamped to the unit.
    pub fn shape_one_minus_square(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
        grain: ResidentGrain,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "one-minus-square";
        let needed = (2 * input_octaves + 1).max(grain.0 + 2);
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(2 * count);
        work.added(2 * count);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(needed));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(grain.0 + 1));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, grain.0 + 1, work, Vec::new())
    }

    /// The derivative of `gelu_pytorch_tanh`: the forward's admission, since it forms the same
    /// square, cube, and series and then one more product family placed at the grain.
    pub fn shape_gelu_tanh_derivative(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
        grain: ResidentGrain,
        c1: Dyadic,
        c2: Dyadic,
        terms: SeriesAperture,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "gelu-tanh-derivative";
        let f = i64::from(grain.0);
        let oct = i64::from(input_octaves);
        let _ = (c1, c2);
        let needed = (2 * oct).max(oct + f + 2).max(2 * f + 4);
        let needed = u32::try_from(needed.max(0)).unwrap_or(u32::MAX);
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let series = 2 * (u64::from(terms.0) + 1);
        let mut work = ExactWork::nothing();
        work.multiplied(count * (20 + 2 * series));
        work.added(count * (12 + series));
        work.divided(count * (4 + series));
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(3 * input_octaves + 53));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves));
        work.dependency_span = BigUint::from(8u64 + u64::from(terms.0));
        // The derivative is bounded by a small constant in value; its admitted octaves at the
        // grain are the grain plus the hand and a little headroom.
        self.flat_shape(OPERATION, rows, width, needed.max(grain.0 + 3), work, Vec::new())
    }

    /// Place a `span`-wide face at column `at` of an `out_width`-wide zero section: the adjoint
    /// of the column selection.  One write per output coordinate, the bound the face's.
    pub fn shape_place_columns(
        &self,
        rows: usize,
        span: usize,
        out_width: usize,
        at: usize,
        input_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "place-columns";
        if span == 0 || at + span > out_width {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!("a face of {span} at column {at} does not fit a width of {out_width}"),
            });
        }
        let count = (rows * out_width) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves.max(1)));
        work.stepped();
        self.flat_shape(OPERATION, rows, out_width, input_octaves.max(1), work, Vec::new())
    }

    /// The adjoint of the RMS rebase: the forward's admission with the differential beside the
    /// presented carrier, and a second named barrier (the sum `Σ g x dy`) in the same block.
    pub fn shape_rms_rebase_adjoint(
        &self,
        rows: usize,
        width: usize,
        group: usize,
        presented_octaves: u32,
        differential_octaves: u32,
        gain: Option<&MountedReadout<'chart>>,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "rms-rebase-adjoint";
        let base = self.shape_rms_rebase(
            rows,
            width,
            group,
            presented_octaves.max(differential_octaves),
            gain,
        )?;
        let gain_octaves = gain.map(MountedReadout::entry_octaves).unwrap_or(0);
        let sums = presented_octaves + differential_octaves + gain_octaves + ceil_log2(group) + 2;
        let needed = base.needed.max(sums.min(Self::carrier_octaves()));
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = base.predicted;
        work.multiplied(count * 14);
        work.added(count * 6);
        work.divided(count * 2);
        Ok(LawShape {
            operation: OPERATION,
            rows,
            width,
            needed,
            predicted: work,
            couplings: base.couplings,
            launches: base.launches,
            shared_octets: base.shared_octets,
            block: base.block,
        })
    }

    /// The adjoint of the contact at the queries: the contact's own admission with the returning
    /// differential beside the values, one block per `(row, head)`, and shared storage for the
    /// two reductions plus the reach's weights and differentials.
    #[allow(clippy::too_many_arguments)]
    pub fn shape_contact_adjoint_queries(
        &self,
        rows: usize,
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        window: usize,
        terms: SeriesAperture,
        grain: ResidentGrain,
        q_octaves: u32,
        k_octaves: u32,
        v_octaves: u32,
        differential_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "contact-adjoint-queries";
        let reach = rows.min(window.max(1));
        let reach_sum: u64 = (0..rows).map(|at| (at + 1).min(window.max(1)) as u64).sum();
        let base = self.shape_contact_with_declared_reach(
            rows,
            heads * head_width,
            kv_heads * head_width,
            kv_heads * head_width,
            heads,
            kv_heads,
            head_width,
            reach,
            reach_sum,
            terms,
            grain,
            q_octaves,
            k_octaves,
            v_octaves.max(differential_octaves),
        )?;
        let f = grain.0;
        let needed = base
            .needed
            .max(differential_octaves + v_octaves + ceil_log2(head_width) + 1)
            .max(f + differential_octaves + v_octaves + ceil_log2(head_width) + ceil_log2(reach) + 2)
            .min(Self::carrier_octaves());
        Self::admit_octaves(OPERATION, needed)?;
        let shared = 2 * base.block * 16 + 4 * (reach as u32) * 16;
        if shared > self.max_shared_octets {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!(
                    "a block of {} with a reach of {reach} needs {shared} shared octets; the device admits {}",
                    base.block, self.max_shared_octets
                ),
            });
        }
        let mut work = base.predicted;
        let carried = reach_sum * heads as u64 * head_width as u64;
        work.multiplied(8 * carried);
        work.added(4 * carried);
        Ok(LawShape {
            operation: OPERATION,
            rows,
            width: heads * head_width,
            needed,
            predicted: work,
            couplings: base.couplings,
            launches: base.launches,
            shared_octets: shared,
            block: base.block,
        })
    }

    /// The adjoint of the contact at the keys or values: one thread per output coordinate over
    /// the rows and heads that reach it.
    #[allow(clippy::too_many_arguments)]
    pub fn shape_contact_adjoint_family(
        &self,
        rows: usize,
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        window: usize,
        grain: ResidentGrain,
        left_octaves: u32,
        right_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "contact-adjoint-family";
        let reach = rows.min(window.max(1));
        let group = heads / kv_heads.max(1);
        let needed = (left_octaves + right_octaves + ceil_log2(reach * group.max(1)) + 2)
            .min(Self::carrier_octaves())
            .max(grain.0 + 2);
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * kv_heads * head_width) as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(4 * count * reach as u64 * group as u64);
        work.added(2 * count * reach as u64 * group as u64);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(needed));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(grain.0 + 1));
        self.flat_shape(OPERATION, rows, kv_heads * head_width, needed, work, Vec::new())
    }

    /// The transposed midpoint seal of a returning differential into a deposit factor: one read
    /// pair and one write per coordinate, the bound the input's.
    pub fn shape_transpose_seal(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "transpose-seal";
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.added(count);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves + 1));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves.max(1)));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves.max(1), work, Vec::new())
    }

    /// The resident derived-rank contraction `h ↦ U(Vh)`.  Its rank is witnessed against the
    /// mounted junction extent, never used as padding or accepted as a caller aperture.  Rank one
    /// remains the original atom.  Higher rank is enacted as that exact atom population inside one
    /// resident front; no `rows × rank` i64 section is exposed between the two factors.
    pub fn shape_factorized_contract(
        &self,
        rows: usize,
        inner: usize,
        input_octaves: u32,
        u: &MountedReadout<'chart>,
        v: &MountedReadout<'chart>,
        rank: usize,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "factorized-contract";
        if rank == 0 {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: "rank zero is a no-change return and has no resident contraction".to_owned(),
            });
        }
        if u.dim() != rank || v.rows() != rank || v.dim() != inner {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!(
                    "native factors require u=[V,R], v=[R,H] with derived R={rank}, got u=[{},{}], v=[{},{}]",
                    u.rows(),
                    u.dim(),
                    v.rows(),
                    v.dim()
                ),
            });
        }
        // Admit the wide v reduction and the wide u product directly.  Calling shape_contract
        // here would smuggle the retired i64 scalar-section claim into the receipt even though
        // this law's internal junction is shared wide storage only.
        let add = |left: u32, right: u32| -> Result<u32, ResidentRefusal> {
            left.checked_add(right)
                .ok_or(ResidentRefusal::CarrierRange {
                    operation: OPERATION,
                    needed: u32::MAX,
                    admitted: Self::carrier_octaves(),
                })
        };
        // Positive map exponents are left shifts in the wide helpers.  Negative exponents may
        // narrow a later face, but cannot erase the earlier carrier obligation, so every stage is
        // admitted independently in causal order.
        let raw_v = add(
            add(add(input_octaves, v.entry_octaves())?, ceil_log2(inner))?,
            1,
        )?;
        let scalar_v = add(raw_v, v.exponent().max(0) as u32)?;
        let product_u = add(add(scalar_v, u.entry_octaves())?, 1)?;
        let final_atom = add(product_u, u.exponent().max(0) as u32)?;
        let final_u = add(final_atom, ceil_log2(rank))?;
        for stage in [raw_v, scalar_v, product_u, final_atom, final_u] {
            Self::admit_octaves(OPERATION, stage)?;
        }
        let needed = final_u;
        let out_width = u.rows();
        let inner_power = inner.checked_next_power_of_two().unwrap_or(usize::MAX);
        let inner_power_u32 = u32::try_from(inner_power).unwrap_or(u32::MAX);
        let block = self
            .reduction_block
            .min(inner_power_u32)
            .max(self.launch.warp);
        let shared_u64 = 2u64
            .saturating_mul(u64::from(block).saturating_add(rank as u64))
            .saturating_mul(16);
        let shared = u32::try_from(shared_u64).map_err(|_| ResidentRefusal::Declaration {
            operation: OPERATION,
            what: format!("the reduction block {block} has no representable shared extent"),
        })?;
        if shared > self.max_shared_octets {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!(
                    "a reduction block of {block} needs {shared} shared octets; the device admits {}",
                    self.max_shared_octets
                ),
            });
        }
        if rows > self.launch.max_grid_x as usize {
            return Err(ResidentRefusal::GridAperture {
                operation: OPERATION,
                rows,
                width: out_width,
            });
        }
        let count = (rows * out_width) as u64;
        // Retain the two constitutive work legs and their wide internal materialization in the
        // receipt, while the graph allocates only the final i64 section.
        let mut first_work = ExactWork::predicted_product(
            rows,
            inner,
            rank,
            u64::from(input_octaves.max(v.entry_octaves())),
        );
        first_work.entries_written = BigUint::from(2 * rows as u64 * rank as u64);
        first_work.resident(2 * rows as u64 * rank as u64);
        first_work.peak_bits = BigUint::from(u64::from(scalar_v));
        first_work.cumulative_bits =
            BigUint::from(2 * rows as u64 * rank as u64 * u64::from(scalar_v));
        let mut second_work = ExactWork::predicted_product(
            rows,
            rank,
            out_width,
            u64::from(scalar_v.max(u.entry_octaves())),
        );
        second_work.entries_written = BigUint::from(2 * count);
        second_work.resident(2 * count);
        second_work.peak_bits = BigUint::from(u64::from(final_u));
        second_work.cumulative_bits = BigUint::from(2 * count * u64::from(final_u));
        let mut work = first_work.then(&second_work);
        // The wide reduction has a logarithmic block span in this realization.  Preserve the
        // constitutive counts and widths while returning the enacted dependency span.
        work.dependency_span = work
            .dependency_span
            .max(BigUint::from(u64::from(ceil_log2(block as usize) + 1)));
        let coupling = CouplingPlan {
            coupling: "derived-rank junction: exact shared-wide rank-one atoms, then one i64 output front",
            kernel: "section_factorized_contract",
            extent: (inner as u64).saturating_mul(rank as u64),
            block,
            predicted: work.clone(),
        };
        Ok(LawShape {
            operation: OPERATION,
            rows,
            width: out_width,
            needed,
            predicted: work,
            couplings: vec![coupling],
            launches: 2,
            shared_octets: shared,
            block,
        })
    }

    /// The RMS rebase over runs of `group`: `x · (mean(x²) + eps)^{-1/2} · g`. The quadratic
    /// capacity is a named barrier realized as a resident block reduction.
    pub fn shape_rms_rebase(
        &self,
        rows: usize,
        width: usize,
        group: usize,
        input_octaves: u32,
        gain: Option<&MountedReadout<'chart>>,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "rms-rebase";
        if group == 0 || width % group != 0 {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!("a group of {group} does not tile a width of {width}"),
            });
        }
        if let Some(gain) = gain {
            if gain.rows() * gain.dim() != group {
                return Err(ResidentRefusal::WidthDisagrees {
                    operation: OPERATION,
                    left: group,
                    right: gain.rows() * gain.dim(),
                });
            }
        }
        let gain_octaves = gain.map(MountedReadout::entry_octaves).unwrap_or(0);
        let oct = input_octaves;
        // The squares are summed at 2^-2(F − s) with s the least shift that fits the wide carrier;
        // the kernel derives s from the group's own census, so here s is bounded from the a-priori
        // octaves and the product x·g must fit the wide carrier.
        let squares = 2 * oct + ceil_log2(group) + 1;
        let needed = squares
            .min(Self::carrier_octaves())
            .max(oct + gain_octaves + 1);
        Self::admit_octaves(OPERATION, needed)?;
        let block = self
            .reduction_block
            .min(group.next_power_of_two() as u32)
            .max(self.launch.warp);
        let shared = 2 * block * 16 + block * 4;
        if shared > self.max_shared_octets {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!(
                    "a block of {block} needs {shared} shared octets; the device admits {}",
                    self.max_shared_octets
                ),
            });
        }
        let blocks = rows * (width / group);
        if blocks > self.launch.max_grid_x as usize {
            return Err(ResidentRefusal::GridAperture {
                operation: OPERATION,
                rows,
                width,
            });
        }
        let count = (rows * width) as u64;
        let groups = blocks as u64;
        let mut work = ExactWork::nothing();
        // the octave census, the squares, the reductions, the radical, the rebase, the gain
        work.multiplied(2 * count + 4 * count + count);
        work.added(2 * count + 2 * count + count);
        work.divided(groups * (64 + 2));
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        let peak = 2 * u64::from(oct) + u64::from(ceil_log2(group)) + 1;
        work.peak_bits = BigUint::from(
            peak.min(u64::from(Self::carrier_octaves()))
                .max(u64::from(oct + gain_octaves + 10)),
        );
        work.cumulative_bits =
            BigUint::from(2 * count * (u64::from(oct) + u64::from(gain_octaves)));
        work.dependency_span = BigUint::from(2 * u64::from(ceil_log2(group)) + 3);
        let mut reduction = ExactWork::nothing();
        reduction.added(2 * count);
        reduction.divided(groups * 66);
        reduction.dependency_span = BigUint::from(u64::from(ceil_log2(group)) + 2);
        let couplings = vec![CouplingPlan {
            coupling: "the quadratic capacity over the group, and the group's own octave census",
            kernel: "section_rms_rebase",
            extent: group as u64,
            block,
            predicted: reduction,
        }];
        Ok(LawShape {
            operation: OPERATION,
            rows,
            width,
            needed,
            predicted: work,
            couplings,
            launches: 2,
            shared_octets: shared,
            block,
        })
    }

    /// The chronology: every head's pair `(x[b], x[b + D/2])` turned by the band element raised to
    /// the row's integer position.
    pub fn shape_chronology(
        &self,
        rows: usize,
        width: usize,
        heads: usize,
        head_width: usize,
        input_octaves: u32,
        bands: &BandElements<'chart>,
        positions: &Positions<'chart>,
        max_position: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "chronology";
        if width != heads * head_width {
            return Err(ResidentRefusal::WidthDisagrees {
                operation: OPERATION,
                left: width,
                right: heads * head_width,
            });
        }
        if bands.bands != head_width / 2 {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!(
                    "{} band elements for a head width of {head_width}",
                    bands.bands
                ),
            });
        }
        if positions.rows != rows {
            return Err(ResidentRefusal::RowsDisagree {
                operation: OPERATION,
                left: rows,
                right: positions.rows,
            });
        }
        let needed = (input_octaves + bands.grain + 1).max(2 * bands.grain + 2);
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * heads * (head_width / 2)) as u64;
        let powering = u64::from(ceil_log2(max_position as usize + 1)) * 2 * 16;
        let mut work = ExactWork::nothing();
        work.multiplied(count * (powering + 16));
        work.added(count * (powering / 2 + 6));
        work.entries_written = BigUint::from(2 * (rows * width) as u64);
        work.resident(2 * (rows * width) as u64);
        work.peak_bits = BigUint::from(u64::from(input_octaves + bands.grain + 1));
        work.cumulative_bits =
            BigUint::from(2 * (rows * width) as u64 * u64::from(input_octaves + 1));
        work.dependency_span = BigUint::from(u64::from(ceil_log2(max_position as usize + 1)) + 1);
        // The launch is flat over (row, head, band).
        let threads = rows * heads * (head_width / 2);
        let count32 = u32::try_from(threads).map_err(|_| ResidentRefusal::GridAperture {
            operation: OPERATION,
            rows,
            width,
        })?;
        self.launch
            .grid_for(count32.max(1))
            .map_err(|_| ResidentRefusal::GridAperture {
                operation: OPERATION,
                rows,
                width,
            })?;
        Ok(LawShape {
            operation: OPERATION,
            rows,
            width,
            needed,
            predicted: work,
            couplings: Vec::new(),
            launches: 2,
            shared_octets: 0,
            block: self.launch.block_x,
        })
    }

    /// The contact and carried construction over `(q, k, v)`, sliding causal window.
    #[allow(clippy::too_many_arguments)]
    pub fn shape_contact(
        &self,
        rows: usize,
        q_width: usize,
        k_width: usize,
        v_width: usize,
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        window: usize,
        terms: SeriesAperture,
        grain: ResidentGrain,
        q_octaves: u32,
        k_octaves: u32,
        v_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        let reach = rows.min(window.max(1));
        let reach_sum = (0..rows).map(|at| (at + 1).min(window.max(1)) as u64).sum();
        self.shape_contact_with_declared_reach(
            rows, q_width, k_width, v_width, heads, kv_heads, head_width, reach, reach_sum, terms,
            grain, q_octaves, k_octaves, v_octaves,
        )
    }

    /// The same exact contact shape under a receiver-founded maximum causal reach. A partitioned
    /// contact law derives this reach from its addressed boundaries; using the total flat row
    /// population would charge impossible cross-partition paths which the kernel never enacts.
    #[allow(clippy::too_many_arguments)]
    pub fn shape_contact_with_declared_reach(
        &self,
        rows: usize,
        q_width: usize,
        k_width: usize,
        v_width: usize,
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        reach: usize,
        reach_sum: u64,
        terms: SeriesAperture,
        grain: ResidentGrain,
        q_octaves: u32,
        k_octaves: u32,
        v_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "contact";
        if q_width != heads * head_width {
            return Err(ResidentRefusal::WidthDisagrees {
                operation: OPERATION,
                left: q_width,
                right: heads * head_width,
            });
        }
        if k_width != kv_heads * head_width || v_width != kv_heads * head_width {
            return Err(ResidentRefusal::WidthDisagrees {
                operation: OPERATION,
                left: k_width.max(v_width),
                right: kv_heads * head_width,
            });
        }
        if kv_heads == 0 || heads % kv_heads != 0 {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!("{heads} heads over {kv_heads} families"),
            });
        }
        let f = grain.0;
        let reach = rows.min(reach.max(1));
        // The bracket sum is SELF-SCALED on the card from the block's own widest octave, so its
        // term is bounded by the carrier whatever the words; the carried construction and the
        // series are not, and decide the admission.
        let needed = (2 * q_octaves.max(k_octaves) + ceil_log2(head_width) + 1)
            .min(Self::carrier_octaves())
            .max(f + 1 + v_octaves + ceil_log2(reach) + 1)
            .max(2 * f + 4);
        Self::admit_octaves(OPERATION, needed)?;
        let block = self
            .reduction_block
            .min(head_width.max(reach).next_power_of_two() as u32)
            .max(self.launch.warp);
        // Two exact scratch rows, each one block wide. The reach is traversed in these tiles and
        // therefore does not become an authored context ceiling or a shared-memory allocation.
        let shared = 2 * block * 16;
        if shared > self.max_shared_octets {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!(
                    "a block of {block} needs {shared} shared octets; the device admits {}",
                    self.max_shared_octets
                ),
            });
        }
        if rows * heads > self.launch.max_grid_x as usize {
            return Err(ResidentRefusal::GridAperture {
                operation: OPERATION,
                rows,
                width: q_width,
            });
        }
        let brackets = 2 * reach_sum * heads as u64 * head_width as u64;
        let series = reach_sum * heads as u64 * 2 * (u64::from(terms.0) + 1);
        let carried = reach_sum * heads as u64 * head_width as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(4 * brackets + 2 * series + 4 * carried);
        work.added(2 * brackets + 2 * series + 2 * carried);
        work.divided(2 * series + 2 * (rows * heads * head_width) as u64);
        work.entries_written = BigUint::from(2 * (rows * heads * head_width) as u64);
        work.resident(2 * (rows * heads * head_width) as u64 + 2 * u64::from(block));
        let peak = (2 * q_octaves.max(k_octaves) + ceil_log2(head_width) + 1).max(v_octaves + 40);
        work.peak_bits = BigUint::from(u64::from(peak));
        work.cumulative_bits =
            BigUint::from(2 * (rows * heads * head_width) as u64 * u64::from(v_octaves + 1));
        work.dependency_span = BigUint::from(5u64 + u64::from(terms.0));
        let coupling = |name: &'static str, extent: u64| {
            let mut reduction = ExactWork::nothing();
            reduction.added(reach_sum * heads as u64);
            reduction.dependency_span = BigUint::from(u64::from(ceil_log2(reach)) + 1);
            CouplingPlan {
                coupling: name,
                kernel: "section_contact",
                extent,
                block,
                predicted: reduction,
            }
        };
        let couplings = vec![
            coupling(
                "the null: greatest upper bracket over the reach",
                reach as u64,
            ),
            coupling(
                "the partition function: sum of certified weights over the reach",
                reach as u64,
            ),
            coupling(
                "the hull: least and greatest carried coordinate over the reach",
                reach as u64,
            ),
        ];
        Ok(LawShape {
            operation: OPERATION,
            rows,
            width: heads * head_width,
            needed,
            predicted: work,
            couplings,
            launches: 2,
            shared_octets: shared,
            block,
        })
    }

    /// `½ x (1 + tanh(c1 (x + c2 x³)))` with the source's `binary64` constants as exact dyadics.
    pub fn shape_gelu_tanh(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
        grain: ResidentGrain,
        c1: Dyadic,
        c2: Dyadic,
        terms: SeriesAperture,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "gelu-tanh";
        let f = i64::from(grain.0);
        let oct = i64::from(input_octaves);
        // The cube and both dyadic products are SELF-SCALED on the card; the square (two words),
        // the final product with `1 + tanh`, and the series decide the admission.
        let _ = (c1, c2);
        let needed = (2 * oct).max(oct + f + 2).max(2 * f + 4);
        let needed = u32::try_from(needed.max(0)).unwrap_or(u32::MAX);
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let series = 2 * (u64::from(terms.0) + 1);
        let mut work = ExactWork::nothing();
        work.multiplied(count * (12 + 2 * series));
        work.added(count * (8 + series));
        work.divided(count * (4 + series));
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(3 * input_octaves + 53));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves));
        work.dependency_span = BigUint::from(6u64 + u64::from(terms.0));
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    /// Certified elementwise hyperbolic tangent at the section's own grain.
    pub fn shape_tanh(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
        grain: ResidentGrain,
        terms: SeriesAperture,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "tanh";
        let needed = input_octaves.max(2 * grain.0 + 4);
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let series = 2 * (u64::from(terms.0) + 1);
        let mut work = ExactWork::nothing();
        work.multiplied(count * 2 * series);
        work.added(count * series);
        work.divided(count * (4 + series));
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(needed));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(grain.0 + 2));
        work.dependency_span = BigUint::from(2u64 + u64::from(terms.0));
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    /// The pointwise product of two standings.
    pub fn shape_hadamard(
        &self,
        rows: usize,
        width: usize,
        a_octaves: u32,
        b_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "hadamard";
        // Two magnitudes below 2^a and 2^b multiply below 2^(a+b).
        let needed = a_octaves + b_octaves;
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(4 * count);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(a_octaves + b_octaves));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(a_octaves + b_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    /// The re-entry: a retained standing and a returned current, joined.
    pub fn shape_re_entry(
        &self,
        rows: usize,
        width: usize,
        a_octaves: u32,
        b_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "re-entry";
        let needed = a_octaves.max(b_octaves) + 1;
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.added(2 * count);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(a_octaves.max(b_octaves) + 1));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(a_octaves.max(b_octaves) + 1));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    /// The product with an enclosed constant carried as its certified enclosure.
    pub fn shape_scale(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
        by: DyadicEnclosure,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "scale";
        let needed = input_octaves + by.octaves() + 1;
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(4 * count);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves + by.octaves()));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    /// Product with one exact aligned resident coefficient.
    pub fn shape_scale_by_aligned(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
        coefficient: &MountedReadout<'chart>,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "scale-by-aligned";
        if coefficient.rows() * coefficient.dim() != 1 {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: "the coefficient population is not scalar".to_owned(),
            });
        }
        let needed = input_octaves + coefficient.entry_octaves() + 1;
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(2 * count);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(needed));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(needed));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    /// One addressed contiguous coordinate face from every row, retaining the input grain and
    /// octave bound exactly.
    pub fn shape_select_columns(
        &self,
        rows: usize,
        width: usize,
        from: usize,
        span: usize,
        input_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "select-columns";
        if span == 0 || from.checked_add(span).is_none_or(|end| end > width) {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!(
                    "face {from}..{} leaves width {width}",
                    from.saturating_add(span)
                ),
            });
        }
        Self::admit_octaves(OPERATION, input_octaves)?;
        let count = (rows * span) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, span, input_octaves, work, Vec::new())
    }

    /// The matched-sibling intervention: a declared span of columns withdrawn, out of place.
    pub fn shape_withdraw_columns(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
        from: usize,
        span: usize,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "withdraw-columns";
        if from + span > width {
            return Err(ResidentRefusal::WidthDisagrees {
                operation: OPERATION,
                left: from + span,
                right: width,
            });
        }
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())
    }

    /// The intervention withdrawing rows `[from, from + span)`.
    pub fn shape_withdraw_rows(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
        from: usize,
        span: usize,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "withdraw-rows";
        if from + span > rows {
            return Err(ResidentRefusal::RowsDisagree {
                operation: OPERATION,
                left: from + span,
                right: rows,
            });
        }
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())
    }

    /// The receiver-directed restriction of a non-empty section to its terminal row.  This is an
    /// exact factorization of every future consequence which reads only that row: unlike
    /// [`Self::shape_withdraw_rows`], the unrequested rows are not allocated as zeroes.
    pub fn shape_terminal_row(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "terminal-row";
        if rows == 0 {
            return Err(ResidentRefusal::RowsDisagree {
                operation: OPERATION,
                left: rows,
                right: 1,
            });
        }
        let count = width as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, 1, width, input_octaves, work, vec![])
    }

    /// The exact terminal row of every non-empty addressed block. The predecessor section is
    /// retained as the reconstruction fibre; only the receiver-visible causal endpoints are
    /// allocated.
    pub fn shape_partition_terminal_rows(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
        boundaries: &[u32],
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "partition-terminal-rows";
        if boundaries.len() < 2
            || boundaries[0] != 0
            || boundaries.last().copied() != Some(rows as u32)
            || boundaries.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!("{rows} source rows with boundaries {boundaries:?}"),
            });
        }
        let groups = boundaries.len() - 1;
        let count = (groups * width) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, groups, width, input_octaves, work, vec![])
    }

    /// The exact directed mean of every non-empty row block declared by `boundaries`.  The
    /// predecessor remains the complete reconstruction fibre; this shape allocates only the
    /// receiver's block means.
    pub fn shape_partition_mean(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
        boundaries: &[u32],
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "partition-mean";
        if boundaries.len() < 2
            || boundaries[0] != 0
            || boundaries.last().copied() != Some(rows as u32)
            || boundaries.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!("{rows} source rows with boundaries {boundaries:?}"),
            });
        }
        let groups = boundaries.len() - 1;
        let longest = boundaries
            .windows(2)
            .map(|pair| pair[1] - pair[0])
            .max()
            .unwrap_or(1);
        let intermediate = input_octaves.saturating_add(ceil_log2(longest as usize));
        Self::admit_octaves(OPERATION, intermediate)?;
        let source_count = (rows * width) as u64;
        let output_count = (groups * width) as u64;
        let mut work = ExactWork::nothing();
        work.added(2 * source_count.saturating_sub(output_count));
        work.divided(2 * output_count);
        work.entries_written = BigUint::from(2 * output_count);
        work.resident(2 * output_count);
        work.peak_bits = BigUint::from(u64::from(intermediate));
        work.cumulative_bits = BigUint::from(2 * output_count * u64::from(input_octaves));
        work.dependency_span = BigUint::from(u64::from(ceil_log2(longest as usize)) + 1);
        self.flat_shape(
            OPERATION,
            groups,
            width,
            input_octaves,
            work,
            vec![CouplingPlan {
                coupling: "each declared block integrates every source row before its directed mean",
                kernel: "section_partition_mean",
                extent: rows as u64,
                block: self.launch.block_x,
                predicted: ExactWork::nothing(),
            }],
        )
    }

    /// The intervention permuting the column blocks of `block` by a declared permutation.
    pub fn shape_permute_columns(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
        block: usize,
        permutation: &[usize],
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "permute-columns";
        if block == 0 || width % block != 0 || permutation.len() != width / block {
            return Err(ResidentRefusal::WidthDisagrees {
                operation: OPERATION,
                left: permutation.len() * block,
                right: width,
            });
        }
        let mut seen = vec![false; permutation.len()];
        for p in permutation {
            if *p >= permutation.len() || seen[*p] {
                return Err(ResidentRefusal::Declaration {
                    operation: OPERATION,
                    what: format!(
                        "{permutation:?} is not a permutation of {} blocks",
                        permutation.len()
                    ),
                });
            }
            seen[*p] = true;
        }
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())
    }

    /// **A control, unsound by construction**: the enclosure collapsed to a midpoint at this site.
    pub fn shape_collapse_control(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "collapse-control";
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.added(count);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())
    }

    /// **The midpoint quotient, fused with its own census.** One node instead of two, and no section
    /// of its own: the predecessor's words are rewritten in place. The predicted price is the
    /// collapse's, and `launches` is ONE — the receipt's apparatus prediction moves with the fusion
    /// rather than describing the unfused pair.
    pub fn shape_midpoint_seal(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "midpoint-quotient(fused seal)";
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.added(count);
        work.entries_written = BigUint::from(2 * count);
        // The census this kernel folds is the collapsed section's: an octave max and a bound or.
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.stepped();
        let mut shape = self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())?;
        shape.launches = 1;
        Ok(shape)
    }

    /// The carry of a resident standing into this passage: one read and one write per coordinate,
    /// no arithmetic, the octave bound unchanged.
    /// **The receiver return**: per emitted row, the null, the partition of the certified
    /// exponential over the complete face, and per coordinate the differential of the normalized
    /// exponential receiver against the next occurrence, its adjoint through the terminal
    /// reactions, and the deposit word. One block per row; the two reductions are named barriers
    /// realized in shared storage. The deposit is at most one unit at the grain, so its bound is
    /// the grain plus the directed hand.
    pub fn shape_receiver_return(
        &self,
        rows: usize,
        width: usize,
        tile_width: usize,
        grain: ResidentGrain,
        terms: SeriesAperture,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "receiver-return";
        if rows == 0 || tile_width == 0 || width % tile_width != 0 {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!(
                    "the face is {rows} x {width} in tiles of {tile_width}; the tiles must cover it exactly"
                ),
            });
        }
        let needed = grain.0 + 2;
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let series = 2 * (u64::from(terms.0) + 1);
        let mut work = ExactWork::nothing();
        work.multiplied(count * (4 * series + 8));
        work.added(count * (2 * series + 8));
        work.divided(count * (2 * series + 2));
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(2 * grain.0 + 2));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(grain.0 + 2));
        work.dependency_span = BigUint::from(2u64 + u64::from(terms.0));
        let block = self.reduction_block.max(self.launch.warp);
        let shared_u64 = 2u64.saturating_mul(u64::from(block)).saturating_mul(16);
        let shared = u32::try_from(shared_u64).map_err(|_| ResidentRefusal::Declaration {
            operation: OPERATION,
            what: format!("the reduction block {block} has no representable shared extent"),
        })?;
        if shared > self.max_shared_octets {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!(
                    "a reduction block of {block} needs {shared} shared octets; the device admits {}",
                    self.max_shared_octets
                ),
            });
        }
        if rows > self.launch.max_grid_x as usize {
            return Err(ResidentRefusal::GridAperture {
                operation: OPERATION,
                rows,
                width,
            });
        }
        Ok(LawShape {
            operation: OPERATION,
            rows,
            width,
            needed,
            predicted: work,
            couplings: Vec::new(),
            launches: 2,
            shared_octets: shared,
            block,
        })
    }

    pub fn shape_carry(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "carry";
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves.max(1)));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())
    }
}
