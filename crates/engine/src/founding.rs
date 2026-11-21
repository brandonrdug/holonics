//! **Founding a part at zero: growth that reads every face as before.**
//!
//! a grown part (lanes, contacts, letters, copies, carry circles, triads, the opening, the junction, the mark, the loud face, the
//! depth rings) is founded so that every face of the source reads bit for bit before deposition moves it
//!
//! Kind: once a growth, on the host. Kernels: none.
//! Lean: `HNN/CarryGate` (the carry circle founded as a turn with friction).
//! Atlas: `contact.carried-product`, `contact.carry-coupling-through-the-leak`, `contact.carry-gate-turn-and-friction`,
//! `contact.triad-manley-rowe-gauge`, `tower.face-loud-sharpness`, `tower.field-growth-by-copies`, `tower.field-mark`, `tower.field-opening-lift`,
//! `tower.field-scan-gate-once-a-site`, `tower.field-tick-return`.
//! Records: `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`, `2026-11-11_RAISED_RATES_BUY…`. The derivations' history is in the records; the items below keep
//! their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

impl Constitution {

    pub(crate) fn with_theta(declaration: Declaration, theta: Vec<i32>) -> Self {
        let layout = Loci::new(&declaration);
        let pi = half_turn(MOVE_BITS + 16);
        let rings: Vec<(usize, Vec<(i64, i64)>)> = ring_periods(declaration.turned_slots(), declaration.reach).into_iter().map(|n| (n, (0..n.min(declaration.reach)).map(|r| ring_phasor(r, n, pi)).collect())).collect();
        let exponential = Exponential::new(FACE_BITS);
        let decays = rings.iter().map(|&(n, _)| (0..declaration.reach).map(|d| skin_decay(d, n, pi, &exponential)).collect()).collect();
        Self { declaration, theta, layout, rings, decays, exponential, fine: Exponential::new(MATERIAL_BITS), pi, scale: None, per_blank_clock: false, bare_stretch: false, mirror_strength: None, lock_carry: None, ruler_leak: None, ruler_far: 0, ruler_level: 0, mark: None }
    }

    /// [definition; agent-inferred, November 6] **A field's last `depth` turned ring sets become depth rings**
    /// ([`Declaration::depth`]): their increments founded at zero (the rings plain, each a still head's reading with
    /// frames that can turn), every other parameter kept; a turned head that becomes a ring gives up its clock and its moment.
    pub fn with_depth(mut self, depth: usize) -> Result<Self> {
        let declaration = Declaration { depth, ..self.declaration };
        declaration.admit()?;
        let width = declaration.alphabet + 1;
        for (p, h) in (0..declaration.heads).filter(|&h| declaration.carries_moment(h)).enumerate() {
            if declaration.is_depth(h) && !self.declaration.is_depth(h) {
                let base = self.layout.pace + p * width;
                for v in &mut self.theta[base..base + width] {
                    *v = 0;
                }
            }
        }
        self.declaration = declaration;
        Ok(self)
    }
}

impl Constitution {
    /// The key draws a growth by `factor` reads, four bytes a draw: `f − 1` a part of each row
    /// copy's entry of every family the founding opens away from zero (the charts and the pair
    /// drives).
    pub fn growth_draws(&self, factor: usize) -> usize {
        self.declaration.growth_draws(factor)
    }

    /// [definition; agent-inferred, November 1; November 3, §16.29] **The field widened by `factor`**, by the tower's
    /// growth law (`hnn::tower::growth`): every face coordinate gets `f` equal copies (the encoding and every face bias
    /// repeated), every contact repeated, and every matrix entry that reads the face split over its `f` column copies
    /// into parts that sum to it; a matrix that writes the face (the current's return, the moment's chart, the pair's
    /// return) has its rows repeated over the face copies, the current's and the moment's columns whole. The heads
    /// are kept: their charts' rows, biases, moments, clocks and temperatures are the old ones. A part's zero-sum
    /// difference is the grown founding's draw at its scale (`√(3/fD)` for the charts and pair drives, read from
    /// `keys` four bytes a draw); the families founded at zero (the returns and the readout) split evenly. Every sum
    /// the forward forms is then the old sum, so the grown field reads the old faces exactly, and the copies part
    /// under learning.
    ///
    /// Returns the grown field and, for each grown entry, the old entry it carries and whether its
    /// covector is divided among the copies (every family but the readout's).
    pub fn grown(&self, factor: usize, keys: &[u8]) -> Result<(Self, Vec<(usize, bool)>)> {
        if factor < 2 {
            return refuse("a growth makes at least two copies");
        }
        if self.scale.is_some() {
            return refuse("a tower grows by its levels' lanes, not by copies (the tower record, D2)");
        }
        if self.declaration.carry > 0 {
            return refuse("a field with carry circles grows by lanes, not by copies (a copy would split a circle's scan)");
        }
        if self.declaration.triads > 0 {
            // [theory, November 12, the triad record §4] The triads are founded last; a copy of their charts and return is not built.
            return refuse("a field with triads grows by no copies (the triads are founded last; their copies are not built)");
        }
        let old = self.declaration;
        let d = old.grown(factor)?;
        let layout = Loci::new(&d);
        let (ol, f) = (&self.layout, factor);
        let (dw, m, fc, a) = (old.width, old.complex(), old.contacts, old.alphabet);
        let dw2 = d.width;
        let mut new = vec![0i32; layout.len];
        let mut from = vec![(0usize, true); layout.len];
        let mut cursor = 0usize;
        let mut draw = |scale: Option<(u128, u128)>| -> Result<i128> {
            let Some((num, den)) = scale else { return Ok(0) };
            let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the growth draws"))?;
            cursor += 4;
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            Ok((k * ((num << MATERIAL_BITS) / den) as i128) >> 31)
        };
        // A matrix of `rows × cols` (old), its rows mapped by `row_of(b, r)` over `row_copies`
        // copies and each column's `f` parts placed at `col_of(c, j)` in a row of `new_cols`.
        let mut split = |old_at: usize, new_at: usize, rows: usize, cols: usize, row_copies: usize, row_of: &dyn Fn(usize, usize) -> usize, new_cols: usize, col_of: &dyn Fn(usize, usize) -> usize, scale: Option<(u128, u128)>, divided: bool| -> Result<()> {
            for b in 0..row_copies {
                for r in 0..rows {
                    let nr = row_of(b, r);
                    for j in 0..cols {
                        let v = self.theta[old_at + r * cols + j] as i128;
                        let (q, rem) = (v.div_euclid(f as i128), v.rem_euclid(f as i128));
                        let mut spent = 0i128;
                        for c in 0..f {
                            let delta = if c + 1 < f { draw(scale)? } else { -spent };
                            spent += delta;
                            let at = new_at + nr * new_cols + col_of(c, j);
                            new[at] = fit32(q + i128::from((c as i128) < rem) + delta, "a grown part outgrew its 32-bit carrier")?;
                            from[at] = (old_at + r * cols + j, divided);
                        }
                    }
                }
            }
            Ok(())
        };
        let scale = Some(chart_scale(dw2));
        // Index maps: a face coordinate's copy `c` at `cD + j`; a contact's at `bf + e`.
        let face = |c: usize, j: usize| c * dw + j;
        // A contact is a complex pair (`e`, `f/2 + e`, §15.1): copy `c` of its real part at `c f/2 + e`,
        // of its imaginary part at `f'/2 + c f/2 + e`, so every copy keeps its pair.
        let contact = |c: usize, e: usize| if e < fc / 2 { c * (fc / 2) + e } else { f * fc / 2 + c * (fc / 2) + e - fc / 2 };
        let kept = |_: usize, r: usize| r;
        // [§16.29] A head's chart reads every face copy (its row kept, each entry split over its column's copies), and the
        // current returns whole to every face copy (each row repeated, below): every copy of a coordinate stays its source.
        split(ol.q, layout.q, 2 * m, dw, 1, &kept, dw2, &face, scale, false)?;
        split(ol.v, layout.v, 2 * m, dw, 1, &kept, dw2, &face, scale, false)?;
        split(ol.probe, layout.probe, 2 * m, dw, 1, &kept, dw2, &face, scale, false)?;
        split(ol.a, layout.a, fc, dw, f, &contact, dw2, &face, scale, true)?;
        split(ol.b, layout.b, fc, dw, f, &contact, dw2, &face, scale, true)?;
        split(ol.w, layout.w, dw, fc, f, &face, f * fc, &contact, None, true)?;
        // The current's return and the moment's chart into the face (§16.22) write the face: each row repeated over the
        // face copies, its columns (the heads' modes, kept) whole, so the grown current and opening are the old ones on
        // every copy; a copy's covector arrives divided, as the face's does.
        for (old_at, new_at) in [(ol.out, layout.out), (ol.moment_face, layout.moment_face)] {
            for b in 0..f {
                for r in 0..dw {
                    for k in 0..2 * m {
                        let at = new_at + face(b, r) * 2 * m + k;
                        new[at] = self.theta[old_at + r * 2 * m + k];
                        from[at] = (old_at + r * 2 * m + k, true);
                    }
                }
            }
        }
        // [§16.26] The readout's lift reads every face copy and writes the first copy of each coordinate only, each entry split
        // evenly over its column's copies, its bias the first copy's; the encoding's rows are repeated over the copies, so the
        // grown face `⟨E′(a), y′⟩ = ⟨E(a), y⟩` exactly, and the copies part under learning.
        for j in 0..dw {
            for k in 0..dw {
                let old_at = ol.read + j * dw + k;
                let v = self.theta[old_at] as i128;
                let (q, rem) = (v.div_euclid(f as i128), v.rem_euclid(f as i128));
                for b in 0..f {
                    for c in 0..f {
                        let at = layout.read + face(b, j) * dw2 + face(c, k);
                        new[at] = if b == 0 { fit32(q + i128::from((c as i128) < rem), "a grown part outgrew its 32-bit carrier")? } else { 0 };
                        from[at] = (old_at, true);
                    }
                }
            }
            for b in 0..f {
                let at = layout.lift_bias + face(b, j);
                new[at] = if b == 0 { self.theta[ol.lift_bias + j] } else { 0 };
                from[at] = (ol.lift_bias + j, true);
            }
        }
        // The heads' own families (§16.29: kept, no face coordinate among them): the paces (§16.16), the moment encodings
        // (§15.1), the temperatures (§15.10) and the charts' biases, each its source's, its covector its source's whole.
        for (old_at, new_at, len) in [
            (ol.pace, layout.pace, layout.moment_face - layout.pace),
            (ol.moment_before, layout.moment_before, layout.moment_after - layout.moment_before),
            (ol.moment_after, layout.moment_after, layout.temper - layout.moment_after),
            (ol.temper, layout.temper, 2 * old.heads),
            (ol.q_bias, layout.q_bias, 2 * m),
            (ol.v_bias, layout.v_bias, 2 * m),
            (ol.probe_bias, layout.probe_bias, 2 * m),
        ] {
            for i in 0..len {
                new[new_at + i] = self.theta[old_at + i];
                from[new_at + i] = (old_at + i, false);
            }
        }
        // Vector families: each entry's copies.
        let mut repeat = |old_at: usize, new_at: usize, len: usize, copies: usize, index: &dyn Fn(usize, usize) -> usize, divided: bool| {
            for c in 0..copies {
                for i in 0..len {
                    new[new_at + index(c, i)] = self.theta[old_at + i];
                    from[new_at + index(c, i)] = (old_at + i, divided);
                }
            }
        };
        for row in 0..=a {
            repeat(ol.enc + row * dw, layout.enc + row * dw2, dw, f, &face, true);
            repeat(ol.before + row * dw, layout.before + row * dw2, dw, f, &face, true);
            repeat(ol.after + row * dw, layout.after + row * dw2, dw, f, &face, true);
        }
        repeat(ol.out_bias, layout.out_bias, dw, f, &face, true);
        repeat(ol.a_bias, layout.a_bias, fc, f, &contact, true);
        repeat(ol.b_bias, layout.b_bias, fc, f, &contact, true);
        repeat(ol.w_bias, layout.w_bias, dw, f, &face, true);
        repeat(ol.read_bias, layout.read_bias, a, 1, &kept, false);
        repeat(ol.moment_face_bias, layout.moment_face_bias, dw, f, &face, true);
        Ok((Self::with_theta(d, new), from))
    }

    /// [definition; agent-inferred, November 4, §16.40] **The field with one more lane** (the tower record, D2): a lane of
    /// `W` coordinates founded after the others as a founding founds them, the encoding's and the strand contacts' rows of
    /// every class uniform on `±1` (the unresolved row at zero) and the moment's chart into the lane uniform on `±√(3/2T)`
    /// at the turned modes, read from `keys` four bytes a draw in that order; every read from the lane (the key, value and
    /// probe charts' columns, both pair drives' columns, the readout's lift, its rows and its columns) and every other
    /// write into it (the current's return, the pair contact's return, the biases) at zero. Every old entry keeps its row
    /// and column in its family. Each old lane's chart is its own ([`lane_chart`]), nothing reads the new lane and nothing
    /// it is written by reaches a read, so the laned field reads every face exactly as the old one did; and every read
    /// from the lane has a covector from the first section on (the lane's chart times the read's covector), so the lane
    /// opens with no copy's symmetry to break (§16.37).
    ///
    /// With triads ([`Declaration::triads`]) their charts' columns over the lane and their return's rows into it stand at zero too, so every
    /// triad's product and every face is the one before the lane. Refused where the face reads its sites' loudness ([`Declaration::loud`]).
    ///
    /// Returns the laned field and, for each entry, the old entry it carries (`None` for the lane's own).
    pub fn laned(&self, keys: &[u8]) -> Result<(Self, Vec<Option<usize>>)> {
        if self.declaration.loud {
            // The face's loudness holds one strength a lane ([`Loci::loud`]); a lane's strength founded beside the standing ones is not built.
            return refuse("a growth in lanes of a field whose face reads its sites' loudness (a lane's strength beside the standing ones is not built)");
        }
        let old = self.declaration;
        let d = old.laned()?;
        let layout = Loci::new(&d);
        let ol = &self.layout;
        let (dw, dw2, m2, fc, a) = (old.width, d.width, 2 * old.complex(), old.contacts, old.alphabet);
        let mut new = vec![0i32; layout.len];
        let mut from: Vec<Option<usize>> = vec![None; layout.len];
        // A block of `rows × cols` (old) placed at the same rows and columns of a block `new_cols` wide.
        let mut place = |old_at: usize, new_at: usize, rows: usize, cols: usize, new_cols: usize| {
            for r in 0..rows {
                for c in 0..cols {
                    new[new_at + r * new_cols + c] = self.theta[old_at + r * cols + c];
                    from[new_at + r * new_cols + c] = Some(old_at + r * cols + c);
                }
            }
        };
        // The reads of the face (its coordinates the columns) and the encodings (a class a row).
        for (o, n, rows) in [(ol.q, layout.q, m2), (ol.v, layout.v, m2), (ol.probe, layout.probe, m2), (ol.a, layout.a, fc), (ol.b, layout.b, fc), (ol.enc, layout.enc, a + 1), (ol.before, layout.before, a + 1), (ol.after, layout.after, a + 1)] {
            place(o, n, rows, dw, dw2);
        }
        // The writes into the face (its coordinates the rows), and the face's own vectors.
        for (o, n, cols) in [(ol.out, layout.out, m2), (ol.w, layout.w, fc), (ol.moment_face, layout.moment_face, m2)] {
            place(o, n, dw, cols, cols);
        }
        for (o, n) in [(ol.out_bias, layout.out_bias), (ol.w_bias, layout.w_bias), (ol.moment_face_bias, layout.moment_face_bias), (ol.lift_bias, layout.lift_bias)] {
            place(o, n, 1, dw, dw);
        }
        place(ol.read, layout.read, dw, dw, dw2);
        // The families with no face coordinate: as they were.
        for (o, n, len) in [
            (ol.q_bias, layout.q_bias, m2),
            (ol.v_bias, layout.v_bias, m2),
            (ol.probe_bias, layout.probe_bias, m2),
            (ol.a_bias, layout.a_bias, fc),
            (ol.b_bias, layout.b_bias, fc),
            (ol.read_bias, layout.read_bias, a),
            (ol.moment_before, layout.moment_before, ol.moment_after - ol.moment_before),
            (ol.moment_after, layout.moment_after, ol.temper - ol.moment_after),
            (ol.temper, layout.temper, 2 * old.heads),
            (ol.pace, layout.pace, ol.moment_face - ol.pace),
        ] {
            place(o, n, 1, len, len);
        }
        // [theory, November 11 17:25] The carry circles' charts read the face as `a` and `b` do (its columns the coordinates): the lane's columns at
        // zero; their biases as they were.
        if d.carry > 0 {
            place(ol.carry, layout.carry, 2 * d.carry, dw, dw2);
            place(ol.carry_bias, layout.carry_bias, 1, 2 * d.carry, 2 * d.carry);
        }
        // [agent-inferred, November 14] The opening's lift reads the charted face as the read block does (`R⁰ r̂ + b⁰`, its rows the lift's
        // coordinates, its columns the face's): the lane's rows and columns at zero, its bias's lane at zero. The junction's row reads the charted
        // read (its columns the face's): the lane's columns at zero. The mark's strengths read no coordinate: as they were.
        if d.opening {
            place(ol.opening, layout.opening, dw, dw, dw2);
            place(ol.opening_bias, layout.opening_bias, 1, dw, dw);
        }
        if d.junction {
            place(ol.junction, layout.junction, 1, dw, dw2);
            place(ol.junction_bias, layout.junction_bias, 1, 1, 1);
        }
        if d.mark {
            place(ol.mark, layout.mark, 1, MARK_BASES, MARK_BASES);
        }
        // [the lead, November 17] The triads' charts read the charted read as the pair drives do (their columns the face's coordinates): the
        // lane's columns at zero, so no leg reads the lane and every product is the one before it; their biases as they were. The return
        // `W_T` writes into the face (its rows the coordinates): the lane's rows at zero. Why this is built now: on November 12 the triads were
        // founded last and a lane after them was refused as not built, so from lap 75 the line could not grow its face at all, and a part
        // founded beside the triads was refused with it; the growth needs no more than the triads' three families laid as `a`, `b` and `W` are.
        if d.triads > 0 {
            let (j2, j6) = (2 * d.triads, 6 * d.triads);
            place(ol.triad, layout.triad, j6, dw, dw2);
            place(ol.triad_bias, layout.triad_bias, 1, j6, j6);
            place(ol.w_triad, layout.w_triad, dw, j2, j2);
        }
        // [the lead, November 20] The pump's chart reads the charted read as the circles' own charts do (its columns the face's coordinates): the
        // lane's columns at zero, so no circle's pump reads the lane; its bias as it was.
        if d.pump {
            place(ol.pump, layout.pump, 2 * d.carry, dw, dw2);
            place(ol.pump_bias, layout.pump_bias, 1, 2 * d.carry, 2 * d.carry);
        }
        // The lane's founding draws.
        let mut cursor = 0usize;
        let mut draw = |num: u128, den: u128, bits: u32| -> Result<i32> {
            let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the lane's founding reads"))?;
            cursor += 4;
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            fit32((k * ((num << bits) / den) as i128) >> 31, "a lane's founded value outgrew its 32-bit carrier")
        };
        for start in [layout.enc, layout.before, layout.after] {
            for row in 0..a {
                for j in dw..dw2 {
                    new[start + row * dw2 + j] = draw(1, 1, FACE_BITS)?;
                }
            }
        }
        let tm = old.moment_modes();
        if tm > 0 {
            let (three_m, dd_m) = chart_scale(2 * tm);
            let carries: Vec<bool> = (0..m2).map(|k| old.carries_moment((k % old.complex()) / old.modes)).collect();
            for o in dw..dw2 {
                for (k, &on) in carries.iter().enumerate() {
                    if on {
                        new[layout.moment_face + o * m2 + k] = draw(three_m, dd_m, MATERIAL_BITS)?;
                    }
                }
            }
        }
        debug_assert_eq!(cursor, 4 * old.lane_draws());
        let mut out = Self::with_theta(d, new);
        (out.per_blank_clock, out.bare_stretch) = (self.per_blank_clock, self.bare_stretch);
        // [agent-inferred, November 14] A tower grows the fine level's lanes alone: the level's field is kept, and the glue's reads and writes of
        // the fine face (`A`'s columns of each harmonic, `B`'s rows and `b_B` of each harmonic) take the lane at zero, so the restriction reads no
        // lane coordinate and the prolongation writes none, and every face is kept. Each block is harmonic-major (`k D₀ + c`, [`charted`]).
        if let Some(sc) = &self.scale {
            // [the lead, November 20] The one-sided block's rows of the fine face (`B⁻`, `b_B⁻`, [`Scale::before_offsets`]) take the lane at
            // zero as `B`'s do, laid after the law's glue as before.
            let before = sc.before_offsets(dw);
            let (h, d1) = (sc.harmonics, sc.coarse.declaration.width);
            let (a0, ab0, b0, bb0, len0) = sc.glue_offsets(dw);
            let (a1, ab1, b1, bb1, len1) = sc.glue_offsets(dw2);
            let (old_fine, new_fine, coarse) = (self.theta.len(), layout.len, sc.coarse.theta.len());
            let total1 = if before.is_some() { len1 + crate::field::scale::glue_before_len(h, dw2, d1) } else { len1 };
            let mut glue = vec![0i32; total1];
            from.resize(new_fine, None);
            from.extend((0..coarse).map(|k| Some(old_fine + k)));
            let mut gfrom: Vec<Option<usize>> = vec![None; total1];
            let (og, ng) = (old_fine + coarse, new_fine + coarse);
            let mut copy = |o: usize, n: usize| {
                glue[n] = sc.glue[o];
                gfrom[n] = Some(og + o);
            };
            for r in 0..d1 {
                for k in 0..h {
                    for c in 0..dw {
                        copy(a0 + r * h * dw + k * dw + c, a1 + r * h * dw2 + k * dw2 + c);
                    }
                }
            }
            for r in 0..d1 {
                copy(ab0 + r, ab1 + r);
            }
            for k in 0..h {
                for c in 0..dw {
                    for col in 0..d1 {
                        copy(b0 + (k * dw + c) * d1 + col, b1 + (k * dw2 + c) * d1 + col);
                    }
                    copy(bb0 + k * dw + c, bb1 + k * dw2 + c);
                }
            }
            if let Some((b2, bb2, _)) = before {
                let (nb2, nbb2) = (len1, len1 + h * dw2 * d1);
                for k in 0..h {
                    for c in 0..dw {
                        for col in 0..d1 {
                            copy(b2 + (k * dw + c) * d1 + col, nb2 + (k * dw2 + c) * d1 + col);
                        }
                        copy(bb2 + k * dw + c, nbb2 + k * dw2 + c);
                    }
                }
            }
            debug_assert_eq!((len0, gfrom.len()), (bb0 + h * dw, total1));
            debug_assert_eq!(ng, from.len());
            from.extend(gfrom);
            out.scale = Some(Box::new(Scale { harmonics: h, split: sc.split, coarse: sc.coarse.clone(), glue }));
        }
        Ok((out, from))
    }
}

impl Constitution {
    /// [definition; theory, November 11 17:25] **The field with `circles` carry circles** ([`Declaration::carry`]): first the growth by
    /// `2 circles` pair contacts ([`Constitution::contacted`], its draws from `keys`), so the circles are the grown field's last `circles` complex
    /// contacts, their `a` and `b` drawn as a growth draws them, their columns of `W` and their biases at zero; then the circles' charts after
    /// every family: the turn rows `Q` drawn uniform on `±√(3/D)` at the material's grain from `keys` past the contacts' draws (four bytes a draw,
    /// the rows in order, as the contacts' drives are drawn), so `q` opens at unit power and a site's turn is a phase of about a radian set by its
    /// own read; the leak rows `L` and both biases `q_b`, `ℓ_b` at zero, so the leak's log chart reads `ℓ = 0` and `d = d₀ = 1/4` at every site
    /// ([`carry_friction`], [`CARRY_LEAK_FOUNDING`]) and each circle is founded as a turn with the near field's friction, `|γ| = 4/5`, a group of
    /// `NEAR − 1` places (founded at `d = 0` the group was unbounded and the first carry lap was refused, [`Declaration::carry`]), its drive
    /// coupled at one ([`carry_coupling`]): the chart's zero is the founded friction. Every sum the forward forms into the face is
    /// then the old sum (the circles' `W` columns are zero), so every face is kept bit for bit; the circles' return has a covector from the
    /// first section on.
    ///
    /// Refused for a tower's levels and for a field that already has carry circles (a plain growth by contacts in such a field is refused
    /// too, [`Declaration::contacted`]: the circles stay the last contacts). Returns the grown field and, for each entry, the old entry
    /// it carries.
    pub fn with_carry(&self, circles: usize, keys: &[u8]) -> Result<(Self, Vec<Option<usize>>)> {
        if self.scale.is_some() {
            return refuse("a tower's levels take carry circles level by level, not through the fine field alone");
        }
        if self.declaration.carry > 0 {
            return refuse("a field that already has carry circles");
        }
        if self.declaration.triads > 0 {
            // [theory, November 12, the triad record §4] The triads' families stand after the circles'; circles grown after them are not built.
            return refuse("a growth in carry circles of a field with triads (the triads are founded last; a growth after them is not built)");
        }
        if circles == 0 {
            return refuse("a growth by no carry circles");
        }
        let (contacted, mut from) = self.contacted(2 * circles, keys)?;
        let d = Declaration { carry: circles, ..contacted.declaration };
        d.admit()?;
        let layout = Loci::new(&d);
        let dw = d.width;
        let mut theta = contacted.theta;
        // [the lead, November 18] The circles' charts are laid after every family this founding knows. A field that already holds a later
        // family (the opening's lift, the junction, the mark, the loudness, closed characters) would have those entries read as the circles'
        // charts: refused here, where a debug assertion alone held it (a release build laid the charts over them; found by a test's fixture).
        if theta.len() != layout.carry {
            return refuse("a first growth in carry circles of a field that holds a family laid after the circles' (not built)");
        }
        theta.resize(layout.len, 0);
        from.resize(layout.len, None);
        let (num, den) = chart_scale(dw);
        let mut cursor = 4 * self.declaration.contact_draws(2 * circles);
        for v in theta[layout.carry..layout.carry + circles * dw].iter_mut() {
            let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the carry circles' founding reads"))?;
            cursor += 4;
            let draw = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            *v = fit32((draw * ((num << MATERIAL_BITS) / den) as i128) >> 31, "a carry circle's founded turn row outgrew its 32-bit carrier")?;
        }
        debug_assert_eq!(cursor, 4 * self.declaration.carry_draws(circles));
        let mut out = Self::with_theta(d, theta);
        (out.per_blank_clock, out.bare_stretch) = (self.per_blank_clock, self.bare_stretch);
        Ok((out, from))
    }

    /// [definition; the lead, November 18, the record of the two streams §19] **The field with `circles` more carry circles**
    /// ([`Declaration::more_carry`]), founded as its first were ([`Constitution::with_carry`]): `2 circles` pair contacts after the standing
    /// ones in each half (real parts, then imaginary), their drives `a` and `b` drawn uniform on `±√(3/D)` at the material's grain from `keys`
    /// (four bytes a draw, the new rows in order, `a` then `b`), their biases and their columns of `W` at zero; then the new circles' turn
    /// rows drawn the same way, their leak rows and both their biases at zero, so each opens as a turn of about a radian set by its site's
    /// read at the founded friction `d₀ = 1/4`, `|γ| = 4/5`. Every standing entry keeps its value: a contact its complex index and strand
    /// side, a circle its number (circle `k` stays circle `k`; the new ones are circles `C..C + circles`), a circle's turn row its row and
    /// its leak row the same row of the leak's half. Every sum the forward forms into the face is the old sum (the new circles' `W` columns
    /// are zero), so every face is kept bit for bit, and the new circles' return has a covector from the first section on. A tower keeps
    /// its level as it stands (the level reads the fine field's width, which a growth in contacts does not change).
    ///
    /// Why: on November 18 a carried product with a stride of its own a symbol, read alone on the host, gave the arriving symbol 0.477 of
    /// its mass on 32 circles and 0.652 on 128 at the places five places settle, where the line read 0.650; a reader opened where the
    /// line's 32 circles stand came to rest there and read as the drawn one (`navigator.content-stride-on-open-text`), so what the readings
    /// left to grow is the circles' extent.
    ///
    /// Returns the grown field and, for each entry of its material, the old entry it carries (`None` for a new contact's and a new
    /// circle's own).
    pub fn more_carry(&self, circles: usize, keys: &[u8]) -> Result<(Self, Vec<Option<usize>>)> {
        let old = self.declaration;
        let d = old.more_carry(circles)?;
        let layout = Loci::new(&d);
        let ol = &self.layout;
        let (dw, fc, f2, c0, c1, added) = (old.width, old.contacts, d.contacts, old.carry, d.carry, 2 * circles);
        if ol.families.len() != layout.families.len() {
            return refuse("a growth in carry circles that changes the families");
        }
        let mut new = vec![0i32; layout.len];
        let mut from: Vec<Option<usize>> = vec![None; layout.len];
        // A standing contact at its index in the grown set (a real part keeps its place, an imaginary part moves past the new real
        // parts); new contact `k` (of `added`) follows its half's standing contacts ([`Constitution::contacted`]).
        let kept = |e: usize| if e < fc / 2 { e } else { f2 / 2 + e - fc / 2 };
        let fresh = |k: usize| if k < added / 2 { fc / 2 + k } else { f2 / 2 + fc / 2 + k - added / 2 };
        let drives = [(ol.a, layout.a), (ol.b, layout.b)];
        for (&(os, ol_len, _), &(ns, nl_len, _)) in ol.families.iter().zip(&layout.families) {
            let mut carry = |o: usize, n: usize| {
                new[n] = self.theta[o];
                from[n] = Some(o);
            };
            if let Some(&(_, ns)) = drives.iter().find(|&&(o, _)| o == os) {
                for e in 0..fc {
                    for j in 0..dw {
                        carry(os + e * dw + j, ns + kept(e) * dw + j);
                    }
                }
            } else if os == ol.a_bias || os == ol.b_bias {
                for e in 0..fc {
                    carry(os + e, ns + kept(e));
                }
            } else if os == ol.w {
                for r in 0..dw {
                    for e in 0..fc {
                        carry(os + r * fc + e, ns + r * f2 + kept(e));
                    }
                }
            } else if os == ol.carry {
                // The turn rows `0..C`, then the leak rows: each half's standing rows first in the grown half.
                for half in 0..2 {
                    for k in 0..c0 {
                        for j in 0..dw {
                            carry(os + (half * c0 + k) * dw + j, ns + (half * c1 + k) * dw + j);
                        }
                    }
                }
            } else if os == ol.carry_bias {
                for half in 0..2 {
                    for k in 0..c0 {
                        carry(os + half * c0 + k, ns + half * c1 + k);
                    }
                }
            } else {
                if ol_len != nl_len {
                    return refuse("a family that changes its length with the carry circles but is not one they index");
                }
                for i in 0..ol_len {
                    carry(os + i, ns + i);
                }
            }
        }
        if from.iter().flatten().count() != self.theta.len() {
            return refuse("a growth in carry circles that did not carry every standing entry once");
        }
        // The draws: the new contacts' drives (`a` then `b`), then the new circles' turn rows.
        let (num, den) = chart_scale(dw);
        let mut cursor = 0usize;
        let draw = |cursor: &mut usize| -> Result<i32> {
            let word = keys.get(*cursor..*cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the new carry circles' founding reads"))?;
            *cursor += 4;
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            fit32((k * ((num << MATERIAL_BITS) / den) as i128) >> 31, "a new carry circle's founded value outgrew its 32-bit carrier")
        };
        for start in [layout.a, layout.b] {
            for k in 0..added {
                for j in 0..dw {
                    new[start + fresh(k) * dw + j] = draw(&mut cursor)?;
                }
            }
        }
        for v in new[layout.carry + c0 * dw..layout.carry + c1 * dw].iter_mut() {
            *v = draw(&mut cursor)?;
        }
        debug_assert_eq!(cursor, 4 * old.carry_draws(circles));
        let mut out = Self::with_theta(d, new);
        (out.per_blank_clock, out.bare_stretch) = (self.per_blank_clock, self.bare_stretch);
        // A tower's level follows the fine field's entries in the material, each entry as it stood.
        out.scale = self.scale.clone();
        let level = self.material_len() - self.theta.len();
        from.extend((0..level).map(|j| Some(self.theta.len() + j)));
        Ok((out, from))
    }

    /// [definition; theory, November 12, the triad record §4] **The field with `triads` triads** ([`Declaration::triads`]): the triads'
    /// families after every other ([`Loci::triad`]), every old entry kept at its offset; the charts' rows `A`, `B` and `G` drawn uniform on
    /// `±√(3/D)` at the material's grain from `keys`, four bytes a draw, the rows in order (`A`, then `B`, then `G`), as a growth in contacts draws
    /// the drives `a` and `b` ([`Constitution::contacted`]), so each leg's read opens at unit power; the charts' biases and the return `W_T` at zero. Every
    /// sum the forward forms into the face is then the old sum (`W_T` is zero, so the one sum `W c + W_T c^T + b_c` is `W c + b_c`), and every face
    /// is kept bit for bit; at the founding only `W_T` has a covector at first order (`∇_α ℓ = 0` while `W_T = 0`, §3.2), and as `W_T` opens the
    /// three legs open with it.
    ///
    /// Refused for a tower's levels, for a field that already has triads and for none. A growth in contacts, in circles or by copies of a
    /// field with triads is refused too ([`Declaration::contacted`], [`Constitution::with_carry`], [`Constitution::grown`]): those growths after
    /// the triads are not built. A lane after them is ([`Constitution::laned`], November 17). Returns the grown field and, for each entry, the old entry it carries (`None` for
    /// the triads' own).
    pub fn with_triads(&self, triads: usize, keys: &[u8]) -> Result<(Self, Vec<Option<usize>>)> {
        self.with_triads_at(triads, keys, false)
    }

    /// [definition; theory, November 16 19:10Z, the crossing triad] **The field with crossing triads**: [`Constitution::with_triads`] with the triads'
    /// legs at the site ([`Declaration::crossing`]); the same families, founded the same way (`W_T` at zero, so every face is the field's before the
    /// growth, bit for bit).
    pub fn with_crossings(&self, triads: usize, keys: &[u8]) -> Result<(Self, Vec<Option<usize>>)> {
        self.with_triads_at(triads, keys, true)
    }

    /// The triads' growth, their legs on the strand or at the site. [definition; November 16] The triads' families stand after the carry circles'
    /// and before the opening's lift, the junction, the mark and the loudness, so on a field that has any of those the growth inserts the triads'
    /// families where they stand and every later family moves by their length, each entry with its value (the map `from` says which old entry
    /// each new one copies). Why: the line of November 16 holds the opening's lift, the junction, the mark and the loudness, which were grown after
    /// the triads' place, and the November 13 refusal of a field with the opening's lift (`agent-inferred` then: "triads grown after it would move
    /// it") is answered by moving it.
    fn with_triads_at(&self, triads: usize, keys: &[u8], crossing: bool) -> Result<(Self, Vec<Option<usize>>)> {
        // [November 16] A tower keeps its level as it stands with the strand's triads refused there as before; crossing triads grow on the fine
        // field alone, as the junction's return and the mark do, and the level's entries follow the fine field's in the material
        // (`agent-inferred`: the crossing reads the fine field's gathered currents, which the level does not hold).
        if self.scale.is_some() && !crossing {
            return refuse("a tower's levels take triads level by level, not through the fine field alone");
        }
        if self.declaration.triads > 0 {
            return refuse("a field that already has triads");
        }
        if triads == 0 {
            return refuse("a growth by no triads");
        }
        let d = Declaration { triads, crossing, ..self.declaration };
        d.admit()?;
        let layout = Loci::new(&d);
        let dw = d.width;
        let old = &self.layout;
        // The triads' families are zero long in the old layout, at `old.triad`; every entry before it keeps its index and every entry from it moves
        // past the new families.
        let inserted = layout.len - self.theta.len();
        if old.triad != layout.triad || old.triad_bias != old.triad || old.w_triad != old.triad || layout.w_triad + dw * 2 * triads != old.triad + inserted {
            return refuse("a field whose triads' families do not stand where a growth inserts them");
        }
        let mut theta = Vec::with_capacity(layout.len);
        theta.extend_from_slice(&self.theta[..old.triad]);
        theta.resize(old.triad + inserted, 0);
        theta.extend_from_slice(&self.theta[old.triad..]);
        let mut from: Vec<Option<usize>> = (0..old.triad).map(Some).collect();
        from.resize(old.triad + inserted, None);
        from.extend((old.triad..self.material_len()).map(Some));
        let (num, den) = chart_scale(dw);
        let mut cursor = 0usize;
        for v in theta[layout.triad..layout.triad + 6 * triads * dw].iter_mut() {
            let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the triads' founding reads"))?;
            cursor += 4;
            let draw = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            *v = fit32((draw * ((num << MATERIAL_BITS) / den) as i128) >> 31, "a triad's founded chart row outgrew its 32-bit carrier")?;
        }
        debug_assert_eq!(cursor, 4 * self.declaration.triad_draws(triads));
        let mut out = Self::with_theta(d, theta);
        out.scale = self.scale.clone();
        (out.per_blank_clock, out.bare_stretch) = (self.per_blank_clock, self.bare_stretch);
        Ok((out, from))
    }

    /// [definition; theory, November 13, P60 items 1a and 3] **The field with the opening's lift** ([`Declaration::opening`]): `R⁰` and `b⁰`
    /// appended at the end of the material, founded at zero, every standing entry kept at its index; no key is read and the draws do not move.
    /// With `R⁰ = 0` and `b⁰ = 0` the opening's face is the class biases' alone, and the first covector reaches the block through `δR⁰ = δy⁰ r̂ᵀ`.
    /// Also the map from each new entry to the old one it copies (`None` for the block). Refused on a tower, and on a field that has it.
    pub fn with_opening(&self) -> Result<(Self, Vec<Option<usize>>)> {
        if self.scale.is_some() {
            return refuse("a tower's levels take the opening's lift level by level, not through the fine field alone");
        }
        if self.declaration.opening {
            return refuse("a field that already has the opening's lift");
        }
        let d = Declaration { opening: true, ..self.declaration };
        d.admit()?;
        let layout = Loci::new(&d);
        let mut theta = self.theta.clone();
        if theta.len() != layout.opening {
            return refuse("a field whose material does not end where the opening's lift begins");
        }
        theta.resize(layout.len, 0);
        let mut from: Vec<Option<usize>> = (0..self.theta.len()).map(Some).collect();
        from.resize(layout.len, None);
        let mut out = Self::with_theta(d, theta);
        (out.per_blank_clock, out.bare_stretch) = (self.per_blank_clock, self.bare_stretch);
        Ok((out, from))
    }

    /// [definition; the lead, November 17, the founding records] **The field with closed characters** ([`Declaration::closed`]): the keys
    /// (`A × 2E` on `2^(−16)`) and the odds (`heads` rows of `D` on `2^(−24)`, then a bias a head on `2^(−16)`) appended at the end of the
    /// material from a ruler's words, every standing entry kept at its index; no key byte is read and the draws do not move. Also the map from
    /// each new entry to the old one it copies (`None` for the families). A tower keeps its level as it stands, and its entries follow the fine
    /// field's in the material, as the junction's growth keeps it. Refused on a field that has closed characters, and where the words are not
    /// the families' lengths.
    pub fn with_closed(&self, closed: usize, keys: &[i32], odds: &[i32]) -> Result<(Self, Vec<Option<usize>>)> {
        if self.declaration.closed > 0 {
            return refuse("a field that already has closed characters");
        }
        if closed == 0 {
            return refuse("a founding of no closed characters");
        }
        let d = Declaration { closed, ..self.declaration };
        d.admit()?;
        let layout = Loci::new(&d);
        if self.theta.len() != layout.closed_key || keys.len() != d.alphabet * 2 * closed || odds.len() != d.heads * (d.width + 1) {
            return refuse("closed characters whose keys or odds are not their families' lengths, or a field whose material does not end where they begin");
        }
        let (fine, total) = (self.theta.len(), self.material_len());
        let mut theta = self.theta.clone();
        theta.extend_from_slice(keys);
        theta.extend_from_slice(odds);
        let mut from: Vec<Option<usize>> = (0..fine).map(Some).collect();
        from.resize(layout.len, None);
        from.extend((fine..total).map(Some));
        let mut out = Self::with_theta(d, theta);
        out.scale = self.scale.clone();
        (out.per_blank_clock, out.bare_stretch) = (self.per_blank_clock, self.bare_stretch);
        Ok((out, from))
    }

    /// [definition; theory, November 13, the junction record §7] **The field with the junction's return** ([`Declaration::junction`]): `L`
    /// and `ℓ_b` appended at the end of the fine field's material, founded at zero (the matched load, `Γ = 0`), every standing entry kept; no key is
    /// read and the draws do not move. A tower keeps its level as it stands (its ticks carry no return), and its entries follow the fine field's in
    /// the material ([`Constitution::material_len`]). Also the map over the whole material from each new entry to the old one it copies (`None` for the
    /// chart). Refused on a field that has the return.
    pub fn with_junction(&self) -> Result<(Self, Vec<Option<usize>>)> {
        if self.declaration.junction {
            return refuse("a field that already has the junction's return");
        }
        let d = Declaration { junction: true, ..self.declaration };
        d.admit()?;
        let layout = Loci::new(&d);
        if self.theta.len() != layout.junction {
            return refuse("a field whose material does not end where the junction's chart begins");
        }
        let (fine, total) = (self.theta.len(), self.material_len());
        let mut theta = self.theta.clone();
        theta.resize(layout.len, 0);
        let mut from: Vec<Option<usize>> = (0..fine).map(Some).collect();
        from.resize(layout.len, None);
        from.extend((fine..total).map(Some));
        let mut out = Self::with_theta(d, theta);
        out.scale = self.scale.clone();
        (out.per_blank_clock, out.bare_stretch) = (self.per_blank_clock, self.bare_stretch);
        Ok((out, from))
    }

    /// [definition; agent-inferred, November 14, the ring record §4] **The field that reads twice** ([`Declaration::mark`]): the mark's
    /// strengths `α_b` appended at the end of the fine field's material, founded at zero, every standing entry kept; no key is read and the
    /// draws do not move. At zero the second read opens every silent site on its open row, so every face is the source's bit for bit. A tower
    /// keeps its level as it stands (it reads with the fine field). Also the map over the whole material from each new entry to the old one it
    /// copies (`None` for the strengths). Refused on a field that reads twice.
    pub fn with_mark(&self) -> Result<(Self, Vec<Option<usize>>)> {
        if self.declaration.mark {
            return refuse("a field that already reads twice");
        }
        let d = Declaration { mark: true, ..self.declaration };
        d.admit()?;
        let layout = Loci::new(&d);
        if self.theta.len() != layout.mark {
            return refuse("a field whose material does not end where the mark's strengths begin");
        }
        let (fine, total) = (self.theta.len(), self.material_len());
        let mut theta = self.theta.clone();
        theta.resize(layout.len, 0);
        let mut from: Vec<Option<usize>> = (0..fine).map(Some).collect();
        from.resize(layout.len, None);
        from.extend((fine..total).map(Some));
        let mut out = Self::with_theta(d, theta);
        out.scale = self.scale.clone();
        (out.per_blank_clock, out.bare_stretch) = (self.per_blank_clock, self.bare_stretch);
        Ok((out, from))
    }

    /// [definition; Brandon, November 15 02:06Z] **The face that reads its sites' loudness** ([`Declaration::loud`]): `κ_ℓ` and `b` appended
    /// at the end of the fine field's material, founded at zero, every standing entry kept; no key is read and the draws do not move. At zero
    /// every site's sharpness is one, so every face is the source's bit for bit. A tower keeps its level as it stands. Also the map over the
    /// whole material from each new entry to the old one it copies (`None` for the new block). Refused on a field whose face already reads it.
    pub fn with_loud(&self) -> Result<(Self, Vec<Option<usize>>)> {
        if self.declaration.loud {
            return refuse("a field whose face already reads its sites' loudness");
        }
        let d = Declaration { loud: true, ..self.declaration };
        d.admit()?;
        let layout = Loci::new(&d);
        if self.theta.len() != layout.loud {
            return refuse("a field whose material does not end where the face's loudness begins");
        }
        let (fine, total) = (self.theta.len(), self.material_len());
        let mut theta = self.theta.clone();
        theta.resize(layout.len, 0);
        let mut from: Vec<Option<usize>> = (0..fine).map(Some).collect();
        from.resize(layout.len, None);
        from.extend((fine..total).map(Some));
        let mut out = Self::with_theta(d, theta);
        out.scale = self.scale.clone();
        (out.per_blank_clock, out.bare_stretch) = (self.per_blank_clock, self.bare_stretch);
        Ok((out, from))
    }

    /// [definition; the lead, November 19 (G-1119-7)] **The field whose carry circles are pumped** ([`Declaration::pump`]): the pump's chart
    /// `P` and `p_b` appended at the end of the fine field's material, founded at zero, every standing entry kept; no key is read and the draws do
    /// not move. At `p = 0` every circle's gate, coupling and move is the unpumped one's in integers ([`carry_gate_pumped`]), so every face is the
    /// source's bit for bit. A tower keeps its level as it stands. Also the map over the whole material from each new entry to the old one it
    /// copies (`None` for the chart). Refused on a field with no carry circles or whose circles are pumped.
    pub fn with_pump(&self) -> Result<(Self, Vec<Option<usize>>)> {
        if self.declaration.pump {
            return refuse("a field whose carry circles are already pumped");
        }
        let d = Declaration { pump: true, ..self.declaration };
        d.admit()?;
        let layout = Loci::new(&d);
        if self.theta.len() != layout.pump {
            return refuse("a field whose material does not end where the pump's chart begins");
        }
        let (fine, total) = (self.theta.len(), self.material_len());
        let mut theta = self.theta.clone();
        theta.resize(layout.len, 0);
        let mut from: Vec<Option<usize>> = (0..fine).map(Some).collect();
        from.resize(layout.len, None);
        from.extend((fine..total).map(Some));
        let mut out = Self::with_theta(d, theta);
        out.scale = self.scale.clone();
        (out.per_blank_clock, out.bare_stretch) = (self.per_blank_clock, self.bare_stretch);
        Ok((out, from))
    }

    /// [definition; theory, November 12 (the record of the opening's room, §4 item 4; corrected 18:44Z: the founding reads no key)]
    /// **The field with `fresh` more letters**, founded at a passage's crossing: the fresh classes follow the standing ones, so every
    /// standing class keeps its index (the void's included, wherever the codec holds it), and the open row (the unresolved operand,
    /// row `A` of each family with one) moves to the end of its family, row `A + F`. A fresh class's rows of the encoding `E`, of the two
    /// strand encodings `E₋` and `E₊`, of the two moment encodings and of each paced head's pace open at zero, and its class bias `c_a` at the
    /// least class bias the standing classes hold. Every other family is copied as it stands.
    ///
    /// Why at zero (the record, §4 item 4): the face reads a class through the encoding that encodes it, `z(a) = ⟨E(a), R r̂ + b_R⟩ + c_a`,
    /// and a site's opening face is a sum of rows, `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1))` and its moment's term. Every reader here is
    /// trained, so a drawn row would read each fresh letter at a random height at every face and be heard beside it as a letter it is not.
    /// At zero a fresh letter reads `c_a` at every face, the share the least-favoured standing letter is given, and its rows take their
    /// covector from the first face compared and the first place the letter stands at or beside; the sum has no product of two fresh rows.
    /// A fresh pace row at zero is the founding's pace, the strand's own clock (agent-inferred: the paces are founded at zero, and the
    /// record names no other opening for them). The readout's map is kept for every lift: `z(a)` at a standing class is its value before,
    /// entry for entry, and at a fresh class it is the least bias. The whole forward on a region of standing classes keeps every face's
    /// standing logits only where no head is paced: on a paced head a blank between arrivals runs at `κ = 1 + Σ_a p_a c[a]` over its own
    /// face, which the fresh classes' share at the least bias moves, so there the faces move by the founding's price (the record §4 item 4;
    /// the price at a face owed to #410).
    ///
    /// No key is read. Refused for a tower's levels. `fresh = 0` returns the field as it stands. Returns the grown field and, for each
    /// entry, the old entry it carries (`None` for a fresh class's own).
    pub fn lettered(&self, fresh: usize) -> Result<(Self, Vec<Option<usize>>)> {
        if self.scale.is_some() {
            return refuse("a tower's levels take letters level by level, not through the fine field alone");
        }
        let old = self.declaration;
        let d = old.lettered(fresh)?;
        let layout = Loci::new(&d);
        let ol = &self.layout;
        let (a, a2, dw, tm2, paced) = (old.alphabet, d.alphabet, old.width, 2 * old.moment_modes(), old.paced_heads());
        let mut new = vec![0i32; layout.len];
        let mut from: Vec<Option<usize>> = vec![None; layout.len];
        // Where an old row of a family with one row a class lands: a class keeps its index, the open row (index `A`) moves to `A + F`.
        let row = |r: usize| if r < a { r } else { a2 };
        let mut place = |o: usize, n: usize| {
            new[n] = self.theta[o];
            from[n] = Some(o);
        };
        // The families with a row a class and the open row: the encodings, the moment encodings.
        for (o, n, width) in [(ol.enc, layout.enc, dw), (ol.before, layout.before, dw), (ol.after, layout.after, dw), (ol.moment_before, layout.moment_before, tm2), (ol.moment_after, layout.moment_after, tm2)] {
            for r in 0..=a {
                for j in 0..width {
                    place(o + r * width + j, n + row(r) * width + j);
                }
            }
        }
        // The paces: each paced head's rate a class and the open row.
        for p in 0..paced {
            for r in 0..=a {
                place(ol.pace + p * (a + 1) + r, layout.pace + p * (a2 + 1) + row(r));
            }
        }
        // The class biases: each standing class at its index; the fresh at the least the standing hold.
        for c in 0..a {
            place(ol.read_bias + c, layout.read_bias + c);
        }
        // The families no class indexes, in their three stretches of the layout: the charts from `q` to the lift, the temperatures and the
        // probe chart, and the moment's chart into the face with every family after it.
        for (o_from, o_to, n_from) in [(ol.q, ol.read_bias, layout.q), (ol.temper, ol.pace, layout.temper), (ol.moment_face, ol.len, layout.moment_face)] {
            for k in 0..o_to - o_from {
                place(o_from + k, n_from + k);
            }
        }
        let least = self.theta[ol.read_bias..ol.read_bias + a].iter().copied().min().unwrap_or(0);
        new[layout.read_bias + a..layout.read_bias + a2].fill(least);
        // [theory, November 12, P49] The two coverage checks are refusals: a growth is rare, and a release build must not pass a family it
        // missed (the stretches no class indexes keep their lengths, and every standing entry is carried once).
        if (layout.read_bias - layout.q, layout.pace - layout.temper, layout.len - layout.moment_face) != (ol.read_bias - ol.q, ol.pace - ol.temper, ol.len - ol.moment_face) {
            return refuse("a growth by letters whose families no class indexes changed their lengths");
        }
        if from.iter().filter(|o| o.is_some()).count() != self.theta.len() {
            return refuse("a growth by letters that did not carry every standing entry once");
        }
        let mut out = Self::with_theta(d, new);
        (out.per_blank_clock, out.bare_stretch) = (self.per_blank_clock, self.bare_stretch);
        Ok((out, from))
    }

    /// [definition; theory, November 10 09:55] **The field with `added` more pair contacts** (the merge's `c = (aᵀs)(bᵀx)`
    /// joined to the face by `W`): the new contacts' `a` and `b` rows are the pair drives, drawn as a founding of this
    /// declaration draws them, uniform on `±√(3/D)` at the material's grain, read from `keys` four bytes a draw (the new set's
    /// rows in order, `a` then `b`); every family that writes the face from the contacts (the pair's return `W`, and in an
    /// energy field the contraction `c`) takes the new contacts' columns at zero, and the contacts' biases open at zero as a
    /// founding opens them. Every sum the forward forms is then the old sum, so every face is kept bit for bit; the new
    /// contacts have a covector from the first section on (`W`'s new columns read the new `c`; the drives learn once `W` moves).
    ///
    /// The contacts are complex pairs (`e`, `f/2 + e`): the real parts then the imaginary parts, so the old contacts keep
    /// their pair and strand side (`e` even reads the site before, odd the one after) at the same indices within each half,
    /// and the new ones follow them in each half. The heads, the lanes and everything else are copied family by family.
    ///
    /// Returns the grown field and, for each entry, the old entry it carries (`None` for a new contact's own).
    pub fn contacted(&self, added: usize, keys: &[u8]) -> Result<(Self, Vec<Option<usize>>)> {
        if self.scale.is_some() {
            return refuse("a tower's levels grow their contacts level by level, not through the fine field alone");
        }
        let old = self.declaration;
        let d = old.contacted(added)?;
        let layout = Loci::new(&d);
        let ol = &self.layout;
        let (dw, fc, f2) = (old.width, old.contacts, d.contacts);
        let mut new = vec![0i32; layout.len];
        let mut from: Vec<Option<usize>> = vec![None; layout.len];
        // Contact `e` of the old set at its index in the grown: a real part keeps its place, an imaginary part moves past the new
        // real parts. The new contact `k` (of `added`) follows its half's old contacts.
        let kept = |e: usize| if e < fc / 2 { e } else { f2 / 2 + e - fc / 2 };
        let fresh = |k: usize| if k < added / 2 { fc / 2 + k } else { f2 / 2 + fc / 2 + k - added / 2 };
        if ol.families.len() != layout.families.len() {
            return refuse("a growth in contacts that changes the families");
        }
        // The families that read or write the face through a contact, by their old start: the pair drives (a contact a row),
        // their biases, the pair's return (a contact a column) and the energy's contraction.
        let drives = [(ol.a, layout.a), (ol.b, layout.b)];
        for (&(os, ol_len, _), &(ns, nl_len, _)) in ol.families.iter().zip(&layout.families) {
            if let Some(&(_, ns)) = drives.iter().find(|&&(o, _)| o == os) {
                for e in 0..fc {
                    for j in 0..dw {
                        new[ns + kept(e) * dw + j] = self.theta[os + e * dw + j];
                        from[ns + kept(e) * dw + j] = Some(os + e * dw + j);
                    }
                }
            } else if os == ol.a_bias || os == ol.b_bias || false {
                for e in 0..fc {
                    new[ns + kept(e)] = self.theta[os + e];
                    from[ns + kept(e)] = Some(os + e);
                }
            } else if os == ol.w {
                for r in 0..dw {
                    for e in 0..fc {
                        new[ns + r * f2 + kept(e)] = self.theta[os + r * fc + e];
                        from[ns + r * f2 + kept(e)] = Some(os + r * fc + e);
                    }
                }
            } else {
                if ol_len != nl_len {
                    return refuse("a family that changes its length with the contacts but is not one they index");
                }
                for i in 0..ol_len {
                    new[ns + i] = self.theta[os + i];
                    from[ns + i] = Some(os + i);
                }
            }
        }
        // The new contacts' drives: a founding's draws at the grown width's scale, the new set's rows in order.
        let (num, den) = chart_scale(dw);
        let mut cursor = 0usize;
        for start in [layout.a, layout.b] {
            for k in 0..added {
                for j in 0..dw {
                    let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the new contacts' founding reads"))?;
                    cursor += 4;
                    let draw = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
                    new[start + fresh(k) * dw + j] = fit32((draw * ((num << MATERIAL_BITS) / den) as i128) >> 31, "a new contact's founded value outgrew its 32-bit carrier")?;
                }
            }
        }
        debug_assert_eq!(cursor, 4 * old.contact_draws(added));
        { let mut grown = Self::with_theta(d, new); (grown.per_blank_clock, grown.bare_stretch) = (self.per_blank_clock, self.bare_stretch); Ok((grown, from)) }
    }
}

impl Learner {

    /// [definition; agent-inferred, November 1] **The learner widened** ([`Constitution::grown`]), its
    /// differences read from the founding key stream past every draw read before, and its moments
    /// lifted as the tower's are: split evenly, each grown coordinate's covector at the growth
    /// point is the old one divided among its `f` copies and the readout's the old one, so a grown
    /// coordinate carries `m/f` and `v/f²`, the readout `m` and `v`, and opens on the old
    /// normalized step. Each copy then steps as the old coordinate did, and the `f` copies of a
    /// sum move together, so the rate falls by `⌈log₂ f⌉` bits: the field's step stays the old one.
    /// A learner holding a step is refused: the step is read first ([`Learner::read_step_on`]).
    pub fn widened(&self, factor: usize, keys: &[u8]) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner widens after its held step is read");
        }
        let rest = keys.get(self.drawn..).ok_or(TowerError::Refused("fewer key bytes than the growth draws"))?;
        let (field, from) = self.field.grown(factor, rest)?;
        let (f, f2) = (factor as i128, (factor * factor) as i128);
        let first = from.iter().map(|&(i, divided)| if divided { div_nearest(self.first[i], f) } else { self.first[i] }).collect();
        let second = from.iter().map(|&(i, divided)| if divided { div_nearest(self.second[i], f2) } else { self.second[i] }).collect();
        let drawn = self.drawn + 4 * self.field.growth_draws(factor);
        let rate_bits = self.rate_bits + (usize::BITS - (factor - 1).leading_zeros());
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits, drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts: None, own_rates: None, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; agent-inferred, November 4, §16.40] **The learner with one more lane** ([`Constitution::laned`]), the lane's
    /// draws read from the founding key stream past every draw read before. Every old entry keeps its moments; each of the
    /// lane's entries opens on its family's statistics, its first moment at zero and its second at the mean of its
    /// family's old second moments (a family no covector has reached opens at zero, at its own first covector, as a
    /// founding's entries do). The rate is kept: no coordinate is shared among copies, so each steps as it did.
    ///
    /// Why the family's statistics and not the founding's opening: an entry opened at its first covector takes the
    /// largest normalized step, `2^(grain − rate)` with the covector's sign, and every read from a fresh lane opens at
    /// once and in agreement, so the lane moved the trained keys, values and drives together by about a tenth of their
    /// unit a section. Measured from run41's alone state grown to `D 512` (`_receipts/law44/probe_founding.txt`): 208
    /// halvings over 212 sections against the alone arm's one, 166 of 212 deposited, the sections' code before their step
    /// 1.628 bits a byte against 1.470, and the withheld code 0.268 to 0.294 bits a site in half a lap. Opened on its
    /// family's second moment, a lane entry's first step is an eighth of its covector over the family's own scale, the
    /// step the trained entries beside it take; on the same state (`probe_family.txt`): 169 halvings over 219 sections,
    /// 211 deposited, the withheld code 0.268 to 0.286. Smaller, not gone: the lane's covectors stay coherent, so its steps
    /// grow toward the full normalized size as its first moments fill.
    pub fn laned(&self, keys: &[u8]) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner grows a lane after its held step is read");
        }
        let rest = keys.get(self.drawn..).ok_or(TowerError::Refused("fewer key bytes than the lane's draws"))?;
        let (field, from) = self.field.laned(rest)?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let mut second: Vec<i128> = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        for &(start, len, _) in field.families_all().iter() {
            let old: Vec<i128> = (start..start + len).filter_map(|k| from[k].map(|i| self.second[i])).collect();
            if old.len() == len || old.is_empty() {
                continue;
            }
            // The mean term by term (each second moment is under `2^126`, so a family's sum is not formed).
            let n = old.len() as i128;
            let mean = old.iter().map(|v| v / n).sum::<i128>() + old.iter().map(|v| v % n).sum::<i128>() / n;
            for k in (start..start + len).filter(|&k| from[k].is_none()) {
                second[k] = mean;
            }
        }
        let drawn = self.drawn + 4 * self.field.declaration.lane_draws();
        // [agent-inferred, November 14] The founded parts' rates are kept (the lane's entries join the lane parts, [`Constitution::founded_parts`]), and
        // where the learner carries each entry's own rate every standing entry keeps it and a lane entry takes `rate_bits`.
        let own_rates = self.own_rates.as_ref().map(|own| from.iter().map(|o| o.map_or(self.rate_bits, |i| own[i])).collect());
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts: self.rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; theory, November 11 17:25] **The learner with `circles` carry circles** ([`Constitution::with_carry`]), the circles' draws read from
    /// the founding key stream past every draw read before. Every old entry keeps its moments and its remainder; the circles' contacts' entries
    /// open as a growth in contacts opens them ([`Learner::contacted`]: the first moments at zero, the second at the mean of their family's
    /// old second moments), and the circles' charts' moments at zero (a family with no old entry). The draws advance past the contacts' and
    /// the turn rows'. The founded parts' rates are kept, the circles' parts at the old rate (octaves 0), so the parts line goes on telling the
    /// contacts before the last plain growth; the held step and the last section's step, of the old layout, are dropped.
    pub fn with_carry(&self, circles: usize, keys: &[u8]) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner takes carry circles after its held step is read");
        }
        let rest = keys.get(self.drawn..).ok_or(TowerError::Refused("fewer key bytes than the carry circles' draws"))?;
        let (field, from) = self.field.with_carry(circles, rest)?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let mut second: Vec<i128> = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        for &(start, len, _) in field.families_all().iter() {
            let old: Vec<i128> = (start..start + len).filter_map(|k| from[k].map(|i| self.second[i])).collect();
            if old.len() == len || old.is_empty() {
                continue;
            }
            // The mean term by term (each second moment is under `2^126`, so a family's sum is not formed).
            let n = old.len() as i128;
            let mean = old.iter().map(|v| v / n).sum::<i128>() + old.iter().map(|v| v % n).sum::<i128>() / n;
            for k in (start..start + len).filter(|&k| from[k].is_none()) {
                second[k] = mean;
            }
        }
        let drawn = self.drawn + 4 * self.field.declaration.carry_draws(circles);
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts: self.rate_parts, own_rates: None, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; the lead, November 18, the record of the two streams §19] **The learner with `circles` more carry circles**
    /// ([`Constitution::more_carry`]), the draws read from the founding key stream past every draw read before. Every standing entry keeps
    /// its moments; a new contact's and a new circle's entries open as a growth opens them ([`Learner::with_carry`]): the first moments at
    /// zero, the second at the mean of their family's standing second moments (the circles' charts have standing entries now, so a new
    /// circle's turn row steps at its family's own scale). An entry's own rate, where the state carries them, is kept and a new entry
    /// opens at the base rate; the parts' rates are kept; the held step and the last section's step, of the old layout, are dropped,
    /// and the step's remainder, where the state carries one, opens at zero over the new length (as every founding here opens it:
    /// no standing entry's remainder is carried).
    pub fn more_carry(&self, circles: usize, keys: &[u8]) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner grows its carry circles after its held step is read");
        }
        let rest = keys.get(self.drawn..).ok_or(TowerError::Refused("fewer key bytes than the new carry circles' draws"))?;
        let (field, from) = self.field.more_carry(circles, rest)?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let mut second: Vec<i128> = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        for &(start, len, _) in field.families_all().iter() {
            let old: Vec<i128> = (start..start + len).filter_map(|k| from[k].map(|i| self.second[i])).collect();
            if old.len() == len || old.is_empty() {
                continue;
            }
            // The mean term by term (each second moment is under `2^126`, so a family's sum is not formed).
            let n = old.len() as i128;
            let mean = old.iter().map(|v| v / n).sum::<i128>() + old.iter().map(|v| v % n).sum::<i128>() / n;
            for k in (start..start + len).filter(|&k| from[k].is_none()) {
                second[k] = mean;
            }
        }
        let own_rates = self.own_rates.as_ref().map(|own| from.iter().map(|o| o.map_or(self.rate_bits, |i| own[i])).collect());
        let drawn = self.drawn + 4 * self.field.declaration.carry_draws(circles);
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts: self.rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; theory, November 12, the triad record §4] **The learner with `triads` triads** ([`Constitution::with_triads`]), the triads' draws read
    /// from the founding key stream past every draw read before (`6 J D` draws, four bytes a draw). Every old entry keeps its moments and its
    /// remainder. The triads' first moments open at zero, and their second moments at the mean of their counterparts' old second moments: the
    /// charts `A`, `B` and `G` at the mean over the pair drives `a` and `b`, the charts' biases at the mean over the drives' biases, and `W_T` at the
    /// mean over `W`. Reason (`agent-inferred`, from the growth in contacts' law, [`Learner::contacted`]): a new entry's first step is then its
    /// covector over its family's scale, the step a trained entry takes, and never the largest normalized step of a fresh entry; the triad's charts
    /// and return are the drives' and `W`'s counterparts with one operand more. The draws advance by `4 · 6 J D` bytes. The founded parts' rates are
    /// kept, the triad's part at octave 0 (the base rate), and where the learner carries each entry's own rate ([`Learner::own_rates`]) every
    /// old entry keeps it and the triads' entries take the base rate, the rate their part's octave 0 gives. Reason for keeping them
    /// (`agent-inferred`, from the record of November 11 on a build entering a line): a growth that keeps every face and every moment keeps every
    /// old entry's rate too, since a state tool that left the part rates behind once made every part train at the base rate with nothing refused.
    /// The held step and the last section's step, of the old layout, are dropped. Refused while a step is held.
    pub fn with_triads(&self, triads: usize, keys: &[u8]) -> Result<Self> {
        self.with_triads_at(triads, keys, false)
    }

    /// [definition; theory, November 16 19:10Z] **The learner with crossing triads** ([`Constitution::with_crossings`]), opened as
    /// [`Learner::with_triads`] opens the strand's: every standing entry keeps its moments, its remainder and its rate at its new index.
    pub fn with_crossings(&self, triads: usize, keys: &[u8]) -> Result<Self> {
        self.with_triads_at(triads, keys, true)
    }

    fn with_triads_at(&self, triads: usize, keys: &[u8], crossing: bool) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner takes triads after its held step is read");
        }
        let rest = keys.get(self.drawn..).ok_or(TowerError::Refused("fewer key bytes than the triads' draws"))?;
        let (field, from) = if crossing { self.field.with_crossings(triads, rest)? } else { self.field.with_triads(triads, rest)? };
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let mut second: Vec<i128> = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        let (old, new) = (&self.field.layout, &field.layout);
        let (dw, f, j2, j6) = (self.field.declaration.width, self.field.declaration.contacts, 2 * triads, 6 * triads);
        // The mean term by term over the counterparts' old second moments (each under `2^126`, so a family's sum is not formed); zero where no
        // covector has reached them, as a founding's entries open.
        let mean = |ranges: &[(usize, usize)]| -> i128 {
            let values: Vec<i128> = ranges.iter().flat_map(|&(start, len)| self.second[start..start + len].iter().copied()).collect();
            if values.is_empty() {
                return 0;
            }
            let n = values.len() as i128;
            values.iter().map(|v| v / n).sum::<i128>() + values.iter().map(|v| v % n).sum::<i128>() / n
        };
        second[new.triad..new.triad + j6 * dw].fill(mean(&[(old.a, f * dw), (old.b, f * dw)]));
        second[new.triad_bias..new.triad_bias + j6].fill(mean(&[(old.a_bias, f), (old.b_bias, f)]));
        second[new.w_triad..new.w_triad + dw * j2].fill(mean(&[(old.w, dw * f)]));
        let rate_parts = self.rate_parts.map(|rp| {
            let mut octaves = rp.octaves;
            octaves[TRIAD_PART] = 0;
            RateParts { octaves, ..rp }
        });
        // Each entry's own rate follows it to its new index; the triads' entries take `rate_bits` (November 16: the families may be inserted
        // before later ones, so the rates are mapped, not appended).
        let own_rates = self.own_rates.as_ref().map(|own| from.iter().map(|o| o.map_or(self.rate_bits, |i| own[i])).collect::<Vec<_>>());
        let drawn = self.drawn + 4 * self.field.declaration.triad_draws(triads);
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; the lead, November 16 21:40Z; atlas `contact.pool-founding`, `contact.tension-founds-face`] **The learner with its triads' legs
    /// founded where the tension leads**: `legs` the charts `A`, `B` and `G` with their biases as [`Loci`] lays them (`6J × D` rows, then `6J`
    /// biases, on the material's grain), read by a ruler from the covector at the strand's return against products of the pair chart
    /// ([`Constitution::crossing_tension`]). With `ret` none the return `W_T` is set to zero, so every face reads bit for bit as the field's before
    /// it and the first deposits charge the return from the covector that reaches it: a founding. With `ret` (`D × 2J`) the return is the
    /// ruler's too: a ruler's state, never trained from. The triads' moments open as a growth opens them ([`Learner::with_triads`]): first
    /// moments at zero, second moments at the mean of their counterparts'; every other entry, moment, rate and line is kept. Why the legs and
    /// not the return: with `W_T = 0` the legs' covectors vanish (atlas `contact.triad-manley-rowe-gauge`), so drawn legs wait on a return that
    /// drawn products charge only by chance, and a law that lives wholly in a product (`code.triad-character-of-composition`) is then met at
    /// its unicity distance by a walk; legs located from the tension give the return its covector at the first section. Refused on a learner
    /// without triads, while a step is held, or where the lengths are not the declaration's.
    pub fn with_located_legs(&self, legs: &[i32], ret: Option<&[i32]>) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner's legs are founded after its held step is read");
        }
        let d = &self.field.declaration;
        let (dw, f, j2, j6) = (d.width, d.contacts, 2 * d.triads, 6 * d.triads);
        if d.triads == 0 || legs.len() != j6 * dw + j6 || ret.is_some_and(|r| r.len() != dw * j2) {
            return refuse("a triad material that is not its declaration's");
        }
        let l = self.field.layout.clone();
        let mut out = self.clone();
        out.field.theta[l.triad..l.triad + j6 * dw].copy_from_slice(&legs[..j6 * dw]);
        out.field.theta[l.triad_bias..l.triad_bias + j6].copy_from_slice(&legs[j6 * dw..]);
        match ret {
            Some(r) => out.field.theta[l.w_triad..l.w_triad + dw * j2].copy_from_slice(r),
            None => out.field.theta[l.w_triad..l.w_triad + dw * j2].fill(0),
        }
        let mean = |ranges: &[(usize, usize)]| -> i128 {
            let values: Vec<i128> = ranges.iter().flat_map(|&(start, len)| self.second[start..start + len].iter().copied()).collect();
            if values.is_empty() {
                return 0;
            }
            let n = values.len() as i128;
            values.iter().map(|v| v / n).sum::<i128>() + values.iter().map(|v| v % n).sum::<i128>() / n
        };
        for (start, len, second) in [(l.triad, j6 * dw, mean(&[(l.a, f * dw), (l.b, f * dw)])), (l.triad_bias, j6, mean(&[(l.a_bias, f), (l.b_bias, f)])), (l.w_triad, dw * j2, mean(&[(l.w, dw * f)]))] {
            out.first[start..start + len].fill(0);
            out.second[start..start + len].fill(second);
        }
        (out.held, out.last) = (None, None);
        Ok(out)
    }

    /// [definition; theory, November 13, P60 items 1f and 3] **The learner with the opening's lift** ([`Constitution::with_opening`]), founded at zero.
    /// Every standing entry keeps its moments, its remainder and its rate; the block's first moments open at zero and its second at the mean of
    /// its counterpart's standing second moments (`R⁰` the readout's lift `R`, `b⁰` the lift's bias `b_R`), as a growth opens a new block's
    /// ([`Learner::with_triads`]), so its first step is its covector over its counterpart's scale. Its rate: the founded parts' rates are kept
    /// and the opening's part takes octave 0, what a newly grown block takes in this line (the triads took it); where the learner carries each
    /// entry's own rate, every standing entry keeps it and the block's entries take `rate_bits`. The draws, the laps and the pass are kept; the
    /// held step and the last section's step, of the old layout, are dropped. Refused while a step is held.
    pub fn with_opening(&self) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner takes the opening's lift after its held step is read");
        }
        let (field, from) = self.field.with_opening()?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let mut second: Vec<i128> = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        let (old, new, dw) = (&self.field.layout, &field.layout, self.field.declaration.width);
        let mean = |start: usize, len: usize| -> i128 {
            let values = &self.second[start..start + len];
            if values.is_empty() {
                return 0;
            }
            let n = values.len() as i128;
            values.iter().map(|v| v / n).sum::<i128>() + values.iter().map(|v| v % n).sum::<i128>() / n
        };
        second[new.opening..new.opening + dw * dw].fill(mean(old.read, dw * dw));
        second[new.opening_bias..new.opening_bias + dw].fill(mean(old.lift_bias, dw));
        let rate_parts = self.rate_parts.map(|rp| {
            let mut octaves = rp.octaves;
            octaves[OPENING_PART] = 0;
            RateParts { octaves, ..rp }
        });
        let own_rates = self.own_rates.as_ref().map(|own| {
            let mut rates = own.clone();
            rates.resize(field.material_len(), self.rate_bits);
            rates
        });
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn: self.drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; the lead, November 17, the founding record] **The learner with closed characters** ([`Constitution::with_closed`]): every
    /// standing entry keeps its moments, its remainder and its rate; the two families' moments open at zero and, where the learner carries each
    /// entry's own rate, their entries take `rate_bits`. They are no founded part: the odds step at the old entries' rate and the keys take no
    /// covector. The
    /// draws, the laps and the pass are kept; the held step and the last section's step are dropped. Refused while a step is held.
    pub fn with_closed(&self, closed: usize, keys: &[i32], odds: &[i32]) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner takes closed characters after its held step is read");
        }
        let (field, from) = self.field.with_closed(closed, keys, odds)?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let second = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        let own_rates = self.own_rates.as_ref().map(|own| from.iter().map(|o| o.map_or(self.rate_bits, |i| own[i])).collect());
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn: self.drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts: self.rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; theory, November 13, the junction record §7] **The learner with the junction's return** ([`Constitution::with_junction`]), founded at
    /// the matched load. Every standing entry keeps its moments, its remainder and its rate. The chart's first moments open at zero and its second
    /// at the mean of its counterpart's standing second moments, as a growth opens a new block's ([`Learner::with_opening`]): `L` and `ℓ_b`
    /// read the site's chart as the carry circles' leak chart and its biases do, and where the field has no circles as the pair drive `a` and its
    /// biases do (agent-inferred: the nearest block that reads the same chart into one real a site). Its rate: the founded parts' rates are kept
    /// and the junction's part takes octave 0, what a newly grown block takes in this line; where the learner carries each entry's own rate, every
    /// standing entry keeps it and the chart's entries take `rate_bits`. The draws, the laps and the pass are kept; the held step and the last
    /// section's step are dropped. Refused while a step is held.
    pub fn with_junction(&self) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner takes the junction's return after its held step is read");
        }
        let (field, from) = self.field.with_junction()?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let mut second: Vec<i128> = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        let (old, new, d) = (&self.field.layout, &field.layout, self.field.declaration);
        let dw = d.width;
        let mean = |start: usize, len: usize| -> i128 {
            let values = &self.second[start..start + len];
            if values.is_empty() {
                return 0;
            }
            let n = values.len() as i128;
            values.iter().map(|v| v / n).sum::<i128>() + values.iter().map(|v| v % n).sum::<i128>() / n
        };
        let (rows, biases) = if d.carry > 0 { ((old.carry + d.carry * dw, d.carry * dw), (old.carry_bias + d.carry, d.carry)) } else { ((old.a, d.contacts * dw), (old.a_bias, d.contacts)) };
        second[new.junction..new.junction + dw].fill(mean(rows.0, rows.1));
        second[new.junction_bias] = mean(biases.0, biases.1);
        let rate_parts = self.rate_parts.map(|rp| {
            let mut octaves = rp.octaves;
            octaves[JUNCTION_PART] = 0;
            RateParts { octaves, ..rp }
        });
        let own_rates = self.own_rates.as_ref().map(|own| from.iter().map(|o| o.map_or(self.rate_bits, |i| own[i])).collect());
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn: self.drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; the lead, November 19 (G-1119-7)] **The learner whose carry circles are pumped** ([`Constitution::with_pump`]), the pump's chart
    /// founded at zero. Every standing entry keeps its moments, its remainder and its rate. The chart's first moments open at zero and its second at
    /// the mean of the circles' own charts' standing second moments (`Q`'s and `L`'s rows for `P`, their biases for `p_b`), as the junction's chart
    /// opens beside them ([`Learner::with_junction`]): `P` reads the site's pair chart into a circle as `Q` and `L` do. Its rate: the chart is the
    /// circles' gate's third chart, so its entries are the `carry` part's ([`Constitution::founded_parts`]) and step at that part's octave
    /// (agent-inferred: one gate, one family); where the learner carries each entry's own rate, the chart's entries take `rate_bits`. The draws,
    /// the laps and the pass are kept; the held step and the last section's step are dropped. Refused while a step is held.
    pub fn with_pump(&self) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner pumps its carry circles after its held step is read");
        }
        let (field, from) = self.field.with_pump()?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let mut second: Vec<i128> = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        let (old, new, d) = (&self.field.layout, &field.layout, self.field.declaration);
        let (dw, c2) = (d.width, 2 * d.carry);
        let mean = |start: usize, len: usize| -> i128 {
            let values = &self.second[start..start + len];
            if values.is_empty() {
                return 0;
            }
            let n = values.len() as i128;
            values.iter().map(|v| v / n).sum::<i128>() + values.iter().map(|v| v % n).sum::<i128>() / n
        };
        second[new.pump..new.pump + c2 * dw].fill(mean(old.carry, c2 * dw));
        second[new.pump_bias..new.pump_bias + c2].fill(mean(old.carry_bias, c2));
        let own_rates = self.own_rates.as_ref().map(|own| from.iter().map(|o| o.map_or(self.rate_bits, |i| own[i])).collect());
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn: self.drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts: self.rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; agent-inferred, November 14, the ring record §4] **The learner that reads twice** ([`Constitution::with_mark`]), its strengths
    /// founded at zero. Every standing entry keeps its moments, its remainder and its rate. The strengths' moments open at zero, so each opens at
    /// its own first nonzero covector (the deposit's law for a coordinate with no history): a strength's covector sums a pairing over every
    /// marked site and coordinate, and no standing block's second moment is its scale (agent-inferred). Its rate: the founded parts' rates are
    /// kept and the mark's part takes octave 0, what a newly grown block takes in this line; where the learner carries each entry's own rate,
    /// every standing entry keeps it and the strengths take `rate_bits`. The draws, the laps and the pass are kept; the held step and the last
    /// section's step are dropped. Refused while a step is held.
    pub fn with_mark(&self) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner reads twice after its held step is read");
        }
        let (field, from) = self.field.with_mark()?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let second = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        let rate_parts = self.rate_parts.map(|rp| {
            let mut octaves = rp.octaves;
            octaves[MARK_PART] = 0;
            RateParts { octaves, ..rp }
        });
        let own_rates = self.own_rates.as_ref().map(|own| from.iter().map(|o| o.map_or(self.rate_bits, |i| own[i])).collect());
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn: self.drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; Brandon, November 15 02:06Z] **The learner whose face reads its sites' loudness** ([`Constitution::with_loud`]): the new block's
    /// moments open at zero, so its first step is its own covector's, and its part's rate at the old entries'. Refused while a step is held.
    pub fn with_loud(&self) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner reads its sites' loudness after its held step is read");
        }
        let (field, from) = self.field.with_loud()?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let second = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        let rate_parts = self.rate_parts.map(|rp| {
            let mut octaves = rp.octaves;
            octaves[LOUD_PART] = 0;
            RateParts { octaves, ..rp }
        });
        let own_rates = self.own_rates.as_ref().map(|own| from.iter().map(|o| o.map_or(self.rate_bits, |i| own[i])).collect());
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn: self.drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; theory, November 12 (the record of the opening's room, §4 item 4)] **The learner with `fresh` more letters**
    /// ([`Constitution::lettered`]), founded at a passage's crossing. No key is read and the draws do not move. Every standing entry keeps its
    /// moments and its remainder (the open rows' with them, at their new place); a fresh entry's first moment opens at zero and its second
    /// at the mean of its family's standing second moments, as a growth in contacts opens a new contact's ([`Learner::contacted`]), so its
    /// first step is its covector over its family's own scale and never the largest normalized step of a fresh entry. The founded parts'
    /// rates are kept, and where the learner carries each entry's own rate ([`Learner::own_rates`]) every standing entry keeps it and a
    /// fresh one takes `rate_bits`. The held step and the last section's step, of the old layout, are dropped; the pass is kept. Refused while
    /// a step is held.
    pub fn lettered(&self, fresh: usize) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner takes letters after its held step is read");
        }
        let (field, from) = self.field.lettered(fresh)?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let mut second: Vec<i128> = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        for &(start, len, _) in field.families_all().iter() {
            let old: Vec<i128> = (start..start + len).filter_map(|k| from[k].map(|i| self.second[i])).collect();
            if old.len() == len || old.is_empty() {
                continue;
            }
            // The mean term by term (each second moment is under `2^126`, so a family's sum is not formed).
            let n = old.len() as i128;
            let mean = old.iter().map(|v| v / n).sum::<i128>() + old.iter().map(|v| v % n).sum::<i128>() / n;
            for k in (start..start + len).filter(|&k| from[k].is_none()) {
                second[k] = mean;
            }
        }
        let own_rates = self.own_rates.as_ref().map(|own| from.iter().map(|o| o.map_or(self.rate_bits, |i| own[i])).collect());
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn: self.drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts: self.rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; theory, November 10 09:55] **The learner with `added` more pair contacts** ([`Constitution::contacted`]), the
    /// contacts' draws read from the founding key stream past every draw read before. Every old entry keeps its moments and its
    /// remainder, and the families' lengths (the families are the same ones); each new contact's entries open on the moments the
    /// lane's open on ([`Learner::laned`]): the first at zero, the second at the mean of the family's old second moments, so a
    /// new contact's first step is an eighth of its covector over the family's own scale, the step its family's trained entries
    /// take, and not the largest normalized step of a fresh entry. The rate is kept: no coordinate is shared among copies. The step
    /// the last section stood at is of the old layout and is dropped, as every growth drops it.
    pub fn contacted(&self, added: usize, keys: &[u8]) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner grows its contacts after its held step is read");
        }
        let rest = keys.get(self.drawn..).ok_or(TowerError::Refused("fewer key bytes than the new contacts' draws"))?;
        let (field, from) = self.field.contacted(added, rest)?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let mut second: Vec<i128> = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        for &(start, len, _) in field.families_all().iter() {
            let old: Vec<i128> = (start..start + len).filter_map(|k| from[k].map(|i| self.second[i])).collect();
            if old.len() == len || old.is_empty() {
                continue;
            }
            // The mean term by term (each second moment is under `2^126`, so a family's sum is not formed).
            let n = old.len() as i128;
            let mean = old.iter().map(|v| v / n).sum::<i128>() + old.iter().map(|v| v % n).sum::<i128>() / n;
            for k in (start..start + len).filter(|&k| from[k].is_none()) {
                second[k] = mean;
            }
        }
        let drawn = self.drawn + 4 * self.field.declaration.contact_draws(added);
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts: None, own_rates: None, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; agent-inferred, November 3, the tower record] **The learner grown in scale**: its field grown in scale
    /// ([`Constitution::scaled_up`], the key stream read on from the learner's drawn bytes), its moments kept on the fine field's
    /// material and opened at zero on the packets' field's and the glue's, which every coordinate opens at its own first
    /// nonzero covector.
    pub fn scaled_up(&self, harmonics: usize, split: usize, declaration: Declaration, keys: &[u8]) -> Result<Self> {
        let (field, drawn) = self.field.scaled_up(harmonics, split, declaration, keys, self.drawn)?;
        let len = field.material_len();
        let (mut first, mut second) = (self.first.clone(), self.second.clone());
        first.resize(len, 0);
        second.resize(len, 0);
        // [November 13, G145; the November 11 failure of a state tool that dropped the part rates] The fine field's entries keep the rates the
        // line carries (its parts' octaves, or each entry's own rate); the level's entries open at the base rate.
        let own_rates = self.own_rates.as_ref().map(|own| {
            let mut out = own.clone();
            out.resize(len, self.rate_bits);
            out
        });
        Ok(Self { remainder: self.remainder.as_ref().map(|_| vec![0; field.material_len()]), field, first, second, rate_bits: self.rate_bits, drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts: self.rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }

    /// [definition; the lead, November 18, the record of the two streams §11] **The learner whose level is opened to one-sided streams**
    /// ([`Constitution::level_before`]): the block `B⁻`, `b_B⁻` at zero after the glue, the material's last entries; its moments open at
    /// zero there and every other entry, moment, rate and line is kept (an entry's own rate, where the state carries them, opens at
    /// the base rate; the step's remainder, where carried, keeps its entries and opens at zero).
    pub fn level_before(&self) -> Result<Self> {
        let field = self.field.level_before()?;
        let len = field.material_len();
        let (mut first, mut second) = (self.first.clone(), self.second.clone());
        first.resize(len, 0);
        second.resize(len, 0);
        let own_rates = self.own_rates.as_ref().map(|own| {
            let mut out = own.clone();
            out.resize(len, self.rate_bits);
            out
        });
        let remainder = self.remainder.as_ref().map(|r| {
            let mut out = r.clone();
            out.resize(len, 0);
            out
        });
        Ok(Self { remainder, field, first, second, rate_bits: self.rate_bits, drawn: self.drawn, laps: self.laps, held: None, read_held: self.read_held, rate_parts: self.rate_parts, own_rates, leak: self.leak, last: None, pass: self.pass.clone() })
    }
}
