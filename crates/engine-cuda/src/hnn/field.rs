//! **The field's card realization** (`holonics_engine::field`, lifted from `hnn::tower::field` by C3 of #603; #404, #407; records
//! `2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN`,
//! §7, and `2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP`,
//! §6).
//!
//! [definition; agent-inferred, November 1] `Resident` implements [`Realization`]: a section's
//! regions read forward through the `K` ticks of the one constitution and returned exactly, and the
//! certificate's rereads, bit for bit the host's [`holonics_engine::field::Host`]
//! (`kernels/field.cu`). The work is laid out as the field is: a site is its global index in a
//! batch of regions, each region keeping its own length (no region is padded to another's), a
//! contact row is a head and a receiving site (one warp a row, its lanes over the site's support:
//! its near field and its resonance class, listed on the card each tick by a stable counting sort),
//! and a region's weights `e_ij` are its own block of the weight store, written and read only on the
//! support. The material, the regions' classes, resolutions and carried mixtures cross to the card;
//! the faces (or the logits) of the unresolved sites and the covector cross back. Every tick's
//! carriers stay on the card through the reverse.
//!
//! [agent-inferred, November 1] **Memory: the weights are kept at their dense address, the regions
//! batched by the card's measured memory.** A region of `S` sites reserves `H·S²` weights on `u64` a
//! kept tick, the address `[i][j]` a column's return reads `e_ij` at without an index; only the
//! support's entries are written and read, so the time follows the pairs met, and the reservation
//! is the most a region's classes can ask (every site of one class). The reverse reads them twice
//! (the values' and the contact's returns), so they are kept rather than recomputed; the contact's
//! return `δs_ij` is held for one head at a time (`S²` on 128 bits). A section's
//! regions are read in batches whose every allocation (the weights, the contact's return and each
//! site's carriers) fits the batch budget, the card's free memory at the open less a margin for the
//! driver, never past the 12 GB the runs keep to.
//! Batches sum their covectors on the card (integer sums: any batching gives the same bits).

#[allow(unused_imports)]
use core::ffi::c_void;
#[allow(unused_imports)]
use std::time::Instant;
#[allow(unused_imports)]
use holonics_engine::field::{band_bits, landmarks_of, BlankClocks, CarryGates, Constitution, Declaration, ReadLogits, Realization, HeldRows, NearOffsets, RealizationCounters, RowCurrent, Region, Scale, TickRead, NEAR, SHARE_BITS, STATE_BITS};
#[allow(unused_imports)]
use holonics_engine::field::{level_cut, level_section, PACE_BITS};
#[allow(unused_imports)]
use holonics_engine::field::{TowerError, TowerFace, MATERIAL_BITS};
#[allow(unused_imports)]
use crate::cuda::{Dim3, Module};
#[allow(unused_imports)]
use crate::hnn::card::{Card, CardBuffer, CardError};

pub use crate::hnn::resident::*;
pub(crate) use crate::hnn::moment::*;
pub use crate::hnn::contact::*;
pub(crate) use crate::hnn::carry::*;
pub use crate::hnn::clock::*;
pub(crate) use crate::hnn::adjoint::*;
pub(crate) use crate::hnn::level::*;
pub use crate::hnn::profile::*;


#[cfg(test)]
mod tests {
    use super::*;
    use holonics_engine::contact::WEIGHT_BITS;

    fn declaration(width: usize, heads: usize, contacts: usize) -> Declaration {
        Declaration { alphabet: 122, width, heads, modes: 8, still: 2, contacts, ticks: 2, frames: 4, reach: 2221, lanes: 1, depth: 0, carry: 0, triads: 0, opening: false, junction: false, mark: false, loud: false, crossing: false, closed: 0, pump: false, lane_leak: false, friction: false, friction_gate: false, fade: false, fade_rate: false, twin: false }
    }

    /// [measurement; theory, November 10 20:34] **The card's footprint by growth route** (host arithmetic, no card read): from the
    /// main line's declaration (width 64 in two lanes, 64 contacts, four heads of eight modes, four ticks, reach 3,771, 100 classes), each
    /// growth route at two and four times (`contacts`: f; `lane`: lanes, the width a lane's coordinates more each; `width`:
    /// [`Declaration::grown`], the width, the contacts and the lanes by the factor): the material's length, whether every affine map
    /// of the declaration still tiles a block (`affine_tiling`: the contacts' rows and the width's rows are a block's threads at most),
    /// and the octets of the longest region (a return at the reach's 3,771 sites) and of one thousand. Printed as `ROUTE` lines; ignored
    /// by default, run with `--ignored --nocapture`.

    #[test]
    #[ignore]
    fn the_card_footprint_by_growth_route() {
        let base = Declaration { alphabet: 100, width: 64, heads: 4, modes: 8, still: 2, contacts: 64, ticks: 4, frames: 4, reach: 3771, lanes: 2, depth: 0, carry: 0, triads: 0, opening: false, junction: false, mark: false, loud: false, crossing: false, closed: 0, pump: false, lane_leak: false, friction: false, friction_gate: false, fade: false, fade_rate: false, twin: false };
        let describe = |name: &str, d: Declaration| {
            let draws = 4 * d.founding_draws();
            let field = holonics_engine::field::Constitution::found(d, &vec![7u8; draws]).expect("founded");
            let (m2, dw, f) = (2 * d.complex(), d.width, d.contacts);
            // [P61] Every map takes the tile form, whatever its shape.
            let tiled: Vec<String> = [(m2, dw), (dw, m2), (f, dw), (dw, f), (dw, dw)].iter().map(|&(r, c)| format!("{r}x{c}:tile")).collect();
            println!("ROUTE {name} width={dw} lanes={} contacts={f} material={} tiles[{}] region_3771_octets={} region_1000_octets={} site_octets={}", d.lanes, field.material_len(), tiled.join(" "), region_octets(&d, true, 3771, 3771), region_octets(&d, true, 1000, 1000), (region_octets(&d, true, 1001, 1001) - region_octets(&d, true, 1000, 1000)));
        };
        describe("base", base);
        for k in [2usize, 4] {
            describe(&format!("contacts x{k}"), Declaration { contacts: base.contacts * k, ..base });
            let mut laned = base;
            for _ in 0..(k - 1) * base.lanes {
                laned = laned.laned().expect("laned");
            }
            describe(&format!("lane x{k}"), laned);
            describe(&format!("width x{k}"), base.grown(k).expect("grown"));
        }
    }

    /// Every region is in one batch, in order, each batch within the budget; a region past the budget
    /// alone is refused.
    #[test]
    fn batches_cover_the_regions_in_order_within_the_budget() {
        let d = declaration(32, 4, 32);
        let lengths = [1412, 300, 2221, 64, 900, 1229, 1229, 77];
        for returning in [false, true] {
            let octets = |n: usize| region_octets(&d, returning, n, n);
            let budget = octets(2221) + octets(900);
            let plan = batches(&lengths, &octets, budget).unwrap();
            assert_eq!(plan.first().unwrap().start, 0);
            assert_eq!(plan.last().unwrap().end, lengths.len());
            for w in plan.windows(2) {
                assert_eq!(w[0].end, w[1].start);
            }
            for b in &plan {
                assert!(!b.is_empty() && lengths[b.clone()].iter().map(|&n| octets(n)).sum::<u64>() <= budget);
            }
            assert!(batches(&lengths, &octets, octets(2221) - 1).is_err());
        }
        assert!(batches(&[], &|n| n as u64, 1).unwrap().is_empty());
    }

    /// The carrier follows the spread read and is the declaration's `row_bits` at its bound: a row of the
    /// widest spread the declaration allows needs exactly `row_bits`, one past it is refused.
    #[test]
    fn the_carrier_follows_the_spread_and_ends_at_the_declarations_bound() {
        let d = declaration(32, 4, 32);
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let field = Constitution::found(d, &keys).unwrap();
        // The gain is read from the largest temperature the material holds (§15.10).
        let bound = field.row_gain().unwrap() + (usize::BITS - 1 - d.reach.leading_zeros()) as u64 + 2;
        // The card weighs a source by one where the host weighs it by `2^62`, so its carrier is the bound less those bits; the
        // refusal stays the host's, at its own need.
        let host = field.row_bits().unwrap() as usize;
        assert_eq!(row_limbs(&field, bound).ok(), Some((host - WEIGHT_BITS as usize).div_ceil(64).max(MIN_LIMBS)).filter(|_| host.div_ceil(64) <= MAX_LIMBS));
        assert!(row_limbs(&field, bound + 1).is_err());
        // A narrow row needs three limbs at least, and the carrier never narrows as the spread widens.
        let mut last = 0;
        for spread in (0..=bound).step_by(7) {
            if let Ok(limbs) = row_limbs(&field, spread) {
                assert!(limbs >= last.max(MIN_LIMBS));
                last = limbs;
            }
        }
        assert_eq!(row_limbs(&field, 0).unwrap(), MIN_LIMBS);
    }

    /// A region's allocations count its weights, its contact's return on a return, and every site's
    /// carriers beside them: a release batch of 128 regions at the reach carries some 3 GB of them at
    /// the grown declaration, which the weights alone never counted.
    #[test]
    fn a_size_class_holds_its_length_within_a_quarter_in_whole_memset_words() {
        for len in (1..5000usize).chain([1 << 20, (1 << 20) + 1, 3_000_001]) {
            let class = size_class(len);
            assert!(class >= len && class % 4 == 0, "{len} {class}");
            // (below 17 elements the memset's four-word step is the whole class)
            assert!(len < 17 || class * 4 <= len * 5, "{len} {class}");
            assert_eq!(size_class(class), class, "{len}");
        }
    }

    #[test]
    fn a_regions_octets_count_its_carriers_beside_its_weights() {
        for d in [declaration(32, 4, 32), declaration(64, 8, 64)] {
            let n = 1504u64;
            // The scores and shares (a word a pair) are kept a tick for a return, with the reverse's covector a
            // pair on 64 bits, and one tick's otherwise; each kept tick adds its carrier widths and class offsets. The clock's skins
            // (P50 step 1, P51) are one store a batch, 32 bits a paced head, support entry and mode, `K = NEAR_SLOTS + definite` entries a row:
            // with every site definite, `n²` entries grow by pair and the near slots and the crowd edges by site.
            let skins = 4 * d.paced_heads() as u64 * d.modes as u64 * n * n;
            let weights = |returning: bool| skins + if returning { d.ticks as u64 * d.heads as u64 * 16 * n * n + 24 * n * n } else { d.heads as u64 * 8 * n * n };
            let fixed = |returning: bool| tick_fixed_octets(&d) * if returning { d.ticks as u64 } else { 1 };
            for returning in [false, true] {
                let all = region_octets(&d, returning, n as usize, n as usize);
                assert!(all > weights(returning) + fixed(returning));
                // The carriers grow by site, the weights by pair.
                let carriers = all - weights(returning) - fixed(returning);
                assert_eq!(region_octets(&d, returning, 2 * n as usize, 2 * n as usize) - 4 * weights(returning) - fixed(returning), 2 * carriers);
            }
        }
        let grown = declaration(64, 8, 64);
        let carriers = 128 * 1504 * (region_octets(&grown, false, 1, 1) - tick_fixed_octets(&grown));
        assert!(carriers > 1 << 30, "{carriers}");
    }

    /// [theory, November 12; the triad record §4] **The triads' maps tile on the main line's declaration** (host arithmetic, no card read): at
    /// `D = 64`, `f = 128` and `J = 16`, the triads' chart (`6J × D` over the pair chart's 32-bit read) tiles as every chart does, and the return of two
    /// blocks (`D × f` over `c` beside `D × 2J` over `c^T`, 64-bit faces) tiles a block of four sites in 46,912 of the 49,152 shared octets, the weights
    /// at their odd strides (`f + 1`, `2J + 1`), the bias, the joint bounds on 128 bits and a pass's rows; a return past a block's shared memory is
    /// refused the tiles and read by the cell map, the same integers.
    #[test]
    fn the_triads_maps_tile_on_the_main_lines_declaration() {
        let (dw, f, triads) = (64usize, 128usize, 16usize);
        assert_eq!(affine_two_tiling(dw, f, 2 * triads), Some((4, 46_912)));
        let need = ((dw * (f + 1) + dw * (2 * triads + 1) + dw) * 4).div_ceil(16) * 16 + 4 * 16 + 4 * (f + 2 * triads) * 8;
        assert_eq!(need, 46_912);
        assert!(affine_two_tiling(dw, 4 * f, 2 * triads).is_none(), "a return past the shared memory reads by cells");
        assert!(affine_two_tiling(512, f, 2 * triads).is_none(), "more rows than a block's threads");
    }

    /// [theory, November 12; the triad record §4] **A region's octets count the triads' carriers, and none at `J = 0`**: a kept tick holds `abg`
    /// `[t][6J]`, `p` and `c^T` `[t][2J]` (80 J octets a site) and a return adds `δc^T` and `δabg` (64 J a site); at `J = 0` the count is the
    /// declaration's as before, term for term.
    #[test]
    fn a_regions_octets_count_the_triads_carriers() {
        let base = Declaration { carry: 32, ..declaration(64, 4, 128) };
        let triads = 16u64;
        let d = Declaration { triads: triads as usize, ..base };
        for n in [2usize, 1504, 3771] {
            let s = n as u64;
            assert_eq!(region_octets(&d, false, n, n) - region_octets(&base, false, n, n), s * 80 * triads);
            assert_eq!(region_octets(&d, true, n, n) - region_octets(&base, true, n, n), s * (base.ticks as u64 * 80 * triads + 64 * triads));
            assert_eq!(read_octets(&d, false, true, n) - read_octets(&base, false, true, n), s * base.ticks as u64 * 80 * triads);
        }
    }

    /// [measurement; Brandon, November 15 02:06Z] **The loud face on the card reads the host's bits** (needs the card): a field of
    /// `declaration(32, 4, 32)` grown by two carry circles and a second lane, whose face reads its sites' loudness
    /// ([`holonics_engine::field::Learner::with_loud`]), its readout and current moved off zero from a keyed stream's tail and the loudness's
    /// `κ` and `b` off the founding, read and returned on regions of 2, 3, 5, 64 and 257 sites through the host and through the card: every face,
    /// every logit and every covector entry equal, the loudness's covector nonzero, and the lanes' powers by stage equal.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_loud_face_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::Learner;
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let mut field = Learner::new(founded, 12).with_carry(2, &keys).unwrap().laned(&keys).unwrap().with_loud().unwrap().field;
        let d = field.declaration;
        let (l, dw, f, m2) = (field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        assert!(d.loud && d.lanes == 2);
        let moved: Vec<(usize, u32)> = (l.read..l.read + dw * dw).map(|i| (i, 14)).chain((l.out..l.out + dw * m2).map(|i| (i, 14))).chain((l.w..l.w + dw * f).map(|i| (i, 14))).collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &(i, shift)) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
        }
        for k in 0..d.lanes {
            field.theta[l.loud + k] = (1 << 13) - ((k as i32) << 11);
        }
        field.theta[l.loud + d.lanes] = -(1 << 12);
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n).collect()).collect();
        let regions: Vec<Region> = classes.iter().zip(&open).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
        assert_eq!(host_faces, card_faces, "the loud faces");
        let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g[i] != card_g[i]).collect();
        assert!(unequal.is_empty(), "{} covector entries differ, the first at {:?} (loud at {})", unequal.len(), unequal.first(), l.loud);
        assert!(host_g[l.loud..l.loud + d.lanes + 1].iter().all(|&v| v != 0), "the loudness takes a covector");
        assert_eq!(holonics_engine::field::Host.read_logits(&field, &regions).unwrap(), card_field.read_logits(&field, &regions).unwrap(), "the loud logits");
        let (card_sf, card_scales) = card_field.read_tick_scales(&field, &regions).unwrap();
        let (host_sf, host_scales) = holonics_engine::field::Host.read_tick_scales(&field, &regions).unwrap();
        assert!(card_sf == host_sf && card_scales == host_scales, "the lanes' powers by stage");
        println!("LOUD_PARITY covector_entries={} loud_covector={:?} faces_equal=1 covector_equal=1", card_g.len(), &card_g[l.loud..l.loud + d.lanes + 1]);
    }

    /// [definition; the lead, November 19 (G-1119-7)] **The pumped circles on the card read the host's bits** (needs the card): a field of
    /// `declaration(32, 4, 32)` grown by four carry circles and pumped ([`holonics_engine::field::Learner::with_pump`]), its readout, current and
    /// pair returns and the pump's chart and bias moved off zero from a keyed stream's tail (so every circle reflects at every site and the faces
    /// have a covector), read and returned through the host and through the card on regions of the law of 2, 3, 5, 64 and 257 sites, on passages
    /// read by two streams of 2, 3, 7, 64 and 300 places (their odd contacts facing the past on every second one), and on a section of both
    /// interleaved: every face and every covector entry equal, the pump's chart and bias with a covector, and a read that does not return equal.
    /// At the founding (the chart at zero) the card's faces and covector are the unpumped field's on every standing entry.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_pumped_circles_on_the_card_read_the_hosts_bits() {
        use holonics_engine::field::{Host, Learner, Realization};
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(3).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 13)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let circled = Learner::new(founded, 12).with_carry(4, &keys).unwrap();
        let pumped = circled.with_pump().unwrap();
        let mut field = pumped.field.clone();
        let d = field.declaration;
        let (l, dw, f, m2, c2) = (field.layout().clone(), d.width, d.contacts, 2 * d.complex(), 2 * d.carry);
        assert!(d.pump && d.carry == 4);
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n).collect()).collect();
        let law: Vec<Region> = classes.iter().zip(&open).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let strand_lengths = [2usize, 3, 7, 64, 300];
        let passages: Vec<Vec<usize>> = strand_lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 53 + 5 + 17 * k) % 120).collect()).collect();
        let known: Vec<Vec<bool>> = strand_lengths.iter().map(|&n| vec![false; n]).collect();
        let strands: Vec<Region> = passages.iter().zip(&known).enumerate().map(|(k, (c, u))| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past: k % 2 == 1, second: false, targets: None, stretches: None }).collect();
        let mixed: Vec<Region> = law.iter().zip(&strands).flat_map(|(a, b)| [*a, *b]).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        // At the founding: the card's pumped field is the unpumped field on every standing entry.
        for regions in [&law, &strands] {
            let (zero_faces, zero_g) = card_field.read_and_return(&field, regions).unwrap();
            let (plain_faces, plain_g) = card_field.read_and_return(&circled.field, regions).unwrap();
            assert_eq!(zero_faces, plain_faces, "at the founding every face is the unpumped field's");
            assert_eq!(zero_g[..circled.field.theta.len()], plain_g[..circled.field.theta.len()], "and every standing entry's covector");
        }
        // Each moved entry with its shift: the material's families on `2^(−24)`, the pump's bias on the face's grain, eight bits coarser.
        let moved: Vec<(usize, u32)> = (l.read..l.read + dw * dw)
            .map(|i| (i, 14))
            .chain((l.out..l.out + dw * m2).map(|i| (i, 14)))
            .chain((l.w..l.w + dw * f).map(|i| (i, 14)))
            .chain((l.pump..l.pump + c2 * dw).map(|i| (i, 8)))
            .chain((l.pump_bias..l.pump_bias + c2).map(|i| (i, 16)))
            .collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &(i, shift)) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
        }
        for (section, regions) in [("law", &law), ("strands", &strands), ("mixed", &mixed)] {
            let (host_faces, host_g) = field.read_and_return(regions).unwrap();
            let (card_faces, card_g) = card_field.read_and_return(&field, regions).unwrap();
            let (hf, cf) = (&host_faces, &card_faces);
            let apart: Vec<(usize, usize)> = (0..regions.len()).flat_map(|r| (0..hf[r].len().max(cf[r].len())).filter(move |&t| hf[r].get(t) != cf[r].get(t)).map(move |t| (r, t))).collect();
            assert!(apart.is_empty(), "{section}: {} faces differ, the first at region and place {:?}", apart.len(), apart.first());
            let unequal: Vec<usize> = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
            assert!(unequal.is_empty(), "{section}: {} covector entries differ, the first at {:?} (pump at {}, pump_bias at {}, carry at {})", unequal.len(), unequal.first(), l.pump, l.pump_bias, l.carry);
            assert!(host_g[l.pump..l.pump + c2 * dw].iter().any(|&v| v != 0) && host_g[l.pump_bias..l.pump_bias + c2].iter().any(|&v| v != 0), "{section}: the pump's chart and bias take a covector");
            assert_eq!(Host.read_faces(&field, regions).unwrap(), card_field.read_faces(&field, regions).unwrap(), "{section}: a read that does not return");
            println!("PUMP_PARITY section={section} regions={} covector_entries={} pump_covector_nonzero={} faces_equal=1 covector_equal=1", regions.len(), card_g.len(), host_g[l.pump..l.pump_bias + c2].iter().filter(|&&v| v != 0).count());
        }
    }

    /// [definition; the lead, November 23, play] **A passage read by two streams and compared with its own targets on the card reads the
    /// host's bits** (needs the card; `Region::targets`): a pumped field with carry circles, its read, readout and pair returns moved off zero
    /// from a keyed stream's tail, read and returned on passages of 2, 3, 7, 64 and 300 places whose open places are compared with a second
    /// keyed sequence, through the host and through the card: every face and every covector entry equal. The faces are the passages' own
    /// without targets (the known stream alone moves a face), and the covector is not (the targets move the comparison); targets equal to the
    /// known stream give the covector of none.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn a_strand_compared_with_its_targets_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::{Learner, Realization};
        let keys: Vec<u8> = (0..262_144u64).flat_map(|i| (i.wrapping_add(3).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_right(holonics_engine::field::FACE_BITS)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let pumped = Learner::new(founded, 12).with_carry(4, &keys).unwrap().with_pump().unwrap();
        let mut field = pumped.field.clone();
        let (l, dw, m2) = (field.layout().clone(), field.declaration.width, 2 * field.declaration.complex());
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).collect();
        // (each moved entry on the material's families' `2^(−24)` less ten places, as the pump's test moves its material)
        let (tail, shift) = (keys.len() - 4 * moved.len() - 8, 14u32);
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
        }
        let lengths = [2usize, 3, 7, 64, 300];
        let passages: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 53 + 5 + 17 * k) % 120).collect()).collect();
        let targets: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 29 + 7 + 13 * k) % 120).collect()).collect();
        let known: Vec<Vec<bool>> = lengths.iter().map(|&n| vec![false; n]).collect();
        fn strand<'a>(classes: &'a [usize], unresolved: &'a [bool], past: bool, with: Option<&'a [usize]>) -> Region<'a> {
            Region { classes, unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past, second: false, targets: with, stretches: None }
        }
        let plain: Vec<Region> = (0..lengths.len()).map(|k| strand(&passages[k], &known[k], k % 2 == 1, None)).collect();
        let aimed: Vec<Region> = (0..lengths.len()).map(|k| strand(&passages[k], &known[k], k % 2 == 1, Some(&targets[k]))).collect();
        let itself: Vec<Region> = (0..lengths.len()).map(|k| strand(&passages[k], &known[k], k % 2 == 1, Some(&passages[k]))).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        let (host_faces, host_g) = field.read_and_return(&aimed).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&field, &aimed).unwrap();
        assert_eq!(host_faces, card_faces, "every face of a strand compared with its targets");
        let unequal = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).count();
        assert_eq!(unequal, 0, "every covector entry of a strand compared with its targets");
        let (plain_faces, plain_g) = card_field.read_and_return(&field, &plain).unwrap();
        assert_eq!(plain_faces, card_faces, "the targets move no face");
        assert_ne!(plain_g, card_g, "the targets move the comparison");
        let (_, itself_g) = card_field.read_and_return(&field, &itself).unwrap();
        assert_eq!(itself_g, plain_g, "targets equal to the known stream are none");
        println!("STRAND_TARGETS_PARITY regions={} covector_entries={} faces_equal=1 covector_equal=1", aimed.len(), card_g.len());
    }

    /// [definition; the lead, November 25] **The classes' fade rates on the card read the host's bits** (needs the card;
    /// `Declaration::fade_rate`): the targets' parity field with its fade rates founded at zero reads every face and covector entry of the field
    /// without them, and with the rates drawn off zero the card's faces and every covector entry, the rates' among them, are the host's, on
    /// strands compared with targets and on regions with open places.
    #[test]
    #[ignore]
    fn the_classes_fade_rates_on_the_card_read_the_hosts_bits() {
        use holonics_engine::field::Learner;
        let keys: Vec<u8> = (0..262_144u64).flat_map(|i| (i.wrapping_add(3).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_right(holonics_engine::field::FACE_BITS)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let carried = Learner::new(founded, 12).with_carry(4, &keys).unwrap();
        let mut plain = carried.field.clone();
        let (l, dw, m2) = (plain.layout().clone(), plain.declaration.width, 2 * plain.declaration.complex());
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.pace..l.pace + plain.declaration.paced_heads() * (plain.declaration.alphabet + 1)).collect();
        let (tail, shift) = (keys.len() - 4 * moved.len() - 8, 14u32);
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            plain.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
        }
        let (zero, _) = plain.with_fade_rate().unwrap();
        let lengths = [2usize, 3, 7, 64, 300];
        let passages: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 53 + 5 + 17 * k) % 120).collect()).collect();
        let targets: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 29 + 7 + 13 * k) % 120).collect()).collect();
        let known: Vec<Vec<bool>> = lengths.iter().map(|&n| vec![false; n]).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1).collect()).collect();
        let strands: Vec<Region> = (0..lengths.len()).map(|k| Region { classes: &passages[k], unresolved: &known[k], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past: k % 2 == 1, second: false, targets: Some(&targets[k]), stretches: None }).collect();
        let regions: Vec<Region> = (0..lengths.len()).map(|k| Region { classes: &passages[k], unresolved: &open[k], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        for (which, batch) in [("strands", &strands), ("regions", &regions)] {
            let (plain_faces, plain_g) = card_field.read_and_return(&plain, batch).unwrap();
            let (zero_faces, zero_g) = card_field.read_and_return(&zero, batch).unwrap();
            assert_eq!(plain_faces, zero_faces, "{which}: the rates founded at zero keep every face on the card");
            assert_eq!(&zero_g[..plain_g.len()], &plain_g[..], "{which}: and every standing covector entry");
        }
        let mut field = zero.clone();
        let rows = field.declaration.paced_heads() * (field.declaration.alphabet + 1);
        let fl = field.layout().clone();
        for (k, v) in field.theta[fl.fade_rate..fl.fade_rate + rows].iter_mut().enumerate() {
            let one = 1i32 << MATERIAL_BITS;
            *v = [-one / 4, one / 8, -3 * one / 8, one / 4, -one / 2][k % 5];
        }
        for (which, batch) in [("strands", &strands), ("regions", &regions)] {
            let (host_faces, host_g) = field.read_and_return(batch).unwrap();
            let (card_faces, card_g) = card_field.read_and_return(&field, batch).unwrap();
            assert_eq!(host_faces, card_faces, "{which}: every face with the rates drawn");
            let unequal: Vec<usize> = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
            let rates: Vec<(i128, i128)> = (fl.fade_rate..fl.fade_rate + rows).map(|i| (host_g[i], card_g[i])).collect();
            println!("FADE_RATE_PARITY {which} unequal={} first={:?} rates={:?}", unequal.len(), unequal.first(), &rates[..rates.len().min(4)]);
            assert!(rates.iter().any(|&(h, _)| h != 0), "{which}: the rates take a covector");
            assert_eq!(unequal.len(), 0, "{which}: every covector entry with the rates drawn");
        }
    }

    /// [definition; the lead, November 24] **The rings' fades on the card read the host's bits** (needs the card; `Declaration::fade`): the
    /// targets' parity field with its rings' fades founded at zero reads every face and covector entry of the field without them, and with the
    /// fades drawn off zero (slower and faster, ring by ring) the card's faces and every covector entry, the fades' among them, are the host's,
    /// on strands compared with targets and on regions with open places.
    #[test]
    #[ignore]
    fn the_rings_fades_on_the_card_read_the_hosts_bits() {
        use holonics_engine::field::Learner;
        let keys: Vec<u8> = (0..262_144u64).flat_map(|i| (i.wrapping_add(3).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_right(holonics_engine::field::FACE_BITS)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let carried = Learner::new(founded, 12).with_carry(4, &keys).unwrap();
        let mut plain = carried.field.clone();
        let (l, dw, m2) = (plain.layout().clone(), plain.declaration.width, 2 * plain.declaration.complex());
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).collect();
        let (tail, shift) = (keys.len() - 4 * moved.len() - 8, 14u32);
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            plain.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
        }
        let (zero, _) = plain.with_fade(2, 0).unwrap();
        let lengths = [2usize, 3, 7, 64, 300];
        let passages: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 53 + 5 + 17 * k) % 120).collect()).collect();
        let targets: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 29 + 7 + 13 * k) % 120).collect()).collect();
        let known: Vec<Vec<bool>> = lengths.iter().map(|&n| vec![false; n]).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1).collect()).collect();
        let strands: Vec<Region> = (0..lengths.len()).map(|k| Region { classes: &passages[k], unresolved: &known[k], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past: k % 2 == 1, second: false, targets: Some(&targets[k]), stretches: None }).collect();
        let regions: Vec<Region> = (0..lengths.len()).map(|k| Region { classes: &passages[k], unresolved: &open[k], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        for (which, batch) in [("strands", &strands), ("regions", &regions)] {
            let (plain_faces, plain_g) = card_field.read_and_return(&plain, batch).unwrap();
            let (zero_faces, zero_g) = card_field.read_and_return(&zero, batch).unwrap();
            assert_eq!(plain_faces, zero_faces, "{which}: the fades founded at zero keep every face on the card");
            assert_eq!(&zero_g[..plain_g.len()], &plain_g[..], "{which}: and every standing covector entry");
        }
        let mut field = zero.clone();
        let slots = field.declaration.turned_slots();
        for (k, v) in field.theta[l.fade..l.fade + slots].iter_mut().enumerate() {
            let one = 1i32 << MATERIAL_BITS;
            *v = [-one / 2, one / 4, -3 * one / 4, one / 2, -one][k % 5];
        }
        field.refresh_fade().unwrap();
        for (which, batch) in [("strands", &strands), ("regions", &regions)] {
            let (host_faces, host_g) = field.read_and_return(batch).unwrap();
            let (card_faces, card_g) = card_field.read_and_return(&field, batch).unwrap();
            assert_eq!(host_faces, card_faces, "{which}: every face with the fades drawn");
            let unequal: Vec<usize> = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
            let fades: Vec<(i128, i128)> = (l.fade..l.fade + slots).map(|i| (host_g[i], card_g[i])).collect();
            println!("FADE_PARITY {which} unequal={} first={:?} fades={:?}", unequal.len(), unequal.first(), &fades[..fades.len().min(4)]);
            assert!(fades.iter().any(|&(h, _)| h != 0), "{which}: the fades take a covector");
            assert_eq!(unequal.len(), 0, "{which}: every covector entry with the fades drawn");
        }
    }

    /// [definition; the lead, November 25] **The rings' second fades on the card read the host's bits** (needs the card; `Declaration::twin`):
    /// on the targets' parity field, on it with the opening compared, and on that with the mark and the rings' first fades (the line's parts),
    /// the second fades founded with their chart at zero read every face and covector entry of the field without them, and with the chart drawn
    /// off zero and the second fades spread about their founding the card's faces and every covector entry, the chart's and the second fades'
    /// among them, are the host's, on strands compared with targets and on regions with open places.
    #[test]
    #[ignore]
    fn the_rings_second_fades_on_the_card_read_the_hosts_bits() {
        use holonics_engine::field::Learner;
        let keys: Vec<u8> = (0..262_144u64).flat_map(|i| (i.wrapping_add(3).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_right(holonics_engine::field::FACE_BITS)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let carried = Learner::new(founded, 12).with_carry(4, &keys).unwrap();
        let one = 1i32 << MATERIAL_BITS;
        let half_a_turn = -(51 * one) / 16;
        let opened = carried.clone().with_opening().unwrap();
        let marked = opened.clone().with_mark().unwrap().with_fade(2, -one / 2).unwrap();
        let lengths = [2usize, 3, 7, 64, 300];
        let passages: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 53 + 5 + 17 * k) % 120).collect()).collect();
        let targets: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 29 + 7 + 13 * k) % 120).collect()).collect();
        let known: Vec<Vec<bool>> = lengths.iter().map(|&n| vec![false; n]).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1).collect()).collect();
        let strands: Vec<Region> = (0..lengths.len()).map(|k| Region { classes: &passages[k], unresolved: &known[k], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past: k % 2 == 1, second: false, targets: Some(&targets[k]), stretches: None }).collect();
        let regions: Vec<Region> = (0..lengths.len()).map(|k| Region { classes: &passages[k], unresolved: &open[k], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        for (case, learner) in [("carried", &carried), ("opened", &opened), ("opened, marked, faded", &marked)] {
            let mut plain = learner.field.clone();
            let (l, dw, m2) = (plain.layout().clone(), plain.declaration.width, 2 * plain.declaration.complex());
            // The readout drawn as the fades' parity draws it, and the moments' encodings and chart drawn too (a founded field holds them at
            // zero, so its moments, and the second fades' with them, read nothing until a deposit moves them).
            let rows = 2 * (plain.declaration.alphabet + 1) * plain.declaration.moment_modes();
            let moved: Vec<(usize, u32)> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.moment_face..l.moment_face + dw * m2).map(|i| (i, 14u32)).chain((l.moment_before..l.moment_before + 2 * rows).map(|i| (i, 18u32))).collect();
            let tail = keys.len() - 4 * moved.len() - 8;
            for (k, &(i, shift)) in moved.iter().enumerate() {
                let word = &keys[tail + 4 * k..tail + 4 * k + 4];
                plain.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
            }
            let (zero, _) = plain.with_twin(half_a_turn).unwrap();
            for (which, batch) in [("strands", &strands), ("regions", &regions)] {
                let (plain_faces, plain_g) = card_field.read_and_return(&plain, batch).unwrap();
                let (zero_faces, zero_g) = card_field.read_and_return(&zero, batch).unwrap();
                assert_eq!(plain_faces, zero_faces, "{case}, {which}: the second fades founded with their chart at zero keep every face on the card");
                assert_eq!(&zero_g[..plain_g.len()], &plain_g[..], "{case}, {which}: and every standing covector entry");
            }
            let mut field = zero.clone();
            let l = field.layout().clone();
            for k in 0..dw * m2 {
                field.theta[l.twin_face + k] = field.theta[l.moment_face + k] / 2;
            }
            let slots = field.declaration.turned_slots();
            for (k, v) in field.theta[l.twin_fade..l.twin_fade + slots].iter_mut().enumerate() {
                *v += [-one / 4, one / 8, -3 * one / 8, one / 4, -one / 2][k % 5];
            }
            field.refresh_fade().unwrap();
            for (which, batch) in [("strands", &strands), ("regions", &regions)] {
                let (host_faces, host_g) = field.read_and_return(batch).unwrap();
                let (card_faces, card_g) = card_field.read_and_return(&field, batch).unwrap();
                assert_eq!(host_faces, card_faces, "{case}, {which}: every face with the second fades drawn");
                let unequal: Vec<usize> = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
                let fades: Vec<(i128, i128)> = (l.twin_fade..l.twin_fade + slots).map(|i| (host_g[i], card_g[i])).collect();
                let chart = (l.twin_face..l.twin_face + dw * m2).filter(|&i| host_g[i] != 0).count();
                let named = |i: usize| -> String {
                    if i >= l.twin_fade { format!("second fade {}", i - l.twin_fade) } else if i >= l.twin_face { format!("second chart {}", i - l.twin_face) } else if field.declaration.fade && i >= l.fade && i < l.fade + slots { format!("fade {}", i - l.fade) } else { format!("entry {i}") }
                };
                println!("TWIN_PARITY {case} {which} unequal={} first={:?} chart_nonzero={chart} fades={:?}", unequal.len(), unequal.first().map(|&i| (named(i), host_g[i], card_g[i])), &fades[..fades.len().min(4)]);
                assert!(fades.iter().any(|&(h, _)| h != 0) && chart > 0, "{case}, {which}: the second fades and their chart take a covector");
                assert_eq!(unequal.len(), 0, "{case}, {which}: every covector entry with the second fades drawn");
            }
        }
    }

    /// [definition; the lead, November 25, Fable's construction] **A passage read as its consecutive stretches on the card reads the host's
    /// bits** (needs the card; `Region::stretches`): on the targets' parity field with its moments drawn, and on it with the opening and the
    /// mark, strands compared with targets and read as two to four stretches give the host's faces and every covector entry, and differ
    /// from the same strands read as one stretch.
    #[test]
    #[ignore]
    fn a_passage_read_as_its_stretches_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::Learner;
        let keys: Vec<u8> = (0..262_144u64).flat_map(|i| (i.wrapping_add(3).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_right(holonics_engine::field::FACE_BITS)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let carried = Learner::new(founded, 12).with_carry(4, &keys).unwrap();
        let opened = carried.clone().with_opening().unwrap().with_mark().unwrap();
        let lengths = [7usize, 64, 300, 41];
        let starts: [&[usize]; 4] = [&[3], &[20, 41], &[100, 180, 250], &[6, 30]];
        let passages: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 53 + 5 + 17 * k) % 120).collect()).collect();
        let targets: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 29 + 7 + 13 * k) % 120).collect()).collect();
        let known: Vec<Vec<bool>> = lengths.iter().map(|&n| vec![false; n]).collect();
        let strands = |joined: bool| -> Vec<Region> { (0..lengths.len()).map(|k| Region { classes: &passages[k], unresolved: &known[k], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past: k % 2 == 1, second: false, targets: Some(&targets[k]), stretches: joined.then_some(starts[k]) }).collect() };
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        for (case, learner) in [("carried", &carried), ("opened and marked", &opened)] {
            let mut field = learner.field.clone();
            let (l, dw, m2) = (field.layout().clone(), field.declaration.width, 2 * field.declaration.complex());
            let rows = 2 * (field.declaration.alphabet + 1) * field.declaration.moment_modes();
            let moved: Vec<(usize, u32)> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.moment_face..l.moment_face + dw * m2).map(|i| (i, 14u32)).chain((l.moment_before..l.moment_before + 2 * rows).map(|i| (i, 18u32))).collect();
            let tail = keys.len() - 4 * moved.len() - 8;
            for (k, &(i, shift)) in moved.iter().enumerate() {
                let word = &keys[tail + 4 * k..tail + 4 * k + 4];
                field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
            }
            let (host_one, _) = field.read_and_return(&strands(false)).unwrap();
            let (host_faces, host_g) = field.read_and_return(&strands(true)).unwrap();
            let (card_faces, card_g) = card_field.read_and_return(&field, &strands(true)).unwrap();
            assert_ne!(host_faces, host_one, "{case}: the stretches move a face");
            assert_eq!(host_faces, card_faces, "{case}: every face read as stretches");
            let unequal: Vec<usize> = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
            println!("JOINED_PARITY {case} unequal={} first={:?}", unequal.len(), unequal.first().map(|&i| (i, host_g[i], card_g[i])));
            assert_eq!(unequal.len(), 0, "{case}: every covector entry read as stretches");
        }
    }

    /// [definition; the lead, November 23, an act answered in kind] **A strand with places read and not compared on the card reads the
    /// host's bits** (needs the card; `holonics_engine::field::UNCOMPARED`): the field and passages of the targets' parity, every third
    /// open place's target left out, on the field and on it with the opening compared (so the opening's comparison leaves them out too),
    /// read and returned through the host and through the card: every face and every covector entry equal, the faces those of the passages without
    /// targets, and a strand whose every place is left out returning nothing on the card.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn a_strand_with_places_read_and_not_compared_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::{Learner, Realization, UNCOMPARED};
        let keys: Vec<u8> = (0..262_144u64).flat_map(|i| (i.wrapping_add(3).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_right(holonics_engine::field::FACE_BITS)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        for opened in [false, true] {
        let carried = Learner::new(founded.clone(), 12).with_carry(4, &keys).unwrap();
        let pumped = if opened { carried.with_opening().unwrap().with_pump().unwrap() } else { carried.with_pump().unwrap() };
        let mut field = pumped.field.clone();
        let (l, dw, m2) = (field.layout().clone(), field.declaration.width, 2 * field.declaration.complex());
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).collect();
        let (tail, shift) = (keys.len() - 4 * moved.len() - 8, 14u32);
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
        }
        let lengths = [2usize, 3, 7, 64, 300];
        let passages: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 53 + 5 + 17 * k) % 120).collect()).collect();
        let targets: Vec<Vec<usize>> = passages.iter().enumerate().map(|(k, p)| p.iter().enumerate().map(|(t, &c)| if (t + k) % 3 == 1 { UNCOMPARED } else { c }).collect()).collect();
        let none: Vec<Vec<usize>> = lengths.iter().map(|&n| vec![UNCOMPARED; n]).collect();
        let known: Vec<Vec<bool>> = lengths.iter().map(|&n| vec![false; n]).collect();
        fn strand<'a>(classes: &'a [usize], unresolved: &'a [bool], past: bool, with: Option<&'a [usize]>) -> Region<'a> {
            Region { classes, unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past, second: false, targets: with, stretches: None }
        }
        let plain: Vec<Region> = (0..lengths.len()).map(|k| strand(&passages[k], &known[k], k % 2 == 1, None)).collect();
        let skipped: Vec<Region> = (0..lengths.len()).map(|k| strand(&passages[k], &known[k], k % 2 == 1, Some(&targets[k]))).collect();
        let silent: Vec<Region> = (0..lengths.len()).map(|k| strand(&passages[k], &known[k], k % 2 == 1, Some(&none[k]))).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        let (host_faces, host_g) = field.read_and_return(&skipped).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&field, &skipped).unwrap();
        assert_eq!(host_faces, card_faces, "every face of a strand with places left out");
        let unequal = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).count();
        assert_eq!(unequal, 0, "every covector entry of a strand with places left out (the opening compared: {opened})");
        let (plain_faces, plain_g) = card_field.read_and_return(&field, &plain).unwrap();
        assert_eq!(plain_faces, card_faces, "leaving places out moves no face");
        assert_ne!(plain_g, card_g, "leaving places out moves the comparison");
        let (_, silent_g) = card_field.read_and_return(&field, &silent).unwrap();
        assert!(silent_g.iter().all(|&v| v == 0), "a strand with every place left out returns nothing on the card");
        println!("STRAND_UNCOMPARED_PARITY opening={opened} regions={} covector_entries={} faces_equal=1 covector_equal=1", skipped.len(), card_g.len());
        }
    }

    /// [definition; the lead, November 21, the reach] **Each head's friction of distance on the card reads the host's bits** (needs the card): a
    /// field of `declaration(32, 4, 32)` grown by four carry circles, pumped, and given its frictions ([`holonics_engine::field::Learner::with_friction`]),
    /// its readout, current and pair returns moved off zero from a keyed stream's tail and its frictions drawn at a quarter of a bit to one bit an
    /// octave of either sign, read and returned through the host and through the card on regions of the law of 2, 3, 5, 64 and 257 sites (whose
    /// class receivers hear crowds), on passages read by two streams of 2, 3, 7, 64 and 300 places (their odd contacts facing the past on every
    /// second one), and on a section of both interleaved: every face and every covector entry equal, the frictions with a covector at both kinds,
    /// and a read that does not return equal. At the founding (the frictions at zero) the card's faces and covector are the field's without them
    /// on every standing entry.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_friction_of_distance_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::{Host, Learner, Realization};
        let keys: Vec<u8> = (0..262_144u64).flat_map(|i| (i.wrapping_add(5).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_right(holonics_engine::field::FACE_BITS)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let pumped = Learner::new(founded, 12).with_carry(4, &keys).unwrap().with_pump().unwrap();
        let frictioned = pumped.with_friction().unwrap();
        let mut field = frictioned.field.clone();
        let mut plain = pumped.field.clone();
        let d = field.declaration;
        let (l, dw, f, m2) = (field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        assert!(d.friction && d.pump);
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n).collect()).collect();
        let law: Vec<Region> = classes.iter().zip(&open).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let strand_lengths = [2usize, 3, 7, 64, 300];
        let passages: Vec<Vec<usize>> = strand_lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 53 + 5 + 17 * k) % 120).collect()).collect();
        let known: Vec<Vec<bool>> = strand_lengths.iter().map(|&n| vec![false; n]).collect();
        let strands: Vec<Region> = passages.iter().zip(&known).enumerate().map(|(k, (c, u))| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past: k % 2 == 1, second: false, targets: None, stretches: None }).collect();
        let mixed: Vec<Region> = law.iter().zip(&strands).flat_map(|(a, b)| [*a, *b]).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        // The readout, the current's and the pair's returns moved off zero in both fields alike, so the faces have a covector.
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.w..l.w + dw * f).collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            let v = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> (MATERIAL_BITS - 10);
            field.theta[i] = v;
            plain.theta[i] = v;
        }
        // At the founding: the card's field with its frictions at zero is the field without them on every standing entry.
        for regions in [&law, &strands] {
            let (zero_faces, zero_g) = card_field.read_and_return(&field, regions).unwrap();
            let (plain_faces, plain_g) = card_field.read_and_return(&plain, regions).unwrap();
            assert_eq!(zero_faces, plain_faces, "at the founding every face is the field's without the frictions");
            assert_eq!(zero_g[..plain.theta.len()], plain_g[..plain.theta.len()], "and every standing entry's covector");
        }
        for (n, v) in field.theta[l.friction..l.friction + 2 * d.heads].iter_mut().enumerate() {
            let bit = 1i32 << holonics_engine::field::FACE_BITS;
            *v = [bit / 4, -bit / 2, 3 * bit / 4, bit, -bit / 4, bit / 2, -3 * bit / 4, bit / 8][n % 8];
        }
        for (section, regions) in [("law", &law), ("strands", &strands), ("mixed", &mixed)] {
            let (host_faces, host_g) = field.read_and_return(regions).unwrap();
            let (card_faces, card_g) = card_field.read_and_return(&field, regions).unwrap();
            let (hf, cf) = (&host_faces, &card_faces);
            let apart: Vec<(usize, usize)> = (0..regions.len()).flat_map(|r| (0..hf[r].len().max(cf[r].len())).filter(move |&t| hf[r].get(t) != cf[r].get(t)).map(move |t| (r, t))).collect();
            assert!(apart.is_empty(), "{section}: {} faces differ, the first at region and place {:?}", apart.len(), apart.first());
            let unequal: Vec<usize> = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
            assert!(unequal.is_empty(), "{section}: {} covector entries differ, the first at {:?} (the frictions at {})", unequal.len(), unequal.first(), l.friction);
            let fr = &host_g[l.friction..l.friction + 2 * d.heads];
            assert!(fr.iter().step_by(2).any(|&v| v != 0) || section == "strands", "{section}: the class receivers' frictions take a covector");
            assert!(fr.iter().skip(1).step_by(2).any(|&v| v != 0), "{section}: the listeners' frictions take a covector");
            assert_eq!(Host.read_faces(&field, regions).unwrap(), card_field.read_faces(&field, regions).unwrap(), "{section}: a read that does not return");
            println!("FRICTION_PARITY section={section} regions={} covector_entries={} friction_covector={:?} faces_equal=1 covector_equal=1", regions.len(), card_g.len(), fr);
        }
    }

    /// [definition; the lead, November 21, the reach §6] **The friction read from the receiver's state on the card reads the host's bits** (needs
    /// the card): the field of [`the_friction_of_distance_on_the_card_reads_the_hosts_bits`] with the friction's gate founded and then drawn (a
    /// row of `D` a head from a keyed stream), read and returned through the host and through the card on the same regions, passages and
    /// section: every face and every covector entry equal, the gate with a covector; at the founding the card's faces and covector are the
    /// field's without the gate on every standing entry.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_friction_read_from_the_receivers_state_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::{Host, Learner, Realization};
        let keys: Vec<u8> = (0..262_144u64).flat_map(|i| (i.wrapping_add(5).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_right(holonics_engine::field::FACE_BITS)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let pumped = Learner::new(founded, 12).with_carry(4, &keys).unwrap().with_pump().unwrap();
        let frictioned = pumped.with_friction().unwrap().with_friction_gate().unwrap();
        let mut field = frictioned.field.clone();
        let mut plain = pumped.with_friction().unwrap().field.clone();
        let d = field.declaration;
        let (l, dw, f, m2) = (field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        assert!(d.friction && d.friction_gate && d.pump);
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n).collect()).collect();
        let law: Vec<Region> = classes.iter().zip(&open).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let strand_lengths = [2usize, 3, 7, 64, 300];
        let passages: Vec<Vec<usize>> = strand_lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 53 + 5 + 17 * k) % 120).collect()).collect();
        let known: Vec<Vec<bool>> = strand_lengths.iter().map(|&n| vec![false; n]).collect();
        let strands: Vec<Region> = passages.iter().zip(&known).enumerate().map(|(k, (c, u))| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past: k % 2 == 1, second: false, targets: None, stretches: None }).collect();
        let mixed: Vec<Region> = law.iter().zip(&strands).flat_map(|(a, b)| [*a, *b]).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        // The readout, the current's and the pair's returns moved off zero in both fields alike, so the faces have a covector.
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.w..l.w + dw * f).collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            let v = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> (MATERIAL_BITS - 10);
            field.theta[i] = v;
            plain.theta[i] = v;
        }
        // At the founding: the card's field with its frictions at zero is the field without them on every standing entry.
        for regions in [&law, &strands] {
            let (zero_faces, zero_g) = card_field.read_and_return(&field, regions).unwrap();
            let (plain_faces, plain_g) = card_field.read_and_return(&plain, regions).unwrap();
            assert_eq!(zero_faces, plain_faces, "at the founding every face is the field's without the gate");
            assert_eq!(zero_g[..plain.theta.len()], plain_g[..plain.theta.len()], "and every standing entry's covector");
        }
        for (n, v) in field.theta[l.friction..l.friction + 2 * d.heads].iter_mut().enumerate() {
            let bit = 1i32 << holonics_engine::field::FACE_BITS;
            *v = [bit / 4, -bit / 2, 3 * bit / 4, bit, -bit / 4, bit / 2, -3 * bit / 4, bit / 8][n % 8];
        }
        for (n, v) in field.theta[l.friction_gate..l.friction_gate + d.heads * dw].iter_mut().enumerate() {
            let word = &keys[16 * n..16 * n + 4];
            *v = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> (MATERIAL_BITS - 12);
        }
        for (section, regions) in [("law", &law), ("strands", &strands), ("mixed", &mixed)] {
            let (host_faces, host_g) = field.read_and_return(regions).unwrap();
            let (card_faces, card_g) = card_field.read_and_return(&field, regions).unwrap();
            let (hf, cf) = (&host_faces, &card_faces);
            let apart: Vec<(usize, usize)> = (0..regions.len()).flat_map(|r| (0..hf[r].len().max(cf[r].len())).filter(move |&t| hf[r].get(t) != cf[r].get(t)).map(move |t| (r, t))).collect();
            assert!(apart.is_empty(), "{section}: {} faces differ, the first at region and place {:?}", apart.len(), apart.first());
            let unequal: Vec<usize> = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
            assert!(unequal.is_empty(), "{section}: {} covector entries differ, the first at {:?} (the frictions at {})", unequal.len(), unequal.first(), l.friction);
            let fr = &host_g[l.friction..l.friction + 2 * d.heads];
            assert!(host_g[l.friction_gate..l.friction_gate + d.heads * dw].iter().any(|&v| v != 0), "{section}: the gate takes a covector");
            assert!(fr.iter().step_by(2).any(|&v| v != 0) || section == "strands", "{section}: the class receivers' frictions take a covector");
            assert!(fr.iter().skip(1).step_by(2).any(|&v| v != 0), "{section}: the listeners' frictions take a covector");
            assert_eq!(Host.read_faces(&field, regions).unwrap(), card_field.read_faces(&field, regions).unwrap(), "{section}: a read that does not return");
            println!("FRICTION_GATE_PARITY section={section} regions={} covector_entries={} friction_covector={:?} faces_equal=1 covector_equal=1", regions.len(), card_g.len(), fr);
        }
    }

    /// [measurement; theory, November 12; the triad record §4] **The triads on the card read the host's bits** (needs the card): a field of
    /// `declaration(32, 4, 32)` grown by two carry circles and sixteen triads ([`holonics_engine::field::Learner::with_triads`]), its
    /// readout, current and pair returns, `W_T` and the triads' chart biases moved off zero from a keyed stream's tail (so the faces have a
    /// covector and every triad term, forward and reverse, is read), read and returned on regions of 2, 3, 5, 64 and 257 sites through the host and
    /// through the card: every face and every covector entry equal, and the covector nonzero on `W_T`, the triads' chart and their biases. The
    /// ends are read with them: a region of two sites has no place with both strand mates, one of three a single one, and one of five reads each
    /// leg's covector at one place only.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_triads_on_the_card_read_the_hosts_bits() {
        use holonics_engine::field::Learner;
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let triads = 16usize;
        let mut field = Learner::new(founded, 12).with_carry(2, &keys).unwrap().with_triads(triads, &keys).unwrap().field;
        let d = field.declaration;
        let (l, dw, f, m2) = (field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        assert_eq!((d.triads, d.carry), (triads, 2));
        // Each moved entry with its shift: the material's families on `2^(−24)`, the triads' biases on the face's grain, eight bits coarser.
        let moved: Vec<(usize, u32)> = (l.read..l.read + dw * dw)
            .map(|i| (i, 14))
            .chain((l.out..l.out + dw * m2).map(|i| (i, 14)))
            .chain((l.w..l.w + dw * f).map(|i| (i, 14)))
            .chain((l.w_triad..l.w_triad + dw * 2 * triads).map(|i| (i, 12)))
            .chain((l.triad_bias..l.triad_bias + 6 * triads).map(|i| (i, 20)))
            .collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &(i, shift)) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
        }
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n).collect()).collect();
        let regions: Vec<Region> = classes.iter().zip(&open).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
        assert_eq!(host_faces, card_faces);
        assert_eq!(host_g.len(), card_g.len());
        let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g[i] != card_g[i]).collect();
        assert!(unequal.is_empty(), "{} covector entries differ, the first at {:?} (triad at {}, triad_bias at {}, w_triad at {})", unequal.len(), unequal.first(), l.triad, l.triad_bias, l.w_triad);
        // [P58 item 3] The faces at their classes gathered on the card are the whole faces' at their classes, beside the same covector.
        let (at_class, narrow_g) = card_field.read_and_return_at_class(&field, &regions).unwrap();
        assert_eq!(at_class, holonics_engine::field::faces_at_class(&host_faces, &regions));
        assert!(narrow_g == card_g, "the narrow read's covector differs from the whole read's");
        // [P57 item 2] The open sites' charts by stage on the card are the host's, beside the same faces.
        let (charts_faces, card_charts) = card_field.read_tick_charts(&field, &regions).unwrap();
        let (host_charts_faces, host_charts) = holonics_engine::field::Host.read_tick_charts(&field, &regions).unwrap();
        assert_eq!(charts_faces, host_charts_faces);
        assert_eq!(card_charts.len(), regions.len());
        assert!(card_charts == host_charts, "the charts by stage differ between the card and the host");
        assert_eq!(card_charts[4].len(), field.declaration.ticks + 1);
        // [Brandon, November 15 00:58Z] The open sites' lane powers by stage on the card are the host's, beside the same faces.
        let (scales_faces, card_scales) = card_field.read_tick_scales(&field, &regions).unwrap();
        let (host_scales_faces, host_scales) = holonics_engine::field::Host.read_tick_scales(&field, &regions).unwrap();
        assert_eq!(scales_faces, host_scales_faces);
        assert!(card_scales == host_scales, "the lane powers by stage differ between the card and the host");
        assert_eq!(card_scales[4].len(), field.declaration.ticks + 1);
        assert!(card_scales.iter().flatten().flatten().any(|&s| s != 0), "no lane power read");
        for (name, start, len) in [("w_triad", l.w_triad, dw * 2 * triads), ("triad", l.triad, 6 * triads * dw), ("triad_bias", l.triad_bias, 6 * triads)] {
            assert!(host_g[start..start + len].iter().any(|&v| v != 0), "the triads' {name} takes no covector");
        }
    }

    /// [measurement; theory, November 16 19:10Z, the crossing triad] **The crossing triads on the card read the host's bits** (the strand's test below
    /// with the triads' legs at the site, `Learner::with_crossings`) (needs the card): a field of
    /// `declaration(32, 4, 32)` grown by two carry circles and sixteen triads ([`holonics_engine::field::Learner::with_triads`]), its
    /// readout, current and pair returns, `W_T` and the triads' chart biases moved off zero from a keyed stream's tail (so the faces have a
    /// covector and every triad term, forward and reverse, is read), read and returned on regions of 2, 3, 5, 64 and 257 sites through the host and
    /// through the card: every face and every covector entry equal, and the covector nonzero on `W_T`, the triads' chart and their biases. The
    /// ends are read with them: a region of two sites has no place with both strand mates, one of three a single one, and one of five reads each
    /// leg's covector at one place only.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_crossing_triads_on_the_card_read_the_hosts_bits() {
        use holonics_engine::field::Learner;
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let triads = 16usize;
        let mut field = Learner::new(founded, 12).with_carry(2, &keys).unwrap().with_crossings(triads, &keys).unwrap().field;
        let d = field.declaration;
        let (l, dw, f, m2) = (field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        assert_eq!((d.triads, d.carry, d.crossing), (triads, 2, true));
        // Each moved entry with its shift: the material's families on `2^(−24)`, the triads' biases on the face's grain, eight bits coarser.
        let moved: Vec<(usize, u32)> = (l.read..l.read + dw * dw)
            .map(|i| (i, 14))
            .chain((l.out..l.out + dw * m2).map(|i| (i, 14)))
            .chain((l.w..l.w + dw * f).map(|i| (i, 14)))
            .chain((l.w_triad..l.w_triad + dw * 2 * triads).map(|i| (i, 12)))
            .chain((l.triad_bias..l.triad_bias + 6 * triads).map(|i| (i, 20)))
            .collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &(i, shift)) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
        }
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n).collect()).collect();
        let regions: Vec<Region> = classes.iter().zip(&open).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
        assert_eq!(host_faces, card_faces);
        assert_eq!(host_g.len(), card_g.len());
        let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g[i] != card_g[i]).collect();
        assert!(unequal.is_empty(), "{} covector entries differ, the first at {:?} (triad at {}, triad_bias at {}, w_triad at {})", unequal.len(), unequal.first(), l.triad, l.triad_bias, l.w_triad);
        // [P58 item 3] The faces at their classes gathered on the card are the whole faces' at their classes, beside the same covector.
        let (at_class, narrow_g) = card_field.read_and_return_at_class(&field, &regions).unwrap();
        assert_eq!(at_class, holonics_engine::field::faces_at_class(&host_faces, &regions));
        assert!(narrow_g == card_g, "the narrow read's covector differs from the whole read's");
        // [P57 item 2] The open sites' charts by stage on the card are the host's, beside the same faces.
        let (charts_faces, card_charts) = card_field.read_tick_charts(&field, &regions).unwrap();
        let (host_charts_faces, host_charts) = holonics_engine::field::Host.read_tick_charts(&field, &regions).unwrap();
        assert_eq!(charts_faces, host_charts_faces);
        assert_eq!(card_charts.len(), regions.len());
        assert!(card_charts == host_charts, "the charts by stage differ between the card and the host");
        assert_eq!(card_charts[4].len(), field.declaration.ticks + 1);
        // [Brandon, November 15 00:58Z] The open sites' lane powers by stage on the card are the host's, beside the same faces.
        let (scales_faces, card_scales) = card_field.read_tick_scales(&field, &regions).unwrap();
        let (host_scales_faces, host_scales) = holonics_engine::field::Host.read_tick_scales(&field, &regions).unwrap();
        assert_eq!(scales_faces, host_scales_faces);
        assert!(card_scales == host_scales, "the lane powers by stage differ between the card and the host");
        assert_eq!(card_scales[4].len(), field.declaration.ticks + 1);
        assert!(card_scales.iter().flatten().flatten().any(|&s| s != 0), "no lane power read");
        for (name, start, len) in [("w_triad", l.w_triad, dw * 2 * triads), ("triad", l.triad, 6 * triads * dw), ("triad_bias", l.triad_bias, 6 * triads)] {
            assert!(host_g[start..start + len].iter().any(|&v| v != 0), "the triads' {name} takes no covector");
        }
    }

    /// [realization; theory, November 13, P61 item 5] **A site's maps in the tile form read the definitions' integers** (needs the card): the
    /// forward map, the transposed map and the outer sum with its bound, at every shape the store line's declaration launches (P61's reading:
    /// forward 64 × 64 and 128 × 64 on 32-bit inputs, 64 × 64 and 64 × 128 on 64-bit ones; transposed 64 × 64, 64 × 128 and 128 × 64; outer
    /// 64 × 64 and 128 × 64 on 32-bit inputs, 64 × 64 and 64 × 128 on 64-bit ones, and the bias's sums of 64, 128 and 244), against the
    /// definitions summed here on 128 bits: every output word, every entry of `g` (a ring sum on 128 bits) and the status bits equal. The
    /// fixtures force the wide form (words past `2^31` in some tiles), a site the forward map refuses (`wmax · xmax · (cols + 1) ≥ 2^126`), a
    /// region the outer bound refuses, a mask of open sites, `add` and `accumulate`, site counts that are no multiple of a tile, and the bias's
    /// sum with no `x`.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn a_sites_maps_in_the_tile_form_read_the_definitions_integers() {
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let cf = Resident::open(&card).unwrap();
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        // A word of `bits` bits, signed.
        let mut word = |bits: u32| -> i64 { let v = (next() >> (64 - bits)) as i64; if next() & 1 == 1 { -v } else { v } };
        let rel = |x: i128, bits: u32| -> i128 { let half = 1i128 << (bits - 1); if x >= 0 { (x + half) >> bits } else { -((-x + half) >> bits) } };
        let (refused_carrier, refused_word64) = (1u32, 2u32);
        let fit = |v: i128, st: &mut u32| -> i64 { if v > i64::MAX as i128 || v < i64::MIN as i128 { *st |= refused_word64; 0 } else { v as i64 } };
        let mut checked = 0usize;
        // Sites: no multiple of a tile, and more than a walk of the outer sum.
        for &sites in &[37usize, 200, 1093] {
            let regions: Vec<u32> = { let mut r = vec![0u32]; let mut at = 0u32; while (at as usize) < sites { at = (at + 97 + (word(9).unsigned_abs() % 300) as u32).min(sites as u32); r.push(at); } r };
            for &only in &[false, true] {
                let unresolved: Vec<u8> = (0..sites).map(|t| u8::from(!only || t % 3 != 1)).collect();
                let mut base = Words { t: sites as u32, r: (regions.len() - 1) as u32, ..Default::default() };
                let unresolved_buf = card.upload(&unresolved).unwrap();
                let region_buf = card.upload(&regions).unwrap();
                base.unresolved = unresolved_buf.device_ptr();
                base.region_off = region_buf.device_ptr();
                // The forward map.
                for &(rows, cols, x64, add, wide_tile, refuse) in &[(64usize, 64usize, false, false, false, false), (128, 64, false, false, false, false), (64, 64, true, true, true, false), (64, 128, true, true, false, true), (64, 64, true, false, false, false)] {
                    let w: Vec<i32> = (0..rows * cols).map(|_| word(28) as i32).collect();
                    let b: Vec<i32> = (0..rows).map(|_| word(20) as i32).collect();
                    let theta: Vec<i32> = w.iter().chain(&b).copied().collect();
                    let wmax_true = w.iter().map(|v| v.unsigned_abs() as u64).max().unwrap();
                    let x: Vec<i64> = (0..sites * cols).map(|c| { let t = c / cols; if x64 && wide_tile && t % 64 < 3 { word(40) } else if x64 && refuse && t == sites / 2 { if c % cols == 0 { 1i64 << 61 } else { word(40) } } else { word(22) } }).collect();
                    // A refused site: the host's carrier bound read with a weight bound past the true one (`2^58 · 2^61 · 129` reaches `2^126`
                    // and stands under `2^128`).
                    let wmax = if refuse { 1u64 << 58 } else { wmax_true };
                    let prior: Vec<i64> = (0..sites * rows).map(|_| word(40)).collect();
                    let theta_buf = card.upload(&theta).unwrap();
                    let status_buf = card.zeroed::<u32>(1).unwrap();
                    let out_buf = card.upload(&prior).unwrap();
                    let x_buf = if x64 { card.upload(&x).unwrap() } else { card.upload(&x.iter().map(|&v| v as i32 as i64).collect::<Vec<_>>()).unwrap() };
                    let x32: Vec<i32> = x.iter().map(|&v| v as i32).collect();
                    let x32_buf = card.upload(&x32).unwrap();
                    let mut words = Words { theta: theta_buf.device_ptr(), status: status_buf.device_ptr(), ..base };
                    let xp = if x64 { x_buf.device_ptr() } else { x32_buf.device_ptr() };
                    let entry = if x64 { "field_affine_x64" } else { "field_affine_x32" };
                    let (outp, addp) = if add { (0, out_buf.device_ptr()) } else { (out_buf.device_ptr(), 0) };
                    cf.affine(entry, &mut words, 0, (rows * cols) as u64, wmax, rows, cols, xp, cols, outp, rows, addp, only).unwrap();
                    let got = card.fetch(&out_buf).unwrap();
                    let st = card.fetch(&status_buf).unwrap()[0];
                    let (mut want, mut wst) = (prior.clone(), 0u32);
                    for t in 0..sites {
                        if only && unresolved[t] == 0 {
                            continue;
                        }
                        let xt: Vec<i128> = (0..cols).map(|i| if x64 { x[t * cols + i] as i128 } else { x32[t * cols + i] as i128 }).collect();
                        let xmax = xt.iter().map(|v| v.unsigned_abs()).max().unwrap();
                        if (wmax as u128) * xmax * (cols as u128 + 1) >= 1u128 << 126 {
                            wst |= refused_carrier;
                            continue;
                        }
                        for o in 0..rows {
                            let sum: i128 = (0..cols).map(|i| w[o * cols + i] as i128 * xt[i]).sum::<i128>() + ((b[o] as i128) << 24);
                            let v = fit(rel(sum, 24), &mut wst);
                            want[t * rows + o] = if add { fit(prior[t * rows + o] as i128 + v as i128, &mut wst) } else { v };
                        }
                    }
                    assert_eq!(st, wst, "forward {rows}x{cols} x64={x64} sites={sites} only={only}: the status bits");
                    assert!(got == want, "forward {rows}x{cols} x64={x64} add={add} sites={sites} only={only}: {} words differ", got.iter().zip(&want).filter(|(a, b)| a != b).count());
                    checked += 1;
                }
                // The transposed map.
                for &(rows, cols, acc, wide_tile) in &[(64usize, 64usize, false, true), (64, 64, true, false), (64, 128, false, false), (128, 64, true, true)] {
                    let w: Vec<i32> = (0..rows * cols).map(|_| word(28) as i32).collect();
                    let y: Vec<i64> = (0..sites * rows).map(|c| if wide_tile && (c / rows) % 64 == 5 { word(44) } else { word(31) }).collect();
                    let prior: Vec<i64> = (0..sites * cols).map(|_| word(40)).collect();
                    let theta_buf = card.upload(&w).unwrap();
                    let status_buf = card.zeroed::<u32>(1).unwrap();
                    let out_buf = card.upload(&prior).unwrap();
                    let y_buf = card.upload(&y).unwrap();
                    let mut words = Words { theta: theta_buf.device_ptr(), status: status_buf.device_ptr(), ..base };
                    cf.transposed(&mut words, 0, rows, cols, y_buf.device_ptr(), rows, out_buf.device_ptr(), acc, only).unwrap();
                    let got = card.fetch(&out_buf).unwrap();
                    let st = card.fetch(&status_buf).unwrap()[0];
                    let (mut want, mut wst) = (prior.clone(), 0u32);
                    for t in 0..sites {
                        if only && unresolved[t] == 0 {
                            continue;
                        }
                        for i in 0..cols {
                            let sum: i128 = (0..rows).map(|o| w[o * cols + i] as i128 * y[t * rows + o] as i128).sum();
                            let v = fit(rel(sum, 24), &mut wst);
                            want[t * cols + i] = if acc { fit(prior[t * cols + i] as i128 + v as i128, &mut wst) } else { v };
                        }
                    }
                    assert_eq!(st, wst, "transposed {rows}x{cols} sites={sites} only={only}: the status bits");
                    assert!(got == want, "transposed {rows}x{cols} acc={acc} sites={sites} only={only}: {} words differ", got.iter().zip(&want).filter(|(a, b)| a != b).count());
                    checked += 1;
                }
                // The outer sum and its bound, and the bias's sums.
                for &(rows, cols, x64, case) in &[(64usize, 64usize, false, 0u8), (128, 64, false, 1), (64, 64, true, 1), (64, 128, true, 2), (64, 0, false, 0), (128, 0, false, 1), (244, 0, false, 0)] {
                    // case 0 narrow; 1 a wide walk (words past 2^31 in one walk); 2 a region refused by the bound.
                    let y: Vec<i64> = (0..sites * rows).map(|c| { let t = c / rows; if case == 1 && t % 512 < 4 { word(40) } else if case == 2 && t < 8 { word(63) } else { word(31) } }).collect();
                    let xw = cols.max(1);
                    let x: Vec<i64> = (0..sites * xw).map(|c| { let t = c / xw; if case == 2 && t < 8 { word(63) } else { word(22) } }).collect();
                    let x32: Vec<i32> = x.iter().map(|&v| v as i32).collect();
                    let entries = rows * cols.max(1);
                    let at = 3usize;
                    let prior: Vec<i128> = (0..entries + 2 * at).map(|_| (word(60) as i128) << 20).collect();
                    let status_buf = card.zeroed::<u32>(1).unwrap();
                    let g_buf = card.upload(&prior).unwrap();
                    let y_buf = card.upload(&y).unwrap();
                    let x_buf = card.upload(&x).unwrap();
                    let x32_buf = card.upload(&x32).unwrap();
                    let mut words = Words { status: status_buf.device_ptr(), ..base };
                    let xp = if cols == 0 { 0 } else if x64 { x_buf.device_ptr() } else { x32_buf.device_ptr() };
                    cf.outer(&mut words, &g_buf, at as u64, rows, cols, y_buf.device_ptr(), rows, xp, xw, x64, only).unwrap();
                    let got = card.fetch(&g_buf).unwrap();
                    let st = card.fetch(&status_buf).unwrap()[0];
                    let (mut want, mut wst) = (prior.clone(), 0u32);
                    let live = |t: usize| !(only && unresolved[t] == 0);
                    let xv = |t: usize, i: usize| -> i128 { if x64 { x[t * xw + i] as i128 } else { x32[t * xw + i] as i128 } };
                    for o in 0..rows {
                        for i in 0..cols.max(1) {
                            let mut sum = 0i128;
                            for t in (0..sites).filter(|&t| live(t)) {
                                sum = sum.wrapping_add((y[t * rows + o] as i128).wrapping_mul(if cols == 0 { 1 } else { xv(t, i) }));
                            }
                            want[at + o * cols.max(1) + i] = want[at + o * cols.max(1) + i].wrapping_add(sum);
                        }
                    }
                    if cols > 0 {
                        for r in 0..regions.len() - 1 {
                            let mut bound = 0u128;
                            let mut over = false;
                            for t in (regions[r] as usize..regions[r + 1] as usize).filter(|&t| live(t)) {
                                let ym = (0..rows).map(|o| (y[t * rows + o] as i128).unsigned_abs()).max().unwrap();
                                let xm = (0..cols).map(|i| xv(t, i).unsigned_abs()).max().unwrap();
                                match bound.checked_add(ym * xm) {
                                    Some(b) if b < 1u128 << 126 => bound = b,
                                    _ => over = true,
                                }
                            }
                            if over {
                                wst |= refused_carrier;
                            }
                        }
                    }
                    assert_eq!(st, wst, "outer {rows}x{cols} x64={x64} case={case} sites={sites} only={only}: the status bits");
                    assert!(got == want, "outer {rows}x{cols} x64={x64} case={case} sites={sites} only={only}: {} entries differ", got.iter().zip(&want).filter(|(a, b)| a != b).count());
                    checked += 1;
                }
            }
        }
        println!("SITE_MAPS_PARITY cases={checked}");
        assert_eq!(checked, 3 * 2 * (5 + 4 + 7));
    }

    /// [realization; November 15, the maps' second loop] **The outer sum's long walks read the definitions' integers** (needs the card): at
    /// 20,298 sites the walk the host reads is 256 to 512 sites (`outer_grid`), so a walk holds eight to sixteen chunks whose proof is read as
    /// they are staged. Over 64 × 128 and 128 × 128 on 32-bit inputs and 128 × 128 on 64-bit ones, with narrow words, with words past `2^31` in
    /// a few sites (a walk that begins again in the wide form mid-walk), with a chunks' bound that passes `2^63` only after several chunks
    /// (words of 28 and 27 bits: a chunk's bound is near `2^60`, so the eighth chunk of a walk passes it), and with a mask of open sites: every entry of `g` and the status bits equal the definition summed here on
    /// 128 bits.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_outer_sums_long_walks_read_the_definitions_integers() {
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let cf = Resident::open(&card).unwrap();
        let sites = 20_298usize;
        let mut state = 0x6A09_E667_F3BC_C909u64;
        let mut word = move |bits: u32| -> i64 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let v = (state >> (64 - bits)) as i64;
            if state & 1 == 1 { -v } else { v }
        };
        let regions: Vec<u32> = (0..=sites as u32).step_by(203).chain(std::iter::once(sites as u32)).collect::<std::collections::BTreeSet<_>>().into_iter().collect();
        let mut checked = 0usize;
        for &only in &[false, true] {
            let unresolved: Vec<u8> = (0..sites).map(|t| u8::from(!only || t % 3 != 1)).collect();
            let (unresolved_buf, region_buf) = (card.upload(&unresolved).unwrap(), card.upload(&regions).unwrap());
            for &(rows, cols, x64) in &[(64usize, 128usize, false), (128, 128, false), (128, 128, true)] {
                let (_, walk) = cf.outer_grid(rows, cols, true, sites);
                assert!(walk >= 256, "the walk at {rows}x{cols} is {walk}");
                // case 0 narrow; 1 words past 2^31 in a few sites; 2 a bound that passes 2^63 after several chunks.
                for case in 0..3u8 {
                    let y: Vec<i64> = (0..sites * rows).map(|c| { let t = c / rows; if case == 1 && t % 997 == 400 { word(40) } else if case == 2 { word(28) } else { word(26) } }).collect();
                    let x: Vec<i64> = (0..sites * cols).map(|c| { let t = c / cols; if case == 1 && x64 && t % 1301 == 7 { word(36) } else if case == 2 { word(27) } else { word(22) } }).collect();
                    let x32: Vec<i32> = x.iter().map(|&v| v as i32).collect();
                    let entries = rows * cols;
                    let prior: Vec<i128> = (0..entries).map(|_| (word(60) as i128) << 20).collect();
                    let status_buf = card.zeroed::<u32>(1).unwrap();
                    let g_buf = card.upload(&prior).unwrap();
                    let (y_buf, x_buf, x32_buf) = (card.upload(&y).unwrap(), card.upload(&x).unwrap(), card.upload(&x32).unwrap());
                    let mut words = Words { t: sites as u32, r: (regions.len() - 1) as u32, unresolved: unresolved_buf.device_ptr(), region_off: region_buf.device_ptr(), status: status_buf.device_ptr(), ..Default::default() };
                    let xp = if x64 { x_buf.device_ptr() } else { x32_buf.device_ptr() };
                    cf.outer(&mut words, &g_buf, 0, rows, cols, y_buf.device_ptr(), rows, xp, cols, x64, only).unwrap();
                    let got = card.fetch(&g_buf).unwrap();
                    let st = card.fetch(&status_buf).unwrap()[0];
                    let xv = |t: usize, i: usize| -> i128 { if x64 { x[t * cols + i] as i128 } else { x32[t * cols + i] as i128 } };
                    let mut want = prior.clone();
                    for o in 0..rows {
                        for i in 0..cols {
                            let mut sum = 0i128;
                            for t in (0..sites).filter(|&t| !(only && unresolved[t] == 0)) {
                                sum = sum.wrapping_add((y[t * rows + o] as i128).wrapping_mul(xv(t, i)));
                            }
                            want[o * cols + i] = want[o * cols + i].wrapping_add(sum);
                        }
                    }
                    assert_eq!(st, 0, "outer {rows}x{cols} x64={x64} case={case} only={only}: no region is refused");
                    assert!(got == want, "outer {rows}x{cols} x64={x64} case={case} only={only} walk={walk}: {} entries differ", got.iter().zip(&want).filter(|(a, b)| a != b).count());
                    checked += 1;
                }
            }
        }
        println!("OUTER_LONG_WALKS cases={checked}");
        assert_eq!(checked, 2 * 3 * 3);
    }

    /// [measurement; November 15, the maps' second loop] **The site maps timed at the store line's shapes** (needs the card): the forward map,
    /// the transposed map and the outer sum at the shapes a section of the line launches most (`FIELD_PROFILE_MAP` of lap 31's 24 sections:
    /// 20,298 sites a launch, maps of 64 × 128, 128 × 128 and 128 × 64), on words of the widths the bits ruler read (weights 27 bits, inputs
    /// 21, covectors 26, where the line's tiles prove their sums), each entry `FIELD_MAPS_LAUNCHES` rounds (default 40) after a warm-up, the variants of a shape in turn, as millionths of a second a launch and products a
    /// second. `FIELD_MAPS_ENTRIES` names other entries of the same parameters to time beside the line's (`kind:entry`, comma-separated, the
    /// kinds `forward`, `forward64`, `transposed`, `outer`, `outer64`). A timing beside other work on the card reads the share it was given.
    #[test]
    #[ignore = "needs the CUDA card; a timing, run alone with --include-ignored --test-threads=1 --nocapture"]
    #[allow(clippy::float_arithmetic, reason = "a reading written at the exterior: printed millionths of a second and rates")]
    fn the_site_maps_timed_at_the_lines_shapes() {
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let cf = Resident::open(&card).unwrap();
        let sites = 20_298usize;
        let launches: u32 = std::env::var("FIELD_MAPS_LAUNCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(40);
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        let mut word = move |bits: u32| -> i64 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let v = (state >> (64 - bits)) as i64;
            if state & 1 == 1 { -v } else { v }
        };
        let regions: Vec<u32> = (0..=sites as u32).step_by(203).chain(std::iter::once(sites as u32)).collect::<std::collections::BTreeSet<_>>().into_iter().collect();
        let unresolved = vec![1u8; sites];
        let unresolved_buf = card.upload(&unresolved).unwrap();
        let region_buf = card.upload(&regions).unwrap();
        let theta: Vec<i32> = (0..128 * 128 + 128).map(|_| word(27) as i32).collect();
        let wmax = theta.iter().map(|v| v.unsigned_abs() as u64).max().unwrap();
        let theta_buf = card.upload(&theta).unwrap();
        let status_buf = card.zeroed::<u32>(1).unwrap();
        let x32: Vec<i32> = (0..sites * 128).map(|_| word(21) as i32).collect();
        let x64: Vec<i64> = x32.iter().map(|&v| i64::from(v)).collect();
        // A covector of 26 bits: the line's tiles prove their 64-bit sums (0.97 of its transposed and outer tiles), and a bench of wider words
        // would time the wide form the line seldom takes.
        let y: Vec<i64> = (0..sites * 128).map(|_| word(26)).collect();
        let (x32_buf, x64_buf, y_buf) = (card.upload(&x32).unwrap(), card.upload(&x64).unwrap(), card.upload(&y).unwrap());
        let out_buf = card.zeroed::<i64>(sites * 128).unwrap();
        let g_buf = card.zeroed::<i128>(128 * 128 + 8).unwrap();
        let base = Words { t: sites as u32, r: (regions.len() - 1) as u32, unresolved: unresolved_buf.device_ptr(), region_off: region_buf.device_ptr(), theta: theta_buf.device_ptr(), status: status_buf.device_ptr(), ..Default::default() };
        // The variants of a shape are launched in turn, one launch each a round, every launch timed alone between two synchronizations,
        // so work beside the bench on the card falls on each variant alike; the median and the least of the rounds are printed.
        let timed = |products: u64, variants: &mut Vec<(String, Box<dyn FnMut() + '_>)>| {
            let mut took: Vec<Vec<f64>> = vec![Vec::new(); variants.len()];
            for round in 0..=launches {
                for (k, (_, run)) in variants.iter_mut().enumerate() {
                    card.synchronize().unwrap();
                    let started = Instant::now();
                    run();
                    card.synchronize().unwrap();
                    if round > 0 {
                        took[k].push(started.elapsed().as_secs_f64() * 1e6);
                    }
                }
            }
            for ((name, _), t) in variants.iter().zip(took.iter_mut()) {
                t.sort_by(f64::total_cmp);
                let (median, least) = (t[t.len() / 2], t[0]);
                println!("MAPS_TIMING entry={name} sites={sites} us_median={median:.1} us_least={least:.1} products_a_second_median={:.3e}", products as f64 / (median * 1e-6));
            }
        };
        let alt: Vec<(String, String)> = std::env::var("FIELD_MAPS_ENTRIES").unwrap_or_default().split(',').filter_map(|s| s.split_once(':')).map(|(k, e)| (k.to_string(), e.to_string())).collect();
        let leak = |e: &str| -> &'static str { Box::leak(e.to_string().into_boxed_str()) };
        for &(rows, cols, wide_input, add) in &[(64usize, 128usize, false, false), (128, 128, false, false), (128, 128, true, true), (128, 64, true, true)] {
            let (x, entry) = if wide_input { (x64_buf.device_ptr(), "field_affine_x64") } else { (x32_buf.device_ptr(), "field_affine_x32") };
            let (outp, addp) = if add { (0, out_buf.device_ptr()) } else { (out_buf.device_ptr(), 0) };
            let mut variants: Vec<(String, Box<dyn FnMut() + '_>)> = Vec::new();
            let cfr = &cf;
            let mut words = base;
            variants.push((format!("{entry}:{rows}x{cols}"), Box::new(move || cfr.affine(entry, &mut words, 0, (rows * cols) as u64, wmax, rows, cols, x, cols, outp, rows, addp, false).unwrap())));
            for (_, alt_entry) in alt.iter().filter(|(k, _)| k == if wide_input { "forward64" } else { "forward" }) {
                let e = leak(alt_entry);
                let grid = (rows as u64).div_ceil(64).saturating_mul((sites as u64).div_ceil(64)).clamp(1, 65_535) as u32;
                let (mut words, mut weight, mut bias, mut wm, mut r32, mut c32, mut xp, mut xs, mut op, mut os, mut ap, mut u) = (base, 0u64, (rows * cols) as u64, wmax, rows as u32, cols as u32, x, cols as u64, outp, rows as u64, addp, 0u32);
                variants.push((format!("{e}:{rows}x{cols}"), Box::new(move || cfr.launch(e, grid, THREADS, &mut [arg(&mut words), arg(&mut weight), arg(&mut bias), arg(&mut wm), arg(&mut r32), arg(&mut c32), arg(&mut xp), arg(&mut xs), arg(&mut op), arg(&mut os), arg(&mut ap), arg(&mut u)]).unwrap())));
            }
            timed((sites * rows * cols) as u64, &mut variants);
        }
        for &(rows, cols, acc) in &[(128usize, 128usize, false), (64, 128, true), (128, 64, false)] {
            let mut variants: Vec<(String, Box<dyn FnMut() + '_>)> = Vec::new();
            let cfr = &cf;
            let (yp, op) = (y_buf.device_ptr(), out_buf.device_ptr());
            let mut words = base;
            variants.push((format!("field_transposed:{rows}x{cols}"), Box::new(move || cfr.transposed(&mut words, 0, rows, cols, yp, rows, op, acc, false).unwrap())));
            for (_, alt_entry) in alt.iter().filter(|(k, _)| k == "transposed") {
                let e = leak(alt_entry);
                let grid = (cols as u64).div_ceil(64).saturating_mul((sites as u64).div_ceil(64)).clamp(1, 65_535) as u32;
                let (mut words, mut weight, mut r32, mut c32, mut yp, mut ys, mut op, mut a, mut u) = (base, 0u64, rows as u32, cols as u32, yp, rows as u64, op, u32::from(acc), 0u32);
                variants.push((format!("{e}:{rows}x{cols}"), Box::new(move || cfr.launch(e, grid, THREADS, &mut [arg(&mut words), arg(&mut weight), arg(&mut r32), arg(&mut c32), arg(&mut yp), arg(&mut ys), arg(&mut op), arg(&mut a), arg(&mut u)]).unwrap())));
            }
            timed((sites * rows * cols) as u64, &mut variants);
        }
        for &(rows, cols, wide_input) in &[(64usize, 128usize, false), (128, 128, false), (128, 128, true), (128, 0, false)] {
            let x = if cols == 0 { 0 } else if wide_input { x64_buf.device_ptr() } else { x32_buf.device_ptr() };
            let mut variants: Vec<(String, Box<dyn FnMut() + '_>)> = Vec::new();
            let (cfr, gb) = (&cf, &g_buf);
            let yp = y_buf.device_ptr();
            let mut words = base;
            variants.push((format!("field_outer_{}:{rows}x{cols}", if wide_input { "x64" } else { "x32" }), Box::new(move || cfr.outer(&mut words, gb, 0, rows, cols, yp, rows, x, cols.max(1), wide_input, false).unwrap())));
            for (_, alt_entry) in alt.iter().filter(|(k, _)| k == if wide_input { "outer64" } else { "outer" }) {
                let e = leak(alt_entry);
                let (grid, walk) = cf.outer_grid(rows, cols, x != 0, sites);
                let (mut words, mut gp, mut at, mut r32, mut c32, mut yp, mut ys, mut xp, mut xs, mut u, mut mx, mut wk) = (base, g_buf.device_ptr(), 0u64, rows as u32, cols as u32, yp, rows as u64, x, cols.max(1) as u64, 0u32, 0u64, walk);
                variants.push((format!("{e}:{rows}x{cols}"), Box::new(move || cfr.launch(e, grid, THREADS, &mut [arg(&mut words), arg(&mut gp), arg(&mut at), arg(&mut r32), arg(&mut c32), arg(&mut yp), arg(&mut ys), arg(&mut xp), arg(&mut xs), arg(&mut u), arg(&mut mx), arg(&mut wk)]).unwrap())));
            }
            timed((sites * rows * cols.max(1)) as u64, &mut variants);
        }
        assert_eq!(card.fetch(&status_buf).unwrap()[0], 0, "no word of the bench is refused");
    }

    /// [measurement; the lead, November 20] **The site maps at width 224 on the tensor units and on the CUDA cores** (needs the card): the forward
    /// map on 32-bit inputs and the transposed map at the shapes the store line's width-224 declaration launches most (1,088 contacts, 1,024 carry
    /// rows, 64 words; `D = 224`), 10,000 sites, words of the widths the carriers' census read (weights 25 bits, inputs 19, covectors 26); each
    /// entry timed alone between synchronizations, the least and the median of `FIELD_MAPS_LAUNCHES` rounds (default 30), the tensor-core
    /// route (`affine`, `transposed`) beside the tile form's kernels launched directly. The outputs of the two routes are compared word for word.
    #[test]
    #[ignore = "needs the CUDA card; a timing, run alone with --include-ignored --test-threads=1 --nocapture"]
    #[allow(clippy::float_arithmetic, reason = "a reading written at the exterior: printed millionths of a second and rates")]
    fn the_site_maps_at_width_224_on_the_tensor_units() {
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let cf = Resident::open(&card).unwrap();
        let sites = 10_000usize;
        let launches: u32 = std::env::var("FIELD_MAPS_LAUNCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(30);
        let mut state = 0x243F_6A88_85A3_08D3u64;
        let mut word = move |bits: u32| -> i64 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let v = (state >> (64 - bits)) as i64;
            if state & 1 == 1 { -v } else { v }
        };
        let regions: Vec<u32> = (0..=sites as u32).step_by(203).chain(std::iter::once(sites as u32)).collect::<std::collections::BTreeSet<_>>().into_iter().collect();
        let unresolved = vec![1u8; sites];
        let (unresolved_buf, region_buf) = (card.upload(&unresolved).unwrap(), card.upload(&regions).unwrap());
        let theta: Vec<i32> = (0..1088 * 224 + 1088).map(|_| word(25) as i32).collect();
        let wmax = theta.iter().map(|v| v.unsigned_abs() as u64).max().unwrap();
        let theta_buf = card.upload(&theta).unwrap();
        let status_buf = card.zeroed::<u32>(1).unwrap();
        let x32: Vec<i32> = (0..sites * 1088).map(|_| word(19) as i32).collect();
        let y: Vec<i64> = (0..sites * 1088).map(|_| word(26)).collect();
        let (x32_buf, y_buf) = (card.upload(&x32).unwrap(), card.upload(&y).unwrap());
        let (out_a, out_b) = (card.zeroed::<i64>(sites * 1088).unwrap(), card.zeroed::<i64>(sites * 1088).unwrap());
        let base = Words { t: sites as u32, r: (regions.len() - 1) as u32, unresolved: unresolved_buf.device_ptr(), region_off: region_buf.device_ptr(), theta: theta_buf.device_ptr(), status: status_buf.device_ptr(), ..Default::default() };
        let time = |run: &mut dyn FnMut()| -> (f64, f64) {
            let mut took = Vec::new();
            for round in 0..=launches {
                card.synchronize().unwrap();
                let started = Instant::now();
                run();
                card.synchronize().unwrap();
                if round > 0 {
                    took.push(started.elapsed().as_secs_f64() * 1e6);
                }
            }
            took.sort_by(f64::total_cmp);
            (took[0], took[took.len() / 2])
        };
        for &(rows, cols) in &[(1088usize, 224usize), (1024, 224), (64, 224), (224, 64)] {
            let products = (sites * rows * cols) as f64;
            let mut words = base;
            let (tc_least, tc_median) = time(&mut || cf.affine("field_affine_x32", &mut words, 0, (rows * cols) as u64, wmax, rows, cols, x32_buf.device_ptr(), cols, out_a.device_ptr(), rows, 0, false).unwrap());
            let grid = (rows as u64).div_ceil(64).saturating_mul((sites as u64).div_ceil(64)).clamp(1, 65_535) as u32;
            let (mut w2, mut weight, mut bias, mut wm, mut r32, mut c32, mut xp, mut xs, mut op, mut os, mut ap, mut u) = (base, 0u64, (rows * cols) as u64, wmax, rows as u32, cols as u32, x32_buf.device_ptr(), cols as u64, out_b.device_ptr(), rows as u64, 0u64, 0u32);
            let (old_least, old_median) = time(&mut || cf.launch("field_affine_tiled_x32", grid, THREADS, &mut [arg(&mut w2), arg(&mut weight), arg(&mut bias), arg(&mut wm), arg(&mut r32), arg(&mut c32), arg(&mut xp), arg(&mut xs), arg(&mut op), arg(&mut os), arg(&mut ap), arg(&mut u)]).unwrap());
            let (a, b) = (card.fetch(&out_a).unwrap(), card.fetch(&out_b).unwrap());
            assert!(a[..sites * rows] == b[..sites * rows], "forward {rows}x{cols}: the two routes differ");
            // The staged variant: the sites' digits cut in the kernel.
            let mut w3 = base;
            let (st_least, _) = time(&mut || {
                let (pl, fl, kw, (mut wsh, mut wpl)) = cf.tc_planes(&mut w3, (0, 0, 0, cols as u64, rows, cols)).unwrap();
                let (mut weight, mut bias, mut wm, mut r32, mut c32, mut xp, mut xs, mut op, mut os, mut ap, mut u, mut pa, mut fa, mut pb, mut fb, mut kw) = (0u64, (rows * cols) as u64, wmax, rows as u32, cols as u32, x32_buf.device_ptr(), cols as u64, out_b.device_ptr(), rows as u64, 0u64, 0u32, pl.device_ptr(), fl.device_ptr(), 0u64, 0u64, kw);
                cf.launch("field_affine_tiled_tcs_x32", grid, THREADS, &mut [arg(&mut w3), arg(&mut weight), arg(&mut bias), arg(&mut wm), arg(&mut r32), arg(&mut c32), arg(&mut xp), arg(&mut xs), arg(&mut op), arg(&mut os), arg(&mut ap), arg(&mut u), arg(&mut pa), arg(&mut fa), arg(&mut pb), arg(&mut fb), arg(&mut kw), arg(&mut wsh), arg(&mut wpl)]).unwrap();
            });
            let b = card.fetch(&out_b).unwrap();
            assert!(a[..sites * rows] == b[..sites * rows], "forward {rows}x{cols}: the staged route differs");
            println!("MAPS224 forward {rows}x{cols} tc_us_least={tc_least:.1} tc_us_median={tc_median:.1} staged_us_least={st_least:.1} tile_us_least={old_least:.1} tile_us_median={old_median:.1} tc_products_a_second={:.3e} tile_products_a_second={:.3e}", products / (tc_least * 1e-6), products / (old_least * 1e-6));
        }
        for &(rows, cols) in &[(1088usize, 224usize), (1024, 224), (64, 224), (224, 64)] {
            let products = (sites * rows * cols) as f64;
            let mut words = base;
            let (tc_least, tc_median) = time(&mut || cf.transposed(&mut words, 0, rows, cols, y_buf.device_ptr(), rows, out_a.device_ptr(), false, false).unwrap());
            let grid = (cols as u64).div_ceil(64).saturating_mul((sites as u64).div_ceil(64)).clamp(1, 65_535) as u32;
            let (mut w2, mut weight, mut r32, mut c32, mut yp, mut ys, mut op, mut a0, mut u) = (base, 0u64, rows as u32, cols as u32, y_buf.device_ptr(), rows as u64, out_b.device_ptr(), 0u32, 0u32);
            let (old_least, old_median) = time(&mut || cf.launch("field_transposed", grid, THREADS, &mut [arg(&mut w2), arg(&mut weight), arg(&mut r32), arg(&mut c32), arg(&mut yp), arg(&mut ys), arg(&mut op), arg(&mut a0), arg(&mut u)]).unwrap());
            let (a, b) = (card.fetch(&out_a).unwrap(), card.fetch(&out_b).unwrap());
            assert!(a[..sites * cols] == b[..sites * cols], "transposed {rows}x{cols}: the two routes differ");
            // The planes variant: the covector's digits written as planes first.
            let mut w3 = base;
            let (pl_least, _) = time(&mut || {
                let (pl, fl, kw, (mut wsh, mut wpl)) = cf.tc_planes(&mut w3, (1, 0, 0, cols as u64, cols, rows)).unwrap();
                let (sp, sf, _, _) = cf.tc_planes(&mut w3, (3, y_buf.device_ptr(), 0, rows as u64, sites, rows)).unwrap();
                let (mut weight, mut r32, mut c32, mut yp, mut ys, mut op, mut a0, mut u, mut pa, mut fa, mut pb, mut fb, mut kw) = (0u64, rows as u32, cols as u32, y_buf.device_ptr(), rows as u64, out_b.device_ptr(), 0u32, 0u32, pl.device_ptr(), fl.device_ptr(), sp.device_ptr(), sf.device_ptr(), kw);
                cf.launch("field_transposed_tc", grid, THREADS, &mut [arg(&mut w3), arg(&mut weight), arg(&mut r32), arg(&mut c32), arg(&mut yp), arg(&mut ys), arg(&mut op), arg(&mut a0), arg(&mut u), arg(&mut pa), arg(&mut fa), arg(&mut pb), arg(&mut fb), arg(&mut kw), arg(&mut wsh), arg(&mut wpl)]).unwrap();
            });
            let b = card.fetch(&out_b).unwrap();
            assert!(a[..sites * cols] == b[..sites * cols], "transposed {rows}x{cols}: the planes route differs");
            println!("MAPS224 transposed {rows}x{cols} tc_us_least={tc_least:.1} tc_us_median={tc_median:.1} planes_us_least={pl_least:.1} tile_us_least={old_least:.1} tile_us_median={old_median:.1} tc_products_a_second={:.3e} tile_products_a_second={:.3e}", products / (tc_least * 1e-6), products / (old_least * 1e-6));
        }
        assert_eq!(card.fetch(&status_buf).unwrap()[0], 0, "no word of the bench is refused");
    }

    /// [measurement; theory, November 13, P60 item 2] **The opening's comparison on the card reads the host's bits** (needs the card): a field of
    /// two carry circles with the opening's lift, its readout, current, pair return and the lift moved off zero from a keyed stream's tail and its
    /// paces moved off zero (so the paced heads' clocks are not plain and the cavity clocks differ from the standing ones), read and returned on
    /// regions of 2, 3, 5, 64 and 257 sites (written and open places, the far crowds reached) through the host and through the card: every face,
    /// every covector entry and every place's opening code equal, the covector reaching the lift, its bias, the unresolved row and the paces; and
    /// one learner's section on both, its receipt (the opening's codes with it) and its state equal.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_opening_comparison_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::{Learner, Host};
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let mut learner = Learner::new(founded, 12).with_carry(2, &keys).unwrap().with_opening().unwrap();
        let d = learner.field.declaration;
        assert!(d.opening);
        let (l, dw, f, m2) = (learner.field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.w..l.w + dw * f).chain(l.opening..l.opening + dw * dw).collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            learner.field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 14;
        }
        let paces = d.paced_heads() * (d.alphabet + 1);
        let before = tail - 4 * paces;
        for k in 0..paces {
            let word = &keys[before + 4 * k..before + 4 * k + 4];
            learner.field.theta[l.pace + k] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
        }
        let field = learner.field.clone();
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n).collect()).collect();
        let regions: Vec<Region> = classes.iter().zip(&open).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
        assert_eq!(host_faces, card_faces);
        let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g[i] != card_g[i]).collect();
        let family = |i: usize| field.families_all().iter().position(|&(s, n, _)| (s..s + n).contains(&i));
        assert!(unequal.is_empty(), "{} covector entries differ, the first at {:?} (its family {:?}; opening at {}, opening_bias at {}, pace at {})", unequal.len(), unequal.first(), unequal.first().map(|&i| family(i)), l.opening, l.opening_bias, l.pace);
        let (host_at, host_ng, host_codes) = Host.read_and_return_opening(&field, &regions).unwrap();
        let (card_at, card_ng, card_codes) = card_field.read_and_return_opening(&field, &regions).unwrap();
        assert_eq!(host_at, card_at);
        assert!(host_ng == card_ng && card_ng == card_g, "the opening's training read's covector differs");
        assert_eq!(host_codes, card_codes);
        assert_eq!(card_codes.iter().map(Vec::len).collect::<Vec<_>>(), lengths.to_vec());
        assert!(card_codes.iter().flatten().all(Option::is_some), "every place compared");
        for (name, start, len) in [("opening", l.opening, dw * dw), ("opening_bias", l.opening_bias, dw), ("unresolved row", l.enc + d.alphabet * dw, dw), ("pace", l.pace, paces)] {
            assert!(host_g[start..start + len].iter().any(|&v| v != 0), "the opening's comparison returns nothing to {name}");
        }
        // One section on the host and on the card: the receipt with the opening's codes, and the state after the deposit.
        let (mut host_learner, mut card_learner) = (learner.clone(), learner.clone());
        let host_receipt = host_learner.section_realized(&regions, &mut Host).unwrap();
        let card_receipt = card_learner.section_realized(&regions, &mut card_field).unwrap();
        assert_eq!(host_receipt, card_receipt);
        assert_eq!(card_receipt.opening.len(), regions.len());
        assert!(host_learner.to_text() == card_learner.to_text(), "the learner's state after a section differs between the host and the card");
    }

    /// [definition; theory, November 13, the design record §4.9; G145] **The level above on the card reads the host's bits**: a learner with
    /// carry circles and the opening's block, its read, out, contact, opening and pace blocks drawn, grown by a level (six harmonics after half
    /// its ticks), the level's prolongation drawn so every path of the level carries; the faces and the whole covector of a training read, and
    /// the faces of a read that does not return (the level reads the opening's news there too), equal on host and card.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_level_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::{level_declaration, level_split, Learner, Realization, Host, LEVEL_HARMONICS};
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let mut learner = Learner::new(founded, 12).with_carry(2, &keys).unwrap().with_opening().unwrap();
        let d = learner.field.declaration;
        let (l, dw, f, m2) = (learner.field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.w..l.w + dw * f).chain(l.opening..l.opening + dw * dw).collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            learner.field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 14;
        }
        let paces = d.paced_heads() * (d.alphabet + 1);
        let before = tail - 4 * paces;
        for k in 0..paces {
            let word = &keys[before + 4 * k..before + 4 * k + 4];
            learner.field.theta[l.pace + k] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
        }
        let mut leveled = learner.scaled_up(LEVEL_HARMONICS, level_split(&d), level_declaration(&d), &keys).unwrap();
        let s = leveled.field.scale.as_deref_mut().unwrap();
        let (_, _, b, _, len) = s.glue_offsets(dw);
        let back = before - 4 * (len - b) - 8;
        for (k, v) in s.glue[b..].iter_mut().enumerate() {
            let word = &keys[back + 4 * k..back + 4 * k + 4];
            *v = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
        }
        let field = leveled.field.clone();
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n).collect()).collect();
        let regions: Vec<Region> = classes.iter().zip(&open).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let cuts: Vec<usize> = regions.iter().map(|r| holonics_engine::field::level_anchors(&field.level_news(r).unwrap(), holonics_engine::field::level_section(d.alphabet)).len()).collect();
        assert!(cuts.iter().zip(&lengths).any(|(&e, &n)| e > 1 && e < n), "the fixture's news cuts some region into epochs: {cuts:?} of {lengths:?}");
        let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
        assert_eq!(host_faces, card_faces);
        let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g[i] != card_g[i]).collect();
        let family = |i: usize| field.families_all().iter().position(|&(s, n, _)| (s..s + n).contains(&i));
        assert!(unequal.is_empty(), "{} covector entries differ, the first at {:?} (its family {:?}; the fine material ends at {})", unequal.len(), unequal.first(), unequal.first().map(|&i| family(i)), field.theta.len());
        assert!(host_g[field.theta.len()..].iter().any(|&v| v != 0), "the level's covector reaches its material");
        let host_read = Host.read_faces(&field, &regions).unwrap();
        let card_read = card_field.read_faces(&field, &regions).unwrap();
        assert_eq!(host_read, card_read, "a read that does not return");
    }

    /// The lettered learner's case ([`a_lettered_learners_section_on_the_card_reads_the_hosts_bits`]): the learner, its layout and width, the
    /// fresh letters' count, and the stretches' classes, open sites and domains.
    fn lettered_case() -> (holonics_engine::field::Learner, holonics_engine::field::Loci, usize, usize, Vec<Vec<usize>>, Vec<Vec<bool>>, Vec<Option<usize>>) {
        use holonics_engine::field::Learner;
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Constitution::found(Declaration { alphabet: 100, ..declaration(32, 4, 32) }, &keys).unwrap();
        let fresh = 5usize;
        let mut learner = Learner::new(founded, 12).with_carry(2, &keys).unwrap().lettered(fresh).unwrap();
        let d = learner.field.declaration;
        assert_eq!((d.alphabet, d.carry), (100 + fresh, 2));
        let (l, dw, f, m2) = (learner.field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.w..l.w + dw * f).collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            learner.field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 14;
        }
        // [theory, November 12, P50 step 1] The paces moved off zero from the words before the tail (a rate a class on `2^(−24)`, within `±2^(−5)`), so
        // the paced heads' clocks are not plain: their skins are formed by the clock's fill and read from its store.
        let paces = d.paced_heads() * (d.alphabet + 1);
        let before = tail - 4 * paces;
        for k in 0..paces {
            let word = &keys[before + 4 * k..before + 4 * k + 4];
            learner.field.theta[l.pace + k] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
        }
        let void = 99usize;
        // Stretches: (context, run, a true end), each one state.
        let stretches = [(7usize, 33usize, true), (12, 61, false), (4, 9, true), (30, 90, false), (5, 17, true)];
        let mut classes: Vec<Vec<usize>> = Vec::new();
        let mut open: Vec<Vec<bool>> = Vec::new();
        let mut domains: Vec<Option<usize>> = Vec::new();
        for (s, &(q, a, ends)) in stretches.iter().enumerate() {
            let n = q + a + if ends { NEAR } else { 0 };
            classes.push((0..n).map(|t| if t >= q + a { void } else if (t * 7 + s) % 11 == 0 { 100 + (t + s) % fresh } else { (t * 37 + 11 * s) % 99 }).collect());
            let (u, dom) = match s % 3 {
                // A mask state over the whole stretch, and one past its context.
                0 => ((0..n).map(|t| t % 3 == 1).collect::<Vec<_>>(), Some(((4 * n * (0..n).filter(|t| t % 3 == 1).count()) as u128).isqrt() as usize)),
                1 => ((0..n).map(|t| t >= q && t % 2 == 0).collect::<Vec<_>>(), Some(((4 * (n - q) * (q..n).filter(|t| t % 2 == 0).count()) as u128).isqrt() as usize)),
                // The writer's state: the context known, the run's first places resolved, the end's voids given.
                _ => ((0..n).map(|t| t >= q + a / 4 && t < q + a).collect::<Vec<_>>(), None),
            };
            open.push(u);
            domains.push(dom);
        }
        assert!(classes.iter().flatten().any(|&c| c >= 100) && classes.iter().flatten().any(|&c| c == 99));
        (learner, l, dw, fresh, classes, open, domains)
    }

    /// [measurement; theory, November 12 (the record of the opening's room, §4 items 2 and 4)] **A lettered learner's section on the card
    /// reads the host's bits** (needs the card): a learner of 100 classes with two carry circles grown by five fresh letters
    /// ([`holonics_engine::field::Learner::lettered`]), its readout, current and pair returns moved off zero from a keyed stream's tail, takes
    /// one section of stretches as the store's trainer forms them (mask states over a whole stretch and past its context with their weighed
    /// domains, and writer's states with the first of their run resolved, a true end's near tail of voids, plain regions with no port) whose
    /// classes hold the void and fresh letters, through the host and through the card: the receipt, the material and the moments after the
    /// deposit equal, and the read and return of the same regions on the learner's field equal face for face and entry for entry, with a
    /// covector reaching the fresh letters' encoding rows.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn a_lettered_learners_section_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::Host;
        let (learner, l, dw, fresh, classes, open, domains) = lettered_case();
        let regions: Vec<Region> = classes.iter().zip(&open).zip(&domains).map(|((c, u), &dom)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: dom, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        let (host_faces, host_g) = learner.field.read_and_return(&regions).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&learner.field, &regions).unwrap();
        assert_eq!(host_faces, card_faces);
        let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g[i] != card_g[i]).collect();
        assert!(unequal.is_empty() && host_g.len() == card_g.len(), "{} covector entries differ, the first at {:?}", unequal.len(), unequal.first());
        assert!(host_g[l.enc + 100 * dw..l.enc + (100 + fresh) * dw].iter().any(|&v| v != 0), "a covector reaches the fresh letters' encoding rows");
        let (mut on_host, mut on_card) = (learner.clone(), learner.clone());
        let host_receipt = on_host.section_realized(&regions, &mut Host).unwrap();
        let card_receipt = on_card.section_realized(&regions, &mut card_field).unwrap();
        assert_eq!(host_receipt, card_receipt);
        assert!(host_receipt.deposited);
        assert_eq!(on_host.to_text(), on_card.to_text(), "the material and the moments after the deposit");
    }

    /// [theory, November 12, P50 step 3] **The turn's series on its narrow words is the wide series** (needs the card): on a sweep of the turn's
    /// arguments with its edges (zero, the least step, the faces just under a whole clock at the half turn, the largest admitted `⌊π 2^30⌉`, and every
    /// 2^13-th argument between), `turn_series_dev` and `exp_series_dev(0, b)` give the same integers on the card.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_turns_series_on_narrow_words_is_the_wide_series() {
        let top = 3_373_259_426i64;
        let mut bs: Vec<i64> = vec![0, 1, -1, 2, -2, top, -top, top - 1, -(top - 1), top - 2, -(top - 2), 1 << 31, -(1 << 31), (1 << 30) - 1, 1 << 30];
        bs.extend((-top..=top).step_by(1 << 13));
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let card_field = Resident::open(&card).unwrap();
        let out = card_field.series_check(&bs).unwrap();
        let differ: Vec<i64> = bs.iter().enumerate().filter(|(c, _)| out[4 * c] != out[4 * c + 2] || out[4 * c + 1] != out[4 * c + 3]).map(|(_, &b)| b).collect();
        assert!(differ.is_empty(), "{} of {} arguments differ, the first {:?}", differ.len(), bs.len(), differ.first());
        let (b0, bt) = (0usize, 5usize);
        assert_eq!((out[4 * b0], out[4 * b0 + 1]), (1 << 30, 0), "the zero argument's face is one");
        assert!((out[4 * bt] + (1 << 30)).abs() < 1 << 10 && out[4 * bt + 1].abs() < 1 << 10, "the largest argument turns to the half turn within the series' rounding");
        // The bound the clock's store holds a phase's parts by (P50 step 2): under `2^30 + 2^10` at every argument.
        let peak = out.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0);
        assert!(peak < (1 << 30) + (1 << 10), "a face's part {peak} past 2^30 + 2^10");
        println!("SERIES_CHECK arguments={} equal={} peak_part={peak} half_turn=({}, {})", bs.len(), bs.len() - differ.len(), out[4 * bt], out[4 * bt + 1]);
    }

    /// [theory, November 12, P50 step 1] **A skin no fill formed is refused**: the lettered learner's read and return with the clock's fill withheld
    /// (the test build writes `SKIN_UNFILLED` over the store before each fill) is refused by the card. So its readers read the clock's store, and a word
    /// no fill formed never enters a sum.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn a_skin_no_fill_formed_is_refused() {
        let (learner, _, _, _, classes, open, domains) = lettered_case();
        let regions: Vec<Region> = classes.iter().zip(&open).zip(&domains).map(|((c, u), &dom)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: dom, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        card_field.unfilled.set(true);
        let refused = card_field.read_and_return(&learner.field, &regions).map(|_| ()).expect_err("a read of a store no fill formed is refused");
        assert!(refused.to_string().contains("a skin read from the clock's store where its fill formed none"), "{refused}");
    }

    /// The strengths the mark is read at off its founding: a quarter, an eighth and three sixteenths on the material's grain (`enc`, `before`,
    /// `after`), the host's covector test's.
    const MARK_STRENGTHS: [i32; 3] = [1 << 22, 1 << 21, 3 << 20];

    /// [the ring record §4] The learners a field that reads twice is grown onto on the card, before the growth: plain (its read, out and contact
    /// blocks drawn off zero from a keyed stream's tail), with two carry circles, with the circles and the opening's lift (the lift and the paces
    /// drawn too, so the paced heads' clocks are not plain), and that learner grown by a level (its prolongation drawn).
    fn mark_cases() -> Vec<(&'static str, holonics_engine::field::Learner)> {
        use holonics_engine::field::{level_declaration, level_split, Learner, LEVEL_HARMONICS};
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Constitution::found(declaration(32, 4, 32), &keys).unwrap();
        let drawn = |mut learner: Learner, paces: bool| -> (Learner, usize) {
            let d = learner.field.declaration;
            let (l, dw, f, m2) = (learner.field.layout().clone(), d.width, d.contacts, 2 * d.complex());
            let lift = if d.opening { dw * dw } else { 0 };
            let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.w..l.w + dw * f).chain(l.opening..l.opening + lift).collect();
            let tail = keys.len() - 4 * moved.len() - 8;
            for (k, &i) in moved.iter().enumerate() {
                let word = &keys[tail + 4 * k..tail + 4 * k + 4];
                learner.field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 14;
            }
            let rates = if paces { d.paced_heads() * (d.alphabet + 1) } else { 0 };
            let before = tail - 4 * rates;
            for k in 0..rates {
                let word = &keys[before + 4 * k..before + 4 * k + 4];
                learner.field.theta[l.pace + k] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
            }
            (learner, before)
        };
        let (plain, _) = drawn(Learner::new(founded.clone(), 12), false);
        let (carry, _) = drawn(Learner::new(founded.clone(), 12).with_carry(2, &keys).unwrap(), false);
        let (opened, before) = drawn(Learner::new(founded, 12).with_carry(2, &keys).unwrap().with_opening().unwrap(), true);
        let d = opened.field.declaration;
        let mut tower = opened.scaled_up(LEVEL_HARMONICS, level_split(&d), level_declaration(&d), &keys).unwrap();
        let s = tower.field.scale.as_deref_mut().unwrap();
        let (_, _, b, _, len) = s.glue_offsets(d.width);
        let back = before - 4 * (len - b) - 8;
        for (k, v) in s.glue[b..].iter_mut().enumerate() {
            let word = &keys[back + 4 * k..back + 4 * k + 4];
            *v = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
        }
        vec![("plain", plain), ("carry", carry), ("opened", opened), ("tower", tower)]
    }

    /// [the ring record §4] The regions the mark is read on: 2, 3, 5, 64 and 257 sites (the ends with none, one and two strand mates, the far
    /// crowds reached), written and open places, and in the two longest a carried face at some open places (unresolved and not silent, so no mark
    /// there, each neighbour of a marked one), the 257 weighed by a domain.
    #[allow(clippy::type_complexity)]
    fn mark_regions() -> (Vec<Vec<usize>>, Vec<Vec<bool>>, Vec<Vec<Option<holonics_engine::field::Shares>>>, Vec<Option<usize>>) {
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n || (n > 5 && t % 7 == 2)).collect()).collect();
        let carried: Vec<Vec<Option<holonics_engine::field::Shares>>> = lengths
            .iter()
            .zip(&open)
            .map(|(&n, u)| if n < 64 { Vec::new() } else { (0..n).map(|t| (u[t] && t % 9 == 4).then(|| vec![((t * 13 % 120) as u32, 40_000u32), ((t * 29 % 120 + 1) as u32, 25_536u32)])).collect() })
            .collect();
        let domains = lengths.iter().zip(&open).map(|(&n, u)| (n == 257).then(|| 2 * u.iter().filter(|&&o| o).count())).collect();
        (classes, open, carried, domains)
    }

    /// [definition; agent-inferred, November 14, the ring record §4] **The field that reads twice on the card reads the host's bits** (needs the
    /// card): grown onto each of [`mark_cases`] ([`holonics_engine::field::Learner::with_mark`]) with its strengths at their founding
    /// and at [`MARK_STRENGTHS`], read and returned on [`mark_regions`] through the host and through the card: every face, every covector entry
    /// (the strengths' among them, nonzero), the faces of a read that does not return, the training path's words with the opening's codes, the
    /// charts by stage and the logits with their echoes equal; at the founding every face is the field's before the growth on the card too, and
    /// off it some face moves. [G180] Both reads are compared and the sum halved once, so at the founding every covector entry but the strengths'
    /// is the field's before the growth: the comparison is the one read's, bit for bit.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_field_that_reads_twice_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::{Realization, Host, MARK_BASES};
        let (classes, open, carried, domains) = mark_regions();
        let regions: Vec<Region> = (0..classes.len()).map(|r| Region { classes: &classes[r], unresolved: &open[r], faces: &carried[r], locked: &[], echo: &[], domain: domains[r], port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        for (name, learner) in mark_cases() {
            let before = card_field.read_and_return(&learner.field, &regions).unwrap();
            let marked = learner.with_mark().unwrap();
            let l = marked.field.layout().clone();
            for strengths in [[0i32; MARK_BASES], MARK_STRENGTHS] {
                let mut field = marked.field.clone();
                field.theta[l.mark..l.mark + MARK_BASES].copy_from_slice(&strengths);
                let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
                let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
                assert_eq!(host_faces, card_faces, "{name} at {strengths:?}: the faces");
                let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
                let family = |i: usize| field.families_all().iter().position(|&(s, n, _)| (s..s + n).contains(&i));
                assert!(unequal.is_empty() && host_g.len() == card_g.len(), "{name} at {strengths:?}: {} covector entries differ, the first at {:?} (its family {:?}; the strengths at {})", unequal.len(), unequal.first(), unequal.first().map(|&i| family(i)), l.mark);
                assert!(host_g[l.mark..l.mark + MARK_BASES].iter().all(|&v| v != 0), "{name} at {strengths:?}: every strength takes a covector");
                if strengths == [0; MARK_BASES] {
                    assert_eq!(card_faces, before.0, "{name}: founded at zero, every face is the field's before the growth");
                    assert!(card_g[..l.mark] == before.1[..l.mark] && card_g[l.mark + MARK_BASES..] == before.1[l.mark..], "{name}: founded at zero, both reads' mean is the one read's covector");
                } else {
                    assert_ne!(card_faces, before.0, "{name}: off the founding some face moves");
                }
                assert_eq!(Host.read_faces(&field, &regions).unwrap(), card_field.read_faces(&field, &regions).unwrap(), "{name} at {strengths:?}: a read that does not return");
                let (host_at, host_ng, host_codes) = Host.read_and_return_opening(&field, &regions).unwrap();
                let (card_at, card_ng, card_codes) = card_field.read_and_return_opening(&field, &regions).unwrap();
                assert_eq!(host_at, card_at, "{name} at {strengths:?}: the training path's words");
                assert!(host_ng == card_ng && card_ng == card_g, "{name} at {strengths:?}: the training path's covector");
                assert_eq!(host_codes, card_codes, "{name} at {strengths:?}: the opening's codes");
                let (host_cf, host_charts) = Host.read_tick_charts(&field, &regions).unwrap();
                let (card_cf, card_charts) = card_field.read_tick_charts(&field, &regions).unwrap();
                assert!(host_cf == card_cf && host_charts == card_charts, "{name} at {strengths:?}: the charts by stage");
                let (host_sf, host_scales) = Host.read_tick_scales(&field, &regions).unwrap();
                let (card_sf, card_scales) = card_field.read_tick_scales(&field, &regions).unwrap();
                assert!(host_sf == card_sf && host_scales == card_scales, "{name} at {strengths:?}: the lane powers by stage");
                assert_eq!(Host.read_logits(&field, &regions).unwrap(), card_field.read_logits(&field, &regions).unwrap(), "{name} at {strengths:?}: the logits and echoes");
                let open_sites: usize = regions.iter().map(|r| r.unresolved.iter().filter(|&&u| u).count()).sum();
                println!("MARK_PARITY field={name} strengths={strengths:?} open_sites={open_sites} covector_entries={} strengths_covector={:?} faces_equal=1 covector_equal=1", card_g.len(), &card_g[l.mark..l.mark + MARK_BASES]);
            }
        }
    }

    /// [measurement; the lead, November 18, the frontier record §6] **The known stream on the card reads the host's bits** (needs the card): each of
    /// [`mark_cases`], and each grown to read twice with its strengths at [`MARK_STRENGTHS`], under a ruler's forward at `3` (every site hears
    /// only what stands before it: the support's and the crowds' side, a still head's class count, the opening's and the moments' after rows, the
    /// odd strand contacts, the circles from the right, a region's first site; one read, the level unheard, the opening compared as the retarded
    /// one) and at `4` (one read, the level unheard), read and returned on [`mark_regions`] and on regions at the frontier (every place known but
    /// the last, weighed by their sites) through the host and through the card: every face, every covector entry, the faces of a read that does
    /// not return and the training path's words with the opening's codes equal. Under `3` the faces differ from the law's, and the level's
    /// material takes no covector under either.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_known_stream_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::{Realization, Host, MARK_BASES};
        let (mut classes, mut open, mut carried, mut domains) = mark_regions();
        for &n in &[2usize, 7, 64, 300] {
            classes.push((0..n).map(|t| (t * 53 + 5) % 120).collect());
            open.push((0..n).map(|t| t + 1 == n).collect());
            carried.push(Vec::new());
            domains.push(Some(n));
        }
        let regions: Vec<Region> = (0..classes.len()).map(|r| Region { classes: &classes[r], unresolved: &open[r], faces: &carried[r], locked: &[], echo: &[], domain: domains[r], port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        for (name, learner) in mark_cases() {
            let marked = {
                let mut m = learner.clone().with_mark().unwrap();
                let l = m.field.layout().clone();
                m.field.theta[l.mark..l.mark + MARK_BASES].copy_from_slice(&MARK_STRENGTHS);
                m
            };
            for (grown, base) in [("read once", &learner.field), ("read twice", &marked.field)] {
                let law = Host.read_faces(base, &regions).unwrap();
                for far in [3u8, 4, 9] {
                    let mut field = base.clone();
                    field.ruler_far = far;
                    let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
                    let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
                    assert_eq!(host_faces, card_faces, "{name}, {grown}, at {far}: the faces");
                    let unequal: Vec<usize> = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
                    let family = |i: usize| field.families_all().iter().position(|&(s, n, _)| (s..s + n).contains(&i));
                    assert!(unequal.is_empty(), "{name}, {grown}, at {far}: {} covector entries differ, the first at {:?} (its family {:?}; the fine material ends at {})", unequal.len(), unequal.first(), unequal.first().map(|&i| family(i)), field.theta.len());
                    assert!(host_g[..field.theta.len()].iter().any(|&v| v != 0) && host_g[field.theta.len()..].iter().all(|&v| v == 0), "{name}, {grown}, at {far}: the fine material takes a covector and the level's none");
                    assert_eq!(Host.read_faces(&field, &regions).unwrap(), card_field.read_faces(&field, &regions).unwrap(), "{name}, {grown}, at {far}: a read that does not return");
                    let (host_at, host_ng, host_codes) = Host.read_and_return_opening(&field, &regions).unwrap();
                    let (card_at, card_ng, card_codes) = card_field.read_and_return_opening(&field, &regions).unwrap();
                    assert_eq!(host_at, card_at, "{name}, {grown}, at {far}: the training path's words");
                    assert!(host_ng == card_ng && card_ng == card_g, "{name}, {grown}, at {far}: the training path's covector");
                    assert_eq!(host_codes, card_codes, "{name}, {grown}, at {far}: the opening's codes");
                    if far != 4 {
                        assert_ne!(card_faces, law, "{name}, {grown}: the known stream's faces are not the law's");
                    }
                    println!("KNOWN_STREAM_PARITY field={name} grown={grown:?} far={far} regions={} covector_entries={} faces_equal=1 covector_equal=1", regions.len(), card_g.len());
                }
                // [the region's own word] A section of the law holding known streams (`Region::before`): the regions at the frontier and every
                // third of the others carry the word, among regions of the law, in the section's order.
                // (every other known stream with its odd strand contacts facing the past, `Region::past`)
                let mixed: Vec<Region> = regions.iter().enumerate().map(|(r, region)| Region { before: region.domain == Some(region.classes.len()) || r % 3 == 1, past: r % 2 == 0, ..*region }).collect();
                assert!(mixed.iter().any(|r| r.before) && mixed.iter().any(|r| !r.before));
                let (host_faces, host_g) = base.read_and_return(&mixed).unwrap();
                let (card_faces, card_g) = card_field.read_and_return(base, &mixed).unwrap();
                assert_eq!(host_faces, card_faces, "{name}, {grown}, a section with known streams: the faces");
                let unequal: Vec<usize> = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
                let family = |i: usize| base.families_all().iter().position(|&(s, n, _)| (s..s + n).contains(&i));
                assert!(unequal.is_empty(), "{name}, {grown}, a section with known streams: {} covector entries differ, the first at {:?} (its family {:?}; the fine material ends at {})", unequal.len(), unequal.first(), unequal.first().map(|&i| family(i)), base.theta.len());
                for (r, region) in mixed.iter().enumerate() {
                    assert!((host_faces[r] == law[r]) != region.before || region.classes.len() <= 2, "{name}, {grown}: region {r} reads the law's faces exactly where it carries no word");
                }
                assert_eq!(Host.read_faces(base, &mixed).unwrap(), card_field.read_faces(base, &mixed).unwrap(), "{name}, {grown}, a section with known streams: a read that does not return");
                let (host_at, host_ng, host_codes) = Host.read_and_return_opening(base, &mixed).unwrap();
                let (card_at, card_ng, card_codes) = card_field.read_and_return_opening(base, &mixed).unwrap();
                assert_eq!(host_at, card_at, "{name}, {grown}, a section with known streams: the training path's words");
                assert!(host_ng == card_ng && card_ng == card_g, "{name}, {grown}, a section with known streams: the training path's covector");
                assert_eq!(host_codes, card_codes, "{name}, {grown}, a section with known streams: the opening's codes");
                println!("KNOWN_STREAM_PARITY field={name} grown={grown:?} section=mixed regions={} known={} faces_equal=1 covector_equal=1", mixed.len(), mixed.iter().filter(|r| r.before).count());
            }
        }
    }

    /// [definition; the lead, November 18, the frontier record §6] **A passage read by two streams on the card reads the host's bits** (needs
    /// the card): on each of [`mark_cases`], and each grown to read twice with its strengths at [`MARK_STRENGTHS`], passages of 2, 3, 7, 64
    /// and 300 places carrying the word (`Region::strand`: the known stream and an open place at every place, each on the bare clock and
    /// reading the retarded cavity moment of its place), alone and in a section beside regions of the law and known streams, read and
    /// returned through the host (`Constitution::strand_pass`, `strand_returned`) and through the card: every open place's face, every
    /// covector entry, the faces of a read that does not return and the training path's words with the opening's codes equal, and a
    /// passage's faces are one a place with none at the first.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn a_passage_read_by_two_streams_on_the_card_reads_the_hosts_bits() {
        use holonics_engine::field::{Realization, Host, MARK_BASES};
        let lengths = [2usize, 3, 7, 64, 300];
        let passages: Vec<Vec<usize>> = lengths.iter().enumerate().map(|(k, &n)| (0..n).map(|t| (t * 53 + 5 + 17 * k) % 120).collect()).collect();
        let known: Vec<Vec<bool>> = lengths.iter().map(|&n| vec![false; n]).collect();
        // (the passages of 3 and 64 places with their odd strand contacts facing the past, `Region::past`; then every one of them)
        let strands: Vec<Region> = passages.iter().zip(&known).enumerate().map(|(k, (c, u))| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past: k % 2 == 1, second: false, targets: None, stretches: None }).collect();
        let faced: Vec<Region> = strands.iter().map(|r| Region { past: true, ..*r }).collect();
        let (classes, open, carried, domains) = mark_regions();
        let others: Vec<Region> = (0..classes.len()).map(|r| Region { classes: &classes[r], unresolved: &open[r], faces: &carried[r], locked: &[], echo: &[], domain: domains[r], port: None, before: r % 2 == 1, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        // A section of the law's regions, known streams and passages read by two streams, interleaved.
        let mixed: Vec<Region> = others.iter().zip(&strands).flat_map(|(a, b)| [*a, *b]).collect();
        // [the record of the two streams §15] The same section with the row of the site after reading the second site before
        // (`Region::second`) in every one-sided region, the odd contacts facing the past in every other one.
        let seconded: Vec<Region> = mixed.iter().enumerate().map(|(k, r)| if r.before || r.strand { Region { second: true, past: k % 4 < 2, ..*r } } else { *r }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        // [the record of the two streams §11] A fifth field: the tower opened to one-sided streams (`Learner::level_before`), its block
        // drawn (the law's prolongation's words in another order), so a strand hears the level: each place the epoch before its own.
        let mut cases = mark_cases();
        {
            let tower = cases.iter().find(|(name, _)| *name == "tower").map(|(_, l)| l.clone()).expect("the tower among the cases");
            let mut level = tower.level_before().unwrap();
            let width = level.field.declaration.width;
            let s = level.field.scale.as_deref_mut().unwrap();
            let (_, _, b, bb, len) = s.glue_offsets(width);
            let (b2, bb2, end) = s.before_offsets(width).unwrap();
            for k in 0..bb - b {
                s.glue[b2 + k] = s.glue[b + (bb - b - 1 - k)];
            }
            for k in 0..len - bb {
                s.glue[bb2 + k] = s.glue[bb + (len - bb - 1 - k)];
            }
            assert_eq!(end, s.glue.len());
            cases.push(("level", level));
        }
        for (name, learner) in cases {
            let marked = {
                let mut m = learner.clone().with_mark().unwrap();
                let l = m.field.layout().clone();
                m.field.theta[l.mark..l.mark + MARK_BASES].copy_from_slice(&MARK_STRENGTHS);
                m
            };
            for (grown, field) in [("read once", &learner.field), ("read twice", &marked.field)] {
                for (section, regions) in [("strands", &strands), ("strands facing the past", &faced), ("mixed", &mixed), ("mixed with the second row", &seconded)] {
                    let (host_faces, host_g) = field.read_and_return(regions).unwrap();
                    let (card_faces, card_g) = card_field.read_and_return(field, regions).unwrap();
                    for (r, region) in regions.iter().enumerate().filter(|(_, region)| region.strand) {
                        assert!(host_faces[r].len() == region.classes.len() && host_faces[r][0].is_none() && host_faces[r][1..].iter().all(Option::is_some), "{name}, {grown}, {section}: region {r} has a face a place past the first");
                    }
                    let (hf, cf) = (&host_faces, &card_faces);
                    let apart: Vec<(usize, usize)> = (0..regions.len()).flat_map(|r| (0..hf[r].len().max(cf[r].len())).filter(move |&t| hf[r].get(t) != cf[r].get(t)).map(move |t| (r, t))).collect();
                    assert!(apart.is_empty(), "{name}, {grown}, {section}: {} faces differ, the first at region and place {:?} (the region a strand: {:?})", apart.len(), apart.first(), apart.first().map(|&(r, _)| regions[r].strand));
                    let unequal: Vec<usize> = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
                    let family = |i: usize| field.families_all().iter().position(|&(s, n, _)| (s..s + n).contains(&i));
                    let families: std::collections::BTreeSet<Option<usize>> = unequal.iter().map(|&i| family(i)).collect();
                    assert!(unequal.is_empty(), "{name}, {grown}, {section}: {} covector entries differ, the first at {:?} (the families {:?}; the fine material ends at {})", unequal.len(), unequal.first(), families, field.theta.len());
                    assert_eq!(Host.read_faces(field, regions).unwrap(), card_field.read_faces(field, regions).unwrap(), "{name}, {grown}, {section}: a read that does not return");
                    let (host_at, host_ng, host_codes) = Host.read_and_return_opening(field, regions).unwrap();
                    let (card_at, card_ng, card_codes) = card_field.read_and_return_opening(field, regions).unwrap();
                    assert_eq!(host_at, card_at, "{name}, {grown}, {section}: the training path's words");
                    assert!(host_ng == card_ng && card_ng == card_g, "{name}, {grown}, {section}: the training path's covector");
                    assert_eq!(host_codes, card_codes, "{name}, {grown}, {section}: the opening's codes");
                    println!("STRAND_PARITY field={name} grown={grown:?} section={section} regions={} places_compared={} covector_entries={} faces_equal=1 covector_equal=1", regions.len(), regions.iter().filter(|r| r.strand).map(|r| r.classes.len() - 1).sum::<usize>(), card_g.len());
                }
            }
        }
    }

    /// [definition; the lead, November 18, the record of the two streams §11] **The level a strand hears, on the card, step by step**
    /// (needs the card): the tower with its one-sided block at its founding and drawn, one passage of 2, 3, 7 and 64 places at a time,
    /// with and without the odd contacts facing the past: the forward alone and then the return, each the host's bits and none refused.
    /// (Its first runs were refused at random with a released value past its carrier: the news was read at the open places, whose rows
    /// of the opening's face are not formed. `field_level_news_strand` reads the known sites alone.)
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_level_a_strand_hears_on_the_card_step_by_step() {
        use holonics_engine::field::{Realization, Host};
        let tower = mark_cases().into_iter().find(|(name, _)| *name == "tower").map(|(_, l)| l).expect("the tower among the cases");
        let founded = tower.level_before().unwrap();
        let mut live = founded.clone();
        {
            let width = live.field.declaration.width;
            let s = live.field.scale.as_deref_mut().unwrap();
            let (_, _, b, bb, len) = s.glue_offsets(width);
            let (b2, bb2, _) = s.before_offsets(width).unwrap();
            for k in 0..bb - b {
                s.glue[b2 + k] = s.glue[b + (bb - b - 1 - k)];
            }
            for k in 0..len - bb {
                s.glue[bb2 + k] = s.glue[bb + (len - bb - 1 - k)];
            }
        }
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        for (state, learner) in [("founded", &founded), ("live", &live)] {
            let field = &learner.field;
            for n in [2usize, 3, 7, 64] {
                let classes: Vec<usize> = (0..n).map(|t| (t * 53 + 5) % 120).collect();
                let known = vec![false; n];
                for past in [false, true] {
                    let regions = [Region { classes: &classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past, second: false, targets: None, stretches: None }];
                    let host_faces = Host.read_faces(field, &regions).unwrap();
                    let forward = card_field.read_faces(field, &regions);
                    let forward_line = match &forward {
                        Ok(f) => format!("ok equal={} first_apart={:?}", *f == host_faces, (0..n).find(|&t| f[0].get(t) != host_faces[0].get(t))),
                        Err(e) => format!("refused: {e}"),
                    };
                    let (_, host_g) = field.read_and_return(&regions).unwrap();
                    let returned = card_field.read_and_return(field, &regions);
                    let return_line = match &returned {
                        Ok((f, g)) => {
                            let unequal: Vec<usize> = (0..host_g.len().max(g.len())).filter(|&i| host_g.get(i) != g.get(i)).collect();
                            let families: std::collections::BTreeSet<Option<usize>> = unequal.iter().map(|&i| field.families_all().iter().position(|&(s, len, _)| (s..s + len).contains(&i))).collect();
                            format!("ok faces_equal={} covector_apart={} families={:?} of {}", *f == host_faces, unequal.len(), families, field.families_all().len())
                        }
                        Err(e) => format!("refused: {e}"),
                    };
                    println!("LEVEL_STEP state={state} places={n} past={past} forward: {forward_line} | return: {return_line}");
                    assert!(matches!(&forward, Ok(f) if *f == host_faces), "{state}, {n} places, past {past}: the forward's faces are the host's");
                    assert!(matches!(&returned, Ok((f, g)) if *f == host_faces && *g == host_g), "{state}, {n} places, past {past}: the return's faces and covector are the host's");
                }
            }
        }
    }

    /// [definition; the lead, November 23] **The level's receipt on the card reads the host's bits** (needs the card; `Scale::receipt`): the
    /// tower with its one-sided block drawn and its level compared at its own grain, one passage of 3, 7 and 64 places at a time, with and
    /// without the odd contacts facing the past, read and returned through the host and through the card: every face and every covector
    /// entry equal, the faces those without the receipt and the covector not.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_levels_receipt_on_the_card_reads_the_hosts_bits() {
        let tower = mark_cases().into_iter().find(|(name, _)| *name == "tower").map(|(_, l)| l).expect("the tower among the cases");
        let mut live = tower.level_before().unwrap();
        {
            let width = live.field.declaration.width;
            let s = live.field.scale.as_deref_mut().unwrap();
            let (_, _, b, bb, len) = s.glue_offsets(width);
            let (b2, bb2, _) = s.before_offsets(width).unwrap();
            for k in 0..bb - b {
                s.glue[b2 + k] = s.glue[b + (bb - b - 1 - k)];
            }
            for k in 0..len - bb {
                s.glue[bb2 + k] = s.glue[bb + (len - bb - 1 - k)];
            }
        }
        let plain = live.field.clone();
        let mut field = plain.clone();
        field.scale.as_deref_mut().unwrap().receipt = true;
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        for n in [3usize, 7, 64] {
            let classes: Vec<usize> = (0..n).map(|t| (t * 53 + 5) % 120).collect();
            let known = vec![false; n];
            for past in [false, true] {
                let regions = [Region { classes: &classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past, second: false, targets: None, stretches: None }];
                let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
                let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
                let unequal = (0..host_g.len().max(card_g.len())).filter(|&i| host_g.get(i) != card_g.get(i)).count();
                println!("LEVEL_RECEIPT_PARITY places={n} past={past} faces_equal={} covector_apart={unequal} of {}", host_faces == card_faces, card_g.len());
                assert_eq!(host_faces, card_faces, "{n} places, past {past}: the faces are the host's");
                assert_eq!(unequal, 0, "{n} places, past {past}: the covector is the host's");
                let (plain_faces, plain_g) = card_field.read_and_return(&plain, &regions).unwrap();
                assert_eq!(plain_faces, card_faces, "{n} places, past {past}: the receipt moves no face");
                if n > 3 {
                    assert_ne!(plain_g, card_g, "{n} places, past {past}: the receipt moves the covector");
                }
            }
        }
    }

    /// [definition; agent-inferred, November 14, the ring record §4] **A marked learner's sections on the card read the host's bits** (needs the
    /// card): each of [`mark_cases`] and the lettered learner grown to read twice, its strengths at [`MARK_STRENGTHS`], takes two sections on
    /// [`mark_regions`] (the lettered one on its own stretches) through the host ([`holonics_engine::field::Host`]) and through the card:
    /// the receipts and the learner's whole state (the material, the strengths among it, and the moments) equal after each. [G180] Each section
    /// compares both reads and deposits their mean.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn a_marked_learners_sections_on_the_card_read_the_hosts_bits() {
        use holonics_engine::field::{Host, MARK_BASES};
        let (classes, open, carried, domains) = mark_regions();
        let regions: Vec<Region> = (0..classes.len()).map(|r| Region { classes: &classes[r], unresolved: &open[r], faces: &carried[r], locked: &[], echo: &[], domain: domains[r], port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let (lettered, _, _, _, lclasses, lopen, ldomains) = lettered_case();
        let lregions: Vec<Region> = lclasses.iter().zip(&lopen).zip(&ldomains).map(|((c, u), &dom)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: dom, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        let mut cases = mark_cases();
        cases.push(("lettered", lettered));
        for (name, learner) in cases {
            let mut marked = learner.with_mark().unwrap();
            let l = marked.field.layout().clone();
            marked.field.theta[l.mark..l.mark + MARK_BASES].copy_from_slice(&MARK_STRENGTHS);
            let on = if name == "lettered" { &lregions } else { &regions };
            let (mut on_host, mut on_card) = (marked.clone(), marked);
            for section in 0..2 {
                let host_receipt = on_host.section_realized(on, &mut Host).unwrap();
                let card_receipt = on_card.section_realized(on, &mut card_field).unwrap();
                assert_eq!(host_receipt, card_receipt, "{name}: section {section}'s receipt");
                assert!(host_receipt.deposited, "{name}: section {section} deposits");
                assert!(on_host.to_text() == on_card.to_text(), "{name}: the learner's state after section {section} differs between the host and the card");
                println!("MARK_SECTION field={name} section={section} code_before={} strengths={:?} state_equal=1", card_receipt.code_before, &on_card.field.theta[l.mark..l.mark + MARK_BASES]);
            }
        }
    }

    /// [measurement; the ring record §4] **The two reads' time on the card against one read** (needs the card): the opened learner's field before
    /// the growth and grown to read twice at [`MARK_STRENGTHS`], each read and returned (a training read; [G180] both reads return) and read without a return on one batch of 32 regions of 257
    /// sites (the open places of [`mark_regions`]'s longest), timed inside one hold as control, marked, control, marked, control after a warm read
    /// of each; the control's spread is the read's resolution.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_field_that_reads_twice_times_its_two_reads_on_the_card() {
        use holonics_engine::field::MARK_BASES;
        let (classes, open, _, _) = mark_regions();
        let regions: Vec<Region> = (0..32).map(|_| Region { classes: &classes[4], unresolved: &open[4], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect();
        let (_, learner) = mark_cases().into_iter().find(|(n, _)| *n == "opened").unwrap();
        let plain = learner.field.clone();
        let mut marked = learner.with_mark().unwrap().field;
        let l = marked.layout().clone();
        marked.theta[l.mark..l.mark + MARK_BASES].copy_from_slice(&MARK_STRENGTHS);
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = Resident::open(&card).unwrap();
        let sites = regions.len() * classes[4].len();
        let open_sites = regions.len() * open[4].iter().filter(|&&u| u).count();
        // A training read (read and return) and a read that does not return, each in its own interleaved hold.
        for returning in [true, false] {
            let mut timed = |field: &Constitution| -> u128 {
                let started = Instant::now();
                if returning {
                    card_field.read_and_return(field, &regions).unwrap();
                } else {
                    card_field.read_faces(field, &regions).unwrap();
                }
                started.elapsed().as_micros()
            };
            timed(&plain);
            timed(&marked);
            let reads: Vec<(&str, u128)> = [("control", &plain), ("marked", &marked), ("control", &plain), ("marked", &marked), ("control", &plain)].into_iter().map(|(n, f)| (n, timed(f))).collect();
            println!("MARK_TIMES returning={} sites={sites} open_sites={open_sites} reads_us={}", u8::from(returning), reads.iter().map(|(n, us)| format!("{n}:{us}")).collect::<Vec<_>>().join(","));
        }
    }
}
