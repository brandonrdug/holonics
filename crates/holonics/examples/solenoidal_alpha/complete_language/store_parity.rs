//! `parity-store`: the card's realization of the store line held against the host's (C2 of the consolidation, #603; the plan's §8,
//! "Parity"). The command is `train-store` itself, run through a realization that asks both the card and the host ([`HostField`]) for
//! every read and compares their results whole. The learner is given the card's, so the run trains as the line trains and its
//! `STORE_SECTION` lines are the line's own (a reproduction of the sections it runs, read by `tools/reproduction.py`).
//!
//! [agent-inferred, November 14] Why one learner and every read compared. The deposit is host code, and every value it consumes from a
//! realization crosses one of the trait's calls, so a learner fed equal reads holds equal bytes. Comparing each read at the call is the
//! learners' comparison taken at its source, with the first unequal read named where it arises rather than where it surfaces. The parity
//! of November 2 (`parity-field`) recorded only the face and covector reads and let the opening's path fall to the trait's default, which
//! would leave the store line's own path (`read_and_return_opening` on the card) unchecked. Here every method the card overrides is
//! forwarded to its override.

use super::*;
use holonics::hnn::tower::field::{BlankClocks, CarryGates, Field, FieldRead, FieldRealization, HeldRows, HostField, NearOffsets, RealizationCounters, Region, RowCurrent, TickRead};
use holonics::hnn::tower::{TowerError, TowerFace};
use std::collections::BTreeMap;
use std::time::Instant;

type Faces = Vec<Vec<Option<TowerFace>>>;
type Reads<T> = std::result::Result<T, TowerError>;

/// The card beside the host: each call asked of both, the card's result returned, every pair compared.
struct Paired<'a> {
    card: &'a mut dyn FieldRealization,
    host: HostField,
    /// By method: calls, unequal calls, the card's and the host's nanoseconds.
    calls: BTreeMap<&'static str, (u64, u64, u128, u128)>,
    /// The training path's unequal sites and covector entries, summed over its calls.
    sites: u64,
    entries: u64,
    first: Option<String>,
}

impl<'a> Paired<'a> {
    fn new(card: &'a mut dyn FieldRealization) -> Self {
        Paired { card, host: HostField, calls: BTreeMap::new(), sites: 0, entries: 0, first: None }
    }

    fn both<T: PartialEq>(&mut self, method: &'static str, card: impl FnOnce(&mut dyn FieldRealization) -> Reads<T>, host: impl FnOnce(&mut HostField) -> Reads<T>) -> Reads<T> {
        let t = Instant::now();
        let c = card(&mut *self.card);
        let card_ns = t.elapsed().as_nanos();
        let t = Instant::now();
        let h = host(&mut self.host);
        let host_ns = t.elapsed().as_nanos();
        let entry = self.calls.entry(method).or_default();
        entry.0 += 1;
        entry.2 += card_ns;
        entry.3 += host_ns;
        let call = entry.0;
        match (c, h) {
            (Ok(c), Ok(h)) => {
                if c != h {
                    entry.1 += 1;
                    self.first.get_or_insert(format!("{method} call {call}"));
                }
                Ok(c)
            }
            (Err(e), Err(_)) => Err(e),
            (Ok(_), Err(e)) => {
                entry.1 += 1;
                self.first.get_or_insert(format!("{method} call {call}: the host refused ({e:?}) what the card returned"));
                Err(TowerError::Refused("parity: the host refused a read the card returned"))
            }
            (Err(e), Ok(_)) => {
                entry.1 += 1;
                self.first.get_or_insert(format!("{method} call {call}: the card refused ({e:?}) what the host returned"));
                Err(e)
            }
        }
    }

    /// The training path's two results compared by site and by covector entry, so a difference is named where it stands.
    #[allow(clippy::type_complexity)]
    fn locate(&mut self, field: &Field, call: u64, card: &(Vec<Vec<Option<(u128, u128)>>>, Vec<i128>, Vec<Vec<Option<i64>>>), host: &(Vec<Vec<Option<(u128, u128)>>>, Vec<i128>, Vec<Vec<Option<i64>>>)) {
        for (r, (c, h)) in card.0.iter().zip(&host.0).enumerate() {
            for (t, (a, b)) in c.iter().zip(h).enumerate() {
                if a != b {
                    self.sites += 1;
                    self.first.get_or_insert(format!("read_and_return_opening call {call}: region {r} site {t} card {a:?} host {b:?}"));
                }
            }
            self.sites += c.len().abs_diff(h.len()) as u64;
        }
        let families = field.families_all();
        for (i, (a, b)) in card.1.iter().zip(&host.1).enumerate() {
            if a != b {
                self.entries += 1;
                let family = families.iter().position(|&(start, len, _)| i < start + len).unwrap_or(families.len());
                self.first.get_or_insert(format!("read_and_return_opening call {call}: covector entry {i} (family {family}) card {a} host {b}"));
            }
        }
        self.entries += card.1.len().abs_diff(host.1.len()) as u64;
        if card.2 != host.2 {
            self.first.get_or_insert(format!("read_and_return_opening call {call}: the opening's codes differ"));
        }
    }

    fn unequal(&self) -> u64 {
        self.calls.values().map(|v| v.1).sum()
    }
}

impl FieldRealization for Paired<'_> {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Reads<(Faces, Vec<i128>)> {
        self.both("read_and_return", |c| c.read_and_return(field, regions), |h| h.read_and_return(field, regions))
    }
    fn read_and_return_at_class(&mut self, field: &Field, regions: &[Region]) -> Reads<(Vec<Vec<Option<(u128, u128)>>>, Vec<i128>)> {
        self.both("read_and_return_at_class", |c| c.read_and_return_at_class(field, regions), |h| h.read_and_return_at_class(field, regions))
    }
    #[allow(clippy::type_complexity)]
    fn read_and_return_opening(&mut self, field: &Field, regions: &[Region]) -> Reads<(Vec<Vec<Option<(u128, u128)>>>, Vec<i128>, Vec<Vec<Option<i64>>>)> {
        // The training path keeps both results to name a difference by site and entry.
        let t = Instant::now();
        let c = self.card.read_and_return_opening(field, regions);
        let card_ns = t.elapsed().as_nanos();
        let t = Instant::now();
        let h = self.host.read_and_return_opening(field, regions);
        let host_ns = t.elapsed().as_nanos();
        let entry = self.calls.entry("read_and_return_opening").or_default();
        entry.0 += 1;
        entry.2 += card_ns;
        entry.3 += host_ns;
        let call = entry.0;
        match (c, h) {
            (Ok(c), Ok(h)) => {
                if c != h {
                    self.calls.entry("read_and_return_opening").or_default().1 += 1;
                    self.locate(field, call, &c, &h);
                }
                Ok(c)
            }
            (Err(e), Err(_)) => Err(e),
            (Ok(_), Err(e)) => {
                entry.1 += 1;
                self.first.get_or_insert(format!("read_and_return_opening call {call}: the host refused ({e:?}) what the card returned"));
                Err(TowerError::Refused("parity: the host refused a read the card returned"))
            }
            (Err(e), Ok(_)) => {
                entry.1 += 1;
                self.first.get_or_insert(format!("read_and_return_opening call {call}: the card refused ({e:?}) what the host returned"));
                Err(e)
            }
        }
    }
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Reads<Faces> {
        self.both("read_faces", |c| c.read_faces(field, regions), |h| h.read_faces(field, regions))
    }
    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> Reads<Vec<FieldRead>> {
        self.both("read_logits", |c| c.read_logits(field, regions), |h| h.read_logits(field, regions))
    }
    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> Reads<Vec<Vec<(usize, u64)>>> {
        self.both("read_landmarks", |c| c.read_landmarks(field, region, question, sites, count), |h| h.read_landmarks(field, region, question, sites, count))
    }
    fn met_pairs(&self) -> Option<u128> {
        self.card.met_pairs()
    }
    fn counters(&self) -> Option<RealizationCounters> {
        self.card.counters()
    }
    fn read_row_shares(&mut self, field: &Field, regions: &[Region], questions: &[usize]) -> Reads<Vec<HeldRows>> {
        self.both("read_row_shares", |c| c.read_row_shares(field, regions, questions), |h| h.read_row_shares(field, regions, questions))
    }
    fn read_covector_shares(&mut self, field: &Field, regions: &[Region]) -> Reads<Vec<[u128; 2]>> {
        self.both("read_covector_shares", |c| c.read_covector_shares(field, regions), |h| h.read_covector_shares(field, regions))
    }
    fn read_row_currents(&mut self, field: &Field, regions: &[Region], questions: &[usize], returning: bool) -> Reads<Vec<Vec<RowCurrent>>> {
        self.both("read_row_currents", |c| c.read_row_currents(field, regions, questions, returning), |h| h.read_row_currents(field, regions, questions, returning))
    }
    fn read_ticks(&mut self, field: &Field, regions: &[Region]) -> Reads<Vec<Vec<TickRead>>> {
        self.both("read_ticks", |c| c.read_ticks(field, regions), |h| h.read_ticks(field, regions))
    }
    fn read_tick_charts(&mut self, field: &Field, regions: &[Region]) -> Reads<(Faces, Vec<Vec<Vec<i32>>>)> {
        self.both("read_tick_charts", |c| c.read_tick_charts(field, regions), |h| h.read_tick_charts(field, regions))
    }
    fn read_faces_gated(&mut self, field: &Field, regions: &[Region]) -> Reads<(Faces, CarryGates)> {
        self.both("read_faces_gated", |c| c.read_faces_gated(field, regions), |h| h.read_faces_gated(field, regions))
    }
    fn read_near_offsets(&mut self, field: &Field, region: &Region, sites: &[usize]) -> Reads<Vec<NearOffsets>> {
        self.both("read_near_offsets", |c| c.read_near_offsets(field, region, sites), |h| h.read_near_offsets(field, region, sites))
    }
    fn read_blank_clocks(&mut self, field: &Field, region: &Region, sites: &[usize]) -> Reads<Vec<BlankClocks>> {
        self.both("read_blank_clocks", |c| c.read_blank_clocks(field, region, sites), |h| h.read_blank_clocks(field, region, sites))
    }
}

/// `parity-store` with `train-store`'s arguments: the store line's sections from `FROM`, each read asked of the card and the host and
/// compared whole (above). Prints `STORE_PARITY` a method (calls, unequal calls, the card's and the host's milliseconds), the training
/// path's unequal sites and covector entries, the first difference, and `STORE_PARITY_DONE` with `EQUAL` or `DIFFERS`. A difference
/// is an error, so the command's exit is the gate's.
pub(super) fn parity(args: &[String], card: &mut dyn FieldRealization) -> Result<()> {
    let mut paired = Paired::new(card);
    let trained = super::store_train::train(args, &mut paired);
    for (method, (calls, unequal, card_ns, host_ns)) in &paired.calls {
        println!("STORE_PARITY method={method} calls={calls} unequal={unequal} card_ms={} host_ms={}", card_ns / 1_000_000, host_ns / 1_000_000);
    }
    let unequal = paired.unequal();
    println!(
        "STORE_PARITY_DONE calls={} unequal={unequal} unequal_sites={} unequal_entries={} first={} {}",
        paired.calls.values().map(|v| v.0).sum::<u64>(),
        paired.sites,
        paired.entries,
        paired.first.as_deref().unwrap_or("-").replace(' ', "_"),
        if unequal == 0 && trained.is_ok() { "EQUAL" } else { "DIFFERS" }
    );
    trained?;
    if unequal > 0 {
        return Err(format!("parity-store: {unequal} reads of the card differ from the host's").into());
    }
    Ok(())
}
