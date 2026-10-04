//! [definition; agent-inferred, October 4; the reception carry §10] **The resident's passage in a
//! continuing state**: what a resident holds between two receiving windows beside its constitution
//! and its carried end, so a saved resident continues the cut where it stopped.
//!
//! Retention is the future-sufficient quotient of the whole resident. Between windows the
//! resident's future reads, beside the constitution and the carry: the lift point (the rings'
//! configuration and windings), the open source moment (its phase-carried counts, the held cells
//! its declared offsets read, and its opening), the aeon in progress (its opening lift point, its
//! cells, whether its carry-out awaits the boundary), the first law's balance of that aeon, the
//! charts the next refinements start from, the address register (the last `D` letters and the
//! clocks its reader reads), and the admitted family's declared ranks. Nothing else is read again:
//! no handle is open between windows (a saved resident refuses one), the arrived targets are
//! replaced by the next window's compare before any deposit or boundary reads them, and the tally,
//! the wall times and the released bits are readings.

use super::*;
use crate::aeon::EnclosedBalance;
use crate::hnn::constitution::ContinuingState;
use crate::hnn::state_text::{Next, counted, keyed, refused, value, values};

impl Resident {
    /// [definition; agent-inferred, October 4; the reception carry §10] **The resident's continuing
    /// state**: its constitution's learned material ([`Constitution::continuing_state`]), its
    /// carried end, and its passage (the module header). Refused where a handle is open (a pending
    /// ratio or a staged deposit: the state is taken between windows), where deposits have stopped,
    /// or where more than one moment is open.
    pub fn continuing_state(&self, ring: usize) -> Result<ContinuingState, HnnError> {
        if !self.pending.is_empty() || !self.staged.is_empty() {
            return refused("a resident with an open pending ratio or staged deposit");
        }
        if self.stop.is_some() {
            return refused("a resident whose deposits have stopped");
        }
        if self.moments.len() > 1 {
            return refused("a resident with more than one open moment");
        }
        let passage = self.moments.values().next().map(|moment| {
            let mut s = String::new();
            line(&mut s, "lift", self.current.lift());
            moment.write(&mut s);
            s += &format!(
                "aeon {} {} {} {}\n",
                u8::from(self.aeon.awaiting),
                u8::from(self.aeon.keys_admitted),
                self.aeon.cells,
                self.aeon.closed
            );
            line(&mut s, "aeon-opening", &self.aeon.opening);
            write_balance(&mut s, self.ledger.balance());
            self.charts.write(&mut s);
            self.address.write(&mut s);
            line(&mut s, "ranks", self.admitted.iter().map(ReceivingPhases::rank));
            s
        });
        Ok(self
            .constitution
            .continuing_state(ring)?
            .with_carry(self.carried.clone())
            .with_passage(passage))
    }

    /// **Place a saved passage on a resident mounted at its restored constitution** (the module
    /// header): the lift point, the moment, the aeon in progress, the first law's balance, the
    /// charts, the register and the admitted ranks. Refused, typed, where any part is out of its
    /// form or of the field's declared shape.
    pub(super) fn with_passage(mut self, text: &str) -> Result<Self, HnnError> {
        let field = self.field.clone();
        let mut lines = text.lines();
        let mut next = |what: &'static str| lines.next().ok_or(HnnError::ContinuingState { what });
        let lift: Vec<BigInt> = values(&keyed(next("the lift point")?, "lift", "the lift point")?, "the lift point")?;
        let current = Current::at(&field, lift)?;
        let head = next("the moment")?;
        let moment = SourceMoment::read(&field, head, &mut next)?;
        let aeon: Vec<u64> = counted(next("the aeon")?, "aeon", 4, "the aeon")?;
        if aeon[0] > 1 || aeon[1] > 1 {
            return refused("the aeon");
        }
        let opening: Vec<BigInt> = values(
            &keyed(next("the aeon's opening")?, "aeon-opening", "the aeon's opening")?,
            "the aeon's opening",
        )?;
        if opening.len() != field.rings().len() {
            return refused("the aeon's opening against the field's rings");
        }
        let balance = read_balance(&mut next)?;
        let charts = Charts::read(next("the charts")?, &mut next)?;
        let address = self
            .address
            .clone()
            .continued(next("the address register")?, &mut next)?;
        let ranks: Vec<usize> = values(&keyed(next("the ranks")?, "ranks", "the ranks")?, "the ranks")?;
        if ranks.len() != self.admitted.len() || next("the passage's end").is_ok() {
            return refused("the passage's ranks or its end");
        }
        self.current = current;
        let id = MomentId(self.fresh());
        self.moments.insert(id, moment);
        self.aeon = AeonState {
            awaiting: aeon[0] == 1,
            keys_admitted: aeon[1] == 1,
            opening,
            cells: aeon[2],
            closed: aeon[3],
        };
        self.ledger = EnclosedLedger::resumed(balance);
        self.charts = charts;
        self.address = address;
        self.admitted = self
            .admitted
            .into_iter()
            .zip(ranks)
            .map(|(phases, rank)| phases.with_rank(rank))
            .collect();
        Ok(self)
    }
}

fn line<T: ToString>(s: &mut String, key: &str, values: impl IntoIterator<Item = T>) {
    crate::hnn::state_text::line(s, key, values);
}

fn write_interval(s: &mut String, key: &str, interval: Option<&ExactInterval>) {
    match interval {
        Some(interval) => line(s, key, [&interval.lower, &interval.upper]),
        None => line(s, key, ["-"]),
    }
}

/// The first law's balance of the aeon in progress: `ledger exchanges depositions arrivals cells
/// widening`, then its enclosures `exchange`, `deposition`, `opening`, `closing`, `arrived`, each
/// `lower upper` (or `-` before any reading).
fn write_balance(s: &mut String, balance: &EnclosedBalance) {
    *s += &format!(
        "ledger {} {} {} {} {}\n",
        balance.exchanges, balance.depositions, balance.arrivals, balance.cells, balance.widening
    );
    write_interval(s, "exchange", Some(&balance.exchange));
    write_interval(s, "deposition", Some(&balance.deposition));
    write_interval(s, "opening", balance.opening.as_ref());
    write_interval(s, "closing", balance.closing.as_ref());
    write_interval(s, "arrived", Some(&balance.arrived));
}

fn read_interval(line: &str, key: &str, what: &'static str) -> Result<Option<ExactInterval>, HnnError> {
    let words = keyed(line, key, what)?;
    match words[..] {
        ["-"] => Ok(None),
        [lower, upper] => Ok(Some(ExactInterval {
            lower: value(Some(&lower), what)?,
            upper: value(Some(&upper), what)?,
        })),
        _ => refused(what),
    }
}

fn read_balance<'a>(next: Next<'_, 'a>) -> Result<EnclosedBalance, HnnError> {
    let what = "the first law's balance";
    let words = keyed(next(what)?, "ledger", what)?;
    let [exchanges, depositions, arrivals, cells, widening] = words[..] else {
        return refused(what);
    };
    let whole = |interval: Option<ExactInterval>| interval.ok_or(HnnError::ContinuingState { what });
    Ok(EnclosedBalance {
        exchanges: value(Some(&exchanges), what)?,
        depositions: value(Some(&depositions), what)?,
        arrivals: value(Some(&arrivals), what)?,
        cells: value(Some(&cells), what)?,
        widening: value(Some(&widening), what)?,
        exchange: whole(read_interval(next(what)?, "exchange", what)?)?,
        deposition: whole(read_interval(next(what)?, "deposition", what)?)?,
        opening: read_interval(next(what)?, "opening", what)?,
        closing: read_interval(next(what)?, "closing", what)?,
        arrived: whole(read_interval(next(what)?, "arrived", what)?)?,
    })
}
