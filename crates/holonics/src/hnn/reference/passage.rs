//! [definition; agent-inferred, October 4] The whole resident passage, format version 2.
//!
//! Retain exactly the operands admitted future actions may read: the lift, optional one open
//! moment, aeon, first-law balance, charts, address including held contact-site kinds,
//! admitted declaring phases, handle counter and the one arrived comparison/opening.
//! Arrived is a bounded contemporary operand, not a history or a frozen material cut.
//! Immediate close, or ingest then close without another compare, may read it.
//!
//! An unversioned passage cannot reconstruct omitted arrived operands or held kinds and is
//! refused at mount. Constitution-only states remain a narrower remount. No legacy passage
//! decoder, inferred empty Arrived or borrowed live predecessor is admitted.

use super::*;
use crate::aeon::EnclosedBalance;
use crate::hnn::constitution::ContinuingState;
use crate::hnn::state_text::{Next, counted, keyed, refused, value, values};

impl Resident {
    /// Save between windows, refusing open pending/staged handles, stopped deposition and
    /// multiple open moments. A passage is retained even when no moment is open.
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
        if self.next == u64::MAX {
            return refused("an exhausted resident handle counter");
        }
        let mut s = String::new();
        line(&mut s, "resident-passage", [2]);
        line(&mut s, "opens", [match self.opens {
            Opens::AtRest => "rest",
            Opens::OnMotion => "motion",
        }]);
        line(&mut s, "admitted", [self.admitted.len()]);
        for phases in &self.admitted {
            phases.write_saved(&mut s);
        }
        line(&mut s, "lift", self.current.lift());
        line(&mut s, "handle-counter", [self.next]);
        line(&mut s, "released-bits", [self.released_bits]);
        match self.moments.iter().next() {
            None => line(&mut s, "moment-slot", ["-".to_string()]),
            Some((id, moment)) => {
                line(&mut s, "moment-slot", [id.0.to_string()]);
                moment.write(&mut s);
            }
        }
        s += &format!("aeon {} {} {} {}\n",
            u8::from(self.aeon.awaiting), u8::from(self.aeon.keys_admitted),
            self.aeon.cells, self.aeon.closed);
        line(&mut s, "aeon-opening", &self.aeon.opening);
        write_balance(&mut s, self.ledger.balance());
        self.charts.write(&mut s);
        self.address.write(&mut s);
        match &self.arrived {
            None => line(&mut s, "arrived", ["none"]),
            Some(arrived) => {
                line(&mut s, "arrived", ["some"]);
                arrived.ratio.write_saved(&mut s);
                line(&mut s, "targets", &arrived.targets);
                write_opening(&mut s, &arrived.opening);
            }
        }
        Ok(self.constitution.continuing_state(ring)?
            .with_carry(self.carried.clone()).with_passage(Some(s)))
    }

    /// Bootstrap from saved declaring phases and saved lift, before mounting at contemporary
    /// material. Re-declaring observability there could refuse a legitimately continued rank.
    pub(super) fn passage_opening(
        field: &Field,
        text: &str,
    ) -> Result<(Current, Vec<ReceivingPhases>, Opens), HnnError> {
        let mut lines = text.lines();
        let mut next = |what: &'static str| lines.next().ok_or(HnnError::ContinuingState { what });
        read_opening(field, &mut next)
    }

    /// Restore only after all saved operands have been read and checked. The resident is owned
    /// privately throughout this method; an error publishes no partially restored resident.
    pub(super) fn with_passage(mut self, text: &str) -> Result<Self, HnnError> {
        let field = self.field.clone();
        let mut lines = text.lines();
        let mut next = |what: &'static str| lines.next().ok_or(HnnError::ContinuingState { what });
        let (current, admitted, opens) = read_opening(&field, &mut next)?;
        if opens != self.opens {
            return refused("the saved passage against the declared reception");
        }
        let counter: Vec<u64> = counted(next("the handle counter")?,
            "handle-counter", 1, "the handle counter")?;
        if counter[0] == u64::MAX {
            return refused("an exhausted resident handle counter");
        }
        let released: Vec<u64> = counted(next("the released-bit reading")?,
            "released-bits", 1, "the released-bit reading")?;
        let slot = keyed(next("the open moment slot")?, "moment-slot", "the open moment slot")?;
        let moment = match slot.as_slice() {
            ["-"] => None,
            [id] => {
                let id: u64 = value(Some(id), "the open moment handle")?;
                if id == 0 || id > counter[0] {
                    return refused("the open moment handle against the counter");
                }
                Some((MomentId(id), SourceMoment::read(&field, next("the moment")?, &mut next)?))
            }
            _ => return refused("the open moment slot"),
        };
        let aeon: Vec<u64> = counted(next("the aeon")?, "aeon", 4, "the aeon")?;
        if aeon[0] > 1 || aeon[1] > 1 {
            return refused("the aeon");
        }
        let opening: Vec<BigInt> = values(
            &keyed(next("the aeon's opening")?, "aeon-opening", "the aeon's opening")?,
            "the aeon's opening",
        )?;
        Current::at(&field, opening.clone())?;
        let balance = read_balance(&mut next)?;
        let charts = Charts::read(next("the charts")?, &mut next)?;
        let address = self.address.clone()
            .continued(next("the address register")?, &mut next)?;
        let arrived = match keyed(next("the arrived operand")?, "arrived", "the arrived operand")?.as_slice() {
            ["none"] => None,
            ["some"] => {
                let ratio = PendingRatio::read_saved(&field, &address, &mut next)?;
                if ratio.commit() > self.constitution.commit() {
                    return refused("the producing commit past the saved constitution");
                }
                let targets: Vec<usize> = values(
                    &keyed(next("the arrived targets")?, "targets", "the arrived targets")?,
                    "the arrived targets",
                )?;
                if targets.len() != ratio.phases().aperture()
                    || targets.iter().any(|&target| target >= field.alphabet())
                {
                    return refused("the arrived targets against their aperture and alphabet");
                }
                Some(Arrived { ratio, targets, opening: read_word_opening(&field, &mut next)? })
            }
            _ => return refused("the arrived operand"),
        };
        if next("the passage's end").is_ok() {
            return refused("the passage's end");
        }
        self.current = current;
        self.moments.clear();
        if let Some((id, moment)) = moment {
            self.moments.insert(id, moment);
        }
        self.next = counter[0];
        self.released_bits = released[0];
        self.aeon = AeonState {
            awaiting: aeon[0] == 1, keys_admitted: aeon[1] == 1,
            opening, cells: aeon[2], closed: aeon[3],
        };
        self.ledger = EnclosedLedger::resumed(balance);
        self.charts = charts;
        self.address = address;
        self.admitted = admitted;
        self.arrived = arrived;
        Ok(self)
    }
}

fn read_opening<'a>(
    field: &Field,
    next: Next<'_, 'a>,
) -> Result<(Current, Vec<ReceivingPhases>, Opens), HnnError> {
    let version: Vec<u64> = counted(next("the resident passage version")?,
        "resident-passage", 1, "the resident passage version")?;
    if version[0] != 2 {
        return refused("the resident passage version (expected 2)");
    }
    let opens = match keyed(next("the declared opening")?, "opens", "the declared opening")?.as_slice() {
        ["rest"] => Opens::AtRest,
        ["motion"] => Opens::OnMotion,
        _ => return refused("the declared opening"),
    };
    let count: Vec<usize> = counted(next("the admitted family")?,
        "admitted", 1, "the admitted family")?;
    let admitted = (0..count[0]).map(|_| {
        let phases = ReceivingPhases::read_saved(field, next("an admitted receiver")?)?;
        if !phases.is_declared_restriction(field)? {
            return refused("the saved admitted family against its field's declaration");
        }
        Ok(phases)
    }).collect::<Result<Vec<_>, HnnError>>()?;
    let lift: Vec<BigInt> = values(
        &keyed(next("the lift point")?, "lift", "the lift point")?, "the lift point",
    )?;
    Ok((Current::at(field, lift)?, admitted, opens))
}

fn write_opening(s: &mut String, opening: &WordOpening) {
    match opening {
        WordOpening::Rest => line(s, "arrived-opening", ["rest"]),
        WordOpening::Received { carry, absorption } => {
            line(s, "arrived-opening", [match absorption {
                Absorption::Nothing => "nothing",
                Absorption::Complete => "complete",
            }]);
            carry.write(s);
        }
    }
}

fn read_word_opening<'a>(field: &Field, next: Next<'_, 'a>) -> Result<WordOpening, HnnError> {
    let what = "the arrived word opening";
    let words = keyed(next(what)?, "arrived-opening", what)?;
    let absorption = match words.as_slice() {
        ["rest"] => return Ok(WordOpening::Rest),
        ["nothing"] => Absorption::Nothing,
        ["complete"] => Absorption::Complete,
        _ => return refused(what),
    };
    let carry = ReceptionCarry::read(next("the arrived carry")?, next)?;
    if !carry.fits(field) {
        return refused("the arrived carry against the field's shape");
    }
    Ok(WordOpening::Received { carry, absorption })
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
