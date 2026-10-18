//! [definition; agent-inferred, October 4] The whole resident passage, format version 3.
//!
//! Retain exactly the operands admitted future actions may read: the lift, optional one open
//! moment, aeon, first-law balance, charts, address including held contact-site kinds,
//! admitted declaring phases, handle counter and the one arrived comparison/opening.
//! Arrived is a bounded contemporary operand, not a history or a frozen material cut.
//! Immediate close, or ingest then close without another compare, may read it.
//!
//! Version 3 marks F1: material learned under the old absolute-lift read is not continued
//! under the passage-frame read. Version 2 and unversioned passages are refused at mount.
//! Constitution-only states remain a narrower remount. No legacy passage decoder, inferred
//! empty Arrived or borrowed live predecessor is admitted.

use super::*;
use crate::aeon::EnclosedBalance;
use crate::hnn::constitution::ContinuingState;
use crate::hnn::state_text::{Next, counted, keyed, refused, value, values};

/// The aeon-local counters and its opening lift, retained with the resident passage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentAeon {
    pub awaiting: bool,
    pub keys_admitted: bool,
    pub opening: Vec<BigInt>,
    pub cells: u64,
    pub closed: u64,
}

/// The one arrived comparison and its actual target/opening operands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentArrived {
    pub ratio: PendingRatio,
    pub targets: Vec<usize>,
    pub opening: WordOpening,
}

/// Validated resident passage fields shared by host and device realizations.
///
/// Construct with [`ResidentPassage::new`] or read the version-3 text with
/// [`ResidentPassage::from_text`]. Both routes validate by the same parser; `to_text` is the sole
/// passage serializer used by host and CUDA.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentPassageParts {
    pub current: Current,
    pub admitted: Vec<ReceivingPhases>,
    pub opens: Opens,
    pub next_handle: u64,
    pub released_bits: u64,
    pub moment: Option<(MomentId, SourceMoment)>,
    pub aeon: ResidentAeon,
    pub balance: EnclosedBalance,
    pub charts: Charts,
    pub address: ActiveAddress,
    pub arrived: Option<ResidentArrived>,
}

/// The complete, validated resident continuation carried inside `ContinuingState` v2.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentPassage {
    parts: ResidentPassageParts,
}

impl ResidentPassage {
    /// Validate typed native operands with the same checks used when loading a saved passage.
    pub fn new(
        field: &Field,
        constitution: &Constitution,
        parts: ResidentPassageParts,
    ) -> Result<Self, HnnError> {
        let text = write_passage(&parts);
        Self::from_text(field, constitution, &text)
    }

    /// Read the one native version-3 passage format against its field and contemporary material.
    pub fn from_text(
        field: &Field,
        constitution: &Constitution,
        text: &str,
    ) -> Result<Self, HnnError> {
        let mut lines = text.lines();
        let mut next = |what: &'static str| lines.next().ok_or(HnnError::ContinuingState { what });
        let (current, admitted, opens) = read_opening(field, &mut next)?;
        let counter: Vec<u64> = counted(
            next("the handle counter")?,
            "handle-counter",
            1,
            "the handle counter",
        )?;
        if counter[0] == u64::MAX {
            return refused("an exhausted resident handle counter");
        }
        let released: Vec<u64> = counted(
            next("the released-bit reading")?,
            "released-bits",
            1,
            "the released-bit reading",
        )?;
        let slot = keyed(
            next("the open moment slot")?,
            "moment-slot",
            "the open moment slot",
        )?;
        let moment = match slot.as_slice() {
            ["-"] => None,
            [id] => {
                let id: u64 = value(Some(id), "the open moment handle")?;
                if id == 0 || id > counter[0] {
                    return refused("the open moment handle against the counter");
                }
                Some((
                    MomentId(id),
                    SourceMoment::read(field, next("the moment")?, &mut next)?,
                ))
            }
            _ => return refused("the open moment slot"),
        };
        if let Some((_, moment)) = &moment {
            SourceCapacity::checked_of(moment, field, &current)?;
        }
        let aeon: Vec<u64> = counted(next("the aeon")?, "aeon", 4, "the aeon")?;
        if aeon[0] > 1 || aeon[1] > 1 {
            return refused("the aeon");
        }
        let opening: Vec<BigInt> = values(
            &keyed(
                next("the aeon's opening")?,
                "aeon-opening",
                "the aeon's opening",
            )?,
            "the aeon's opening",
        )?;
        Current::at(field, opening.clone())?;
        let balance = read_balance(&mut next)?;
        let charts = Charts::read(next("the charts")?, &mut next)?;
        charts.validate_for(field)?;
        let prototype = ActiveAddress::of_field(field, &current, constitution)?;
        let address = prototype.continued(next("the address register")?, &mut next)?;
        validate_address(field, &address)?;
        let address_opening = if aeon[0] == 1 {
            current.lift()
        } else {
            &opening
        };
        if !address.reader().agrees(field, &current, address_opening) {
            return Err(HnnError::Shape {
                what: "the saved address register's clock against the lift point",
                expected: field.rings().len(),
                found: 0,
            });
        }
        let arrived = match keyed(
            next("the arrived operand")?,
            "arrived",
            "the arrived operand",
        )?
        .as_slice()
        {
            ["none"] => None,
            ["some"] => {
                let ratio = PendingRatio::read_saved(field, &address, &mut next)?;
                if ratio.phases().observation_partition()
                    != field.receiving_context(ratio.phases().ring())
                {
                    return refused(
                        "the producing receiver's observation partition against its field",
                    );
                }
                validate_address(field, ratio.address())?;
                let ratio_current = ratio.current(field)?;
                SourceCapacity::checked_of(ratio.moment(), field, &ratio_current)?;
                if ratio.commit() > constitution.commit() {
                    return refused("the producing commit past the saved constitution");
                }
                let targets: Vec<usize> = values(
                    &keyed(
                        next("the arrived targets")?,
                        "targets",
                        "the arrived targets",
                    )?,
                    "the arrived targets",
                )?;
                if targets.len() != ratio.phases().aperture()
                    || targets.iter().any(|&target| target >= field.alphabet())
                {
                    return refused("the arrived targets against their aperture and alphabet");
                }
                // An arrived ratio has already passed its actual refine. A partitioned
                // reader must therefore retain one realized outcome for every phase.
                ratio.observed_addresses(&targets)?;
                Some(ResidentArrived {
                    ratio,
                    targets,
                    opening: read_word_opening(field, &mut next)?,
                })
            }
            _ => return refused("the arrived operand"),
        };
        if next("the passage's end").is_ok() {
            return refused("the passage's end");
        }
        Ok(Self {
            parts: ResidentPassageParts {
                current,
                admitted,
                opens,
                next_handle: counter[0],
                released_bits: released[0],
                moment,
                aeon: ResidentAeon {
                    awaiting: aeon[0] == 1,
                    keys_admitted: aeon[1] == 1,
                    opening,
                    cells: aeon[2],
                    closed: aeon[3],
                },
                balance,
                charts,
                address,
                arrived,
            },
        })
    }

    /// The exact native v3 passage text, including all arrived and mode-view operands.
    pub fn to_text(&self) -> String {
        write_passage(&self.parts)
    }

    pub fn parts(&self) -> &ResidentPassageParts {
        &self.parts
    }

    pub fn into_parts(self) -> ResidentPassageParts {
        self.parts
    }
}

impl ContinuingState {
    /// Attach the shared native passage codec to this exact learned constitution state.
    pub fn with_resident_passage(self, passage: ResidentPassage) -> Self {
        self.with_passage(Some(passage.to_text()))
    }

    /// Decode and validate this state's resident passage against its declared opening material.
    pub fn resident_passage(
        &self,
        field: &Field,
        opening: &Constitution,
    ) -> Result<Option<ResidentPassage>, HnnError> {
        let Some(text) = self.passage() else {
            return Ok(None);
        };
        let constitution = opening.clone().continued(self)?;
        Ok(Some(ResidentPassage::from_text(
            field,
            &constitution,
            text,
        )?))
    }
}

fn write_passage(parts: &ResidentPassageParts) -> String {
    let mut s = String::new();
    line(&mut s, "resident-passage", [3]);
    line(
        &mut s,
        "opens",
        [match parts.opens {
            Opens::AtRest => "rest",
            Opens::OnMotion => "motion",
        }],
    );
    line(&mut s, "admitted", [parts.admitted.len()]);
    for phases in &parts.admitted {
        phases.write_saved(&mut s);
    }
    line(&mut s, "lift", parts.current.lift());
    line(&mut s, "handle-counter", [parts.next_handle]);
    line(&mut s, "released-bits", [parts.released_bits]);
    match &parts.moment {
        None => line(&mut s, "moment-slot", ["-".to_string()]),
        Some((id, moment)) => {
            line(&mut s, "moment-slot", [id.0.to_string()]);
            moment.write(&mut s);
        }
    }
    s += &format!(
        "aeon {} {} {} {}\n",
        u8::from(parts.aeon.awaiting),
        u8::from(parts.aeon.keys_admitted),
        parts.aeon.cells,
        parts.aeon.closed
    );
    line(&mut s, "aeon-opening", &parts.aeon.opening);
    write_balance(&mut s, &parts.balance);
    parts.charts.write(&mut s);
    parts.address.write(&mut s);
    match &parts.arrived {
        None => line(&mut s, "arrived", ["none"]),
        Some(arrived) => {
            line(&mut s, "arrived", ["some"]);
            arrived.ratio.write_saved(&mut s);
            line(&mut s, "targets", &arrived.targets);
            write_opening(&mut s, &arrived.opening);
        }
    }
    s
}

impl Resident {
    /// Save between windows, refusing open pending/staged handles, stopped deposition and
    /// multiple open moments. A passage is retained even when no moment is open.
    pub fn continuing_state(&self, ring: usize) -> Result<ContinuingState, HnnError> {
        self.admit_exact_current()?;
        if self.receiving_chart.is_some() {
            return refused("a receiving codec chart whose passage serialization is not admitted");
        }
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
        let parts = ResidentPassageParts {
            current: self.current.clone(),
            admitted: self.admitted.clone(),
            opens: self.opens,
            next_handle: self.next,
            released_bits: self.released_bits,
            moment: self
                .moments
                .iter()
                .next()
                .map(|(id, moment)| (*id, moment.clone())),
            aeon: ResidentAeon {
                awaiting: self.aeon.awaiting,
                keys_admitted: self.aeon.keys_admitted,
                opening: self.aeon.opening.clone(),
                cells: self.aeon.cells,
                closed: self.aeon.closed,
            },
            balance: self.ledger.balance().clone(),
            charts: self.charts.clone(),
            address: self.address.clone(),
            arrived: self.arrived.as_ref().map(|arrived| ResidentArrived {
                ratio: arrived.ratio.clone(),
                targets: arrived.targets.clone(),
                opening: arrived.opening.clone(),
            }),
        };
        let passage = ResidentPassage::new(&self.field, &self.constitution, parts)?;
        Ok(self
            .constitution
            .continuing_state(ring)?
            .with_carry(self.carried.clone())
            .with_resident_passage(passage))
    }

    /// Restore only after all saved operands have been read and checked. The resident is owned
    /// privately throughout this method; an error publishes no partially restored resident.
    pub(super) fn with_passage(mut self, passage: ResidentPassage) -> Result<Self, HnnError> {
        let parts = passage.into_parts();
        if parts.opens != self.opens {
            return refused("the saved passage against the declared reception");
        }
        self.current = parts.current;
        self.moments.clear();
        if let Some((id, moment)) = parts.moment {
            self.moments.insert(id, moment);
        }
        self.next = parts.next_handle;
        self.released_bits = parts.released_bits;
        self.aeon = AeonState {
            awaiting: parts.aeon.awaiting,
            keys_admitted: parts.aeon.keys_admitted,
            opening: parts.aeon.opening,
            cells: parts.aeon.cells,
            closed: parts.aeon.closed,
        };
        self.ledger = EnclosedLedger::resumed(parts.balance);
        self.charts = parts.charts;
        self.address = parts.address;
        self.admitted = parts.admitted;
        self.arrived = parts.arrived.map(|arrived| Arrived {
            ratio: arrived.ratio,
            targets: arrived.targets,
            opening: arrived.opening,
        });
        Ok(self)
    }
}

fn read_opening<'a>(
    field: &Field,
    next: Next<'_, 'a>,
) -> Result<(Current, Vec<ReceivingPhases>, Opens), HnnError> {
    let version: Vec<u64> = counted(
        next("the resident passage version")?,
        "resident-passage",
        1,
        "the resident passage version",
    )?;
    if version[0] != 3 {
        return refused("the resident passage version (expected 3)");
    }
    let opens = match keyed(
        next("the declared opening")?,
        "opens",
        "the declared opening",
    )?
    .as_slice()
    {
        ["rest"] => Opens::AtRest,
        ["motion"] => Opens::OnMotion,
        _ => return refused("the declared opening"),
    };
    let count: Vec<usize> = counted(
        next("the admitted family")?,
        "admitted",
        1,
        "the admitted family",
    )?;
    let admitted = (0..count[0])
        .map(|_| {
            let phases = ReceivingPhases::read_saved(field, next("an admitted receiver")?)?;
            if !phases.is_declared_restriction(field)? {
                return refused("the saved admitted family against its field's declaration");
            }
            Ok(phases)
        })
        .collect::<Result<Vec<_>, HnnError>>()?;
    let lift: Vec<BigInt> = values(
        &keyed(next("the lift point")?, "lift", "the lift point")?,
        "the lift point",
    )?;
    Ok((Current::at(field, lift)?, admitted, opens))
}

fn validate_address(field: &Field, address: &ActiveAddress) -> Result<(), HnnError> {
    let family = field.letter_family();
    let alphabet = field.alphabet();
    let feature_codes = family.letters().codes();
    for letter in address.letters() {
        match letter {
            Letter::Boundary => {}
            Letter::Cell(cell) if family.is_empty() && *cell < alphabet => {}
            Letter::Bundle(bundle)
                if !family.is_empty()
                    && bundle.cell < alphabet
                    && u64::from(bundle.features) < feature_codes => {}
            _ => return refused("the address letters against the field's declared family"),
        }
    }
    Ok(())
}

fn write_opening(s: &mut String, opening: &WordOpening) {
    match opening {
        WordOpening::Rest => line(s, "arrived-opening", ["rest"]),
        WordOpening::Received { carry, absorption } => {
            line(
                s,
                "arrived-opening",
                [match absorption {
                    Absorption::Nothing => "nothing",
                    Absorption::Complete => "complete",
                }],
            );
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

fn read_interval(
    line: &str,
    key: &str,
    what: &'static str,
) -> Result<Option<ExactInterval>, HnnError> {
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
    let whole =
        |interval: Option<ExactInterval>| interval.ok_or(HnnError::ContinuingState { what });
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

#[cfg(test)]
mod tests {
    use super::*;
    fn arrived_resident(outside_future: bool) -> (Reference, Resident) {
        use crate::hnn::tests::{learning, support};
        let field = learning::chain();
        let reference = Reference::campaign_one();
        let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
        let (moment, _) = reference
            .ingest(&mut resident, None, &support::encoded(&field, &[0]))
            .unwrap();
        let phases = if outside_future {
            let mut declaration = field.receivers()[0].clone();
            declaration.tolerance /= crate::ratio::integer(2);
            ReceivingPhases::declare(
                &field,
                resident.constitution(),
                resident.current(),
                &declaration,
            )
            .unwrap()
        } else {
            resident.admitted()[0].clone()
        };
        let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
        let targets = support::encoded(&field, &vec![0; phases.aperture()]);
        let (staged, _) = reference.compare(&mut resident, pending, &targets).unwrap();
        reference
            .discard(&mut resident, Handle::Staged(staged))
            .unwrap();
        (reference, resident)
    }

    #[test]
    fn producing_receiver_allows_native_receiver_outside_future_family() {
        let (_, resident) = arrived_resident(true);
        let state = resident
            .continuing_state(resident.field.sources()[0])
            .unwrap();
        let passage = ResidentPassage::from_text(
            &resident.field,
            resident.constitution(),
            state.passage().unwrap(),
        )
        .unwrap();
        let arrived = passage.parts().arrived.as_ref().unwrap();
        assert!(!passage.parts().admitted.contains(arrived.ratio.phases()));
    }

    #[test]
    fn producing_receiver_rejects_invalid_field_partition_ring_and_epoch() {
        let (_, resident) = arrived_resident(false);
        let state = resident
            .continuing_state(resident.field.sources()[0])
            .unwrap();
        let text = state.passage().unwrap();
        let lines: Vec<_> = text.lines().collect();
        let producer = lines
            .iter()
            .rposition(|line| line.starts_with("phases "))
            .unwrap();
        let original: Vec<_> = lines[producer]
            .split_whitespace()
            .map(str::to_owned)
            .collect();
        for (index, invalid) in [
            (1, resident.field.rings().len().to_string()),
            (2, (original[2].parse::<usize>().unwrap() + 1).to_string()),
        ] {
            let mut words = original.clone();
            words[index] = invalid;
            let changed = words.join(" ");
            assert!(ReceivingPhases::read_saved(&resident.field, &changed).is_err());
            let mut bad = lines.clone();
            bad[producer] = &changed;
            assert!(
                ResidentPassage::from_text(
                    &resident.field,
                    resident.constitution(),
                    &bad.join("\n")
                )
                .is_err()
            );
        }
        let mut bad_partition = original;
        bad_partition.push("receiving-section-v1".into());
        let changed = bad_partition.join(" ");
        assert!(ReceivingPhases::read_saved(&resident.field, &changed).is_ok());
        // Keep the ratio structurally readable after adding a partition: its existing
        // serializer includes the observation count even when no path is retained.
        let changed_ratio = format!("{changed}\nratio-observation 0");
        let mut bad = lines;
        bad[producer] = &changed_ratio;
        assert!(matches!(
            ResidentPassage::from_text(&resident.field, resident.constitution(), &bad.join("\n")),
            Err(HnnError::ContinuingState {
                what: "the producing receiver's observation partition against its field"
            })
        ));
    }
}
