//! Version 4 retains the resident passage and publication subtotals; the ratio owns its receiver.
//! Version 2, version 3 and unversioned passages are refused without migration.

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
/// Construct with [`ResidentPassage::new`] or read its versioned text with
/// [`ResidentPassage::from_text`]. Both routes validate by the same parser; `to_text` is the sole
/// passage serializer used by host and CUDA. Coarse-law version 4 remains byte-compatible; the
/// retained-fibre law is explicit in version 5.
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
    pub source_return_frontier: BTreeMap<usize, usize>,
    pub prepared_input: Option<prepared_input::PreparedInputState>,
}

/// The complete, validated resident continuation carried inside `ContinuingState`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentPassage {
    parts: ResidentPassageParts,
    receiving_law: crate::hnn::receiving::ReceivingLaw,
}

impl ResidentPassage {
    /// Validate typed native operands with the same checks used when loading a saved passage.
    pub fn new(
        field: &Field,
        constitution: &Constitution,
        parts: ResidentPassageParts,
    ) -> Result<Self, HnnError> {
        Self::new_with_law(
            field,
            constitution,
            parts,
            crate::hnn::receiving::ReceivingLaw::CoarseGrainV1,
        )
    }

    /// Validate a passage while retaining its explicitly selected receiving law.
    pub fn new_with_law(
        field: &Field,
        constitution: &Constitution,
        parts: ResidentPassageParts,
        receiving_law: crate::hnn::receiving::ReceivingLaw,
    ) -> Result<Self, HnnError> {
        let text = write_passage(&parts, receiving_law);
        Self::from_text(field, constitution, &text)
    }

    /// Read a versioned native passage against its field and contemporary material.
    pub fn from_text(
        field: &Field,
        constitution: &Constitution,
        text: &str,
    ) -> Result<Self, HnnError> {
        constitution.admit_epoch_field(field)?;
        let mut lines = text.lines();
        let mut next = |what: &'static str| lines.next().ok_or(HnnError::ContinuingState { what });
        let (current, admitted, opens, receiving_law) = read_opening(field, &mut next)?;
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
        let mut source_return_frontier = BTreeMap::new();
        if text.starts_with("resident-passage 6\n") || text.starts_with("resident-passage 7\n") || text.starts_with("resident-passage 8\n") {
            let header: Vec<usize> = counted(
                next("the reciprocal frontier count")?,
                "source-return-frontiers",
                1,
                "the reciprocal frontier count",
            )?;
            if (header[0] == 0 && !text.starts_with("resident-passage 8\n")) || header[0] > field.sources().len() {
                return refused("the bounded reciprocal frontier count");
            }
            for _ in 0..header[0] {
                let row: Vec<usize> = counted(
                    next("the reciprocal frontier")?,
                    "source-return-frontier",
                    2,
                    "the reciprocal frontier",
                )?;
                let cells = moment.as_ref().map_or(0, |(_, m)| m.cells());
                if !field.sources().contains(&row[0])
                    || u64::try_from(row[1]).map_err(|_| HnnError::CountOverflow)? >= cells
                    || source_return_frontier.insert(row[0], row[1]).is_some()
                {
                    return refused("one actual consumed encounter frontier per source");
                }
            }
        }
        let prepared_input=if text.starts_with("resident-passage 8\n"){
            let row=keyed(next("prepared input continuation")?,"prepared-input","prepared input continuation")?;
            if row.len()!=1{return refused("one prepared input continuation");}
            let input=prepared_input::PreparedInputState::from_text(field,constitution,&prepared_input::codec::unhex(row[0])?)?;
            if moment.as_ref().map(|(_,m)|m.cells())!=Some(input.source_cells()){return refused("prepared input and native source share one frontier");}
            if input.context_chart()==prepared_input::ContextChart::LaggedReceiverBoundaryV1{
                // Both counters are already saved: retain the cumulative source,
                // validate its aeon-local subinterval and derive the explicit origin.
                native_context::NativeSourceFrontier::from_counts(input.source_cells(),aeon[2])?;
            }
            Some(input)
        }else{None};
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
                source_return_frontier,
                prepared_input,
            },
            receiving_law,
        })
    }

    /// The exact native passage text, including all arrived and mode-view operands.
    pub fn to_text(&self) -> String {
        write_passage(&self.parts, self.receiving_law)
    }

    pub fn receiving_law(&self) -> crate::hnn::receiving::ReceivingLaw {
        self.receiving_law
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
        // Bind even a constitution-only save before reporting that no passage was stored.
        let constitution = opening.clone().continued_on(field, self)?;
        let Some(text) = self.passage() else {
            return Ok(None);
        };
        Ok(Some(ResidentPassage::from_text(
            field,
            &constitution,
            text,
        )?))
    }
}

fn write_passage(
    parts: &ResidentPassageParts,
    receiving_law: crate::hnn::receiving::ReceivingLaw,
) -> String {
    let mut s = String::new();
    if parts.prepared_input.is_some(){
        line(&mut s,"resident-passage",[8]);
        line(&mut s,"receiving-law",[crate::hnn::receiving::ReceivingLaw::RetainedFibreV1.as_str()]);
    }else{match receiving_law {
        crate::hnn::receiving::ReceivingLaw::CoarseGrainV1 => {
            line(
                &mut s,
                "resident-passage",
                [if parts.source_return_frontier.is_empty() {
                    4
                } else {
                    6
                }],
            );
        }
        crate::hnn::receiving::ReceivingLaw::RetainedFibreV1 => {
            line(
                &mut s,
                "resident-passage",
                [if parts.source_return_frontier.is_empty() {
                    5
                } else {
                    7
                }],
            );
            line(&mut s, "receiving-law", [receiving_law.as_str()]);
        }
    }
    }
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
    if !parts.source_return_frontier.is_empty() || parts.prepared_input.is_some() {
        line(
            &mut s,
            "source-return-frontiers",
            [parts.source_return_frontier.len()],
        );
        for (&ring, &position) in &parts.source_return_frontier {
            line(&mut s, "source-return-frontier", [ring, position]);
        }
    }
    if let Some(input)=&parts.prepared_input{line(&mut s,"prepared-input",[prepared_input::codec::hex(&input.to_text())]);}
    s
}

impl Resident {
    /// Save between windows, refusing open pending/staged handles, stopped deposition and
    /// multiple open moments. A passage is retained even when no moment is open.
    pub fn continuing_state(&self, ring: usize) -> Result<ContinuingState, HnnError> {
        self.admit_exact_current()?;
        if let Some(chart)=&self.receiving_chart {
            if self.native_context_chart()?.as_ref()!=Some(chart){return refused("a receiving codec chart whose passage serialization is not admitted");}
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
            source_return_frontier: self.source_return_frontier.clone(),
            prepared_input: self.prepared_input.clone(),
            arrived: self.arrived.as_ref().map(|arrived| ResidentArrived {
                ratio: arrived.ratio.clone(),
                targets: arrived.targets.clone(),
                opening: arrived.opening.clone(),
            }),
        };
        let passage = ResidentPassage::new_with_law(
            &self.field,
            &self.constitution,
            parts,
            self.receiving_law,
        )?;
        let state = self
            .constitution
            .continuing_state(ring)?
            .with_carry(self.carried.clone())
            .with_founding(self.founding.clone(), self.staged_founding)
            .with_resident_passage(passage);
        match self.observed_epoch_ingress {
            Some((receiver, ticks)) => state.with_receiver_ingress_ticks(receiver, ticks),
            None => Ok(state),
        }
    }

    /// Restore only after all saved operands have been read and checked. The resident is owned
    /// privately throughout this method; an error publishes no partially restored resident.
    pub(super) fn with_passage(mut self, passage: ResidentPassage) -> Result<Self, HnnError> {
        let receiving_law = passage.receiving_law();
        let parts = passage.into_parts();
        if parts.opens != self.opens {
            return refused("the saved passage against the declared reception");
        }
        self.source_return_frontier = parts.source_return_frontier;
        self.prepared_input=parts.prepared_input;
        self.receiving_chart=self.native_context_chart()?;
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
        self.receiving_law = receiving_law;
        self.arrived = parts.arrived.map(|arrived| Arrived {
            ratio: arrived.ratio,
            targets: arrived.targets,
            opening: arrived.opening,
        });
        Ok(self)
    }
}

/// Refuse superseded formats before reading operands whose representation changed.
pub(crate) fn check_version(line: &str) -> Result<crate::hnn::receiving::ReceivingLaw, HnnError> {
    let words: Vec<_> = line.split_whitespace().collect();
    if words == ["resident-passage", "4"] || words == ["resident-passage", "6"] {
        return Ok(crate::hnn::receiving::ReceivingLaw::CoarseGrainV1);
    }
    if words == ["resident-passage", "5"] || words == ["resident-passage", "7"] || words == ["resident-passage", "8"] {
        return Ok(crate::hnn::receiving::ReceivingLaw::RetainedFibreV1);
    }
    let version = match words.as_slice() {
        ["resident-passage", number] => number
            .parse()
            .map(crate::hnn::SavedPassageVersion::Number)
            .unwrap_or(crate::hnn::SavedPassageVersion::Malformed),
        ["resident-passage", ..] => crate::hnn::SavedPassageVersion::Malformed,
        _ => crate::hnn::SavedPassageVersion::Unversioned,
    };
    Err(HnnError::PassageVersion { version })
}

fn read_opening<'a>(
    field: &Field,
    next: Next<'_, 'a>,
) -> Result<
    (
        Current,
        Vec<ReceivingPhases>,
        Opens,
        crate::hnn::receiving::ReceivingLaw,
    ),
    HnnError,
> {
    let receiving_law = check_version(next("the resident passage version")?)?;
    if receiving_law == crate::hnn::receiving::ReceivingLaw::RetainedFibreV1 {
        let law = keyed(
            next("the explicit receiving law")?,
            "receiving-law",
            "the explicit receiving law",
        )?;
        if law.as_slice() != [receiving_law.as_str()] {
            return refused("the retained-fibre passage's explicit receiving law");
        }
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
    Ok((Current::at(field, lift)?, admitted, opens, receiving_law))
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
        "ledger {} {} {} {} {} {}\n",
        balance.exchanges,
        balance.depositions,
        balance.publications,
        balance.arrivals,
        balance.cells,
        balance.widening
    );
    write_interval(s, "exchange", Some(&balance.exchange));
    write_interval(s, "deposition", Some(&balance.deposition));
    write_interval(s, "deposited", Some(&balance.deposited));
    write_interval(s, "published", Some(&balance.published));
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
    let whole =
        |interval: Option<ExactInterval>| interval.ok_or(HnnError::ContinuingState { what });
    let [
        exchanges,
        depositions,
        publications,
        arrivals,
        cells,
        widening,
    ] = words[..]
    else {
        return refused(what);
    };
    let exchange = whole(read_interval(next(what)?, "exchange", what)?)?;
    let deposition = whole(read_interval(next(what)?, "deposition", what)?)?;
    let deposited = whole(read_interval(next(what)?, "deposited", what)?)?;
    let published = whole(read_interval(next(what)?, "published", what)?)?;
    if exact_plus(&deposited, &published) != deposition {
        return refused("the v4 deposition subtotals against their inclusive total");
    }
    let opening = read_interval(next(what)?, "opening", what)?;
    let closing = read_interval(next(what)?, "closing", what)?;
    let arrived = whole(read_interval(next(what)?, "arrived", what)?)?;
    Ok(EnclosedBalance {
        exchanges: value(Some(&exchanges), what)?,
        depositions: value(Some(&depositions), what)?,
        publications: value(Some(&publications), what)?,
        arrivals: value(Some(&arrivals), what)?,
        cells: value(Some(&cells), what)?,
        widening: value(Some(&widening), what)?,
        exchange,
        deposition,
        deposited,
        published,
        opening,
        closing,
        arrived,
    })
}

fn exact_plus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower + &b.lower,
        upper: &a.upper + &b.upper,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn main_version_three_save_is_refused_before_changed_law_operands() {
        // Written at 03b949b83006236044e7e15abb2142d00918474d by Resident::continuing_state().to_text().
        let text = include_str!("fixtures/main-v3.state");
        assert!(
            matches!(ContinuingState::from_text(text, crate::hnn::constitution::CAMPAIGN_ONE_BUDGET),
            Err(HnnError::PassageVersion { version }) if version == crate::hnn::SavedPassageVersion::Number(3))
        );
    }
    #[test]
    fn version_four_never_decodes_located_prior_text() {
        let (_, resident) = arrived_resident(false);
        let state = resident
            .continuing_state(resident.field.sources()[0])
            .unwrap();
        let text = state.to_text();
        assert!(text.contains("receiving_prior none"));
        assert!(state.passage().unwrap().starts_with("resident-passage 4\n"));
        let decoded = ResidentPassage::from_text(
            &resident.field,
            resident.constitution(),
            state.passage().unwrap(),
        )
        .unwrap();
        assert_eq!(decoded.to_text(), state.passage().unwrap());
        let changed = text.replacen("receiving_prior none", "located none", 1);
        let stamped = ContinuingState::stamped(&changed, resident.constitution()).unwrap();
        assert!(ContinuingState::from_text(&stamped, resident.constitution().budget()).is_err());
    }

    #[test]
    fn retained_fibre_selection_is_fresh_only_and_passage_roundtrips_its_identity() {
        use crate::hnn::receiving::ReceivingLaw;
        use crate::hnn::tests::{learning, support};

        let field = learning::chain();
        let reference = Reference::campaign_one();
        let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
        assert_eq!(resident.receiving_law(), ReceivingLaw::CoarseGrainV1);
        resident
            .select_receiving_law(ReceivingLaw::CoarseGrainV1)
            .unwrap();
        resident
            .select_receiving_law(ReceivingLaw::RetainedFibreV1)
            .unwrap();
        assert_eq!(resident.receiving_law(), ReceivingLaw::RetainedFibreV1);
        let saved = resident
            .continuing_state(resident.field.sources()[0])
            .unwrap();
        let passage = saved.passage().unwrap();
        assert!(passage.starts_with("resident-passage 5\nreceiving-law retained-fibre-v1\n"));
        let loaded =
            ContinuingState::from_text(&saved.to_text(), resident.constitution().budget()).unwrap();
        let cold = reference
            .mount_continued(
                &field,
                &Current::at_rest(&field),
                resident.constitution().clone(),
                &loaded,
            )
            .unwrap();
        assert_eq!(cold.receiving_law(), ReceivingLaw::RetainedFibreV1);
        assert_eq!(
            cold.continuing_state(resident.field.sources()[0]).unwrap(),
            saved
        );

        let mut momentful = reference.mount(&field, &Current::at_rest(&field)).unwrap();
        reference
            .ingest(&mut momentful, None, &support::encoded(&field, &[0]))
            .unwrap();
        momentful
            .select_receiving_law(ReceivingLaw::CoarseGrainV1)
            .unwrap();
        let before = momentful
            .continuing_state(momentful.field.sources()[0])
            .unwrap();
        assert!(
            momentful
                .select_receiving_law(ReceivingLaw::RetainedFibreV1)
                .is_err()
        );
        assert_eq!(momentful.receiving_law(), ReceivingLaw::CoarseGrainV1);
        assert_eq!(
            momentful
                .continuing_state(momentful.field.sources()[0])
                .unwrap(),
            before
        );
    }
    #[test]
    fn superseded_and_unversioned_passages_are_typed_refusals() {
        for (text, expected) in [
            (
                "resident-passage 2",
                crate::hnn::SavedPassageVersion::Number(2),
            ),
            (
                "resident-passage 3",
                crate::hnn::SavedPassageVersion::Number(3),
            ),
            ("opens rest", crate::hnn::SavedPassageVersion::Unversioned),
        ] {
            assert!(
                matches!(check_version(text), Err(HnnError::PassageVersion { version }) if version == expected)
            );
        }
    }
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
