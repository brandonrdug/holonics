//! **The reception carry on the card** (record B §2.1–§2.4 and §2.3a; the deposit record §3;
//! host owners `holonics::hnn::word::{ReceptionCarry, Word::open_received}` and
//! `holonics::hnn::reference::Reception`).
//!
//! [definition; agent-inferred, October 3] Under a declared carry
//! (`holonics::hnn::reference::Reception::Carry`) a reception's word opens on the end change the
//! previous reception's consumed word left. On the card that change **stays on the card**: the
//! consumed word's storage, arrivals and states are copied into a buffer of their own
//! ([`crate::hnn::execute::ResidentWord::end_words`], nothing crosses the bus), and the next word
//! copies them into its own change before its open. Beside them the host keeps the carry's exact
//! mirror, read from the consumed word's record ([`CardCarry::ended`]): the change, the field's
//! elapsed ticks, each contact's conductance at the word's cut and its momentum `π_a = C_a w_a`,
//! the carry the reference holds, so the chained balance, the state's bits and a saved continuing
//! state read the same carry on either port.
//!
//! [definition; record B §2.3a, the deposit record §3] **The crossing runs in the card's open**
//! (`kernels/hnn_word.cuh`, "The carried open"): each carried wave is transmitted across its
//! contact's reference change, `a′ = (1 + Γ)a = 2G/(G + G′)·a`, from the plan's gain, and each rate is
//! held at momentum, `w′ = w + δ`. The jump `δ` is the commit's solve `C′δ = π − C′w` (the particular
//! point of the reduced solve), read from the host owner `ReceptionCarry::crossed` against the
//! publication's storage forms, since the card's words carry no exact preimage solve
//! (agent-inferred). Both leave the dyadics in general, so the card splits them onto `L_w` over
//! their denominators and carries those remainders through every later split of the word
//! ([`crate::hnn::execute::CarryPlan`]).
//!
//! [definition; agent-inferred] **What the card refuses.** A declared resonator on a received
//! opening: under `Absorption::Nothing` because the card still carries the change after the last
//! junction, which the host law no longer does (the reception carry §2.4: the carry is the last
//! crossing and the pump continues from it), and under `Absorption::Complete` because the card's
//! pump phase reads the word's own ticks from zero (`step % phases`), not the field's elapsed
//! ticks. The card's change is owed (#76; the record's §7 names it). A carried change off the transients' lattice, or past the signed
//! 64-bit word, is refused at its restore.

use std::rc::Rc;

use holonics::hnn::reference::carry_bits;
use holonics::hnn::{Absorption, Field, HnnError, ReceptionCarry};
use holonics::ratio::Rat;
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

use crate::hnn::DeviceError;
use crate::hnn::card::{Card, CardBuffer};
use crate::hnn::dyadic::{coordinate, refused};
use crate::hnn::execute::{CarryPlan, ResidentWord, WordPlan};
use crate::hnn::publication::Loci;
use crate::hnn::readout;

fn device(error: DeviceError) -> HnnError {
    error.into_hnn()
}

/// [definition] **A reception's carried end on the card**: the host's exact mirror and, when any
/// coordinate moves, the change's words at `L_w` resident on the card (`crate::hnn::execute::carried_parts`'s
/// layout). `None` holds the rest change: the carry at complete absorption, or a change that is
/// zero.
pub(crate) struct CardCarry<'c> {
    pub(crate) host: ReceptionCarry,
    words: Option<CardBuffer<'c, u8>>,
}

/// [definition] **What a reception's word opens on, on the card** (`holonics::hnn::WordOpening`):
/// at rest, or on a carried end under a declared absorption.
#[derive(Clone)]
pub(crate) enum CardOpening<'c> {
    Rest,
    Received {
        carry: Rc<CardCarry<'c>>,
        absorption: Absorption,
    },
}

/// Whether a change moves anywhere: a storage wave, an arriving wave or a contact state off zero.
fn moving(carry: &ReceptionCarry) -> bool {
    let change = &carry.change;
    change
        .storage
        .iter()
        .chain(change.arrivals.iter().flatten())
        .chain(change.states.iter().flatten())
        .flatten()
        .any(|x| !x.is_zero())
}

impl<'c> CardCarry<'c> {
    /// [definition; the reception carry §2.1] **The carried end a consumed word leaves**: its end
    /// change read from its record, the field's elapsed ticks (the opening's plus its junction
    /// steps; the host now carries the last crossing at one tick fewer, §2.4, and this read follows
    /// it under #76), each contact's conductance at its cut and momentum `C_a w_a` under its
    /// publication's storage, after the boundary's absorption; under `Absorption::Nothing` its
    /// change's words copied on the card.
    pub(crate) fn ended(
        word: &ResidentWord<'c>,
        opened_at: usize,
        absorption: Absorption,
    ) -> Result<Self, HnnError> {
        let plan = &word.plan;
        let change = readout::end(plan, &word.record);
        let momenta = word
            .publication
            .loci
            .contacts
            .iter()
            .zip(&change.states)
            .map(|(contact, [_, rate])| Ok(contact.forms[0].apply(rate)?))
            .collect::<Result<Vec<_>, HnnError>>()?;
        let host = ReceptionCarry {
            ticks: opened_at + plan.steps,
            conductances: plan
                .contacts
                .iter()
                .map(|c| c.conductance.clone())
                .collect(),
            momenta,
            // The card refuses a declared resonator on a received opening (module header), so it
            // carries no resonator momentum.
            resonator_momenta: vec![None; change.resonators.len()],
            change,
        }
        .absorbed(absorption);
        let words = match absorption {
            Absorption::Nothing if moving(&host) => Some(word.end_words()?),
            _ => None,
        };
        Ok(Self { host, words })
    }

    /// [definition; the reception carry §2.4] **A restored carry on the card**
    /// (`Reference::mount_carried`): the host's carry, its change uploaded as words at `L_w`;
    /// refused where a coordinate lies off the transients' lattice or past the signed 64-bit
    /// word, or the carry has another field's shape.
    pub(crate) fn restored(
        card: &'c Card,
        field: &Field,
        host: ReceptionCarry,
    ) -> Result<Self, HnnError> {
        if !host.fits(field) {
            return Err(HnnError::ContinuingState {
                what: "a carried end mounted at rest or of another field's shape",
            });
        }
        if !moving(&host) {
            return Ok(Self { host, words: None });
        }
        let lw = field
            .word_lattice()
            .ok_or_else(|| refused("a field whose word runs on no declared lattice"))?
            .transient_exponent();
        let change = &host.change;
        let mut words = Vec::new();
        let runs = change
            .storage
            .iter()
            .chain(change.arrivals.iter().flatten())
            .chain(change.states.iter().map(|[u, _]| u))
            .chain(change.states.iter().map(|[_, w]| w));
        for x in runs.flatten() {
            let word = coordinate(x, lw).and_then(|c| c.to_i64()).ok_or_else(|| {
                refused("a carried change off the transients' lattice or past the word")
            })?;
            words.extend(word.to_ne_bytes());
        }
        let words = card.upload(&words).map_err(device)?;
        Ok(Self {
            host,
            words: Some(words),
        })
    }
}

impl<'c> CardOpening<'c> {
    /// **The exact bits of the opening** (the reference's `opening_bits`): none at rest.
    pub(crate) fn bits(&self) -> u64 {
        match self {
            Self::Rest => 0,
            Self::Received { carry, .. } => carry_bits(&carry.host),
        }
    }

    /// The field's elapsed ticks the word opens at: zero at rest.
    pub(crate) fn ticks(&self) -> usize {
        match self {
            Self::Rest => 0,
            Self::Received { carry, .. } => carry.host.ticks,
        }
    }

    /// [definition; record B §2.3a, the deposit record §3] **The plan opening on this opening**:
    /// unchanged where the word opens on the rest change (at rest, at complete absorption, or on a
    /// zero carry), otherwise with its carry table ([`WordPlan::with_carry`]): each contact's gain
    /// `2G/(G + G′)` from the carried and the plan's conductances, and each row's held-rate jump
    /// from the host owner (`ReceptionCarry::crossed` against the publication's storage forms),
    /// with the carried words the word copies in. A declared resonator on a received opening is
    /// refused (module header).
    pub(crate) fn plan<'w>(
        &'w self,
        plan: WordPlan,
        loci: &Loci,
        resonators: &[Option<holonics::hnn::ring::ResonatorOperands>],
    ) -> Result<(WordPlan, Option<&'w CardBuffer<'c, u8>>), HnnError> {
        let Self::Received { carry, absorption } = self else {
            return Ok((plan, None));
        };
        if let Some(ring) = resonators.iter().position(Option::is_some) {
            return Err(HnnError::Resonator {
                ring,
                what: match absorption {
                    Absorption::Nothing => {
                        "the card's carry of the last crossing and its pump phase is owed (#76)"
                    }
                    Absorption::Complete => {
                        "the card's pump phase at a carried tick is owed (it reads the word's own ticks)"
                    }
                },
            });
        }
        // At complete absorption the word opens on the rest change whatever the carry holds.
        let (Absorption::Nothing, Some(words)) = (absorption, &carry.words) else {
            return Ok((plan, None));
        };
        let host = &carry.host;
        let conductances: Vec<Rat> = plan
            .contacts
            .iter()
            .map(|c| c.conductance.clone())
            .collect();
        let storage: Vec<&ExactRatMatrix> = loci.contacts.iter().map(|c| &c.forms[0]).collect();
        let crossed =
            host.crossed(&conductances, &storage, &vec![None; host.change.resonators.len()])?;
        let reduced = |value: &Rat, what: &'static str| -> Result<(i64, i64), HnnError> {
            match (value.numer().to_i64(), value.denom().to_i64()) {
                (Some(n), Some(d)) => Ok((n, d)),
                _ => Err(refused(what)),
            }
        };
        let gains = host
            .conductances
            .iter()
            .zip(&conductances)
            .map(|(from, to)| {
                if from == to {
                    return Ok((1, 1));
                }
                reduced(
                    &(Rat::from_integer(BigInt::from(2)) * from / (from + to)),
                    "a crossed wave's gain 2G/(G + G′) past the word",
                )
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let unit = Rat::from_integer(BigInt::from(1) << plan.lw as usize);
        let mut jumps = Vec::with_capacity(plan.k);
        for ([_, carried], [_, held]) in host.change.states.iter().zip(&crossed.states) {
            for (w, held) in carried.iter().zip(held) {
                jumps.push(reduced(
                    &((held - w) * &unit),
                    "a held rate's jump past the word",
                )?);
            }
        }
        Ok((plan.with_carry(CarryPlan { gains, jumps })?, Some(words)))
    }
}
