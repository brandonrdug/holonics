//! **The reception carry on the card** (record B §2.1–§2.4 and §2.3a; the deposit record §3;
//! host owners `holonics::hnn::word::{ReceptionCarry, Word::open_received}` and
//! `holonics::hnn::reference::Reception`).
//!
//! [definition; agent-inferred, October 3] Under a declared carry
//! (`holonics::hnn::reference::Reception::Carry`) a reception's word opens on the end change the
//! previous word read left (its refine writes it, record B §8). On the card that change **stays on
//! the card**: the word's storage, arrivals and states are copied into a buffer of their own
//! ([`crate::hnn::execute::ResidentWord::end_words`], nothing crosses the bus), and the next word
//! copies them into its own change before its open. Beside them the host keeps the carry's exact
//! mirror, read from the word's record ([`CardCarry::ended`]): the change, the field's
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
//! [definition; record B §2.4] **The carry is the last crossing, and the pump continues.** A
//! word ends between its last crossing `T = opened_at + steps − 1` and hop `T`, so the carry is the
//! change arriving at that crossing (the record at the start of the last junction step) with every
//! resonator state as hop `T − 1` left it, at tick `T`. The next word's hops read `T + step`, and
//! each loaded ring's pump phase is that tick's (`WordPlan::opened_at`). A carried resonator's rate
//! is held at its momentum `C_r w_r` across the deposit and split onto `L_w` at the open, its
//! remainder carried in the velocity's split over its denominator, as a contact's rate is. A carried
//! change off the transients' lattice, or past the signed 64-bit word, is refused at its restore.

use std::rc::Rc;

use holonics::hnn::reference::carry_bits;
use holonics::hnn::{Absorption, Field, HnnError, ReceptionCarry, WordOpening};
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

/// Whether a change moves anywhere: a storage wave, an arriving wave, a contact state or a
/// resonator state off zero.
fn moving(carry: &ReceptionCarry) -> bool {
    let change = &carry.change;
    change
        .storage
        .iter()
        .chain(change.arrivals.iter().flatten())
        .chain(change.states.iter().flatten())
        .chain(change.resonators.iter().flatten().flatten())
        .flatten()
        .any(|x| !x.is_zero())
}

impl<'c> CardCarry<'c> {
    /// [definition; the reception carry §2.1, §2.4] **The carried end a word leaves**
    /// (`Word::reception_end`): the change arriving at its last crossing, read from its record,
    /// with every resonator state as its last hop left it; that crossing's tick
    /// `opened_at + steps − 1`; each contact's conductance at its cut and momentum `C_a w_a`, and
    /// each carried resonator's momentum `C_r w_r`, under its publication; after the boundary's
    /// absorption. Under `Absorption::Nothing` its words are copied on the card.
    pub(crate) fn ended(
        word: &ResidentWord<'c>,
        opened_at: usize,
        absorption: Absorption,
    ) -> Result<Self, HnnError> {
        let plan = &word.plan;
        let change = readout::crossing(plan, &word.record);
        let loci = &word.publication.loci;
        let momenta = loci
            .contacts
            .iter()
            .zip(&change.states)
            .map(|(contact, [_, rate])| Ok(contact.forms[0].apply(rate)?))
            .collect::<Result<Vec<_>, HnnError>>()?;
        let resonator_momenta = change
            .resonators
            .iter()
            .zip(&loci.resonators)
            .map(|(state, material)| match (state, material) {
                (Some([_, rate]), Some(material)) => Ok(Some(material.forms().0.apply(rate)?)),
                _ => Ok(None),
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let host = ReceptionCarry {
            ticks: opened_at + plan.steps - 1,
            conductances: plan
                .contacts
                .iter()
                .map(|c| c.conductance.clone())
                .collect(),
            momenta,
            resonator_momenta,
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
        // Each ring's resonator state per row, zero where none is carried.
        let resonator = |side: usize| -> Vec<Rat> {
            change
                .resonators
                .iter()
                .zip(field.rings())
                .flat_map(|(state, ring)| match state {
                    Some(state) => state[side].clone(),
                    None => vec![Rat::zero(); ring.width()],
                })
                .collect()
        };
        let (resonator_u, resonator_w) = (resonator(0), resonator(1));
        let runs = change
            .storage
            .iter()
            .chain(change.arrivals.iter().flatten())
            .chain(change.states.iter().map(|[u, _]| u))
            .chain(change.states.iter().map(|[_, w]| w))
            .chain([&resonator_u, &resonator_w]);
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

    /// **The host opening it mirrors** (`holonics::hnn::WordOpening`), which the host's
    /// composition reads its diamond from (the reception carry §8).
    pub(crate) fn host(&self) -> WordOpening {
        match self {
            Self::Rest => WordOpening::Rest,
            Self::Received { carry, absorption } => WordOpening::Received {
                carry: carry.host.clone(),
                absorption: *absorption,
            },
        }
    }

    /// The field's elapsed ticks the word opens at: zero at rest.
    pub(crate) fn ticks(&self) -> usize {
        match self {
            Self::Rest => 0,
            Self::Received { carry, .. } => carry.host.ticks,
        }
    }

    /// [definition; record B §2.3a, §2.4, the deposit record §3] **The plan opening on this
    /// opening**: at the opening's tick (`WordPlan::opened_at`: the pump continues), with its carry
    /// table where the word opens on a moving carry under `Absorption::Nothing`
    /// ([`WordPlan::with_carry`]): each contact's gain `2G/(G + G′)` from the carried and the plan's
    /// conductances, and each contact row's and each loaded ring row's held-rate jump from the host
    /// owner (`ReceptionCarry::crossed` against the publication's storage and capacity forms), with
    /// the carried words the word copies in. At rest, at complete absorption, or on a zero carry the
    /// word opens on the rest change at its tick.
    pub(crate) fn plan<'w>(
        &'w self,
        plan: WordPlan,
        loci: &Loci,
    ) -> Result<(WordPlan, Option<&'w CardBuffer<'c, u8>>), HnnError> {
        let plan = plan.opened_at(self.ticks());
        let Self::Received { carry, absorption } = self else {
            return Ok((plan, None));
        };
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
        let capacities: Vec<Option<&ExactRatMatrix>> = loci
            .resonators
            .iter()
            .map(|material| material.as_ref().map(|material| material.forms().0))
            .collect();
        let crossed = host.crossed(&conductances, &storage, &capacities)?;
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
        let mut resonator_jumps = vec![(0, 1); plan.n];
        for ((ring, carried), held) in plan
            .rings
            .iter()
            .zip(&host.change.resonators)
            .zip(&crossed.resonators)
        {
            let (Some([_, carried]), Some([_, held])) = (carried, held) else {
                continue;
            };
            for (i, (w, held)) in carried.iter().zip(held).enumerate() {
                resonator_jumps[ring.rows + i] = reduced(
                    &((held - w) * &unit),
                    "a held resonator rate's jump past the word",
                )?;
            }
        }
        Ok((
            plan.with_carry(CarryPlan {
                gains,
                jumps,
                resonator_jumps,
            })?,
            Some(words),
        ))
    }
}
