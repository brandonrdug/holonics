//! THE EROS REST — one seal over a whole body, and the three controls that decide whether it is a
//! model at all.
//!
//! **Plan:** `blueprint/THE_EROS_INSTANTIATION.md`. **Occasion:** Brandon, 2026-08-15 —
//! *"instantiate models of Eros that are 'pretrained' in the sense that they are conditioned
//! ecological neural networks stored and able to be recycled into active processes."*
//!
//! ## What this is, and what it refuses to be
//!
//! A model instantiation is a **rest**: the sealed bytes of a body's carriers. Six per-organ rests
//! already stand — `ConditionedRest`, `AgenticLanguageNativeRest`, `LeanMathematicsNativeRest`,
//! `AgenticResearchNativeRest`, `ReturnedCompositeRest`, `CudaResidentTextMaterialNativeRest` — and
//! **no object held a whole body.** This is that join, and it is deliberately a join rather than a
//! re-implementation: each organ supplies its own wire under a declared name and this module never
//! learns any organ's anatomy.
//!
//! **There is no training mode.** The deposit happens on the passage — `e.fly = met`,
//! `sweep += basis` — so conditioning is what running *is*, and "pretrained" abbreviates *was
//! sealed after conditioning* and means nothing else. What the industry calls a training step and
//! what it calls a forward pass are the same passage; the only difference is whether the bytes are
//! written back.
//!
//! ## The frame is the part that decides
//!
//! The lineage channel carries `{anchor, sweep, basis, winding}` — the accumulated **action** of the
//! body's own history, and the pole every relating is read from. It is sealed here whole and never
//! netted: `OrientedWinding` keeps its two hands apart, so a passage followed by its opposite leaves
//! two passages standing rather than returning to zero.
//!
//! ## The controls
//!
//! ```text
//!   REMOUNT EXACTNESS   seal -> mount -> seal is BYTE-IDENTICAL
//!   CONDITIONING        seal -> run -> seal DIFFERS, and the difference is exhibited
//!   THE DISTANT GRIP    a deposit at A leaves a reading at B unmoved, AND a reaching
//!                       deposit moves its own reading with the separating word exhibited
//! ```
//!
//! The second is the anti-freezing proof and it is **predicted to fail** on the agentic ecology,
//! whose frame was measured at genesis in 21,070 of 21,070 contacts on 2026-08-15. A control that
//! passes on its first material has not been tested.

use body::channel::{DepositCensus, LineageChannel, CHANNEL_WORDS};

/// One organ's own rest, joined by declared name and opaque bytes. This module never learns an
/// organ's anatomy; each organ owns its wire and its refusals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrganRest {
    /// the organ's declared name — the address, never an index
    pub organ: String,
    /// whatever that organ's own rest serialises to
    pub bytes: Vec<u8>,
}

/// One of the body's substrate carriers, joined by declared name and its exact words.
///
/// The caller supplies `standing`, `own` and `carrier` to `ErosBody::over`, so all three are
/// readable by the caller after the body drops and **no API change is needed to seal a whole body**.
/// The enclosure rows live in the carrier, so this is where the **flywheel** is sealed — the fourth
/// body, whose absence the 2026-08-15 measurement showed decides everything downstream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MediumBlock {
    /// the carrier's declared name — `standing`, `own`, `carrier`
    pub carrier: String,
    /// its exact words; never a digest, because a digest cannot exhibit which word moved
    pub words: Vec<u32>,
}

/// Why a rest refused. Every variant is a structural refusal taken before any octet is composed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ErosRestRefusal {
    /// the packed channel row is not canonical, so the bytes are not a body's frame
    ChannelNotCanonical,
    /// two organs declared the same name — an address that resolves to two things is not an address
    OrganNameRepeated { organ: String },
    /// an organ supplied no bytes; an empty rest is not a rest, it is an absence wearing a name
    OrganRestEmpty { organ: String },
    /// two carriers declared the same name
    CarrierNameRepeated { carrier: String },
    /// two rests of the same body disagree on a carrier's extent, so no word-wise comparison exists
    CarrierExtentDisagrees {
        carrier: String,
        was: usize,
        now: usize,
    },
}

/// ★ ONE SEAL OVER A WHOLE BODY.
///
/// The frame is carried as its canonical packed row; the organs are carried by declared name. The
/// action ledger is **derived** on demand rather than stored beside the frame, so the two can never
/// disagree — a rest that carried both would have to be checked against itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ErosRest {
    channel: [u32; CHANNEL_WORDS],
    medium: Vec<MediumBlock>,
    organs: Vec<OrganRest>,
}

impl ErosRest {
    /// Seal a live body's frame together with its declared organ rests.
    ///
    /// Refuses a repeated organ name and an empty organ block before composing anything, and
    /// refuses a channel row that does not round-trip its own canonical form.
    pub fn seal(
        channel: LineageChannel,
        medium: Vec<MediumBlock>,
        organs: Vec<OrganRest>,
    ) -> Result<Self, ErosRestRefusal> {
        let mut carriers: Vec<&str> = Vec::new();
        for block in &medium {
            if carriers.contains(&block.carrier.as_str()) {
                return Err(ErosRestRefusal::CarrierNameRepeated {
                    carrier: block.carrier.clone(),
                });
            }
            carriers.push(&block.carrier);
        }
        let mut seen: Vec<&str> = Vec::new();
        for organ in &organs {
            if organ.bytes.is_empty() {
                return Err(ErosRestRefusal::OrganRestEmpty {
                    organ: organ.organ.clone(),
                });
            }
            if seen.contains(&organ.organ.as_str()) {
                return Err(ErosRestRefusal::OrganNameRepeated {
                    organ: organ.organ.clone(),
                });
            }
            seen.push(&organ.organ);
        }
        let mut row = [0u32; CHANNEL_WORDS];
        channel.pack(&mut row, 0);
        if !LineageChannel::packed_row_is_canonical(&row, 0) {
            return Err(ErosRestRefusal::ChannelNotCanonical);
        }
        Ok(Self {
            channel: row,
            medium,
            organs,
        })
    }

    /// Mount the frame back. This is a **resume**, never a restart: across a seam the worldline
    /// continues, so the channel returned here is the same frame the body left, sweep and winding
    /// intact.
    pub fn mount(&self) -> Result<LineageChannel, ErosRestRefusal> {
        LineageChannel::unpack(&self.channel, 0).ok_or(ErosRestRefusal::ChannelNotCanonical)
    }

    /// ★ THE MODEL'S SPEND, readable without mounting it: whole quanta ⊕ the undivided remainder.
    /// Derived from the sealed frame, so it cannot drift from what the bytes say.
    pub fn ledger(&self) -> Result<DepositCensus, ErosRestRefusal> {
        Ok(self.mount()?.deposit_census())
    }

    pub fn organs(&self) -> &[OrganRest] {
        &self.organs
    }

    pub fn medium(&self) -> &[MediumBlock] {
        &self.medium
    }

    /// ★ WHICH WORDS OF WHICH CARRIER MOVED — the whole-body arm of the conditioning control.
    ///
    /// Returns, per carrier, the **words** that differ. A carrier present in one rest and absent in
    /// the other is named with an empty word list, because an appearing carrier is a change and not
    /// a missing comparison. Disagreeing extents refuse rather than truncate: a comparison over a
    /// prefix is not a comparison.
    ///
    /// The words are named rather than counted, so a caller can ask **where** a deposit landed —
    /// which is what the distant-grip control needs and what a digest could never supply.
    pub fn medium_difference(
        &self,
        later: &ErosRest,
    ) -> Result<Vec<(String, Vec<usize>)>, ErosRestRefusal> {
        let mut moved = Vec::new();
        for block in &self.medium {
            match later.medium.iter().find(|b| b.carrier == block.carrier) {
                None => moved.push((block.carrier.clone(), Vec::new())),
                Some(other) => {
                    if other.words.len() != block.words.len() {
                        return Err(ErosRestRefusal::CarrierExtentDisagrees {
                            carrier: block.carrier.clone(),
                            was: block.words.len(),
                            now: other.words.len(),
                        });
                    }
                    let at: Vec<usize> = (0..block.words.len())
                        .filter(|&i| block.words[i] != other.words[i])
                        .collect();
                    if !at.is_empty() {
                        moved.push((block.carrier.clone(), at));
                    }
                }
            }
        }
        for block in &later.medium {
            if !self.medium.iter().any(|b| b.carrier == block.carrier) {
                moved.push((block.carrier.clone(), Vec::new()));
            }
        }
        Ok(moved)
    }

    /// The canonical bytes of the frame — what a remount-exactness control compares.
    pub fn frame_row(&self) -> &[u32; CHANNEL_WORDS] {
        &self.channel
    }

    /// ★ DID CONDITIONING ADVANCE THE BODY. Returns the words at which two rests of the same body
    /// differ, and an **empty return means the run deposited nothing** — the model is frozen in
    /// fact, whatever any document says.
    ///
    /// A count is deliberately not returned. The moved words are named so the difference is
    /// exhibited rather than tallied.
    pub fn frame_difference(&self, later: &ErosRest) -> Vec<usize> {
        (0..CHANNEL_WORDS)
            .filter(|&at| self.channel[at] != later.channel[at])
            .collect()
    }

    /// Whether any organ block moved, by declared name. Organs present in one rest and absent in
    /// the other are named too — an organ that appeared is a change, not a missing comparison.
    pub fn organ_difference(&self, later: &ErosRest) -> Vec<String> {
        let mut moved = Vec::new();
        for organ in &self.organs {
            match later.organs.iter().find(|o| o.organ == organ.organ) {
                None => moved.push(organ.organ.clone()),
                Some(other) if other.bytes != organ.bytes => moved.push(organ.organ.clone()),
                Some(_) => {}
            }
        }
        for organ in &later.organs {
            if !self.organs.iter().any(|o| o.organ == organ.organ) {
                moved.push(organ.organ.clone());
            }
        }
        moved
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::num::Cog;

    fn organ(name: &str, bytes: &[u8]) -> OrganRest {
        OrganRest {
            organ: name.to_owned(),
            bytes: bytes.to_vec(),
        }
    }

    fn genesis() -> LineageChannel {
        LineageChannel::from_located_first_difference((Cog::lit(3), Cog::lit(1)))
    }

    /// CONTROL 1 — REMOUNT EXACTNESS. `seal -> mount -> seal` must be byte-identical, or the form on
    /// disk is a lossy image and no reading through it is evidence.
    #[test]
    fn a_rest_remounts_to_the_same_bytes_or_it_is_a_lossy_image() {
        let sealed = ErosRest::seal(genesis(), Vec::new(), vec![organ("derivation", b"a"), organ("language", b"b")])
            .expect("a genesis frame seals");
        let mounted = sealed.mount().expect("a sealed frame mounts");
        let resealed = ErosRest::seal(mounted, sealed.medium().to_vec(), sealed.organs().to_vec()).expect("it seals again");
        assert_eq!(sealed, resealed, "seal -> mount -> seal is byte-identical");
        assert!(
            sealed.frame_difference(&resealed).is_empty(),
            "no word of the frame moved across a round trip"
        );
    }

    /// CONTROL 2 — CONDITIONING ADVANCES IT. A run must move the frame, and the moved words must be
    /// **exhibited**. This is the anti-freezing proof: an empty difference means the body is frozen
    /// in fact whatever the doctrine says.
    #[test]
    fn conditioning_moves_the_frame_and_the_moved_words_are_exhibited() {
        let before = ErosRest::seal(genesis(), Vec::new(), vec![organ("derivation", b"a")]).expect("seals");
        // one passage, exactly as a run performs it — no update rule, no loss, no step
        let after_channel = genesis().fold_formed_hand_or_self(Cog::lit(1), Cog::lit(2), true, false);
        let after = ErosRest::seal(after_channel, Vec::new(), vec![organ("derivation", b"a")]).expect("seals");

        let moved = before.frame_difference(&after);
        assert!(
            !moved.is_empty(),
            "a passage that deposits nothing leaves a frozen model; the control must fail there"
        );
        // the ledger's spend is readable off the rest without mounting the body
        let spent_before = before.ledger().expect("a ledger").deposits;
        let spent_after = after.ledger().expect("a ledger").deposits;
        assert_ne!(spent_before, spent_after, "the action ledger advanced");

        // AND THE NEGATIVE ARM, which is what makes the control a control: a rest sealed twice from
        // the SAME frame must show no movement at all.
        let twin = ErosRest::seal(genesis(), Vec::new(), vec![organ("derivation", b"a")]).expect("seals");
        assert!(
            before.frame_difference(&twin).is_empty(),
            "an unmoved body must report an unmoved frame, or the control would pass on anything"
        );
    }

    /// An organ that changed is named, and one that appeared is a change rather than a gap.
    #[test]
    fn organ_movement_is_named_and_an_appearing_organ_counts_as_movement() {
        let before = ErosRest::seal(genesis(), Vec::new(), vec![organ("derivation", b"a")]).expect("seals");
        let after = ErosRest::seal(
            genesis(),
            Vec::new(),
            vec![organ("derivation", b"a2"), organ("language", b"b")],
        )
        .expect("seals");
        let mut moved = before.organ_difference(&after);
        moved.sort();
        assert_eq!(moved, vec!["derivation".to_owned(), "language".to_owned()]);
        assert!(before.frame_difference(&after).is_empty(), "the frame did not move");
    }

    /// The structural refusals fire before any octet is composed.
    #[test]
    fn a_repeated_organ_name_and_an_empty_organ_block_are_both_refused() {
        assert_eq!(
            ErosRest::seal(genesis(), Vec::new(), vec![organ("d", b"a"), organ("d", b"b")]),
            Err(ErosRestRefusal::OrganNameRepeated { organ: "d".into() })
        );
        assert_eq!(
            ErosRest::seal(genesis(), Vec::new(), vec![organ("d", b"")]),
            Err(ErosRestRefusal::OrganRestEmpty { organ: "d".into() })
        );
    }
}
