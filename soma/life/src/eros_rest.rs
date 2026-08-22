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
    /// the octets do not open with this form's prefix — they are some other form, or not one
    WireIsNotThisForm { opened: Vec<u8> },
    /// a declared field ran past the end of the octets; the wire is truncated, not merely wrong
    WireEndedInsideAField {
        at: &'static str,
        declared: usize,
        remaining: usize,
    },
    /// an extent does not fit this machine's carrier
    WireExtentExceeded { at: &'static str },
    /// a declared name is not UTF-8, so it is not a name
    WireNameIsNotUtf8 { at: &'static str },
    /// every declared field was read and octets remain; a rest is the whole form, never a prefix of
    /// one, and reading a prefix as a body is how a truncated file mounts as a smaller machine
    WireHasTrailingOctets { remaining: usize },
}

/// This form's prefix and its layout version, read out of the prefix rather than restated.
pub const EROS_REST_PREFIX: [u8; 8] = *b"EROS\0\0\0\x01";
/// The codec's own layout version — the `\x01` above.
pub const EROS_REST_VERSION: u32 = EROS_REST_PREFIX[7] as u32;

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

    /// The frame's deposit census: whole quanta ⊕ the undivided remainder. Derived from the sealed
    /// frame, so it cannot drift from what the bytes say.
    ///
    /// **This is a SPECIES-ERASED QUOTIENT and it is not the model's spend.** `DepositCensus`'s own
    /// doc in `body::channel` states that it merges circuit crossing and founding into the same two
    /// hands, so **two different histories return the same census**. An earlier form of this comment
    /// called it *"THE MODEL'S SPEND"* and *"the action ledger"*, which promotes a quotient that
    /// cannot separate two histories into a path. It is a face; read it as one, and read
    /// [`Self::frame_difference`] and [`Self::medium_difference`] for what actually moved.
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

    // ---------------------------------------------------------------------------------------------
    // ★ THE WIRE — what makes a rest cross a process, and therefore what makes a run CONTINUE
    // ---------------------------------------------------------------------------------------------
    //
    // `conditioned_rest`'s header states the whole argument for one organ: *"Without one, a
    // conditioning run is a run: it reads a corpus, founds a morphology, derives, prints and exits,
    // and the next run re-reads the corpus. A body that cannot rest cannot depart from its source."*
    //
    // This is the whole-body join, and until now it had **no wire at all** — it could hold a body in
    // memory and could not hand one to a later process. So every run began at an origin and
    // recomputed its position from the raw material instead of taking it from where the last run
    // stood. That is not a gap in the physics: a deposit already bends a later passage, and priming
    // the standing terrain was measured on 2026-08-16 to move 123 of 1200 cut positions **inside one
    // process**. The gap is that the terrain died with the process.
    //
    // The carriers cross as their **exact words**, never a digest, for the reason `MediumBlock`
    // already states: a digest cannot exhibit which word moved, and which word moved is the whole of
    // the conditioning control.

    /// Seal a whole body to octets. The frame's canonical row, then every carrier by declared name
    /// with its exact words, then every organ by declared name with its opaque bytes.
    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, ErosRestRefusal> {
        let mut octets = Vec::new();
        octets.extend_from_slice(&EROS_REST_PREFIX);
        for word in &self.channel {
            octets.extend_from_slice(&word.to_le_bytes());
        }
        put_extent(&mut octets, self.medium.len(), "carrier population")?;
        for block in &self.medium {
            put_bytes(&mut octets, block.carrier.as_bytes(), "a carrier name")?;
            put_extent(&mut octets, block.words.len(), "a carrier extent")?;
            for word in &block.words {
                octets.extend_from_slice(&word.to_le_bytes());
            }
        }
        put_extent(&mut octets, self.organs.len(), "organ population")?;
        for organ in &self.organs {
            put_bytes(&mut octets, organ.organ.as_bytes(), "an organ name")?;
            put_bytes(&mut octets, &organ.bytes, "an organ rest")?;
        }
        Ok(octets)
    }

    /// Mount a whole body from octets alone.
    ///
    /// **Every refusal `seal` takes is taken again here**, by coming back through `seal` rather than
    /// constructing the fields directly. A wire that mounts therefore satisfies exactly the
    /// conditions a wire that sealed satisfied — which is `conditioned_rest`'s discipline, *"taken at
    /// the seal and again at the mount"*, and it is why a repeated carrier name cannot enter a body
    /// through the wire even though nothing on the wire itself forbids one.
    pub fn from_native_bytes(bytes: &[u8]) -> Result<Self, ErosRestRefusal> {
        let mut cursor = WireCursor { bytes, at: 0 };
        let opened = cursor.take(EROS_REST_PREFIX.len(), "the form prefix")?;
        if opened != EROS_REST_PREFIX {
            return Err(ErosRestRefusal::WireIsNotThisForm {
                opened: opened.to_vec(),
            });
        }
        let mut row = [0u32; CHANNEL_WORDS];
        for word in row.iter_mut() {
            *word = cursor.u32("the frame row")?;
        }
        let carriers = cursor.extent("carrier population")?;
        let mut medium = Vec::with_capacity(carriers.min(1 << 12));
        for _ in 0..carriers {
            let carrier = cursor.utf8("a carrier name")?;
            let extent = cursor.extent("a carrier extent")?;
            let mut words = Vec::with_capacity(extent.min(1 << 20));
            for _ in 0..extent {
                words.push(cursor.u32("a carrier word")?);
            }
            medium.push(MediumBlock { carrier, words });
        }
        let organ_count = cursor.extent("organ population")?;
        let mut organs = Vec::with_capacity(organ_count.min(1 << 12));
        for _ in 0..organ_count {
            let organ = cursor.utf8("an organ name")?;
            let bytes = cursor.bytes("an organ rest")?;
            organs.push(OrganRest { organ, bytes });
        }
        if cursor.at != cursor.bytes.len() {
            return Err(ErosRestRefusal::WireHasTrailingOctets {
                remaining: cursor.bytes.len() - cursor.at,
            });
        }
        let channel =
            LineageChannel::unpack(&row, 0).ok_or(ErosRestRefusal::ChannelNotCanonical)?;
        Self::seal(channel, medium, organs)
    }

    /// ★ RESUME — the standing position a later occurrence continues FROM.
    ///
    /// `mount` returns the frame alone, which is the pole a relating is read from and not a place to
    /// stand. This returns the whole position: the frame, every carrier by declared name, and every
    /// organ rest. A caller hands the carriers straight back to a body.
    ///
    /// **The continuation this exists for is one line at the call site**: a prior run's `own` region
    /// is the deposited terrain, so it becomes the next run's `standing`. That is the edge the
    /// terrain-priming measurement exercised inside one process; with the wire above it crosses
    /// processes, and a run stops beginning at an origin.
    ///
    /// It **consumes** the rest, which is the honest signature: a body resumes *from* a rest, and
    /// the carriers move rather than being duplicated. A caller that wants both keeps its own copy.
    pub fn resume(self) -> Result<ResumedStanding, ErosRestRefusal> {
        let channel = self.mount()?;
        Ok(ResumedStanding {
            channel,
            medium: self.medium,
            organs: self.organs,
        })
    }
}

/// ★ THE STANDING POSITION a resumed body continues from — the frame, the carriers, the organs.
///
/// This is deliberately not a body. `eros_rest` never learns an organ's anatomy and does not learn a
/// body's either; it hands back what was sealed, addressed by the names it was sealed under, and the
/// caller wires it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResumedStanding {
    pub channel: LineageChannel,
    pub medium: Vec<MediumBlock>,
    pub organs: Vec<OrganRest>,
}

impl ResumedStanding {
    /// One carrier's exact words, by the name it was sealed under. `None` is a genuine absence: the
    /// body that sealed did not carry a region under that name.
    pub fn carrier(&self, name: &str) -> Option<&[u32]> {
        self.medium
            .iter()
            .find(|block| block.carrier == name)
            .map(|block| block.words.as_slice())
    }

    /// One organ's opaque rest, by the name it was sealed under.
    pub fn organ(&self, name: &str) -> Option<&[u8]> {
        self.organs
            .iter()
            .find(|organ| organ.organ == name)
            .map(|organ| organ.bytes.as_slice())
    }
}

// -------------------------------------------------------------------------------------------------
// The wire's own small carriers. Local rather than shared, matching every other rest in `life`.
// -------------------------------------------------------------------------------------------------

fn put_extent(
    octets: &mut Vec<u8>,
    extent: usize,
    at: &'static str,
) -> Result<(), ErosRestRefusal> {
    let extent = u64::try_from(extent).map_err(|_| ErosRestRefusal::WireExtentExceeded { at })?;
    octets.extend_from_slice(&extent.to_le_bytes());
    Ok(())
}

fn put_bytes(octets: &mut Vec<u8>, value: &[u8], at: &'static str) -> Result<(), ErosRestRefusal> {
    put_extent(octets, value.len(), at)?;
    octets.extend_from_slice(value);
    Ok(())
}

struct WireCursor<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> WireCursor<'a> {
    fn take(&mut self, count: usize, at: &'static str) -> Result<&'a [u8], ErosRestRefusal> {
        let end = self
            .at
            .checked_add(count)
            .ok_or(ErosRestRefusal::WireExtentExceeded { at })?;
        if end > self.bytes.len() {
            return Err(ErosRestRefusal::WireEndedInsideAField {
                at,
                declared: count,
                remaining: self.bytes.len() - self.at,
            });
        }
        let taken = &self.bytes[self.at..end];
        self.at = end;
        Ok(taken)
    }

    fn u32(&mut self, at: &'static str) -> Result<u32, ErosRestRefusal> {
        let taken = self.take(4, at)?;
        Ok(u32::from_le_bytes([taken[0], taken[1], taken[2], taken[3]]))
    }

    fn extent(&mut self, at: &'static str) -> Result<usize, ErosRestRefusal> {
        let taken = self.take(8, at)?;
        let mut row = [0u8; 8];
        row.copy_from_slice(taken);
        usize::try_from(u64::from_le_bytes(row))
            .map_err(|_| ErosRestRefusal::WireExtentExceeded { at })
    }

    fn bytes(&mut self, at: &'static str) -> Result<Vec<u8>, ErosRestRefusal> {
        let extent = self.extent(at)?;
        Ok(self.take(extent, at)?.to_vec())
    }

    fn utf8(&mut self, at: &'static str) -> Result<String, ErosRestRefusal> {
        String::from_utf8(self.bytes(at)?).map_err(|_| ErosRestRefusal::WireNameIsNotUtf8 { at })
    }
}

#[cfg(test)]
mod wire_tests {
    use super::*;
    use body::manifold::{ErosBody, ENCLOSURE_WORDS};
    use body::num::Cog;

    const AXIS: i64 = 1 << 4;
    const SEED: &[u8] = b"the eros rest crosses";

    fn cells() -> usize {
        (AXIS * AXIS) as usize * 16
    }

    fn genesis() -> LineageChannel {
        LineageChannel::from_located_first_difference((Cog::lit(3), Cog::lit(1)))
    }

    fn a_rest() -> ErosRest {
        ErosRest::seal(
            genesis(),
            vec![
                MediumBlock {
                    carrier: "standing".to_owned(),
                    words: vec![0, 0, 7],
                },
                MediumBlock {
                    carrier: "own".to_owned(),
                    words: vec![11, 0, 13, 0],
                },
            ],
            vec![OrganRest {
                organ: "derivation".to_owned(),
                bytes: b"an organ's own wire".to_vec(),
            }],
        )
        .expect("a whole body seals")
    }

    /// The wire is exact or it is an image. `seal -> encode -> decode` must return the same rest,
    /// and re-encoding it must return the same octets.
    #[test]
    fn a_whole_body_crosses_the_wire_and_comes_back_the_same_body() {
        let sealed = a_rest();
        let octets = sealed.encode_native_bytes().expect("a rest encodes");
        let mounted = ErosRest::from_native_bytes(&octets).expect("those octets mount");
        assert_eq!(sealed, mounted, "the wire carried the body unchanged");
        assert_eq!(
            octets,
            mounted.encode_native_bytes().expect("it re-encodes"),
            "encode -> decode -> encode is byte-identical"
        );
    }

    /// A truncated wire must REFUSE and name the field it ended inside. A form that mounted a prefix
    /// would mount a smaller machine and report nothing, which is the loss the whole form exists to
    /// make detectable.
    #[test]
    fn a_truncated_wire_refuses_inside_the_field_it_ended_in() {
        let octets = a_rest().encode_native_bytes().expect("a rest encodes");
        for cut in [8usize, 20, octets.len() - 1] {
            match ErosRest::from_native_bytes(&octets[..cut]) {
                Err(ErosRestRefusal::WireEndedInsideAField { .. }) => {}
                other => panic!("a wire cut at {cut} must refuse inside a field, got {other:?}"),
            }
        }
    }

    /// Octets left over after every declared field is read are not a rest with extra room; they are
    /// evidence the reader and the writer disagree.
    #[test]
    fn trailing_octets_refuse_rather_than_being_ignored() {
        let mut octets = a_rest().encode_native_bytes().expect("a rest encodes");
        octets.push(0);
        assert!(matches!(
            ErosRest::from_native_bytes(&octets),
            Err(ErosRestRefusal::WireHasTrailingOctets { remaining: 1 })
        ));
    }

    /// Foreign octets are refused by name rather than read as a body.
    #[test]
    fn another_form_refuses_at_the_prefix() {
        let mut octets = a_rest().encode_native_bytes().expect("a rest encodes");
        octets[..8].copy_from_slice(b"CDER\0\0\0\x01");
        assert!(matches!(
            ErosRest::from_native_bytes(&octets),
            Err(ErosRestRefusal::WireIsNotThisForm { .. })
        ));
    }

    /// ★ THE GATE IS TAKEN AT THE SEAL **AND AGAIN AT THE MOUNT**. The wire format itself permits a
    /// repeated carrier name — nothing about length-prefixed octets forbids one — so this hand-built
    /// wire is well-formed and must still be refused, because `from_native_bytes` comes back through
    /// `seal`. A codec that trusted its own octets would mount a body whose address resolves to two
    /// things, which is not an address.
    #[test]
    fn a_well_formed_wire_carrying_a_repeated_carrier_name_is_still_refused() {
        let mut octets = Vec::new();
        octets.extend_from_slice(&EROS_REST_PREFIX);
        let mut row = [0u32; CHANNEL_WORDS];
        genesis().pack(&mut row, 0);
        for word in row {
            octets.extend_from_slice(&word.to_le_bytes());
        }
        put_extent(&mut octets, 2, "carrier population").expect("two carriers fit");
        for _ in 0..2 {
            put_bytes(&mut octets, b"own", "a carrier name").expect("a name fits");
            put_extent(&mut octets, 1, "a carrier extent").expect("an extent fits");
            octets.extend_from_slice(&7u32.to_le_bytes());
        }
        put_extent(&mut octets, 0, "organ population").expect("no organs fit");
        assert!(matches!(
            ErosRest::from_native_bytes(&octets),
            Err(ErosRestRefusal::CarrierNameRepeated { .. })
        ));
    }

    /// `resume` returns the position, addressed by the names it was sealed under. An absent name is
    /// a genuine absence, not an empty region.
    #[test]
    fn resume_returns_the_position_addressed_by_its_declared_names() {
        let sealed = a_rest();
        let frame = sealed.mount().expect("the frame mounts");
        let standing = sealed.resume().expect("a sealed body resumes");
        assert_eq!(standing.carrier("own"), Some([11u32, 0, 13, 0].as_slice()));
        assert_eq!(standing.carrier("standing"), Some([0u32, 0, 7].as_slice()));
        assert_eq!(
            standing.carrier("flywheel"),
            None,
            "an absent name is absent"
        );
        assert_eq!(
            standing.organ("derivation"),
            Some(b"an organ's own wire".as_slice())
        );
        assert_eq!(
            standing.channel, frame,
            "the frame a body left is the frame it resumes on"
        );
    }

    /// ★ THE DEED THE WIRE EXISTS FOR — a run continues from where the last one stood.
    ///
    /// A first body conducts over bare standing and deposits into its own region. That region is
    /// sealed, **crosses the wire**, and comes back as the *standing* a second body reads. The second
    /// body's reading must differ from a third body's reading over bare standing, or the terrain
    /// crossed the wire and conditioned nothing — which would refute the whole construction.
    ///
    /// Bounded honestly: this proves the WIRE carries the terrain and that the terrain conditions a
    /// later body. It does not cross a process; the detached arm belongs to a driver.
    #[test]
    fn a_later_body_stands_on_terrain_that_crossed_the_wire() {
        // Enough arrivals that the first body actually deposits. Three short words leave `own` all
        // zero at this axis, and the precondition below refuses that fixture rather than reading a
        // difference off a terrain that was never laid — which is the defect four drivers in this
        // tree carry, measured 2026-08-16: they hand `ErosBody` an all-zero standing chart and read
        // the cut against terrain that is not there.
        let stems: [&[u8]; 6] = [
            b"the relating is one complex product",
            b"a pole collapsed onto a relatum",
            b"the arrival lands where it did not choose",
            b"a passage deposits and a later current rides it",
            b"the reflection series closes on a crystal",
            b"an address is a collapsed face that reopens",
        ];
        let mut material: Vec<Vec<u8>> = Vec::new();
        for turn in 0..64u8 {
            for stem in &stems {
                let mut word = stem.to_vec();
                word.push(b'a' + (turn % 26));
                word.push(b'0' + (turn / 26));
                material.push(word);
            }
        }

        let bare = vec![0u32; cells()];
        let mut deposited = vec![0u32; cells()];
        let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];
        {
            let mut first =
                ErosBody::over(&bare, &mut deposited, AXIS, SEED, 1 << 20, &mut carrier);
            for word in &material {
                first.perceive(word, 100);
            }
        }
        assert!(
            deposited.iter().any(|word| *word != 0),
            "the first body deposited nothing, so there is no terrain to carry"
        );

        let sealed = ErosRest::seal(
            genesis(),
            vec![MediumBlock {
                carrier: "own".to_owned(),
                words: deposited.clone(),
            }],
            vec![OrganRest {
                organ: "conduct".to_owned(),
                bytes: b"one".to_vec(),
            }],
        )
        .expect("the first body's terrain seals");
        let octets = sealed.encode_native_bytes().expect("it encodes");
        let resumed = ErosRest::from_native_bytes(&octets)
            .expect("it mounts")
            .resume()
            .expect("it resumes");
        let terrain = resumed
            .carrier("own")
            .expect("the deposited region crossed under its declared name");
        assert_eq!(
            terrain,
            deposited.as_slice(),
            "the terrain crossed unchanged"
        );

        // The same lane, read twice: over the terrain that crossed, and over bare standing.
        let read = |standing: &[u32]| -> Vec<bool> {
            let mut own = vec![0u32; cells()];
            let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];
            let mut body = ErosBody::over(standing, &mut own, AXIS, SEED, 1 << 20, &mut carrier);
            material
                .iter()
                .map(|word| body.perceive(word, 100).thought_completed)
                .collect()
        };
        let over_terrain = read(terrain);
        let over_bare = read(&bare);
        assert_eq!(
            over_terrain.len(),
            over_bare.len(),
            "the two readings are of one lane"
        );
        assert_ne!(
            over_terrain, over_bare,
            "the terrain crossed the wire and conditioned nothing — the continuation is refuted"
        );
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
        let sealed = ErosRest::seal(
            genesis(),
            Vec::new(),
            vec![organ("derivation", b"a"), organ("language", b"b")],
        )
        .expect("a genesis frame seals");
        let mounted = sealed.mount().expect("a sealed frame mounts");
        let resealed = ErosRest::seal(mounted, sealed.medium().to_vec(), sealed.organs().to_vec())
            .expect("it seals again");
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
        let before =
            ErosRest::seal(genesis(), Vec::new(), vec![organ("derivation", b"a")]).expect("seals");
        // one passage, exactly as a run performs it — no update rule, no loss, no step
        let after_channel =
            genesis().fold_formed_hand_or_self(Cog::lit(1), Cog::lit(2), true, false);
        let after = ErosRest::seal(after_channel, Vec::new(), vec![organ("derivation", b"a")])
            .expect("seals");

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
        let twin =
            ErosRest::seal(genesis(), Vec::new(), vec![organ("derivation", b"a")]).expect("seals");
        assert!(
            before.frame_difference(&twin).is_empty(),
            "an unmoved body must report an unmoved frame, or the control would pass on anything"
        );
    }

    /// An organ that changed is named, and one that appeared is a change rather than a gap.
    #[test]
    fn organ_movement_is_named_and_an_appearing_organ_counts_as_movement() {
        let before =
            ErosRest::seal(genesis(), Vec::new(), vec![organ("derivation", b"a")]).expect("seals");
        let after = ErosRest::seal(
            genesis(),
            Vec::new(),
            vec![organ("derivation", b"a2"), organ("language", b"b")],
        )
        .expect("seals");
        let mut moved = before.organ_difference(&after);
        moved.sort();
        assert_eq!(moved, vec!["derivation".to_owned(), "language".to_owned()]);
        assert!(
            before.frame_difference(&after).is_empty(),
            "the frame did not move"
        );
    }

    /// The structural refusals fire before any octet is composed.
    #[test]
    fn a_repeated_organ_name_and_an_empty_organ_block_are_both_refused() {
        assert_eq!(
            ErosRest::seal(
                genesis(),
                Vec::new(),
                vec![organ("d", b"a"), organ("d", b"b")]
            ),
            Err(ErosRestRefusal::OrganNameRepeated { organ: "d".into() })
        );
        assert_eq!(
            ErosRest::seal(genesis(), Vec::new(), vec![organ("d", b"")]),
            Err(ErosRestRefusal::OrganRestEmpty { organ: "d".into() })
        );
    }
}
