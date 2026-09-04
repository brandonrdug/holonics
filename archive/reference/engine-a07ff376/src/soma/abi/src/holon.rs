//! Receiver-relative swept construction over shared presentation cuts.

pub const LAYOUT_VERSION: u32 = 1;

pub const HEADER_VERSION: usize = 0;
pub const HEADER_CUTS_LO: usize = 1;
pub const HEADER_CUTS_HI: usize = 2;
pub const HEADER_HOLONS_LO: usize = 3;
pub const HEADER_HOLONS_HI: usize = 4;
pub const HEADER_CUT_INCIDENCES_LO: usize = 5;
pub const HEADER_CUT_INCIDENCES_HI: usize = 6;
pub const HEADER_RECEIPTS_LO: usize = 7;
pub const HEADER_RECEIPTS_HI: usize = 8;
pub const HEADER_RECEIPT_INCIDENCES_LO: usize = 9;
pub const HEADER_RECEIPT_INCIDENCES_HI: usize = 10;
pub const HEADER_RESIDUALS_LO: usize = 11;
pub const HEADER_RESIDUALS_HI: usize = 12;
pub const HEADER_RESIDUAL_INCIDENCES_LO: usize = 13;
pub const HEADER_RESIDUAL_INCIDENCES_HI: usize = 14;
pub const HEADER_WORDS: usize = 15;

pub const CUT_PRESENTATION_LO: usize = 0;
pub const CUT_PRESENTATION_HI: usize = 1;
pub const CUT_CONFIGURATION_LO: usize = 2;
pub const CUT_CONFIGURATION_HI: usize = 3;
pub const CUT_WORDS: usize = 4;

pub const REFERENCE_ORDINAL_LO: usize = 0;
pub const REFERENCE_ORDINAL_HI: usize = 1;
pub const REFERENCE_WORDS: usize = 2;

pub const HOLON_CUT_INCIDENCE_OFFSET_LO: usize = 0;
pub const HOLON_CUT_INCIDENCE_OFFSET_HI: usize = 1;
pub const HOLON_CUT_INCIDENCES_LO: usize = 2;
pub const HOLON_CUT_INCIDENCES_HI: usize = 3;
pub const HOLON_RECEIPT_INCIDENCE_OFFSET_LO: usize = 4;
pub const HOLON_RECEIPT_INCIDENCE_OFFSET_HI: usize = 5;
pub const HOLON_RECEIPT_INCIDENCES_LO: usize = 6;
pub const HOLON_RECEIPT_INCIDENCES_HI: usize = 7;
pub const HOLON_RESIDUAL_INCIDENCE_OFFSET_LO: usize = 8;
pub const HOLON_RESIDUAL_INCIDENCE_OFFSET_HI: usize = 9;
pub const HOLON_RESIDUAL_INCIDENCES_LO: usize = 10;
pub const HOLON_RESIDUAL_INCIDENCES_HI: usize = 11;
pub const HOLON_WORDS: usize = 12;

pub const RESIDUAL_CUT_LO: usize = 0;
pub const RESIDUAL_CUT_HI: usize = 1;
pub const RESIDUAL_CONFIGURATION_INCIDENCE_OFFSET_LO: usize = 2;
pub const RESIDUAL_CONFIGURATION_INCIDENCE_OFFSET_HI: usize = 3;
pub const RESIDUAL_INCIDENCES_LO: usize = 4;
pub const RESIDUAL_INCIDENCES_HI: usize = 5;
pub const RESIDUAL_WORDS: usize = 6;

pub const RECEIPT_BEFORE_CUT_LO: usize = 0;
pub const RECEIPT_BEFORE_CUT_HI: usize = 1;
pub const RECEIPT_MEETING_CUT_LO: usize = 2;
pub const RECEIPT_MEETING_CUT_HI: usize = 3;
pub const RECEIPT_DEED_CUT_LO: usize = 4;
pub const RECEIPT_DEED_CUT_HI: usize = 5;
pub const RECEIPT_CONSEQUENCE_CUT_LO: usize = 6;
pub const RECEIPT_CONSEQUENCE_CUT_HI: usize = 7;
pub const RECEIPT_RETURN_CUT_LO: usize = 8;
pub const RECEIPT_RETURN_CUT_HI: usize = 9;
pub const RECEIPT_AFTER_CUT_LO: usize = 10;
pub const RECEIPT_AFTER_CUT_HI: usize = 11;
pub const RECEIPT_RESIDUAL_INCIDENCE_OFFSET_LO: usize = 12;
pub const RECEIPT_RESIDUAL_INCIDENCE_OFFSET_HI: usize = 13;
pub const RECEIPT_RESIDUAL_INCIDENCES_LO: usize = 14;
pub const RECEIPT_RESIDUAL_INCIDENCES_HI: usize = 15;
pub const RECEIPT_WORDS: usize = 16;

pub const SILENT_RECEIPT_BEFORE_CUT_LO: usize = 0;
pub const SILENT_RECEIPT_BEFORE_CUT_HI: usize = 1;
pub const SILENT_RECEIPT_MEETING_CUT_LO: usize = 2;
pub const SILENT_RECEIPT_MEETING_CUT_HI: usize = 3;
pub const SILENT_RECEIPT_DEED_CUT_LO: usize = 4;
pub const SILENT_RECEIPT_DEED_CUT_HI: usize = 5;
pub const SILENT_RECEIPT_AFTER_CUT_LO: usize = 6;
pub const SILENT_RECEIPT_AFTER_CUT_HI: usize = 7;
pub const SILENT_RECEIPT_RESIDUAL_INCIDENCE_OFFSET_LO: usize = 8;
pub const SILENT_RECEIPT_RESIDUAL_INCIDENCE_OFFSET_HI: usize = 9;
pub const SILENT_RECEIPT_RESIDUAL_INCIDENCES_LO: usize = 10;
pub const SILENT_RECEIPT_RESIDUAL_INCIDENCES_HI: usize = 11;
pub const SILENT_RECEIPT_WORDS: usize = 12;

pub const SOURCE_DISPOSITION_TAG: usize = 0;
pub const SOURCE_DISPOSITION_RETURNED_CURRENT_LO: usize = 1;
pub const SOURCE_DISPOSITION_RETURNED_CURRENT_HI: usize = 2;
pub const SOURCE_DISPOSITION_WORDS: usize = 3;
pub const SOURCE_STANDING: u32 = 1;
pub const SOURCE_CONTINUED: u32 = 2;
pub const SOURCE_ENDED: u32 = 3;

pub const RETURN_ORIGIN_TAG: usize = 0;
pub const RETURN_ORIGIN_SOURCE_CURRENT_LO: usize = 1;
pub const RETURN_ORIGIN_SOURCE_CURRENT_HI: usize = 2;
pub const RETURN_ORIGIN_WORDS: usize = 3;
pub const RETURN_BIRTH: u32 = 1;
pub const RETURN_CONTINUED: u32 = 2;

pub const LINEAGE_INCIDENCE_SOURCE_INCIDENCE_LO: usize = 0;
pub const LINEAGE_INCIDENCE_SOURCE_INCIDENCE_HI: usize = 1;
pub const LINEAGE_INCIDENCE_SOURCE_EVENT_OFFSET_LO: usize = 2;
pub const LINEAGE_INCIDENCE_SOURCE_EVENT_OFFSET_HI: usize = 3;
pub const LINEAGE_INCIDENCE_RETURNED_INCIDENCE_LO: usize = 4;
pub const LINEAGE_INCIDENCE_RETURNED_INCIDENCE_HI: usize = 5;
pub const LINEAGE_INCIDENCE_RETURNED_EVENT_OFFSET_LO: usize = 6;
pub const LINEAGE_INCIDENCE_RETURNED_EVENT_OFFSET_HI: usize = 7;
pub const LINEAGE_INCIDENCE_WORDS: usize = 8;

pub const SETTLEMENT_LAYOUT_VERSION: u32 = 1;
pub const SETTLEMENT_HEADER_VERSION: usize = 0;
pub const SETTLEMENT_HEADER_SETTLEMENTS_LO: usize = 1;
pub const SETTLEMENT_HEADER_SETTLEMENTS_HI: usize = 2;
pub const SETTLEMENT_HEADER_SILENT_RECEIPTS_LO: usize = 3;
pub const SETTLEMENT_HEADER_SILENT_RECEIPTS_HI: usize = 4;
pub const SETTLEMENT_HEADER_SOURCE_DISPOSITIONS_LO: usize = 5;
pub const SETTLEMENT_HEADER_SOURCE_DISPOSITIONS_HI: usize = 6;
pub const SETTLEMENT_HEADER_RETURN_ORIGINS_LO: usize = 7;
pub const SETTLEMENT_HEADER_RETURN_ORIGINS_HI: usize = 8;
pub const SETTLEMENT_HEADER_LINEAGE_INCIDENCES_LO: usize = 9;
pub const SETTLEMENT_HEADER_LINEAGE_INCIDENCES_HI: usize = 10;
pub const SETTLEMENT_HEADER_WORDS: usize = 11;

pub const SETTLEMENT_TRANSITION_LO: usize = 0;
pub const SETTLEMENT_TRANSITION_HI: usize = 1;
pub const SETTLEMENT_KIND: usize = 2;
pub const SETTLEMENT_RECEIPT_LO: usize = 3;
pub const SETTLEMENT_RECEIPT_HI: usize = 4;
pub const SETTLEMENT_SOURCE_OFFSET_LO: usize = 5;
pub const SETTLEMENT_SOURCE_OFFSET_HI: usize = 6;
pub const SETTLEMENT_SOURCES_LO: usize = 7;
pub const SETTLEMENT_SOURCES_HI: usize = 8;
pub const SETTLEMENT_ORIGIN_OFFSET_LO: usize = 9;
pub const SETTLEMENT_ORIGIN_OFFSET_HI: usize = 10;
pub const SETTLEMENT_ORIGINS_LO: usize = 11;
pub const SETTLEMENT_ORIGINS_HI: usize = 12;
pub const SETTLEMENT_LINEAGE_OFFSET_LO: usize = 13;
pub const SETTLEMENT_LINEAGE_OFFSET_HI: usize = 14;
pub const SETTLEMENT_LINEAGES_LO: usize = 15;
pub const SETTLEMENT_LINEAGES_HI: usize = 16;
pub const SETTLEMENT_WORDS: usize = 17;
pub const SETTLEMENT_RETURNED: u32 = 1;
pub const SETTLEMENT_SILENT: u32 = 2;

#[inline]
const fn u64_words(value: u64) -> [u32; 2] {
    [value as u32, (value >> 32) as u32]
}

#[inline]
const fn u64_from_words(lo: u32, hi: u32) -> u64 {
    lo as u64 | ((hi as u64) << 32)
}

#[inline]
const fn optional_span_is_valid(offset: u64, extent: u64) -> bool {
    if extent == 0 {
        offset == 0
    } else {
        offset.checked_add(extent).is_some()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Header(pub [u32; HEADER_WORDS]);

impl Header {
    #[inline]
    pub const fn new(
        cuts: u64,
        holons: u64,
        cut_incidences: u64,
        receipts: u64,
        receipt_incidences: u64,
        residuals: u64,
        residual_incidences: u64,
    ) -> Option<Self> {
        if cuts == 0 || holons == 0 || cut_incidences == 0 {
            return None;
        }
        if (receipts == 0) != (receipt_incidences == 0)
            || (residuals == 0) != (residual_incidences == 0)
        {
            return None;
        }
        let cuts = u64_words(cuts);
        let holons = u64_words(holons);
        let cut_incidences = u64_words(cut_incidences);
        let receipts = u64_words(receipts);
        let receipt_incidences = u64_words(receipt_incidences);
        let residuals = u64_words(residuals);
        let residual_incidences = u64_words(residual_incidences);
        Some(Self([
            LAYOUT_VERSION,
            cuts[0],
            cuts[1],
            holons[0],
            holons[1],
            cut_incidences[0],
            cut_incidences[1],
            receipts[0],
            receipts[1],
            receipt_incidences[0],
            receipt_incidences[1],
            residuals[0],
            residuals[1],
            residual_incidences[0],
            residual_incidences[1],
        ]))
    }

    #[inline]
    pub const fn from_words(words: [u32; HEADER_WORDS]) -> Option<Self> {
        if words[HEADER_VERSION] != LAYOUT_VERSION {
            return None;
        }
        Self::new(
            u64_from_words(words[HEADER_CUTS_LO], words[HEADER_CUTS_HI]),
            u64_from_words(words[HEADER_HOLONS_LO], words[HEADER_HOLONS_HI]),
            u64_from_words(
                words[HEADER_CUT_INCIDENCES_LO],
                words[HEADER_CUT_INCIDENCES_HI],
            ),
            u64_from_words(words[HEADER_RECEIPTS_LO], words[HEADER_RECEIPTS_HI]),
            u64_from_words(
                words[HEADER_RECEIPT_INCIDENCES_LO],
                words[HEADER_RECEIPT_INCIDENCES_HI],
            ),
            u64_from_words(words[HEADER_RESIDUALS_LO], words[HEADER_RESIDUALS_HI]),
            u64_from_words(
                words[HEADER_RESIDUAL_INCIDENCES_LO],
                words[HEADER_RESIDUAL_INCIDENCES_HI],
            ),
        )
    }

    #[inline]
    pub const fn cuts(self) -> u64 {
        u64_from_words(self.0[HEADER_CUTS_LO], self.0[HEADER_CUTS_HI])
    }

    #[inline]
    pub const fn holons(self) -> u64 {
        u64_from_words(self.0[HEADER_HOLONS_LO], self.0[HEADER_HOLONS_HI])
    }

    #[inline]
    pub const fn cut_incidences(self) -> u64 {
        u64_from_words(
            self.0[HEADER_CUT_INCIDENCES_LO],
            self.0[HEADER_CUT_INCIDENCES_HI],
        )
    }

    #[inline]
    pub const fn receipts(self) -> u64 {
        u64_from_words(self.0[HEADER_RECEIPTS_LO], self.0[HEADER_RECEIPTS_HI])
    }

    #[inline]
    pub const fn receipt_incidences(self) -> u64 {
        u64_from_words(
            self.0[HEADER_RECEIPT_INCIDENCES_LO],
            self.0[HEADER_RECEIPT_INCIDENCES_HI],
        )
    }

    #[inline]
    pub const fn residuals(self) -> u64 {
        u64_from_words(self.0[HEADER_RESIDUALS_LO], self.0[HEADER_RESIDUALS_HI])
    }

    #[inline]
    pub const fn residual_incidences(self) -> u64 {
        u64_from_words(
            self.0[HEADER_RESIDUAL_INCIDENCES_LO],
            self.0[HEADER_RESIDUAL_INCIDENCES_HI],
        )
    }

    #[inline]
    pub const fn words(self) -> [u32; HEADER_WORDS] {
        self.0
    }
}

/// One instantaneous receiver cut.  Both ordinals are local to the durable membrane journal;
/// the presentation retains the actual configuration and all source/world coordinates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct BoundaryCut(pub [u32; CUT_WORDS]);

impl BoundaryCut {
    #[inline]
    pub const fn new(presentation: u64, configuration: u64) -> Self {
        let presentation = u64_words(presentation);
        let configuration = u64_words(configuration);
        Self([
            presentation[0],
            presentation[1],
            configuration[0],
            configuration[1],
        ])
    }

    #[inline]
    pub const fn presentation(self) -> u64 {
        u64_from_words(self.0[CUT_PRESENTATION_LO], self.0[CUT_PRESENTATION_HI])
    }

    /// Generic execution-grade name for the first ordinal.  Historical records use a
    /// presentation population; the native membrane uses an active-cut body population.  The
    /// wire is unchanged and neither spelling enters Soma.
    #[inline]
    pub const fn body(self) -> u64 {
        self.presentation()
    }

    #[inline]
    pub const fn configuration(self) -> u64 {
        u64_from_words(self.0[CUT_CONFIGURATION_LO], self.0[CUT_CONFIGURATION_HI])
    }

    /// Generic execution-grade name for the receiver-local cut within [`Self::body`].
    #[inline]
    pub const fn cut(self) -> u64 {
        self.configuration()
    }

    #[inline]
    pub const fn words(self) -> [u32; CUT_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; CUT_WORDS]) -> Self {
        Self(words)
    }
}

macro_rules! reference_row {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        #[repr(transparent)]
        pub struct $name(pub [u32; REFERENCE_WORDS]);

        impl $name {
            #[inline]
            pub const fn new(ordinal: u64) -> Self {
                Self(u64_words(ordinal))
            }

            #[inline]
            pub const fn ordinal(self) -> u64 {
                u64_from_words(self.0[REFERENCE_ORDINAL_LO], self.0[REFERENCE_ORDINAL_HI])
            }

            #[inline]
            pub const fn words(self) -> [u32; REFERENCE_WORDS] {
                self.0
            }

            #[inline]
            pub const fn from_words(words: [u32; REFERENCE_WORDS]) -> Self {
                Self(words)
            }
        }
    };
}

reference_row!(CutIncidence);
reference_row!(ReceiptIncidence);
reference_row!(ResidualIncidence);

/// One allocation-free reference into the shared populations making a bounded HolonArc.
/// Cut incidence is nonempty.  Receipt and residual populations may be exactly empty for an
/// open first reception; their canonical empty spelling is offset zero, extent zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct HolonSpan(pub [u32; HOLON_WORDS]);

impl HolonSpan {
    #[inline]
    pub const fn new(
        cut_incidence_offset: u64,
        cut_incidences: u64,
        receipt_incidence_offset: u64,
        receipt_incidences: u64,
        residual_incidence_offset: u64,
        residual_incidences: u64,
    ) -> Option<Self> {
        if cut_incidences == 0
            || cut_incidence_offset.checked_add(cut_incidences).is_none()
            || !optional_span_is_valid(receipt_incidence_offset, receipt_incidences)
            || !optional_span_is_valid(residual_incidence_offset, residual_incidences)
        {
            return None;
        }
        let cut_offset = u64_words(cut_incidence_offset);
        let cuts = u64_words(cut_incidences);
        let receipt_offset = u64_words(receipt_incidence_offset);
        let receipts = u64_words(receipt_incidences);
        let residual_offset = u64_words(residual_incidence_offset);
        let residuals = u64_words(residual_incidences);
        Some(Self([
            cut_offset[0],
            cut_offset[1],
            cuts[0],
            cuts[1],
            receipt_offset[0],
            receipt_offset[1],
            receipts[0],
            receipts[1],
            residual_offset[0],
            residual_offset[1],
            residuals[0],
            residuals[1],
        ]))
    }

    #[inline]
    pub const fn cut_incidence_offset(self) -> u64 {
        u64_from_words(
            self.0[HOLON_CUT_INCIDENCE_OFFSET_LO],
            self.0[HOLON_CUT_INCIDENCE_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn cut_incidences(self) -> u64 {
        u64_from_words(
            self.0[HOLON_CUT_INCIDENCES_LO],
            self.0[HOLON_CUT_INCIDENCES_HI],
        )
    }

    #[inline]
    pub const fn receipt_incidence_offset(self) -> u64 {
        u64_from_words(
            self.0[HOLON_RECEIPT_INCIDENCE_OFFSET_LO],
            self.0[HOLON_RECEIPT_INCIDENCE_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn receipt_incidences(self) -> u64 {
        u64_from_words(
            self.0[HOLON_RECEIPT_INCIDENCES_LO],
            self.0[HOLON_RECEIPT_INCIDENCES_HI],
        )
    }

    #[inline]
    pub const fn residual_incidence_offset(self) -> u64 {
        u64_from_words(
            self.0[HOLON_RESIDUAL_INCIDENCE_OFFSET_LO],
            self.0[HOLON_RESIDUAL_INCIDENCE_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn residual_incidences(self) -> u64 {
        u64_from_words(
            self.0[HOLON_RESIDUAL_INCIDENCES_LO],
            self.0[HOLON_RESIDUAL_INCIDENCES_HI],
        )
    }

    #[inline]
    pub const fn words(self) -> [u32; HOLON_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; HOLON_WORDS]) -> Option<Self> {
        Self::new(
            u64_from_words(
                words[HOLON_CUT_INCIDENCE_OFFSET_LO],
                words[HOLON_CUT_INCIDENCE_OFFSET_HI],
            ),
            u64_from_words(
                words[HOLON_CUT_INCIDENCES_LO],
                words[HOLON_CUT_INCIDENCES_HI],
            ),
            u64_from_words(
                words[HOLON_RECEIPT_INCIDENCE_OFFSET_LO],
                words[HOLON_RECEIPT_INCIDENCE_OFFSET_HI],
            ),
            u64_from_words(
                words[HOLON_RECEIPT_INCIDENCES_LO],
                words[HOLON_RECEIPT_INCIDENCES_HI],
            ),
            u64_from_words(
                words[HOLON_RESIDUAL_INCIDENCE_OFFSET_LO],
                words[HOLON_RESIDUAL_INCIDENCE_OFFSET_HI],
            ),
            u64_from_words(
                words[HOLON_RESIDUAL_INCIDENCES_LO],
                words[HOLON_RESIDUAL_INCIDENCES_HI],
            ),
        )
    }
}

/// One exact nonempty incidence section of one boundary cut.  Several rows may describe a
/// noncontiguous residual without copying any event material.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct ResidualSpan(pub [u32; RESIDUAL_WORDS]);

impl ResidualSpan {
    #[inline]
    pub const fn new(
        cut: u64,
        configuration_incidence_offset: u64,
        incidences: u64,
    ) -> Option<Self> {
        if incidences == 0
            || configuration_incidence_offset
                .checked_add(incidences)
                .is_none()
        {
            return None;
        }
        let cut = u64_words(cut);
        let offset = u64_words(configuration_incidence_offset);
        let incidences = u64_words(incidences);
        Some(Self([
            cut[0],
            cut[1],
            offset[0],
            offset[1],
            incidences[0],
            incidences[1],
        ]))
    }

    #[inline]
    pub const fn cut(self) -> u64 {
        u64_from_words(self.0[RESIDUAL_CUT_LO], self.0[RESIDUAL_CUT_HI])
    }

    #[inline]
    pub const fn configuration_incidence_offset(self) -> u64 {
        u64_from_words(
            self.0[RESIDUAL_CONFIGURATION_INCIDENCE_OFFSET_LO],
            self.0[RESIDUAL_CONFIGURATION_INCIDENCE_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn incidences(self) -> u64 {
        u64_from_words(
            self.0[RESIDUAL_INCIDENCES_LO],
            self.0[RESIDUAL_INCIDENCES_HI],
        )
    }

    #[inline]
    pub const fn words(self) -> [u32; RESIDUAL_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; RESIDUAL_WORDS]) -> Option<Self> {
        Self::new(
            u64_from_words(words[RESIDUAL_CUT_LO], words[RESIDUAL_CUT_HI]),
            u64_from_words(
                words[RESIDUAL_CONFIGURATION_INCIDENCE_OFFSET_LO],
                words[RESIDUAL_CONFIGURATION_INCIDENCE_OFFSET_HI],
            ),
            u64_from_words(words[RESIDUAL_INCIDENCES_LO], words[RESIDUAL_INCIDENCES_HI]),
        )
    }
}

/// Fixed-layout fate of one source carrier at a world settlement. This row is causal
/// continuity, not an output score: a source either remains standing, continues as one named
/// returned carrier, or ends under an actual world consequence. Split ancestry remains in
/// independent [`LineageIncidenceRow`] rows rather than being collapsed into this one mount.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct SourceDispositionRow(pub [u32; SOURCE_DISPOSITION_WORDS]);

impl SourceDispositionRow {
    #[inline]
    pub const fn standing() -> Self {
        Self([SOURCE_STANDING, 0, 0])
    }

    #[inline]
    pub const fn continued(returned_current: u64) -> Self {
        let returned = u64_words(returned_current);
        Self([SOURCE_CONTINUED, returned[0], returned[1]])
    }

    #[inline]
    pub const fn ended() -> Self {
        Self([SOURCE_ENDED, 0, 0])
    }

    #[inline]
    pub const fn tag(self) -> u32 {
        self.0[SOURCE_DISPOSITION_TAG]
    }

    #[inline]
    pub const fn returned_current(self) -> Option<u64> {
        if self.tag() == SOURCE_CONTINUED {
            Some(u64_from_words(
                self.0[SOURCE_DISPOSITION_RETURNED_CURRENT_LO],
                self.0[SOURCE_DISPOSITION_RETURNED_CURRENT_HI],
            ))
        } else {
            None
        }
    }

    #[inline]
    pub const fn words(self) -> [u32; SOURCE_DISPOSITION_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; SOURCE_DISPOSITION_WORDS]) -> Option<Self> {
        match words[SOURCE_DISPOSITION_TAG] {
            SOURCE_STANDING | SOURCE_ENDED
                if words[SOURCE_DISPOSITION_RETURNED_CURRENT_LO] == 0
                    && words[SOURCE_DISPOSITION_RETURNED_CURRENT_HI] == 0 =>
            {
                Some(Self(words))
            }
            SOURCE_CONTINUED => Some(Self(words)),
            _ => None,
        }
    }
}

/// Fixed-layout origin of one returned carrier. Physical continuation names the one exact
/// source carrier mounted into it; a birth owns a fresh carrier while its plural causal parents
/// remain explicit lineage-incidence rows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct ReturnOriginRow(pub [u32; RETURN_ORIGIN_WORDS]);

impl ReturnOriginRow {
    #[inline]
    pub const fn birth() -> Self {
        Self([RETURN_BIRTH, 0, 0])
    }

    #[inline]
    pub const fn continued(source_current: u64) -> Self {
        let source = u64_words(source_current);
        Self([RETURN_CONTINUED, source[0], source[1]])
    }

    #[inline]
    pub const fn tag(self) -> u32 {
        self.0[RETURN_ORIGIN_TAG]
    }

    #[inline]
    pub const fn source_current(self) -> Option<u64> {
        if self.tag() == RETURN_CONTINUED {
            Some(u64_from_words(
                self.0[RETURN_ORIGIN_SOURCE_CURRENT_LO],
                self.0[RETURN_ORIGIN_SOURCE_CURRENT_HI],
            ))
        } else {
            None
        }
    }

    #[inline]
    pub const fn words(self) -> [u32; RETURN_ORIGIN_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; RETURN_ORIGIN_WORDS]) -> Option<Self> {
        match words[RETURN_ORIGIN_TAG] {
            RETURN_BIRTH
                if words[RETURN_ORIGIN_SOURCE_CURRENT_LO] == 0
                    && words[RETURN_ORIGIN_SOURCE_CURRENT_HI] == 0 =>
            {
                Some(Self(words))
            }
            RETURN_CONTINUED => Some(Self(words)),
            _ => None,
        }
    }
}

/// One sparse causal edge between exact event occurrences in the deed and returned cuts.
/// Incidence ordinals are local to their named receipt cuts and event offsets are local to
/// those incidences. Currents and opaque organ occurrences remain derivable from the mounted
/// cuts. Repeated equal rows remain repeated physical incidence rather than being deduplicated.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct LineageIncidenceRow(pub [u32; LINEAGE_INCIDENCE_WORDS]);

impl LineageIncidenceRow {
    #[inline]
    pub const fn new(
        source_incidence: u64,
        source_event_offset: u64,
        returned_incidence: u64,
        returned_event_offset: u64,
    ) -> Self {
        let source_incidence = u64_words(source_incidence);
        let source_event = u64_words(source_event_offset);
        let returned_incidence = u64_words(returned_incidence);
        let returned_event = u64_words(returned_event_offset);
        Self([
            source_incidence[0],
            source_incidence[1],
            source_event[0],
            source_event[1],
            returned_incidence[0],
            returned_incidence[1],
            returned_event[0],
            returned_event[1],
        ])
    }

    #[inline]
    pub const fn source_incidence(self) -> u64 {
        u64_from_words(
            self.0[LINEAGE_INCIDENCE_SOURCE_INCIDENCE_LO],
            self.0[LINEAGE_INCIDENCE_SOURCE_INCIDENCE_HI],
        )
    }

    #[inline]
    pub const fn source_event_offset(self) -> u64 {
        u64_from_words(
            self.0[LINEAGE_INCIDENCE_SOURCE_EVENT_OFFSET_LO],
            self.0[LINEAGE_INCIDENCE_SOURCE_EVENT_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn returned_incidence(self) -> u64 {
        u64_from_words(
            self.0[LINEAGE_INCIDENCE_RETURNED_INCIDENCE_LO],
            self.0[LINEAGE_INCIDENCE_RETURNED_INCIDENCE_HI],
        )
    }

    #[inline]
    pub const fn returned_event_offset(self) -> u64 {
        u64_from_words(
            self.0[LINEAGE_INCIDENCE_RETURNED_EVENT_OFFSET_LO],
            self.0[LINEAGE_INCIDENCE_RETURNED_EVENT_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn words(self) -> [u32; LINEAGE_INCIDENCE_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; LINEAGE_INCIDENCE_WORDS]) -> Self {
        Self(words)
    }
}

/// Extents for the versioned settlement companion to the historical Holon body. Keeping this
/// as a companion header preserves the existing cut/receipt wire while making silence and
/// exact carrier/event lineage enumerable rather than runtime-only side state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct SettlementHeader(pub [u32; SETTLEMENT_HEADER_WORDS]);

impl SettlementHeader {
    #[inline]
    pub const fn new(
        settlements: u64,
        silent_receipts: u64,
        source_dispositions: u64,
        return_origins: u64,
        lineage_incidences: u64,
    ) -> Option<Self> {
        if silent_receipts > settlements
            || (settlements == 0
                && (silent_receipts != 0
                    || source_dispositions != 0
                    || return_origins != 0
                    || lineage_incidences != 0))
            || (settlements != 0 && source_dispositions == 0)
        {
            return None;
        }
        let settlements = u64_words(settlements);
        let silent = u64_words(silent_receipts);
        let source = u64_words(source_dispositions);
        let origins = u64_words(return_origins);
        let lineages = u64_words(lineage_incidences);
        Some(Self([
            SETTLEMENT_LAYOUT_VERSION,
            settlements[0],
            settlements[1],
            silent[0],
            silent[1],
            source[0],
            source[1],
            origins[0],
            origins[1],
            lineages[0],
            lineages[1],
        ]))
    }

    #[inline]
    pub const fn from_words(words: [u32; SETTLEMENT_HEADER_WORDS]) -> Option<Self> {
        if words[SETTLEMENT_HEADER_VERSION] != SETTLEMENT_LAYOUT_VERSION {
            return None;
        }
        Self::new(
            u64_from_words(
                words[SETTLEMENT_HEADER_SETTLEMENTS_LO],
                words[SETTLEMENT_HEADER_SETTLEMENTS_HI],
            ),
            u64_from_words(
                words[SETTLEMENT_HEADER_SILENT_RECEIPTS_LO],
                words[SETTLEMENT_HEADER_SILENT_RECEIPTS_HI],
            ),
            u64_from_words(
                words[SETTLEMENT_HEADER_SOURCE_DISPOSITIONS_LO],
                words[SETTLEMENT_HEADER_SOURCE_DISPOSITIONS_HI],
            ),
            u64_from_words(
                words[SETTLEMENT_HEADER_RETURN_ORIGINS_LO],
                words[SETTLEMENT_HEADER_RETURN_ORIGINS_HI],
            ),
            u64_from_words(
                words[SETTLEMENT_HEADER_LINEAGE_INCIDENCES_LO],
                words[SETTLEMENT_HEADER_LINEAGE_INCIDENCES_HI],
            ),
        )
    }

    #[inline]
    pub const fn settlements(self) -> u64 {
        u64_from_words(
            self.0[SETTLEMENT_HEADER_SETTLEMENTS_LO],
            self.0[SETTLEMENT_HEADER_SETTLEMENTS_HI],
        )
    }

    #[inline]
    pub const fn silent_receipts(self) -> u64 {
        u64_from_words(
            self.0[SETTLEMENT_HEADER_SILENT_RECEIPTS_LO],
            self.0[SETTLEMENT_HEADER_SILENT_RECEIPTS_HI],
        )
    }

    #[inline]
    pub const fn source_dispositions(self) -> u64 {
        u64_from_words(
            self.0[SETTLEMENT_HEADER_SOURCE_DISPOSITIONS_LO],
            self.0[SETTLEMENT_HEADER_SOURCE_DISPOSITIONS_HI],
        )
    }

    #[inline]
    pub const fn return_origins(self) -> u64 {
        u64_from_words(
            self.0[SETTLEMENT_HEADER_RETURN_ORIGINS_LO],
            self.0[SETTLEMENT_HEADER_RETURN_ORIGINS_HI],
        )
    }

    #[inline]
    pub const fn lineage_incidences(self) -> u64 {
        u64_from_words(
            self.0[SETTLEMENT_HEADER_LINEAGE_INCIDENCES_LO],
            self.0[SETTLEMENT_HEADER_LINEAGE_INCIDENCES_HI],
        )
    }

    #[inline]
    pub const fn words(self) -> [u32; SETTLEMENT_HEADER_WORDS] {
        self.0
    }
}

/// Exact settlement populations belonging to one transition. Receipt ordinals are typed by
/// `kind`; all population spans are append-only and independently bounded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct SettlementSpan(pub [u32; SETTLEMENT_WORDS]);

impl SettlementSpan {
    #[allow(clippy::too_many_arguments)]
    #[inline]
    const fn make(
        transition: u64,
        kind: u32,
        receipt: u64,
        source_offset: u64,
        sources: u64,
        origin_offset: u64,
        origins: u64,
        lineage_offset: u64,
        lineages: u64,
    ) -> Option<Self> {
        if sources == 0
            || !optional_span_is_valid(source_offset, sources)
            || !optional_span_is_valid(origin_offset, origins)
            || !optional_span_is_valid(lineage_offset, lineages)
            || (kind == SETTLEMENT_SILENT && (origins != 0 || lineages != 0))
            || (kind != SETTLEMENT_SILENT && kind != SETTLEMENT_RETURNED)
        {
            return None;
        }
        let transition = u64_words(transition);
        let receipt = u64_words(receipt);
        let source_offset = u64_words(source_offset);
        let sources = u64_words(sources);
        let origin_offset = u64_words(origin_offset);
        let origins = u64_words(origins);
        let lineage_offset = u64_words(lineage_offset);
        let lineages = u64_words(lineages);
        Some(Self([
            transition[0],
            transition[1],
            kind,
            receipt[0],
            receipt[1],
            source_offset[0],
            source_offset[1],
            sources[0],
            sources[1],
            origin_offset[0],
            origin_offset[1],
            origins[0],
            origins[1],
            lineage_offset[0],
            lineage_offset[1],
            lineages[0],
            lineages[1],
        ]))
    }

    #[allow(clippy::too_many_arguments)]
    #[inline]
    pub const fn returned(
        transition: u64,
        receipt: u64,
        source_offset: u64,
        sources: u64,
        origin_offset: u64,
        origins: u64,
        lineage_offset: u64,
        lineages: u64,
    ) -> Option<Self> {
        Self::make(
            transition,
            SETTLEMENT_RETURNED,
            receipt,
            source_offset,
            sources,
            origin_offset,
            origins,
            lineage_offset,
            lineages,
        )
    }

    #[inline]
    pub const fn silent(
        transition: u64,
        receipt: u64,
        source_offset: u64,
        sources: u64,
    ) -> Option<Self> {
        Self::make(
            transition,
            SETTLEMENT_SILENT,
            receipt,
            source_offset,
            sources,
            0,
            0,
            0,
            0,
        )
    }

    #[inline]
    pub const fn transition(self) -> u64 {
        u64_from_words(
            self.0[SETTLEMENT_TRANSITION_LO],
            self.0[SETTLEMENT_TRANSITION_HI],
        )
    }

    #[inline]
    pub const fn kind(self) -> u32 {
        self.0[SETTLEMENT_KIND]
    }

    #[inline]
    pub const fn receipt(self) -> u64 {
        u64_from_words(self.0[SETTLEMENT_RECEIPT_LO], self.0[SETTLEMENT_RECEIPT_HI])
    }

    #[inline]
    pub const fn source_offset(self) -> u64 {
        u64_from_words(
            self.0[SETTLEMENT_SOURCE_OFFSET_LO],
            self.0[SETTLEMENT_SOURCE_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn sources(self) -> u64 {
        u64_from_words(self.0[SETTLEMENT_SOURCES_LO], self.0[SETTLEMENT_SOURCES_HI])
    }

    #[inline]
    pub const fn origin_offset(self) -> u64 {
        u64_from_words(
            self.0[SETTLEMENT_ORIGIN_OFFSET_LO],
            self.0[SETTLEMENT_ORIGIN_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn origins(self) -> u64 {
        u64_from_words(self.0[SETTLEMENT_ORIGINS_LO], self.0[SETTLEMENT_ORIGINS_HI])
    }

    #[inline]
    pub const fn lineage_offset(self) -> u64 {
        u64_from_words(
            self.0[SETTLEMENT_LINEAGE_OFFSET_LO],
            self.0[SETTLEMENT_LINEAGE_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn lineages(self) -> u64 {
        u64_from_words(
            self.0[SETTLEMENT_LINEAGES_LO],
            self.0[SETTLEMENT_LINEAGES_HI],
        )
    }

    #[inline]
    pub const fn words(self) -> [u32; SETTLEMENT_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; SETTLEMENT_WORDS]) -> Option<Self> {
        Self::make(
            u64_from_words(
                words[SETTLEMENT_TRANSITION_LO],
                words[SETTLEMENT_TRANSITION_HI],
            ),
            words[SETTLEMENT_KIND],
            u64_from_words(words[SETTLEMENT_RECEIPT_LO], words[SETTLEMENT_RECEIPT_HI]),
            u64_from_words(
                words[SETTLEMENT_SOURCE_OFFSET_LO],
                words[SETTLEMENT_SOURCE_OFFSET_HI],
            ),
            u64_from_words(words[SETTLEMENT_SOURCES_LO], words[SETTLEMENT_SOURCES_HI]),
            u64_from_words(
                words[SETTLEMENT_ORIGIN_OFFSET_LO],
                words[SETTLEMENT_ORIGIN_OFFSET_HI],
            ),
            u64_from_words(words[SETTLEMENT_ORIGINS_LO], words[SETTLEMENT_ORIGINS_HI]),
            u64_from_words(
                words[SETTLEMENT_LINEAGE_OFFSET_LO],
                words[SETTLEMENT_LINEAGE_OFFSET_HI],
            ),
            u64_from_words(words[SETTLEMENT_LINEAGES_LO], words[SETTLEMENT_LINEAGES_HI]),
        )
    }
}

/// One complete ordered return lifecycle.  Every role names a boundary cut rather than a
/// universal deed enum or world object.  Exact zero residual is lawful and canonically uses
/// offset zero, extent zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct TransitionReceipt(pub [u32; RECEIPT_WORDS]);

impl TransitionReceipt {
    #[allow(clippy::too_many_arguments)]
    #[inline]
    pub const fn new(
        before_cut: u64,
        meeting_cut: u64,
        deed_cut: u64,
        consequence_cut: u64,
        return_cut: u64,
        after_cut: u64,
        residual_incidence_offset: u64,
        residual_incidences: u64,
    ) -> Option<Self> {
        if !optional_span_is_valid(residual_incidence_offset, residual_incidences) {
            return None;
        }
        let before = u64_words(before_cut);
        let meeting = u64_words(meeting_cut);
        let deed = u64_words(deed_cut);
        let consequence = u64_words(consequence_cut);
        let returned = u64_words(return_cut);
        let after = u64_words(after_cut);
        let residual_offset = u64_words(residual_incidence_offset);
        let residuals = u64_words(residual_incidences);
        Some(Self([
            before[0],
            before[1],
            meeting[0],
            meeting[1],
            deed[0],
            deed[1],
            consequence[0],
            consequence[1],
            returned[0],
            returned[1],
            after[0],
            after[1],
            residual_offset[0],
            residual_offset[1],
            residuals[0],
            residuals[1],
        ]))
    }

    #[inline]
    const fn cut_at(self, lo: usize, hi: usize) -> u64 {
        u64_from_words(self.0[lo], self.0[hi])
    }

    #[inline]
    pub const fn before_cut(self) -> u64 {
        self.cut_at(RECEIPT_BEFORE_CUT_LO, RECEIPT_BEFORE_CUT_HI)
    }

    #[inline]
    pub const fn meeting_cut(self) -> u64 {
        self.cut_at(RECEIPT_MEETING_CUT_LO, RECEIPT_MEETING_CUT_HI)
    }

    #[inline]
    pub const fn deed_cut(self) -> u64 {
        self.cut_at(RECEIPT_DEED_CUT_LO, RECEIPT_DEED_CUT_HI)
    }

    #[inline]
    pub const fn consequence_cut(self) -> u64 {
        self.cut_at(RECEIPT_CONSEQUENCE_CUT_LO, RECEIPT_CONSEQUENCE_CUT_HI)
    }

    #[inline]
    pub const fn return_cut(self) -> u64 {
        self.cut_at(RECEIPT_RETURN_CUT_LO, RECEIPT_RETURN_CUT_HI)
    }

    #[inline]
    pub const fn after_cut(self) -> u64 {
        self.cut_at(RECEIPT_AFTER_CUT_LO, RECEIPT_AFTER_CUT_HI)
    }

    #[inline]
    pub const fn residual_incidence_offset(self) -> u64 {
        u64_from_words(
            self.0[RECEIPT_RESIDUAL_INCIDENCE_OFFSET_LO],
            self.0[RECEIPT_RESIDUAL_INCIDENCE_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn residual_incidences(self) -> u64 {
        u64_from_words(
            self.0[RECEIPT_RESIDUAL_INCIDENCES_LO],
            self.0[RECEIPT_RESIDUAL_INCIDENCES_HI],
        )
    }

    #[inline]
    pub const fn words(self) -> [u32; RECEIPT_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; RECEIPT_WORDS]) -> Option<Self> {
        Self::new(
            u64_from_words(words[RECEIPT_BEFORE_CUT_LO], words[RECEIPT_BEFORE_CUT_HI]),
            u64_from_words(words[RECEIPT_MEETING_CUT_LO], words[RECEIPT_MEETING_CUT_HI]),
            u64_from_words(words[RECEIPT_DEED_CUT_LO], words[RECEIPT_DEED_CUT_HI]),
            u64_from_words(
                words[RECEIPT_CONSEQUENCE_CUT_LO],
                words[RECEIPT_CONSEQUENCE_CUT_HI],
            ),
            u64_from_words(words[RECEIPT_RETURN_CUT_LO], words[RECEIPT_RETURN_CUT_HI]),
            u64_from_words(words[RECEIPT_AFTER_CUT_LO], words[RECEIPT_AFTER_CUT_HI]),
            u64_from_words(
                words[RECEIPT_RESIDUAL_INCIDENCE_OFFSET_LO],
                words[RECEIPT_RESIDUAL_INCIDENCE_OFFSET_HI],
            ),
            u64_from_words(
                words[RECEIPT_RESIDUAL_INCIDENCES_LO],
                words[RECEIPT_RESIDUAL_INCIDENCES_HI],
            ),
        )
    }
}

/// One terminal contact with no world-side actuation. The source relation genuinely lived,
/// so before, meeting, deed, and the post-deed receiver all remain exact. Consequence and
/// return are absent rather than represented by sentinel cuts. Residual incidence remains
/// addressable exactly as it does for a complete returned transition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct SilentReceipt(pub [u32; SILENT_RECEIPT_WORDS]);

impl SilentReceipt {
    #[inline]
    pub const fn new(
        before_cut: u64,
        meeting_cut: u64,
        deed_cut: u64,
        after_cut: u64,
        residual_incidence_offset: u64,
        residual_incidences: u64,
    ) -> Option<Self> {
        if !optional_span_is_valid(residual_incidence_offset, residual_incidences) {
            return None;
        }
        let before = u64_words(before_cut);
        let meeting = u64_words(meeting_cut);
        let deed = u64_words(deed_cut);
        let after = u64_words(after_cut);
        let residual_offset = u64_words(residual_incidence_offset);
        let residuals = u64_words(residual_incidences);
        Some(Self([
            before[0],
            before[1],
            meeting[0],
            meeting[1],
            deed[0],
            deed[1],
            after[0],
            after[1],
            residual_offset[0],
            residual_offset[1],
            residuals[0],
            residuals[1],
        ]))
    }

    #[inline]
    const fn cut_at(self, lo: usize, hi: usize) -> u64 {
        u64_from_words(self.0[lo], self.0[hi])
    }

    #[inline]
    pub const fn before_cut(self) -> u64 {
        self.cut_at(SILENT_RECEIPT_BEFORE_CUT_LO, SILENT_RECEIPT_BEFORE_CUT_HI)
    }

    #[inline]
    pub const fn meeting_cut(self) -> u64 {
        self.cut_at(SILENT_RECEIPT_MEETING_CUT_LO, SILENT_RECEIPT_MEETING_CUT_HI)
    }

    #[inline]
    pub const fn deed_cut(self) -> u64 {
        self.cut_at(SILENT_RECEIPT_DEED_CUT_LO, SILENT_RECEIPT_DEED_CUT_HI)
    }

    #[inline]
    pub const fn after_cut(self) -> u64 {
        self.cut_at(SILENT_RECEIPT_AFTER_CUT_LO, SILENT_RECEIPT_AFTER_CUT_HI)
    }

    #[inline]
    pub const fn residual_incidence_offset(self) -> u64 {
        u64_from_words(
            self.0[SILENT_RECEIPT_RESIDUAL_INCIDENCE_OFFSET_LO],
            self.0[SILENT_RECEIPT_RESIDUAL_INCIDENCE_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn residual_incidences(self) -> u64 {
        u64_from_words(
            self.0[SILENT_RECEIPT_RESIDUAL_INCIDENCES_LO],
            self.0[SILENT_RECEIPT_RESIDUAL_INCIDENCES_HI],
        )
    }

    #[inline]
    pub const fn words(self) -> [u32; SILENT_RECEIPT_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; SILENT_RECEIPT_WORDS]) -> Option<Self> {
        Self::new(
            u64_from_words(
                words[SILENT_RECEIPT_BEFORE_CUT_LO],
                words[SILENT_RECEIPT_BEFORE_CUT_HI],
            ),
            u64_from_words(
                words[SILENT_RECEIPT_MEETING_CUT_LO],
                words[SILENT_RECEIPT_MEETING_CUT_HI],
            ),
            u64_from_words(
                words[SILENT_RECEIPT_DEED_CUT_LO],
                words[SILENT_RECEIPT_DEED_CUT_HI],
            ),
            u64_from_words(
                words[SILENT_RECEIPT_AFTER_CUT_LO],
                words[SILENT_RECEIPT_AFTER_CUT_HI],
            ),
            u64_from_words(
                words[SILENT_RECEIPT_RESIDUAL_INCIDENCE_OFFSET_LO],
                words[SILENT_RECEIPT_RESIDUAL_INCIDENCE_OFFSET_HI],
            ),
            u64_from_words(
                words[SILENT_RECEIPT_RESIDUAL_INCIDENCES_LO],
                words[SILENT_RECEIPT_RESIDUAL_INCIDENCES_HI],
            ),
        )
    }
}
