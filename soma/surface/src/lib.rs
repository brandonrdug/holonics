//! surface — the M4 felt-series card boundary. `FeltSurface` carries first-person raw-light
//! lineages into disjoint OWN/carrier regions, then mounts the ratified configuration product:
//! whole-Rung grain declaration, exact wide sum, and one final re-base after the light's true end.
//! The older `Surface` API remains quarantined whole; none of its entry names map onto this module.

pub use wgpu;

/// The bounded mirror returned by one fresh card composition. Standing and every OWN plane cross
/// only so the cpu/card causal gate can compare them byte-exact; the four-word `reads` projection
/// is the production-facing topology mouth (occupied ⊕ resultant ⊕ fiber ⊕ two-armed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FeltCardRead {
    pub standing: Vec<u32>,
    pub owns: Vec<u32>,
    pub cog_grains: Vec<u64>,
    pub arm_grains: Vec<u32>,
    pub cog_sums: Vec<u64>,
    pub arm_sums: Vec<u64>,
    pub touched: Vec<u32>,
    pub reads: [u64; 4],
}

/// One raw-light lineage mounted at the card boundary. The two-byte frame seed is construction,
/// not an identity label: its first difference founds K's positional gauge.
pub struct FeltLineageInput<'a> {
    pub light: &'a [u8],
    pub frame_seed: [u8; 2],
}

/// One lineage whose first-person regional chart has its own boundary reservation. `own_axis²`
/// founded cells are concatenated with the other lineages' charts; no lane receives a standing-sized
/// plane. The axis is a membrane-declared species face, not a mechanism tolerance.
pub struct FoundedLineageInput<'a> {
    pub light: &'a [u8],
    pub frame_seed: [u8; 2],
    pub own_axis: u32,
}

/// A bounded readback of the still-separated first-person regions. `counts` is four u64 words per
/// lane: ride ⊕ found-this ⊕ found-that ⊕ dark. Standing is included to pin its immutability before
/// the true light-end composition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FeltScopeRead {
    pub standing: Vec<u32>,
    pub owns: Vec<u32>,
    pub carriers: Vec<u32>,
    pub counts: Vec<u64>,
}

/// Resident M4b media. OWN and carrier are disjoint lane-major regions; the raw lights, their
/// two-byte founding frames, and the immutable pre-light standing remain mounted across strokes.
pub struct FeltLineageMount {
    standing: wgpu::Buffer,
    owns: wgpu::Buffer,
    carriers: wgpu::Buffer,
    _bytes: wgpu::Buffer,
    _lanes_buffer: wgpu::Buffer,
    counts: wgpu::Buffer,
    scope_params: wgpu::Buffer,
    scope_group: wgpu::BindGroup,
    cells: usize,
    lanes: usize,
    standing_words: usize,
    own_words: usize,
    carrier_words: usize,
    worldline_light_ends: Vec<u64>,
}

/// M5 resident media. Each lane row points into one concatenated buffer of differently sized
/// founded charts. Cells carry their founding construction, so the receiving edge re-grounds them
/// without a key, sparse map, allocation event, replay, sort, or search.
pub struct FoundedLineageMount {
    standing: wgpu::Buffer,
    owns: wgpu::Buffer,
    carriers: wgpu::Buffer,
    _bytes: wgpu::Buffer,
    _lanes_buffer: wgpu::Buffer,
    counts: wgpu::Buffer,
    radiation: wgpu::Buffer,
    scope_params: wgpu::Buffer,
    scope_group: wgpu::BindGroup,
    standing_axis: u32,
    cells: usize,
    own_cells: usize,
    lanes: usize,
    standing_words: usize,
    own_words: usize,
    carrier_words: usize,
    radiation_words: usize,
    radiation_stride: u32,
    own_axes: Vec<u32>,
    worldline_light_ends: Vec<u64>,
    light_bytes: u64,
    /// The receiving chart's monotone OWN register. It changes only at a true receiving edge.
    occupancy: u64,
}

const SLEEP_MAGIC: [u32; 2] = [u32::from_le_bytes(*b"SOMA"), u32::from_le_bytes(*b"REST")];
const SLEEP_DENSE_VERSION: u32 = 2;
const SLEEP_OCCUPIED_VERSION: u32 = 3;
const SLEEP_COMPACT_VERSION: u32 = 4;
const SLEEP_AXES_VERSION: u32 = 5;
const SLEEP_NO_AXES_VERSION: u32 = 6;
const SLEEP_UNIFORM_CARRIER_VERSION: u32 = 7;
const SLEEP_VARIABLE_CARRIER_VERSION: u32 = 8;
pub const SLEEP_LAYOUT_VERSION: u32 = 9;
const SLEEP_VERSION: u32 = SLEEP_LAYOUT_VERSION;
const SLEEP_V2_V8_HEADER_WORDS: usize = 14;
const SLEEP_HEADER_WORDS: usize = 16;
// Historical widths are part of their archive versions. They must never follow the active runtime
// row when FORM_WORDS or the carrier tail changes.
const SLEEP_V2_FORM_WORDS: usize = 17;
const SLEEP_V3_RECORD_WORDS: usize = 18;
const SLEEP_V4_FORM_WORDS: usize = 11;
const SLEEP_RECORD_WORDS: usize = 12;

struct ArchiveComparator<R> {
    reader: R,
}

impl<R: std::io::Read> std::io::Write for ArchiveComparator<R> {
    fn write(&mut self, expected: &[u8]) -> std::io::Result<usize> {
        let mut compared = 0usize;
        let mut actual = [0u8; 4096];
        while compared < expected.len() {
            let extent = actual.len().min(expected.len() - compared);
            self.reader.read_exact(&mut actual[..extent])?;
            if actual[..extent] != expected[compared..compared + extent] {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "the SLEEP/read seam changed the canonical body wire",
                ));
            }
            compared += extent;
        }
        Ok(expected.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl<R: std::io::Read> ArchiveComparator<R> {
    fn finish(mut self) -> std::io::Result<()> {
        let mut trailing = [0u8; 1];
        if self.reader.read(&mut trailing)? != 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "the SLEEP archive ends at its declared body boundary",
            ));
        }
        Ok(())
    }
}
const SLEEP_V2_V4_CARRIER_HEADER_WORDS: usize = 72;
const SLEEP_V2_V4_CARRIER_DEPTH_WORDS: usize = 290;
const SLEEP_V5_V6_CONTINUATION_WORDS: usize = 19;
const _: [(); SLEEP_V2_FORM_WORDS] = [(); body::medium::LEGACY_FORM_WORDS];
const _: [(); SLEEP_V4_FORM_WORDS] = [(); body::medium::COMPACT_FORM_WORDS];
const _: [(); SLEEP_V2_V4_CARRIER_HEADER_WORDS] = [(); body::manifold::CARRIER_HEADER_WORDS];
const _: [(); SLEEP_V2_V4_CARRIER_DEPTH_WORDS] =
    [(); body::manifold::ENCLOSURE_WORDS + body::manifold::CARRIER_DEFERRED_WORDS];
const _: [(); SLEEP_V5_V6_CONTINUATION_WORDS] = [(); body::manifold::CARRIER_CONTINUATION_WORDS];

fn historical_carrier_row_words(depth: usize) -> Option<usize> {
    depth
        .checked_mul(SLEEP_V2_V4_CARRIER_DEPTH_WORDS)
        .and_then(|words| words.checked_add(SLEEP_V2_V4_CARRIER_HEADER_WORDS))
}

fn historical_carrier_row_depth(words: usize) -> Option<usize> {
    let carried = words.checked_sub(SLEEP_V2_V4_CARRIER_HEADER_WORDS)?;
    if carried == 0 || carried % SLEEP_V2_V4_CARRIER_DEPTH_WORDS != 0 {
        return None;
    }
    let depth = carried / SLEEP_V2_V4_CARRIER_DEPTH_WORDS;
    (historical_carrier_row_words(depth) == Some(words)).then_some(depth)
}

fn v5_v6_carrier_row_words(depth: usize) -> Option<usize> {
    historical_carrier_row_words(depth)
        .and_then(|words| words.checked_add(SLEEP_V5_V6_CONTINUATION_WORDS))
}

/// V5/V6 predate the pending-deed tail. Their depth must be read against their own literal
/// `72 + 290d + 19` row; asking the active helper would silently infer one fewer enclosure after
/// the active row grows.
fn v5_v6_carrier_row_depth(words: usize) -> Option<usize> {
    let prefix = words.checked_sub(SLEEP_V5_V6_CONTINUATION_WORDS)?;
    let depth = historical_carrier_row_depth(prefix)?;
    (v5_v6_carrier_row_words(depth) == Some(words)).then_some(depth)
}

#[derive(Clone, Copy)]
enum SleepCarrierWire {
    V2V4,
    V5V6,
    UniformActive,
    VariableActive,
}

/// One observed chart edge. `carries` counts the chart digits forced by this one arriving light;
/// `occupancy` is the accepted post-edge register face. The topology projection is an aperture,
/// never state consumed by the engine.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChartEdgeRead {
    pub prior_axis: u32,
    pub standing_axis: u32,
    pub carries: u32,
    pub occupancy: u64,
    pub topology: [u64; 4],
}

/// One whole founded body at its receiving edge. The standing medium and every complete carrier
/// row (including K) are the identity-bearing construction. The structural lineage count and row
/// extent frame those carriers; light-local chart axes, OWN, counts, raw light, and radiation do
/// not cross the sleep seam.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SleepingBody {
    standing_axis: u32,
    occupancy: u64,
    /// One exact complete carrier/K row extent per lineage. This is structural framing for the
    /// concatenated carrier words, never body topology or a current-visible address.
    carrier_row_words: Vec<u32>,
    lineage_count: u32,
    standing: Vec<u32>,
    carriers: Vec<u32>,
    comprehended_light_bytes: u64,
}

/// The exact receiving body before its complete at-rest carrier rows are materialized. This is a
/// SLEEP-mouth frame, not a reduced body: every row extent and the full identity byte measure are
/// present, while the rows themselves may cross the archive from a bounded streaming source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SleepingBodyFrame {
    standing_axis: u32,
    occupancy: u64,
    carrier_row_words: Vec<u32>,
    standing: Vec<u32>,
    comprehended_light_bytes: u64,
    carrier_words: u64,
}

pub struct SleepingBodyArchiveWriter<'a> {
    frame: &'a SleepingBodyFrame,
    writer: std::io::BufWriter<std::fs::File>,
    next_row: usize,
}

impl SleepingBody {
    fn invalid_archive(message: impl Into<String>) -> std::io::Error {
        std::io::Error::new(std::io::ErrorKind::InvalidData, message.into())
    }

    fn read_words(reader: &mut impl std::io::Read, words: &mut [u32]) -> std::io::Result<()> {
        reader.read_exact(bytemuck::cast_slice_mut(words))?;
        #[cfg(target_endian = "big")]
        for word in words {
            *word = u32::from_le(*word);
        }
        Ok(())
    }

    fn zeroed_words(extent: usize, face: &'static str) -> std::io::Result<Vec<u32>> {
        let mut words = Vec::new();
        words
            .try_reserve_exact(extent)
            .map_err(|_| Self::invalid_archive(format!("this boundary can mount the {face}")))?;
        words.resize(extent, 0);
        Ok(words)
    }

    /// Assemble one whole body at its receiving edge. Every producer crosses this mouth so the
    /// archive encoder never needs a second layout or an unchecked field path.
    pub fn from_parts(
        standing_axis: u32,
        occupancy: u64,
        carrier_row_words: u32,
        lineage_count: u32,
        standing: Vec<u32>,
        carriers: Vec<u32>,
        comprehended_light_bytes: u64,
    ) -> Result<Self, String> {
        let row_words = vec![carrier_row_words; lineage_count as usize];
        Self::from_variable_parts(
            standing_axis,
            occupancy,
            row_words,
            standing,
            carriers,
            comprehended_light_bytes,
        )
    }

    /// Assemble one whole body whose complete carrier rows have independent structural extents.
    /// Row framing belongs to the sleep/container mouth; the concatenated canonical rows remain
    /// the identity-bearing construction.
    pub fn from_variable_parts(
        standing_axis: u32,
        occupancy: u64,
        carrier_row_words: Vec<u32>,
        standing: Vec<u32>,
        carriers: Vec<u32>,
        comprehended_light_bytes: u64,
    ) -> Result<Self, String> {
        let lineage_count = u32::try_from(carrier_row_words.len())
            .map_err(|_| "the structural lineage count fits its archive mouth".to_string())?;
        let body = Self {
            standing_axis,
            occupancy,
            carrier_row_words,
            lineage_count,
            standing,
            carriers,
            comprehended_light_bytes,
        };
        body.validate()?;
        Ok(body)
    }

    /// Assemble parts which have already crossed this module's complete current-archive read.
    /// This remains private: external producers must enter through the validating constructors.
    fn from_checked_parts(
        standing_axis: u32,
        occupancy: u64,
        carrier_row_words: Vec<u32>,
        standing: Vec<u32>,
        carriers: Vec<u32>,
        comprehended_light_bytes: u64,
    ) -> SleepingBody {
        SleepingBody {
            standing_axis,
            occupancy,
            lineage_count: carrier_row_words.len() as u32,
            carrier_row_words,
            standing,
            carriers,
            comprehended_light_bytes,
        }
    }

    fn validate_carrier_parts(carrier_row_words: &[u32], carriers: &[u32]) -> Result<(), String> {
        let carrier_words = carrier_row_words.iter().try_fold(0usize, |sum, &words| {
            let row_words = words as usize;
            let depth = body::manifold::carrier_row_depth(row_words);
            if depth == 0 || body::manifold::carrier_row_words(depth) != row_words {
                return Err(
                    "the sleeping body carries complete reservation-derived carrier rows"
                        .to_string(),
                );
            }
            sum.checked_add(row_words)
                .ok_or_else(|| "the sleeping carrier extent is representable".to_string())
        })?;
        if carriers.len() != carrier_words {
            return Err("the sleeping body carries one whole carrier/K row per lineage".into());
        }
        let mut at = 0usize;
        for &row_words in carrier_row_words {
            let end = at + row_words as usize;
            let row = &carriers[at..end];
            if !body::manifold::carried_frame_is_at_rest(row) {
                return Err(
                    "the sleeping body carries canonical complete carrier/K constructions at rest"
                        .into(),
                );
            }
            let cursor = row[body::manifold::CARRIER_CURSOR_LO] as u64
                | ((row[body::manifold::CARRIER_CURSOR_HI] as u64) << 32);
            let dark = row[body::manifold::CARRIER_DARK_LO] as u64
                | ((row[body::manifold::CARRIER_DARK_HI] as u64) << 32);
            if cursor < 2 {
                return Err("a sleeping lineage carries its crossed predecessor".into());
            }
            if dark != 0 {
                return Err(
                    "the sleeping receiving edge carries no unfinished dark passage".into(),
                );
            }
            at = end;
        }
        Ok(())
    }

    fn validate_frame_parts(
        standing_axis: u32,
        occupancy: u64,
        carrier_row_words: &[u32],
        standing: &[u32],
        comprehended_light_bytes: u64,
    ) -> Result<u64, String> {
        if standing_axis == 0 || standing_axis & (standing_axis - 1) != 0 {
            return Err("the sleeping body has one positive dyadic standing axis".into());
        }
        if carrier_row_words.is_empty() {
            return Err("the sleeping body carries one positive structural lineage count".into());
        }
        u32::try_from(carrier_row_words.len())
            .map_err(|_| "the structural lineage count fits its archive mouth".to_string())?;
        let standing_cells = (standing_axis as usize)
            .checked_mul(standing_axis as usize)
            .ok_or_else(|| "the sleeping standing extent is representable".to_string())?;
        let standing_words = standing_cells
            .checked_mul(body::medium::FORM_WORDS)
            .ok_or_else(|| "the sleeping standing word extent is representable".to_string())?;
        if standing.len() != standing_words {
            return Err("the sleeping body carries one whole form per standing place".into());
        }
        let mut occupied = 0u64;
        for (grip, words) in standing.chunks_exact(body::medium::FORM_WORDS).enumerate() {
            let form =
                body::medium::RegionalForm::unpack_compact_checked(words, 0).map_err(|_| {
                    "the sleeping body carries checked canonical regional forms".to_string()
                })?;
            let mut canonical = [0u32; body::medium::FORM_WORDS];
            form.pack(&mut canonical, 0);
            if canonical.as_slice() != words {
                return Err("the sleeping body carries canonical regional forms".into());
            }
            if form.occupied() {
                u32::try_from(grip)
                    .map_err(|_| "an occupied standing grip fits its archive mouth".to_string())?;
                occupied = occupied
                    .checked_add(1)
                    .ok_or_else(|| "the sleeping occupancy is representable".to_string())?;
            }
        }
        if occupied != occupancy {
            return Err("the sleeping chart register names exactly its founded grips".into());
        }
        occupancy
            .checked_mul(SLEEP_RECORD_WORDS as u64)
            .ok_or_else(|| "the occupied standing extent is representable".to_string())?;
        let carrier_words = carrier_row_words.iter().try_fold(0u64, |sum, &words| {
            let row_words = words as usize;
            let depth = body::manifold::carrier_row_depth(row_words);
            if depth == 0 || body::manifold::carrier_row_words(depth) != row_words {
                return Err(
                    "the sleeping body carries complete reservation-derived carrier rows"
                        .to_string(),
                );
            }
            sum.checked_add(words as u64)
                .ok_or_else(|| "the sleeping carrier extent is representable".to_string())
        })?;
        if comprehended_light_bytes == 0 {
            return Err("a sleeping body has crossed one positive world-delivered light".into());
        }
        Ok(carrier_words)
    }

    fn validate_carrier_row(row: &[u32]) -> Result<(), String> {
        if !body::manifold::carried_frame_is_at_rest(row) {
            return Err(
                "the sleeping body carries canonical complete carrier/K constructions at rest"
                    .into(),
            );
        }
        let cursor = row[body::manifold::CARRIER_CURSOR_LO] as u64
            | ((row[body::manifold::CARRIER_CURSOR_HI] as u64) << 32);
        let dark = row[body::manifold::CARRIER_DARK_LO] as u64
            | ((row[body::manifold::CARRIER_DARK_HI] as u64) << 32);
        if cursor < 2 {
            return Err("a sleeping lineage carries its crossed predecessor".into());
        }
        if dark != 0 {
            return Err("the sleeping receiving edge carries no unfinished dark passage".into());
        }
        Ok(())
    }

    fn validate(&self) -> Result<(), String> {
        if self.carrier_row_words.len() != self.lineage_count() {
            return Err("the sleeping body frames one carrier row per lineage".into());
        }
        let carrier_words = Self::validate_frame_parts(
            self.standing_axis,
            self.occupancy,
            &self.carrier_row_words,
            &self.standing,
            self.comprehended_light_bytes,
        )?;
        if carrier_words != self.carriers.len() as u64 {
            return Err("the sleeping body carries one whole carrier/K row per lineage".into());
        }
        Self::validate_carrier_parts(&self.carrier_row_words, &self.carriers)?;
        Ok(())
    }

    pub fn standing_axis(&self) -> u32 {
        self.standing_axis
    }

    /// The common row extent used by historical and bounded uniform-row mouths. Mixed-row bodies
    /// deliberately have no such scalar face.
    pub fn uniform_carrier_row_words(&self) -> Option<usize> {
        let first = *self.carrier_row_words.first()?;
        self.carrier_row_words
            .iter()
            .all(|words| *words == first)
            .then_some(first as usize)
    }

    pub fn carrier_row_words(&self) -> usize {
        self.uniform_carrier_row_words()
            .expect("this bounded mouth requires one uniform carrier row extent")
    }

    pub fn carrier_row_word_extents(&self) -> &[u32] {
        &self.carrier_row_words
    }

    pub fn carrier_rows(&self) -> impl ExactSizeIterator<Item = &[u32]> + '_ {
        let mut at = 0usize;
        self.carrier_row_words.iter().map(move |&words| {
            let start = at;
            at += words as usize;
            &self.carriers[start..at]
        })
    }

    pub fn occupancy(&self) -> u64 {
        self.occupancy
    }

    pub fn lineage_count(&self) -> usize {
        self.lineage_count as usize
    }

    pub fn standing(&self) -> &[u32] {
        &self.standing
    }

    pub fn carriers(&self) -> &[u32] {
        &self.carriers
    }

    pub fn comprehended_light_bytes(&self) -> u64 {
        self.comprehended_light_bytes
    }

    /// Consume a fully checked body at the genuinely-new-light mouth and retain only the face a
    /// new lineage can receive. Complete ended carriers crossed SLEEP as identity and dissipate
    /// here; they are never reassigned to the new currents.
    pub fn into_receiving_parts(self) -> (u32, u64, Vec<u32>, u64) {
        (
            self.standing_axis,
            self.occupancy,
            self.standing,
            self.comprehended_light_bytes,
        )
    }

    /// The identity-bearing body at one declared sleep version: standing records ⊕ complete
    /// carrier/K rows ⊕ the chart register. Archive framing remains outside this measure. V2's
    /// historical wire was dense; V3 onward carry occupied records at their fixed version widths.
    pub fn body_bytes_for_version(&self, version: u32) -> Result<u64, String> {
        let word_bytes = core::mem::size_of::<u32>() as u64;
        let uniform_depth = self
            .uniform_carrier_row_words()
            .map(body::manifold::carrier_row_depth);
        let historical_carrier_words = uniform_depth
            .and_then(historical_carrier_row_words)
            .and_then(|row| row.checked_mul(self.lineage_count()))
            .and_then(|words| u64::try_from(words).ok());
        let v5_v6_carrier_words = uniform_depth
            .and_then(v5_v6_carrier_row_words)
            .and_then(|row| row.checked_mul(self.lineage_count()))
            .and_then(|words| u64::try_from(words).ok());
        let active_carrier_words = u64::try_from(self.carriers.len()).ok();
        let uniform_active_carrier_words = self
            .uniform_carrier_row_words()
            .and_then(|_| active_carrier_words);
        let (standing_words, carrier_words) = match version {
            SLEEP_DENSE_VERSION => (
                (self.standing_axis as u64)
                    .checked_mul(self.standing_axis as u64)
                    .and_then(|cells| cells.checked_mul(SLEEP_V2_FORM_WORDS as u64)),
                historical_carrier_words,
            ),
            SLEEP_OCCUPIED_VERSION => (
                self.occupancy.checked_mul(SLEEP_V3_RECORD_WORDS as u64),
                historical_carrier_words,
            ),
            SLEEP_COMPACT_VERSION => (
                self.occupancy.checked_mul(SLEEP_RECORD_WORDS as u64),
                historical_carrier_words,
            ),
            SLEEP_AXES_VERSION | SLEEP_NO_AXES_VERSION => (
                self.occupancy.checked_mul(SLEEP_RECORD_WORDS as u64),
                v5_v6_carrier_words,
            ),
            SLEEP_UNIFORM_CARRIER_VERSION => (
                self.occupancy.checked_mul(SLEEP_RECORD_WORDS as u64),
                uniform_active_carrier_words,
            ),
            SLEEP_VARIABLE_CARRIER_VERSION | SLEEP_VERSION => (
                self.occupancy.checked_mul(SLEEP_RECORD_WORDS as u64),
                active_carrier_words,
            ),
            _ => return Err("the body-byte read declares a supported sleep version".into()),
        };
        let standing_words = standing_words.ok_or_else(|| {
            "the declared sleep version has a representable standing extent".to_string()
        })?;
        let carrier_words = carrier_words.ok_or_else(|| {
            "the declared sleep version has a representable carrier extent".to_string()
        })?;
        let standing = standing_words.checked_mul(word_bytes).ok_or_else(|| {
            "the declared sleep version has a representable standing byte extent".to_string()
        })?;
        let carriers = carrier_words.checked_mul(word_bytes).ok_or_else(|| {
            "a validated sleeping body's carriers have a representable extent".to_string()
        })?;
        standing
            .checked_add(carriers)
            .and_then(|bytes| bytes.checked_add(core::mem::size_of::<u64>() as u64))
            .ok_or_else(|| {
                "a validated sleeping body has a representable identity extent".to_string()
            })
    }

    /// The current create-new wire's identity-bearing extent.
    pub fn body_bytes(&self) -> u64 {
        self.body_bytes_for_version(SLEEP_VERSION)
            .expect("a validated sleeping body's current-version extent is representable")
    }

    fn compact_standing_words(&self) -> usize {
        usize::try_from(self.occupancy)
            .ok()
            .and_then(|occupied| occupied.checked_mul(SLEEP_RECORD_WORDS))
            .expect(
                "a validated sleeping body's occupied forms have a representable compact extent",
            )
    }

    fn archive_words(&self) -> usize {
        SLEEP_HEADER_WORDS
            .checked_add(self.compact_standing_words())
            .and_then(|words| words.checked_add(self.carrier_row_words.len()))
            .and_then(|words| words.checked_add(self.carriers.len()))
            .expect("a validated sleep archive extent is representable")
    }

    fn write_words(writer: &mut impl std::io::Write, words: &[u32]) -> std::io::Result<()> {
        #[cfg(target_endian = "little")]
        {
            writer.write_all(bytemuck::cast_slice(words))
        }
        #[cfg(target_endian = "big")]
        {
            for word in words {
                writer.write_all(&word.to_le_bytes())?;
            }
            Ok(())
        }
    }

    /// Stream the current create-new archive directly to a writer. No complete word or octet copy
    /// stands beside the body; `encode` below is only the bounded in-memory convenience.
    fn write_archive(&self, writer: &mut impl std::io::Write) -> std::io::Result<usize> {
        // SleepingBody's private fields and validating constructors make canonicality a type
        // invariant. Keep the expensive whole-body audit in debug gates; repeating it before
        // every production serialization would rescan the body after its receiving-edge check.
        debug_assert!(self.validate().is_ok());
        let standing_words = self.compact_standing_words();
        let carrier_words = self.carriers.len() as u64;
        let standing_words = standing_words as u64;
        let header = [
            SLEEP_MAGIC[0],
            SLEEP_MAGIC[1],
            SLEEP_VERSION,
            SLEEP_HEADER_WORDS as u32,
            self.standing_axis,
            self.lineage_count,
            u32::try_from(self.carrier_row_words.len())
                .expect("a validated carrier framing extent fits the archive mouth"),
            standing_words as u32,
            (standing_words >> 32) as u32,
            carrier_words as u32,
            (carrier_words >> 32) as u32,
            self.comprehended_light_bytes as u32,
            (self.comprehended_light_bytes >> 32) as u32,
            self.occupancy as u32,
            (self.occupancy >> 32) as u32,
            SLEEP_RECORD_WORDS as u32,
        ];
        Self::write_words(writer, &header)?;
        let mut record = [0u32; SLEEP_RECORD_WORDS];
        for (grip, form_words) in self
            .standing
            .chunks_exact(body::medium::FORM_WORDS)
            .enumerate()
        {
            let form = body::medium::RegionalForm::unpack(form_words, 0);
            if form.occupied() {
                record.fill(0);
                record[0] = u32::try_from(grip)
                    .expect("an occupied standing grip fits the archive's positional word");
                form.pack(&mut record, 1);
                Self::write_words(writer, &record)?;
            }
        }
        Self::write_words(writer, &self.carrier_row_words)?;
        Self::write_words(writer, &self.carriers)?;
        self.archive_words()
            .checked_mul(core::mem::size_of::<u32>())
            .ok_or_else(|| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "the archive byte extent is representable",
                )
            })
    }

    /// Render the one exact archive chart. Only occupied grip ⊕ form records cross; the dense
    /// zero reservation belongs to the mounted boundary. Every word is explicitly little-endian
    /// so remounting does not depend on the cpu's native byte order.
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(
            self.archive_words()
                .checked_mul(core::mem::size_of::<u32>())
                .expect("a validated sleep archive byte extent is representable"),
        );
        self.write_archive(&mut bytes)
            .expect("writing a validated body to memory cannot fail");
        bytes
    }

    pub fn decode(bytes: &[u8]) -> Result<SleepingBody, String> {
        if bytes.len() % core::mem::size_of::<u32>() != 0 {
            return Err("the sleep archive ends between whole words".into());
        }
        let words: Vec<u32> = bytes
            .chunks_exact(4)
            .map(|word| u32::from_le_bytes([word[0], word[1], word[2], word[3]]))
            .collect();
        if words.len() < 4 || words[0..2] != SLEEP_MAGIC {
            return Err("the sleep archive mouth or version does not match this body".into());
        }
        match words[2] {
            SLEEP_DENSE_VERSION
                if words.len() >= SLEEP_V2_V8_HEADER_WORDS
                    && words[3] as usize == SLEEP_V2_V8_HEADER_WORDS
                    && words[13] == 0 =>
            {
                Self::decode_dense(&words)
            }
            SLEEP_OCCUPIED_VERSION
                if words.len() >= SLEEP_V2_V8_HEADER_WORDS
                    && words[3] as usize == SLEEP_V2_V8_HEADER_WORDS
                    && words[13] == SLEEP_V3_RECORD_WORDS as u32 =>
            {
                Self::decode_occupied(
                    &words,
                    SLEEP_V3_RECORD_WORDS,
                    true,
                    SleepCarrierWire::V2V4,
                    true,
                )
            }
            SLEEP_COMPACT_VERSION
                if words.len() >= SLEEP_V2_V8_HEADER_WORDS
                    && words[3] as usize == SLEEP_V2_V8_HEADER_WORDS
                    && words[13] == SLEEP_RECORD_WORDS as u32 =>
            {
                Self::decode_occupied(
                    &words,
                    SLEEP_RECORD_WORDS,
                    false,
                    SleepCarrierWire::V2V4,
                    true,
                )
            }
            SLEEP_AXES_VERSION
                if words.len() >= SLEEP_V2_V8_HEADER_WORDS
                    && words[3] as usize == SLEEP_V2_V8_HEADER_WORDS
                    && words[13] == SLEEP_RECORD_WORDS as u32 =>
            {
                Self::decode_occupied(
                    &words,
                    SLEEP_RECORD_WORDS,
                    false,
                    SleepCarrierWire::V5V6,
                    true,
                )
            }
            SLEEP_NO_AXES_VERSION
                if words.len() >= SLEEP_V2_V8_HEADER_WORDS
                    && words[3] as usize == SLEEP_V2_V8_HEADER_WORDS
                    && words[13] == SLEEP_RECORD_WORDS as u32 =>
            {
                Self::decode_occupied(
                    &words,
                    SLEEP_RECORD_WORDS,
                    false,
                    SleepCarrierWire::V5V6,
                    false,
                )
            }
            SLEEP_UNIFORM_CARRIER_VERSION
                if words.len() >= SLEEP_V2_V8_HEADER_WORDS
                    && words[3] as usize == SLEEP_V2_V8_HEADER_WORDS
                    && words[13] == SLEEP_RECORD_WORDS as u32 =>
            {
                Self::decode_occupied(
                    &words,
                    SLEEP_RECORD_WORDS,
                    false,
                    SleepCarrierWire::UniformActive,
                    false,
                )
            }
            SLEEP_VARIABLE_CARRIER_VERSION
                if words.len() >= SLEEP_V2_V8_HEADER_WORDS
                    && words[3] as usize == SLEEP_V2_V8_HEADER_WORDS
                    && words[13] == SLEEP_RECORD_WORDS as u32 =>
            {
                Self::decode_occupied(
                    &words,
                    SLEEP_RECORD_WORDS,
                    false,
                    SleepCarrierWire::VariableActive,
                    false,
                )
            }
            SLEEP_VERSION
                if words.len() >= SLEEP_HEADER_WORDS
                    && words[3] as usize == SLEEP_HEADER_WORDS
                    && words[15] == SLEEP_RECORD_WORDS as u32 =>
            {
                Self::decode_current(&words)
            }
            _ => Err("the sleep archive mouth or version does not match this body".into()),
        }
    }

    fn decode_current(words: &[u32]) -> Result<SleepingBody, String> {
        let lanes = words[5] as usize;
        let framing_words = words[6] as usize;
        if lanes == 0 || framing_words != lanes {
            return Err("the current sleep wire frames one carrier row per lineage".into());
        }
        let payload_words_u64 = words[7] as u64 | ((words[8] as u64) << 32);
        let carrier_words_u64 = words[9] as u64 | ((words[10] as u64) << 32);
        let payload_words = usize::try_from(payload_words_u64)
            .map_err(|_| "the occupied standing extent is representable".to_string())?;
        let carrier_words = usize::try_from(carrier_words_u64)
            .map_err(|_| "the sleeping carrier extent is representable".to_string())?;
        let comprehended_light_bytes = words[11] as u64 | ((words[12] as u64) << 32);
        let occupancy = words[13] as u64 | ((words[14] as u64) << 32);
        if payload_words_u64
            != occupancy
                .checked_mul(SLEEP_RECORD_WORDS as u64)
                .ok_or_else(|| "the occupied standing extent is representable".to_string())?
        {
            return Err("the sleep archive carries exactly one record per occupied grip".into());
        }
        let expected = SLEEP_HEADER_WORDS
            .checked_add(payload_words)
            .and_then(|extent| extent.checked_add(framing_words))
            .and_then(|extent| extent.checked_add(carrier_words))
            .ok_or_else(|| "the sleep archive extent is representable".to_string())?;
        if words.len() != expected {
            return Err("the sleep archive contains exactly one declared body".into());
        }
        let standing_axis = words[4];
        let standing_cells = (standing_axis as usize)
            .checked_mul(standing_axis as usize)
            .ok_or_else(|| "the sleeping standing extent is representable".to_string())?;
        if standing_axis == 0
            || !standing_axis.is_power_of_two()
            || occupancy > standing_cells as u64
        {
            return Err("the sleeping body has one valid occupied dyadic chart".into());
        }
        let standing_word_count = standing_cells
            .checked_mul(body::medium::FORM_WORDS)
            .ok_or_else(|| "the sleeping standing word extent is representable".to_string())?;
        let mut standing = vec![0u32; standing_word_count];
        let payload_end = SLEEP_HEADER_WORDS + payload_words;
        let mut prior_grip = None;
        for record in words[SLEEP_HEADER_WORDS..payload_end].chunks_exact(SLEEP_RECORD_WORDS) {
            let grip = record[0] as usize;
            if grip >= standing_cells || prior_grip.is_some_and(|prior| grip <= prior) {
                return Err("occupied grips cross the sleep mouth once in chart order".into());
            }
            let form = body::medium::RegionalForm::unpack_compact_checked(&record[1..], 0)
                .map_err(|_| {
                    "a compact sleep record carries one canonical regional form".to_string()
                })?;
            if !form.occupied() {
                return Err("an occupied sleep record carries one founded regional form".into());
            }
            let mut canonical = [0u32; SLEEP_V4_FORM_WORDS];
            form.pack(&mut canonical, 0);
            if canonical.as_slice() != &record[1..] {
                return Err("an occupied sleep record carries one canonical regional form".into());
            }
            form.pack(&mut standing, grip * body::medium::FORM_WORDS);
            prior_grip = Some(grip);
        }
        let carrier_at = payload_end + framing_words;
        let carrier_row_words = words[payload_end..carrier_at].to_vec();
        let carriers = words[carrier_at..].to_vec();
        SleepingBody::from_variable_parts(
            standing_axis,
            occupancy,
            carrier_row_words,
            standing,
            carriers,
            comprehended_light_bytes,
        )
    }

    /// V2–V4 carried the exact carrier prefix which preceded the within-atom continuation. Decode
    /// that historical row literally and append only the canonical all-zero continuation and
    /// pending-deed tails, per lineage.
    fn extend_v2_v4_carriers(
        lanes: usize,
        historical_row_words: usize,
        historical: &[u32],
    ) -> Result<(u32, Vec<u32>), String> {
        let depth = historical_carrier_row_depth(historical_row_words).ok_or_else(|| {
            "the historical sleep archive carries one literal carrier row".to_string()
        })?;
        let historical_extent = lanes
            .checked_mul(historical_row_words)
            .ok_or_else(|| "the historical carrier extent is representable".to_string())?;
        if historical.len() != historical_extent {
            return Err("the historical sleep archive carries one whole row per lineage".into());
        }
        let active_row_words = body::manifold::carrier_row_words(depth);
        let synthesized_words = body::manifold::CARRIER_CONTINUATION_WORDS
            .checked_add(body::manifold::CARRIER_PENDING_DEED_WORDS)
            .ok_or_else(|| "the active carrier tail is representable".to_string())?;
        if active_row_words
            != historical_row_words
                .checked_add(synthesized_words)
                .ok_or_else(|| "the active carrier row is representable".to_string())?
        {
            return Err(
                "the historical carrier prefix extends into exactly one active tail".into(),
            );
        }
        let active_extent = lanes
            .checked_mul(active_row_words)
            .ok_or_else(|| "the active carrier extent is representable".to_string())?;
        let mut carriers = Vec::new();
        carriers
            .try_reserve_exact(active_extent)
            .map_err(|_| "this boundary can mount the active carrier extent".to_string())?;
        for row in historical.chunks_exact(historical_row_words) {
            carriers.extend_from_slice(row);
            carriers.resize(carriers.len() + synthesized_words, 0);
        }
        Ok((
            u32::try_from(active_row_words)
                .map_err(|_| "the active carrier row fits its archive mouth".to_string())?,
            carriers,
        ))
    }

    /// V5/V6 already carry the literal nineteen-word descending continuation. Validate that tail
    /// at rest, then synthesize this version's absent pending-deed face separately for every
    /// lineage. A historical row is never offered to the active depth helper.
    fn extend_v5_v6_carriers(
        lanes: usize,
        historical_row_words: usize,
        historical: &[u32],
    ) -> Result<(u32, Vec<u32>), String> {
        let depth = v5_v6_carrier_row_depth(historical_row_words)
            .ok_or_else(|| "the V5/V6 sleep archive carries one literal carrier row".to_string())?;
        let historical_extent = lanes
            .checked_mul(historical_row_words)
            .ok_or_else(|| "the historical carrier extent is representable".to_string())?;
        if historical.len() != historical_extent {
            return Err("the historical sleep archive carries one whole row per lineage".into());
        }
        let prefix_words = historical_carrier_row_words(depth)
            .ok_or_else(|| "the historical carrier prefix is representable".to_string())?;
        let active_row_words = body::manifold::carrier_row_words(depth);
        if active_row_words
            != historical_row_words
                .checked_add(body::manifold::CARRIER_PENDING_DEED_WORDS)
                .ok_or_else(|| "the active carrier row is representable".to_string())?
        {
            return Err("the V5/V6 carrier row gains exactly the pending-deed tail".into());
        }
        let active_extent = lanes
            .checked_mul(active_row_words)
            .ok_or_else(|| "the active carrier extent is representable".to_string())?;
        let mut carriers = Vec::new();
        carriers
            .try_reserve_exact(active_extent)
            .map_err(|_| "this boundary can mount the active carrier extent".to_string())?;
        for row in historical.chunks_exact(historical_row_words) {
            if row[prefix_words + body::manifold::CARRIER_CONTINUATION_PHASE]
                != body::manifold::CONTINUATION_NONE
            {
                return Err("a V5/V6 sleeping lineage carries no active continuation".into());
            }
            carriers.extend_from_slice(row);
            carriers.resize(
                carriers.len() + body::manifold::CARRIER_PENDING_DEED_WORDS,
                0,
            );
        }
        Ok((
            u32::try_from(active_row_words)
                .map_err(|_| "the active carrier row fits its archive mouth".to_string())?,
            carriers,
        ))
    }

    /// Read the superseded dense V2 chart semantically, then materialize the current runtime row.
    /// V2's 17-word width is historical and never follows active `FORM_WORDS`.
    fn decode_dense(words: &[u32]) -> Result<SleepingBody, String> {
        let lanes = words[5] as usize;
        let standing_words = words[7] as usize;
        let carrier_words = words[8] as usize;
        let axes_end = SLEEP_V2_V8_HEADER_WORDS
            .checked_add(lanes)
            .ok_or_else(|| "the sleep archive axis extent is representable".to_string())?;
        let standing_end = axes_end
            .checked_add(standing_words)
            .ok_or_else(|| "the V2 standing extent is representable".to_string())?;
        let expected = standing_end
            .checked_add(carrier_words)
            .ok_or_else(|| "the sleep archive extent is representable".to_string())?;
        if words.len() != expected {
            return Err("the sleep archive contains exactly one declared body".into());
        }
        Self::validate_historical_axes(&words[SLEEP_V2_V8_HEADER_WORDS..axes_end], lanes)?;
        let standing_axis = words[4];
        let standing_cells = (standing_axis as usize)
            .checked_mul(standing_axis as usize)
            .ok_or_else(|| "the sleeping standing extent is representable".to_string())?;
        let historical_words = standing_cells
            .checked_mul(SLEEP_V2_FORM_WORDS)
            .ok_or_else(|| "the V2 standing extent is representable".to_string())?;
        if standing_words != historical_words {
            return Err("the V2 archive carries one fixed 17-word form per standing place".into());
        }
        let runtime_words = standing_cells
            .checked_mul(body::medium::FORM_WORDS)
            .ok_or_else(|| "the current sleeping standing extent is representable".to_string())?;
        let mut standing = Vec::new();
        standing
            .try_reserve_exact(runtime_words)
            .map_err(|_| "this boundary can mount the sleeping standing extent".to_string())?;
        standing.resize(runtime_words, 0);
        for (cell, row) in words[axes_end..standing_end]
            .chunks_exact(SLEEP_V2_FORM_WORDS)
            .enumerate()
        {
            let form = body::medium::RegionalForm::unpack_legacy_checked(row).map_err(|_| {
                "a V2 record carries one canonical legacy regional form".to_string()
            })?;
            let at = cell * body::medium::FORM_WORDS;
            form.pack(&mut standing, at);
        }
        let (carrier_row_words, carriers) =
            Self::extend_v2_v4_carriers(lanes, words[6] as usize, &words[standing_end..])?;
        SleepingBody::from_parts(
            standing_axis,
            words[11] as u64 | ((words[12] as u64) << 32),
            carrier_row_words,
            words[5],
            standing,
            carriers,
            words[9] as u64 | ((words[10] as u64) << 32),
        )
    }

    /// Read V3's legacy occupied records or V4–V8 compact records semantically, then materialize
    /// the current dense runtime row. This is archive decode, never a thaw dispatch.
    fn decode_occupied(
        words: &[u32],
        record_words: usize,
        legacy: bool,
        carrier_wire: SleepCarrierWire,
        historical_axes: bool,
    ) -> Result<SleepingBody, String> {
        let lanes = usize::try_from(words[5])
            .map_err(|_| "the sleeping lineage extent is representable".to_string())?;
        let payload_words = usize::try_from(words[7])
            .map_err(|_| "the occupied standing extent is representable".to_string())?;
        let carrier_words = usize::try_from(words[8])
            .map_err(|_| "the sleeping carrier extent is representable".to_string())?;
        let occupancy = words[11] as u64 | ((words[12] as u64) << 32);
        let records = usize::try_from(occupancy)
            .map_err(|_| "the sleeping occupancy is representable".to_string())?;
        let expected_payload = records
            .checked_mul(record_words)
            .ok_or_else(|| "the occupied standing extent is representable".to_string())?;
        if payload_words != expected_payload {
            return Err("the sleep archive carries exactly one record per occupied grip".into());
        }
        let axes_words = if historical_axes { lanes } else { 0 };
        let carrier_framing_words = if matches!(carrier_wire, SleepCarrierWire::VariableActive) {
            let framing = usize::try_from(words[6])
                .map_err(|_| "the carrier framing extent is representable".to_string())?;
            if framing != lanes {
                return Err("the variable sleep wire frames one carrier row per lineage".into());
            }
            framing
        } else {
            0
        };
        let expected = SLEEP_V2_V8_HEADER_WORDS
            .checked_add(axes_words)
            .and_then(|words| words.checked_add(payload_words))
            .and_then(|words| words.checked_add(carrier_framing_words))
            .and_then(|words| words.checked_add(carrier_words))
            .ok_or_else(|| "the sleep archive extent is representable".to_string())?;
        if words.len() != expected {
            return Err("the sleep archive contains exactly one declared body".into());
        }

        let standing_axis = words[4];
        if standing_axis == 0 || standing_axis & (standing_axis - 1) != 0 {
            return Err("the sleeping body has one positive dyadic standing axis".into());
        }
        let standing_cells = (standing_axis as usize)
            .checked_mul(standing_axis as usize)
            .ok_or_else(|| "the sleeping standing extent is representable".to_string())?;
        if occupancy > standing_cells as u64 {
            return Err("the sleeping occupancy fits its standing chart".into());
        }
        let standing_word_count = standing_cells
            .checked_mul(body::medium::FORM_WORDS)
            .ok_or_else(|| "the sleeping standing word extent is representable".to_string())?;
        let axes_end = SLEEP_V2_V8_HEADER_WORDS
            .checked_add(axes_words)
            .ok_or_else(|| "the sleep archive axis extent is representable".to_string())?;
        if historical_axes {
            Self::validate_historical_axes(&words[SLEEP_V2_V8_HEADER_WORDS..axes_end], lanes)?;
        }
        let payload_end = axes_end
            .checked_add(payload_words)
            .ok_or_else(|| "the occupied standing extent is representable".to_string())?;
        let payload = &words[axes_end..payload_end];

        let mut standing = Vec::new();
        standing
            .try_reserve_exact(standing_word_count)
            .map_err(|_| "this boundary can mount the sleeping standing extent".to_string())?;
        standing.resize(standing_word_count, 0);
        let mut prior_grip = None;
        for record in payload.chunks_exact(record_words) {
            let grip = record[0] as usize;
            if grip >= standing_cells {
                return Err("an occupied grip lies within its sleeping chart".into());
            }
            if prior_grip.is_some_and(|prior| grip <= prior) {
                return Err("occupied grips cross the sleep mouth once in chart order".into());
            }
            let form_words = &record[1..record_words];
            let form = if legacy {
                body::medium::RegionalForm::unpack_legacy_checked(form_words).map_err(|_| {
                    "a V3 record carries one canonical legacy regional form".to_string()
                })?
            } else {
                body::medium::RegionalForm::unpack_compact_checked(form_words, 0).map_err(|_| {
                    "a compact sleep record carries one canonical regional form".to_string()
                })?
            };
            if !form.occupied() {
                return Err("an occupied sleep record carries one founded regional form".into());
            }
            let canonical = if legacy {
                let mut row = [0u32; SLEEP_V2_FORM_WORDS];
                form.pack_legacy_checked(&mut row)
                    .map_err(|_| "the V3 form remains in the legacy domain".to_string())?;
                row.as_slice() == form_words
            } else {
                let mut row = [0u32; SLEEP_V4_FORM_WORDS];
                form.pack(&mut row, 0);
                row.as_slice() == form_words
            };
            if !canonical {
                return Err("an occupied sleep record carries one canonical regional form".into());
            }
            prior_grip = Some(grip);
            form.pack(&mut standing, grip * body::medium::FORM_WORDS);
        }

        let carrier_start = payload_end
            .checked_add(carrier_framing_words)
            .ok_or_else(|| "the carrier framing extent is representable".to_string())?;
        let (carrier_row_words, carriers) = match carrier_wire {
            SleepCarrierWire::V2V4 => {
                let (row_words, carriers) =
                    Self::extend_v2_v4_carriers(lanes, words[6] as usize, &words[payload_end..])?;
                (vec![row_words; lanes], carriers)
            }
            SleepCarrierWire::V5V6 => {
                let (row_words, carriers) =
                    Self::extend_v5_v6_carriers(lanes, words[6] as usize, &words[payload_end..])?;
                (vec![row_words; lanes], carriers)
            }
            SleepCarrierWire::UniformActive => {
                (vec![words[6]; lanes], words[payload_end..].to_vec())
            }
            SleepCarrierWire::VariableActive => (
                words[payload_end..carrier_start].to_vec(),
                words[carrier_start..].to_vec(),
            ),
        };
        SleepingBody::from_variable_parts(
            standing_axis,
            occupancy,
            carrier_row_words,
            standing,
            carriers,
            words[9] as u64 | ((words[10] as u64) << 32),
        )
    }

    /// V2–V5 carried one light-local chart axis per lineage. Those words remain part of their
    /// literal historical mouths and must still validate, but §XXXII-c's REGISTER dies at the
    /// receiving edge, so no historical axis enters the active body.
    fn validate_historical_axes(axes: &[u32], lanes: usize) -> Result<(), String> {
        if axes.len() != lanes
            || axes
                .iter()
                .any(|axis| *axis == 0 || *axis & (*axis - 1) != 0)
        {
            return Err(
                "the historical sleep archive carries one positive dyadic chart per lineage".into(),
            );
        }
        Ok(())
    }

    /// Deposit a new chart without an overwrite path. The caller supplies the periplus name; this
    /// mouth can only create it once.
    pub fn archive_new(&self, path: &std::path::Path) -> std::io::Result<usize> {
        use std::io::Write as _;
        let file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)?;
        let mut writer = std::io::BufWriter::new(file);
        let bytes = self.write_archive(&mut writer)?;
        writer.flush()?;
        writer.get_ref().sync_all()?;
        Ok(bytes)
    }

    /// Check the current archive directly against this body's canonical wire without building a
    /// second body or complete octet image beside it. This is the exact SLEEP/read gauge at the
    /// listener boundary; it changes neither the body nor the archive.
    pub fn verify_archive(&self, path: &std::path::Path) -> std::io::Result<usize> {
        let file = std::fs::File::open(path)?;
        let reader = std::io::BufReader::new(file);
        let mut comparator = ArchiveComparator { reader };
        let bytes = self.write_archive(&mut comparator)?;
        comparator.finish()?;
        Ok(bytes)
    }

    fn read_current_frame(
        path: &std::path::Path,
        materialize_carriers: bool,
    ) -> std::io::Result<(SleepingBodyFrame, Option<Vec<u32>>)> {
        use std::io::Read as _;
        let file = std::fs::File::open(path)?;
        let archive_bytes = file.metadata()?.len();
        let mut reader = std::io::BufReader::new(file);
        let mut prefix = [0u32; 4];
        Self::read_words(&mut reader, &mut prefix)?;
        if prefix[0..2] != SLEEP_MAGIC {
            return Err(Self::invalid_archive(
                "the archive is not a canonical current SLEEP mouth",
            ));
        }
        let (
            header_words,
            standing_axis,
            lineages,
            framing_words,
            payload_words,
            carrier_words,
            comprehended_light_bytes,
            occupancy,
        ) = match prefix[2] {
            SLEEP_VARIABLE_CARRIER_VERSION if prefix[3] as usize == SLEEP_V2_V8_HEADER_WORDS => {
                let mut header = [0u32; SLEEP_V2_V8_HEADER_WORDS];
                header[..4].copy_from_slice(&prefix);
                Self::read_words(&mut reader, &mut header[4..])?;
                if header[13] as usize != SLEEP_RECORD_WORDS {
                    return Err(Self::invalid_archive(
                        "the V8 archive carries compact standing records",
                    ));
                }
                (
                    SLEEP_V2_V8_HEADER_WORDS,
                    header[4],
                    header[5] as usize,
                    header[6] as usize,
                    header[7] as u64,
                    header[8] as u64,
                    header[9] as u64 | ((header[10] as u64) << 32),
                    header[11] as u64 | ((header[12] as u64) << 32),
                )
            }
            SLEEP_VERSION if prefix[3] as usize == SLEEP_HEADER_WORDS => {
                let mut header = [0u32; SLEEP_HEADER_WORDS];
                header[..4].copy_from_slice(&prefix);
                Self::read_words(&mut reader, &mut header[4..])?;
                if header[15] as usize != SLEEP_RECORD_WORDS {
                    return Err(Self::invalid_archive(
                        "the current archive carries compact standing records",
                    ));
                }
                (
                    SLEEP_HEADER_WORDS,
                    header[4],
                    header[5] as usize,
                    header[6] as usize,
                    header[7] as u64 | ((header[8] as u64) << 32),
                    header[9] as u64 | ((header[10] as u64) << 32),
                    header[11] as u64 | ((header[12] as u64) << 32),
                    header[13] as u64 | ((header[14] as u64) << 32),
                )
            }
            _ => {
                return Err(Self::invalid_archive(
                    "the archive is not a canonical current SLEEP mouth",
                ));
            }
        };

        if standing_axis == 0 || standing_axis & (standing_axis - 1) != 0 {
            return Err(Self::invalid_archive(
                "the sleeping body has one positive dyadic standing axis",
            ));
        }
        if lineages == 0 || framing_words != lineages {
            return Err(Self::invalid_archive(
                "the current sleep wire frames one carrier row per lineage",
            ));
        }
        let occupied = usize::try_from(occupancy)
            .map_err(|_| Self::invalid_archive("the sleeping occupancy is representable"))?;
        let expected_payload = occupancy
            .checked_mul(SLEEP_RECORD_WORDS as u64)
            .ok_or_else(|| {
                Self::invalid_archive("the occupied standing extent is representable")
            })?;
        if payload_words != expected_payload {
            return Err(Self::invalid_archive(
                "the sleep archive carries exactly one record per occupied grip",
            ));
        }
        let archive_words = (header_words as u64)
            .checked_add(payload_words)
            .and_then(|words| words.checked_add(framing_words as u64))
            .and_then(|words| words.checked_add(carrier_words))
            .ok_or_else(|| Self::invalid_archive("the sleep archive extent is representable"))?;
        let expected_bytes = archive_words
            .checked_mul(core::mem::size_of::<u32>() as u64)
            .ok_or_else(|| {
                Self::invalid_archive("the sleep archive byte extent is representable")
            })?;
        if archive_bytes != expected_bytes {
            return Err(Self::invalid_archive(
                "the sleep archive contains exactly one declared body",
            ));
        }

        let standing_cells = (standing_axis as usize)
            .checked_mul(standing_axis as usize)
            .ok_or_else(|| {
                Self::invalid_archive("the sleeping standing extent is representable")
            })?;
        if occupancy > standing_cells as u64 {
            return Err(Self::invalid_archive(
                "the sleeping occupancy fits its standing chart",
            ));
        }
        let standing_words = standing_cells
            .checked_mul(body::medium::FORM_WORDS)
            .ok_or_else(|| {
                Self::invalid_archive("the sleeping standing word extent is representable")
            })?;
        let mut standing = Self::zeroed_words(standing_words, "sleeping standing extent")?;
        let mut prior_grip = None;
        let mut record = [0u32; SLEEP_RECORD_WORDS];
        for _ in 0..occupied {
            Self::read_words(&mut reader, &mut record)?;
            let grip = record[0] as usize;
            if grip >= standing_cells || prior_grip.is_some_and(|prior| grip <= prior) {
                return Err(Self::invalid_archive(
                    "occupied grips cross the sleep mouth once in chart order",
                ));
            }
            let form_words = &record[1..];
            let form = body::medium::RegionalForm::unpack_compact_checked(form_words, 0).map_err(
                |_| {
                    Self::invalid_archive(
                        "a compact sleep record carries one canonical regional form",
                    )
                },
            )?;
            if !form.occupied() {
                return Err(Self::invalid_archive(
                    "an occupied sleep record carries one founded regional form",
                ));
            }
            let mut canonical = [0u32; SLEEP_V4_FORM_WORDS];
            form.pack(&mut canonical, 0);
            if canonical.as_slice() != form_words {
                return Err(Self::invalid_archive(
                    "an occupied sleep record carries one canonical regional form",
                ));
            }
            form.pack(&mut standing, grip * body::medium::FORM_WORDS);
            prior_grip = Some(grip);
        }

        let mut carrier_row_words = Self::zeroed_words(lineages, "carrier framing extent")?;
        Self::read_words(&mut reader, &mut carrier_row_words)?;
        let frame = SleepingBodyFrame::from_parts(
            standing_axis,
            occupancy,
            carrier_row_words,
            standing,
            comprehended_light_bytes,
        )
        .map_err(Self::invalid_archive)?;
        if frame.carrier_words != carrier_words {
            return Err(Self::invalid_archive(
                "the sleeping body carries one whole carrier/K row per lineage",
            ));
        }
        let mut carriers = if materialize_carriers {
            let words = usize::try_from(carrier_words).map_err(|_| {
                Self::invalid_archive("this boundary can mount the sleeping carrier extent")
            })?;
            let mut carriers = Vec::new();
            carriers.try_reserve_exact(words).map_err(|_| {
                Self::invalid_archive("this boundary can mount the sleeping carrier extent")
            })?;
            Some(carriers)
        } else {
            None
        };
        let mut row = Vec::new();
        for &row_words in &frame.carrier_row_words {
            row.clear();
            row.try_reserve_exact(row_words as usize).map_err(|_| {
                Self::invalid_archive("this boundary can mount one sleeping carrier row")
            })?;
            row.resize(row_words as usize, 0);
            Self::read_words(&mut reader, &mut row)?;
            Self::validate_carrier_row(&row).map_err(Self::invalid_archive)?;
            if let Some(carriers) = carriers.as_mut() {
                carriers.extend_from_slice(&row);
            }
        }
        let mut trailing = [0u8; 1];
        if reader.read(&mut trailing)? != 0 {
            return Err(Self::invalid_archive(
                "the SLEEP archive ends at its declared body boundary",
            ));
        }
        Ok((frame, carriers))
    }

    /// Read the current SLEEP mouth in one streaming passage and materialize the complete runtime
    /// body. Large production continuations should use `read_current_receiving_archive`, because
    /// ended carrier rows dissipate before genuinely new currents arrive.
    pub fn read_current_archive(path: &std::path::Path) -> std::io::Result<SleepingBody> {
        let (frame, carriers) = Self::read_current_frame(path, true)?;
        let carriers = carriers.expect("the materializing read returns its carrier construction");
        Ok(SleepingBody::from_checked_parts(
            frame.standing_axis,
            frame.occupancy,
            frame.carrier_row_words,
            frame.standing,
            carriers,
            frame.comprehended_light_bytes,
        ))
    }

    /// Validate every current carrier row while retaining only the standing receiving face which
    /// genuinely new lineages can inherit. No ended carrier aggregate is materialized merely to
    /// discard it at the next light.
    pub fn read_current_receiving_archive(
        path: &std::path::Path,
    ) -> std::io::Result<(u32, u64, Vec<u32>, u64)> {
        let (frame, carriers) = Self::read_current_frame(path, false)?;
        debug_assert!(carriers.is_none());
        Ok(frame.into_receiving_parts())
    }

    pub fn read_archive(path: &std::path::Path) -> std::io::Result<SleepingBody> {
        let mut file = std::fs::File::open(path)?;
        let mut prefix = [0u32; 3];
        Self::read_words(&mut file, &mut prefix)?;
        if prefix[0..2] == SLEEP_MAGIC
            && matches!(prefix[2], SLEEP_VARIABLE_CARRIER_VERSION | SLEEP_VERSION)
        {
            return Self::read_current_archive(path);
        }
        let bytes = std::fs::read(path)?;
        SleepingBody::decode(&bytes).map_err(Self::invalid_archive)
    }
}

impl SleepingBodyFrame {
    pub fn from_parts(
        standing_axis: u32,
        occupancy: u64,
        carrier_row_words: Vec<u32>,
        standing: Vec<u32>,
        comprehended_light_bytes: u64,
    ) -> Result<SleepingBodyFrame, String> {
        let carrier_words = SleepingBody::validate_frame_parts(
            standing_axis,
            occupancy,
            &carrier_row_words,
            &standing,
            comprehended_light_bytes,
        )?;
        Ok(SleepingBodyFrame {
            standing_axis,
            occupancy,
            carrier_row_words,
            standing,
            comprehended_light_bytes,
            carrier_words,
        })
    }

    pub fn standing_axis(&self) -> u32 {
        self.standing_axis
    }

    pub fn occupancy(&self) -> u64 {
        self.occupancy
    }

    pub fn lineage_count(&self) -> usize {
        self.carrier_row_words.len()
    }

    pub fn carrier_row_word_extents(&self) -> &[u32] {
        &self.carrier_row_words
    }

    pub fn carrier_words(&self) -> u64 {
        self.carrier_words
    }

    pub fn standing(&self) -> &[u32] {
        &self.standing
    }

    pub fn comprehended_light_bytes(&self) -> u64 {
        self.comprehended_light_bytes
    }

    pub fn body_bytes(&self) -> u64 {
        self.occupancy
            .checked_mul(SLEEP_RECORD_WORDS as u64)
            .and_then(|words| words.checked_add(self.carrier_words))
            .and_then(|words| words.checked_mul(core::mem::size_of::<u32>() as u64))
            .and_then(|bytes| bytes.checked_add(core::mem::size_of::<u64>() as u64))
            .expect("a validated streaming body has a representable identity extent")
    }

    pub fn archive_bytes(&self) -> u64 {
        self.occupancy
            .checked_mul(SLEEP_RECORD_WORDS as u64)
            .and_then(|words| words.checked_add(self.carrier_row_words.len() as u64))
            .and_then(|words| words.checked_add(self.carrier_words))
            .and_then(|words| words.checked_add(SLEEP_HEADER_WORDS as u64))
            .and_then(|words| words.checked_mul(core::mem::size_of::<u32>() as u64))
            .expect("a validated streaming body has a representable archive extent")
    }

    pub fn into_receiving_parts(self) -> (u32, u64, Vec<u32>, u64) {
        (
            self.standing_axis,
            self.occupancy,
            self.standing,
            self.comprehended_light_bytes,
        )
    }

    pub fn archive_new(
        &self,
        path: &std::path::Path,
    ) -> std::io::Result<SleepingBodyArchiveWriter<'_>> {
        let file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)?;
        let mut writer = std::io::BufWriter::new(file);
        let standing_words = self
            .occupancy
            .checked_mul(SLEEP_RECORD_WORDS as u64)
            .ok_or_else(|| {
                SleepingBody::invalid_archive("the occupied standing extent is representable")
            })?;
        let header = [
            SLEEP_MAGIC[0],
            SLEEP_MAGIC[1],
            SLEEP_VERSION,
            SLEEP_HEADER_WORDS as u32,
            self.standing_axis,
            self.carrier_row_words.len() as u32,
            self.carrier_row_words.len() as u32,
            standing_words as u32,
            (standing_words >> 32) as u32,
            self.carrier_words as u32,
            (self.carrier_words >> 32) as u32,
            self.comprehended_light_bytes as u32,
            (self.comprehended_light_bytes >> 32) as u32,
            self.occupancy as u32,
            (self.occupancy >> 32) as u32,
            SLEEP_RECORD_WORDS as u32,
        ];
        SleepingBody::write_words(&mut writer, &header)?;
        let mut record = [0u32; SLEEP_RECORD_WORDS];
        for (grip, form_words) in self
            .standing
            .chunks_exact(body::medium::FORM_WORDS)
            .enumerate()
        {
            let form = body::medium::RegionalForm::unpack(form_words, 0);
            if form.occupied() {
                record.fill(0);
                record[0] = grip as u32;
                form.pack(&mut record, 1);
                SleepingBody::write_words(&mut writer, &record)?;
            }
        }
        SleepingBody::write_words(&mut writer, &self.carrier_row_words)?;
        Ok(SleepingBodyArchiveWriter {
            frame: self,
            writer,
            next_row: 0,
        })
    }
}

impl SleepingBodyArchiveWriter<'_> {
    pub fn write_carrier_row(&mut self, row: &[u32]) -> std::io::Result<()> {
        let expected = self
            .frame
            .carrier_row_words
            .get(self.next_row)
            .copied()
            .ok_or_else(|| {
                SleepingBody::invalid_archive("the archive receives each carrier row once")
            })? as usize;
        if row.len() != expected {
            return Err(SleepingBody::invalid_archive(format!(
                "carrier row {} has {} words, expected {expected}",
                self.next_row,
                row.len(),
            )));
        }
        SleepingBody::validate_carrier_row(row).map_err(SleepingBody::invalid_archive)?;
        SleepingBody::write_words(&mut self.writer, row)?;
        self.next_row += 1;
        Ok(())
    }

    pub fn finish(mut self) -> std::io::Result<usize> {
        use std::io::Write as _;
        if self.next_row != self.frame.carrier_row_words.len() {
            return Err(SleepingBody::invalid_archive(
                "the archive receives every complete carrier row",
            ));
        }
        self.writer.flush()?;
        self.writer.get_ref().sync_all()?;
        let expected = self.frame.archive_bytes();
        let actual = self.writer.get_ref().metadata()?.len();
        if actual != expected {
            return Err(SleepingBody::invalid_archive(format!(
                "the streaming SLEEP archive has {actual} octets, expected {expected}",
            )));
        }
        usize::try_from(actual)
            .map_err(|_| SleepingBody::invalid_archive("the archive extent fits this boundary"))
    }
}

/// M4's card mouth: first-person lineage scope terminates into the accepted three-phase
/// configuration product. No historical scope entry or CAS-era mechanism is mapped here.
pub struct FeltSurface {
    pub adapter_name: String,
    pub max_storage_binding_bytes: u64,
    device: wgpu::Device,
    queue: wgpu::Queue,
    scope: wgpu::ComputePipeline,
    scope_founded: wgpu::ComputePipeline,
    grain: wgpu::ComputePipeline,
    sum: wgpu::ComputePipeline,
    founded_grain: wgpu::ComputePipeline,
    founded_sum: wgpu::ComputePipeline,
    finish: wgpu::ComputePipeline,
    chart_mark: wgpu::ComputePipeline,
    chart_count: wgpu::ComputePipeline,
    chart_recast: wgpu::ComputePipeline,
    scope_layout: wgpu::BindGroupLayout,
    scope_founded_layout: wgpu::BindGroupLayout,
    grain_layout: wgpu::BindGroupLayout,
    sum_layout: wgpu::BindGroupLayout,
    finish_layout: wgpu::BindGroupLayout,
    chart_mark_layout: wgpu::BindGroupLayout,
    chart_count_layout: wgpu::BindGroupLayout,
    chart_recast_layout: wgpu::BindGroupLayout,
    max_workgroups: u32,
}

impl FeltSurface {
    fn standing_occupancy(standing: &[u32]) -> u64 {
        standing
            .chunks_exact(body::medium::FORM_WORDS)
            .map(|words| {
                body::medium::RegionalForm::unpack_compact_checked(words, 0)
                    .expect("the mounted standing boundary carries canonical compact forms")
            })
            .filter(|form| form.occupied())
            .count() as u64
    }

    /// Open only on a card that carries the exact 64-bit atomic operations used by the fold. There
    /// is no fallback implementation: absence of the mechanism is an honest absent surface.
    pub fn new() -> Option<FeltSurface> {
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor::default());
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))
        .ok()?;
        let required = wgpu::Features::SHADER_INT64
            | wgpu::Features::SHADER_INT64_ATOMIC_ALL_OPS
            | wgpu::Features::EXPERIMENTAL_PASSTHROUGH_SHADERS;
        if !adapter.features().contains(required) {
            eprintln!(
                "surface: M4 card absent — adapter lacks {:?}",
                required - adapter.features()
            );
            return None;
        }
        let info = adapter.get_info();
        let adapter_name = format!("{} ({:?}/{:?})", info.name, info.device_type, info.backend);
        let limits = adapter.limits();
        let max_workgroups = limits.max_compute_workgroups_per_dimension;
        let max_storage_binding_bytes =
            (limits.max_storage_buffer_binding_size as u64).min(limits.max_buffer_size);
        let (device, queue) = pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor {
            required_features: required,
            required_limits: limits,
            experimental_features: unsafe { wgpu::ExperimentalFeatures::enabled() },
            ..Default::default()
        }))
        .ok()?;
        device.on_uncaptured_error(std::sync::Arc::new(|e| {
            eprintln!("surface: M4 wgpu uncaptured error — {e}")
        }));
        device.set_device_lost_callback(|reason, message| {
            eprintln!("surface: card device lost ({reason:?}) — {message}")
        });
        let module = unsafe {
            device.create_shader_module_passthrough(wgpu::ShaderModuleDescriptorPassthrough {
                label: Some("soma-felt-series"),
                spirv: Some(wgpu::util::make_spirv_raw(include_bytes!(
                    "../../kernel/soma.spv"
                ))),
                ..Default::default()
            })
        };
        let layout = |label: &str, bindings: u32| {
            let entries: Vec<_> = (0..bindings).map(storage_entry).collect();
            device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some(label),
                entries: &entries,
            })
        };
        let scope_layout = layout("scope_felt", 7);
        let scope_founded_layout = layout("scope_founded", 8);
        let grain_layout = layout("link_grain", 6);
        let sum_layout = layout("link_sum", 8);
        let finish_layout = layout("link_finish", 8);
        let chart_mark_layout = layout("chart_mark", 3);
        let chart_count_layout = layout("chart_count", 4);
        let chart_recast_layout = layout("chart_recast", 3);
        let pipeline = |entry: &str, bind_layout: &wgpu::BindGroupLayout| {
            let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some(entry),
                bind_group_layouts: &[bind_layout],
                push_constant_ranges: &[],
            });
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(entry),
                layout: Some(&pipeline_layout),
                module: &module,
                entry_point: Some(entry),
                compilation_options: Default::default(),
                cache: None,
            })
        };
        let scope = pipeline("scope_felt", &scope_layout);
        let scope_founded = pipeline("scope_founded", &scope_founded_layout);
        let grain = pipeline("link_grain", &grain_layout);
        let sum = pipeline("link_sum", &sum_layout);
        let founded_grain = pipeline("link_founded_grain", &grain_layout);
        let founded_sum = pipeline("link_founded_sum", &sum_layout);
        let finish = pipeline("link_finish", &finish_layout);
        let chart_mark = pipeline("chart_mark", &chart_mark_layout);
        let chart_count = pipeline("chart_count", &chart_count_layout);
        let chart_recast = pipeline("chart_recast", &chart_recast_layout);
        Some(FeltSurface {
            adapter_name,
            max_storage_binding_bytes,
            device,
            queue,
            scope,
            scope_founded,
            grain,
            sum,
            founded_grain,
            founded_sum,
            finish,
            chart_mark,
            chart_count,
            chart_recast,
            scope_layout,
            scope_founded_layout,
            grain_layout,
            sum_layout,
            finish_layout,
            chart_mark_layout,
            chart_count_layout,
            chart_recast_layout,
            max_workgroups,
        })
    }

    fn storage<T: bytemuck::Pod>(&self, label: &str, data: &[T]) -> wgpu::Buffer {
        use wgpu::util::DeviceExt;
        assert!(
            !data.is_empty(),
            "a mounted card buffer has positive extent"
        );
        let bytes = (data.len() * core::mem::size_of::<T>()) as u64;
        assert!(
            bytes <= self.max_storage_binding_bytes,
            "{label} ({bytes} bytes) fits the card's storage-binding aperture ({})",
            self.max_storage_binding_bytes,
        );
        self.device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some(label),
                contents: bytemuck::cast_slice(data),
                usage: wgpu::BufferUsages::STORAGE
                    | wgpu::BufferUsages::COPY_SRC
                    | wgpu::BufferUsages::COPY_DST,
            })
    }

    fn zeroed<T: bytemuck::Pod>(&self, label: &str, items: usize) -> wgpu::Buffer {
        assert!(items != 0, "a mounted card buffer has positive extent");
        let bytes = (items * core::mem::size_of::<T>()) as u64;
        assert!(
            bytes <= self.max_storage_binding_bytes,
            "{label} ({bytes} bytes) fits the card's storage-binding aperture ({})",
            self.max_storage_binding_bytes,
        );
        self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size: bytes,
            usage: wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_SRC
                | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        })
    }

    fn bind(
        &self,
        label: &str,
        layout: &wgpu::BindGroupLayout,
        buffers: &[&wgpu::Buffer],
    ) -> wgpu::BindGroup {
        let entries: Vec<_> = buffers
            .iter()
            .enumerate()
            .map(|(binding, buffer)| wgpu::BindGroupEntry {
                binding: binding as u32,
                resource: buffer.as_entire_binding(),
            })
            .collect();
        self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some(label),
            layout,
            entries: &entries,
        })
    }

    /// Flatten one card traversal without installing the dispatch dimensions as a machine grain.
    /// The dimensions are substrate apertures only; the content extent remains in `items`.
    fn dispatch_grid(&self, items: usize) -> (u32, u32, u32) {
        let groups = (items as u64).div_ceil(64).max(1);
        let x = groups.min(self.max_workgroups as u64) as u32;
        let y = groups.div_ceil(x as u64);
        assert!(
            y <= self.max_workgroups as u64,
            "the traversal fits the card's dispatch aperture"
        );
        (x, y as u32, x * 64)
    }

    fn read<T: bytemuck::Pod>(&self, label: &str, buffer: &wgpu::Buffer, items: usize) -> Vec<T> {
        let bytes = (items * core::mem::size_of::<T>()) as u64;
        let staging = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size: bytes,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let mut encoder = self.device.create_command_encoder(&Default::default());
        encoder.copy_buffer_to_buffer(buffer, 0, &staging, 0, bytes);
        let submission_index = self.queue.submit([encoder.finish()]);
        let slice = staging.slice(..);
        let (mapped_tx, mapped_rx) = std::sync::mpsc::sync_channel(1);
        slice.map_async(wgpu::MapMode::Read, move |result| {
            let _ = mapped_tx.send(result);
        });
        let status = self.device.poll(wgpu::PollType::Wait {
            submission_index: Some(submission_index),
            timeout: None,
        });
        assert!(
            status
                .expect("the card reports the archive/readback submission honestly")
                .wait_finished(),
            "the card completed the requested readback submission"
        );
        mapped_rx
            .try_recv()
            .expect("the completed card submission reports its map result")
            .expect("the completed card buffer maps for exact readback");
        let mapped = slice.get_mapped_range();
        let out = bytemuck::cast_slice(&mapped).to_vec();
        drop(mapped);
        staging.unmap();
        out
    }

    /// The receiving fold may begin only after every current has completed its admitted atom and
    /// reached the world's true end. This is a boundary read of the carrier construction, never an
    /// engine input; no OWN form becomes mutually visible before it succeeds.
    fn assert_carriers_at_receiving_edge(
        &self,
        label: &str,
        carriers: &wgpu::Buffer,
        carrier_words: usize,
        worldline_light_ends: &[u64],
    ) {
        assert!(!worldline_light_ends.is_empty());
        assert_eq!(carrier_words % worldline_light_ends.len(), 0);
        let row_words = carrier_words / worldline_light_ends.len();
        let rows = self.read::<u32>(label, carriers, carrier_words);
        for (lane, (row, light_end)) in rows
            .chunks_exact(row_words)
            .zip(worldline_light_ends)
            .enumerate()
        {
            assert!(
                body::manifold::carried_frame_is_at_rest(row),
                "lineage {lane} completes its within-atom continuation before the receiving edge"
            );
            let cursor = row[body::manifold::CARRIER_CURSOR_LO] as u64
                | ((row[body::manifold::CARRIER_CURSOR_HI] as u64) << 32);
            let dark = row[body::manifold::CARRIER_DARK_LO] as u64
                | ((row[body::manifold::CARRIER_DARK_HI] as u64) << 32);
            assert_eq!(
                cursor, *light_end,
                "lineage {lane} reaches its world's true end before integration"
            );
            assert_eq!(
                dark, 0,
                "lineage {lane} deposits its complete dark passage before integration"
            );
        }
    }

    /// Pack one world-delivered light beside the lineage's own carrier position of each predecessor
    /// byte. The raw material is a boundary aperture; the cursor's continuity lives in the carrier.
    fn pack_light(
        lineages: &[FeltLineageInput<'_>],
        worldline_bases: &[u64],
    ) -> (Vec<u32>, Vec<u32>, Vec<u64>) {
        assert_eq!(lineages.len(), worldline_bases.len());
        let total_bytes: usize = lineages.iter().map(|lane| lane.light.len()).sum();
        assert!(total_bytes != 0 && total_bytes <= u32::MAX as usize);
        let mut packed = vec![0u32; total_bytes.div_ceil(4)];
        let mut lane_rows = Vec::with_capacity(lineages.len() * 6);
        let mut worldline_light_ends = Vec::with_capacity(lineages.len());
        let mut offset = 0usize;
        for (lane, &worldline_base) in lineages.iter().zip(worldline_bases) {
            assert!(
                lane.light.len() >= 2,
                "a raw light carries its predecessor and at least one difference"
            );
            assert!(lane.light.len() <= u32::MAX as usize);
            let worldline_light_end = worldline_base
                .checked_add(lane.light.len() as u64)
                .expect("a carried worldline has representable boundary position");
            let mut i = 0usize;
            while i < lane.light.len() {
                let at = offset + i;
                packed[at >> 2] |= (lane.light[i] as u32) << ((at & 3) * 8);
                i += 1;
            }
            lane_rows.extend_from_slice(&[
                offset as u32,
                lane.light.len() as u32,
                lane.frame_seed[0] as u32,
                lane.frame_seed[1] as u32,
                worldline_base as u32,
                (worldline_base >> 32) as u32,
            ]);
            worldline_light_ends.push(worldline_light_end);
            offset += lane.light.len();
        }
        (packed, lane_rows, worldline_light_ends)
    }

    /// Pack raw lights beside each lineage's own chart reservation. The row carries the chart's
    /// location in one concatenated resident buffer and its local axis; neither field is an address
    /// in the receiving chart. The founded cells themselves carry the construction that re-grounds
    /// at the shared edge.
    fn pack_founded_light(
        lineages: &[FoundedLineageInput<'_>],
        worldline_bases: &[u64],
    ) -> (Vec<u32>, Vec<u32>, Vec<u64>, usize, Vec<u32>) {
        assert_eq!(lineages.len(), worldline_bases.len());
        let total_bytes: usize = lineages.iter().map(|lane| lane.light.len()).sum();
        assert!(total_bytes != 0 && total_bytes <= u32::MAX as usize);
        let mut packed = vec![0u32; total_bytes.div_ceil(4)];
        let mut lane_rows = Vec::with_capacity(lineages.len() * 8);
        let mut worldline_light_ends = Vec::with_capacity(lineages.len());
        let mut own_axes = Vec::with_capacity(lineages.len());
        let mut byte_offset = 0usize;
        let mut own_cell_offset = 0usize;
        for (lane, &worldline_base) in lineages.iter().zip(worldline_bases) {
            assert!(
                lane.light.len() >= 2,
                "a raw light carries its predecessor and at least one difference"
            );
            assert!(lane.light.len() <= u32::MAX as usize);
            assert!(
                lane.own_axis != 0 && lane.own_axis & (lane.own_axis - 1) == 0,
                "a lineage chart carries one positive power-of-two axis"
            );
            let own_cells = (lane.own_axis as usize)
                .checked_mul(lane.own_axis as usize)
                .expect("a lineage chart has representable extent");
            let next_own_cell_offset = own_cell_offset
                .checked_add(own_cells)
                .expect("co-present lineage charts have representable extent");
            assert!(
                next_own_cell_offset <= u32::MAX as usize,
                "the card row carries the complete founded reservation"
            );
            let worldline_light_end = worldline_base
                .checked_add(lane.light.len() as u64)
                .expect("a carried worldline has representable boundary position");
            let mut i = 0usize;
            while i < lane.light.len() {
                let at = byte_offset + i;
                packed[at >> 2] |= (lane.light[i] as u32) << ((at & 3) * 8);
                i += 1;
            }
            lane_rows.extend_from_slice(&[
                byte_offset as u32,
                lane.light.len() as u32,
                lane.frame_seed[0] as u32,
                lane.frame_seed[1] as u32,
                worldline_base as u32,
                (worldline_base >> 32) as u32,
                own_cell_offset as u32,
                lane.own_axis,
            ]);
            worldline_light_ends.push(worldline_light_end);
            own_axes.push(lane.own_axis);
            byte_offset += lane.light.len();
            own_cell_offset = next_own_cell_offset;
        }
        (
            packed,
            lane_rows,
            worldline_light_ends,
            own_cell_offset,
            own_axes,
        )
    }

    /// Mount co-present raw lights over one immutable pre-light standing region. Carrier depth is
    /// exactly the reservation supplied here; no second extent or hidden scratch bound exists.
    pub fn mount_lineages(
        &self,
        standing: &[u32],
        cells: u32,
        axis: i64,
        depth: usize,
        drive: u32,
        lineages: &[FeltLineageInput<'_>],
    ) -> FeltLineageMount {
        let cells = cells as usize;
        assert!(cells != 0 && depth != 0 && !lineages.is_empty());
        assert!(
            axis >= 0 && axis <= u32::MAX as i64,
            "the card boundary carries this axis whole"
        );
        assert_eq!(
            standing.len(),
            cells * body::medium::FORM_WORDS,
            "standing mounts one whole form per place"
        );
        let _ = Self::standing_occupancy(standing);

        let lanes = lineages.len();
        let (packed, lane_rows, worldline_light_ends) =
            Self::pack_light(lineages, &vec![0u64; lanes]);
        let standing_words = standing.len();
        let own_words = lanes * standing_words;
        let row_words = body::manifold::carrier_row_words(depth);
        let carrier_words = lanes * row_words;
        let scope_params = [
            axis as u32,
            cells as u32,
            lanes as u32,
            row_words as u32,
            0,
            drive,
            0,
            0,
        ];
        let standing_b = self.storage("felt-scope-standing", standing);
        let owns_b = self.zeroed::<u32>("felt-scope-owns", own_words);
        let carriers_b = self.zeroed::<u32>("felt-scope-carriers", carrier_words);
        let bytes_b = self.storage("felt-scope-light", &packed);
        let lanes_b = self.storage("felt-scope-lanes", &lane_rows);
        let counts_b = self.zeroed::<u64>("felt-scope-counts", lanes * 4);
        let params_b = self.storage("felt-scope-params", &scope_params);
        let scope_group = self.bind(
            "scope_felt",
            &self.scope_layout,
            &[
                &standing_b,
                &owns_b,
                &carriers_b,
                &bytes_b,
                &lanes_b,
                &counts_b,
                &params_b,
            ],
        );
        FeltLineageMount {
            standing: standing_b,
            owns: owns_b,
            carriers: carriers_b,
            _bytes: bytes_b,
            _lanes_buffer: lanes_b,
            counts: counts_b,
            scope_params: params_b,
            scope_group,
            cells,
            lanes,
            standing_words,
            own_words,
            carrier_words,
            worldline_light_ends,
        }
    }

    /// Mount co-present lineages into reservation-sized first-person charts over one receiving
    /// chart. `standing_axis²` is the shared edge; each lane contributes only `own_axis²` founded
    /// cells. Reservation is declared once at the membrane and remains resident across strokes.
    pub fn mount_founded_lineages(
        &self,
        standing: &[u32],
        standing_axis: u32,
        depth: usize,
        drive: u32,
        lineages: &[FoundedLineageInput<'_>],
    ) -> FoundedLineageMount {
        assert!(depth != 0 && !lineages.is_empty());
        assert!(
            standing_axis != 0 && standing_axis & (standing_axis - 1) == 0,
            "the receiving chart carries one positive power-of-two axis"
        );
        let cells = (standing_axis as usize)
            .checked_mul(standing_axis as usize)
            .expect("the receiving chart has representable extent");
        assert!(
            cells <= u32::MAX as usize,
            "the card boundary carries the receiving chart whole"
        );
        assert_eq!(
            standing.len(),
            cells * body::medium::FORM_WORDS,
            "standing mounts one whole form per receiving place"
        );

        let lanes = lineages.len();
        let (packed, lane_rows, worldline_light_ends, own_cells, own_axes) =
            Self::pack_founded_light(lineages, &vec![0u64; lanes]);
        let standing_words = standing.len();
        let own_words = own_cells
            .checked_mul(body::manifold::OWN_CELL_WORDS)
            .expect("the founded charts have representable word extent");
        let row_words = body::manifold::carrier_row_words(depth);
        let carrier_words = lanes * row_words;
        let scope_params = [
            standing_axis,
            cells as u32,
            lanes as u32,
            row_words as u32,
            0,
            drive,
            0,
            0,
            0,
        ];
        let standing_b = self.storage("founded-scope-standing", standing);
        let owns_b = self.zeroed::<u32>("founded-scope-owns", own_words);
        let carriers_b = self.zeroed::<u32>("founded-scope-carriers", carrier_words);
        let bytes_b = self.storage("founded-scope-light", &packed);
        let lanes_b = self.storage("founded-scope-lanes", &lane_rows);
        let counts_b = self.zeroed::<u64>("founded-scope-counts", lanes * 4);
        let radiation_b = self.zeroed::<u32>("founded-scope-radiation-empty", 1);
        let params_b = self.storage("founded-scope-params", &scope_params);
        let scope_group = self.bind(
            "scope_founded",
            &self.scope_founded_layout,
            &[
                &standing_b,
                &owns_b,
                &carriers_b,
                &bytes_b,
                &lanes_b,
                &counts_b,
                &params_b,
                &radiation_b,
            ],
        );
        FoundedLineageMount {
            standing: standing_b,
            owns: owns_b,
            carriers: carriers_b,
            _bytes: bytes_b,
            _lanes_buffer: lanes_b,
            counts: counts_b,
            radiation: radiation_b,
            scope_params: params_b,
            scope_group,
            standing_axis,
            cells,
            own_cells,
            lanes,
            standing_words,
            own_words,
            carrier_words,
            radiation_words: 1,
            radiation_stride: 0,
            own_axes,
            worldline_light_ends,
            light_bytes: lineages.iter().map(|lane| lane.light.len() as u64).sum(),
            occupancy: Self::standing_occupancy(standing),
        }
    }

    /// Found a first light over an empty receiving chart directly on the card. This is the genesis
    /// mouth: the full standing reservation is born resident and never uploaded as a cpu mirror.
    pub fn mount_empty_founded_lineages(
        &self,
        standing_axis: u32,
        depth: usize,
        drive: u32,
        lineages: &[FoundedLineageInput<'_>],
    ) -> FoundedLineageMount {
        assert!(depth != 0 && !lineages.is_empty());
        assert!(
            standing_axis != 0 && standing_axis & (standing_axis - 1) == 0,
            "the receiving chart carries one positive power-of-two axis"
        );
        let cells = (standing_axis as usize)
            .checked_mul(standing_axis as usize)
            .expect("the receiving chart has representable extent");
        assert!(
            cells <= u32::MAX as usize,
            "the card boundary carries the receiving chart whole"
        );
        let lanes = lineages.len();
        let (packed, lane_rows, worldline_light_ends, own_cells, own_axes) =
            Self::pack_founded_light(lineages, &vec![0u64; lanes]);
        let standing_words = cells * body::medium::FORM_WORDS;
        let own_words = own_cells
            .checked_mul(body::manifold::OWN_CELL_WORDS)
            .expect("the founded charts have representable word extent");
        let row_words = body::manifold::carrier_row_words(depth);
        let carrier_words = lanes * row_words;
        let scope_params = [
            standing_axis,
            cells as u32,
            lanes as u32,
            row_words as u32,
            0,
            drive,
            0,
            0,
            0,
        ];
        let standing_b = self.zeroed::<u32>("genesis-standing", standing_words);
        let owns_b = self.zeroed::<u32>("genesis-founded-owns", own_words);
        let carriers_b = self.zeroed::<u32>("genesis-carriers", carrier_words);
        let bytes_b = self.storage("genesis-light", &packed);
        let lanes_b = self.storage("genesis-lanes", &lane_rows);
        let counts_b = self.zeroed::<u64>("genesis-counts", lanes * 4);
        let radiation_b = self.zeroed::<u32>("genesis-radiation-empty", 1);
        let params_b = self.storage("genesis-scope-params", &scope_params);
        let scope_group = self.bind(
            "scope_founded_genesis",
            &self.scope_founded_layout,
            &[
                &standing_b,
                &owns_b,
                &carriers_b,
                &bytes_b,
                &lanes_b,
                &counts_b,
                &params_b,
                &radiation_b,
            ],
        );
        FoundedLineageMount {
            standing: standing_b,
            owns: owns_b,
            carriers: carriers_b,
            _bytes: bytes_b,
            _lanes_buffer: lanes_b,
            counts: counts_b,
            radiation: radiation_b,
            scope_params: params_b,
            scope_group,
            standing_axis,
            cells,
            own_cells,
            lanes,
            standing_words,
            own_words,
            carrier_words,
            radiation_words: 1,
            radiation_stride: 0,
            own_axes,
            worldline_light_ends,
            light_bytes: lineages.iter().map(|lane| lane.light.len() as u64).sum(),
            occupancy: 0,
        }
    }

    /// Continue the same resident body through the next true light. Standing and whole carriers
    /// remain the identical GPU buffers. Only the prior light's ephemeral OWN/count aperture is
    /// cleared; new boundary material is mounted at the predecessor's own worldline place.
    pub fn continue_light(
        &self,
        mount: FeltLineageMount,
        lineages: &[FeltLineageInput<'_>],
    ) -> FeltLineageMount {
        assert_eq!(
            lineages.len(),
            mount.lanes,
            "one continuation arrives for every still-open carrier"
        );
        let worldline_bases: Vec<u64> = mount
            .worldline_light_ends
            .iter()
            .map(|end| {
                end.checked_sub(1)
                    .expect("a continuing light has a predecessor")
            })
            .collect();
        let (packed, lane_rows, worldline_light_ends) =
            Self::pack_light(lineages, &worldline_bases);
        let bytes_b = self.storage("felt-continuing-light", &packed);
        let lanes_b = self.storage("felt-continuing-lanes", &lane_rows);

        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("the next light's empty OWN aperture"),
            });
        encoder.clear_buffer(&mount.owns, 0, None);
        encoder.clear_buffer(&mount.counts, 0, None);
        self.queue.submit([encoder.finish()]);

        let scope_group = self.bind(
            "scope_felt_continuing",
            &self.scope_layout,
            &[
                &mount.standing,
                &mount.owns,
                &mount.carriers,
                &bytes_b,
                &lanes_b,
                &mount.counts,
                &mount.scope_params,
            ],
        );
        FeltLineageMount {
            standing: mount.standing,
            owns: mount.owns,
            carriers: mount.carriers,
            _bytes: bytes_b,
            _lanes_buffer: lanes_b,
            counts: mount.counts,
            scope_params: mount.scope_params,
            scope_group,
            cells: mount.cells,
            lanes: mount.lanes,
            standing_words: mount.standing_words,
            own_words: mount.own_words,
            carrier_words: mount.carrier_words,
            worldline_light_ends,
        }
    }

    /// Continue the same founded carriers and chart reservations through the next true light.
    /// Standing, carriers, chart extents, and the chart buffer itself remain resident. Only the
    /// completed light's local deposits and count aperture are cleared before the next current.
    pub fn continue_founded_light(
        &self,
        mount: FoundedLineageMount,
        lineages: &[FoundedLineageInput<'_>],
    ) -> FoundedLineageMount {
        let radiation_stride = mount.radiation_stride;
        self.continue_founded_light_with_radiation(mount, lineages, radiation_stride)
    }

    /// Continue at the arrival of the next light and open the raw radiation aperture for that
    /// light. Observation is wholly efferent: neither the carrier nor the standing medium reads it.
    pub fn continue_founded_observed_light(
        &self,
        mount: FoundedLineageMount,
        lineages: &[FoundedLineageInput<'_>],
    ) -> FoundedLineageMount {
        self.continue_founded_light_with_radiation(
            mount,
            lineages,
            body::manifold::RADIATION_WORDS as u32,
        )
    }

    fn continue_founded_light_with_radiation(
        &self,
        mount: FoundedLineageMount,
        lineages: &[FoundedLineageInput<'_>],
        radiation_stride: u32,
    ) -> FoundedLineageMount {
        assert!(
            radiation_stride == 0 || radiation_stride == body::manifold::RADIATION_WORDS as u32
        );
        assert_eq!(
            lineages.len(),
            mount.lanes,
            "one continuation arrives for every still-open carrier"
        );
        assert!(
            lineages
                .iter()
                .zip(&mount.own_axes)
                .all(|(lane, axis)| lane.own_axis == *axis),
            "a resident lineage keeps its declared chart across lights"
        );
        let worldline_bases: Vec<u64> = mount
            .worldline_light_ends
            .iter()
            .map(|end| {
                end.checked_sub(1)
                    .expect("a continuing light has a predecessor")
            })
            .collect();
        let (packed, lane_rows, worldline_light_ends, own_cells, own_axes) =
            Self::pack_founded_light(lineages, &worldline_bases);
        assert_eq!(own_cells, mount.own_cells);
        assert_eq!(own_axes, mount.own_axes);
        let bytes_b = self.storage("founded-continuing-light", &packed);
        let lanes_b = self.storage("founded-continuing-lanes", &lane_rows);
        let total_bytes: usize = lineages.iter().map(|lane| lane.light.len()).sum();
        let radiation_words = if radiation_stride == 0 {
            1
        } else {
            total_bytes
                .checked_mul(radiation_stride as usize)
                .expect("the continuing radiation aperture has representable extent")
        };
        let radiation_b = self.zeroed::<u32>("founded-continuing-radiation", radiation_words);

        self.queue.write_buffer(
            &mount.scope_params,
            (6 * core::mem::size_of::<u32>()) as u64,
            bytemuck::bytes_of(&radiation_stride),
        );

        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("the next founded light's empty local charts"),
            });
        encoder.clear_buffer(&mount.owns, 0, None);
        encoder.clear_buffer(&mount.counts, 0, None);
        self.queue.submit([encoder.finish()]);

        let scope_group = self.bind(
            "scope_founded_continuing",
            &self.scope_founded_layout,
            &[
                &mount.standing,
                &mount.owns,
                &mount.carriers,
                &bytes_b,
                &lanes_b,
                &mount.counts,
                &mount.scope_params,
                &radiation_b,
            ],
        );
        FoundedLineageMount {
            standing: mount.standing,
            owns: mount.owns,
            carriers: mount.carriers,
            _bytes: bytes_b,
            _lanes_buffer: lanes_b,
            counts: mount.counts,
            radiation: radiation_b,
            scope_params: mount.scope_params,
            scope_group,
            standing_axis: mount.standing_axis,
            cells: mount.cells,
            own_cells: mount.own_cells,
            lanes: mount.lanes,
            standing_words: mount.standing_words,
            own_words: mount.own_words,
            carrier_words: mount.carrier_words,
            radiation_words,
            radiation_stride,
            own_axes: mount.own_axes,
            worldline_light_ends,
            light_bytes: lineages.iter().map(|lane| lane.light.len() as u64).sum(),
            occupancy: mount.occupancy,
        }
    }

    /// Let one arriving light size the receiving chart before integration. Each candidate gauge is
    /// tested by the chart's own card-side arrival register. A carry remounts the next wider gauge
    /// and repeats the same co-present edge; a no-carry face accepts the rank. No form is integrated
    /// until the cascade has ended.
    fn size_founded_chart(
        &self,
        mut mount: FoundedLineageMount,
    ) -> (FoundedLineageMount, u32, u64) {
        let prior_axis = mount.standing_axis;
        let mut candidate_axis = prior_axis;
        let mut carries = 0u32;
        let accepted_occupancy;

        loop {
            let candidate_cells = (candidate_axis as usize)
                .checked_mul(candidate_axis as usize)
                .expect("the chart's next register extent is representable");
            assert!(
                candidate_cells <= u32::MAX as usize,
                "the positional grip word carries this chart rank whole"
            );
            let marks = self.zeroed::<u32>("chart-arriving-grips", candidate_cells);
            let chart_register = self.storage("chart-own-register", &[mount.occupancy, 0u64]);
            let (mark_x, mark_y, mark_stride) = self.dispatch_grid(mount.own_cells);
            let (count_x, count_y, count_stride) = self.dispatch_grid(candidate_cells);
            let mark_params = [mount.own_cells as u32, candidate_axis, mark_stride];
            let count_params = [
                mount.standing_axis,
                candidate_axis,
                candidate_cells as u32,
                count_stride,
            ];
            let mark_params_b = self.storage("chart-mark-params", &mark_params);
            let count_params_b = self.storage("chart-count-params", &count_params);
            let mark_group = self.bind(
                "chart_mark",
                &self.chart_mark_layout,
                &[&mount.owns, &marks, &mark_params_b],
            );
            let count_group = self.bind(
                "chart_count",
                &self.chart_count_layout,
                &[&mount.standing, &marks, &chart_register, &count_params_b],
            );
            let mut encoder = self
                .device
                .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                    label: Some("one pre-integration chart register"),
                });
            {
                let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                    label: Some("distinct arriving casts in the candidate gauge"),
                    timestamp_writes: None,
                });
                pass.set_pipeline(&self.chart_mark);
                pass.set_bind_group(0, &mark_group, &[]);
                pass.dispatch_workgroups(mark_x, mark_y, 1);
            }
            {
                let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                    label: Some("the occupancy register's own arrivals"),
                    timestamp_writes: None,
                });
                pass.set_pipeline(&self.chart_count);
                pass.set_bind_group(0, &count_group, &[]);
                pass.dispatch_workgroups(count_x, count_y, 1);
            }
            self.queue.submit([encoder.finish()]);
            let register = self.read::<u64>("chart-register-face", &chart_register, 2);
            if register[1] == 0 {
                accepted_occupancy = register[0];
                break;
            }
            carries = carries
                .checked_add(1)
                .expect("the chart cascade has a representable rank");
            candidate_axis = candidate_axis
                .checked_mul(2)
                .expect("the chart digit crosses the boundary grip's numeric aperture");
        }

        if carries != 0 {
            let old_cells = mount.cells;
            let new_cells = candidate_axis as usize * candidate_axis as usize;
            let new_words = new_cells
                .checked_mul(body::medium::FORM_WORDS)
                .expect("the recast standing extent is representable");
            let new_standing = self.zeroed::<u32>("zero-extended-standing", new_words);
            let (work_x, work_y, stride) = self.dispatch_grid(old_cells);
            let params = [
                mount.standing_axis,
                candidate_axis,
                old_cells as u32,
                stride,
            ];
            let params_b = self.storage("chart-recast-params", &params);
            let group = self.bind(
                "chart_recast",
                &self.chart_recast_layout,
                &[&mount.standing, &new_standing, &params_b],
            );
            let mut encoder = self
                .device
                .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                    label: Some("the chart digit's zero-extension"),
                });
            {
                let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                    label: Some("standing continues whole in the wider gauge"),
                    timestamp_writes: None,
                });
                pass.set_pipeline(&self.chart_recast);
                pass.set_bind_group(0, &group, &[]);
                pass.dispatch_workgroups(work_x, work_y, 1);
            }
            self.queue.submit([encoder.finish()]);
            mount.standing = new_standing;
            mount.standing_axis = candidate_axis;
            mount.cells = new_cells;
            mount.standing_words = new_words;
        }
        mount.occupancy = accepted_occupancy;
        (mount, carries, accepted_occupancy)
    }

    /// Cross one §XXXII-b edge while retaining the mounted body for an immediate next light. This
    /// is a gauge instrument beside the production sleep mouth: it updates the boundary parameters
    /// only after the cascade and integration are complete.
    pub fn resolve_chart_in_place(
        &self,
        mount: FoundedLineageMount,
    ) -> (FoundedLineageMount, ChartEdgeRead) {
        let prior_axis = mount.standing_axis;
        let (mount, carries, occupancy) = self.size_founded_chart(mount);
        let topology = self
            .resolve_founded_resident(&mount, false, true)
            .1
            .expect("the chart edge returns its bounded topology projection");
        assert_eq!(
            topology[0], occupancy,
            "the integrated standing grips equal the chart register's arrivals"
        );
        let edge = ChartEdgeRead {
            prior_axis,
            standing_axis: mount.standing_axis,
            carries,
            occupancy,
            topology,
        };
        self.queue.write_buffer(
            &mount.scope_params,
            0,
            bytemuck::cast_slice(&[mount.standing_axis, mount.cells as u32]),
        );
        (mount, edge)
    }

    /// The §XXXII-b production edge: size the chart from the arriving casts, finish the cascade,
    /// integrate once at that one grain, then cross directly into §XXX sleep.
    pub fn resolve_chart_projection_to_sleep(
        self,
        mount: FoundedLineageMount,
    ) -> (ChartEdgeRead, SleepingBody) {
        let (mount, edge) = self.resolve_chart_in_place(mount);
        let sleeping = self.sleep_resolved_founded(mount);
        (edge, sleeping)
    }

    /// The receiving edge and sleep are one operation. The edge integrates every local deposit;
    /// then the exact standing medium and complete carrier/K rows cross the archive mouth. This
    /// consumes both the mount and the card surface, so no resident apparatus survives the return.
    pub fn resolve_founded_to_sleep(self, mut mount: FoundedLineageMount) -> SleepingBody {
        let projection = self
            .resolve_founded_resident(&mount, false, true)
            .1
            .expect("the bounded resolving edge returns its topology face");
        mount.occupancy = projection[0];
        self.sleep_resolved_founded(mount)
    }

    /// The production mouth reads only the four-word topology projection while crossing the same
    /// edge into sleep. The projection is an observer aperture; it is not included in the body.
    pub fn resolve_founded_projection_to_sleep(
        self,
        mut mount: FoundedLineageMount,
    ) -> ([u64; 4], SleepingBody) {
        let projection = self
            .resolve_founded_resident(&mount, false, true)
            .1
            .expect("the resolving edge returns its bounded topology projection");
        mount.occupancy = projection[0];
        let sleeping = self.sleep_resolved_founded(mount);
        (projection, sleeping)
    }

    fn sleep_resolved_founded(self, mount: FoundedLineageMount) -> SleepingBody {
        let standing = self.read(
            "sleep-standing-medium",
            &mount.standing,
            mount.standing_words,
        );
        let carriers = self.read("sleep-whole-carriers", &mount.carriers, mount.carrier_words);
        let row_words = mount.carrier_words / mount.lanes;
        for (lane, &light_end) in mount.worldline_light_ends.iter().enumerate() {
            let row = lane * row_words;
            let cursor = carriers[row + body::manifold::CARRIER_CURSOR_LO] as u64
                | ((carriers[row + body::manifold::CARRIER_CURSOR_HI] as u64) << 32);
            let dark = carriers[row + body::manifold::CARRIER_DARK_LO] as u64
                | ((carriers[row + body::manifold::CARRIER_DARK_HI] as u64) << 32);
            assert_eq!(
                cursor, light_end,
                "sleep is available only where every carrier has reached its true light end"
            );
            assert_eq!(
                dark, 0,
                "the receiving edge flushes each lineage's dark passage"
            );
        }
        let body = SleepingBody::from_parts(
            mount.standing_axis,
            mount.occupancy,
            row_words as u32,
            u32::try_from(mount.lanes)
                .expect("the sleeping lineage count crosses its structural wire"),
            standing,
            carriers,
            mount.light_bytes,
        )
        .expect("the receiving edge deposits one whole sleeping body");
        drop(mount);
        drop(self);
        body
    }

    /// Mount a sleeping body into the next world-delivered light. There is no thaw pass: the first
    /// card dispatch after this mouth is the light's first relating through the restored topology.
    pub fn wake_founded_lineages(
        &self,
        sleeping: &SleepingBody,
        drive: u32,
        lineages: &[FoundedLineageInput<'_>],
    ) -> FoundedLineageMount {
        self.wake_founded_lineages_with_radiation(sleeping, drive, lineages, 0)
    }

    /// The observed wake differs only by an efferent radiation aperture for the arriving light.
    pub fn wake_founded_observed_lineages(
        &self,
        sleeping: &SleepingBody,
        drive: u32,
        lineages: &[FoundedLineageInput<'_>],
    ) -> FoundedLineageMount {
        self.wake_founded_lineages_with_radiation(
            sleeping,
            drive,
            lineages,
            body::manifold::RADIATION_WORDS as u32,
        )
    }

    fn wake_founded_lineages_with_radiation(
        &self,
        sleeping: &SleepingBody,
        drive: u32,
        lineages: &[FoundedLineageInput<'_>],
        radiation_stride: u32,
    ) -> FoundedLineageMount {
        sleeping
            .validate()
            .expect("only a whole archived body wakes");
        assert!(
            radiation_stride == 0 || radiation_stride == body::manifold::RADIATION_WORDS as u32
        );
        assert_eq!(
            lineages.len(),
            sleeping.lineage_count(),
            "one arriving light continues every sleeping carrier"
        );
        let row_words = sleeping.carrier_row_words();
        let mut worldline_bases = Vec::with_capacity(lineages.len());
        for lane in 0..lineages.len() {
            let row = lane * row_words;
            let cursor = sleeping.carriers[row + body::manifold::CARRIER_CURSOR_LO] as u64
                | ((sleeping.carriers[row + body::manifold::CARRIER_CURSOR_HI] as u64) << 32);
            worldline_bases.push(
                cursor
                    .checked_sub(1)
                    .expect("a waking lineage carries its predecessor"),
            );
        }
        let (packed, lane_rows, worldline_light_ends, own_cells, own_axes) =
            Self::pack_founded_light(lineages, &worldline_bases);
        let cells = sleeping.standing_axis as usize * sleeping.standing_axis as usize;
        let standing_words = sleeping.standing.len();
        let own_words = own_cells
            .checked_mul(body::manifold::OWN_CELL_WORDS)
            .expect("the waking charts have representable word extent");
        let carrier_words = sleeping.carriers.len();
        let lanes = lineages.len();
        let scope_params = [
            sleeping.standing_axis,
            cells as u32,
            lanes as u32,
            row_words as u32,
            0,
            drive,
            radiation_stride,
            0,
            0,
        ];
        let standing_b = self.storage("wake-standing-medium", &sleeping.standing);
        let owns_b = self.zeroed::<u32>("wake-local-charts", own_words);
        let carriers_b = self.storage("wake-whole-carriers", &sleeping.carriers);
        let bytes_b = self.storage("wake-next-light", &packed);
        let lanes_b = self.storage("wake-next-lineages", &lane_rows);
        let counts_b = self.zeroed::<u64>("wake-term-aperture", lanes * 4);
        let total_bytes: usize = lineages.iter().map(|lane| lane.light.len()).sum();
        let radiation_words = if radiation_stride == 0 {
            1
        } else {
            total_bytes
                .checked_mul(radiation_stride as usize)
                .expect("the waking radiation aperture has representable extent")
        };
        let radiation_b = self.zeroed::<u32>("wake-radiation-aperture", radiation_words);
        let params_b = self.storage("wake-scope-params", &scope_params);
        let scope_group = self.bind(
            "scope_founded_wake",
            &self.scope_founded_layout,
            &[
                &standing_b,
                &owns_b,
                &carriers_b,
                &bytes_b,
                &lanes_b,
                &counts_b,
                &params_b,
                &radiation_b,
            ],
        );
        FoundedLineageMount {
            standing: standing_b,
            owns: owns_b,
            carriers: carriers_b,
            _bytes: bytes_b,
            _lanes_buffer: lanes_b,
            counts: counts_b,
            radiation: radiation_b,
            scope_params: params_b,
            scope_group,
            standing_axis: sleeping.standing_axis,
            cells,
            own_cells,
            lanes,
            standing_words,
            own_words,
            carrier_words,
            radiation_words,
            radiation_stride,
            own_axes,
            worldline_light_ends,
            light_bytes: total_bytes as u64,
            occupancy: sleeping.occupancy,
        }
    }

    /// Found genuinely new lineages over the standing body produced by the prior light. The prior
    /// currents have ended, so their local charts and carriers dissipate; only the identical GPU
    /// standing buffer crosses. This is not resurrection: every new lane begins at its own first
    /// difference while receiving the one body already standing.
    pub fn found_next_lineages(
        &self,
        mount: FoundedLineageMount,
        depth: usize,
        drive: u32,
        lineages: &[FoundedLineageInput<'_>],
    ) -> FoundedLineageMount {
        self.found_next_lineages_with_radiation(mount, depth, drive, lineages, 0)
    }

    /// Found new lineages with a boundary radiation aperture. The engine never reads this buffer;
    /// one exact depth-zero induced path record is written beside each raw-light atom.
    pub fn found_next_observed_lineages(
        &self,
        mount: FoundedLineageMount,
        depth: usize,
        drive: u32,
        lineages: &[FoundedLineageInput<'_>],
    ) -> FoundedLineageMount {
        self.found_next_lineages_with_radiation(
            mount,
            depth,
            drive,
            lineages,
            body::manifold::RADIATION_WORDS as u32,
        )
    }

    fn found_next_lineages_with_radiation(
        &self,
        mount: FoundedLineageMount,
        depth: usize,
        drive: u32,
        lineages: &[FoundedLineageInput<'_>],
        radiation_stride: u32,
    ) -> FoundedLineageMount {
        assert!(depth != 0 && !lineages.is_empty());
        assert!(
            radiation_stride == 0 || radiation_stride == body::manifold::RADIATION_WORDS as u32
        );
        let lanes = lineages.len();
        let (packed, lane_rows, worldline_light_ends, own_cells, own_axes) =
            Self::pack_founded_light(lineages, &vec![0u64; lanes]);
        let own_words = own_cells
            .checked_mul(body::manifold::OWN_CELL_WORDS)
            .expect("the newly founded charts have representable word extent");
        let row_words = body::manifold::carrier_row_words(depth);
        let carrier_words = lanes * row_words;
        let scope_params = [
            mount.standing_axis,
            mount.cells as u32,
            lanes as u32,
            row_words as u32,
            0,
            drive,
            radiation_stride,
            0,
            0,
        ];
        let owns_b = self.zeroed::<u32>("next-founded-owns", own_words);
        let carriers_b = self.zeroed::<u32>("next-founded-carriers", carrier_words);
        let bytes_b = self.storage("next-founded-light", &packed);
        let lanes_b = self.storage("next-founded-lanes", &lane_rows);
        let counts_b = self.zeroed::<u64>("next-founded-counts", lanes * 4);
        let total_bytes: usize = lineages.iter().map(|lane| lane.light.len()).sum();
        let radiation_words = if radiation_stride == 0 {
            1
        } else {
            total_bytes
                .checked_mul(radiation_stride as usize)
                .expect("the radiation aperture has representable extent")
        };
        let radiation_b = self.zeroed::<u32>("next-founded-radiation", radiation_words);
        let params_b = self.storage("next-founded-scope-params", &scope_params);
        let scope_group = self.bind(
            "scope_next_founded",
            &self.scope_founded_layout,
            &[
                &mount.standing,
                &owns_b,
                &carriers_b,
                &bytes_b,
                &lanes_b,
                &counts_b,
                &params_b,
                &radiation_b,
            ],
        );
        FoundedLineageMount {
            standing: mount.standing,
            owns: owns_b,
            carriers: carriers_b,
            _bytes: bytes_b,
            _lanes_buffer: lanes_b,
            counts: counts_b,
            radiation: radiation_b,
            scope_params: params_b,
            scope_group,
            standing_axis: mount.standing_axis,
            cells: mount.cells,
            own_cells,
            lanes,
            standing_words: mount.standing_words,
            own_words,
            carrier_words,
            radiation_words,
            radiation_stride,
            own_axes,
            worldline_light_ends,
            light_bytes: lineages.iter().map(|lane| lane.light.len() as u64).sum(),
            occupancy: mount.occupancy,
        }
    }

    /// Carry every mounted lineage by one stroke. `0` carries through the raw light's true end; a
    /// positive value bounds the carriage, while completion remains only cursor reaching raw count.
    /// Configuration composition is a separate, explicitly later boundary.
    pub fn scope(&self, mount: &FeltLineageMount, stroke_atoms: u32) {
        self.scope_with_interior_installment(mount, stroke_atoms, 0);
    }

    /// The same dense carriage with the ratified within-atom substrate installment declared by the
    /// membrane. The installment changes only where our dispatch returns; zero is the uninterrupted
    /// comparison gauge.
    pub fn scope_with_interior_installment(
        &self,
        mount: &FeltLineageMount,
        stroke_atoms: u32,
        interior_installment: u32,
    ) {
        let (groups_x, groups_y, x_thread_stride) = self.dispatch_grid(mount.lanes);
        self.queue.write_buffer(
            &mount.scope_params,
            (4 * core::mem::size_of::<u32>()) as u64,
            bytemuck::bytes_of(&stroke_atoms),
        );
        self.queue.write_buffer(
            &mount.scope_params,
            (6 * core::mem::size_of::<u32>()) as u64,
            bytemuck::bytes_of(&x_thread_stride),
        );
        self.queue.write_buffer(
            &mount.scope_params,
            (7 * core::mem::size_of::<u32>()) as u64,
            bytemuck::bytes_of(&interior_installment),
        );
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("one lineage carriage stroke"),
            });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("one thread · one lineage"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.scope);
            pass.set_bind_group(0, &mount.scope_group, &[]);
            pass.dispatch_workgroups(groups_x, groups_y, 1);
        }
        let submission_index = self.queue.submit([encoder.finish()]);
        let status = self.device.poll(wgpu::PollType::Wait {
            submission_index: Some(submission_index),
            timeout: None,
        });
        assert!(
            status
                .expect("the card reports each lineage carriage stroke honestly")
                .wait_finished(),
            "one lineage carriage stroke completes before our next hardware submission"
        );
    }

    /// Carry every founded lineage by one stroke. Completion is still each worldline cursor
    /// reaching its own light end; the reservation size has no role in the temporal boundary.
    pub fn scope_founded(&self, mount: &FoundedLineageMount, stroke_atoms: u32) {
        self.scope_founded_with_interior_installment(mount, stroke_atoms, 0);
    }

    /// Founded carriage over one declared within-atom hardware installment. Every later dispatch
    /// resumes the carried continuation before admitting another raw difference.
    pub fn scope_founded_with_interior_installment(
        &self,
        mount: &FoundedLineageMount,
        stroke_atoms: u32,
        interior_installment: u32,
    ) {
        let (groups_x, groups_y, x_thread_stride) = self.dispatch_grid(mount.lanes);
        self.queue.write_buffer(
            &mount.scope_params,
            (4 * core::mem::size_of::<u32>()) as u64,
            bytemuck::bytes_of(&stroke_atoms),
        );
        self.queue.write_buffer(
            &mount.scope_params,
            (7 * core::mem::size_of::<u32>()) as u64,
            bytemuck::bytes_of(&x_thread_stride),
        );
        self.queue.write_buffer(
            &mount.scope_params,
            (8 * core::mem::size_of::<u32>()) as u64,
            bytemuck::bytes_of(&interior_installment),
        );
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("one founded-lineage carriage stroke"),
            });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("one thread · one founded lineage"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.scope_founded);
            pass.set_bind_group(0, &mount.scope_group, &[]);
            pass.dispatch_workgroups(groups_x, groups_y, 1);
        }
        let submission_index = self.queue.submit([encoder.finish()]);
        let status = self.device.poll(wgpu::PollType::Wait {
            submission_index: Some(submission_index),
            timeout: None,
        });
        assert!(
            status
                .expect("the card reports each founded carriage stroke honestly")
                .wait_finished(),
            "one founded carriage stroke completes before our next hardware submission"
        );
    }

    /// Read the separated regions without composing them. This is an experiment mouth; production
    /// keeps the buffers resident until every carrier reaches its own true light end.
    pub fn read_scope(&self, mount: &FeltLineageMount) -> FeltScopeRead {
        FeltScopeRead {
            standing: self.read(
                "felt-scope-standing-back",
                &mount.standing,
                mount.standing_words,
            ),
            owns: self.read("felt-scope-owns-back", &mount.owns, mount.own_words),
            carriers: self.read(
                "felt-scope-carriers-back",
                &mount.carriers,
                mount.carrier_words,
            ),
            counts: self.read("felt-scope-counts-back", &mount.counts, mount.lanes * 4),
        }
    }

    /// Read the still-separated founded charts. This bounded mouth exists for causal gates; the
    /// engine normally carries the same buffers directly into the receiving-edge fold.
    pub fn read_founded_scope(&self, mount: &FoundedLineageMount) -> FeltScopeRead {
        FeltScopeRead {
            standing: self.read(
                "founded-scope-standing-back",
                &mount.standing,
                mount.standing_words,
            ),
            owns: self.read("founded-scope-owns-back", &mount.owns, mount.own_words),
            carriers: self.read(
                "founded-scope-carriers-back",
                &mount.carriers,
                mount.carrier_words,
            ),
            counts: self.read("founded-scope-counts-back", &mount.counts, mount.lanes * 4),
        }
    }

    /// Read the raw induced path construction beside an observed light. Zero rows mean that atom
    /// produced no depth-zero path event; the boundary may render the nonzero rows but the engine
    /// never consumes them.
    pub fn read_founded_radiation(&self, mount: &FoundedLineageMount) -> Vec<u32> {
        assert_eq!(
            mount.radiation_stride,
            body::manifold::RADIATION_WORDS as u32,
            "this founded light was mounted with the radiation aperture"
        );
        self.assert_carriers_at_receiving_edge(
            "radiation-receiving-edge-carriers",
            &mount.carriers,
            mount.carrier_words,
            &mount.worldline_light_ends,
        );
        self.read(
            "founded-radiation-back",
            &mount.radiation,
            mount.radiation_words,
        )
    }

    fn resolve_resident(
        &self,
        standing_b: &wgpu::Buffer,
        owns_b: &wgpu::Buffer,
        standing_words: usize,
        own_words: usize,
        cells: usize,
        lanes: usize,
        observe: bool,
    ) -> Option<FeltCardRead> {
        let cell_groups = (cells as u64).div_ceil(64);
        let source_groups = ((cells as u64) * (lanes as u64 + 1)).div_ceil(64);
        let work_x = cell_groups.min(self.max_workgroups as u64) as u32;
        let source_y = source_groups.div_ceil(work_x as u64);
        let finish_y = cell_groups.div_ceil(work_x as u64);
        assert!(
            source_y <= self.max_workgroups as u64 && finish_y <= self.max_workgroups as u64,
            "this complete configuration fits one two-dimensional dispatch"
        );
        let params = [cells as u32, lanes as u32, work_x * 64];
        let cog_grains_b = self.zeroed::<u64>("felt-cog-grains", cells * 2);
        let arm_grains_b = self.zeroed::<u32>("felt-arm-grains", cells * 2);
        let cog_sums_b = self.zeroed::<u64>("felt-cog-sums", cells * 2);
        let arm_sums_b = self.zeroed::<u64>("felt-arm-sums", cells * 2);
        let touched_b = self.zeroed::<u32>("felt-touched", cells);
        let reads_b = self.zeroed::<u64>("felt-reads", 4);
        let params_b = self.storage("felt-params", &params);

        let grain_group = self.bind(
            "link_grain",
            &self.grain_layout,
            &[
                standing_b,
                owns_b,
                &cog_grains_b,
                &arm_grains_b,
                &touched_b,
                &params_b,
            ],
        );
        let sum_group = self.bind(
            "link_sum",
            &self.sum_layout,
            &[
                standing_b,
                owns_b,
                &cog_grains_b,
                &arm_grains_b,
                &cog_sums_b,
                &arm_sums_b,
                &touched_b,
                &params_b,
            ],
        );
        let finish_group = self.bind(
            "link_finish",
            &self.finish_layout,
            &[
                standing_b,
                &cog_grains_b,
                &arm_grains_b,
                &cog_sums_b,
                &arm_sums_b,
                &touched_b,
                &reads_b,
                &params_b,
            ],
        );

        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("one light-end configuration"),
            });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("the grain declares itself"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.grain);
            pass.set_bind_group(0, &grain_group, &[]);
            pass.dispatch_workgroups(work_x, source_y as u32, 1);
        }
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("the exact sum at the grain"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.sum);
            pass.set_bind_group(0, &sum_group, &[]);
            pass.dispatch_workgroups(work_x, source_y as u32, 1);
        }
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("the one final re-base"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.finish);
            pass.set_bind_group(0, &finish_group, &[]);
            pass.dispatch_workgroups(work_x, finish_y as u32, 1);
        }
        self.queue.submit([encoder.finish()]);

        if !observe {
            return None;
        }

        let reads = self.read::<u64>("felt-reads-back", &reads_b, 4);
        Some(FeltCardRead {
            standing: self.read("felt-standing-back", standing_b, standing_words),
            owns: self.read("felt-owns-back", owns_b, own_words),
            cog_grains: self.read("felt-cog-grains-back", &cog_grains_b, cells * 2),
            arm_grains: self.read("felt-arm-grains-back", &arm_grains_b, cells * 2),
            cog_sums: self.read("felt-cog-sums-back", &cog_sums_b, cells * 2),
            arm_sums: self.read("felt-arm-sums-back", &arm_sums_b, cells * 2),
            touched: self.read("felt-touched-back", &touched_b, cells),
            reads: [reads[0], reads[1], reads[2], reads[3]],
        })
    }

    fn resolve_founded_resident(
        &self,
        mount: &FoundedLineageMount,
        observe_full: bool,
        observe_projection: bool,
    ) -> (Option<FeltCardRead>, Option<[u64; 4]>) {
        self.assert_carriers_at_receiving_edge(
            "founded-receiving-edge-carriers",
            &mount.carriers,
            mount.carrier_words,
            &mount.worldline_light_ends,
        );
        let cell_groups = (mount.cells as u64).div_ceil(64);
        let source_groups = ((mount.cells as u64) + (mount.own_cells as u64)).div_ceil(64);
        let work_x = source_groups.min(self.max_workgroups as u64).max(1) as u32;
        let source_y = source_groups.div_ceil(work_x as u64);
        let finish_y = cell_groups.div_ceil(work_x as u64);
        assert!(
            source_y <= self.max_workgroups as u64 && finish_y <= self.max_workgroups as u64,
            "this founded configuration fits one two-dimensional dispatch"
        );
        let params = [
            mount.cells as u32,
            mount.own_cells as u32,
            work_x * 64,
            mount.standing_axis,
        ];
        let cog_grains_b = self.zeroed::<u64>("founded-cog-grains", mount.cells * 2);
        let arm_grains_b = self.zeroed::<u32>("founded-arm-grains", mount.cells * 2);
        let cog_sums_b = self.zeroed::<u64>("founded-cog-sums", mount.cells * 2);
        let arm_sums_b = self.zeroed::<u64>("founded-arm-sums", mount.cells * 2);
        let touched_b = self.zeroed::<u32>("founded-touched", mount.cells);
        let reads_b = self.zeroed::<u64>("founded-reads", 4);
        let params_b = self.storage("founded-link-params", &params);

        let grain_group = self.bind(
            "link_founded_grain",
            &self.grain_layout,
            &[
                &mount.standing,
                &mount.owns,
                &cog_grains_b,
                &arm_grains_b,
                &touched_b,
                &params_b,
            ],
        );
        let sum_group = self.bind(
            "link_founded_sum",
            &self.sum_layout,
            &[
                &mount.standing,
                &mount.owns,
                &cog_grains_b,
                &arm_grains_b,
                &cog_sums_b,
                &arm_sums_b,
                &touched_b,
                &params_b,
            ],
        );
        let finish_group = self.bind(
            "link_finish_founded",
            &self.finish_layout,
            &[
                &mount.standing,
                &cog_grains_b,
                &arm_grains_b,
                &cog_sums_b,
                &arm_sums_b,
                &touched_b,
                &reads_b,
                &params_b,
            ],
        );

        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("one founded light-end configuration"),
            });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("founded constructions declare the receiving grain"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.founded_grain);
            pass.set_bind_group(0, &grain_group, &[]);
            pass.dispatch_workgroups(work_x, source_y as u32, 1);
        }
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("founded constructions sum exactly at that grain"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.founded_sum);
            pass.set_bind_group(0, &sum_group, &[]);
            pass.dispatch_workgroups(work_x, source_y as u32, 1);
        }
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("the founded edge's one final re-base"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.finish);
            pass.set_bind_group(0, &finish_group, &[]);
            pass.dispatch_workgroups(work_x, finish_y as u32, 1);
        }
        self.queue.submit([encoder.finish()]);

        if !observe_full && !observe_projection {
            return (None, None);
        }

        let reads = self.read::<u64>("founded-reads-back", &reads_b, 4);
        let projection = [reads[0], reads[1], reads[2], reads[3]];
        if !observe_full {
            return (None, Some(projection));
        }
        let full = FeltCardRead {
            standing: self.read(
                "founded-standing-back",
                &mount.standing,
                mount.standing_words,
            ),
            owns: self.read("founded-owns-back", &mount.owns, mount.own_words),
            cog_grains: self.read("founded-cog-grains-back", &cog_grains_b, mount.cells * 2),
            arm_grains: self.read("founded-arm-grains-back", &arm_grains_b, mount.cells * 2),
            cog_sums: self.read("founded-cog-sums-back", &cog_sums_b, mount.cells * 2),
            arm_sums: self.read("founded-arm-sums-back", &arm_sums_b, mount.cells * 2),
            touched: self.read("founded-touched-back", &touched_b, mount.cells),
            reads: projection,
        };
        (Some(full), Some(projection))
    }

    /// Cross one true receiving edge while keeping the standing/card apparatus entirely resident.
    /// The observer can read later; no boundary material returns during this causal operation.
    pub fn resolve_mounted_in_place(&self, mount: &FeltLineageMount) {
        self.assert_carriers_at_receiving_edge(
            "dense-receiving-edge-carriers",
            &mount.carriers,
            mount.carrier_words,
            &mount.worldline_light_ends,
        );
        let read = self.resolve_resident(
            &mount.standing,
            &mount.owns,
            mount.standing_words,
            mount.own_words,
            mount.cells,
            mount.lanes,
            false,
        );
        debug_assert!(read.is_none());
    }

    /// Resolve the complete configuration in the same buffers that produced its OWN regions.
    /// Callers cross this boundary only after every carrier cursor has reached its light's true end.
    pub fn resolve_mounted(&self, mount: &FeltLineageMount) -> FeltCardRead {
        self.assert_carriers_at_receiving_edge(
            "dense-observed-edge-carriers",
            &mount.carriers,
            mount.carrier_words,
            &mount.worldline_light_ends,
        );
        self.resolve_resident(
            &mount.standing,
            &mount.owns,
            mount.standing_words,
            mount.own_words,
            mount.cells,
            mount.lanes,
            true,
        )
        .expect("an observed resolution returns its bounded mirror")
    }

    /// Cross the founded receiving edge in place. No chart is expanded to standing size and no
    /// bounded readback is required by the operation itself.
    pub fn resolve_founded_in_place(&self, mount: &FoundedLineageMount) {
        let (read, projection) = self.resolve_founded_resident(mount, false, false);
        debug_assert!(read.is_none() && projection.is_none());
    }

    /// Resolve and expose one bounded mirror of the founded receiving edge for an exact card gate.
    pub fn resolve_founded(&self, mount: &FoundedLineageMount) -> FeltCardRead {
        self.resolve_founded_resident(mount, true, true)
            .0
            .expect("an observed founded resolution returns its bounded mirror")
    }

    /// Cross a production-sized founded edge and return only its four-word topology projection.
    /// Exact standing remains resident; this membrane instrument does not mirror either chart.
    pub fn resolve_founded_projection(&self, mount: &FoundedLineageMount) -> [u64; 4] {
        self.resolve_founded_resident(mount, false, true)
            .1
            .expect("a projected founded resolution returns its topology mouth")
    }

    /// Read only the four term counts per lineage. Forms and carriers remain resident and are not
    /// reflected across the boundary.
    pub fn read_founded_term_counts(&self, mount: &FoundedLineageMount) -> Vec<u64> {
        self.read("founded-term-counts-back", &mount.counts, mount.lanes * 4)
    }

    /// Mount one modest, complete configuration and resolve it once. `owns` is lane-major:
    /// `[OWN₀ cells][OWN₁ cells]…`. This is deliberately a fresh-operation mirror; production
    /// residency begins when the card also produces those OWN planes and their carrier/`K`.
    pub fn compose(&self, standing: &[u32], owns: &[u32], cells: u32, lanes: u32) -> FeltCardRead {
        let cells = cells as usize;
        let lanes = lanes as usize;
        assert!(
            cells != 0 && lanes != 0,
            "the composition has cells and co-present lineages"
        );
        assert_eq!(
            standing.len(),
            cells * body::medium::FORM_WORDS,
            "standing mounts one whole form per place"
        );
        assert_eq!(
            owns.len(),
            lanes * standing.len(),
            "every lineage mounts one disjoint OWN plane"
        );

        let standing_b = self.storage("felt-standing", standing);
        let owns_b = self.storage("felt-owns", owns);
        self.resolve_resident(
            &standing_b,
            &owns_b,
            standing.len(),
            owns.len(),
            cells,
            lanes,
            true,
        )
        .expect("a bounded composition returns its mirror")
    }
}

#[cfg(test)]
#[path = "sleep_tests.rs"]
mod sleep_tests;

/// Historical cpu scaffold. It is unconstructible through the public API while the card is quarantined.
pub struct Surface {
    pub adapter_name: String,
    device: wgpu::Device,
    queue: wgpu::Queue,
    mesh: wgpu::ComputePipeline,
    path: wgpu::ComputePipeline,
    live: wgpu::ComputePipeline,
    scope: wgpu::ComputePipeline,
    mesh_layout: wgpu::BindGroupLayout,
    wind: wgpu::ComputePipeline,
    gather: wgpu::ComputePipeline,
    probe: wgpu::ComputePipeline,
    wind_layout: wgpu::BindGroupLayout,
}

fn storage_entry(binding: u32) -> wgpu::BindGroupLayoutEntry {
    wgpu::BindGroupLayoutEntry {
        binding,
        visibility: wgpu::ShaderStages::COMPUTE,
        ty: wgpu::BindingType::Buffer {
            ty: wgpu::BufferBindingType::Storage { read_only: false },
            has_dynamic_offset: false,
            min_binding_size: None,
        },
        count: None,
    }
}

impl Surface {
    /// The card is deliberately unavailable after the no-CAS ruling. This refusal is load-bearing:
    /// no old membrane mode may mistake the inert aperture for a functioning engine.
    pub fn new() -> Option<Surface> {
        eprintln!("surface: card quarantined by FORMULA §XXIV — derive the living lineage carrier before rebuilding");
        None
    }

    /// The superseded boundary scaffold remains private only so its cpu-side instruments can be
    /// read during the recut. Nothing calls it, and the quarantine module does not expose its entries.
    #[allow(dead_code)]
    fn historical_new() -> Option<Surface> {
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor::default());
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))
        .ok()?;
        let info = adapter.get_info();
        let adapter_name = format!("{} ({:?}/{:?})", info.name, info.device_type, info.backend);
        let (device, queue) = pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor {
            required_features: wgpu::Features::SHADER_INT64
                | wgpu::Features::EXPERIMENTAL_PASSTHROUGH_SHADERS,
            required_limits: adapter.limits(),
            experimental_features: unsafe { wgpu::ExperimentalFeatures::enabled() },
            ..Default::default()
        }))
        .ok()?;
        device.on_uncaptured_error(std::sync::Arc::new(|e| {
            eprintln!("surface: wgpu uncaptured error — {e}")
        }));
        let module = unsafe {
            device.create_shader_module_passthrough(wgpu::ShaderModuleDescriptorPassthrough {
                label: Some("soma"),
                spirv: Some(wgpu::util::make_spirv_raw(include_bytes!(
                    "../../kernel/soma.spv"
                ))),
                ..Default::default()
            })
        };
        let mesh_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("mesh"),
            entries: &[
                storage_entry(0), // pool shards 0..7 — THE MOUNT: one flat reservation to the law,
                storage_entry(1), //   eight 1 GB bindings to the card (the binding wall through this
                storage_entry(2), //   stack is 2^31−1 bytes — the probe measured it; the shard grain
                storage_entry(3), //   is the wall's own: 2^28 cells)
                storage_entry(4),
                storage_entry(5),
                storage_entry(6),
                storage_entry(7),
                storage_entry(8), // carrier — THE CARRIER: each current's stand between strokes
                storage_entry(9), // bytes
                storage_entry(10), // spans
                storage_entry(11), // lanes
                storage_entry(12), // params
                storage_entry(13), // stats
            ],
        });
        let wind_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("wind_sweep"),
            entries: &[
                storage_entry(0), // pool shards 0..7
                storage_entry(1),
                storage_entry(2),
                storage_entry(3),
                storage_entry(4),
                storage_entry(5),
                storage_entry(6),
                storage_entry(7),
                storage_entry(8), // radiated / partials
                storage_entry(9), // params
            ],
        });
        let mk = |layout: &wgpu::BindGroupLayout, entry: &str| {
            let pl = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some(entry),
                bind_group_layouts: &[layout],
                push_constant_ranges: &[],
            });
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(entry),
                layout: Some(&pl),
                module: &module,
                entry_point: Some(entry),
                compilation_options: Default::default(),
                cache: None,
            })
        };
        let wind = mk(&wind_layout, "wind_sweep");
        let gather = mk(&wind_layout, "wind_gather");
        let probe = mk(&wind_layout, "probe");
        let mesh = mk(&mesh_layout, "mesh");
        let path = mk(&mesh_layout, "path");
        let live = mk(&mesh_layout, "live");
        let scope = mk(&mesh_layout, "scope");
        Some(Surface {
            adapter_name,
            device,
            queue,
            mesh,
            path,
            live,
            scope,
            mesh_layout,
            wind,
            gather,
            probe,
            wind_layout,
        })
    }

    /// a storage buffer initialized with the given words.
    pub fn storage(&self, label: &str, data: &[u32]) -> wgpu::Buffer {
        use wgpu::util::DeviceExt;
        self.device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some(label),
                contents: bytemuck::cast_slice(data),
                usage: wgpu::BufferUsages::STORAGE
                    | wgpu::BufferUsages::COPY_SRC
                    | wgpu::BufferUsages::COPY_DST,
            })
    }

    /// a zeroed storage buffer of `words` u32s (the boundary's reservation).
    pub fn zeroed(&self, label: &str, words: usize) -> wgpu::Buffer {
        self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size: (words * 4) as u64,
            usage: wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_SRC
                | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        })
    }

    /// dispatch MESH — one thread per lane, one dispatch the whole gather.
    pub fn mesh(&self, b: [&wgpu::Buffer; 14], lanes: u32) {
        let entries: Vec<wgpu::BindGroupEntry> = b
            .iter()
            .enumerate()
            .map(|(i, buf)| wgpu::BindGroupEntry {
                binding: i as u32,
                resource: buf.as_entire_binding(),
            })
            .collect();
        let bg = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("mesh"),
            layout: &self.mesh_layout,
            entries: &entries,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut p = enc.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("mesh"),
                timestamp_writes: None,
            });
            p.set_pipeline(&self.mesh);
            p.set_bind_group(0, &bg, &[]);
            p.dispatch_workgroups(lanes.div_ceil(64), 1, 1);
        }
        self.queue.submit([enc.finish()]);
    }

    /// dispatch PATH — one thread per lane: the whole gather THEN the lane's brain current runs forward
    /// (W6 — the deed-run-forward over the standing terrain; the visited grips land in the stats blocks).
    pub fn path(&self, b: [&wgpu::Buffer; 14], lanes: u32) {
        let entries: Vec<wgpu::BindGroupEntry> = b
            .iter()
            .enumerate()
            .map(|(i, buf)| wgpu::BindGroupEntry {
                binding: i as u32,
                resource: buf.as_entire_binding(),
            })
            .collect();
        let bg = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("path"),
            layout: &self.mesh_layout,
            entries: &entries,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut p = enc.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("path"),
                timestamp_writes: None,
            });
            p.set_pipeline(&self.path);
            p.set_bind_group(0, &bg, &[]);
            p.dispatch_workgroups(lanes.div_ceil(64), 1, 1);
        }
        self.queue.submit([enc.finish()]);
    }

    /// dispatch LIVE — one thread per lane: the whole circuit (W7 — the eye lands each arrival and the
    /// brain takes one deed-run-forward step per beat; the coupling live both ways in one entry).
    pub fn live(&self, b: [&wgpu::Buffer; 14], lanes: u32) {
        let entries: Vec<wgpu::BindGroupEntry> = b
            .iter()
            .enumerate()
            .map(|(i, buf)| wgpu::BindGroupEntry {
                binding: i as u32,
                resource: buf.as_entire_binding(),
            })
            .collect();
        let bg = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("live"),
            layout: &self.mesh_layout,
            entries: &entries,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut p = enc.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("live"),
                timestamp_writes: None,
            });
            p.set_pipeline(&self.live);
            p.set_bind_group(0, &bg, &[]);
            p.dispatch_workgroups(lanes.div_ceil(64), 1, 1);
        }
        self.queue.submit([enc.finish()]);
    }

    /// dispatch SCOPE — one thread per lane of RAW LIGHT (W9 — the living boundary: the atom-grain
    /// sub-illicium finds the folds; the whole circuit runs on the bricks).
    pub fn scope(&self, b: [&wgpu::Buffer; 14], lanes: u32) {
        let entries: Vec<wgpu::BindGroupEntry> = b
            .iter()
            .enumerate()
            .map(|(i, buf)| wgpu::BindGroupEntry {
                binding: i as u32,
                resource: buf.as_entire_binding(),
            })
            .collect();
        let bg = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("scope"),
            layout: &self.mesh_layout,
            entries: &entries,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut p = enc.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("scope"),
                timestamp_writes: None,
            });
            p.set_pipeline(&self.scope);
            p.set_bind_group(0, &bg, &[]);
            p.dispatch_workgroups(lanes.div_ceil(64), 1, 1);
        }
        self.queue.submit([enc.finish()]);
    }

    /// dispatch WIND_SWEEP — one thread per cell (the digit, race-free).
    pub fn wind(&self, b: [&wgpu::Buffer; 10], cells: u32) {
        let entries: Vec<wgpu::BindGroupEntry> = b
            .iter()
            .enumerate()
            .map(|(i, buf)| wgpu::BindGroupEntry {
                binding: i as u32,
                resource: buf.as_entire_binding(),
            })
            .collect();
        let bg = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("wind"),
            layout: &self.wind_layout,
            entries: &entries,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut p = enc.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("wind"),
                timestamp_writes: None,
            });
            p.set_pipeline(&self.wind);
            p.set_bind_group(0, &bg, &[]);
            let groups = cells.div_ceil(64);
            let wx = groups.min(32768);
            let wy = groups.div_ceil(32768);
            p.dispatch_workgroups(wx, wy, 1); // 2D — one dimension caps at 65535 workgroups
        }
        self.queue.submit([enc.finish()]);
    }

    /// dispatch WIND_GATHER — the digit ⊕ the on-card ledger: one thread per REGION of cells; the boundary
    /// reads kilobytes of partials, never the pool.
    pub fn gather(&self, b: [&wgpu::Buffer; 10], threads: u32) {
        let entries: Vec<wgpu::BindGroupEntry> = b
            .iter()
            .enumerate()
            .map(|(i, buf)| wgpu::BindGroupEntry {
                binding: i as u32,
                resource: buf.as_entire_binding(),
            })
            .collect();
        let bg = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("gather"),
            layout: &self.wind_layout,
            entries: &entries,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut p = enc.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("gather"),
                timestamp_writes: None,
            });
            p.set_pipeline(&self.gather);
            p.set_bind_group(0, &bg, &[]);
            let groups = threads.div_ceil(64);
            let wx = groups.min(32768);
            p.dispatch_workgroups(wx, groups.div_ceil(32768), 1);
        }
        self.queue.submit([enc.finish()]);
    }

    /// dispatch PROBE — the mount's own smoke: markers into each shard's first word, read back through the
    /// same atomics; the boundary compares. Runs before any scaled mount is trusted.
    pub fn probe(&self, b: [&wgpu::Buffer; 10]) {
        let entries: Vec<wgpu::BindGroupEntry> = b
            .iter()
            .enumerate()
            .map(|(i, buf)| wgpu::BindGroupEntry {
                binding: i as u32,
                resource: buf.as_entire_binding(),
            })
            .collect();
        let bg = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("probe"),
            layout: &self.wind_layout,
            entries: &entries,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut p = enc.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("probe"),
                timestamp_writes: None,
            });
            p.set_pipeline(&self.probe);
            p.set_bind_group(0, &bg, &[]);
            p.dispatch_workgroups(1, 1, 1);
        }
        self.queue.submit([enc.finish()]);
    }

    /// READ a small addressed window (word offset ⊕ count) — targeted grips without crossing the pool's volume.
    pub fn read_at(&self, buf: &wgpu::Buffer, word_off: u64, words: usize) -> Vec<u32> {
        if words == 0 {
            return Vec::new();
        }
        let size = (words * 4) as u64;
        let staging = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("staging-at"),
            size,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        enc.copy_buffer_to_buffer(buf, word_off * 4, &staging, 0, size);
        self.queue.submit([enc.finish()]);
        let slice = staging.slice(..);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        let _ = self.device.poll(wgpu::PollType::Wait {
            submission_index: None,
            timeout: None,
        });
        let data = slice.get_mapped_range();
        let out: Vec<u32> = bytemuck::cast_slice(&data).to_vec();
        drop(data);
        staging.unmap();
        out
    }

    /// READ a buffer back across the boundary — an AUDIT: rare, deliberate, never a per-cycle harness.
    pub fn read(&self, buf: &wgpu::Buffer, words: usize) -> Vec<u32> {
        if words == 0 {
            return Vec::new();
        }
        let size = (words * 4) as u64;
        let staging = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("staging"),
            size,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        enc.copy_buffer_to_buffer(buf, 0, &staging, 0, size);
        self.queue.submit([enc.finish()]);
        let slice = staging.slice(..);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        let _ = self.device.poll(wgpu::PollType::Wait {
            submission_index: None,
            timeout: None,
        });
        let data = slice.get_mapped_range();
        let out: Vec<u32> = bytemuck::cast_slice(&data).to_vec();
        drop(data);
        staging.unmap();
        out
    }
}
