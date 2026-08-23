//! Exact source and layout incidence across heterogeneous mathematical presentations.
//!
//! This is the missing M0 edge between exterior document/image mouths and the standing oriented
//! incidence complex. A caller may supply exact artifact bytes and either exact-rational placed
//! carriers or an [`ExactRaster`]. It may not supply contacts. This owner derives only generic
//! serial and planar relations; operator spellings, Unicode classes, equation identifiers, file
//! names, and mathematical grammar are absent from the constitutive path.
//!
//! PDF, SVG, Typst, PNG, and equation-atlas names remain apparatus/provenance charts. Equal payload
//! bytes are a face equality, never occurrence identity: every situated carrier is addressed by
//! artifact identity and local ordinal. Cross-chart correspondence returns every normalized-box
//! overlap and every unmatched occurrence. It chooses no representative.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_rational::BigRational;
use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::incidence_production::{
    DeclaredContactFace, DeclaredOccurrence, IncidenceComplex, IncidenceProductionError, Patch,
};

pub type Rat = BigRational;

const SCHEMA: &str = "soma-life.mathematical-source-circulation.v1";

fn zero_rat() -> Rat {
    Rat::from_integer(BigInt::from(0))
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    Sha256::digest(bytes.as_ref())
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

/// The exact identity of one exterior artifact. `locator` is lineage, never identity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ArtifactIdentity {
    /// Identity of this caused artifact occurrence. Distinct reruns may carry equal bytes.
    pub occurrence: String,
    pub locator: String,
    pub octets: u64,
    pub sha256: String,
}

impl ArtifactIdentity {
    pub fn of_bytes(
        occurrence: impl Into<String>,
        locator: impl Into<String>,
        bytes: &[u8],
    ) -> Result<Self, SourceLayoutError> {
        let occurrence = occurrence.into();
        if occurrence.is_empty() {
            return Err(SourceLayoutError::EmptyArtifactOccurrence);
        }
        let octets = u64::try_from(bytes.len()).map_err(|_| SourceLayoutError::Extent)?;
        Ok(Self {
            occurrence,
            locator: locator.into(),
            octets,
            sha256: hex(bytes),
        })
    }
}

/// Exterior chart provenance. It is recorded and never branches recovery.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum TestimonyChart {
    BornDigital,
    Vector,
    Raster,
    ExteriorAtlas,
}

/// One exact page/chart extent.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactExtent {
    width: Rat,
    height: Rat,
}

impl ExactExtent {
    pub fn new(width: Rat, height: Rat) -> Result<Self, SourceLayoutError> {
        if width <= zero_rat() || height <= zero_rat() {
            return Err(SourceLayoutError::NonPositiveExtent);
        }
        Ok(Self { width, height })
    }

    pub fn width(&self) -> &Rat {
        &self.width
    }

    pub fn height(&self) -> &Rat {
        &self.height
    }
}

/// An exact axis-aligned receiver box. Coordinates are carried as rationals, never parsed through
/// floating point.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactBox {
    left: Rat,
    top: Rat,
    right: Rat,
    bottom: Rat,
}

impl ExactBox {
    pub fn new(left: Rat, top: Rat, right: Rat, bottom: Rat) -> Result<Self, SourceLayoutError> {
        if left > right || top > bottom {
            return Err(SourceLayoutError::InvertedBox);
        }
        Ok(Self {
            left,
            top,
            right,
            bottom,
        })
    }

    pub fn normalized(&self, extent: &ExactExtent) -> Self {
        Self {
            left: &self.left / &extent.width,
            top: &self.top / &extent.height,
            right: &self.right / &extent.width,
            bottom: &self.bottom / &extent.height,
        }
    }

    pub fn left(&self) -> &Rat {
        &self.left
    }

    pub fn top(&self) -> &Rat {
        &self.top
    }

    pub fn right(&self) -> &Rat {
        &self.right
    }

    pub fn bottom(&self) -> &Rat {
        &self.bottom
    }

    fn overlaps(&self, other: &Self) -> bool {
        self.left < other.right
            && other.left < self.right
            && self.top < other.bottom
            && other.top < self.bottom
    }

    fn strictly_contains(&self, other: &Self) -> bool {
        (self != other)
            && self.left <= other.left
            && self.top <= other.top
            && self.right >= other.right
            && self.bottom >= other.bottom
    }

    fn vertical_overlap(&self, other: &Self) -> bool {
        self.top < other.bottom && other.top < self.bottom
    }

    fn horizontal_overlap(&self, other: &Self) -> bool {
        self.left < other.right && other.left < self.right
    }

    fn lies_in(&self, extent: &ExactExtent) -> bool {
        self.left >= zero_rat()
            && self.top >= zero_rat()
            && self.right <= extent.width
            && self.bottom <= extent.height
    }
}

/// Parse a finite decimal lexeme exactly. This is the narrow Poppler/SVG coordinate mouth: the
/// decimal spelling becomes a rational and no `f32`/`f64` exists on the path.
pub fn exact_decimal(lexeme: &str, digit_aperture: usize) -> Result<Rat, SourceLayoutError> {
    let trimmed = lexeme.trim();
    if trimmed.is_empty() {
        return Err(SourceLayoutError::MalformedDecimal(lexeme.to_owned()));
    }
    let (negative, unsigned) = match trimmed.as_bytes()[0] {
        b'-' => (true, &trimmed[1..]),
        b'+' => (false, &trimmed[1..]),
        _ => (false, trimmed),
    };
    let mut parts = unsigned.split('.');
    let whole = parts.next().unwrap_or_default();
    let fraction = parts.next();
    if parts.next().is_some()
        || whole.is_empty()
        || !whole.bytes().all(|octet| octet.is_ascii_digit())
        || fraction.is_some_and(|digits| !digits.bytes().all(|octet| octet.is_ascii_digit()))
    {
        return Err(SourceLayoutError::MalformedDecimal(lexeme.to_owned()));
    }
    let digits = fraction.unwrap_or_default();
    let digit_population = whole
        .len()
        .checked_add(digits.len())
        .ok_or(SourceLayoutError::Extent)?;
    if digit_population > digit_aperture {
        return Err(SourceLayoutError::DecimalApertureExceeded {
            digits: digit_population,
            aperture: digit_aperture,
        });
    }
    let scale = BigInt::from(10_u8)
        .pow(u32::try_from(digits.len()).map_err(|_| SourceLayoutError::Extent)?);
    let mut numerator = whole
        .parse::<BigInt>()
        .map_err(|_| SourceLayoutError::MalformedDecimal(lexeme.to_owned()))?
        * &scale;
    if !digits.is_empty() {
        numerator += digits
            .parse::<BigInt>()
            .map_err(|_| SourceLayoutError::MalformedDecimal(lexeme.to_owned()))?;
    }
    if negative {
        numerator = -numerator;
    }
    Ok(Rat::new(numerator, scale))
}

/// Exact, pre-deed work testimony for source/layout circulation.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct SourceLayoutWorkDemand {
    pub pair_visits: u128,
    pub sample_visits: u128,
    pub carried_octets: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceLayoutWorkCover {
    pub pair_visits: u128,
    pub sample_visits: u128,
    pub carried_octets: u128,
}

impl SourceLayoutWorkCover {
    pub fn exactly(demand: &SourceLayoutWorkDemand) -> Self {
        Self {
            pair_visits: demand.pair_visits,
            sample_visits: demand.sample_visits,
            carried_octets: demand.carried_octets,
        }
    }

    fn admits(&self, demand: &SourceLayoutWorkDemand) -> bool {
        demand.pair_visits <= self.pair_visits
            && demand.sample_visits <= self.sample_visits
            && demand.carried_octets <= self.carried_octets
    }
}

pub fn layout_demand(
    occurrences: &[PlacedCarrier],
) -> Result<SourceLayoutWorkDemand, SourceLayoutError> {
    let population = u128::try_from(occurrences.len()).map_err(|_| SourceLayoutError::Extent)?;
    let unordered = population
        .checked_mul(population.saturating_sub(1))
        .and_then(|value| value.checked_div(2))
        .ok_or(SourceLayoutError::Extent)?;
    // One unordered overlap/containment visit, plus horizontal and vertical candidate visits.
    let pair_visits = unordered
        .checked_add(
            population
                .checked_mul(population)
                .and_then(|value| value.checked_mul(2))
                .ok_or(SourceLayoutError::Extent)?,
        )
        .ok_or(SourceLayoutError::Extent)?;
    let carried_octets = carried_octets(occurrences)?;
    Ok(SourceLayoutWorkDemand {
        pair_visits,
        sample_visits: 0,
        carried_octets,
    })
}

/// Work for the exact serial receiver alone. This is the lawful bounded face for a vector object
/// stream whose planar relations remain in the cross-chart reconstruction fibre.
pub fn serial_layout_demand(
    occurrences: &[PlacedCarrier],
) -> Result<SourceLayoutWorkDemand, SourceLayoutError> {
    Ok(SourceLayoutWorkDemand {
        pair_visits: 0,
        sample_visits: 0,
        carried_octets: carried_octets(occurrences)?,
    })
}

fn carried_octets(occurrences: &[PlacedCarrier]) -> Result<u128, SourceLayoutError> {
    occurrences.iter().try_fold(0_u128, |sum, occurrence| {
        sum.checked_add(u128::from(occurrence.payload_octets))
            .ok_or(SourceLayoutError::Extent)
    })
}

/// One situated source occurrence. The payload digest is a receiver face; `address` preserves the
/// distinct occurrence even when another occurrence carries identical bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PlacedCarrier {
    pub address: String,
    pub payload_sha256: String,
    pub payload_octets: u64,
    pub serial_ordinal: Option<u64>,
    pub bounds: ExactBox,
    payload: Vec<u8>,
}

impl PlacedCarrier {
    pub fn new(
        artifact: &ArtifactIdentity,
        local_ordinal: u64,
        payload: Vec<u8>,
        serial_ordinal: Option<u64>,
        bounds: ExactBox,
    ) -> Result<Self, SourceLayoutError> {
        if payload.is_empty() {
            return Err(SourceLayoutError::EmptyCarrier);
        }
        let payload_octets = u64::try_from(payload.len()).map_err(|_| SourceLayoutError::Extent)?;
        Ok(Self {
            address: format!(
                "{}:{}:{local_ordinal}",
                artifact.occurrence, artifact.sha256
            ),
            payload_sha256: hex(&payload),
            payload_octets,
            serial_ordinal,
            bounds,
            payload,
        })
    }

    fn patch(&self) -> Result<Patch, IncidenceProductionError> {
        Patch::new(self.payload.clone(), self.address.clone())
    }
}

/// Relations derived from placement alone. None names a mathematical role.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum LayoutRelation {
    SerialNext,
    Contains,
    Overlaps,
    HorizontalNext,
    VerticalNext,
}

impl LayoutRelation {
    fn face(self) -> &'static str {
        match self {
            Self::SerialNext => "serial-next",
            Self::Contains => "spatial-contains",
            Self::Overlaps => "spatial-overlaps",
            Self::HorizontalNext => "horizontal-next",
            Self::VerticalNext => "vertical-next",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct LayoutContact {
    pub from: usize,
    pub to: usize,
    pub relation: LayoutRelation,
}

/// One admitted exterior testimony and the incidence derived from it.
#[derive(Debug)]
pub struct SourceLayoutTestimony {
    pub schema: String,
    pub chart: TestimonyChart,
    pub artifact: ArtifactIdentity,
    pub extent: ExactExtent,
    pub occurrences: Vec<PlacedCarrier>,
    pub contacts: Vec<LayoutContact>,
    /// `None` for a lawful zero-dimensional testimony with no derived contact. The standing
    /// `IncidenceComplex` refuses a body with no 1-cell; inventing a self-contact would counterfeit
    /// source incidence.
    pub complex: Option<IncidenceComplex>,
    pub work: SourceLayoutWorkDemand,
    pub outside_declared_artifact_open: bool,
}

/// Derive one testimony. The caller supplies occurrences, not links.
pub fn derive_layout(
    chart: TestimonyChart,
    artifact: ArtifactIdentity,
    extent: ExactExtent,
    occurrences: Vec<PlacedCarrier>,
    cover: &SourceLayoutWorkCover,
) -> Result<SourceLayoutTestimony, SourceLayoutError> {
    validate_occurrences(&artifact, &extent, &occurrences)?;
    let work = layout_demand(&occurrences)?;
    if !cover.admits(&work) {
        return Err(SourceLayoutError::WorkCoverInsufficient {
            demand: work,
            cover: cover.clone(),
        });
    }
    let contacts = derived_contacts(&occurrences);
    let complex = (!contacts.is_empty())
        .then(|| found_complex(&occurrences, &contacts))
        .transpose()?;
    Ok(SourceLayoutTestimony {
        schema: SCHEMA.to_owned(),
        chart,
        artifact,
        extent,
        occurrences,
        contacts,
        complex,
        work,
        outside_declared_artifact_open: true,
    })
}

/// Derive only the material's explicit serial occurrence order. The caller still cannot supply
/// links: unique ordinals found `SerialNext`, while every planar relation stays open for
/// co-testimony. This prevents a vector container with many primitive path/use occurrences from
/// being replayed through an unnecessary Cartesian planar receiver.
pub fn derive_serial_layout(
    chart: TestimonyChart,
    artifact: ArtifactIdentity,
    extent: ExactExtent,
    occurrences: Vec<PlacedCarrier>,
    cover: &SourceLayoutWorkCover,
) -> Result<SourceLayoutTestimony, SourceLayoutError> {
    validate_occurrences(&artifact, &extent, &occurrences)?;
    let work = serial_layout_demand(&occurrences)?;
    if !cover.admits(&work) {
        return Err(SourceLayoutError::WorkCoverInsufficient {
            demand: work,
            cover: cover.clone(),
        });
    }
    let mut serial = occurrences
        .iter()
        .enumerate()
        .filter_map(|(at, occurrence)| occurrence.serial_ordinal.map(|ordinal| (ordinal, at)))
        .collect::<Vec<_>>();
    serial.sort_unstable();
    let contacts = serial
        .windows(2)
        .map(|pair| LayoutContact {
            from: pair[0].1,
            to: pair[1].1,
            relation: LayoutRelation::SerialNext,
        })
        .collect::<Vec<_>>();
    let complex = (!contacts.is_empty())
        .then(|| found_complex(&occurrences, &contacts))
        .transpose()?;
    Ok(SourceLayoutTestimony {
        schema: SCHEMA.to_owned(),
        chart,
        artifact,
        extent,
        occurrences,
        contacts,
        complex,
        work,
        outside_declared_artifact_open: true,
    })
}

fn validate_occurrences(
    artifact: &ArtifactIdentity,
    extent: &ExactExtent,
    occurrences: &[PlacedCarrier],
) -> Result<(), SourceLayoutError> {
    if occurrences.is_empty() {
        return Err(SourceLayoutError::NoOccurrences);
    }
    let expected_prefix = format!("{}:{}:", artifact.occurrence, artifact.sha256);
    if occurrences
        .iter()
        .any(|occurrence| !occurrence.address.starts_with(&expected_prefix))
    {
        return Err(SourceLayoutError::ForeignOccurrence);
    }
    let mut addresses = BTreeSet::new();
    let mut serial = BTreeSet::new();
    for occurrence in occurrences {
        if !addresses.insert(occurrence.address.clone()) {
            return Err(SourceLayoutError::DuplicateOccurrenceAddress(
                occurrence.address.clone(),
            ));
        }
        if !occurrence.bounds.lies_in(&extent) {
            return Err(SourceLayoutError::OccurrenceOutsideExtent(
                occurrence.address.clone(),
            ));
        }
        if let Some(ordinal) = occurrence.serial_ordinal {
            if !serial.insert(ordinal) {
                return Err(SourceLayoutError::DuplicateSerialOrdinal(ordinal));
            }
        }
    }
    Ok(())
}

fn derived_contacts(occurrences: &[PlacedCarrier]) -> Vec<LayoutContact> {
    let mut contacts = BTreeSet::new();

    let mut serial = occurrences
        .iter()
        .enumerate()
        .filter_map(|(at, occurrence)| occurrence.serial_ordinal.map(|ordinal| (ordinal, at)))
        .collect::<Vec<_>>();
    serial.sort_unstable();
    for pair in serial.windows(2) {
        contacts.insert(LayoutContact {
            from: pair[0].1,
            to: pair[1].1,
            relation: LayoutRelation::SerialNext,
        });
    }

    for left in 0..occurrences.len() {
        for right in left + 1..occurrences.len() {
            let a = &occurrences[left].bounds;
            let b = &occurrences[right].bounds;
            if a.strictly_contains(b) {
                contacts.insert(LayoutContact {
                    from: left,
                    to: right,
                    relation: LayoutRelation::Contains,
                });
            } else if b.strictly_contains(a) {
                contacts.insert(LayoutContact {
                    from: right,
                    to: left,
                    relation: LayoutRelation::Contains,
                });
            } else if a.overlaps(b) {
                contacts.insert(LayoutContact {
                    from: left,
                    to: right,
                    relation: LayoutRelation::Overlaps,
                });
                // Overlap has no natural hand. Retain both orientations so the incidental storage
                // order of the pair cannot become a directed source relation.
                contacts.insert(LayoutContact {
                    from: right,
                    to: left,
                    relation: LayoutRelation::Overlaps,
                });
            }
        }

        // Immediate planar neighbours are founded by the least exact gap. Ties remain plural.
        let horizontal = occurrences
            .iter()
            .enumerate()
            .filter(|(right, candidate)| {
                *right != left
                    && occurrences[left].bounds.right <= candidate.bounds.left
                    && occurrences[left].bounds.vertical_overlap(&candidate.bounds)
            })
            .map(|(right, candidate)| {
                (
                    &candidate.bounds.left - &occurrences[left].bounds.right,
                    right,
                )
            })
            .collect::<Vec<_>>();
        retain_minimum_contacts(
            &mut contacts,
            left,
            horizontal,
            LayoutRelation::HorizontalNext,
        );
        let vertical = occurrences
            .iter()
            .enumerate()
            .filter(|(below, candidate)| {
                *below != left
                    && occurrences[left].bounds.bottom <= candidate.bounds.top
                    && occurrences[left]
                        .bounds
                        .horizontal_overlap(&candidate.bounds)
            })
            .map(|(below, candidate)| {
                (
                    &candidate.bounds.top - &occurrences[left].bounds.bottom,
                    below,
                )
            })
            .collect::<Vec<_>>();
        retain_minimum_contacts(&mut contacts, left, vertical, LayoutRelation::VerticalNext);
    }
    contacts.into_iter().collect()
}

fn retain_minimum_contacts(
    contacts: &mut BTreeSet<LayoutContact>,
    from: usize,
    candidates: Vec<(Rat, usize)>,
    relation: LayoutRelation,
) {
    let Some(minimum) = candidates.iter().map(|(gap, _)| gap).min() else {
        return;
    };
    for (_, to) in candidates.iter().filter(|(gap, _)| gap == minimum) {
        contacts.insert(LayoutContact {
            from,
            to: *to,
            relation,
        });
    }
}

fn found_complex(
    occurrences: &[PlacedCarrier],
    contacts: &[LayoutContact],
) -> Result<IncidenceComplex, SourceLayoutError> {
    let mut declared = Vec::with_capacity(occurrences.len() + contacts.len());
    let mut faces = Vec::with_capacity(occurrences.len() + contacts.len());
    // Singleton declarations make isolated occurrences sites of the same complex. The later
    // contact declarations reuse those addresses and therefore add bonds without copying sites.
    for (at, occurrence) in occurrences.iter().enumerate() {
        declared.push(DeclaredOccurrence {
            identity: format!("source-layout-site:{at}"),
            storage_ordinal: u64::try_from(at).map_err(|_| SourceLayoutError::Extent)?,
            caused_by: BTreeSet::new(),
            inscription: vec![occurrence.patch()?],
        });
        faces.push(Vec::new());
    }
    for (at, contact) in contacts.iter().enumerate() {
        let from = occurrences
            .get(contact.from)
            .ok_or(SourceLayoutError::Extent)?;
        let to = occurrences
            .get(contact.to)
            .ok_or(SourceLayoutError::Extent)?;
        declared.push(DeclaredOccurrence {
            identity: format!("source-layout-contact:{at}"),
            storage_ordinal: u64::try_from(occurrences.len() + at)
                .map_err(|_| SourceLayoutError::Extent)?,
            caused_by: BTreeSet::new(),
            inscription: vec![from.patch()?, to.patch()?],
        });
        faces.push(vec![DeclaredContactFace::new(contact.relation.face())?]);
    }
    let complex = IncidenceComplex::found_with_contact_faces(&declared, 2, &faces)?;
    let sites = complex
        .sites()
        .iter()
        .enumerate()
        .map(|(at, site)| (site.surface.as_str(), at))
        .collect::<BTreeMap<_, _>>();
    for occurrence in occurrences {
        if !sites.contains_key(occurrence.address.as_str()) {
            return Err(SourceLayoutError::IncidenceUnfaithful(
                occurrence.address.clone(),
            ));
        }
    }
    for contact in contacts {
        let from = &occurrences[contact.from].address;
        let to = &occurrences[contact.to].address;
        let Some(from_at) = sites.get(from.as_str()).copied() else {
            return Err(SourceLayoutError::IncidenceUnfaithful(from.clone()));
        };
        let Some(to_at) = sites.get(to.as_str()).copied() else {
            return Err(SourceLayoutError::IncidenceUnfaithful(to.clone()));
        };
        let faithful = complex.bonds().iter().any(|bond| {
            bond.from == from_at
                && bond.to == to_at
                && bond
                    .contact_faces
                    .iter()
                    .any(|face| face.name() == contact.relation.face())
        });
        if !faithful {
            return Err(SourceLayoutError::IncidenceUnfaithful(format!(
                "{} -> {} ({})",
                from,
                to,
                contact.relation.face()
            )));
        }
    }
    Ok(complex)
}

mod acoustic;
mod correspondence;
mod optical_holons;
mod optical_recovery;
mod raster;
#[cfg(test)]
mod tests;

pub use acoustic::{AcousticFrame, ExactAcousticOccurrence, ExactAcousticRefusal};
pub use correspondence::{
    compare_presentations, correspond, correspondence_demand, CoTestimonyFiber, ComparedContact,
    CorrespondenceCandidate, PresentationComparison,
};
pub use optical_holons::{
    grow_optical_holons, DeviceOpticalHolonReceipt, EquationGlyphFibre,
    ExactOpticalIncidenceReceipt, ExactOpticalScale, HierarchicalOpticalPassage,
    NativeEquationConstraintSection, NativeHierarchicalOpticalConsequence, OpticalAlternativeCover,
    OpticalFormMember, OpticalHolon, OpticalHolonGrain, OpticalHolonIncidence,
    OpticalHolonIncidenceKind, OpticalHolonIntervention, OpticalLocalRelation, OpticalObjectClass,
    OpticalObjectClassFace, RepeatedOpticalFormFibre, OPTICAL_HOLON_SCHEMA,
};
pub use optical_recovery::{
    ablate_optical_relation, bind_optical_glyph_testimony, compare_optical_controls,
    recover_optical_passage, AmbiguityAlternative, AmbiguityFibre, DeviceOpticalReceipt,
    ExteriorOpticalGlyph, NativeOpticalConsequence, OpticalAblationReturn, OpticalBounds,
    OpticalComponent, OpticalControlComparison, OpticalGlyphBinding, OpticalGlyphTestimony,
    OpticalPassage, OpticalReceiverSignature, OpticalRecoveryDemand, OpticalRegion,
    OpticalRelation, OpticalRelationKind, OpticalWorkReceipt,
};
pub use raster::{
    admit_raster_components, derive_raster_fiber, raster_component_admission_demand, raster_demand,
    PixelConnectivity, RasterComponentFiber, RasterSourceFiber,
};

#[derive(Debug)]
pub enum SourceLayoutError {
    EmptyArtifactOccurrence,
    EmptyCarrier,
    NoOccurrences,
    NoForeground,
    ForeignOccurrence,
    DuplicateOccurrenceAddress(String),
    DuplicateSerialOrdinal(u64),
    OccurrenceOutsideExtent(String),
    IncidenceUnfaithful(String),
    DecimalApertureExceeded {
        digits: usize,
        aperture: usize,
    },
    WorkCoverInsufficient {
        demand: SourceLayoutWorkDemand,
        cover: SourceLayoutWorkCover,
    },
    NonPositiveExtent,
    InvertedBox,
    MalformedDecimal(String),
    Extent,
    Device(String),
    OpticalDeviceShape,
    OpticalCoordinateNotIntegral,
    OpticalGlyphTestimonyAlreadyBound,
    OpticalGlyphOutsideExtent(u32),
    OpticalHolon(String),
    Image(holonic_engine::image::ImageCarrierError),
    Incidence(IncidenceProductionError),
}

impl std::fmt::Display for SourceLayoutError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for SourceLayoutError {}

impl From<IncidenceProductionError> for SourceLayoutError {
    fn from(error: IncidenceProductionError) -> Self {
        Self::Incidence(error)
    }
}

impl From<holonic_engine::image::ImageCarrierError> for SourceLayoutError {
    fn from(error: holonic_engine::image::ImageCarrierError) -> Self {
        Self::Image(error)
    }
}
