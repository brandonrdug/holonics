//! **A region the trainer owns** (`TrainRegion`): its classes, its open places, its domain and its port, and the views the field reads of it.
//! Moved from the store line's harness (`complete_language/field_train.rs`) by C4 of #603, each item's text as it stood but for its visibility.

use crate::codec::FieldCodec;
use crate::field::{Echo, Port, Region, Shares};

/// A training region: its classes, its unresolved sites, its carried faces and its locks (each
/// empty where none).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrainRegion {
    pub classes: Vec<usize>,
    pub unresolved: Vec<bool>,
    pub faces: Vec<Option<Shares>>,
    pub locked: Vec<bool>,
    /// Each carried site's echo (§15.3), empty where none.
    pub echo: Vec<Option<Echo>>,
    /// The sites its open ones were drawn from (§16.23, [`Region::domain`]).
    pub domain: Option<usize>,
    /// Its answer port (§16.24, [`Region::port`]): the first place, the void, the cells, and whether it is compared at
    /// its boundary (§16.47) rather than through its coupling.
    pub port: Option<(usize, usize, Vec<usize>, bool, Option<usize>, Option<Vec<bool>>)>,
    /// Whether its port cuts the room to its windows ([`holonics::hnn::tower::field::Port::window`]).
    pub window: bool,
    /// Whether its port compares its open places on their letters off the void ([`holonics::hnn::tower::field::Port::letters`]).
    pub letters: bool,
}

impl TrainRegion {
    /// A region carrying no face and no lock.
    pub fn plain(classes: Vec<usize>, unresolved: Vec<bool>) -> Self {
        Self { classes, unresolved, faces: Vec::new(), locked: Vec::new(), echo: Vec::new(), domain: None, port: None, window: false, letters: false }
    }
}

/// A region as the field reads it.
pub fn view_of(region: &TrainRegion) -> Region<'_> {
    Region { classes: &region.classes, unresolved: &region.unresolved, faces: &region.faces, locked: &region.locked, echo: &region.echo, domain: region.domain, port: region.port.as_ref().map(|(start, void, target, boundary, stop, heard)| Port { start: *start, void: *void, target, boundary: *boundary, stop: *stop, heard: heard.as_deref(), window: region.window, letters: region.letters }) }
}

/// The regions as the field reads them.
pub fn views_of(regions: &[TrainRegion]) -> Vec<Region<'_>> {
    regions.iter().map(view_of).collect()
}

/// A problem's region classes: the question and its line, the answer, then `void` to `length`.
pub fn region_classes(codec: &FieldCodec, q: &[usize], a: &[usize], length: usize) -> Vec<usize> {
    let mut out: Vec<usize> = q.iter().chain(a).copied().collect();
    out.resize(length, codec.void());
    out
}
