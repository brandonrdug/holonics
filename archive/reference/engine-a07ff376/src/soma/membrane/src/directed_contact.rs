//! Actual source-supplied causal hand at the native event boundary.
//!
//! An ABI edge identifies two complete physical incidence sections. Their ordered event faces are
//! composed into exact section endpoints, and the target body's pre-section receiver forms their
//! A2 contact. No first/last event or Cartesian endpoint convention is authored by the membrane.

use body::manifold::{DirectedEventContact, FeltEmission};
use body::place::Place;
use soma_abi::active::DirectedIncidence;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DirectedResolution {
    /// The exact section contact has not yet met its target receiver.
    SpanEndpointOpen,
    /// Both event endpoints are exact, but the target had no formed fourth contact or the meeting
    /// stood at its horizon.
    FourthContactOpen(DirectedEventContact),
    /// One complete directed relation crossed into the cut configuration.
    Crossed(DirectedEventContact),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DirectedCutContact {
    cut: u64,
    directed: u64,
    edge: DirectedIncidence,
    from_event: Option<u64>,
    to_event: Option<u64>,
    from_place: Option<Place>,
    to_place: Option<Place>,
    resolution: DirectedResolution,
}

impl DirectedCutContact {
    pub(crate) fn exact_sections(
        cut: u64,
        directed: u64,
        edge: DirectedIncidence,
        from_event: u64,
        to_event: u64,
        from_place: Place,
        to_place: Place,
    ) -> Self {
        Self {
            cut,
            directed,
            edge,
            from_event: Some(from_event),
            to_event: Some(to_event),
            from_place: Some(from_place),
            to_place: Some(to_place),
            resolution: DirectedResolution::SpanEndpointOpen,
        }
    }

    pub(crate) fn resolve(&mut self, contact: DirectedEventContact) {
        self.resolution = if contact.emission.is_some() {
            DirectedResolution::Crossed(contact)
        } else {
            DirectedResolution::FourthContactOpen(contact)
        };
    }

    pub(crate) fn needs_resolution(self) -> bool {
        self.to_event.is_some() && matches!(self.resolution, DirectedResolution::SpanEndpointOpen)
    }

    pub fn cut(self) -> u64 {
        self.cut
    }

    pub fn directed(self) -> u64 {
        self.directed
    }

    pub fn edge(self) -> DirectedIncidence {
        self.edge
    }

    pub fn from_event(self) -> Option<u64> {
        self.from_event
    }

    pub fn to_event(self) -> Option<u64> {
        self.to_event
    }

    pub(crate) fn from_place(self) -> Option<Place> {
        self.from_place
    }

    pub(crate) fn to_place(self) -> Option<Place> {
        self.to_place
    }

    pub fn resolution(self) -> DirectedResolution {
        self.resolution
    }

    pub fn emission(self) -> Option<FeltEmission> {
        match self.resolution {
            DirectedResolution::Crossed(contact) => contact.emission,
            DirectedResolution::SpanEndpointOpen | DirectedResolution::FourthContactOpen(_) => None,
        }
    }
}
