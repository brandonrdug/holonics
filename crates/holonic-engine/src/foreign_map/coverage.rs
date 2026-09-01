use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

/// How far the source mouth itself carried one declared population.
///
/// This is deliberately separate from [`TransportClass`]. Decoding a stored codeword does not
/// recover a transport, and manifesting a matrix does not make it a potential pathway.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum AdmissionClass {
    /// The container declared the population and the mouth has not decoded it.
    ManifestedOnly,
    /// Decoded at its own codeword grain with no remainder. This is source admission, not a lift.
    DecodedExact,
    /// Decoded into a certified enclosure carrying its remainder.
    DecodedBounded,
    /// The mouth refused it by name.
    UnreadRefused,
}

impl AdmissionClass {
    pub fn name(self) -> &'static str {
        match self {
            Self::ManifestedOnly => "manifested only",
            Self::DecodedExact => "decoded exactly",
            Self::DecodedBounded => "decoded boundedly",
            Self::UnreadRefused => "unread/refused",
        }
    }
}

/// How far an admitted population has participated in a recovered transport.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum TransportClass {
    /// No typed predecessor, successor, constitutive law, or receiver has yet been posed.
    Unposed,
    /// A transport candidate exists and no caused material has crossed it.
    PotentialOnly,
    /// Caused material crossed it and current, successor and residual returned.
    StimulatedActively,
    /// Reachable, and the declared material never excited it.
    Unexcited,
}

impl TransportClass {
    pub fn name(self) -> &'static str {
        match self {
            Self::Unposed => "unposed",
            Self::PotentialOnly => "potential-only",
            Self::StimulatedActively => "stimulated actively",
            Self::Unexcited => "unexcited",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoverageState {
    pub admission: AdmissionClass,
    pub transport: TransportClass,
}

/// The coverage ledger, on three axes because two of them disagree.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CoverageLedger {
    state: BTreeMap<String, CoverageState>,
    load_bearing: BTreeSet<String>,
}

impl CoverageLedger {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn manifest(
        &mut self,
        name: impl Into<String>,
        admission: AdmissionClass,
    ) -> Option<CoverageState> {
        self.state.insert(
            name.into(),
            CoverageState {
                admission,
                transport: TransportClass::Unposed,
            },
        )
    }

    /// Move only the mouth/admission axis and return its prior class.
    pub fn place_admission(
        &mut self,
        name: &str,
        admission: AdmissionClass,
    ) -> Option<AdmissionClass> {
        let state = self.state.get_mut(name)?;
        Some(std::mem::replace(&mut state.admission, admission))
    }

    /// Move only the transport/excitation axis and return its prior class.
    pub fn place_transport(
        &mut self,
        name: &str,
        transport: TransportClass,
    ) -> Option<TransportClass> {
        let state = self.state.get_mut(name)?;
        Some(std::mem::replace(&mut state.transport, transport))
    }

    /// Declare that the transport cannot be enacted without this population.
    ///
    /// This is the axis neither a rank census nor a byte census carries. A `1,856`-octet population
    /// of clip bounds and a `5.64` GB table are the same size on this axis if the pathway needs
    /// both.
    pub fn declare_load_bearing(&mut self, name: &str) -> bool {
        self.state.contains_key(name) && self.load_bearing.insert(name.to_owned())
    }

    pub fn state_of(&self, name: &str) -> Option<CoverageState> {
        self.state.get(name).copied()
    }

    pub fn is_load_bearing(&self, name: &str) -> bool {
        self.load_bearing.contains(name)
    }

    pub fn admission_census(&self) -> BTreeMap<AdmissionClass, usize> {
        let mut census = BTreeMap::new();
        for state in self.state.values() {
            *census.entry(state.admission).or_insert(0) += 1;
        }
        census
    }

    pub fn transport_census(&self) -> BTreeMap<TransportClass, usize> {
        let mut census = BTreeMap::new();
        for state in self.state.values() {
            *census.entry(state.transport).or_insert(0) += 1;
        }
        census
    }

    /// Load-bearing populations that are not yet actively stimulated, by name.
    ///
    /// **This is the station's own falsifier and it returns a list rather than a count.** A pathway
    /// claiming to have executed while this is non-empty has not executed.
    pub fn load_bearing_not_stimulated(&self) -> Vec<&str> {
        self.load_bearing
            .iter()
            .filter(|name| {
                !matches!(
                    self.state.get(name.as_str()).map(|state| state.transport),
                    Some(TransportClass::StimulatedActively)
                )
            })
            .map(String::as_str)
            .collect()
    }

    pub fn declared(&self) -> usize {
        self.state.len()
    }
}
