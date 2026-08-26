//! Source-neutral receiver-history recurrence for ordinary-material Athena circulation.
//!
//! The live carrier is one generalized suffix current `(state, matched_length)`. A state is a
//! receiver-equivalence class of ordered material histories; carrying one later germ applies the
//! sparse generator action and suffix fallback directly. Contact, emanative, and return factor
//! fibres are folded from developmental source labels and then sealed as native support sets.
//! Source occurrences, path positions, response rows, dyadic substring trees, and decoders do not
//! survive cultivation.

use std::collections::{BTreeMap, BTreeSet};

use body::num::COG_WORDS;
use soma_membrane::ReceiverFiberIdentity;

use crate::{
    resonance_ecology::ResonanceGerm,
    suffix_ecology::ExactLabeledSuffixEcology,
};

use super::native_material_circulation::NativeCirculationError;

const WIRE_MAGIC: [u8; 8] = *b"ATHFRC04";
const WIRE_VERSION: u32 = 4;
const CONTACT_SOURCE_SCHEMA: u64 = 0x4154_4843_4f4e_5443;
const EMANATIVE_SOURCE_SCHEMA: u64 = 0x4154_4845_4d41_4e41;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct GermKey {
    identity: ReceiverFiberIdentity,
    phase: [u32; COG_WORDS],
}

impl From<&ResonanceGerm> for GermKey {
    fn from(germ: &ResonanceGerm) -> Self {
        Self {
            identity: germ.identity().clone(),
            phase: germ.phase().words(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct NativeRecurrentEdge {
    germ: u32,
    target: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct NativeRecurrentState {
    maximum_length: u32,
    suffix: Option<u32>,
    contact_support: u32,
    emanative_support: u32,
    occurrence_population: u64,
    edge_start: u64,
    edge_len: u32,
    return_support: u32,
    return_occurrence_population: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct NativeRecurrentContact {
    pub factor_support: Vec<u32>,
    pub matched_length: u32,
    pub occurrence_population: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct NativeRecurrentBranch {
    pub germ: ResonanceGerm,
    pub target_state: (u32, u32),
    pub factor_support: Vec<u32>,
    pub greatest_context_length: u32,
    pub recurrence_multiplicity: u64,
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct NativeRecurrenceComplex {
    germs: Vec<ResonanceGerm>,
    pub factor_addresses: Vec<String>,
    supports: Vec<Vec<u32>>,
    states: Vec<NativeRecurrentState>,
    edges: Vec<NativeRecurrentEdge>,
    opening_current: (u32, u32),
    collapsed_source_occurrences: u64,
    germ_lookup: BTreeMap<GermKey, u32>,
}

impl NativeRecurrenceComplex {
    pub(super) fn condition(
        paths: &[Vec<ResonanceGerm>],
        addresses: &[&str],
        response_open_schema: u64,
        response_close_schema: u64,
    ) -> Result<Self, NativeCirculationError> {
        if paths.is_empty() || paths.len() != addresses.len() {
            return Err(NativeCirculationError::Standing);
        }

        let mut material = Vec::with_capacity(paths.len() * 2);
        let mut labels = Vec::with_capacity(paths.len() * 2);
        let mut generative_paths = Vec::with_capacity(paths.len());
        let mut opening_germ = None::<ResonanceGerm>;
        for (factor, path) in paths.iter().enumerate() {
            let open = path
                .iter()
                .position(|germ| germ.identity().schema() == response_open_schema)
                .ok_or(NativeCirculationError::Standing)?;
            if open == 0
                || open + 1 >= path.len()
                || path.last().is_none_or(|germ| {
                    germ.identity().schema() != response_close_schema
                })
            {
                return Err(NativeCirculationError::Standing);
            }
            match &opening_germ {
                Some(held) if held != &path[open] => {
                    return Err(NativeCirculationError::Standing)
                }
                Some(_) => {}
                None => opening_germ = Some(path[open].clone()),
            }
            let factor = u32::try_from(factor).map_err(|_| NativeCirculationError::Standing)?;
            material.push(path[..open].to_vec());
            labels.push(source_label(CONTACT_SOURCE_SCHEMA, factor));
            material.push(path[open..].to_vec());
            labels.push(source_label(EMANATIVE_SOURCE_SCHEMA, factor));
            generative_paths.push((factor, path[open..].to_vec()));
        }

        let ecology = ExactLabeledSuffixEcology::condition(&material, &labels)
            .map_err(|error| NativeCirculationError::Recurrence(format!("{error:?}")))?;
        let opening = ecology
            .ecology()
            .receive_path(&[opening_germ.ok_or(NativeCirculationError::Standing)?])
            .map_err(|error| NativeCirculationError::Recurrence(format!("{error:?}")))?;

        let mut return_states = BTreeMap::<u32, (BTreeSet<u32>, u64)>::new();
        for (factor, path) in &generative_paths {
            let current = ecology
                .ecology()
                .receive_path(path)
                .map_err(|error| NativeCirculationError::Recurrence(format!("{error:?}")))?;
            let entry = return_states.entry(current.state()).or_default();
            entry.0.insert(*factor);
            entry.1 = entry
                .1
                .checked_add(1)
                .ok_or(NativeCirculationError::Standing)?;
        }

        let receiver_history = ecology
            .into_receiver_history()
            .map_err(|error| NativeCirculationError::Recurrence(format!("{error:?}")))?;
        if receiver_history.states.is_empty() || receiver_history.supports.is_empty() {
            return Err(NativeCirculationError::Standing);
        }

        let mut support_lookup = BTreeMap::<Vec<u32>, u32>::new();
        let mut supports = Vec::<Vec<u32>>::new();
        intern_support(&mut support_lookup, &mut supports, Vec::new())?;
        let mut descended_supports = Vec::with_capacity(receiver_history.supports.len());
        for raw_support in &receiver_history.supports {
            let mut contact = BTreeSet::new();
            let mut emanative = BTreeSet::new();
            for source in raw_support {
                let source = receiver_history
                    .source_catalogue
                    .get(*source as usize)
                    .ok_or(NativeCirculationError::Standing)?;
                let factor = source_factor(source)?;
                match source.schema() {
                    CONTACT_SOURCE_SCHEMA => {
                        contact.insert(factor);
                    }
                    EMANATIVE_SOURCE_SCHEMA => {
                        emanative.insert(factor);
                    }
                    _ => return Err(NativeCirculationError::Standing),
                }
            }
            let contact = intern_support(
                &mut support_lookup,
                &mut supports,
                contact.into_iter().collect(),
            )?;
            let emanative = intern_support(
                &mut support_lookup,
                &mut supports,
                emanative.into_iter().collect(),
            )?;
            descended_supports.push((contact, emanative));
        }
        let mut germs = Vec::<ResonanceGerm>::new();
        let mut germ_lookup = BTreeMap::<GermKey, u32>::new();
        let mut states = Vec::with_capacity(receiver_history.states.len());
        let mut edges = Vec::new();
        let mut collapsed_source_occurrences = 0u64;

        for (at, raw) in receiver_history.states.into_iter().enumerate() {
            let (contact_support, emanative_support) = descended_supports
                .get(raw.support as usize)
                .copied()
                .ok_or(NativeCirculationError::Standing)?;
            if supports[contact_support as usize].len() < 2
                && supports[emanative_support as usize].len() < 2
            {
                collapsed_source_occurrences = collapsed_source_occurrences
                    .checked_add(raw.material_end_multiplicity)
                    .ok_or(NativeCirculationError::Standing)?;
            }
            let (return_support, return_occurrence_population) =
                match return_states.get(
                    &u32::try_from(at).map_err(|_| NativeCirculationError::Standing)?,
                ) {
                    Some((factors, population)) => (
                        intern_support(
                            &mut support_lookup,
                            &mut supports,
                            factors.iter().copied().collect(),
                        )?,
                        *population,
                    ),
                    None => (0, 0),
                };

            let edge_start =
                u64::try_from(edges.len()).map_err(|_| NativeCirculationError::Standing)?;
            let mut local = Vec::new();
            for transition in raw.transitions {
                let germ = transition.germ;
                let key = GermKey::from(&germ);
                let germ = match germ_lookup.get(&key) {
                    Some(germ) => *germ,
                    None => {
                        let id = u32::try_from(germs.len())
                            .map_err(|_| NativeCirculationError::Standing)?;
                        germ_lookup.insert(key, id);
                        germs.push(germ);
                        id
                    }
                };
                local.push(NativeRecurrentEdge {
                    germ,
                    target: transition.target,
                });
            }
            local.sort_by_key(|edge| edge.germ);
            if local.windows(2).any(|pair| pair[0].germ == pair[1].germ) {
                return Err(NativeCirculationError::Standing);
            }
            let edge_len =
                u32::try_from(local.len()).map_err(|_| NativeCirculationError::Standing)?;
            edges.extend(local);
            states.push(NativeRecurrentState {
                maximum_length: raw.maximum_length,
                suffix: raw.suffix,
                contact_support,
                emanative_support,
                occurrence_population: raw.material_end_multiplicity,
                edge_start,
                edge_len,
                return_support,
                return_occurrence_population,
            });
        }

        let complex = Self {
            germs,
            factor_addresses: addresses.iter().map(|address| (*address).to_owned()).collect(),
            supports,
            states,
            edges,
            opening_current: (opening.state(), opening.matched_length()),
            collapsed_source_occurrences,
            germ_lookup,
        };
        complex.validate()?;
        Ok(complex)
    }

    pub(super) fn factor_population(&self) -> usize {
        self.factor_addresses.len()
    }

    pub(super) fn state_population(&self) -> usize {
        self.states.len()
    }

    pub(super) fn transition_population(&self) -> usize {
        self.edges.len()
    }

    pub(super) fn support_population(&self) -> usize {
        self.supports.len()
    }

    pub(super) fn collapsed_unique_occurrences(&self) -> u64 {
        self.collapsed_source_occurrences
    }

    pub(super) fn opening_current(&self) -> (u32, u32) {
        self.opening_current
    }

    pub(super) fn contact_current(
        &self,
        path: &[ResonanceGerm],
    ) -> Result<(u32, u32), NativeCirculationError> {
        if path.is_empty() {
            return Err(NativeCirculationError::Standing);
        }
        let mut current = (0, 0);
        for germ in path {
            current = self.carry(current, germ)?;
        }
        Ok(current)
    }

    pub(super) fn terminal_contact(
        &self,
        current: (u32, u32),
    ) -> Option<NativeRecurrentContact> {
        let state = self.states.get(current.0 as usize)?;
        let factor_support = self.supports.get(state.contact_support as usize)?.clone();
        if factor_support.is_empty() {
            return None;
        }
        Some(NativeRecurrentContact {
            factor_support,
            matched_length: current.1,
            occurrence_population: state.occurrence_population,
        })
    }

    pub(super) fn carry(
        &self,
        current: (u32, u32),
        germ: &ResonanceGerm,
    ) -> Result<(u32, u32), NativeCirculationError> {
        let symbol = self.germ_lookup.get(&GermKey::from(germ)).copied();
        let mut state = current.0;
        let mut matched = current.1;
        loop {
            let held = self
                .states
                .get(state as usize)
                .ok_or(NativeCirculationError::Standing)?;
            if matched > held.maximum_length {
                return Err(NativeCirculationError::Standing);
            }
            if let Some(symbol) = symbol {
                if let Some(edge) = self
                    .edge_rows(held)?
                    .iter()
                    .find(|edge| edge.germ == symbol)
                {
                    return Ok((
                        edge.target,
                        matched
                            .checked_add(1)
                            .ok_or(NativeCirculationError::Standing)?,
                    ));
                }
            }
            let Some(suffix) = held.suffix else {
                return Ok((0, 0));
            };
            state = suffix;
            matched = matched.min(
                self.states
                    .get(state as usize)
                    .ok_or(NativeCirculationError::Standing)?
                    .maximum_length,
            );
        }
    }

    pub(super) fn frontier_current(
        &self,
        current: (u32, u32),
    ) -> Result<Vec<NativeRecurrentBranch>, NativeCirculationError> {
        let mut candidates = BTreeMap::<u32, u32>::new();
        let mut state = current.0;
        let mut context = current.1;
        while state != 0 {
            let held = self
                .states
                .get(state as usize)
                .ok_or(NativeCirculationError::Standing)?;
            if context > held.maximum_length {
                return Err(NativeCirculationError::Standing);
            }
            for edge in self.edge_rows(held)? {
                candidates.entry(edge.germ).or_insert(context);
            }
            let Some(suffix) = held.suffix else { break };
            state = suffix;
            context = context.min(
                self.states
                    .get(state as usize)
                    .ok_or(NativeCirculationError::Standing)?
                    .maximum_length,
            );
        }
        let mut branches = Vec::new();
        for (germ, greatest_context_length) in candidates {
            let germ = self
                .germs
                .get(germ as usize)
                .ok_or(NativeCirculationError::Standing)?
                .clone();
            let target_state = self.carry(current, &germ)?;
            let target = self
                .states
                .get(target_state.0 as usize)
                .ok_or(NativeCirculationError::Standing)?;
            let factor_support = self
                .supports
                .get(target.emanative_support as usize)
                .ok_or(NativeCirculationError::Standing)?
                .clone();
            if factor_support.is_empty() {
                continue;
            }
            branches.push(NativeRecurrentBranch {
                germ,
                target_state,
                factor_support,
                greatest_context_length,
                recurrence_multiplicity: target.occurrence_population,
            });
        }
        Ok(branches)
    }

    pub(super) fn is_return_state(&self, current: (u32, u32)) -> Option<(Vec<u32>, u64)> {
        let state = self.states.get(current.0 as usize)?;
        if state.return_occurrence_population == 0 {
            return None;
        }
        let support = self.supports.get(state.return_support as usize)?.clone();
        (!support.is_empty()).then_some((support, state.return_occurrence_population))
    }

    fn edge_rows(
        &self,
        state: &NativeRecurrentState,
    ) -> Result<&[NativeRecurrentEdge], NativeCirculationError> {
        let start =
            usize::try_from(state.edge_start).map_err(|_| NativeCirculationError::Standing)?;
        let end = start
            .checked_add(state.edge_len as usize)
            .filter(|end| *end <= self.edges.len())
            .ok_or(NativeCirculationError::Standing)?;
        Ok(&self.edges[start..end])
    }

    pub(super) fn validate(&self) -> Result<(), NativeCirculationError> {
        if self.factor_addresses.is_empty()
            || self.germs.is_empty()
            || self.states.is_empty()
            || self.supports.first().is_none_or(|support| !support.is_empty())
            || self.opening_current.0 as usize >= self.states.len()
            || self.opening_current.1 == 0
        {
            return Err(NativeCirculationError::Standing);
        }
        let mut addresses = BTreeSet::new();
        if self
            .factor_addresses
            .iter()
            .any(|address| address.is_empty() || !addresses.insert(address))
        {
            return Err(NativeCirculationError::Standing);
        }
        let factor_extent = self.factor_addresses.len() as u32;
        let mut support_set = BTreeSet::new();
        for support in &self.supports {
            if support.windows(2).any(|pair| pair[0] >= pair[1])
                || support.iter().any(|factor| *factor >= factor_extent)
                || !support_set.insert(support)
            {
                return Err(NativeCirculationError::Standing);
            }
        }
        if self.germ_lookup.len() != self.germs.len()
            || self.germ_lookup.iter().any(|(key, germ)| {
                self.germs
                    .get(*germ as usize)
                    .is_none_or(|held| GermKey::from(held) != *key)
            })
        {
            return Err(NativeCirculationError::Standing);
        }
        let mut next_edge = 0u64;
        for (at, state) in self.states.iter().enumerate() {
            if state.edge_start != next_edge
                || state.contact_support as usize >= self.supports.len()
                || state.emanative_support as usize >= self.supports.len()
                || state.return_support as usize >= self.supports.len()
                || (at == 0 && (state.maximum_length != 0 || state.suffix.is_some()))
                || (at > 0
                    && state.suffix.is_none_or(|suffix| {
                        suffix as usize >= self.states.len()
                            || self.states[suffix as usize].maximum_length >= state.maximum_length
                    }))
                || (state.return_occurrence_population == 0) != (state.return_support == 0)
            {
                return Err(NativeCirculationError::Standing);
            }
            let rows = self.edge_rows(state)?;
            if rows.windows(2).any(|pair| pair[0].germ >= pair[1].germ)
                || rows.iter().any(|edge| {
                    edge.germ as usize >= self.germs.len()
                        || edge.target as usize >= self.states.len()
                })
            {
                return Err(NativeCirculationError::Standing);
            }
            next_edge = next_edge
                .checked_add(u64::from(state.edge_len))
                .ok_or(NativeCirculationError::Standing)?;
        }
        if usize::try_from(next_edge).ok() != Some(self.edges.len()) {
            return Err(NativeCirculationError::Standing);
        }
        Ok(())
    }

    pub(super) fn write_to(&self, out: &mut Vec<u8>) -> Result<(), NativeCirculationError> {
        self.validate()?;
        out.extend_from_slice(&WIRE_MAGIC);
        out.extend_from_slice(&WIRE_VERSION.to_le_bytes());
        for extent in [
            self.factor_addresses.len(),
            self.germs.len(),
            self.supports.len(),
            self.states.len(),
            self.edges.len(),
        ] {
            out.extend_from_slice(
                &u64::try_from(extent)
                    .map_err(|_| NativeCirculationError::Standing)?
                    .to_le_bytes(),
            );
        }
        out.extend_from_slice(&self.opening_current.0.to_le_bytes());
        out.extend_from_slice(&self.opening_current.1.to_le_bytes());
        out.extend_from_slice(&self.collapsed_source_occurrences.to_le_bytes());
        for address in &self.factor_addresses {
            put_blob(out, address.as_bytes())?;
        }
        for germ in &self.germs {
            out.extend_from_slice(&germ.identity().schema().to_le_bytes());
            out.extend_from_slice(&(germ.identity().words().len() as u64).to_le_bytes());
            for word in germ.identity().words() {
                out.extend_from_slice(&word.to_le_bytes());
            }
            for word in germ.phase().words() {
                out.extend_from_slice(&word.to_le_bytes());
            }
        }
        for support in &self.supports {
            put_u32s(out, support)?;
        }
        for state in &self.states {
            out.extend_from_slice(&state.maximum_length.to_le_bytes());
            out.extend_from_slice(&state.suffix.unwrap_or(u32::MAX).to_le_bytes());
            out.extend_from_slice(&state.contact_support.to_le_bytes());
            out.extend_from_slice(&state.emanative_support.to_le_bytes());
            out.extend_from_slice(&state.occurrence_population.to_le_bytes());
            out.extend_from_slice(&state.edge_start.to_le_bytes());
            out.extend_from_slice(&state.edge_len.to_le_bytes());
            out.extend_from_slice(&state.return_support.to_le_bytes());
            out.extend_from_slice(&state.return_occurrence_population.to_le_bytes());
        }
        for edge in &self.edges {
            out.extend_from_slice(&edge.germ.to_le_bytes());
            out.extend_from_slice(&edge.target.to_le_bytes());
        }
        Ok(())
    }

    pub(super) fn read(bytes: &[u8]) -> Result<Self, NativeCirculationError> {
        let mut cursor = 0usize;
        if take(bytes, &mut cursor, 8)? != WIRE_MAGIC {
            return Err(NativeCirculationError::Wire("recurrent-factor magic".to_owned()));
        }
        if read_u32(bytes, &mut cursor)? != WIRE_VERSION {
            return Err(NativeCirculationError::Wire("recurrent-factor version".to_owned()));
        }
        let factor_count = read_extent(bytes, &mut cursor)?;
        let germ_count = read_extent(bytes, &mut cursor)?;
        let support_count = read_extent(bytes, &mut cursor)?;
        let state_count = read_extent(bytes, &mut cursor)?;
        let edge_count = read_extent(bytes, &mut cursor)?;
        let opening_current = (read_u32(bytes, &mut cursor)?, read_u32(bytes, &mut cursor)?);
        let collapsed_source_occurrences = read_u64(bytes, &mut cursor)?;
        let mut factor_addresses = Vec::with_capacity(factor_count);
        for _ in 0..factor_count {
            factor_addresses.push(
                String::from_utf8(read_blob(bytes, &mut cursor)?.to_vec())
                    .map_err(|error| NativeCirculationError::Wire(error.to_string()))?,
            );
        }
        let mut germs = Vec::with_capacity(germ_count);
        for _ in 0..germ_count {
            let schema = read_u64(bytes, &mut cursor)?;
            let words = read_extent(bytes, &mut cursor)?;
            let mut identity = Vec::with_capacity(words);
            for _ in 0..words {
                identity.push(read_u32(bytes, &mut cursor)?);
            }
            let mut phase = [0u32; COG_WORDS];
            for word in &mut phase {
                *word = read_u32(bytes, &mut cursor)?;
            }
            germs.push(ResonanceGerm::new(
                ReceiverFiberIdentity::new(schema, identity),
                soma_abi::active::RelationAtom::from_words(phase)
                    .ok_or(NativeCirculationError::Standing)?,
            ));
        }
        let mut supports = Vec::with_capacity(support_count);
        for _ in 0..support_count {
            supports.push(read_u32s(bytes, &mut cursor)?);
        }
        let mut states = Vec::with_capacity(state_count);
        for _ in 0..state_count {
            let maximum_length = read_u32(bytes, &mut cursor)?;
            let suffix = match read_u32(bytes, &mut cursor)? {
                u32::MAX => None,
                suffix => Some(suffix),
            };
            states.push(NativeRecurrentState {
                maximum_length,
                suffix,
                contact_support: read_u32(bytes, &mut cursor)?,
                emanative_support: read_u32(bytes, &mut cursor)?,
                occurrence_population: read_u64(bytes, &mut cursor)?,
                edge_start: read_u64(bytes, &mut cursor)?,
                edge_len: read_u32(bytes, &mut cursor)?,
                return_support: read_u32(bytes, &mut cursor)?,
                return_occurrence_population: read_u64(bytes, &mut cursor)?,
            });
        }
        let mut edges = Vec::with_capacity(edge_count);
        for _ in 0..edge_count {
            edges.push(NativeRecurrentEdge {
                germ: read_u32(bytes, &mut cursor)?,
                target: read_u32(bytes, &mut cursor)?,
            });
        }
        if cursor != bytes.len() {
            return Err(NativeCirculationError::Wire(
                "trailing recurrent-factor octets".to_owned(),
            ));
        }
        let germ_lookup = germs
            .iter()
            .enumerate()
            .map(|(at, germ)| {
                Ok((
                    GermKey::from(germ),
                    u32::try_from(at).map_err(|_| NativeCirculationError::Standing)?,
                ))
            })
            .collect::<Result<BTreeMap<_, _>, NativeCirculationError>>()?;
        let complex = Self {
            germs,
            factor_addresses,
            supports,
            states,
            edges,
            opening_current,
            collapsed_source_occurrences,
            germ_lookup,
        };
        complex.validate()?;
        Ok(complex)
    }
}

fn source_label(schema: u64, factor: u32) -> ReceiverFiberIdentity {
    ReceiverFiberIdentity::new(schema, [factor])
}

fn source_factor(source: &ReceiverFiberIdentity) -> Result<u32, NativeCirculationError> {
    if !matches!(source.schema(), CONTACT_SOURCE_SCHEMA | EMANATIVE_SOURCE_SCHEMA)
        || source.words().len() != 1
    {
        return Err(NativeCirculationError::Standing);
    }
    Ok(source.words()[0])
}

fn intern_support(
    lookup: &mut BTreeMap<Vec<u32>, u32>,
    supports: &mut Vec<Vec<u32>>,
    support: Vec<u32>,
) -> Result<u32, NativeCirculationError> {
    if let Some(id) = lookup.get(&support) {
        return Ok(*id);
    }
    let id = u32::try_from(supports.len()).map_err(|_| NativeCirculationError::Standing)?;
    lookup.insert(support.clone(), id);
    supports.push(support);
    Ok(id)
}

fn put_blob(out: &mut Vec<u8>, value: &[u8]) -> Result<(), NativeCirculationError> {
    out.extend_from_slice(
        &u64::try_from(value.len())
            .map_err(|_| NativeCirculationError::Standing)?
            .to_le_bytes(),
    );
    out.extend_from_slice(value);
    Ok(())
}

fn put_u32s(out: &mut Vec<u8>, values: &[u32]) -> Result<(), NativeCirculationError> {
    out.extend_from_slice(
        &u64::try_from(values.len())
            .map_err(|_| NativeCirculationError::Standing)?
            .to_le_bytes(),
    );
    for value in values {
        out.extend_from_slice(&value.to_le_bytes());
    }
    Ok(())
}

fn read_blob<'a>(bytes: &'a [u8], cursor: &mut usize) -> Result<&'a [u8], NativeCirculationError> {
    let len = read_extent(bytes, cursor)?;
    take(bytes, cursor, len)
}

fn read_u32s(bytes: &[u8], cursor: &mut usize) -> Result<Vec<u32>, NativeCirculationError> {
    let count = read_extent(bytes, cursor)?;
    (0..count).map(|_| read_u32(bytes, cursor)).collect()
}

fn read_extent(bytes: &[u8], cursor: &mut usize) -> Result<usize, NativeCirculationError> {
    usize::try_from(read_u64(bytes, cursor)?)
        .map_err(|_| NativeCirculationError::Wire("recurrent-factor extent".to_owned()))
}

fn read_u32(bytes: &[u8], cursor: &mut usize) -> Result<u32, NativeCirculationError> {
    let raw = take(bytes, cursor, 4)?;
    Ok(u32::from_le_bytes([raw[0], raw[1], raw[2], raw[3]]))
}

fn read_u64(bytes: &[u8], cursor: &mut usize) -> Result<u64, NativeCirculationError> {
    let raw = take(bytes, cursor, 8)?;
    Ok(u64::from_le_bytes([
        raw[0], raw[1], raw[2], raw[3], raw[4], raw[5], raw[6], raw[7],
    ]))
}

fn take<'a>(
    bytes: &'a [u8],
    cursor: &mut usize,
    len: usize,
) -> Result<&'a [u8], NativeCirculationError> {
    let end = cursor
        .checked_add(len)
        .filter(|end| *end <= bytes.len())
        .ok_or_else(|| NativeCirculationError::Wire("truncated recurrent-factor wire".to_owned()))?;
    let out = &bytes[*cursor..end];
    *cursor = end;
    Ok(out)
}

#[cfg(test)]
mod tests {
    use body::num::Cog;
    use soma_abi::active::RelationAtom;

    use super::*;

    const MATERIAL: u64 = 0x1111;
    const OPEN: u64 = 0x2222;
    const CLOSE: u64 = 0x3333;

    fn material(word: u32, phase: i64) -> ResonanceGerm {
        ResonanceGerm::new(
            ReceiverFiberIdentity::new(MATERIAL, [word]),
            RelationAtom::new(Cog::lit(phase)).unwrap(),
        )
    }

    fn boundary(schema: u64) -> ResonanceGerm {
        ResonanceGerm::new(
            ReceiverFiberIdentity::new(schema, []),
            RelationAtom::new(Cog::lit(2)).unwrap(),
        )
    }

    #[test]
    fn suffix_current_roundtrips_without_source_occurrences() {
        let paths = vec![
            vec![
                material(1, 1),
                material(2, 1),
                boundary(OPEN),
                material(7, 3),
                material(8, 3),
                boundary(CLOSE),
            ],
            vec![
                material(1, 1),
                material(3, 1),
                boundary(OPEN),
                material(7, 3),
                material(9, 3),
                boundary(CLOSE),
            ],
        ];
        let addresses = ["factor-a", "factor-b"];
        let complex = NativeRecurrenceComplex::condition(&paths, &addresses, OPEN, CLOSE).unwrap();
        let mut wire = Vec::new();
        complex.write_to(&mut wire).unwrap();
        let returned = NativeRecurrenceComplex::read(&wire).unwrap();
        assert_eq!(returned, complex);

        let contact = returned
            .contact_current(&[material(1, 1)])
            .unwrap();
        assert_eq!(
            returned.terminal_contact(contact).unwrap().factor_support,
            vec![0, 1]
        );
        let opening = returned.opening_current();
        let first = returned
            .frontier_current(opening)
            .unwrap()
            .into_iter()
            .find(|branch| branch.germ == material(7, 3))
            .unwrap();
        assert_eq!(first.factor_support, vec![0, 1]);
        let after_first = returned.carry(opening, &first.germ).unwrap();
        let second = returned.frontier_current(after_first).unwrap();
        assert!(second.iter().any(|branch| branch.germ == material(8, 3)));
        assert!(second.iter().any(|branch| branch.germ == material(9, 3)));
    }

    #[test]
    fn equal_immediate_face_separates_under_the_later_generator() {
        let paths = vec![
            vec![
                material(4, 1),
                material(5, 1),
                material(6, 1),
                boundary(OPEN),
                material(10, 3),
                material(11, 3),
                boundary(CLOSE),
            ],
            vec![
                material(4, 1),
                material(5, 1),
                material(12, 1),
                boundary(OPEN),
                material(10, 3),
                material(13, 3),
                boundary(CLOSE),
            ],
        ];
        let complex =
            NativeRecurrenceComplex::condition(&paths, &["left", "right"], OPEN, CLOSE).unwrap();
        let shared = complex
            .contact_current(&[material(4, 1), material(5, 1)])
            .unwrap();
        assert_eq!(
            complex.terminal_contact(shared).unwrap().factor_support,
            vec![0, 1]
        );
        let left = complex.carry(shared, &material(6, 1)).unwrap();
        let right = complex.carry(shared, &material(12, 1)).unwrap();
        assert_ne!(left, right);
        assert_eq!(
            complex.terminal_contact(left).unwrap().factor_support,
            vec![0]
        );
        assert_eq!(
            complex.terminal_contact(right).unwrap().factor_support,
            vec![1]
        );
    }
}
