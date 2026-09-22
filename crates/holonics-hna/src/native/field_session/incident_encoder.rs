//! The exact diagonal one-hot normal law for E_in. Each exterior symbol owns one scalar H
//! and one d-dimensional B column. This is the factorization of the same normal law, not a
//! dense m-by-m statistic or a numerical encoding of a symbol ordinal.
use super::*;
use holonic_engine::{
    ExactWavePhaseTransport,
    native_ecology::constitutive_fibre::{
        BoundaryMaterialMaps, BoundaryMaterialSeed, NativeNormalPrior, NormalMaterialRest,
        ResidentNormalEnclosureSection, ResidentNormalMaterialView,
    },
};
use std::collections::BTreeSet;

pub(super) struct IncidentEncoder<'c> {
    surface: &'c ResidentSurface<'c>,
    columns: Vec<ResidentNormalMaterial<'c>>,
    width: usize,
    grain: ResidentGrain,
    /// Stable exterior symbol identity -> current codec column position.
    positions: BTreeMap<usize, usize>,
    seed: Option<BoundaryMaterialSeed>,
}
pub(super) struct IncidentEncoded<'c> {
    pub rows: ResidentNormalEnclosureSection<'c>,
    pub symbols: Vec<usize>,
    pub producing: Vec<ResidentNormalMaterialView<'c>>,
}
pub(super) struct IncidentEncoderUpdate<'c> {
    columns: Vec<(usize, ResidentNormalMaterial<'c>)>,
}
pub(super) struct IncidentEncoderAppend<'c> {
    pub identities: Vec<usize>,
    pub columns: Vec<ResidentNormalMaterial<'c>>,
}

/// A declared old-position -> new-position codec rechart.  The map is an
/// address transport; it carries no ordinal geometry or numerical values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct IncidentCodecPermutation {
    old_to_new: Vec<usize>,
}

impl<'c> IncidentEncoder<'c> {
    pub fn found(
        surface: &'c ResidentSurface<'c>,
        maps: &BoundaryMaterialMaps,
        grain: ResidentGrain,
    ) -> Result<Self> {
        maps.validate_bootstrap()?;
        let width = maps.local_complex();
        let columns = maps
            .encoder
            .iter()
            .map(|column| {
                let prior = NativeNormalPrior::from_coefficients(
                    column.iter().map(|z| vec![z.clone()]).collect(),
                )?;
                ResidentNormalMaterial::found_features_with_prior(surface, 1, width, grain, prior)
            })
            .collect::<std::result::Result<Vec<_>, _>>()?;
        Ok(Self {
            surface,
            columns,
            width,
            grain,
            positions: (0..maps.encoder.len())
                .enumerate()
                .map(|(p, id)| (id, p))
                .collect(),
            seed: None,
        })
    }

    pub fn found_with_seed(
        surface: &'c ResidentSurface<'c>,
        maps: &BoundaryMaterialMaps,
        grain: ResidentGrain,
        seed: BoundaryMaterialSeed,
    ) -> Result<Self> {
        let mut encoder = Self::found(surface, maps, grain)?;
        encoder.seed = Some(seed);
        Ok(encoder)
    }

    pub fn bind_seed(&mut self, seed: BoundaryMaterialSeed) {
        self.seed = Some(seed);
    }
    pub(super) fn inspect_columns(&self) -> Result<Vec<serde_json::Value>> {
        self.columns
            .iter()
            .map(|column| {
                Ok(json!({
                    "observations": column.observations(),
                    "state": column.inspect().map_err(invalid)?,
                    "prior": column.prior(),
                }))
            })
            .collect()
    }
    fn ones(&self, rows: usize) -> Result<ResidentNormalEnclosureSection<'c>> {
        if rows == 0 {
            return Err(invalid("empty encoder source section"));
        }
        let points = self
            .surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    rows,
                    2,
                    ResidentGrain(0),
                    64,
                    (0..rows).flat_map(|_| [(1, 1), (0, 0)]).collect(),
                )
                .map_err(invalid)?,
            )
            .map_err(invalid)?;
        Ok(ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::integers(&points)?,
            self.grain,
        )?)
    }
    pub fn encode(&self, symbols: &[usize]) -> Result<IncidentEncoded<'c>> {
        if symbols.is_empty() || symbols.iter().any(|i| !self.positions.contains_key(i)) {
            return Err(invalid("encoder source outside admitted codec"));
        }
        let feature = self.ones(1)?;
        let mut by_symbol = BTreeMap::new();
        for &symbol in symbols {
            if let std::collections::btree_map::Entry::Vacant(entry) = by_symbol.entry(symbol) {
                let position = *self
                    .positions
                    .get(&symbol)
                    .ok_or_else(|| invalid("encoder source outside admitted codec"))?;
                entry.insert(
                    self.columns[position]
                        .retained_view()
                        .read_applied_enclosed_section(&feature)?,
                );
            }
        }
        // Apply each admitted column once, then restrict those resident results by source
        // address. A repeated inscription does not create a repeated material application.
        let positions = by_symbol
            .keys()
            .enumerate()
            .map(|(row, &symbol)| (symbol, row))
            .collect::<BTreeMap<_, _>>();
        let unique = ResidentNormalEnclosureSection::concatenate_rows(
            &by_symbol.values().collect::<Vec<_>>(),
        )?;
        let addresses = symbols.iter().map(|s| positions[s]).collect::<Vec<_>>();
        let rows = unique.gather_phase_rows(
            &addresses,
            &vec![ExactWavePhaseTransport::identity(); addresses.len()],
            2 * self.width,
        )?;
        Ok(IncidentEncoded {
            rows,
            symbols: symbols.to_vec(),
            producing: self
                .columns
                .iter()
                .map(ResidentNormalMaterial::retained_view)
                .collect(),
        })
    }
    /// The encoder table `|A| × 2d`: row `a` is `E(a)`, the current column of codec identity
    /// `a`, for identities `0..alphabet`. A symbol passage indexes these rows.
    pub fn table(&self, alphabet: usize) -> Result<ResidentNormalEnclosureSection<'c>> {
        Ok(self.encode(&(0..alphabet).collect::<Vec<_>>())?.rows)
    }

    /// The encoder return of a symbol passage from its per-symbol covector `g_a = Σ_(k:u_k=a) g_k`
    /// (`|A| × 2d`) and its occurrence counts. Each column is one normal observation per
    /// occurrence with feature 1, so its update reads only `Σ g` and `k_a`: the occurrence rows
    /// are staged as `g_a` followed by `k_a − 1` zero covectors, which carries the same `H += k_a`
    /// and `B += k_a W + 2^-step Σ g` (up to the per-row rounding of the step scale). Those
    /// `k_a − 1` zero rows are transient at observe (`O(k_a)` resident rows, freed with the
    /// staging) and never retained. One row per symbol would need a weighted normal observation
    /// (`H += k f f*`), which the normal-material owner does not expose; a feature `√k_a` is not
    /// dyadic.
    pub fn prepare_pooled_return(
        &self,
        counts: &[usize],
        symbol_covector: &ResidentNormalEnclosureSection<'c>,
        step_bits: u32,
    ) -> Result<IncidentEncoderUpdate<'c>> {
        if symbol_covector.rows() != counts.len()
            || symbol_covector.components() != 2 * self.width
            || symbol_covector.grain() != self.grain
            || step_bits > 120
        {
            return Err(invalid("encoder symbol covector chart"));
        }
        let mut columns = Vec::new();
        for (symbol, &count) in counts.iter().enumerate() {
            if count == 0 {
                continue;
            }
            let position = *self
                .positions
                .get(&symbol)
                .ok_or_else(|| invalid("encoder producing codec requires explicit rechart"))?;
            let current = self
                .columns
                .get(position)
                .ok_or_else(|| invalid("encoder producing codec requires explicit rechart"))?;
            let row = symbol_covector.gather_phase_rows(
                &[symbol],
                &[ExactWavePhaseTransport::identity()],
                2 * self.width,
            )?;
            let g = if count == 1 {
                row
            } else {
                let zero = ResidentNormalEnclosureSection::zeros(
                    self.surface,
                    count - 1,
                    2 * self.width,
                    self.grain,
                )?;
                ResidentNormalEnclosureSection::concatenate_rows(&[&row, &zero])?
            };
            let feature = self.ones(count)?;
            columns.push((
                position,
                current.stage_covector_return(&feature, &g, step_bits)?,
            ));
        }
        Ok(IncidentEncoderUpdate { columns })
    }

    /// `anchor_covector` has d native complex coordinates per actual source cell. It is the
    /// return through the producing field/receiver, never an exterior class probability vector.
    pub fn prepare_return(
        &self,
        producing: &IncidentEncoded<'c>,
        anchor_covector: &ResidentNormalEnclosureSection<'c>,
        step_bits: u32,
    ) -> Result<IncidentEncoderUpdate<'c>> {
        self.prepare_symbol_return(&producing.symbols, anchor_covector, step_bits)
    }

    /// The same return from the passage's codec identities alone. Each symbol's column is one
    /// normal observation per occurrence with feature 1, so its update reads only the per-symbol
    /// sum of the returned covectors and the occurrence count; no encoded row or producing
    /// column copy is read. The column is updated at its contemporary material.
    pub fn prepare_symbol_return(
        &self,
        symbols: &[usize],
        anchor_covector: &ResidentNormalEnclosureSection<'c>,
        step_bits: u32,
    ) -> Result<IncidentEncoderUpdate<'c>> {
        if anchor_covector.rows() != symbols.len()
            || anchor_covector.components() != 2 * self.width
            || anchor_covector.grain() != self.grain
            || step_bits > 120
        {
            return Err(invalid("encoder native anchor covector chart"));
        }
        let mut occurrences: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for (row, &symbol) in symbols.iter().enumerate() {
            occurrences.entry(symbol).or_default().push(row);
        }
        let mut columns = Vec::with_capacity(occurrences.len());
        for (symbol, addresses) in occurrences {
            let position = *self
                .positions
                .get(&symbol)
                .ok_or_else(|| invalid("encoder producing codec requires explicit rechart"))?;
            let current = self
                .columns
                .get(position)
                .ok_or_else(|| invalid("encoder producing codec requires explicit rechart"))?;
            let g = anchor_covector.gather_phase_rows(
                &addresses,
                &vec![ExactWavePhaseTransport::identity(); addresses.len()],
                2 * self.width,
            )?;
            let feature = self.ones(addresses.len())?;
            columns.push((
                position,
                current.stage_covector_return(&feature, &g, step_bits)?,
            ));
        }
        Ok(IncidentEncoderUpdate { columns })
    }
    pub fn publish(&mut self, update: IncidentEncoderUpdate<'c>) {
        for (index, column) in update.columns {
            self.columns[index] = column;
        }
    }
    /// Transport the current columns through an explicit codec permutation.  A
    /// pending `IncidentEncoded` retains stable identities, so its later return
    /// automatically follows this J map when it stages an update.
    pub fn rechart(&mut self, old_to_new: Vec<usize>) -> Result<IncidentCodecPermutation> {
        let n = self.columns.len();
        if old_to_new.len() != n {
            return Err(invalid("codec permutation extent"));
        }
        let mut seen = vec![false; n];
        for &new in &old_to_new {
            if new >= n || std::mem::replace(&mut seen[new], true) {
                return Err(invalid("codec permutation is not bijective"));
            }
        }
        let old = std::mem::take(&mut self.columns);
        let mut next: Vec<Option<ResidentNormalMaterial<'c>>> =
            std::iter::repeat_with(|| None).take(n).collect();
        for (old_position, column) in old.into_iter().enumerate() {
            next[old_to_new[old_position]] = Some(column);
        }
        self.columns = next.into_iter().map(Option::unwrap).collect();
        for position in self.positions.values_mut() {
            *position = old_to_new[*position];
        }
        Ok(IncidentCodecPermutation { old_to_new })
    }
    /// Admit source-only material for new stable identities.  Existing columns
    /// and their normal statistics are untouched; no historical zero target is
    /// invented for an appended class.
    pub fn append_seed_columns(
        &mut self,
        additions: &[(usize, Vec<holonic_engine::ExactComplexWaveCurrent>)],
    ) -> Result<()> {
        let mut incoming = Vec::with_capacity(additions.len());
        let mut admitted = BTreeMap::new();
        for (identity, column) in additions {
            if self.positions.contains_key(identity)
                || admitted.insert(*identity, ()).is_some()
                || column.len() != self.width
                || column
                    .iter()
                    .all(holonic_engine::ExactComplexWaveCurrent::is_zero)
            {
                return Err(invalid("encoder append identity or width"));
            }
            let prior = NativeNormalPrior::from_coefficients(
                column.iter().map(|z| vec![z.clone()]).collect(),
            )?;
            incoming.push((
                *identity,
                ResidentNormalMaterial::found_features_with_prior(
                    self.surface,
                    1,
                    self.width,
                    self.grain,
                    prior,
                )?,
            ));
        }
        let start = self.columns.len();
        self.columns
            .extend(incoming.into_iter().map(|(_, column)| column));
        for (offset, (identity, _)) in additions.iter().enumerate() {
            self.positions.insert(*identity, start + offset);
        }
        Ok(())
    }

    pub fn prepare_append_from_seed(
        &self,
        new_count: usize,
        identities: &[usize],
    ) -> Result<IncidentEncoderAppend<'c>> {
        let seed = self
            .seed
            .ok_or_else(|| invalid("encoder append requires persisted material seed"))?;
        if new_count <= self.columns.len() || identities.len() != new_count - self.columns.len() {
            return Err(invalid("encoder append extent"));
        }
        let maps = seed.initial_maps(new_count, self.width)?;
        let mut incoming = Vec::with_capacity(identities.len());
        let mut seen = BTreeSet::new();
        for (offset, identity) in identities.iter().copied().enumerate() {
            if self.positions.contains_key(&identity) || !seen.insert(identity) {
                return Err(invalid("encoder append identity already admitted"));
            }
            let column = maps
                .encoder
                .get(self.columns.len() + offset)
                .ok_or_else(|| invalid("encoder append seeded column"))?;
            let prior = NativeNormalPrior::from_coefficients(
                column.iter().map(|z| vec![z.clone()]).collect(),
            )?;
            incoming.push(ResidentNormalMaterial::found_features_with_prior(
                self.surface,
                1,
                self.width,
                self.grain,
                prior,
            )?);
        }
        Ok(IncidentEncoderAppend {
            identities: identities.to_vec(),
            columns: incoming,
        })
    }

    pub fn publish_append(&mut self, append: IncidentEncoderAppend<'c>) -> Result<()> {
        if append.identities.len() != append.columns.len()
            || append
                .identities
                .iter()
                .any(|id| self.positions.contains_key(id))
        {
            return Err(invalid("encoder append publication"));
        }
        let start = self.columns.len();
        self.columns.extend(append.columns);
        for (offset, identity) in append.identities.into_iter().enumerate() {
            self.positions.insert(identity, start + offset);
        }
        Ok(())
    }
    pub fn producing_views(&self) -> Vec<ResidentNormalMaterialView<'c>> {
        self.columns
            .iter()
            .map(ResidentNormalMaterial::retained_view)
            .collect()
    }
    pub fn material_observations(&self) -> Vec<u64> {
        self.columns
            .iter()
            .map(ResidentNormalMaterial::observations)
            .collect()
    }
    pub fn rest(&self) -> Result<Vec<NormalMaterialRest>> {
        Ok(self
            .columns
            .iter()
            .map(|c| c.rest())
            .collect::<std::result::Result<_, _>>()?)
    }
    /// Durable identity companion for the legacy vector rest.  The material
    /// rests retain their own priors/statistics; this map retains which stable
    /// codec identity owns each column position.
    pub fn rest_with_identities(&self) -> Result<(Vec<NormalMaterialRest>, Vec<usize>)> {
        let rests = self.rest()?;
        let mut identities = vec![0usize; self.columns.len()];
        for (&identity, &position) in &self.positions {
            if position >= identities.len() {
                return Err(invalid("encoder identity position"));
            }
            identities[position] = identity;
        }
        Ok((rests, identities))
    }
    pub fn remount_with_identities(
        surface: &'c ResidentSurface<'c>,
        rests: Vec<NormalMaterialRest>,
        identities: Vec<usize>,
    ) -> Result<Self> {
        if rests.len() != identities.len() {
            return Err(invalid("encoder identity extent"));
        }
        let first = rests.first().ok_or_else(|| invalid("empty encoder rest"))?;
        let width = first.targets();
        let grain = first.grain();
        if rests.iter().any(|r| {
            r.source_chart().complex_sources() != Some(1)
                || r.targets() != width
                || r.grain() != grain
        }) {
            return Err(invalid("encoder diagonal normal rest chart"));
        }
        let mut positions = BTreeMap::new();
        for (position, &identity) in identities.iter().enumerate() {
            if positions.insert(identity, position).is_some() {
                return Err(invalid("duplicate encoder identity"));
            }
        }
        let columns = rests
            .into_iter()
            .map(|r| r.remount(surface))
            .collect::<std::result::Result<_, _>>()?;
        Ok(Self {
            surface,
            columns,
            width,
            grain,
            positions,
            seed: None,
        })
    }
}

#[cfg(test)]
#[path = "incident_encoder_tests.rs"]
mod incident_encoder_tests;
