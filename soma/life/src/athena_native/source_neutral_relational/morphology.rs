//! Relational morphology owner implementations.

use super::*;
impl SourceNeutralRelationalMorphology {
    pub fn validate(&self) -> Result<(), SourceNeutralRelationalError> {
        if self.schema != SOURCE_NEUTRAL_RELATIONAL_MORPHOLOGY_SCHEMA
            || self.factor_population == 0
            || self.faces.is_empty()
            || self.cells.is_empty()
            || self
                .factor_adjacency
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || self
                .factor_adjacency
                .iter()
                .any(|(left, right)| left >= right || *right >= self.factor_population)
            || self.faces.iter().enumerate().any(|(at, face)| {
                face.address != face_address(at as u32, face)
                    || invalid_support(&face.factor_support, self.factor_population)
                    || face.phase_population.iter().any(|phase| {
                        phase.factor >= self.factor_population
                            || phase.phase > 2
                            || phase.occurrence_population == 0
                    })
                    || face.cell_incidence.iter().any(|incidence| {
                        incidence.cell as usize >= self.cells.len()
                            || incidence.boundary_position > 3
                            || incidence.incidence_population == 0
                    })
            })
            || self.cells.iter().enumerate().any(|(at, cell)| {
                cell.address != cell_address(at as u32, cell)
                    || !matches!(cell.oriented_boundary.len(), 3 | 4)
                    || cell
                        .oriented_boundary
                        .iter()
                        .any(|face| *face as usize >= self.faces.len())
                    || invalid_support(&cell.factor_support, self.factor_population)
                    || cell.phase_population.iter().any(|phase| {
                        phase.factor >= self.factor_population
                            || phase.phase > 2
                            || phase.occurrence_population == 0
                    })
            })
            || self.identity_sha256 != self.rederived_identity()
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        Ok(())
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn factor_population(&self) -> usize {
        self.factor_population as usize
    }

    pub fn face_population(&self) -> usize {
        self.faces.len()
    }

    pub fn cell_population(&self) -> usize {
        self.cells.len()
    }

    /// Exact class of each factor under its complete quotient face/cell incidence.  The returned
    /// integers are coordinates of equal structural signatures, not hashes or semantic labels.
    pub(super) fn factor_observation_classes(
        &self,
    ) -> Result<Vec<u64>, SourceNeutralRelationalError> {
        let mut keys = vec![Vec::<(u8, u32, u64)>::new(); self.factor_population()];
        for (face_at, face) in self.faces.iter().enumerate() {
            for phase in &face.phase_population {
                keys[phase.factor as usize].push((
                    phase.phase,
                    u32::try_from(face_at).map_err(|_| SourceNeutralRelationalError::Extent)?,
                    phase.occurrence_population,
                ));
            }
        }
        for (cell_at, cell) in self.cells.iter().enumerate() {
            for phase in &cell.phase_population {
                keys[phase.factor as usize].push((
                    phase.phase.saturating_add(3),
                    u32::try_from(cell_at).map_err(|_| SourceNeutralRelationalError::Extent)?,
                    phase.occurrence_population,
                ));
            }
        }
        keys.iter_mut()
            .for_each(|signature| signature.sort_unstable());
        partition(keys.iter().map(key).collect::<Result<Vec<_>, _>>()?)
            .map(|classes| classes.into_iter().map(u64::from).collect())
    }

    /// Return the complete bounded receiver family induced by the source-neutral relational
    /// complex.  The first axis is equality of the complete stable face/cell signature.  Every
    /// later axis is one disjoint-edge section of the retained factor adjacency: the endpoints
    /// of an edge share one receiver face and every other factor remains separated.
    ///
    /// The edge sections are cultivated from the graph itself.  A new section is founded only
    /// when the next retained edge meets both endpoints of every existing section, so there is
    /// no caller-chosen width, rank, neighborhood radius, or semantic class count.  Their union
    /// reconstructs every retained adjacency exactly, while each section is an involutive local
    /// swing suitable for the existing receiver/action contraction.
    pub(crate) fn factor_receiver_axes(
        &self,
    ) -> Result<Vec<Vec<u64>>, SourceNeutralRelationalError> {
        self.validate()?;
        let mut axes = vec![self.factor_observation_classes()?];
        for matching in self.adjacency_matchings() {
            let mut observations = (0..self.factor_population)
                .map(u64::from)
                .collect::<Vec<_>>();
            for (left, right) in matching {
                observations[right as usize] = u64::from(left);
            }
            axes.push(observations);
        }
        if axes
            .iter()
            .any(|axis| axis.len() != self.factor_population())
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        Ok(axes)
    }

    /// Return the complete sparse three-phase incidence for one-time resident mounting. Face and
    /// cell rows share one address space but retain their exact reconstruction addresses. The
    /// engine, not this cold chart, derives the signed phase quotient and causal adjoint.
    pub(crate) fn resident_current_atlas(
        &self,
    ) -> Result<ResidentSparseRelationalCurrentAtlas, SourceNeutralRelationalError> {
        self.validate()?;
        let row_population = self
            .faces
            .len()
            .checked_add(self.cells.len())
            .ok_or(SourceNeutralRelationalError::Extent)?;
        let term_capacity = self
            .faces
            .iter()
            .map(|face| face.phase_population.len())
            .chain(self.cells.iter().map(|cell| cell.phase_population.len()))
            .try_fold(0_usize, |sum, extent| sum.checked_add(extent))
            .ok_or(SourceNeutralRelationalError::Extent)?;
        let mut row_offsets = Vec::with_capacity(row_population + 1);
        let mut term_factors = Vec::with_capacity(term_capacity);
        let mut term_ingress_population = Vec::with_capacity(term_capacity);
        let mut term_emanation_population = Vec::with_capacity(term_capacity);
        let mut term_return_population = Vec::with_capacity(term_capacity);
        let mut row_reconstruction_addresses = Vec::with_capacity(row_population);
        row_offsets.push(0_u64);
        for (address, populations) in self
            .faces
            .iter()
            .map(|face| (&face.address, &face.phase_population))
            .chain(
                self.cells
                    .iter()
                    .map(|cell| (&cell.address, &cell.phase_population)),
            )
        {
            let mut by_factor = BTreeMap::<u32, [u64; 3]>::new();
            for population in populations {
                let coordinate = by_factor.entry(population.factor).or_default();
                let phase = coordinate
                    .get_mut(population.phase as usize)
                    .ok_or(SourceNeutralRelationalError::Quotient)?;
                *phase = phase
                    .checked_add(population.occurrence_population)
                    .ok_or(SourceNeutralRelationalError::Extent)?;
            }
            if by_factor.is_empty() {
                return Err(SourceNeutralRelationalError::Quotient);
            }
            for (factor, populations) in by_factor {
                term_factors.push(factor);
                term_ingress_population.push(populations[0]);
                term_emanation_population.push(populations[1]);
                term_return_population.push(populations[2]);
            }
            row_offsets.push(
                u64::try_from(term_factors.len())
                    .map_err(|_| SourceNeutralRelationalError::Extent)?,
            );
            row_reconstruction_addresses.push(address.clone());
        }
        if row_offsets.len() != row_population + 1
            || term_factors.is_empty()
            || term_factors.len() != term_ingress_population.len()
            || term_factors.len() != term_emanation_population.len()
            || term_factors.len() != term_return_population.len()
        {
            return Err(SourceNeutralRelationalError::Quotient);
        }
        Ok(ResidentSparseRelationalCurrentAtlas {
            identity_sha256: self.identity_sha256.clone(),
            row_offsets,
            term_factors,
            term_ingress_population,
            term_emanation_population,
            term_return_population,
            row_reconstruction_addresses,
        })
    }

    fn adjacency_matchings(&self) -> Vec<Vec<(u32, u32)>> {
        let mut matchings = Vec::<(BTreeSet<u32>, Vec<(u32, u32)>)>::new();
        for &(left, right) in &self.factor_adjacency {
            let admitted = matchings
                .iter()
                .position(|(occupied, _)| !occupied.contains(&left) && !occupied.contains(&right))
                .unwrap_or_else(|| {
                    matchings.push((BTreeSet::new(), Vec::new()));
                    matchings.len() - 1
                });
            matchings[admitted].0.insert(left);
            matchings[admitted].0.insert(right);
            matchings[admitted].1.push((left, right));
        }
        matchings
            .into_iter()
            .map(|(_, matching)| matching)
            .collect()
    }

    pub(crate) fn rederived_identity(&self) -> String {
        digest(&(
            SOURCE_NEUTRAL_RELATIONAL_MORPHOLOGY_SCHEMA,
            self.factor_population,
            &self.factor_adjacency,
            &self.faces,
            &self.cells,
            self.obstructed_delivery_population,
        ))
    }
}
