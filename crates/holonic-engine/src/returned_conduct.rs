//! A deposited circuit difference founded as passage-local reusable conduct.
//!
//! The return crosses three exact widths. [`ReturnedIncidence`] is the wide seal carrier: it binds
//! one deterministic returned occurrence to a normalized changed cell and the complete passage in
//! the deposited first production. [`ValidatedReturnedAtlas`] proves that whole population against
//! the two circuits, then condenses it to dense neutral target rows suitable for an exterior
//! resident grouping deed. [`ReturnedContactMorphology::found_from_groups`] accepts only the exact
//! groups returned by that deed and retains only [`PassageSite`] plus local causes.
//!
//! Full first-production text and bridges do not survive validation. A later production derives its
//! base afresh and copies the current passage geometry into one stable companion per supported site.
//! Returned companions never become roots, so a third turn cannot grow a route ladder.

use std::cmp::Ordering;

use holonic_structure::{LocalSequence, LocalSet};
use serde::{Deserialize, Serialize};

use crate::{
    algebraic::{CausalCellId, ComparativeMultiplicity},
    conditioned_derivation::{
        ConditionedBody, ConditionedCircuit, ConditionedDerivationRefusal, DerivationQuery,
        DerivedPassage, Passage, PassageOrigin, found_conditioned_circuit,
    },
    derivation_atlas::{CircuitAperture, RouteMovement, route_movement},
};

/// One member of a normalized cell boundary.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct BoundaryMemberAddress {
    pub grade: u32,
    pub name: String,
    /// Both monotone arms, not only their signed difference.
    pub coefficient: ComparativeMultiplicity,
}

/// A stable structural cell address. Raw [`CausalCellId`] values never cross this boundary.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct CellAddress {
    pub grade: u32,
    pub name: String,
    pub boundary: LocalSequence<BoundaryMemberAddress>,
}

/// The first-production form occurrence, distinct from any path or content address.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct FirstProductionIdentity {
    pub form: String,
}

/// The declared returned-reading form under which deterministic relation occurrences are minted.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReturnReadingIdentity {
    pub form: String,
}

/// Exterior source testimony carried by a relation but not confused with occurrence identity.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReturnSourceLineage {
    pub source: String,
}

/// One exact returned relation occurrence.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReturnOccurrenceId {
    pub reading: ReturnReadingIdentity,
    pub ordinal: u64,
}

/// The exact route movement that licensed one positive passage-cell contact.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct FoundedRouteAddress {
    pub statement: String,
    pub passage: String,
}

/// The full validation-only address of one deposited first passage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FirstPassageAddress {
    pub first_production: FirstProductionIdentity,
    pub ordinal: u64,
    pub passage: DerivedPassage,
}

impl PartialOrd for FirstPassageAddress {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FirstPassageAddress {
    fn cmp(&self, other: &Self) -> Ordering {
        passage_address_key(self).cmp(&passage_address_key(other))
    }
}

fn passage_address_key(
    address: &FirstPassageAddress,
) -> (
    &str,
    u64,
    &str,
    &str,
    &str,
    &str,
    &str,
    &[crate::conditioned_derivation::Bridge],
    &str,
) {
    (
        address.first_production.form.as_str(),
        address.ordinal,
        address.passage.name.as_str(),
        address.passage.statement.as_str(),
        address.passage.reaches.as_str(),
        address.passage.brought.as_str(),
        address.passage.stem.as_str(),
        address.passage.bridges.as_slice(),
        address.passage.text.as_str(),
    )
}

/// One exact seal row before lawful condensation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReturnedIncidence {
    pub occurrence: ReturnOccurrenceId,
    pub source_lineage: ReturnSourceLineage,
    pub founded_route: Option<FoundedRouteAddress>,
    pub passage: FirstPassageAddress,
    pub cell: CellAddress,
    pub stood_before: bool,
    pub stands_after: bool,
}

/// Minimal reusable identity: the derive pooling key plus its receiver statement.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PassageSite {
    pub statement: String,
    pub reaches: String,
    pub stem: String,
    pub brought: String,
}

impl PassageSite {
    pub fn of(passage: &DerivedPassage) -> Self {
        Self {
            statement: passage.statement.to_owned(),
            reaches: passage.reaches.to_owned(),
            stem: passage.stem.to_owned(),
            brought: passage.brought.to_owned(),
        }
    }
}

/// One condensed cause. No first-production text or bridge population remains.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReturnedCause {
    pub occurrence: ReturnOccurrenceId,
    pub source_lineage: ReturnSourceLineage,
    pub founded_route: Option<FoundedRouteAddress>,
    pub cell: CellAddress,
    pub stood_before: bool,
    pub stands_after: bool,
}

/// A canonical dense target table entry. `target` is apparatus-local, never semantic identity.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ValidatedTarget {
    pub target: u64,
    pub site: PassageSite,
}

/// One declared relation occurrence in exact reading order.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ValidatedOccurrence {
    pub occurrence: ReturnOccurrenceId,
    pub source_lineage: ReturnSourceLineage,
    pub founded_route: Option<FoundedRouteAddress>,
}

/// One neutral validated row offered to an exterior exact grouping deed.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ValidatedRelation {
    pub target: u64,
    pub cause: ReturnedCause,
}

/// Exact validation output. It is consumed when exterior groups found continuing morphology.
#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct ValidatedReturnedAtlas {
    schema: String,
    first_production_lineage: FirstProductionIdentity,
    targets: LocalSequence<ValidatedTarget>,
    occurrences: LocalSequence<ValidatedOccurrence>,
    relations: LocalSequence<ValidatedRelation>,
}

impl ValidatedReturnedAtlas {
    pub const SCHEMA: &'static str = "holonic-engine.validated-returned-atlas.v1";

    /// Recompute and compare the complete `(occurrence, passage, cell, direction)` population.
    pub fn validate(
        body: &ConditionedBody,
        query: &DerivationQuery,
        before: &ConditionedCircuit,
        after: &ConditionedCircuit,
        first_production: &FirstProductionIdentity,
        first: &[DerivedPassage],
        routes: &RouteMovement,
        reading: &ReturnReadingIdentity,
        source_lineage: &ReturnSourceLineage,
        returned: LocalSequence<ReturnedIncidence>,
    ) -> Result<Self, ReturnedConductRefusal> {
        let authoritative_first = body.derive(query)?;
        if first != authoritative_first.as_slice() {
            return Err(ReturnedConductRefusal::FirstProductionIsNotAuthoritative);
        }
        if before.aperture != after.aperture {
            return Err(ReturnedConductRefusal::CircuitAperturesDisagree);
        }
        validate_contact_aperture(before.aperture)?;
        let authoritative_before =
            found_conditioned_circuit(body.standing().to_owned(), before.aperture)?;
        let authoritative_after =
            body.circuit_from_production(query, LocalSequence::from_slice(first), after.aperture)?;
        validate_circuit_identity(
            before,
            &authoritative_before,
            ReturnedCircuitPosition::Before,
        )?;
        validate_circuit_identity(after, &authoritative_after, ReturnedCircuitPosition::After)?;
        if route_movement(&before.circuit, &after.circuit) != *routes {
            return Err(ReturnedConductRefusal::RouteMovementIsNotAuthoritative);
        }
        let expected = canonical_incidences(
            before,
            after,
            first_production,
            first,
            routes,
            reading,
            source_lineage,
        )?;
        validate_incidence_order(&returned)?;
        if let Some(surplus) = returned.iter().find(|row| !expected.contains(row)) {
            return Err(ReturnedConductRefusal::SurplusIncidence {
                incidence: surplus.to_owned(),
            });
        }
        if let Some(missing) = expected.iter().find(|row| !returned.contains(row)) {
            return Err(ReturnedConductRefusal::MissingIncidence {
                incidence: missing.to_owned(),
            });
        }

        let mut targets = LocalSequence::with_capacity(first.len());
        for (target, passage) in first.iter().enumerate() {
            targets.push(ValidatedTarget {
                target: target as u64,
                site: PassageSite::of(passage),
            });
        }
        let mut occurrences = LocalSequence::with_capacity(returned.len());
        let mut relations = LocalSequence::new();
        for incidence in returned {
            let target = incidence.passage.ordinal;
            occurrences.push(ValidatedOccurrence {
                occurrence: incidence.occurrence.to_owned(),
                source_lineage: incidence.source_lineage.to_owned(),
                founded_route: incidence.founded_route.to_owned(),
            });
            relations.push(ValidatedRelation {
                target,
                cause: ReturnedCause {
                    occurrence: incidence.occurrence,
                    source_lineage: incidence.source_lineage,
                    founded_route: incidence.founded_route,
                    cell: incidence.cell,
                    stood_before: incidence.stood_before,
                    stands_after: incidence.stands_after,
                },
            });
        }
        targets.sort();
        relations.sort();
        Ok(Self {
            schema: Self::SCHEMA.to_owned(),
            first_production_lineage: first_production.to_owned(),
            targets,
            occurrences,
            relations,
        })
    }

    pub fn schema(&self) -> &str {
        &self.schema
    }

    pub fn first_production_lineage(&self) -> &FirstProductionIdentity {
        &self.first_production_lineage
    }

    pub fn targets(&self) -> &[ValidatedTarget] {
        &self.targets
    }

    pub fn relations(&self) -> &[ValidatedRelation] {
        &self.relations
    }

    pub fn occurrences(&self) -> &[ValidatedOccurrence] {
        &self.occurrences
    }
}

/// One externally returned target group. Group chronology is target order; cause chronology is the
/// canonical validated relation order.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReturnedTargetGroup {
    pub target: u64,
    pub causes: LocalSequence<ReturnedCause>,
}

/// Minimal exact rest record.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReturnedContactRecord {
    pub site: PassageSite,
    pub causes: LocalSequence<ReturnedCause>,
}

/// Reusable returned conduct. This continuing owner intentionally does not implement `Clone`.
#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct ReturnedContactMorphology {
    schema: String,
    /// Exterior lineage only; never consulted to produce a route.
    first_production_lineage: FirstProductionIdentity,
    records: LocalSequence<ReturnedContactRecord>,
}

impl ReturnedContactMorphology {
    pub const SCHEMA: &'static str = "holonic-engine.returned-contact-morphology.v1";

    /// Found morphology only from externally returned exact groups.
    pub fn found_from_groups(
        atlas: ValidatedReturnedAtlas,
        groups: LocalSequence<ReturnedTargetGroup>,
    ) -> Result<Self, ReturnedConductRefusal> {
        validate_groups(&atlas, &groups)?;
        let mut records = LocalSequence::new();
        for group in groups {
            // Exact validation permits withdrawals, while positive support alone conducts.
            let mut positive = LocalSequence::new();
            for cause in group.causes {
                if !cause.stood_before && cause.stands_after {
                    positive.push(cause);
                }
            }
            if positive.is_empty() {
                continue;
            }
            let Some(target) = atlas
                .targets
                .iter()
                .find(|target| target.target == group.target)
            else {
                return Err(ReturnedConductRefusal::ReturnedGroupTargetIsUnknown {
                    target: group.target,
                });
            };
            records.push(ReturnedContactRecord {
                site: target.site.to_owned(),
                causes: positive,
            });
        }
        records.sort();
        Self::resume(atlas.first_production_lineage, records)
    }

    /// Resume exact minimal records decoded by an exterior rest codec.
    pub fn resume(
        first_production_lineage: FirstProductionIdentity,
        records: LocalSequence<ReturnedContactRecord>,
    ) -> Result<Self, ReturnedConductRefusal> {
        if first_production_lineage.form.is_empty() {
            return Err(ReturnedConductRefusal::FirstProductionIdentityIsEmpty);
        }
        let mut occurrences = LocalSet::new();
        for (at, record) in records.iter().enumerate() {
            validate_site(&record.site)?;
            if at > 0 && records[at - 1].site >= record.site {
                return Err(ReturnedConductRefusal::ContactRecordsAreNotCanonical { at });
            }
            if record.causes.is_empty() {
                return Err(ReturnedConductRefusal::ContactCarriesNoCause {
                    site: record.site.to_owned(),
                });
            }
            for (cause_at, cause) in record.causes.iter().enumerate() {
                validate_occurrence(&cause.occurrence)?;
                validate_source_lineage(&cause.source_lineage)?;
                validate_cell_address(&cause.cell)?;
                if cause.stood_before || !cause.stands_after {
                    return Err(ReturnedConductRefusal::ContactCauseIsNotPositive {
                        site: record.site.to_owned(),
                        cause: cause.to_owned(),
                    });
                }
                let Some(route) = &cause.founded_route else {
                    return Err(ReturnedConductRefusal::PositiveCauseCarriesNoFoundedRoute {
                        cause: cause.to_owned(),
                    });
                };
                if route.statement != record.site.statement || route.passage.is_empty() {
                    return Err(ReturnedConductRefusal::FoundedRouteMissedPassageSite {
                        site: record.site.to_owned(),
                        route: route.to_owned(),
                    });
                }
                if cause_at > 0 && record.causes[cause_at - 1] >= *cause {
                    return Err(ReturnedConductRefusal::ContactCausesAreNotCanonical {
                        site: record.site.to_owned(),
                        at: cause_at,
                    });
                }
                if !occurrences.insert(cause.occurrence.to_owned()) {
                    return Err(ReturnedConductRefusal::ReturnOccurrenceIsNotUnique {
                        occurrence: cause.occurrence.to_owned(),
                    });
                }
            }
        }
        Ok(Self {
            schema: Self::SCHEMA.to_owned(),
            first_production_lineage,
            records,
        })
    }

    pub fn schema(&self) -> &str {
        &self.schema
    }

    pub fn first_production_lineage(&self) -> &FirstProductionIdentity {
        &self.first_production_lineage
    }

    pub fn records(&self) -> &[ReturnedContactRecord] {
        &self.records
    }

    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    /// Remove all exact relation occurrences supporting one local site.
    pub fn ablate_site(
        mut self,
        site: &PassageSite,
    ) -> Result<SiteAblation, ReturnedConductRefusal> {
        let Some(at) = self.records.iter().position(|record| &record.site == site) else {
            return Err(ReturnedConductRefusal::PassageSiteWasAbsent {
                site: site.to_owned(),
            });
        };
        let removed = self.records.remove(at);
        Ok(SiteAblation {
            morphology: self,
            removed,
        })
    }

    /// Remove every operative site after the full contact was validated and grouped.
    pub fn ablate_all(mut self) -> AllSitesAblation {
        let mut removed = LocalSequence::new();
        while !self.records.is_empty() {
            removed.push(self.records.remove(0));
        }
        AllSitesAblation {
            morphology: self,
            removed,
        }
    }

    /// Derive the base afresh and add one stable companion at each supported site it carries.
    pub fn materialize(
        &self,
        body: &ConditionedBody,
        query: &DerivationQuery,
    ) -> Result<ReturnedProduction, ReturnedConductRefusal> {
        let derived = body.derive(query)?;
        unique_sites(&derived)?;
        let mut occupied = LocalSet::new();
        for standing in body.standing_derivations() {
            occupied.insert(standing.name);
        }
        for passage in &derived {
            if !occupied.insert(passage.name.to_owned()) {
                return Err(ReturnedConductRefusal::PassageNameCollision {
                    name: passage.name.to_owned(),
                });
            }
        }

        let mut base = LocalSequence::with_capacity(derived.len());
        for passage in derived {
            base.push(passage);
        }

        let mut returned = LocalSequence::new();
        for record in &self.records {
            let Some(root) = base
                .iter()
                .find(|root| PassageSite::of(root) == record.site)
            else {
                // Contact remains local to the receiver question that rederives its site.
                continue;
            };
            for cause in &record.causes {
                let Some(route) = &cause.founded_route else {
                    return Err(ReturnedConductRefusal::PositiveCauseCarriesNoFoundedRoute {
                        cause: cause.to_owned(),
                    });
                };
                if route.statement != root.statement || route.passage != root.name {
                    return Err(ReturnedConductRefusal::FoundedRouteMissedFreshRoot {
                        site: record.site.to_owned(),
                        route: route.to_owned(),
                    });
                }
            }
            let name = companion_name(root);
            if !occupied.insert(name.to_owned()) {
                return Err(ReturnedConductRefusal::PassageNameCollision { name });
            }
            returned.push(ReturnedRoute {
                site: record.site.to_owned(),
                passage: root.reemitted_as(name),
                causes: record.causes.to_owned(),
            });
        }
        Ok(ReturnedProduction {
            schema: "holonic-engine.returned-contact-production.v1".to_owned(),
            base,
            returned,
        })
    }
}

/// Result of a targeted site ablation.
#[derive(Debug, PartialEq, Eq)]
pub struct SiteAblation {
    pub morphology: ReturnedContactMorphology,
    pub removed: ReturnedContactRecord,
}

/// Result of removing every operative returned-contact site.
#[derive(Debug, PartialEq, Eq)]
pub struct AllSitesAblation {
    pub morphology: ReturnedContactMorphology,
    pub removed: LocalSequence<ReturnedContactRecord>,
}

/// One fresh companion emission.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReturnedRoute {
    pub site: PassageSite,
    pub passage: DerivedPassage,
    pub causes: LocalSequence<ReturnedCause>,
}

/// Exact base projection beside its returned companions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReturnedProduction {
    schema: String,
    base: LocalSequence<DerivedPassage>,
    returned: LocalSequence<ReturnedRoute>,
}

impl ReturnedProduction {
    pub fn schema(&self) -> &str {
        &self.schema
    }

    pub fn base(&self) -> &[DerivedPassage] {
        &self.base
    }

    pub fn returned(&self) -> &[ReturnedRoute] {
        &self.returned
    }

    pub fn passages(&self) -> LocalSequence<DerivedPassage> {
        let mut passages = self.base.to_owned();
        for route in &self.returned {
            passages.push(route.passage.to_owned());
        }
        passages
    }

    /// Recheck the base projection, then found the complete returned circuit.
    pub fn found_circuit(
        &self,
        body: &ConditionedBody,
        query: &DerivationQuery,
        aperture: CircuitAperture,
    ) -> Result<ConditionedCircuit, ReturnedConductRefusal> {
        let expected = body.derive(query)?;
        if self.base.as_ref() != expected.as_slice() {
            return Err(ReturnedConductRefusal::BaseProjectionMoved);
        }
        let opened = body.open_passages(self.passages())?;
        Ok(found_conditioned_circuit(opened.into_inner(), aperture)?)
    }
}

fn companion_name(root: &DerivedPassage) -> String {
    format!("returned_{}", root.name)
}

fn unique_sites(passages: &[DerivedPassage]) -> Result<(), ReturnedConductRefusal> {
    let mut sites = LocalSet::new();
    for passage in passages {
        let site = PassageSite::of(passage);
        if !sites.insert(site.to_owned()) {
            return Err(ReturnedConductRefusal::PassageSiteIsNotUnique { site });
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct IncidenceAddress {
    passage: FirstPassageAddress,
    cell: CellAddress,
    stood_before: bool,
    stands_after: bool,
}

/// Mint the one exact occurrence assigned to every canonical changed passage-cell relation.
pub fn canonical_incidences(
    before: &ConditionedCircuit,
    after: &ConditionedCircuit,
    first_production: &FirstProductionIdentity,
    first: &[DerivedPassage],
    routes: &RouteMovement,
    reading: &ReturnReadingIdentity,
    source_lineage: &ReturnSourceLineage,
) -> Result<LocalSequence<ReturnedIncidence>, ReturnedConductRefusal> {
    validate_reading(&reading)?;
    validate_source_lineage(source_lineage)?;
    if before.aperture != after.aperture {
        return Err(ReturnedConductRefusal::CircuitAperturesDisagree);
    }
    validate_contact_aperture(before.aperture)?;
    if route_movement(&before.circuit, &after.circuit) != *routes {
        return Err(ReturnedConductRefusal::RouteMovementIsNotAuthoritative);
    }
    let difference = canonical_difference(before, after, first_production, first)?;
    let mut returned = LocalSequence::with_capacity(difference.len());
    for (ordinal, address) in difference.iter().enumerate() {
        let founded_route = founded_route_of(address, routes)?;
        returned.push(ReturnedIncidence {
            occurrence: ReturnOccurrenceId {
                reading: reading.to_owned(),
                ordinal: ordinal as u64,
            },
            source_lineage: source_lineage.to_owned(),
            founded_route,
            passage: address.passage.to_owned(),
            cell: address.cell.to_owned(),
            stood_before: address.stood_before,
            stands_after: address.stands_after,
        });
    }
    Ok(returned)
}

fn founded_route_of(
    address: &IncidenceAddress,
    routes: &RouteMovement,
) -> Result<Option<FoundedRouteAddress>, ReturnedConductRefusal> {
    if address.stood_before || !address.stands_after {
        return Ok(None);
    }
    let passage = &address.passage.passage;
    let founded = routes
        .founded_routes()
        .get(&passage.statement)
        .is_some_and(|names| names.contains(&passage.name));
    if !founded {
        return Err(ReturnedConductRefusal::PositiveIncidenceLacksFoundedRoute {
            passage: address.passage.to_owned(),
            cell: address.cell.to_owned(),
        });
    }
    Ok(Some(FoundedRouteAddress {
        statement: passage.statement.to_owned(),
        passage: passage.name.to_owned(),
    }))
}

fn canonical_difference(
    before: &ConditionedCircuit,
    after: &ConditionedCircuit,
    first_production: &FirstProductionIdentity,
    first: &[DerivedPassage],
) -> Result<LocalSequence<IncidenceAddress>, ReturnedConductRefusal> {
    if first_production.form.is_empty() {
        return Err(ReturnedConductRefusal::FirstProductionIdentityIsEmpty);
    }
    let first = first_passages(first_production, first)?;
    let before_cells = normalized_cells(before)?;
    let after_cells = normalized_cells(after)?;
    let mut cells = LocalSet::new();
    for (cell, _) in &before_cells {
        cells.insert(cell.to_owned());
    }
    for (cell, _) in &after_cells {
        cells.insert(cell.to_owned());
    }
    let mut returned = LocalSet::new();
    for cell in cells {
        let before_id = cell_id(&before_cells, &cell);
        let after_id = cell_id(&after_cells, &cell);
        let stood_before = before_id.is_some();
        let stands_after = after_id.is_some();
        if stood_before == stands_after {
            continue;
        }
        let (circuit, id) = if let Some(id) = after_id {
            (after, id)
        } else {
            (
                before,
                before_id.expect("one side of a symmetric difference stands"),
            )
        };
        let Some(founders) = circuit.provenance.get(&id) else {
            return Err(ReturnedConductRefusal::ChangedCellIsUnclaimed {
                cell: cell.to_owned(),
            });
        };
        if founders.is_empty() {
            return Err(ReturnedConductRefusal::ChangedCellIsUnclaimed {
                cell: cell.to_owned(),
            });
        }
        for founder in founders {
            let passage = circuit.passages.get(founder.0 as usize).ok_or_else(|| {
                ReturnedConductRefusal::ChangedCellIsUnclaimed {
                    cell: cell.to_owned(),
                }
            })?;
            returned.insert(IncidenceAddress {
                passage: resolve_first_passage(passage, &first, &cell)?,
                cell: cell.to_owned(),
                stood_before,
                stands_after,
            });
        }
    }
    let mut ordered = LocalSequence::with_capacity(returned.len());
    for incidence in returned {
        ordered.push(incidence);
    }
    Ok(ordered)
}

fn first_passages(
    first_production: &FirstProductionIdentity,
    first: &[DerivedPassage],
) -> Result<LocalSequence<(PassageSite, FirstPassageAddress)>, ReturnedConductRefusal> {
    let mut sites = LocalSet::new();
    let mut passages = LocalSequence::with_capacity(first.len());
    for (ordinal, passage) in first.iter().enumerate() {
        let site = PassageSite::of(passage);
        if !sites.insert(site.to_owned()) {
            return Err(ReturnedConductRefusal::PassageSiteIsNotUnique { site });
        }
        passages.push((
            site,
            FirstPassageAddress {
                first_production: first_production.to_owned(),
                ordinal: ordinal as u64,
                passage: passage.to_owned(),
            },
        ));
    }
    Ok(passages)
}

fn resolve_first_passage(
    passage: &Passage,
    first: &[(PassageSite, FirstPassageAddress)],
    cell: &CellAddress,
) -> Result<FirstPassageAddress, ReturnedConductRefusal> {
    let PassageOrigin::Derived {
        stem,
        reaches,
        brought,
    } = &passage.origin
    else {
        return Err(ReturnedConductRefusal::DifferenceOutsideFirstProduction {
            cell: cell.to_owned(),
            passage: passage.derivation.name.to_owned(),
        });
    };
    let site = PassageSite {
        statement: passage.derivation.statement.to_owned(),
        reaches: reaches.to_owned(),
        stem: stem.to_owned(),
        brought: brought.to_owned(),
    };
    let Some((_, address)) = first.iter().find(|(candidate, _)| candidate == &site) else {
        return Err(ReturnedConductRefusal::DifferenceOutsideFirstProduction {
            cell: cell.to_owned(),
            passage: passage.derivation.name.to_owned(),
        });
    };
    let expected = &address.passage;
    if expected.name != passage.derivation.name
        || expected.statement != passage.derivation.statement
        || expected.reaches != *reaches
        || expected.stem != *stem
        || expected.brought != *brought
        || expected.text != passage.text
    {
        return Err(ReturnedConductRefusal::DifferenceOutsideFirstProduction {
            cell: cell.to_owned(),
            passage: passage.derivation.name.to_owned(),
        });
    }
    Ok(address.to_owned())
}

fn normalized_cells(
    circuit: &ConditionedCircuit,
) -> Result<LocalSequence<(CellAddress, CausalCellId)>, ReturnedConductRefusal> {
    let complex = circuit.circuit.complex();
    let mut normalized = LocalSequence::new();
    for cell in complex.cells().values() {
        let mut boundary = LocalSequence::new();
        for (member_id, coefficient) in cell.boundary.coefficients() {
            let member = complex.cell(*member_id).map_err(|refusal| {
                ReturnedConductRefusal::MalformedCircuit {
                    detail: refusal.to_string(),
                }
            })?;
            boundary.push(BoundaryMemberAddress {
                grade: member.grade,
                name: member.name.to_owned(),
                coefficient: coefficient.to_owned(),
            });
        }
        boundary.sort();
        normalized.push((
            CellAddress {
                grade: cell.grade,
                name: cell.name.to_owned(),
                boundary,
            },
            cell.id,
        ));
    }
    normalized.sort_by(|left, right| left.0.cmp(&right.0));
    for pair in normalized.windows(2) {
        if pair[0].0 == pair[1].0 {
            return Err(ReturnedConductRefusal::CellAddressIsNotUnique {
                cell: pair[0].0.to_owned(),
            });
        }
    }
    Ok(normalized)
}

/// The circuit's complete canonical structural cell population, with every raw identifier removed.
pub fn cell_addresses(
    circuit: &ConditionedCircuit,
) -> Result<LocalSequence<CellAddress>, ReturnedConductRefusal> {
    let normalized = normalized_cells(circuit)?;
    let mut addresses = LocalSequence::with_capacity(normalized.len());
    for (address, _) in normalized {
        addresses.push(address);
    }
    Ok(addresses)
}

/// Resolve one normalized address back to the exact owned passage-name population that founded it.
pub fn passages_founding_address(
    circuit: &ConditionedCircuit,
    address: &CellAddress,
) -> Result<LocalSequence<String>, ReturnedConductRefusal> {
    validate_cell_address(address)?;
    let normalized = normalized_cells(circuit)?;
    let Some((_, id)) = normalized
        .iter()
        .find(|(candidate, _)| candidate == address)
    else {
        return Err(ReturnedConductRefusal::CellAddressWasAbsent {
            cell: address.to_owned(),
        });
    };
    let Some(founders) = circuit.provenance.get(id) else {
        return Err(ReturnedConductRefusal::ChangedCellIsUnclaimed {
            cell: address.to_owned(),
        });
    };
    let mut names = LocalSequence::with_capacity(founders.len());
    for founder in founders {
        let Some(passage) = circuit.passages.get(founder.0 as usize) else {
            return Err(ReturnedConductRefusal::ChangedCellIsUnclaimed {
                cell: address.to_owned(),
            });
        };
        names.push(passage.derivation.name.to_owned());
    }
    if names.is_empty() {
        return Err(ReturnedConductRefusal::ChangedCellIsUnclaimed {
            cell: address.to_owned(),
        });
    }
    Ok(names)
}

fn cell_id(cells: &[(CellAddress, CausalCellId)], sought: &CellAddress) -> Option<CausalCellId> {
    cells
        .iter()
        .find(|(cell, _)| cell == sought)
        .map(|(_, id)| *id)
}

fn validate_circuit_identity(
    actual: &ConditionedCircuit,
    authoritative: &ConditionedCircuit,
    position: ReturnedCircuitPosition,
) -> Result<(), ReturnedConductRefusal> {
    if circuits_are_identical(actual, authoritative)? {
        return Ok(());
    }
    Err(ReturnedConductRefusal::CircuitIsNotAuthoritative { position })
}

fn circuits_are_identical(
    actual: &ConditionedCircuit,
    authoritative: &ConditionedCircuit,
) -> Result<bool, ReturnedConductRefusal> {
    if actual.aperture != authoritative.aperture
        || actual.passages != authoritative.passages
        || actual.unclaimed != authoritative.unclaimed
    {
        return Ok(false);
    }
    let actual_cells = normalized_cells(actual)?;
    let authoritative_cells = normalized_cells(authoritative)?;
    if actual_cells.len() != authoritative_cells.len() {
        return Ok(false);
    }
    for at in 0..actual_cells.len() {
        let (actual_address, actual_id) = &actual_cells[at];
        let (authoritative_address, authoritative_id) = &authoritative_cells[at];
        if actual_address != authoritative_address
            || actual.provenance.get(actual_id) != authoritative.provenance.get(authoritative_id)
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn validate_reading(reading: &ReturnReadingIdentity) -> Result<(), ReturnedConductRefusal> {
    if reading.form.is_empty() {
        return Err(ReturnedConductRefusal::ReturnReadingIdentityIsEmpty {
            reading: reading.to_owned(),
        });
    }
    Ok(())
}

fn validate_contact_aperture(aperture: CircuitAperture) -> Result<(), ReturnedConductRefusal> {
    if aperture != CircuitAperture::STATEMENT_INCIDENT {
        return Err(ReturnedConductRefusal::UnsupportedReturnedContactAperture { aperture });
    }
    Ok(())
}

fn validate_occurrence(occurrence: &ReturnOccurrenceId) -> Result<(), ReturnedConductRefusal> {
    if occurrence.reading.form.is_empty() {
        return Err(ReturnedConductRefusal::ReturnOccurrenceIdentityIsEmpty {
            occurrence: occurrence.to_owned(),
        });
    }
    Ok(())
}

fn validate_source_lineage(lineage: &ReturnSourceLineage) -> Result<(), ReturnedConductRefusal> {
    if lineage.source.is_empty() {
        return Err(ReturnedConductRefusal::ReturnSourceLineageIsEmpty {
            lineage: lineage.to_owned(),
        });
    }
    Ok(())
}

fn validate_site(site: &PassageSite) -> Result<(), ReturnedConductRefusal> {
    if site.statement.is_empty()
        || site.reaches.is_empty()
        || site.stem.is_empty()
        || site.brought.is_empty()
    {
        return Err(ReturnedConductRefusal::PassageSiteIsMalformed {
            site: site.to_owned(),
        });
    }
    Ok(())
}

fn validate_cell_address(cell: &CellAddress) -> Result<(), ReturnedConductRefusal> {
    if cell.name.is_empty() || (cell.grade == 0 && !cell.boundary.is_empty()) {
        return Err(ReturnedConductRefusal::CellAddressIsMalformed {
            cell: cell.to_owned(),
        });
    }
    for (at, member) in cell.boundary.iter().enumerate() {
        if member.name.is_empty()
            || member.coefficient.is_zero()
            || member.grade.checked_add(1) != Some(cell.grade)
            || (at > 0
                && (
                    cell.boundary[at - 1].grade,
                    cell.boundary[at - 1].name.as_str(),
                ) >= (member.grade, member.name.as_str()))
        {
            return Err(ReturnedConductRefusal::CellAddressIsMalformed {
                cell: cell.to_owned(),
            });
        }
    }
    Ok(())
}

fn validate_incidence_order(returned: &[ReturnedIncidence]) -> Result<(), ReturnedConductRefusal> {
    for (at, incidence) in returned.iter().enumerate() {
        validate_occurrence(&incidence.occurrence)?;
        if incidence.stood_before == incidence.stands_after {
            return Err(ReturnedConductRefusal::IncidenceDirectionIsNotMovement {
                at,
                incidence: incidence.to_owned(),
            });
        }
        if at > 0 && returned[at - 1] == *incidence {
            return Err(ReturnedConductRefusal::DuplicateIncidence {
                at,
                incidence: incidence.to_owned(),
            });
        }
        if at > 0 && returned[at - 1] > *incidence {
            return Err(ReturnedConductRefusal::IncidencePopulationIsNotCanonical { at });
        }
    }
    Ok(())
}

fn validate_groups(
    atlas: &ValidatedReturnedAtlas,
    groups: &[ReturnedTargetGroup],
) -> Result<(), ReturnedConductRefusal> {
    let mut opened = LocalSet::new();
    for (at, group) in groups.iter().enumerate() {
        if at > 0 && groups[at - 1].target >= group.target {
            return Err(ReturnedConductRefusal::ReturnedGroupsAreNotCanonical { at });
        }
        if group.causes.is_empty() {
            return Err(ReturnedConductRefusal::ReturnedGroupCarriesNoCause {
                target: group.target,
            });
        }
        if !atlas
            .targets
            .iter()
            .any(|target| target.target == group.target)
        {
            return Err(ReturnedConductRefusal::ReturnedGroupTargetIsUnknown {
                target: group.target,
            });
        }
        for (cause_at, cause) in group.causes.iter().enumerate() {
            if cause_at > 0 && group.causes[cause_at - 1] >= *cause {
                return Err(ReturnedConductRefusal::ReturnedGroupCausesAreNotCanonical {
                    target: group.target,
                    at: cause_at,
                });
            }
            let relation = ValidatedRelation {
                target: group.target,
                cause: cause.to_owned(),
            };
            if !opened.insert(relation.to_owned()) {
                return Err(ReturnedConductRefusal::ReturnedGroupRelationIsDuplicate { relation });
            }
        }
    }
    let mut expected = LocalSet::new();
    for relation in &atlas.relations {
        expected.insert(relation.to_owned());
    }
    if let Some(surplus) = opened.iter().find(|relation| !expected.contains(relation)) {
        return Err(ReturnedConductRefusal::ReturnedGroupRelationIsSurplus {
            relation: surplus.to_owned(),
        });
    }
    if let Some(missing) = expected.iter().find(|relation| !opened.contains(relation)) {
        return Err(ReturnedConductRefusal::ReturnedGroupRelationIsMissing {
            relation: missing.to_owned(),
        });
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReturnedCircuitPosition {
    Before,
    After,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReturnedConductRefusal {
    FirstProductionIdentityIsEmpty,
    FirstProductionIsNotAuthoritative,
    CircuitAperturesDisagree,
    UnsupportedReturnedContactAperture {
        aperture: CircuitAperture,
    },
    CircuitIsNotAuthoritative {
        position: ReturnedCircuitPosition,
    },
    RouteMovementIsNotAuthoritative,
    PositiveIncidenceLacksFoundedRoute {
        passage: FirstPassageAddress,
        cell: CellAddress,
    },
    PositiveCauseCarriesNoFoundedRoute {
        cause: ReturnedCause,
    },
    FoundedRouteMissedPassageSite {
        site: PassageSite,
        route: FoundedRouteAddress,
    },
    FoundedRouteMissedFreshRoot {
        site: PassageSite,
        route: FoundedRouteAddress,
    },
    ReturnReadingIdentityIsEmpty {
        reading: ReturnReadingIdentity,
    },
    ReturnOccurrenceIdentityIsEmpty {
        occurrence: ReturnOccurrenceId,
    },
    ReturnSourceLineageIsEmpty {
        lineage: ReturnSourceLineage,
    },
    PassageSiteIsNotUnique {
        site: PassageSite,
    },
    PassageSiteIsMalformed {
        site: PassageSite,
    },
    PassageNameCollision {
        name: String,
    },
    CellAddressIsNotUnique {
        cell: CellAddress,
    },
    CellAddressIsMalformed {
        cell: CellAddress,
    },
    CellAddressWasAbsent {
        cell: CellAddress,
    },
    ChangedCellIsUnclaimed {
        cell: CellAddress,
    },
    DifferenceOutsideFirstProduction {
        cell: CellAddress,
        passage: String,
    },
    IncidenceDirectionIsNotMovement {
        at: usize,
        incidence: ReturnedIncidence,
    },
    DuplicateIncidence {
        at: usize,
        incidence: ReturnedIncidence,
    },
    IncidencePopulationIsNotCanonical {
        at: usize,
    },
    SurplusIncidence {
        incidence: ReturnedIncidence,
    },
    MissingIncidence {
        incidence: ReturnedIncidence,
    },
    ReturnedGroupsAreNotCanonical {
        at: usize,
    },
    ReturnedGroupCarriesNoCause {
        target: u64,
    },
    ReturnedGroupTargetIsUnknown {
        target: u64,
    },
    ReturnedGroupCausesAreNotCanonical {
        target: u64,
        at: usize,
    },
    ReturnedGroupRelationIsDuplicate {
        relation: ValidatedRelation,
    },
    ReturnedGroupRelationIsSurplus {
        relation: ValidatedRelation,
    },
    ReturnedGroupRelationIsMissing {
        relation: ValidatedRelation,
    },
    ContactRecordsAreNotCanonical {
        at: usize,
    },
    ContactCarriesNoCause {
        site: PassageSite,
    },
    ContactCauseIsNotPositive {
        site: PassageSite,
        cause: ReturnedCause,
    },
    ContactCausesAreNotCanonical {
        site: PassageSite,
        at: usize,
    },
    ReturnOccurrenceIsNotUnique {
        occurrence: ReturnOccurrenceId,
    },
    PassageSiteWasAbsent {
        site: PassageSite,
    },
    BaseProjectionMoved,
    MalformedCircuit {
        detail: String,
    },
    Conditioned {
        detail: String,
    },
}

impl From<ConditionedDerivationRefusal> for ReturnedConductRefusal {
    fn from(refusal: ConditionedDerivationRefusal) -> Self {
        Self::Conditioned {
            detail: refusal.to_string(),
        }
    }
}

impl std::fmt::Display for ReturnedConductRefusal {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(out, "returned conduct refused: {self:?}")
    }
}

impl std::error::Error for ReturnedConductRefusal {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        conditioned_derivation::{expose, found_conditioned_circuit},
        rebase_invariants::PivotRule,
    };

    const STATEMENT: &str = "(h : P) : exactCarrier P";
    const FIRST_FORM: &str = "first-production-form/one";

    fn deposit() -> LocalSequence<(String, String)> {
        LocalSequence::from([
            (
                "alpha.lean".to_owned(),
                "namespace Soma\ntheorem carrier_alpha (h : P) : exactCarrier P := by\n  have bridged := exactCarry h\nend Soma\n".to_owned(),
            ),
            (
                "beta.lean".to_owned(),
                "namespace Soma\ntheorem carrier_beta (h : P) : exactCarrier P := by\n  have bridged := formalKernel h\nend Soma\n".to_owned(),
            ),
            (
                "gamma.lean".to_owned(),
                "namespace Soma\ntheorem transport_gamma (a b : Nat) : a = b := by\n  have bridged := exactTransport a\nend Soma\n".to_owned(),
            ),
        ])
    }

    fn body() -> ConditionedBody {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&[
            expose("corpus/one", "exact carrier formal kernel transport"),
            expose("corpus/two", "formal carrier exact kernel transport"),
        ]);
        body
    }

    fn reading() -> ReturnReadingIdentity {
        ReturnReadingIdentity {
            form: "returned-reading-form/one".to_owned(),
        }
    }

    fn first_production() -> FirstProductionIdentity {
        FirstProductionIdentity {
            form: FIRST_FORM.to_owned(),
        }
    }

    fn source_lineage() -> ReturnSourceLineage {
        ReturnSourceLineage {
            source: "returned-reading.sha256/example#relation-front".to_owned(),
        }
    }

    fn routes(fixture: &Fixture) -> RouteMovement {
        route_movement(&fixture.before.circuit, &fixture.after.circuit)
    }

    struct Fixture {
        body: ConditionedBody,
        query: DerivationQuery,
        before: ConditionedCircuit,
        after: ConditionedCircuit,
        first: LocalSequence<DerivedPassage>,
    }

    fn fixture() -> Fixture {
        let body = body();
        let query = DerivationQuery::reaching(STATEMENT);
        let derived = body.derive(&query).expect("first production");
        let mut first = LocalSequence::with_capacity(derived.len());
        for passage in derived {
            first.push(passage);
        }
        assert!(first.len() > 1);
        let before = found_conditioned_circuit(
            body.standing().to_owned(),
            CircuitAperture::STATEMENT_INCIDENT,
        )
        .expect("standing circuit");
        let after = body
            .circuit_from_production(
                &query,
                first.to_owned(),
                CircuitAperture::STATEMENT_INCIDENT,
            )
            .expect("first circuit");
        Fixture {
            body,
            query,
            before,
            after,
            first,
        }
    }

    fn exact(fixture: &Fixture) -> LocalSequence<ReturnedIncidence> {
        canonical_incidences(
            &fixture.before,
            &fixture.after,
            &first_production(),
            &fixture.first,
            &routes(fixture),
            &reading(),
            &source_lineage(),
        )
        .expect("canonical incidences")
    }

    fn validated(fixture: &Fixture) -> ValidatedReturnedAtlas {
        ValidatedReturnedAtlas::validate(
            &fixture.body,
            &fixture.query,
            &fixture.before,
            &fixture.after,
            &first_production(),
            &fixture.first,
            &routes(fixture),
            &reading(),
            &source_lineage(),
            exact(fixture),
        )
        .expect("validated atlas")
    }

    /// CPU audit only. Production founding has no path to this helper.
    fn offline_groups_for_audit(
        atlas: &ValidatedReturnedAtlas,
    ) -> LocalSequence<ReturnedTargetGroup> {
        let mut groups: LocalSequence<ReturnedTargetGroup> = LocalSequence::new();
        for relation in atlas.relations() {
            match groups
                .iter_mut()
                .find(|group| group.target == relation.target)
            {
                Some(group) => group.causes.push(relation.cause.to_owned()),
                None => groups.push(ReturnedTargetGroup {
                    target: relation.target,
                    causes: LocalSequence::from([relation.cause.to_owned()]),
                }),
            }
        }
        groups.sort();
        for group in &mut groups {
            group.causes.sort();
        }
        groups
    }

    #[test]
    fn forged_missing_extra_duplicate_and_reordered_rows_are_refused() {
        let fixture = fixture();
        let exact = exact(&fixture);
        assert!(exact.len() > 2);
        assert!(matches!(
            validate_contact_aperture(CircuitAperture::PER_ROUTE),
            Err(ReturnedConductRefusal::UnsupportedReturnedContactAperture {
                aperture: CircuitAperture::PER_ROUTE
            })
        ));

        let mut forged_first = fixture.first.to_owned();
        forged_first[0].bridges[0].route.push_str("/forged");
        assert!(matches!(
            ValidatedReturnedAtlas::validate(
                &fixture.body,
                &fixture.query,
                &fixture.before,
                &fixture.after,
                &first_production(),
                &forged_first,
                &routes(&fixture),
                &reading(),
                &source_lineage(),
                exact.to_owned(),
            ),
            Err(ReturnedConductRefusal::FirstProductionIsNotAuthoritative)
        ));
        assert!(matches!(
            canonical_incidences(
                &fixture.before,
                &fixture.after,
                &first_production(),
                &fixture.first,
                &route_movement(&fixture.before.circuit, &fixture.before.circuit),
                &reading(),
                &source_lineage(),
            ),
            Err(ReturnedConductRefusal::RouteMovementIsNotAuthoritative)
        ));
        assert!(matches!(
            ValidatedReturnedAtlas::validate(
                &fixture.body,
                &fixture.query,
                &fixture.after,
                &fixture.before,
                &first_production(),
                &fixture.first,
                &routes(&fixture),
                &reading(),
                &source_lineage(),
                exact.to_owned(),
            ),
            Err(ReturnedConductRefusal::CircuitIsNotAuthoritative {
                position: ReturnedCircuitPosition::Before
            })
        ));

        let mut forged = exact.to_owned();
        forged[0].cell.name.push_str("/forged");
        forged.sort();
        assert!(matches!(
            ValidatedReturnedAtlas::validate(
                &fixture.body,
                &fixture.query,
                &fixture.before,
                &fixture.after,
                &first_production(),
                &fixture.first,
                &routes(&fixture),
                &reading(),
                &source_lineage(),
                forged,
            ),
            Err(ReturnedConductRefusal::SurplusIncidence { .. })
        ));

        let mut forged_lineage = exact.to_owned();
        forged_lineage[0].source_lineage.source.push_str("/forged");
        assert!(matches!(
            ValidatedReturnedAtlas::validate(
                &fixture.body,
                &fixture.query,
                &fixture.before,
                &fixture.after,
                &first_production(),
                &fixture.first,
                &routes(&fixture),
                &reading(),
                &source_lineage(),
                forged_lineage,
            ),
            Err(ReturnedConductRefusal::SurplusIncidence { .. })
        ));

        let mut missing = exact.to_owned();
        missing.remove(0);
        assert!(matches!(
            ValidatedReturnedAtlas::validate(
                &fixture.body,
                &fixture.query,
                &fixture.before,
                &fixture.after,
                &first_production(),
                &fixture.first,
                &routes(&fixture),
                &reading(),
                &source_lineage(),
                missing,
            ),
            Err(ReturnedConductRefusal::MissingIncidence { .. })
        ));

        let mut extra = exact.to_owned();
        let mut surplus = extra[0].to_owned();
        surplus.occurrence.ordinal = exact.len() as u64 + 7;
        extra.push(surplus);
        extra.sort();
        assert!(matches!(
            ValidatedReturnedAtlas::validate(
                &fixture.body,
                &fixture.query,
                &fixture.before,
                &fixture.after,
                &first_production(),
                &fixture.first,
                &routes(&fixture),
                &reading(),
                &source_lineage(),
                extra,
            ),
            Err(ReturnedConductRefusal::SurplusIncidence { .. })
        ));

        let mut duplicate = exact.to_owned();
        duplicate.insert(1, duplicate[0].to_owned());
        assert!(matches!(
            ValidatedReturnedAtlas::validate(
                &fixture.body,
                &fixture.query,
                &fixture.before,
                &fixture.after,
                &first_production(),
                &fixture.first,
                &routes(&fixture),
                &reading(),
                &source_lineage(),
                duplicate,
            ),
            Err(ReturnedConductRefusal::DuplicateIncidence { .. })
        ));

        let mut reordered = exact;
        reordered.swap(0, 1);
        assert!(matches!(
            ValidatedReturnedAtlas::validate(
                &fixture.body,
                &fixture.query,
                &fixture.before,
                &fixture.after,
                &first_production(),
                &fixture.first,
                &routes(&fixture),
                &reading(),
                &source_lineage(),
                reordered,
            ),
            Err(ReturnedConductRefusal::IncidencePopulationIsNotCanonical { .. })
        ));
    }

    #[test]
    fn a_still_reading_founds_no_target_group_or_companion() {
        let fixture = fixture();
        let rows = canonical_incidences(
            &fixture.after,
            &fixture.after,
            &first_production(),
            &fixture.first,
            &route_movement(&fixture.after.circuit, &fixture.after.circuit),
            &reading(),
            &source_lineage(),
        )
        .expect("still rows");
        assert!(rows.is_empty());
        let morphology =
            ReturnedContactMorphology::resume(first_production(), LocalSequence::new())
                .expect("explicit still morphology");
        assert!(morphology.is_empty());
        let production = morphology
            .materialize(&fixture.body, &fixture.query)
            .expect("base only");
        assert_eq!(production.base(), fixture.first.as_ref());
        assert!(production.returned().is_empty());
    }

    #[test]
    fn exact_external_groups_reconcile_withdrawals_before_positive_condensation() {
        let site = PassageSite {
            statement: STATEMENT.to_owned(),
            reaches: "carrier_alpha".to_owned(),
            stem: "exact".to_owned(),
            brought: "exactCarry".to_owned(),
        };
        let route = FoundedRouteAddress {
            statement: STATEMENT.to_owned(),
            passage: "conditioned_exact_carrier_alpha".to_owned(),
        };
        let positive = ReturnedCause {
            occurrence: ReturnOccurrenceId {
                reading: reading(),
                ordinal: 0,
            },
            source_lineage: source_lineage(),
            founded_route: Some(route.to_owned()),
            cell: CellAddress {
                grade: 0,
                name: "founded-cell".to_owned(),
                boundary: LocalSequence::new(),
            },
            stood_before: false,
            stands_after: true,
        };
        let withdrawal = ReturnedCause {
            occurrence: ReturnOccurrenceId {
                reading: reading(),
                ordinal: 1,
            },
            source_lineage: source_lineage(),
            founded_route: None,
            cell: CellAddress {
                grade: 0,
                name: "withdrawn-cell".to_owned(),
                boundary: LocalSequence::new(),
            },
            stood_before: true,
            stands_after: false,
        };
        let atlas = ValidatedReturnedAtlas {
            schema: ValidatedReturnedAtlas::SCHEMA.to_owned(),
            first_production_lineage: first_production(),
            targets: LocalSequence::from([ValidatedTarget {
                target: 0,
                site: site.to_owned(),
            }]),
            occurrences: LocalSequence::from([
                ValidatedOccurrence {
                    occurrence: positive.occurrence.to_owned(),
                    source_lineage: positive.source_lineage.to_owned(),
                    founded_route: positive.founded_route.to_owned(),
                },
                ValidatedOccurrence {
                    occurrence: withdrawal.occurrence.to_owned(),
                    source_lineage: withdrawal.source_lineage.to_owned(),
                    founded_route: withdrawal.founded_route.to_owned(),
                },
            ]),
            relations: LocalSequence::from([
                ValidatedRelation {
                    target: 0,
                    cause: positive.to_owned(),
                },
                ValidatedRelation {
                    target: 0,
                    cause: withdrawal.to_owned(),
                },
            ]),
        };
        let morphology = ReturnedContactMorphology::found_from_groups(
            atlas,
            LocalSequence::from([ReturnedTargetGroup {
                target: 0,
                causes: LocalSequence::from([positive, withdrawal]),
            }]),
        )
        .expect("both directions reconcile before condensation");
        assert_eq!(morphology.records().len(), 1);
        assert_eq!(morphology.records()[0].site, site);
        assert_eq!(morphology.records()[0].causes.len(), 1);
        assert!(!morphology.records()[0].causes[0].stood_before);
        assert!(morphology.records()[0].causes[0].stands_after);
    }

    #[test]
    fn one_event_per_relation_supports_one_companion_per_root_and_moves_the_circuit() {
        let fixture = fixture();
        let atlas = validated(&fixture);
        assert_eq!(atlas.targets().len(), fixture.first.len());
        assert_eq!(atlas.occurrences().len(), atlas.relations().len());
        let groups = offline_groups_for_audit(&atlas);
        let morphology = ReturnedContactMorphology::found_from_groups(atlas, groups)
            .expect("contact morphology");
        assert_eq!(morphology.records().len(), fixture.first.len());
        let production = morphology
            .materialize(&fixture.body, &fixture.query)
            .expect("returned production");
        assert_eq!(production.base(), fixture.first.as_ref());
        assert_eq!(production.returned().len(), fixture.first.len());
        for route in production.returned() {
            let root = fixture
                .first
                .iter()
                .find(|root| PassageSite::of(root) == route.site)
                .expect("fresh root");
            assert_eq!(route.passage.statement, root.statement);
            assert_eq!(route.passage.reaches, root.reaches);
            assert_eq!(route.passage.stem, root.stem);
            assert_eq!(route.passage.brought, root.brought);
            assert_eq!(route.passage.bridges, root.bridges);
        }
        let returned = production
            .found_circuit(
                &fixture.body,
                &fixture.query,
                CircuitAperture::STATEMENT_INCIDENT,
            )
            .expect("returned circuit");
        assert_ne!(
            returned.circuit.complex().f_vector(),
            fixture.after.circuit.complex().f_vector()
        );
        assert_ne!(
            returned
                .circuit
                .invariants(PivotRule::SmallestMagnitude)
                .expect("returned invariants"),
            fixture
                .after
                .circuit
                .invariants(PivotRule::SmallestMagnitude)
                .expect("base invariants")
        );
        let base_cells = cell_addresses(&fixture.after).expect("base cell addresses");
        let returned_cells = cell_addresses(&returned).expect("returned cell addresses");
        let moved = returned_cells
            .iter()
            .find(|cell| !base_cells.contains(cell))
            .expect("one exact returned cell moved");
        let founders =
            passages_founding_address(&returned, moved).expect("moved cell has exact founders");
        assert!(production.returned().iter().any(|route| {
            founders
                .iter()
                .any(|founder| founder == &route.passage.name)
        }));
    }

    #[test]
    fn targeted_site_ablation_preserves_every_unrelated_returned_route() {
        let fixture = fixture();
        let atlas = validated(&fixture);
        let groups = offline_groups_for_audit(&atlas);
        let full =
            ReturnedContactMorphology::found_from_groups(atlas, groups).expect("full morphology");
        let target = full.records()[0].site.to_owned();
        let full_production = full
            .materialize(&fixture.body, &fixture.query)
            .expect("full production");
        let ablated = full.ablate_site(&target).expect("target stands");
        assert!(!ablated.removed.causes.is_empty());
        let ablated_production = ablated
            .morphology
            .materialize(&fixture.body, &fixture.query)
            .expect("ablated production");
        assert_eq!(ablated_production.base(), full_production.base());
        assert_eq!(
            ablated_production.returned().len() + 1,
            full_production.returned().len()
        );
        assert!(
            ablated_production
                .returned()
                .iter()
                .all(|route| route.site != target)
        );
        for route in ablated_production.returned() {
            assert!(full_production.returned().contains(route));
        }
    }

    #[test]
    fn exact_records_resume_without_first_production_bytes() {
        let fixture = fixture();
        let atlas = validated(&fixture);
        let groups = offline_groups_for_audit(&atlas);
        let founded = ReturnedContactMorphology::found_from_groups(atlas, groups)
            .expect("founded morphology");
        let lineage = founded.first_production_lineage().to_owned();
        let records = LocalSequence::from_slice(founded.records());
        let resumed = ReturnedContactMorphology::resume(lineage, records).expect("resumed records");
        assert_eq!(resumed, founded);
    }

    #[test]
    fn malformed_minimal_rest_is_refused_by_the_engine_owner() {
        let fixture = fixture();
        let atlas = validated(&fixture);
        let groups = offline_groups_for_audit(&atlas);
        let founded = ReturnedContactMorphology::found_from_groups(atlas, groups)
            .expect("founded morphology");
        let lineage = founded.first_production_lineage().to_owned();
        let mut malformed_site = LocalSequence::from_slice(founded.records());
        malformed_site[0].site.statement.clear();
        assert!(matches!(
            ReturnedContactMorphology::resume(lineage.to_owned(), malformed_site),
            Err(ReturnedConductRefusal::PassageSiteIsMalformed { .. })
        ));

        let mut malformed_cell = LocalSequence::from_slice(founded.records());
        malformed_cell[0].causes[0].cell.name.clear();
        assert!(matches!(
            ReturnedContactMorphology::resume(lineage, malformed_cell),
            Err(ReturnedConductRefusal::CellAddressIsMalformed { .. })
        ));
    }

    #[test]
    fn all_site_ablation_keeps_the_same_predecessor_and_removes_every_companion() {
        let fixture = fixture();
        let atlas = validated(&fixture);
        let groups = offline_groups_for_audit(&atlas);
        let morphology = ReturnedContactMorphology::found_from_groups(atlas, groups)
            .expect("fully validated and grouped contact");
        let supported = morphology.records().len();
        let ablated = morphology.ablate_all();
        assert_eq!(ablated.removed.len(), supported);
        assert!(ablated.morphology.is_empty());
        let production = ablated
            .morphology
            .materialize(&fixture.body, &fixture.query)
            .expect("same predecessor with no operative contact");
        assert_eq!(production.base(), fixture.first.as_ref());
        assert!(production.returned().is_empty());
    }

    #[test]
    fn a_third_turn_reuses_the_same_sites_and_never_founds_a_route_ladder() {
        let fixture = fixture();
        let atlas = validated(&fixture);
        let groups = offline_groups_for_audit(&atlas);
        let morphology = ReturnedContactMorphology::found_from_groups(atlas, groups)
            .expect("contact morphology");
        let second = morphology
            .materialize(&fixture.body, &fixture.query)
            .expect("second turn");
        let third = morphology
            .materialize(&fixture.body, &fixture.query)
            .expect("third turn");
        assert_eq!(second, third);
        assert!(
            third
                .returned()
                .iter()
                .all(|route| !route.passage.name.starts_with("returned_returned_"))
        );
        let mut sites = LocalSet::new();
        for route in third.returned() {
            sites.insert(route.site.to_owned());
        }
        assert_eq!(sites.len(), fixture.first.len());
    }
}
