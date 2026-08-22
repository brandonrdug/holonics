//! Typed attachment, passage, binder, and exact-owner validation.

use super::*;

pub(super) fn source_addresses(testimonies: &[SourceLayoutTestimony]) -> BTreeSet<String> {
    testimonies
        .iter()
        .flat_map(|testimony| {
            testimony
                .occurrences
                .iter()
                .map(|occurrence| occurrence.address.clone())
        })
        .collect()
}

pub(super) fn require_sources(
    held: &BTreeSet<String>,
    admitted: &BTreeSet<String>,
) -> Result<(), MathematicalParticleError> {
    if held.is_empty() {
        return Err(MathematicalParticleError::EmptySourceLineage);
    }
    held.iter()
        .find(|source| !admitted.contains(*source))
        .map_or(Ok(()), |source| {
            Err(MathematicalParticleError::UnknownSourceOccurrence(
                source.clone(),
            ))
        })
}

pub(super) fn require_unique<T: Ord>(
    items: impl IntoIterator<Item = T>,
    error: MathematicalParticleError,
) -> Result<(), MathematicalParticleError> {
    let mut seen = BTreeSet::new();
    for item in items {
        if !seen.insert(item) {
            return Err(error);
        }
    }
    Ok(())
}

pub(super) fn require_subset<T: Copy + Ord>(
    held: &BTreeSet<T>,
    admitted: &BTreeSet<T>,
    error: impl Fn(T) -> MathematicalParticleError,
) -> Result<(), MathematicalParticleError> {
    held.iter()
        .find(|item| !admitted.contains(*item))
        .copied()
        .map_or(Ok(()), |item| Err(error(item)))
}

pub(super) fn passage<'a>(
    occurrence: &str,
    passages: &'a [TypedPassage],
) -> Result<&'a TypedPassage, MathematicalParticleError> {
    passages
        .iter()
        .find(|passage| passage.occurrence == occurrence)
        .ok_or_else(|| MathematicalParticleError::UnknownPassage(occurrence.to_owned()))
}

pub(super) fn resolve_reference<'a>(
    reference: &TypedPassageRef,
    passages: &'a [TypedPassage],
) -> Result<&'a TypedOperationWord, MathematicalParticleError> {
    passage(&reference.passage, passages)?
        .branches
        .get(&reference.branch)
        .ok_or(MathematicalParticleError::UnknownPassageBranch(
            reference.branch,
        ))
}

pub(super) fn resolve_selection(
    selection: &PassageSelection,
    passages: &[TypedPassage],
) -> Result<(), MathematicalParticleError> {
    inspect_selection(selection, passages).map(|_| ())
}

pub(super) fn inspect_selection(
    selection: &PassageSelection,
    passages: &[TypedPassage],
) -> Result<BTreeSet<EvolutionLawId>, MathematicalParticleError> {
    if selection.branches.is_empty() {
        return Err(MathematicalParticleError::UnknownPassage(
            selection.passage.clone(),
        ));
    }
    let passage = passage(&selection.passage, passages)?;
    let mut laws = BTreeSet::new();
    for branch in &selection.branches {
        let staging = passage
            .staging
            .get(branch)
            .ok_or(MathematicalParticleError::UnknownPassageBranch(*branch))?;
        laws.insert(staging.law);
        let word = passage
            .branches
            .get(branch)
            .ok_or(MathematicalParticleError::UnknownPassageBranch(*branch))?;
        laws.extend(word.steps.iter().map(|step| step.law));
    }
    Ok(laws)
}

pub(super) fn validate_ports(
    typed: &[TypedPort],
    ports: &BTreeSet<BoundaryId>,
    carriers: &[CarrierOccurrence],
    binders: &[BinderScope],
    operation: &PortedOperationComplex,
) -> Result<(), MathematicalParticleError> {
    require_unique(
        typed.iter().map(|port| port.boundary.boundary()),
        MathematicalParticleError::DuplicatePortTyping,
    )?;
    let typed_ids = typed
        .iter()
        .map(|port| port.boundary.boundary())
        .collect::<BTreeSet<_>>();
    if &typed_ids != ports {
        return Err(MathematicalParticleError::PortTypingNotTotal);
    }
    for port in typed {
        let carrier = carriers.iter().find(|carrier| carrier.id == port.carrier);
        let Some(carrier) = carrier else {
            return Err(MathematicalParticleError::UnknownCarrier(port.carrier));
        };
        if port.boundary.carrier() != carrier.owner_carrier {
            return Err(MathematicalParticleError::CarrierLicenseDisagrees(
                port.boundary.boundary(),
            ));
        }
        for slot in port.boundary.tensor_slots() {
            let binder = BinderId(slot.binder);
            let Some(scope) = binders.iter().find(|scope| scope.id == binder) else {
                return Err(MathematicalParticleError::UnknownBinder(binder));
            };
            let using_laws = operation
                .shape
                .laws
                .values()
                .filter(|law| {
                    law.inputs.contains(&port.boundary.boundary())
                        || law.outputs.contains(&port.boundary.boundary())
                })
                .map(|law| law.id)
                .collect::<BTreeSet<_>>();
            if !scope.ports.contains(&port.boundary.boundary())
                || !using_laws.is_subset(&scope.laws)
            {
                return Err(MathematicalParticleError::BinderScopeDoesNotCover {
                    binder,
                    port: port.boundary.boundary(),
                });
            }
        }
    }
    Ok(())
}

pub(super) fn validate_operation_typing(
    typed: &[TypedOperation],
    operation: &PortedOperationComplex,
    hypotheses: &BTreeSet<HypothesisId>,
    branches: &BTreeSet<BranchId>,
) -> Result<(), MathematicalParticleError> {
    require_unique(
        typed.iter().map(|value| value.law),
        MathematicalParticleError::DuplicateOperationTyping,
    )?;
    let actual = operation
        .shape
        .laws
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    if typed.iter().map(|value| value.law).collect::<BTreeSet<_>>() != actual {
        return Err(MathematicalParticleError::OperationTypingNotTotal);
    }
    for value in typed {
        let law = &operation.shape.laws[&value.law];
        if value.input_arity != law.inputs.len() || value.output_arity != law.outputs.len() {
            return Err(MathematicalParticleError::ArityDisagrees(value.law));
        }
        require_subset(
            &value.hypotheses,
            hypotheses,
            MathematicalParticleError::UnknownHypothesis,
        )?;
        require_subset(
            &value.branches,
            branches,
            MathematicalParticleError::UnknownBranch,
        )?;
    }
    Ok(())
}

pub(super) fn validate_owner_typing(
    bindings: &[BindingValidation],
    ports: &[TypedPort],
) -> Result<(), MathematicalParticleError> {
    let owners = bindings
        .iter()
        .flat_map(|binding| {
            binding
                .exact_owner_licenses
                .iter()
                .map(|license| license.owner())
        })
        .collect::<BTreeSet<_>>();
    if owners != BTreeSet::from([ExactOwnerKind::ExactLinear, ExactOwnerKind::Quantity]) {
        return Err(MathematicalParticleError::MissingExactOwnerLicense);
    }
    let mut licensed = BTreeMap::new();
    for boundary in bindings
        .iter()
        .flat_map(|binding| &binding.exact_owner_licenses)
        .flat_map(|license| {
            license
                .constraint()
                .inputs()
                .iter()
                .chain(license.constraint().outputs())
        })
    {
        match licensed.insert(boundary.boundary(), boundary) {
            Some(held) if held != boundary => {
                return Err(MathematicalParticleError::ConflictingBoundaryLicense(
                    boundary.boundary(),
                ));
            }
            _ => {}
        }
    }
    for port in ports {
        if licensed.get(&port.boundary.boundary()).copied() != Some(&port.boundary) {
            return Err(MathematicalParticleError::OwnerTypingDisagrees(
                port.boundary.boundary(),
            ));
        }
    }
    Ok(())
}
