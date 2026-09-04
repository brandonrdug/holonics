//! Owner-specific exact returns crossing one owned plural mathematical passage.
//!
//! This file deliberately defines no method enum and performs no dispatch. `exact_linear` and
//! `quantity` remain the arithmetic owners. A particle owns each [`TypedPassage`] once; proposals
//! and exact returns carry only branch references.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::category::BoundaryId;
use holonic_engine::causal::EventId;
use holonic_engine::evolution::EvolutionLawId;
use holonic_engine::exact_owner_testimony::{ExactOwnerKind, ExactOwnerLicense};
use holonic_engine::exact_value::ExactValue;
use holonic_engine::ported_operation::{OperationSpecies, PortedOperationComplex, PortedWord};
use holonic_engine::quantity::{DimensionMatrix, Quantity};
use num_rational::BigRational as Rat;

use super::lineage::{operation_occurrence, pullback_join};
use super::{AddressedPassage, MathematicalParticleError, PassageEndpoint, TypedOperationWord};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PassageBranchId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedConstructionStep {
    pub event: EventId,
    pub law: EvolutionLawId,
    pub outputs: Vec<BoundaryId>,
}

/// One co-present passage occurrence. Its branch population is an exact map, not a serial word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedPassage {
    pub(super) occurrence: String,
    pub(super) source_occurrences: BTreeSet<String>,
    pub(super) staging_sources: BTreeMap<PassageBranchId, BTreeSet<String>>,
    pub(super) staging: BTreeMap<PassageBranchId, TypedConstructionStep>,
    pub(super) branches: BTreeMap<PassageBranchId, TypedOperationWord>,
    pub(super) addressed: AddressedPassage,
    pub(super) staging_front_depth: usize,
    pub(super) front_depth: usize,
    pub(super) terminal_events: BTreeMap<PassageBranchId, EventId>,
}

impl TypedPassage {
    pub fn found(
        occurrence: impl Into<String>,
        staging_sources: BTreeMap<PassageBranchId, BTreeSet<String>>,
        staging: BTreeMap<PassageBranchId, TypedConstructionStep>,
        branches: BTreeMap<PassageBranchId, TypedOperationWord>,
        operation: &PortedOperationComplex,
        admitted_sources: &BTreeSet<String>,
    ) -> Result<Self, MathematicalParticleError> {
        let occurrence = occurrence.into();
        if occurrence.is_empty()
            || branches.len() < 2
            || staging_sources.keys().collect::<BTreeSet<_>>()
                != branches.keys().collect::<BTreeSet<_>>()
            || staging.keys().collect::<BTreeSet<_>>() != branches.keys().collect::<BTreeSet<_>>()
        {
            return Err(MathematicalParticleError::Method(
                "a typed passage has no occurrence/source or is not plural".to_owned(),
            ));
        }
        let source_occurrences = staging_sources
            .values()
            .flat_map(|sources| sources.iter().cloned())
            .collect::<BTreeSet<_>>();
        if source_occurrences.is_empty() || staging_sources.values().any(BTreeSet::is_empty) {
            return Err(MathematicalParticleError::EmptySourceLineage);
        }
        if let Some(source) = source_occurrences
            .iter()
            .find(|source| !admitted_sources.contains(*source))
        {
            return Err(MathematicalParticleError::UnknownSourceOccurrence(
                source.clone(),
            ));
        }
        let mut terminal_events = BTreeMap::new();
        for (branch, word) in &branches {
            TypedOperationWord::found(&word.occurrence, word.steps.clone(), operation)?;
            terminal_events.insert(
                *branch,
                word.steps.last().expect("a founded word is nonempty").event,
            );
        }
        let fronts = operation
            .fronts()
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
        let layer_of = fronts
            .iter()
            .flat_map(|front| {
                front
                    .occurrences
                    .iter()
                    .map(move |event| (*event, front.depth))
            })
            .collect::<BTreeMap<_, _>>();
        let mut staging_front_depth = None;
        let mut addressed_occurrences = BTreeMap::new();
        let mut pullback_joins = BTreeSet::new();
        for (branch, step) in &staging {
            let occurrence = operation
                .shape
                .occurrences
                .get(&step.event)
                .ok_or(MathematicalParticleError::UnknownEvent(step.event))?;
            let law = operation
                .shape
                .laws
                .get(&step.law)
                .ok_or(MathematicalParticleError::UnknownLaw(step.law))?;
            if occurrence.law != step.law
                || !law.inputs.is_empty()
                || law.outputs != step.outputs
                || operation.operations[&step.law].species != OperationSpecies::Construction
            {
                return Err(MathematicalParticleError::StagingConstructionInvalid(
                    step.event,
                ));
            }
            let branch_word = &branches[branch];
            if branch_word.steps[0].inputs != step.outputs {
                return Err(MathematicalParticleError::StagingDoesNotFeedBranch(
                    step.event,
                ));
            }
            let staged = operation_occurrence(
                step.event,
                PassageEndpoint::Exterior(staging_sources[branch].clone()),
                PassageEndpoint::Ports(step.outputs.clone()),
                operation,
            )?;
            if addressed_occurrences
                .insert(step.event, staged.clone())
                .is_some()
            {
                return Err(MathematicalParticleError::AddressedOccurrenceKeyDisagrees);
            }
            let mut predecessor = staged;
            for word_step in &branch_word.steps {
                let addressed = operation_occurrence(
                    word_step.event,
                    PassageEndpoint::Ports(word_step.inputs.clone()),
                    PassageEndpoint::Ports(word_step.outputs.clone()),
                    operation,
                )?;
                let join = pullback_join(&predecessor, &addressed, operation).map_err(|error| {
                    if matches!(
                        error,
                        MathematicalParticleError::PullbackInteractionAbsent { .. }
                    ) {
                        MathematicalParticleError::StagingDoesNotFeedBranch(step.event)
                    } else {
                        error
                    }
                })?;
                pullback_joins.insert(join);
                if addressed_occurrences
                    .insert(word_step.event, addressed.clone())
                    .is_some()
                {
                    return Err(MathematicalParticleError::AddressedOccurrenceKeyDisagrees);
                }
                predecessor = addressed;
            }
            let depth = layer_of[&step.event];
            match staging_front_depth {
                Some(held) if held != depth => {
                    return Err(MathematicalParticleError::StagingNotCoPresent);
                }
                None => staging_front_depth = Some(depth),
                _ => {}
            }
        }
        if terminal_events.values().collect::<BTreeSet<_>>().len() != terminal_events.len() {
            return Err(MathematicalParticleError::BranchTerminalsNotDistinct);
        }
        let terminals = terminal_events.values().copied().collect::<BTreeSet<_>>();
        let front = fronts
            .iter()
            .find(|front| {
                terminals
                    .iter()
                    .all(|event| front.occurrences.contains(event))
            })
            .ok_or(MathematicalParticleError::BranchTerminalsNotCoPresent)?;
        let staging_front_depth =
            staging_front_depth.expect("staging keys equal nonempty branches");
        if staging_front_depth >= front.depth {
            return Err(MathematicalParticleError::StagingDoesNotPrecedeBranches);
        }
        let addressed = AddressedPassage::from_parts(addressed_occurrences, pullback_joins)?;
        Ok(Self {
            occurrence,
            source_occurrences,
            staging_sources,
            staging,
            branches,
            addressed,
            staging_front_depth,
            front_depth: front.depth,
            terminal_events,
        })
    }

    pub fn occurrence(&self) -> &str {
        &self.occurrence
    }

    pub fn source_occurrences(&self) -> &BTreeSet<String> {
        &self.source_occurrences
    }

    pub fn staging_sources(&self) -> &BTreeMap<PassageBranchId, BTreeSet<String>> {
        &self.staging_sources
    }

    pub fn addressed(&self) -> &AddressedPassage {
        &self.addressed
    }

    pub fn branch(&self, id: PassageBranchId) -> Option<&TypedOperationWord> {
        self.branches.get(&id)
    }

    pub fn branches(&self) -> &BTreeMap<PassageBranchId, TypedOperationWord> {
        &self.branches
    }

    pub fn staging(&self) -> &BTreeMap<PassageBranchId, TypedConstructionStep> {
        &self.staging
    }

    pub fn staging_front_depth(&self) -> usize {
        self.staging_front_depth
    }

    pub fn front_depth(&self) -> usize {
        self.front_depth
    }

    pub fn terminal_events(&self) -> &BTreeMap<PassageBranchId, EventId> {
        &self.terminal_events
    }

    pub fn reference(
        &self,
        branch: PassageBranchId,
    ) -> Result<TypedPassageRef, MathematicalParticleError> {
        self.branches
            .contains_key(&branch)
            .then(|| TypedPassageRef {
                passage: self.occurrence.clone(),
                branch,
            })
            .ok_or(MathematicalParticleError::UnknownPassageBranch(branch))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypedPassageRef {
    pub(super) passage: String,
    pub(super) branch: PassageBranchId,
}

impl TypedPassageRef {
    pub fn passage(&self) -> &str {
        &self.passage
    }

    pub fn branch(&self) -> PassageBranchId {
        self.branch
    }
}

fn resolve_branch<'a>(
    reference: &TypedPassageRef,
    passage: &'a TypedPassage,
) -> Result<&'a TypedOperationWord, MathematicalParticleError> {
    if reference.passage != passage.occurrence {
        return Err(MathematicalParticleError::UnknownPassage(
            reference.passage.clone(),
        ));
    }
    passage
        .branch(reference.branch)
        .ok_or(MathematicalParticleError::UnknownPassageBranch(
            reference.branch,
        ))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactLinearOwnerReturn {
    pub(super) passage: TypedPassageRef,
    pub(super) realization_word: String,
    /// Per input row: initial standing, every intermediate standing, and terminal standing.
    pub(super) lineage: Vec<Vec<Vec<Rat>>>,
    pub(super) terminal_value_face: Vec<ExactValue>,
    pub(super) steps: Vec<ExactLinearStepReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactLinearStepReceipt {
    pub event: EventId,
    pub law: EvolutionLawId,
    pub inputs: Vec<BoundaryId>,
    pub outputs: Vec<BoundaryId>,
    pub matrix_sha256: String,
    pub owner_evidence_sha256: String,
}

impl ExactLinearOwnerReturn {
    pub fn passage(&self) -> &TypedPassageRef {
        &self.passage
    }

    pub fn realization_word(&self) -> &str {
        &self.realization_word
    }

    pub fn lineage(&self) -> &[Vec<Vec<Rat>>] {
        &self.lineage
    }

    pub fn terminal_value_face(&self) -> &[ExactValue] {
        &self.terminal_value_face
    }

    pub fn steps(&self) -> &[ExactLinearStepReceipt] {
        &self.steps
    }
}

/// Enact `PortedWord` in causal order. The product matrix is not formed and no method label is
/// inspected.
pub fn conduct_exact_linear(
    reference: TypedPassageRef,
    passage: &TypedPassage,
    word: &PortedWord,
    matrices: &BTreeMap<EvolutionLawId, holonic_engine::exact_linear::ExactRatMatrix>,
    licenses: &BTreeMap<EvolutionLawId, ExactOwnerLicense>,
    standing: &[Rat],
) -> Result<ExactLinearOwnerReturn, MathematicalParticleError> {
    conduct_exact_linear_population(
        reference,
        passage,
        word,
        matrices,
        licenses,
        1,
        standing.len(),
        standing,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn conduct_exact_linear_population(
    reference: TypedPassageRef,
    passage: &TypedPassage,
    word: &PortedWord,
    matrices: &BTreeMap<EvolutionLawId, holonic_engine::exact_linear::ExactRatMatrix>,
    licenses: &BTreeMap<EvolutionLawId, ExactOwnerLicense>,
    rows: usize,
    width: usize,
    standing: &[Rat],
) -> Result<ExactLinearOwnerReturn, MathematicalParticleError> {
    let branch = resolve_branch(&reference, passage)?;
    let standing_identity = holonic_engine::exact_owner_testimony::exact_input_population_identity(
        rows, width, standing,
    )
    .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
    if word.steps.len() != branch.steps.len() {
        return Err(MathematicalParticleError::Method(
            "the exact-linear realization does not carry the referenced branch's ports".to_owned(),
        ));
    }
    let staging = &passage.staging[&reference.branch];
    let mut steps = Vec::with_capacity(branch.steps.len() + 1);
    let staging_license = licenses
        .get(&staging.law)
        .ok_or(MathematicalParticleError::MissingExactOwnerLicense)?;
    let staging_matrix = matrices
        .get(&staging.law)
        .ok_or(MathematicalParticleError::MissingExactOwnerLicense)?;
    if staging_license.owner() != ExactOwnerKind::ExactLinear
        || staging_license.constraint().law() != staging.law
        || !staging_license.constraint().inputs().is_empty()
        || staging_license
            .constraint()
            .outputs()
            .iter()
            .map(|boundary| boundary.boundary())
            .collect::<Vec<_>>()
            != staging.outputs
        || !staging_license.constraint().matches_matrix(staging_matrix)
        || staging_license.constraint().input_identity() != standing_identity
    {
        return Err(MathematicalParticleError::ExactOwnerReturnDisagrees(
            staging.law,
        ));
    }
    steps.push(ExactLinearStepReceipt {
        event: staging.event,
        law: staging.law,
        inputs: Vec::new(),
        outputs: staging.outputs.clone(),
        matrix_sha256: staging_license.constraint().matrix_sha256().to_owned(),
        owner_evidence_sha256: staging_license.evidence_sha256().to_owned(),
    });
    for (typed, realized) in branch.steps.iter().zip(&word.steps) {
        let license = licenses
            .get(&typed.law)
            .ok_or(MathematicalParticleError::MissingExactOwnerLicense)?;
        let constraint = license.constraint();
        let matrix = matrices
            .get(&typed.law)
            .ok_or(MathematicalParticleError::MissingExactOwnerLicense)?;
        if license.owner() != ExactOwnerKind::ExactLinear
            || constraint.law() != typed.law
            || typed.inputs != vec![realized.source_port]
            || typed.outputs != vec![realized.target_port]
            || matrix != &realized.matrix
            || !constraint.matches_matrix(&realized.matrix)
            || constraint.input_identity() != standing_identity
            || constraint
                .inputs()
                .iter()
                .map(|boundary| boundary.boundary())
                .collect::<Vec<_>>()
                != typed.inputs
            || constraint
                .outputs()
                .iter()
                .map(|boundary| boundary.boundary())
                .collect::<Vec<_>>()
                != typed.outputs
        {
            return Err(MathematicalParticleError::ExactOwnerReturnDisagrees(
                typed.law,
            ));
        }
        steps.push(ExactLinearStepReceipt {
            event: typed.event,
            law: typed.law,
            inputs: typed.inputs.clone(),
            outputs: typed.outputs.clone(),
            matrix_sha256: constraint.matrix_sha256().to_owned(),
            owner_evidence_sha256: license.evidence_sha256().to_owned(),
        });
    }
    let lineage = standing
        .chunks(width)
        .map(|row| {
            word.enact(row)
                .map_err(|error| MathematicalParticleError::Method(error.to_string()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let terminal_value_face = lineage
        .iter()
        .flat_map(|row| row.last().into_iter().flatten().cloned())
        .map(ExactValue::rational)
        .collect();
    Ok(ExactLinearOwnerReturn {
        passage: reference,
        realization_word: word.name.clone(),
        lineage,
        terminal_value_face,
        steps,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactQuantityOwnerReturn {
    pub(super) passage: TypedPassageRef,
    pub(super) factors: Vec<Quantity>,
    pub(super) powered_factors: Vec<Quantity>,
    pub(super) kernel_word: Vec<Rat>,
    pub(super) returned: Quantity,
    pub(super) dimension_matrix: DimensionMatrix,
    pub(super) boundary_columns: BTreeMap<EvolutionLawId, BTreeMap<BoundaryId, Vec<usize>>>,
    pub(super) owner_evidence_sha256: BTreeMap<EvolutionLawId, String>,
}

impl ExactQuantityOwnerReturn {
    pub fn passage(&self) -> &TypedPassageRef {
        &self.passage
    }

    pub fn factors(&self) -> &[Quantity] {
        &self.factors
    }

    pub fn returned(&self) -> &Quantity {
        &self.returned
    }

    pub fn powered_factors(&self) -> &[Quantity] {
        &self.powered_factors
    }

    pub fn kernel_word(&self) -> &[Rat] {
        &self.kernel_word
    }

    pub fn dimension_matrix(&self) -> &DimensionMatrix {
        &self.dimension_matrix
    }

    pub fn boundary_columns(&self) -> &BTreeMap<EvolutionLawId, BTreeMap<BoundaryId, Vec<usize>>> {
        &self.boundary_columns
    }

    pub fn owner_evidence_sha256(&self) -> &BTreeMap<EvolutionLawId, String> {
        &self.owner_evidence_sha256
    }
}

/// Compose an exact quantity product. Dimension transport and mismatch refusal remain owned by
/// `quantity`; this seam only retains the branch reference which carried it.
pub fn conduct_exact_quantity(
    reference: TypedPassageRef,
    passage: &TypedPassage,
    dimension_matrix: DimensionMatrix,
    boundary_columns: BTreeMap<EvolutionLawId, BTreeMap<BoundaryId, Vec<usize>>>,
    licenses: &BTreeMap<EvolutionLawId, ExactOwnerLicense>,
    factors: Vec<Quantity>,
) -> Result<ExactQuantityOwnerReturn, MathematicalParticleError> {
    let branch = resolve_branch(&reference, passage)?;
    if branch.steps.len() != 1 {
        return Err(MathematicalParticleError::Method(
            "one quantity return must bind one exact dimension matrix".to_owned(),
        ));
    }
    let step = &branch.steps[0];
    let staging = &passage.staging[&reference.branch];
    let matrix = dimension_matrix
        .as_exact_matrix()
        .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
    if factors.len() != dimension_matrix.extent()
        || factors
            .iter()
            .zip(dimension_matrix.dimensions())
            .any(|(factor, dimension)| factor.dimension() != dimension)
    {
        return Err(MathematicalParticleError::ExactOwnerReturnDisagrees(
            step.law,
        ));
    }
    let mut owner_evidence_sha256 = BTreeMap::new();
    let mut kernel_word = None;
    for law in [staging.law, step.law] {
        let license = licenses
            .get(&law)
            .ok_or(MathematicalParticleError::MissingExactOwnerLicense)?;
        let columns = boundary_columns
            .get(&law)
            .ok_or(MathematicalParticleError::MissingExactOwnerLicense)?;
        let constraint = license.constraint();
        if license.owner() != ExactOwnerKind::Quantity
            || constraint.law() != law
            || !constraint.matches_matrix(&matrix)
            || constraint.boundary_columns() != columns
        {
            return Err(MathematicalParticleError::ExactOwnerReturnDisagrees(law));
        }
        let held_kernel = constraint
            .quantity_kernel_word()
            .ok_or(MathematicalParticleError::ExactOwnerReturnDisagrees(law))?;
        if constraint.input_identity()
            != holonic_engine::exact_owner_testimony::exact_input_identity(held_kernel)
        {
            return Err(MathematicalParticleError::ExactOwnerReturnDisagrees(law));
        }
        match &kernel_word {
            Some(held) if held != held_kernel => {
                return Err(MathematicalParticleError::ExactOwnerReturnDisagrees(law));
            }
            None => kernel_word = Some(held_kernel.to_vec()),
            _ => {}
        }
        owner_evidence_sha256.insert(law, license.evidence_sha256().to_owned());
    }
    let kernel_word = kernel_word.expect("two quantity licenses carry kernels");
    let powered_factors = factors
        .iter()
        .zip(&kernel_word)
        .map(|(factor, exponent)| {
            factor
                .powed(exponent)
                .map_err(|error| MathematicalParticleError::Method(error.to_string()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut powered = powered_factors.iter();
    let mut returned = powered.next().cloned().ok_or_else(|| {
        MathematicalParticleError::Method("an exact quantity passage has no factor".to_owned())
    })?;
    for factor in powered {
        returned = returned
            .product(factor)
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
    }
    let contract_license = &licenses[&step.law];
    let output_dimensions = contract_license
        .constraint()
        .outputs()
        .iter()
        .flat_map(|boundary| boundary.dimensions())
        .collect::<Vec<_>>();
    if output_dimensions.is_empty()
        || !output_dimensions
            .iter()
            .all(|dimension| *dimension == returned.dimension())
    {
        return Err(MathematicalParticleError::ExactOwnerReturnDisagrees(
            step.law,
        ));
    }
    Ok(ExactQuantityOwnerReturn {
        passage: reference,
        factors,
        powered_factors,
        kernel_word,
        returned,
        dimension_matrix,
        boundary_columns,
        owner_evidence_sha256,
    })
}
