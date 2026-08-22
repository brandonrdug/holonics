//! The one six-event ported operation topology used by M1.

use holonic_engine::category::BoundaryId;
use holonic_engine::causal::EventId;
use holonic_engine::evolution::EvolutionLawId;
use holonic_engine::interaction::OccurrencePort;
use holonic_engine::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};

#[derive(Clone, Copy)]
pub struct PortIds {
    pub affine_in: BoundaryId,
    pub affine_out: BoundaryId,
    pub heat_in: BoundaryId,
    pub heat_out: BoundaryId,
    pub quantity_in: BoundaryId,
    pub quantity_out: BoundaryId,
}

#[derive(Clone, Copy)]
pub struct LawIds {
    pub affine_enter: EvolutionLawId,
    pub affine_contract: EvolutionLawId,
    pub heat_enter: EvolutionLawId,
    pub heat_contract: EvolutionLawId,
    pub quantity_enter: EvolutionLawId,
    pub quantity_contract: EvolutionLawId,
}

impl LawIds {
    pub fn all(self) -> [EvolutionLawId; 6] {
        [
            self.affine_enter,
            self.affine_contract,
            self.heat_enter,
            self.heat_contract,
            self.quantity_enter,
            self.quantity_contract,
        ]
    }
}

#[derive(Clone, Copy)]
pub struct EventIds {
    pub affine_enter: EventId,
    pub affine_contract: EventId,
    pub heat_enter: EventId,
    pub heat_contract: EventId,
    pub quantity_enter: EventId,
    pub quantity_contract: EventId,
}

pub struct OperationTopology {
    pub operation: PortedOperationComplex,
    pub ports: PortIds,
    pub laws: LawIds,
    pub events: EventIds,
}

pub fn construct() -> Result<OperationTopology, String> {
    let mut operation = PortedOperationComplex::new("m1-three-branch-operation-complex");
    let ports = PortIds {
        affine_in: operation.port("affine-in"),
        affine_out: operation.port("affine-out"),
        heat_in: operation.port("heat-in"),
        heat_out: operation.port("heat-out"),
        quantity_in: operation.port("quantity-in"),
        quantity_out: operation.port("quantity-out"),
    };
    let pending = |question: &str| {
        vec![SourceTestimony::Undecided {
            question: question.to_owned(),
        }]
    };
    let laws = LawIds {
        affine_enter: bind(
            &mut operation,
            "affine-enter",
            OperationSpecies::Construction,
            Vec::new(),
            vec![ports.affine_in],
            pending("exact-linear owner must license the addressed affine fixture"),
        )?,
        affine_contract: bind(
            &mut operation,
            "affine-contract",
            OperationSpecies::Transport,
            vec![ports.affine_in],
            vec![ports.affine_out],
            pending("exact-linear owner must return the affine residual"),
        )?,
        heat_enter: bind(
            &mut operation,
            "heat-enter",
            OperationSpecies::Construction,
            Vec::new(),
            vec![ports.heat_in],
            pending("conditional Euclidean and t>0 hypotheses remain explicit"),
        )?,
        heat_contract: bind(
            &mut operation,
            "heat-contract",
            OperationSpecies::Transport,
            vec![ports.heat_in],
            vec![ports.heat_out],
            pending("numeric equality is a conditional fixture consequence, not a paper proof"),
        )?,
        quantity_enter: bind(
            &mut operation,
            "quantity-enter",
            OperationSpecies::Construction,
            Vec::new(),
            vec![ports.quantity_in],
            pending("quantity owner must license the complete dimensional population"),
        )?,
        quantity_contract: bind(
            &mut operation,
            "quantity-contract",
            OperationSpecies::Transport,
            vec![ports.quantity_in],
            vec![ports.quantity_out],
            pending("quantity owner must return a dimensionless kernel consequence"),
        )?,
    };
    let events = EventIds {
        affine_enter: occur(&mut operation, laws.affine_enter)?,
        affine_contract: occur(&mut operation, laws.affine_contract)?,
        heat_enter: occur(&mut operation, laws.heat_enter)?,
        heat_contract: occur(&mut operation, laws.heat_contract)?,
        quantity_enter: occur(&mut operation, laws.quantity_enter)?,
        quantity_contract: occur(&mut operation, laws.quantity_contract)?,
    };
    for (name, boundary, source, target) in [
        (
            "affine standing enters",
            ports.affine_in,
            events.affine_enter,
            events.affine_contract,
        ),
        (
            "heat standing enters",
            ports.heat_in,
            events.heat_enter,
            events.heat_contract,
        ),
        (
            "quantity standing enters",
            ports.quantity_in,
            events.quantity_enter,
            events.quantity_contract,
        ),
    ] {
        operation
            .carries_precedence(
                name,
                boundary,
                OccurrencePort::output(source, 0),
                OccurrencePort::input(target, 0),
            )
            .map_err(|error| error.to_string())?;
    }
    Ok(OperationTopology {
        operation,
        ports,
        laws,
        events,
    })
}

fn bind(
    operation: &mut PortedOperationComplex,
    name: &str,
    species: OperationSpecies,
    inputs: Vec<BoundaryId>,
    outputs: Vec<BoundaryId>,
    testimony: Vec<SourceTestimony>,
) -> Result<EvolutionLawId, String> {
    let carrier = (species != OperationSpecies::Construction).then(|| "Q".to_owned());
    operation
        .bind_operation(name, species, inputs, outputs, carrier, testimony)
        .map_err(|error| error.to_string())
}

fn occur(operation: &mut PortedOperationComplex, law: EvolutionLawId) -> Result<EventId, String> {
    operation.occur(law).map_err(|error| error.to_string())
}
