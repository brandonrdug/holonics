//! A resident rank-one cultivation overlay for the lifted Phoenix body.
//!
//! This is a small site owner, not a trainer or scheduler.  The W2 predecessor potential remains
//! an immutable carried standing in [`ResidentMaterial`].  New morphology crosses the same resident
//! chart as two factor populations, `u` and `v`, and the passage enacts
//!
//! ```text
//!   h  ── FactorizedContract(u,v) ────────┐
//!   y₀ ───────────────────────────────────┴─ ReEntry
//! ```
//!
//! Thus the output is exactly `y₀ + u(vᵀh)` in the resident integer interval carrier.  The CPU
//! only validates extents and retains lineage labels.  Exact work is returned by the compiled
//! passage.  It never evaluates a
//! factor or replays the deed.  A caller supplies the authenticated W3 witness and the
//! predecessor sections as read-only standings; source-detached validation therefore remains at
//! the existing occurrence boundary.

use std::rc::Rc;

use crate::causal::EventId;
use crate::embedding_fiber::{AlignedMaterial, ResidentReadout};
use crate::exact_linear::{ExactRankFactorization, ExactRatMatrix};
use crate::front_passage::{
    AlignedMaterialPlan, CompiledPassage, DeedReceiver, FactorizedContract, FrontPassage,
    FrontPassageObstruction, MaterialAdmission, ReEntry, ResidentMaterial, ResidentRealization,
    Standing, WithdrawRows,
};
use crate::interaction::OccurrencePort;
use crate::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};
use crate::resident_law::MountedPopulation;
use crate::resident_section::{ResidentGrain, ResidentSection, ResidentSurface};
use crate::source_occurrence::OccurrenceWitness;
use num_traits::Zero;
use relational_geometry::Rat;
use serde::Serialize;
use sha2::{Digest, Sha256};

const FACTORIZED_LAW: &str = "phoenix.overlay.factorized-contract";
const RE_ENTRY_LAW: &str = "phoenix.overlay.re-entry";
const STANDING_LAW: &str = "phoenix.overlay.standing";

/// Nominal ports carried by the overlay word. Equal extents do not collapse these identities.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OverlayPorts {
    pub input: String,
    pub predecessor: String,
    pub predecessor_output: String,
    pub delta_output: String,
    pub output: String,
}

/// Shapes used to authenticate the two resident factor maps before the passage is compiled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OverlayShape {
    pub rows: usize,
    pub input_width: usize,
}

impl OverlayShape {
    pub fn factor_shapes(self, rank: usize) -> ([usize; 2], [usize; 2]) {
        ([self.rows, rank], [rank, self.input_width])
    }
}

/// Authenticated source/native testimony for one candidate passage.  This is supplied by the W3
/// rest owner; the overlay never invents a locator, symbol, or topology binding.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct OverlayTestimony {
    pub input: Vec<SourceTestimony>,
    pub predecessor: Vec<SourceTestimony>,
    pub terminal_withdraw: Vec<SourceTestimony>,
    pub v: Vec<SourceTestimony>,
    pub u: Vec<SourceTestimony>,
    pub re_entry: Vec<SourceTestimony>,
}

impl OverlayTestimony {
    fn missing_operation(&self) -> Option<&'static str> {
        [
            (&self.input, STANDING_LAW),
            (&self.predecessor, STANDING_LAW),
            (&self.terminal_withdraw, "phoenix.overlay.withdraw-terminal"),
            (&self.v, FACTORIZED_LAW),
            (&self.u, FACTORIZED_LAW),
            (&self.re_entry, RE_ENTRY_LAW),
        ]
        .into_iter()
        .find_map(|(testimony, operation)| testimony.is_empty().then_some(operation))
    }
}

/// A sparse exact factor. Entries outside `support` do not exist and are therefore exact zero.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SupportedFactor {
    pub ambient: usize,
    pub support: Vec<usize>,
    pub values: Vec<Rat>,
}

/// A sparse exact defect chart. Only the supported row/column rectangle is materialized.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SparseDefect {
    pub ambient_rows: usize,
    pub ambient_columns: usize,
    pub support_rows: Vec<usize>,
    pub support_columns: Vec<usize>,
    pub supported: ExactRatMatrix,
}

/// The structured receiver which separates the lower-rank foil from the candidate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SeparatingReceiver {
    pub target: (usize, usize),
    pub predecessor: Rat,
    pub candidate: Rat,
}

/// The exact rank-one defect return. `rank` is never caller-selected: validation computes it from
/// the supported chart. The zero matrix is the explicit lower-rank foil and `separator` carries
/// an exact coordinate/value distinction rather than an arbitrary label.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RankDerivationReceipt {
    pub defect: SparseDefect,
    pub left: SupportedFactor,
    pub right: SupportedFactor,
    pub zero_rank_foil: SparseDefect,
    pub separator: SeparatingReceiver,
}

/// A higher-rank exact factorization returned by the defect itself.  The image cardinality in
/// `factorization` is the only admitted junction extent; no caller rank is stored beside it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivedRankDerivationReceipt {
    pub defect: SparseDefect,
    pub factorization: ExactRankFactorization,
    pub zero_rank_foil: SparseDefect,
    pub separator: SeparatingReceiver,
}

/// One derivation face for the same factorized law.  The rank-one arm preserves the authenticated
/// W3 product receipt byte-for-byte; the derived arm carries the complete exact image basis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FactorDerivationReceipt {
    RankOne(RankDerivationReceipt),
    Derived(DerivedRankDerivationReceipt),
}

/// Canonical bytes for the complete sparse rank return. This is the one representation shared by
/// admission and the W3 product seal; it never hashes a debug rendering.
pub fn canonical_rank_derivation_bytes(receipt: &RankDerivationReceipt) -> Vec<u8> {
    fn frame(bytes: &mut Vec<u8>, value: &[u8]) {
        bytes.extend_from_slice(&(value.len() as u64).to_le_bytes());
        bytes.extend_from_slice(value);
    }
    fn text(bytes: &mut Vec<u8>, value: &str) {
        frame(bytes, value.as_bytes());
    }
    fn sparse(bytes: &mut Vec<u8>, value: &SparseDefect) {
        bytes.extend_from_slice(&(value.ambient_rows as u64).to_le_bytes());
        bytes.extend_from_slice(&(value.ambient_columns as u64).to_le_bytes());
        bytes.extend_from_slice(&(value.support_rows.len() as u64).to_le_bytes());
        for index in &value.support_rows {
            bytes.extend_from_slice(&(*index as u64).to_le_bytes());
        }
        bytes.extend_from_slice(&(value.support_columns.len() as u64).to_le_bytes());
        for index in &value.support_columns {
            bytes.extend_from_slice(&(*index as u64).to_le_bytes());
        }
        bytes.extend_from_slice(&(value.supported.rows() as u64).to_le_bytes());
        bytes.extend_from_slice(&(value.supported.columns() as u64).to_le_bytes());
        for entry in value.supported.entries() {
            text(bytes, &entry.to_string());
        }
    }
    fn factor(bytes: &mut Vec<u8>, value: &SupportedFactor) {
        bytes.extend_from_slice(&(value.ambient as u64).to_le_bytes());
        bytes.extend_from_slice(&(value.support.len() as u64).to_le_bytes());
        for index in &value.support {
            bytes.extend_from_slice(&(*index as u64).to_le_bytes());
        }
        for entry in &value.values {
            text(bytes, &entry.to_string());
        }
    }
    let mut bytes = Vec::new();
    frame(&mut bytes, b"holonic-engine.phoenix.w3-rank-derivation.v1");
    sparse(&mut bytes, &receipt.defect);
    factor(&mut bytes, &receipt.left);
    factor(&mut bytes, &receipt.right);
    sparse(&mut bytes, &receipt.zero_rank_foil);
    bytes.extend_from_slice(&(receipt.separator.target.0 as u64).to_le_bytes());
    bytes.extend_from_slice(&(receipt.separator.target.1 as u64).to_le_bytes());
    text(&mut bytes, &receipt.separator.predecessor.to_string());
    text(&mut bytes, &receipt.separator.candidate.to_string());
    bytes
}

/// Content identity for [`canonical_rank_derivation_bytes`].
pub fn canonical_rank_derivation_digest(receipt: &RankDerivationReceipt) -> String {
    format!(
        "{:x}",
        Sha256::digest(canonical_rank_derivation_bytes(receipt))
    )
}

pub fn canonical_factor_derivation_digest(receipt: &FactorDerivationReceipt) -> String {
    match receipt {
        FactorDerivationReceipt::RankOne(receipt) => canonical_rank_derivation_digest(receipt),
        FactorDerivationReceipt::Derived(receipt) => {
            let bytes = serde_json::to_vec(&(
                "holonic-engine.phoenix.derived-rank-derivation.v1",
                &receipt.defect,
                &receipt.factorization,
                &receipt.zero_rank_foil,
                &receipt.separator.target,
                receipt.separator.predecessor.to_string(),
                receipt.separator.candidate.to_string(),
            ))
            .expect("exact derived-rank receipt is serializable");
            format!("{:x}", Sha256::digest(bytes))
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CandidateRefusal {
    MissingRankReceipt,
    MissingTestimony { operation: &'static str },
    DefectShape,
    FactorShape,
    DefectRank { rank: usize },
    ZeroRankFoilNotZero,
    ZeroRankFoilNotSeparated,
    FactorSupportMismatch,
    SupportInvalid,
    ReconstructionMismatch,
    ExactLinear(String),
    Diagram(String),
}

impl std::fmt::Display for CandidateRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl RankDerivationReceipt {
    fn validate(&self, shape: OverlayShape) -> Result<(), CandidateRefusal> {
        if self.defect.ambient_rows != shape.rows
            || self.defect.ambient_columns != shape.input_width
        {
            return Err(CandidateRefusal::DefectShape);
        }
        if !valid_support(self.defect.ambient_rows, &self.defect.support_rows)
            || !valid_support(self.defect.ambient_columns, &self.defect.support_columns)
            || self.defect.supported.rows() != self.defect.support_rows.len()
            || self.defect.supported.columns() != self.defect.support_columns.len()
        {
            return Err(CandidateRefusal::SupportInvalid);
        }
        if !self.left.valid(self.defect.ambient_rows)
            || !self.right.valid(self.defect.ambient_columns)
        {
            return Err(CandidateRefusal::SupportInvalid);
        }
        if self.left.support != self.defect.support_rows
            || self.right.support != self.defect.support_columns
        {
            return Err(CandidateRefusal::FactorSupportMismatch);
        }
        let rank = self
            .defect
            .supported
            .rank()
            .map_err(|error| CandidateRefusal::ExactLinear(error.to_string()))?;
        if rank != 1 {
            return Err(CandidateRefusal::DefectRank { rank });
        }
        if self.zero_rank_foil.ambient_rows != self.defect.ambient_rows
            || self.zero_rank_foil.ambient_columns != self.defect.ambient_columns
            || self.zero_rank_foil.support_rows != self.defect.support_rows
            || self.zero_rank_foil.support_columns != self.defect.support_columns
            || self.zero_rank_foil.supported.rows() != self.defect.support_rows.len()
            || self.zero_rank_foil.supported.columns() != self.defect.support_columns.len()
        {
            return Err(CandidateRefusal::ZeroRankFoilNotZero);
        }
        if self
            .zero_rank_foil
            .supported
            .entries()
            .iter()
            .any(|entry| !entry.is_zero())
        {
            return Err(CandidateRefusal::ZeroRankFoilNotZero);
        }
        if self.zero_rank_foil == self.defect {
            return Err(CandidateRefusal::ZeroRankFoilNotSeparated);
        }
        let reconstructed = ExactRatMatrix::new(
            self.left
                .values
                .iter()
                .map(|left| self.right.values.iter().map(|right| left * right).collect())
                .collect(),
        )
        .map_err(|error| CandidateRefusal::ExactLinear(error.to_string()))?;
        if reconstructed != self.defect.supported {
            return Err(CandidateRefusal::ReconstructionMismatch);
        }
        let (target_row, target_column) = self.separator.target;
        let row = self
            .defect
            .support_rows
            .iter()
            .position(|row| *row == target_row);
        let column = self
            .defect
            .support_columns
            .iter()
            .position(|column| *column == target_column);
        let (Some(row), Some(column)) = (row, column) else {
            return Err(CandidateRefusal::ZeroRankFoilNotSeparated);
        };
        let candidate = self
            .defect
            .supported
            .get(row, column)
            .map_err(|error| CandidateRefusal::ExactLinear(error.to_string()))?;
        if !self.separator.predecessor.is_zero()
            || self.separator.candidate != *candidate
            || self.separator.predecessor == self.separator.candidate
        {
            return Err(CandidateRefusal::ZeroRankFoilNotSeparated);
        }
        Ok(())
    }
}

impl DerivedRankDerivationReceipt {
    fn validate(&self, shape: OverlayShape, rank: usize) -> Result<(), CandidateRefusal> {
        if rank == 0
            || self.defect.ambient_rows != shape.rows
            || self.defect.ambient_columns != shape.input_width
            || !valid_support(self.defect.ambient_rows, &self.defect.support_rows)
            || !valid_support(self.defect.ambient_columns, &self.defect.support_columns)
            || self.defect.supported.rows() != self.defect.support_rows.len()
            || self.defect.supported.columns() != self.defect.support_columns.len()
        {
            return Err(CandidateRefusal::DefectShape);
        }
        if self.factorization.rows != self.defect.supported.rows()
            || self.factorization.columns != self.defect.supported.columns()
            || self.factorization.derived_rank != rank
            || self.factorization.reconstruction != self.defect.supported
            || self
                .factorization
                .left
                .multiply(&self.factorization.right)
                .map_err(|error| CandidateRefusal::ExactLinear(error.to_string()))?
                != self.defect.supported
        {
            return Err(CandidateRefusal::ReconstructionMismatch);
        }
        if self.zero_rank_foil.ambient_rows != self.defect.ambient_rows
            || self.zero_rank_foil.ambient_columns != self.defect.ambient_columns
            || self.zero_rank_foil.support_rows != self.defect.support_rows
            || self.zero_rank_foil.support_columns != self.defect.support_columns
            || self
                .zero_rank_foil
                .supported
                .entries()
                .iter()
                .any(|entry| !entry.is_zero())
        {
            return Err(CandidateRefusal::ZeroRankFoilNotZero);
        }
        let (target_row, target_column) = self.separator.target;
        let row = self
            .defect
            .support_rows
            .iter()
            .position(|row| *row == target_row)
            .ok_or(CandidateRefusal::ZeroRankFoilNotSeparated)?;
        let column = self
            .defect
            .support_columns
            .iter()
            .position(|column| *column == target_column)
            .ok_or(CandidateRefusal::ZeroRankFoilNotSeparated)?;
        let candidate = self
            .defect
            .supported
            .get(row, column)
            .map_err(|error| CandidateRefusal::ExactLinear(error.to_string()))?;
        if !self.separator.predecessor.is_zero()
            || self.separator.candidate != *candidate
            || candidate.is_zero()
        {
            return Err(CandidateRefusal::ZeroRankFoilNotSeparated);
        }
        Ok(())
    }
}

impl FactorDerivationReceipt {
    fn validate(&self, shape: OverlayShape, rank: usize) -> Result<(), CandidateRefusal> {
        match self {
            Self::RankOne(receipt) if rank == 1 => receipt.validate(shape),
            Self::RankOne(_) => Err(CandidateRefusal::DefectRank { rank: 1 }),
            Self::Derived(receipt) => receipt.validate(shape, rank),
        }
    }
}

fn valid_support(ambient: usize, support: &[usize]) -> bool {
    support.iter().all(|index| *index < ambient) && support.windows(2).all(|pair| pair[0] < pair[1])
}

impl SupportedFactor {
    fn valid(&self, ambient: usize) -> bool {
        self.ambient == ambient
            && valid_support(ambient, &self.support)
            && self.support.len() == self.values.len()
            && self.values.iter().all(|value| !value.is_zero())
    }
}

/// A factorized candidate morphology. It is not cultivation until a valid derivation receipt,
/// authenticated witness, detached remount, changed successor conduct, and ablation return exist.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactorizedCandidate {
    pub u_population: String,
    pub v_population: String,
    pub shape: OverlayShape,
    pub rank: usize,
    pub terminal_rows: usize,
    pub ports: OverlayPorts,
    pub testimony: OverlayTestimony,
}

impl FactorizedCandidate {
    pub fn new(
        u_population: impl Into<String>,
        v_population: impl Into<String>,
        shape: OverlayShape,
        rank: usize,
        terminal_rows: usize,
        testimony: OverlayTestimony,
    ) -> Self {
        Self {
            u_population: u_population.into(),
            v_population: v_population.into(),
            shape,
            rank,
            terminal_rows,
            testimony,
            ports: OverlayPorts {
                input: "phoenix.overlay/input".to_owned(),
                predecessor: "phoenix.overlay/w2-predecessor".to_owned(),
                predecessor_output: "phoenix.overlay/w2-predecessor-output".to_owned(),
                delta_output: "phoenix.overlay/delta-output".to_owned(),
                output: "phoenix.overlay/output".to_owned(),
            },
        }
    }

    /// The exact aligned ingress plan for the two factor maps. The W3 caller must admit this plan
    /// before either `ResidentReadout::mount` call.
    pub fn aligned_material_plan(&self) -> AlignedMaterialPlan {
        AlignedMaterialPlan::maps(vec![
            (self.u_population.clone(), self.shape.rows, self.rank),
            (self.v_population.clone(), self.rank, self.shape.input_width),
        ])
    }

    pub fn admit_aligned_factors<'chart>(
        &self,
        surface: &'chart ResidentSurface<'chart>,
        grain: ResidentGrain,
    ) -> Result<MaterialAdmission, FrontPassageObstruction> {
        let passage = FrontPassage::new(surface, grain);
        let prediction = passage.predict_aligned_material(&self.aligned_material_plan());
        passage.admit_material(&prediction)
    }

    /// Build the typed operation complex. No realization or launch is performed here.
    pub fn complex(
        &self,
        receipt: Option<&FactorDerivationReceipt>,
    ) -> Result<(PortedOperationComplex, OverlayEvents), CandidateRefusal> {
        let Some(receipt) = receipt else {
            return Err(CandidateRefusal::MissingRankReceipt);
        };
        receipt.validate(self.shape, self.rank)?;
        if let Some(operation) = self.testimony.missing_operation() {
            return Err(CandidateRefusal::MissingTestimony { operation });
        }
        if self.shape.rows == 0
            || self.shape.input_width == 0
            || self.rank == 0
            || self.terminal_rows == 0
        {
            return Err(CandidateRefusal::FactorShape);
        }
        let mut complex = PortedOperationComplex::new("phoenix.factorized-cultivation-overlay");
        let input = complex.port(self.ports.input.clone());
        let predecessor_output = complex.port(self.ports.predecessor_output.clone());
        let terminal_input = complex.port("phoenix.overlay/terminal-input");
        let delta_output = complex.port(self.ports.delta_output.clone());
        let output = complex.port(self.ports.output.clone());
        let input_standing = complex
            .bind_operation(
                "phoenix.overlay.standing.input",
                OperationSpecies::Construction,
                vec![],
                vec![input],
                None,
                self.testimony.input.clone(),
            )
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        let predecessor_standing = complex
            .bind_operation(
                "phoenix.overlay.standing.predecessor",
                OperationSpecies::Construction,
                vec![],
                vec![predecessor_output],
                None,
                self.testimony.predecessor.clone(),
            )
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        let terminal_withdraw = complex
            .bind_operation(
                "phoenix.overlay.withdraw-terminal",
                OperationSpecies::Quotient,
                vec![input],
                vec![terminal_input],
                None,
                self.testimony.terminal_withdraw.clone(),
            )
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        let factorized = complex
            .bind_operation(
                FACTORIZED_LAW,
                OperationSpecies::Transport,
                vec![terminal_input],
                vec![delta_output],
                Some(self.u_population.clone()),
                self.testimony
                    .v
                    .iter()
                    .chain(self.testimony.u.iter())
                    .cloned()
                    .collect(),
            )
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        let re_entry = complex
            .bind_operation(
                RE_ENTRY_LAW,
                OperationSpecies::Construction,
                vec![predecessor_output, delta_output],
                vec![output],
                None,
                self.testimony.re_entry.clone(),
            )
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        let input_event = complex
            .occur(input_standing)
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        let predecessor_event = complex
            .occur(predecessor_standing)
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        let terminal_event = complex
            .occur(terminal_withdraw)
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        let factorized_event = complex
            .occur(factorized)
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        let re_entry_event = complex
            .occur(re_entry)
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        complex
            .carries_precedence(
                "overlay input to terminal quotient",
                input,
                OccurrencePort::output(input_event, 0),
                OccurrencePort::input(terminal_event, 0),
            )
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        complex
            .carries_precedence(
                "terminal quotient to v factor",
                terminal_input,
                OccurrencePort::output(terminal_event, 0),
                OccurrencePort::input(factorized_event, 0),
            )
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        complex
            .carries_precedence(
                "predecessor to re-entry",
                predecessor_output,
                OccurrencePort::output(predecessor_event, 0),
                OccurrencePort::input(re_entry_event, 0),
            )
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        complex
            .carries_precedence(
                "delta to re-entry",
                delta_output,
                OccurrencePort::output(factorized_event, 0),
                OccurrencePort::input(re_entry_event, 1),
            )
            .map_err(|error| CandidateRefusal::Diagram(error.to_string()))?;
        Ok((
            complex,
            OverlayEvents {
                input: input_event,
                predecessor: predecessor_event,
                terminal: terminal_event,
                factorized: factorized_event,
                re_entry: re_entry_event,
            },
        ))
    }

    /// Bind the diagram to the resident card. The supplied `source` is the W1/W3 authenticated
    /// witness; this owner does not invent a source or run an alternate CPU realization.
    pub fn bind<'chart>(
        &self,
        surface: &'chart ResidentSurface<'chart>,
        material: &ResidentMaterial<'chart>,
        source: &dyn OccurrenceWitness,
        receiver: &DeedReceiver,
        material_admission: Option<&MaterialAdmission>,
        input_name: &str,
        predecessor_name: &str,
        input_bound: u32,
        grain: ResidentGrain,
        receipt: Option<&FactorDerivationReceipt>,
    ) -> Result<OverlayPassage<'chart>, FrontPassageObstruction> {
        let (complex, events) = self.complex(receipt).map_err(|reason| {
            FrontPassageObstruction::Compile(crate::front_passage::CompileRefusal::Shape(
                reason.to_string(),
            ))
        })?;
        let mut realization = ResidentRealization::default();
        realization.bind(
            events.input,
            Standing {
                name: input_name.to_owned(),
            },
        );
        realization.bind(
            events.predecessor,
            Standing {
                name: predecessor_name.to_owned(),
            },
        );
        realization.bind(
            events.terminal,
            WithdrawRows {
                from: 0,
                span: self.terminal_rows.saturating_sub(1),
            },
        );
        realization.bind(
            events.factorized,
            FactorizedContract {
                u_population: self.u_population.clone(),
                v_population: self.v_population.clone(),
                rank: self.rank,
            },
        );
        realization.bind(events.re_entry, ReEntry);
        let passage = FrontPassage::new(surface, grain).bind(
            &complex,
            &realization,
            material,
            source,
            receiver,
            material_admission,
            events.re_entry,
        )?;
        Ok(OverlayPassage {
            passage,
            events,
            input_bound,
        })
    }
}

/// The event lineage of one overlay passage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OverlayEvents {
    pub input: EventId,
    pub predecessor: EventId,
    pub terminal: EventId,
    pub factorized: EventId,
    pub re_entry: EventId,
}

/// A bound overlay, retaining the typed input bound beside the compiled GPU deed.
pub struct OverlayPassage<'chart> {
    pub passage: CompiledPassage<'chart>,
    pub events: OverlayEvents,
    pub input_bound: u32,
}

/// Mount one aligned factor into resident material. This is the only mutation this owner makes:
/// it inserts a new named population; existing resident populations are never replaced.
pub fn mount_factor<'chart>(
    readout: &'chart ResidentReadout,
    material: &mut ResidentMaterial<'chart>,
    population: impl Into<String>,
    aligned: &AlignedMaterial,
    rows: usize,
    width: usize,
) -> Result<(), String> {
    let population = population.into();
    if rows == 0 || width == 0 || aligned.entries.len() != rows.saturating_mul(width) {
        return Err(format!(
            "factor {population} has shape [{rows}, {width}] but {} aligned entries",
            aligned.entries.len()
        ));
    }
    if material.populations.contains_key(&population) {
        return Err(format!(
            "factor population {population} is already resident"
        ));
    }
    let mounted = readout
        .mount(aligned, width)
        .map_err(|error| format!("mount {population}: {error:?}"))?;
    let masses = mounted
        .absolute_row_mass()
        .map_err(|error| format!("mass {population}: {error:?}"))?;
    let widest = masses
        .iter()
        .map(|mass| mass.unsigned_abs())
        .max()
        .unwrap_or(0);
    let mass_octaves = i64::from(128 - widest.leading_zeros()) + i64::from(mounted.exponent());
    material.populations.insert(
        population,
        MountedPopulation {
            readout: mounted,
            mass_value_octaves: u32::try_from(mass_octaves.max(0)).unwrap_or(0),
        },
    );
    Ok(())
}

/// Declare one read-only standing consumed by the overlay. Callers use this for both `h` and the
/// W2 predecessor potential `y0`; ownership remains with the standing map, not the overlay.
pub fn carry_standing<'chart>(
    material: &mut ResidentMaterial<'chart>,
    name: impl Into<String>,
    section: ResidentSection<'chart>,
    bound_octaves: u32,
) {
    material
        .standings
        .insert(name.into(), (Rc::new(section), bound_octaves));
}

/// Extent receipt used before binding: it proves the factors match the declared defect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OverlayExtentReceipt {
    pub u_rows: usize,
    pub u_width: usize,
    pub v_rows: usize,
    pub v_width: usize,
    pub predecessor_is_read_only: bool,
    /// The fused resident front's complete output extent; no scalar section is exposed.
    pub delta_rows: usize,
    pub delta_width: usize,
    pub rank: usize,
}

pub fn inspect_extents(
    factors: &FactorizedCandidate,
    material: &ResidentMaterial<'_>,
) -> Result<OverlayExtentReceipt, String> {
    let u = material
        .populations
        .get(&factors.u_population)
        .ok_or_else(|| {
            format!(
                "u factor population {} is not resident",
                factors.u_population
            )
        })?;
    let v = material
        .populations
        .get(&factors.v_population)
        .ok_or_else(|| {
            format!(
                "v factor population {} is not resident",
                factors.v_population
            )
        })?;
    if (u.readout.rows(), u.readout.width()) != (factors.shape.rows, factors.rank)
        || (v.readout.rows(), v.readout.width()) != (factors.rank, factors.shape.input_width)
    {
        return Err("derived-rank factors have incompatible extents".to_owned());
    }
    Ok(OverlayExtentReceipt {
        u_rows: u.readout.rows(),
        u_width: u.readout.width(),
        v_rows: v.readout.rows(),
        v_width: v.readout.width(),
        predecessor_is_read_only: true,
        delta_rows: factors.terminal_rows,
        delta_width: factors.shape.rows,
        rank: factors.rank,
    })
}

#[cfg(test)]
mod cultivation_overlay_tests;
