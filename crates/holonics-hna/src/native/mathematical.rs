//! Caller-controlled mathematical applications of the shared exact and resident owners.
//! Construction is an explicitly requested exterior exact search. Its result is immutable
//! executable material; application and retained-product receivers run on the resident surface.
//! Product names do not select an engine. Handles address objects in this session only.
use super::{NativeSessionError, RationalWire, ReceiverWire};
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    exact_linear::{
        BilinearOperator, BilinearProductCore, BilinearRealization, BilinearSupportSearch,
        ExactRatMatrix, ReceiverFactorization,
    },
    native_ecology::constitutive_fibre::{
        ConditionCoverage, ConditionImageReading, ConditionPreimageReading,
        ResidentConstitutiveCurrent,
    },
    resident_section::{
        ResidentBilinearMap, ResidentBilinearReturn, ResidentSection, ResidentSurface,
    },
};
use num_rational::BigRational;
use num_traits::One;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{collections::BTreeMap, sync::Arc, time::Instant};

mod relation;
use relation::NativeConditionRelation;

pub type RationalMatrixWire = Vec<Vec<RationalWire>>;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RelationCalibrationWire {
    /// Interleaved real/imaginary coordinates in the declared complex port.
    pub source: Vec<RationalWire>,
    pub condition: Vec<RationalWire>,
    pub observed: Vec<RationalWire>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum MathematicalInputWire {
    Values {
        values: Vec<RationalWire>,
    },
    /// Consume the original retained output directly, with its actual rectangular chart.
    ProductOutput {
        product: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BilinearTargetWire {
    pub left_extent: usize,
    pub right_extent: usize,
    /// Output rows; column i*right_extent+j is the coefficient of left[i]*right[j].
    pub coefficients: RationalMatrixWire,
}
impl BilinearTargetWire {
    fn operator(&self) -> Result<BilinearOperator, NativeSessionError> {
        if self.left_extent == 0 || self.right_extent == 0 {
            return Err(invalid("bilinear input ports must be nonempty"));
        }
        BilinearOperator::new(
            self.left_extent,
            self.right_extent,
            matrix(&self.coefficients)?,
        )
        .map_err(invalid)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum BilinearConstructionWire {
    Core {
        left_forms: RationalMatrixWire,
        right_forms: RationalMatrixWire,
    },
    Search {
        left_forms: RationalMatrixWire,
        right_forms: RationalMatrixWire,
        min_products: usize,
        max_products: usize,
        max_candidates: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "operation", rename_all = "kebab-case", deny_unknown_fields)]
pub enum MathematicalRequest {
    ConstructRelation {
        source_complex: usize,
        condition_complex: usize,
        target_complex: usize,
        calibration: Vec<RelationCalibrationWire>,
        initial_source: Vec<RationalWire>,
        initial_observed: Vec<RationalWire>,
    },
    PredictRelation {
        relation: u64,
        source: MathematicalInputWire,
        #[serde(default)]
        retain_prediction: bool,
    },
    ObserveRelation {
        relation: u64,
        prediction: u64,
        observed: Vec<RationalWire>,
    },
    InspectCondition {
        relation: u64,
    },
    ReleasePrediction {
        relation: u64,
        prediction: u64,
    },
    ReleaseRelation {
        relation: u64,
    },
    ConstructBilinear {
        target: BilinearTargetWire,
        construction: BilinearConstructionWire,
    },
    /// A linear action is lowered with a declared unit right port; rank is derived by RREF.
    ConstructLinear {
        coefficients: RationalMatrixWire,
    },
    ResumeConstruction {
        search: u64,
        max_candidates: usize,
    },
    Apply {
        operator: u64,
        left: Vec<RationalWire>,
        #[serde(default)]
        right: Option<Vec<RationalWire>>,
        /// Only explicitly retained products survive this request. They can be released below.
        #[serde(default)]
        retain_product: bool,
    },
    BindReceiver {
        operator: u64,
        coefficients: RationalMatrixWire,
    },
    ComposeReceiver {
        operator: u64,
        matrix: RationalMatrixWire,
    },
    ReadProduct {
        operator: u64,
        product: u64,
    },
    ReleaseProduct {
        product: u64,
    },
    ReleaseOperator {
        operator: u64,
    },
    ReleaseSearch {
        search: u64,
    },
}

struct Operator<'c> {
    realization: BilinearRealization,
    native: ResidentBilinearMap<'c>,
    linear: bool,
}
struct Search {
    iterator: BilinearSupportSearch,
    examined: usize,
    // A found candidate survives a device mounting refusal; resuming does not skip it.
    candidate: Option<BilinearRealization>,
}

pub struct NativeMathematicalSession<'c> {
    surface: &'c ResidentSurface<'c>,
    operators: BTreeMap<u64, Operator<'c>>,
    products: BTreeMap<u64, ResidentBilinearReturn<'c>>,
    searches: BTreeMap<u64, Search>,
    relations: BTreeMap<u64, NativeConditionRelation<'c>>,
    next_operator: u64,
    next_product: u64,
    next_search: u64,
    next_relation: u64,
}

pub fn with_mathematical_session<R>(
    operation: impl FnOnce(&mut NativeMathematicalSession<'_>) -> Result<R, NativeSessionError>,
) -> Result<R, NativeSessionError> {
    let readout = ResidentReadout::new().map_err(invalid)?;
    let surface = ResidentSurface::on(&readout).map_err(invalid)?;
    let mut session = NativeMathematicalSession::on(&surface);
    let result = operation(&mut session);
    drop(session);
    result
}

fn invalid(error: impl ToString) -> NativeSessionError {
    NativeSessionError::Application(error.to_string())
}
fn vector(row: &[RationalWire]) -> Result<Vec<BigRational>, NativeSessionError> {
    row.iter().map(RationalWire::rational).collect()
}
fn matrix(rows: &RationalMatrixWire) -> Result<ExactRatMatrix, NativeSessionError> {
    if rows.is_empty() || rows[0].is_empty() {
        return Err(invalid(
            "mathematical packet requires nonempty matrix ports",
        ));
    }
    ExactRatMatrix::new(rows.iter().map(|r| vector(r)).collect::<Result<_, _>>()?).map_err(invalid)
}
fn row_wire(row: &[BigRational]) -> Vec<RationalWire> {
    row.iter().map(RationalWire::from_rational).collect()
}
fn matrix_wire(matrix: &ExactRatMatrix) -> RationalMatrixWire {
    matrix.to_rows().iter().map(|r| row_wire(r)).collect()
}
fn condition_wire(reading: ConditionPreimageReading) -> Value {
    match reading {
        ConditionPreimageReading::Compatible {
            particular,
            directions,
        } => json!({
            "kind":"compatible", "particular":row_wire(&particular),
            "directions":directions.iter().map(|r| row_wire(r)).collect::<Vec<_>>() }),
        ConditionPreimageReading::OutsideRepresentedRelation { residual } => json!({
            "kind":"outside-represented-relation", "residual":row_wire(&residual) }),
    }
}
fn image_wire(reading: ConditionImageReading) -> Value {
    let coverage = match reading.coverage {
        ConditionCoverage::Complete => json!({"kind":"complete"}),
        ConditionCoverage::EmptyConditionFibre => json!({"kind":"empty-condition-fibre"}),
        ConditionCoverage::Partial {
            direction,
            condition,
            residual,
        } => json!({
            "kind":"partial", "direction":direction, "condition":row_wire(&condition), "residual":row_wire(&residual) }),
        ConditionCoverage::NoSupportedCondition {
            condition,
            residual,
        } => json!({
            "kind":"no-supported-condition", "condition":row_wire(&condition), "residual":row_wire(&residual) }),
    };
    json!({"condition_width":reading.condition_width, "output_width":reading.output_width,
        "coverage":coverage, "supported_conditions":ReceiverWire::from(&reading.supported_conditions),
        "supported_outputs":ReceiverWire::from(&reading.supported_outputs), "joint":ReceiverWire::from(&reading.joint)})
}
fn factor_description(realization: &BilinearRealization) -> Value {
    json!({
        "left_forms": matrix_wire(realization.core().left_forms()),
        "right_forms": matrix_wire(realization.core().right_forms()),
        "tensor_image": matrix_wire(realization.core().tensor_image()),
        "receiver_family": {
            "particular": matrix_wire(&realization.receiver().particular),
            "free_row_directions": realization.receiver().free_row_directions.iter()
                .map(|r| row_wire(r)).collect::<Vec<_>>(),
            "scope": "every free row direction annihilates the complete retained product core"
        },
        "products": realization.core().products(),
        "tensor_chart": "column i*right_extent+j",
        "left_extent": realization.core().left_forms().columns(),
        "right_extent": realization.core().right_forms().columns(),
        "output_extent": realization.receiver().particular.rows(),
    })
}
fn separator(factor: ReceiverFactorization) -> Value {
    match factor {
        ReceiverFactorization::Obstructed {
            source_null,
            returned,
        } => json!({
            "status": "obstructed", "scope": "requested receiver does not factor through this core",
            "source_null": row_wire(&source_null), "returned": row_wire(&returned),
            "separator_domain": "linear tensor-coordinate carrier; not asserted to be a rank-one input"
        }),
        ReceiverFactorization::Factored(_) => unreachable!("only a refused binding"),
    }
}

impl<'c> NativeMathematicalSession<'c> {
    pub fn on(surface: &'c ResidentSurface<'c>) -> Self {
        Self {
            surface,
            operators: BTreeMap::new(),
            products: BTreeMap::new(),
            searches: BTreeMap::new(),
            relations: BTreeMap::new(),
            next_operator: 0,
            next_product: 0,
            next_search: 0,
            next_relation: 0,
        }
    }
    pub fn inspect(&self) -> Value {
        json!({"scope": "native-mathematical-application-session", "operators": self.operators.keys().collect::<Vec<_>>(),
            "retained_products": self.products.keys().collect::<Vec<_>>(),
            "pending_constructions": self.searches.keys().collect::<Vec<_>>(),
            "relations": self.relations.iter().map(|(id, r)| json!({"relation":id,
                "calibration_rows":r.occurrences(), "pending_prediction":r.pending_id()})).collect::<Vec<_>>(),
            "census": self.surface.census()})
    }
    fn publish(
        &mut self,
        realization: BilinearRealization,
        linear: bool,
    ) -> Result<Value, NativeSessionError> {
        let next = self
            .next_operator
            .checked_add(1)
            .ok_or_else(|| invalid("operator addresses exhausted"))?;
        let native = ResidentBilinearMap::mount(self.surface, &realization).map_err(invalid)?;
        let id = self.next_operator;
        let result = json!({"status": "constructed", "operator": id, "linear_unit_right_port": linear,
            "factors": factor_description(&realization), "execution": "resident exact rational packet"});
        self.operators.insert(
            id,
            Operator {
                realization,
                native,
                linear,
            },
        );
        self.next_operator = next;
        Ok(result)
    }
    fn read(&self, section: &ResidentSection<'c>) -> Result<Vec<RationalWire>, NativeSessionError> {
        let packet = self.surface.read_out(section).map_err(invalid)?;
        if packet.len() < 2
            || packet.iter().any(|(lo, hi)| lo != hi)
            || packet.last().unwrap().0 <= 0
        {
            return Err(invalid("terminal receiver is not an exact rational packet"));
        }
        let denominator = packet.last().unwrap().0;
        Ok(packet[..packet.len() - 1]
            .iter()
            .map(|(n, _)| {
                RationalWire::from_rational(&BigRational::new((*n).into(), denominator.into()))
            })
            .collect())
    }
    /// No automatic source recording or product-name routing occurs at this exterior seam.
    pub fn request(&mut self, request: &MathematicalRequest) -> Result<Value, NativeSessionError> {
        let before = self.surface.census();
        let start = Instant::now();
        let mut value = self.execute(request)?;
        value["cost"] = json!({"elapsed_microseconds": start.elapsed().as_micros(),
            "census_before": before, "census_after": self.surface.census(),
            "scope": "application request body: construction/input mounting, resident execution and terminal decoding; excludes JSON transport and session startup"});
        Ok(value)
    }
    fn execute(&mut self, request: &MathematicalRequest) -> Result<Value, NativeSessionError> {
        match request {
            MathematicalRequest::ConstructRelation {
                source_complex,
                condition_complex,
                target_complex,
                calibration,
                initial_source,
                initial_observed,
            } => {
                let next = self
                    .next_relation
                    .checked_add(1)
                    .ok_or_else(|| invalid("relation addresses exhausted"))?;
                let mut relation = NativeConditionRelation::found(
                    self.surface,
                    *source_complex,
                    *condition_complex,
                    *target_complex,
                )?;
                for row in calibration {
                    let source = self
                        .surface
                        .mount_exact_rational_packet(&vector(&row.source)?)
                        .map_err(invalid)?;
                    let condition = self
                        .surface
                        .mount_exact_rational_packet(&vector(&row.condition)?)
                        .map_err(invalid)?;
                    let observed = self
                        .surface
                        .mount_exact_rational_packet(&vector(&row.observed)?)
                        .map_err(invalid)?;
                    relation.calibrate(
                        ResidentConstitutiveCurrent::rational(&source)?,
                        ResidentConstitutiveCurrent::rational(&condition)?,
                        Some(ResidentConstitutiveCurrent::rational(&observed)?),
                    )?;
                }
                let source = self
                    .surface
                    .mount_exact_rational_packet(&vector(initial_source)?)
                    .map_err(invalid)?;
                let observed = self
                    .surface
                    .mount_exact_rational_packet(&vector(initial_observed)?)
                    .map_err(invalid)?;
                relation.form_condition(
                    ResidentConstitutiveCurrent::rational(&source)?,
                    ResidentConstitutiveCurrent::rational(&observed)?,
                )?;
                let reading = relation.condition().expect("founded condition").inspect()?;
                let id = self.next_relation;
                self.relations.insert(id, relation);
                self.next_relation = next;
                Ok(
                    json!({"status":"relation-constructed", "relation":id, "condition_family":condition_wire(reading),
                    "source_complex":source_complex, "condition_complex":condition_complex, "target_complex":target_complex,
                    "scope":"native calibrated source/condition/mixed-product relation and compatible condition family",
                    "coordinate_chart":"interleaved real/imaginary pairs", "calibration_rows":calibration.len()}),
                )
            }
            MathematicalRequest::PredictRelation {
                relation,
                source,
                retain_prediction,
            } => {
                let mounted;
                let section = match source {
                    MathematicalInputWire::Values { values } => {
                        mounted = self
                            .surface
                            .mount_exact_rational_packet(&vector(values)?)
                            .map_err(invalid)?;
                        &mounted
                    }
                    MathematicalInputWire::ProductOutput { product } => self
                        .products
                        .get(product)
                        .ok_or_else(|| invalid("unknown or released product"))?
                        .output(),
                };
                let owner = self
                    .relations
                    .get_mut(relation)
                    .ok_or_else(|| invalid("unknown relation"))?;
                if *retain_prediction && owner.pending_id().is_some() {
                    return Err(invalid("this relation already retains an observation cut; observe or explicitly release it first (read-only predictions remain available)"));
                }
                let (prediction, reading) = owner.predict(
                    ResidentConstitutiveCurrent::rational(section)?,
                    *retain_prediction,
                )?;
                Ok(
                    json!({"status":"relation-predicted", "relation":relation, "prediction":prediction, "reading":image_wire(reading),
                    "source":source, "scope":"full joint condition/output image; no selected condition representative"}),
                )
            }
            MathematicalRequest::ObserveRelation {
                relation,
                prediction,
                observed,
            } => {
                let observed = self
                    .surface
                    .mount_exact_rational_packet(&vector(observed)?)
                    .map_err(invalid)?;
                let owner = self
                    .relations
                    .get_mut(relation)
                    .ok_or_else(|| invalid("unknown relation"))?;
                let family = owner.observe_pending(
                    *prediction,
                    ResidentConstitutiveCurrent::rational(&observed)?,
                )?;
                Ok(
                    json!({"status":"relation-refined", "relation":relation, "prediction_consumed":prediction,
                    "condition_family":condition_wire(family), "scope":"native restriction of the producing joint image"}),
                )
            }
            MathematicalRequest::InspectCondition { relation } => {
                let owner = self
                    .relations
                    .get(relation)
                    .ok_or_else(|| invalid("unknown relation"))?;
                Ok(json!({"status":"condition-family", "relation":relation,
                    "condition_family":condition_wire(owner.condition().expect("founded condition").inspect()?)}))
            }
            MathematicalRequest::ReleasePrediction {
                relation,
                prediction,
            } => {
                self.relations
                    .get_mut(relation)
                    .ok_or_else(|| invalid("unknown relation"))?
                    .release_prediction(*prediction)?;
                Ok(json!({"status":"released", "relation":relation, "prediction":prediction}))
            }
            MathematicalRequest::ReleaseRelation { relation } => {
                let owner = self
                    .relations
                    .get(relation)
                    .ok_or_else(|| invalid("unknown relation"))?;
                if owner.pending_id().is_some() {
                    return Err(invalid(
                        "observe or release the pending prediction before releasing its relation",
                    ));
                }
                self.relations.remove(relation);
                Ok(json!({"status":"released", "relation":relation}))
            }
            MathematicalRequest::ConstructBilinear {
                target,
                construction,
            } => {
                let target = target.operator()?;
                match construction {
                    BilinearConstructionWire::Core {
                        left_forms,
                        right_forms,
                    } => {
                        let core = Arc::new(
                            BilinearProductCore::new(matrix(left_forms)?, matrix(right_forms)?)
                                .map_err(invalid)?,
                        );
                        match core.bind(&target).map_err(invalid)? {
                            Ok(realization) => self.publish(realization, false),
                            Err(obstruction) => Ok(separator(obstruction)),
                        }
                    }
                    BilinearConstructionWire::Search {
                        left_forms,
                        right_forms,
                        min_products,
                        max_products,
                        max_candidates,
                    } => {
                        if *min_products == 0 || min_products > max_products || *max_candidates == 0
                        {
                            return Err(invalid("search requires a positive, ordered product range and candidate allowance"));
                        }
                        let iterator = BilinearSupportSearch::new(
                            target,
                            matrix(left_forms)?,
                            matrix(right_forms)?,
                            *min_products..=*max_products,
                        )
                        .map_err(invalid)?;
                        let id = self.next_search;
                        self.next_search = id
                            .checked_add(1)
                            .ok_or_else(|| invalid("search addresses exhausted"))?;
                        self.searches.insert(
                            id,
                            Search {
                                iterator,
                                examined: 0,
                                candidate: None,
                            },
                        );
                        self.resume(id, *max_candidates)
                    }
                }
            }
            MathematicalRequest::ConstructLinear { coefficients } => {
                let target_matrix = matrix(coefficients)?;
                let factor = target_matrix.rank_factorization().map_err(invalid)?;
                // Rank-zero maps still need a resident zero carrier in this packet primitive.
                // Report that representational lane separately from the derived mathematical rank.
                let left = if factor.derived_rank == 0 {
                    ExactRatMatrix::zero(1, target_matrix.columns()).map_err(invalid)?
                } else {
                    factor.right
                };
                let right = ExactRatMatrix::new(vec![vec![BigRational::one()]; left.rows()])
                    .map_err(invalid)?;
                let core = Arc::new(BilinearProductCore::new(left, right).map_err(invalid)?);
                let target = BilinearOperator::new(target_matrix.columns(), 1, target_matrix)
                    .map_err(invalid)?;
                let realization = core
                    .bind(&target)
                    .map_err(invalid)?
                    .map_err(|_| invalid("rank factorization failed to bind"))?;
                let mut value = self.publish(realization, true)?;
                value["derived_rank"] = json!(factor.derived_rank);
                value["construction_work"] = json!(factor.work);
                value["unit_port_lowering"] =
                    json!("right=[1]; carrier lanes are not a bilinear-rank optimality claim");
                Ok(value)
            }
            MathematicalRequest::ResumeConstruction {
                search,
                max_candidates,
            } => self.resume(*search, *max_candidates),
            MathematicalRequest::Apply {
                operator,
                left,
                right,
                retain_product,
            } => {
                let next = self
                    .next_product
                    .checked_add(1)
                    .ok_or_else(|| invalid("product addresses exhausted"))?;
                let op = self
                    .operators
                    .get(operator)
                    .ok_or_else(|| invalid("unknown operator"))?;
                let x = self
                    .surface
                    .mount_exact_rational_packet(&vector(left)?)
                    .map_err(invalid)?;
                let y = if op.linear {
                    if right.is_some() {
                        return Err(invalid("linear application supplies only left; right is the declared unit port"));
                    }
                    vec![BigRational::one()]
                } else {
                    vector(
                        right
                            .as_ref()
                            .ok_or_else(|| invalid("bilinear application requires right input"))?,
                    )?
                };
                let y = self
                    .surface
                    .mount_exact_rational_packet(&y)
                    .map_err(invalid)?;
                let reads = self.surface.census().section_read_outs;
                let result = op.native.apply(&x, &y).map_err(invalid)?;
                let intermediate_reads = self.surface.census().section_read_outs - reads;
                let output = self.read(result.output())?;
                let product = if *retain_product {
                    let id = self.next_product;
                    self.products.insert(id, result);
                    self.next_product = next;
                    Some(id)
                } else {
                    None
                };
                Ok(
                    json!({"status":"applied", "operator":operator, "output":output, "product":product,
                    "intermediate_section_readouts":intermediate_reads, "source_products_recomputed":true}),
                )
            }
            MathematicalRequest::BindReceiver {
                operator,
                coefficients,
            } => {
                let op = self
                    .operators
                    .get(operator)
                    .ok_or_else(|| invalid("unknown operator"))?;
                let target = BilinearOperator::new(
                    op.realization.core().left_forms().columns(),
                    op.realization.core().right_forms().columns(),
                    matrix(coefficients)?,
                )
                .map_err(invalid)?;
                match op.realization.core().bind(&target).map_err(invalid)? {
                    Ok(realization) => self.publish(realization, op.linear),
                    Err(obstruction) => Ok(separator(obstruction)),
                }
            }
            MathematicalRequest::ComposeReceiver {
                operator,
                matrix: next,
            } => {
                let op = self
                    .operators
                    .get(operator)
                    .ok_or_else(|| invalid("unknown operator"))?;
                let realization = op
                    .realization
                    .then_receiver(&matrix(next)?)
                    .map_err(invalid)?;
                self.publish(realization, op.linear)
            }
            MathematicalRequest::ReadProduct { operator, product } => {
                let op = self
                    .operators
                    .get(operator)
                    .ok_or_else(|| invalid("unknown operator"))?;
                let source = self
                    .products
                    .get(product)
                    .ok_or_else(|| invalid("unknown or released product"))?;
                let reads = self.surface.census().section_read_outs;
                let returned = op.native.read_product(source).map_err(invalid)?;
                let intermediate_reads = self.surface.census().section_read_outs - reads;
                Ok(
                    json!({"status":"read", "operator":operator, "product":product, "output":self.read(&returned)?,
                    "source_products_recomputed":false, "intermediate_section_readouts":intermediate_reads}),
                )
            }
            MathematicalRequest::ReleaseProduct { product } => {
                self.products
                    .remove(product)
                    .ok_or_else(|| invalid("unknown or released product"))?;
                Ok(json!({"status":"released", "product":product}))
            }
            MathematicalRequest::ReleaseOperator { operator } => {
                self.operators
                    .remove(operator)
                    .ok_or_else(|| invalid("unknown or released operator"))?;
                Ok(json!({"status":"released", "operator":operator}))
            }
            MathematicalRequest::ReleaseSearch { search } => {
                self.searches
                    .remove(search)
                    .ok_or_else(|| invalid("unknown or released search"))?;
                Ok(json!({"status":"released", "search":search}))
            }
        }
    }
    fn resume(&mut self, id: u64, max_candidates: usize) -> Result<Value, NativeSessionError> {
        if max_candidates == 0 {
            return Err(invalid("candidate allowance must be positive"));
        }
        let search = self
            .searches
            .get_mut(&id)
            .ok_or_else(|| invalid("unknown or released search"))?;
        if search.candidate.is_none() {
            for _ in 0..max_candidates {
                let Some(candidate) = search.iterator.next() else {
                    break;
                };
                search.examined += 1;
                if let Ok(realization) = candidate.map_err(invalid)?.into_realization() {
                    search.candidate = Some(realization);
                    break;
                }
            }
        }
        let examined = search.examined;
        if let Some(candidate) = &search.candidate {
            // Only immutable construction material is shared; no continuing ecology is cloned.
            let candidate = candidate.clone();
            let mut value = self.publish(candidate, false)?;
            self.searches.remove(&id);
            value["examined_supports"] = json!(examined);
            value["search_scope"] = json!("first found in caller-declared forms and ascending product range; no global optimality claim");
            Ok(value)
        } else if search.iterator.remaining_support().is_none() {
            self.searches.remove(&id);
            Ok(json!({"status":"exhausted", "examined_supports":examined,
                "scope":"no factorization in the supplied finite grammar and product range"}))
        } else {
            Ok(
                json!({"status":"search-pending", "search":id, "examined_supports":examined,
                "next_support":search.iterator.remaining_support()}),
            )
        }
    }
}

#[cfg(test)]
mod tests;
