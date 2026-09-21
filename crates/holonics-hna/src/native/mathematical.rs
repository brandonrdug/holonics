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
        ResidentConstitutiveCurrent, ResidentConstitutiveFibre, ResidentConstitutiveSection,
        ResidentNormalMaterial,
    },
    resident_section::{
        ResidentBilinearMap, ResidentBilinearReturn, ResidentGrain, ResidentSection, ResidentSurface,
    },
};
use num_rational::BigRational;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{collections::BTreeMap, sync::Arc, time::Instant};

mod relation;
mod code;
use relation::{NativeConditionRelation, NativeConditionalPredictor};

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
    /// Read an admitted receiver from the retained interior, then consume it on device.
    ProductReceiver {
        product: u64,
        operator: u64,
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
    /// Release an executable exact-rational function from a retained factor graph.
    EmitRust { operator: u64 },
    /// Both resident restrictions read the same preparation BEFORE its target is observed.
    ConstructPredictor {
        source_operator: u64,
        condition_operator: u64,
        target_complex: usize,
        fractional_bits: u32,
    },
    PredictSection {
        predictor: u64,
        preparation: MathematicalInputWire,
        #[serde(default)]
        retain_prediction: bool,
    },
    ObserveSection {
        predictor: u64,
        prediction: u64,
        observed: Vec<RationalWire>,
    },
    ReleaseSectionPrediction { predictor: u64, prediction: u64 },
    ReleasePredictor { predictor: u64 },
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
    /// Apply a retained linear action to the whole current condition/source family.
    PredictCondition {
        relation: u64,
        operator: u64,
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
    /// Construct a reduced exact power of a retained square linear action.
    Power {
        operator: u64,
        exponent: u64,
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
    ApplyInputs {
        operator: u64,
        left: MathematicalInputWire,
        #[serde(default)]
        right: Option<MathematicalInputWire>,
        #[serde(default)]
        retain_product: bool,
        /// A retained intermediate need not cross the host boundary before further use.
        #[serde(default = "emit_by_default")]
        emit_output: bool,
    },
    BindReceiver {
        operator: u64,
        coefficients: RationalMatrixWire,
    },
    ComposeReceiver {
        operator: u64,
        matrix: RationalMatrixWire,
    },
    /// Compile a following retained operator with its right port fixed for this construction.
    Compose {
        operator: u64,
        following: u64,
        #[serde(default)]
        right: Option<Vec<RationalWire>>,
    },
    /// Ordered output blocks sharing one retained core, without recomputing each branch.
    JoinReceivers {
        operators: Vec<u64>,
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
    // A lazily compiled graph chart of the same supplied action, for full-family images.
    // Failure to compile this receiver does not revoke the existing point-packet operator.
    family: Option<ResidentConstitutiveFibre<'c>>,
}

impl<'c> Operator<'c> {
    fn family(
        &mut self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<&ResidentConstitutiveFibre<'c>, NativeSessionError> {
        if !self.linear {
            return Err(invalid("a family action requires the declared unit-right linear chart; fix the other bilinear port before this use"));
        }
        if self.family.is_none() {
            // Exterior compilation of the already supplied immutable action, not a host
            // prediction or a learner. Existing native row calculus builds its graph from
            // the declared columns; every later family image/refinement remains resident.
            let matrix = self
                .realization
                .receiver()
                .particular
                .multiply(self.realization.core().tensor_image())
                .map_err(invalid)?;
            let mut graph =
                ResidentConstitutiveFibre::found(surface, matrix.columns(), matrix.rows())?;
            for column in 0..matrix.columns() {
                let mut unit = vec![BigRational::zero(); matrix.columns()];
                unit[column] = BigRational::one();
                let source = surface
                    .mount_exact_rational_packet(&unit)
                    .map_err(invalid)?;
                let values = (0..matrix.rows())
                    .map(|row| matrix.get(row, column).cloned())
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(invalid)?;
                let target = surface
                    .mount_exact_rational_packet(&values)
                    .map_err(invalid)?;
                graph.advance_resident(
                    ResidentConstitutiveCurrent::rational(&source)?,
                    Some(ResidentConstitutiveCurrent::rational(&target)?),
                )?;
            }
            self.family = Some(graph);
        }
        Ok(self.family.as_ref().expect("completed graph compilation"))
    }
}

fn emit_by_default() -> bool {
    true
}

impl MathematicalInputWire {
    /// One codec/borrowing path shared by operator application and conditional prediction.
    /// The callback cannot retain a borrow of a transient mount or introduce a host readout.
    fn with_section<'c, R>(
        &self,
        surface: &'c ResidentSurface<'c>,
        operators: &BTreeMap<u64, Operator<'c>>,
        products: &BTreeMap<u64, ResidentBilinearReturn<'c>>,
        consume: impl FnOnce(&ResidentSection<'c>) -> Result<R, NativeSessionError>,
    ) -> Result<R, NativeSessionError> {
        match self {
            Self::Values { values } => {
                let section = surface
                    .mount_exact_rational_packet(&vector(values)?)
                    .map_err(invalid)?;
                consume(&section)
            }
            Self::ProductOutput { product } => consume(
                products
                    .get(product)
                    .ok_or_else(|| invalid("unknown or released product"))?
                    .output(),
            ),
            Self::ProductReceiver { product, operator } => {
                let source = products
                    .get(product)
                    .ok_or_else(|| invalid("unknown or released product"))?;
                let receiver = operators
                    .get(operator)
                    .ok_or_else(|| invalid("unknown receiver operator"))?;
                let section = receiver.native.read_product(source).map_err(invalid)?;
                consume(&section)
            }
        }
    }
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
    predictors: BTreeMap<u64, NativeConditionalPredictor<'c>>,
    next_operator: u64,
    next_product: u64,
    next_search: u64,
    next_relation: u64,
    next_predictor: u64,
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
            predictors: BTreeMap::new(),
            next_operator: 0,
            next_product: 0,
            next_search: 0,
            next_relation: 0,
            next_predictor: 0,
        }
    }

    /// Borrow a retained mathematical input on the same resident surface without
    /// decoding it at the host boundary.  Product output and product-receiver
    /// inputs retain their existing core-identity checks through `with_section`.
    pub(crate) fn with_resident_input<R>(
        &self,
        input: &MathematicalInputWire,
        consume: impl FnOnce(&ResidentSection<'c>) -> Result<R, NativeSessionError>,
    ) -> Result<R, NativeSessionError> {
        input.with_section(
            self.surface,
            &self.operators,
            &self.products,
            consume,
        )
    }

    pub(crate) fn surface(&self) -> &'c ResidentSurface<'c> {
        self.surface
    }

    pub fn inspect(&self) -> Value {
        json!({"scope": "native-mathematical-application-session", "operators": self.operators.keys().collect::<Vec<_>>(),
            "retained_products": self.products.keys().collect::<Vec<_>>(),
            "pending_constructions": self.searches.keys().collect::<Vec<_>>(),
            "relations": self.relations.iter().map(|(id, r)| json!({"relation":id,
                "calibration_rows":r.occurrences(), "pending_prediction":r.pending_id()})).collect::<Vec<_>>(),
            "predictors": self.predictors.iter().map(|(id,p)| json!({"predictor":id,
                "source_operator":p.source_operator,"condition_operator":p.condition_operator,
                "observations":p.material.observations(),"source_chart":p.material.source_chart(),
                "pending_prediction":p.pending_id()})).collect::<Vec<_>>(),
            "census": self.surface.census()})
    }
    fn publish(
        &mut self,
        realization: BilinearRealization,
        linear: bool,
    ) -> Result<Value, NativeSessionError> {
        let native = ResidentBilinearMap::mount(self.surface, &realization).map_err(invalid)?;
        self.publish_ready(realization, native, linear)
    }
    fn publish_rebinding(
        &mut self,
        source: u64,
        realization: BilinearRealization,
    ) -> Result<Value, NativeSessionError> {
        let owner = self
            .operators
            .get(&source)
            .ok_or_else(|| invalid("unknown source operator"))?;
        let native = owner
            .native
            .rebind_receiver(&realization)
            .map_err(invalid)?;
        self.publish_ready(realization, native, owner.linear)
    }
    fn publish_ready(
        &mut self,
        realization: BilinearRealization,
        native: ResidentBilinearMap<'c>,
        linear: bool,
    ) -> Result<Value, NativeSessionError> {
        let next = self
            .next_operator
            .checked_add(1)
            .ok_or_else(|| invalid("operator addresses exhausted"))?;
        let id = self.next_operator;
        let result = json!({"status": "constructed", "operator": id, "linear_unit_right_port": linear,
            "factors": factor_description(&realization), "execution": "resident exact rational packet"});
        self.operators.insert(
            id,
            Operator {
                realization,
                native,
                linear,
                family: None,
            },
        );
        self.next_operator = next;
        Ok(result)
    }
    fn construct_linear_matrix(
        &mut self,
        target_matrix: ExactRatMatrix,
    ) -> Result<Value, NativeSessionError> {
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
    fn declared_linear_matrix(
        &self,
        operator: u64,
    ) -> Result<(ExactRatMatrix, holonic_engine::exact_work::ExactWork), NativeSessionError> {
        let op = self
            .operators
            .get(&operator)
            .ok_or_else(|| invalid("unknown operator"))?;
        if !op.linear {
            return Err(invalid("power requires a retained linear operator"));
        }
        if op.realization.core().right_forms().columns() != 1 {
            return Err(invalid("power requires the declared unit right port"));
        }
        op.realization
            .receiver()
            .particular
            .multiply_with_work(op.realization.core().tensor_image())
            .map_err(invalid)
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
            MathematicalRequest::EmitRust {operator} => {
                let owner=self.operators.get(operator).ok_or_else(||invalid("unknown operator"))?;
                let source=code::rust_function(&owner.realization,owner.linear)?;
                Ok(json!({"status":"code-emitted","operator":operator,"language":"rust",
                    "function":"holonic_apply","source":source,"linear":owner.linear,
                    "graph":factor_description(&owner.realization),
                    "numeric_chart":"num_rational::BigRational; arbitrary-precision exact integer coefficients",
                    "scope":"function of the retained operator; target compilation/execution is exterior"}))
            }
            MathematicalRequest::ConstructPredictor {source_operator,condition_operator,target_complex,fractional_bits} => {
                let a=self.operators.get(source_operator).ok_or_else(||invalid("unknown source restriction"))?;
                let c=self.operators.get(condition_operator).ok_or_else(||invalid("unknown condition restriction"))?;
                let ns=a.realization.receiver().particular.rows();
                let nc=c.realization.receiver().particular.rows();
                if !a.linear || !c.linear || ns==0 || nc==0 || ns%2!=0 || nc%2!=0 ||
                    a.realization.core().left_forms().columns()!=c.realization.core().left_forms().columns() {
                    return Err(invalid("source and condition restrictions must be linear complex charts on one preparation domain"));
                }
                let ns=ns/2;let nc=nc/2;
                let features=ns.checked_mul(nc).and_then(|v|v.checked_add(ns)).and_then(|v|v.checked_add(nc))
                    .ok_or_else(||invalid("feature extent overflow"))?;
                let material=ResidentNormalMaterial::found_features(self.surface,features,*target_complex,ResidentGrain(*fractional_bits))?;
                let id=self.next_predictor;
                let next=id.checked_add(1).ok_or_else(||invalid("predictor addresses exhausted"))?;
                self.predictors.insert(id,NativeConditionalPredictor::new(*source_operator,*condition_operator,material));
                self.next_predictor=next;
                Ok(json!({"status":"predictor-constructed","predictor":id,"source_complex":ns,"condition_complex":nc,
                    "feature_complex":features,"target_complex":target_complex,"source_operator":source_operator,"condition_operator":condition_operator,
                    "law":"H=I+sum uu*, B=sum vu*, WH=B; u=(s,c,c tensor s)","observations":0}))
            }
            MathematicalRequest::PredictSection {predictor,preparation,retain_prediction} => {
                let owner=self.predictors.get_mut(predictor).ok_or_else(||invalid("unknown predictor"))?;
                let a=self.operators.get(&owner.source_operator).ok_or_else(||invalid("missing source restriction"))?;
                let c=self.operators.get(&owner.condition_operator).ok_or_else(||invalid("missing condition restriction"))?;
                let reads=self.surface.census().section_read_outs;
                let unit=self.surface.mount_exact_rational_packet(&[BigRational::one()]).map_err(invalid)?;
                let features=preparation.with_section(self.surface,&self.operators,&self.products,|x| {
                    let source=a.native.apply(x,&unit).map_err(invalid)?;
                    let condition=c.native.apply(x,&unit).map_err(invalid)?;
                    Ok(ResidentConstitutiveSection::rationals(source.output())?
                        .bilinear_features(self.surface,ResidentConstitutiveSection::rationals(condition.output())?)?.into_features())
                })?;
                let intermediate=self.surface.census().section_read_outs-reads;
                let mut result=owner.predict(features,*retain_prediction)?;
                result["predictor"]=json!(predictor);
                result["preparation"]=json!(preparation);
                result["intermediate_section_readouts"]=json!(intermediate);
                Ok(result)
            }
            MathematicalRequest::ObserveSection {predictor,prediction,observed} => {
                let observation=self.surface.mount_exact_rational_packet(&vector(observed)?).map_err(invalid)?;
                self.predictors.get_mut(predictor).ok_or_else(||invalid("unknown predictor"))?
                    .observe(*prediction,ResidentConstitutiveCurrent::rational(&observation)?)
            }
            MathematicalRequest::ReleaseSectionPrediction {predictor,prediction} => {
                self.predictors.get_mut(predictor).ok_or_else(||invalid("unknown predictor"))?.release(*prediction)?;
                Ok(json!({"status":"released","predictor":predictor,"prediction":prediction}))
            }
            MathematicalRequest::ReleasePredictor {predictor} => {
                let owner=self.predictors.get(predictor).ok_or_else(||invalid("unknown predictor"))?;
                if owner.pending_id().is_some(){return Err(invalid("observe or dispose of the pending section prediction before releasing its predictor"));}
                self.predictors.remove(predictor);
                Ok(json!({"status":"released","predictor":predictor}))
            }
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
                let owner = self
                    .relations
                    .get_mut(relation)
                    .ok_or_else(|| invalid("unknown relation"))?;
                if *retain_prediction && owner.pending_id().is_some() {
                    return Err(invalid("this relation already retains an observation cut; observe or explicitly release it first (read-only predictions remain available)"));
                }
                let (prediction, reading) = source.with_section(
                    self.surface,
                    &self.operators,
                    &self.products,
                    |section| {
                        Ok(owner.predict(
                            ResidentConstitutiveCurrent::rational(section)?,
                            *retain_prediction,
                        )?)
                    },
                )?;
                Ok(
                    json!({"status":"relation-predicted", "relation":relation, "prediction":prediction, "reading":image_wire(reading),
                    "source":source, "scope":"full joint condition/output image; no selected condition representative"}),
                )
            }
            MathematicalRequest::PredictCondition {
                relation,
                operator,
                retain_prediction,
            } => {
                let owner = self
                    .relations
                    .get_mut(relation)
                    .ok_or_else(|| invalid("unknown relation"))?;
                if *retain_prediction && owner.pending_id().is_some() {
                    return Err(invalid("this relation already retains an observation cut; observe or explicitly release it first"));
                }
                let op = self
                    .operators
                    .get_mut(operator)
                    .ok_or_else(|| invalid("unknown operator"))?;
                let compiled_now = op.family.is_none();
                let (prediction, reading) =
                    owner.predict_through(op.family(self.surface)?, *retain_prediction)?;
                Ok(
                    json!({"status":"family-predicted", "relation":relation, "operator":operator,
                    "prediction":prediction, "reading":image_wire(reading),
                    "family_graph_compiled":compiled_now,
                    "scope":"joint prospective output of one complete source/condition family; no source representative selected"}),
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
                self.construct_linear_matrix(matrix(coefficients)?)
            }
            MathematicalRequest::Power { operator, exponent } => {
                let (source, source_reconstruction_work) = self.declared_linear_matrix(*operator)?;
                let rows = source.rows();
                let (powered, power_work) = source
                    .power_reduced_with_work(*exponent)
                    .map_err(invalid)?;
                let mut value = self.construct_linear_matrix(powered)?;
                value["power_of"] = json!(*operator);
                value["exponent"] = json!(*exponent);
                value["source_reconstruction_work"] = json!(source_reconstruction_work);
                value["power_construction_work"] = json!(power_work);
                value["power_scope"] = json!({
                    "source_shape": [rows, rows],
                    "source": "declared retained linear operator matrix reconstructed from its exact receiver/core",
                    "reduction": "exact minimal-polynomial exponentiation by squaring",
                    "execution": "exterior exact construction; resident application"
                });
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
                let left = MathematicalInputWire::Values {
                    values: left.clone(),
                };
                let right = right.as_ref().map(|values| MathematicalInputWire::Values {
                    values: values.clone(),
                });
                self.apply_inputs(*operator, &left, right.as_ref(), *retain_product, true)
            }
            MathematicalRequest::ApplyInputs {
                operator,
                left,
                right,
                retain_product,
                emit_output,
            } => self.apply_inputs(
                *operator,
                left,
                right.as_ref(),
                *retain_product,
                *emit_output,
            ),
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
                    Ok(realization) => self.publish_rebinding(*operator, realization),
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
                self.publish_rebinding(*operator, realization)
            }
            MathematicalRequest::Compose {
                operator,
                following,
                right,
            } => {
                let first = self
                    .operators
                    .get(operator)
                    .ok_or_else(|| invalid("unknown first operator"))?;
                let next = self
                    .operators
                    .get(following)
                    .ok_or_else(|| invalid("unknown following operator"))?;
                let fixed = if next.linear {
                    if right.is_some() {
                        return Err(invalid(
                            "following linear action already has its declared unit right port",
                        ));
                    }
                    vec![BigRational::one()]
                } else {
                    vector(right.as_ref().ok_or_else(|| {
                        invalid("composition requires the following right port to be fixed")
                    })?)?
                };
                let realization = first
                    .realization
                    .then_fixed_right(&next.realization, &fixed)
                    .map_err(invalid)?;
                let mut result = self.publish_rebinding(*operator, realization)?;
                result["composition"] = json!({"first":operator,"following":following,
                    "following_right":row_wire(&fixed),"scope":"the following fixed-right section is compiled into the first core receiver"});
                Ok(result)
            }
            MathematicalRequest::JoinReceivers { operators } => {
                let (&first_id, rest) = operators.split_first().ok_or_else(|| {
                    invalid("joint receiver requires at least one retained operator")
                })?;
                let first = self
                    .operators
                    .get(&first_id)
                    .ok_or_else(|| invalid("unknown first receiver"))?;
                let others = rest
                    .iter()
                    .map(|id| {
                        self.operators
                            .get(id)
                            .map(|op| &op.realization)
                            .ok_or_else(|| invalid("unknown receiver"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let extents = std::iter::once(&first.realization)
                    .chain(others.iter().copied())
                    .map(|op| op.receiver().particular.rows())
                    .collect::<Vec<_>>();
                let realization = first.realization.join_receivers(&others).map_err(invalid)?;
                let mut result = self.publish_rebinding(first_id, realization)?;
                result["joint_receiver"] = json!({"operators":operators, "output_extents":extents,
                    "scope":"ordered receiver blocks of the same retained product core"});
                Ok(result)
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
                if self.predictors.values().any(|p|p.source_operator==*operator || p.condition_operator==*operator) {
                    return Err(invalid("operator is a live predictor restriction; release that predictor first"));
                }
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
    fn apply_inputs(
        &mut self,
        operator: u64,
        left: &MathematicalInputWire,
        right: Option<&MathematicalInputWire>,
        retain_product: bool,
        emit_output: bool,
    ) -> Result<Value, NativeSessionError> {
        if !emit_output && !retain_product {
            return Err(invalid(
                "an unread intermediate must be retained for its next consumer",
            ));
        }
        let next = self
            .next_product
            .checked_add(u64::from(retain_product))
            .ok_or_else(|| invalid("product addresses exhausted"))?;
        let op = self
            .operators
            .get(&operator)
            .ok_or_else(|| invalid("unknown operator"))?;
        let unit = MathematicalInputWire::Values {
            values: vec![RationalWire::integer(1)],
        };
        let right = if op.linear {
            if right.is_some() {
                return Err(invalid(
                    "linear application supplies only left; right is the declared unit port",
                ));
            }
            &unit
        } else {
            right.ok_or_else(|| invalid("bilinear application requires right input"))?
        };
        let reads = self.surface.census().section_read_outs;
        let result = left.with_section(self.surface, &self.operators, &self.products, |x| {
            right.with_section(self.surface, &self.operators, &self.products, |y| {
                op.native.apply(x, y).map_err(invalid)
            })
        })?;
        let intermediate_reads = self.surface.census().section_read_outs - reads;
        let output = if emit_output {
            Some(self.read(result.output())?)
        } else {
            None
        };
        let product = if retain_product {
            let id = self.next_product;
            self.products.insert(id, result);
            self.next_product = next;
            Some(id)
        } else {
            None
        };
        Ok(
            json!({"status":"applied","operator":operator,"output":output,"product":product,
            "intermediate_section_readouts":intermediate_reads,"source_products_recomputed":true,
            "output_emitted":emit_output}),
        )
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
