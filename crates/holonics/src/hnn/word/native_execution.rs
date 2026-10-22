//! Numerical realization boundary for the SAME private native predictor.
//! These are executed operands, not caller-issued certificates. The original
//! unrun Word authenticates them and constructs all error/gain witnesses.
use super::*;
use crate::hnn::{constitution::Constitution,pending::PendingRatio};
use crate::hnn::port::WordReturn;
use crate::hnn::ratio::RatioCovector;

pub trait NativePredictionExecution:Sync {
    /// Exterior conservative count, including failed dispatch reservations.
    fn attempted_native_operations(&self)->u64{0}
    fn forward_native(&self,field:&Field,theta:&Constitution,ratio:&PendingRatio,
        charts:&mut Charts,opening:&WordOpening,phases:&ReceivingPhases)->Result<NativeExecutedPrediction,HnnError>;
}
pub trait NativeExecutedReturn:std::fmt::Debug {
    /// Consumes the opaque record whose actual/fresh forward supplied the read.
    fn return_native(self:Box<Self>,covector:&RatioCovector,map:&ExactRatMatrix,phases:&ReceivingPhases)->Result<WordReturn,HnnError>;
}
pub struct NativeExecutedPath {
    pub exact_opening:EndChange,
    /// Full-tick crossings, including the final pre-junction endpoint.
    pub points:Vec<EndChange>,
    pub anchors:Vec<Vec<Vec<Rat>>>,
    pub midpoints:Vec<Vec<Vec<Rat>>>,
}
pub struct NativeExecutedPrediction {
    pub operands:Operands,
    pub actual:NativeExecutedPath,
    pub fresh:NativeExecutedPath,
    pub reception_end:ReceptionCarry,
    /// Full-tick balance, excluding the backend's terminal read-only junction.
    pub released:Released,
    pub source_preparation:Option<action::PortPreparationReceipt>,
    pub returned:Box<dyn NativeExecutedReturn>,
}
