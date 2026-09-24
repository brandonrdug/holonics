//! Exterior exact-current codecs. Decimal strings avoid JSON-number precision loss.
use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RationalWire {
    pub numerator: String,
    pub denominator: String,
}
impl RationalWire {
    pub fn integer(value: i64) -> Self {
        Self {
            numerator: value.to_string(),
            denominator: "1".into(),
        }
    }
    pub fn from_rational(value: &BigRational) -> Self {
        Self {
            numerator: value.numer().to_string(),
            denominator: value.denom().to_string(),
        }
    }
    pub fn rational(&self) -> Result<BigRational, NativeSessionError> {
        let n: BigInt = self
            .numerator
            .parse()
            .map_err(|_| NativeSessionError::Application("invalid integer numerator".into()))?;
        let d: BigInt = self
            .denominator
            .parse()
            .map_err(|_| NativeSessionError::Application("invalid integer denominator".into()))?;
        if d <= BigInt::zero() {
            return Err(NativeSessionError::Application(
                "denominator must be positive".into(),
            ));
        }
        Ok(BigRational::new(n, d))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CurrentWire {
    pub real: RationalWire,
    pub imaginary: RationalWire,
}
impl CurrentWire {
    pub fn integers(real: i64, imaginary: i64) -> Self {
        Self {
            real: RationalWire::integer(real),
            imaginary: RationalWire::integer(imaginary),
        }
    }
    pub fn from_current(current: &ExactComplexWaveCurrent) -> Self {
        Self {
            real: RationalWire::from_rational(&current.real),
            imaginary: RationalWire::from_rational(&current.imaginary),
        }
    }
    pub fn current(&self) -> Result<ExactComplexWaveCurrent, NativeSessionError> {
        Ok(ExactComplexWaveCurrent::new(
            self.real.rational()?,
            self.imaginary.rational()?,
        ))
    }
    pub fn native(&self) -> Result<NativePhaseCurrent, NativeSessionError> {
        Ok(NativePhaseCurrent::from_current(&self.current()?)?)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum ReceiverWire {
    Unique {
        current: Vec<RationalWire>,
    },
    OutsideDomain {
        source_remainder: Vec<RationalWire>,
    },
    Plural {
        particular: Vec<RationalWire>,
        directions: Vec<Vec<RationalWire>>,
    },
}
impl From<&ConstitutiveReading> for ReceiverWire {
    fn from(value: &ConstitutiveReading) -> Self {
        let row =
            |r: &[num_rational::BigRational]| r.iter().map(RationalWire::from_rational).collect();
        match value {
            ConstitutiveReading::Unique { current } => Self::Unique {
                current: row(current),
            },
            ConstitutiveReading::OutsideDomain { source_remainder } => Self::OutsideDomain {
                source_remainder: row(source_remainder),
            },
            ConstitutiveReading::Plural {
                particular,
                directions,
            } => Self::Plural {
                particular: row(particular),
                directions: directions.iter().map(|r| row(r)).collect(),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JunctionSpec {
    pub incoming_admittance: i64,
    pub held_admittance: i64,
    pub incoming_transport: CurrentWire,
    pub initial_held: CurrentWire,
}
impl JunctionSpec {
    pub fn native(&self) -> Result<NativeJunctionSeed, NativeSessionError> {
        let seed = NativeJunctionSeed {
            incoming_admittance: self.incoming_admittance,
            held_admittance: self.held_admittance,
            incoming_transport: self.incoming_transport.native()?,
            initial_held: self.initial_held.native()?,
        };
        seed.validate()?;
        Ok(seed)
    }
}

pub const NATIVE_MODEL_SPEC_SCHEMA: &str = "org.holonics.hna.native-phase-seed.v1";
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeModelSpec {
    pub schema: String,
    pub nodes: Vec<JunctionSpec>,
}
impl NativeModelSpec {
    pub fn read(bytes: &[u8]) -> Result<Self, NativeSessionError> {
        let spec: Self = serde_json::from_slice(bytes)?;
        spec.material()?;
        Ok(spec)
    }
    pub fn material(&self) -> Result<Vec<NativeJunctionSeed>, NativeSessionError> {
        if self.schema != NATIVE_MODEL_SPEC_SCHEMA || self.nodes.is_empty() {
            return Err(NativeSessionError::Application(
                "native seed schema or empty material".into(),
            ));
        }
        self.nodes.iter().map(JunctionSpec::native).collect()
    }
}
