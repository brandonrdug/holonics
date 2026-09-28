//! Canonical checkpoint codec for a contemporary passage-code accumulator.
//!
//! The payload stores the four carried `ProductBound`s and the exact exponent and factor
//! count. It is a state representation: it does not retain faces or reconstruct the state by
//! replaying them.

use super::{PassageCode, ProductBound};

const MAGIC: &[u8; 8] = b"HPASS\0\0\x01";
const PRODUCT_BOUND_BITS: u32 = 127;
const PAYLOAD_LEN: usize = 8 + 4 * (16 + 8) + 8 + 8;

/// A refusal to encode or restore a passage-code accumulator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PassageCodecError {
    Version,
    Truncated { offset: usize },
    Trailing { offset: usize },
    Malformed { offset: usize, reason: &'static str },
    Inconsistent,
}

impl std::fmt::Display for PassageCodecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Version => write!(f, "unsupported passage-code checkpoint version"),
            Self::Truncated { offset } => {
                write!(f, "truncated passage-code checkpoint at byte {offset}")
            }
            Self::Trailing { offset } => {
                write!(f, "trailing passage-code checkpoint bytes at byte {offset}")
            }
            Self::Malformed { offset, reason } => {
                write!(
                    f,
                    "malformed passage-code checkpoint at byte {offset}: {reason}"
                )
            }
            Self::Inconsistent => write!(f, "inconsistent passage-code accumulator"),
        }
    }
}

impl std::error::Error for PassageCodecError {}

struct Writer(Vec<u8>);

impl Writer {
    fn u64(&mut self, value: u64) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    fn u128(&mut self, value: u128) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    fn bound(&mut self, bound: ProductBound) {
        self.u128(bound.mantissa);
        self.u64(bound.exponent);
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take<const N: usize>(&mut self) -> Result<[u8; N], PassageCodecError> {
        let end = self.at.checked_add(N).ok_or(PassageCodecError::Malformed {
            offset: self.at,
            reason: "length overflow",
        })?;
        let Some(slice) = self.bytes.get(self.at..end) else {
            return Err(PassageCodecError::Truncated { offset: self.at });
        };
        self.at = end;
        Ok(slice.try_into().expect("fixed-size slice"))
    }

    fn u64(&mut self) -> Result<u64, PassageCodecError> {
        Ok(u64::from_le_bytes(self.take()?))
    }

    fn u128(&mut self) -> Result<u128, PassageCodecError> {
        Ok(u128::from_le_bytes(self.take()?))
    }

    fn bound(&mut self) -> Result<ProductBound, PassageCodecError> {
        let offset = self.at;
        let mantissa = self.u128()?;
        let exponent = self.u64()?;
        if mantissa == 0 || 128 - mantissa.leading_zeros() > PRODUCT_BOUND_BITS {
            return Err(PassageCodecError::Malformed {
                offset,
                reason: "product-bound mantissa is outside its canonical range",
            });
        }
        Ok(ProductBound { mantissa, exponent })
    }
}

impl PassageCode {
    /// Encode the contemporary accumulator as a versioned, fixed-width little-endian payload.
    pub fn encode_checkpoint(&self) -> Vec<u8> {
        let mut writer = Writer(MAGIC.to_vec());
        for bound in self.numerator.into_iter().chain(self.denominator) {
            writer.bound(bound);
        }
        writer.u64(self.exponent);
        writer.u64(self.factors);
        debug_assert_eq!(writer.0.len(), PAYLOAD_LEN);
        writer.0
    }

    /// Restore the accumulator directly, refusing a wrong version or noncanonical payload.
    pub fn decode_checkpoint(bytes: &[u8]) -> Result<Self, PassageCodecError> {
        if bytes.len() < MAGIC.len() {
            return Err(PassageCodecError::Truncated {
                offset: bytes.len(),
            });
        }
        if &bytes[..MAGIC.len()] != MAGIC {
            return Err(PassageCodecError::Version);
        }
        let mut reader = Reader {
            bytes,
            at: MAGIC.len(),
        };
        let numerator = [reader.bound()?, reader.bound()?];
        let denominator = [reader.bound()?, reader.bound()?];
        let exponent = reader.u64()?;
        let factors = reader.u64()?;
        if reader.at != bytes.len() {
            return Err(PassageCodecError::Trailing { offset: reader.at });
        }
        if numerator[0] > numerator[1]
            || denominator[0] > denominator[1]
            || (factors == 0
                && (numerator != [ProductBound::ONE; 2]
                    || denominator != [ProductBound::ONE; 2]
                    || exponent != 0))
        {
            return Err(PassageCodecError::Inconsistent);
        }
        let restored = Self {
            numerator,
            denominator,
            exponent,
            factors,
        };
        if restored.encode_checkpoint() != bytes {
            return Err(PassageCodecError::Inconsistent);
        }
        Ok(restored)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::Rat;
    use num_bigint::{BigInt, BigUint};

    fn ratio(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    #[test]
    fn passage_checkpoint_restores_future_faces_and_canonical_bytes() {
        let mut current = PassageCode::new();
        current.side(7, 5);
        current.face(&ratio(11, 40)).unwrap();
        current.dyadic(&BigUint::from(37u8), 9);

        let bytes = current.encode_checkpoint();
        let mut restored = PassageCode::decode_checkpoint(&bytes).unwrap();
        assert_eq!(restored, current);
        assert_eq!(restored.encode_checkpoint(), bytes);
        assert_eq!(restored.bits().unwrap(), current.bits().unwrap());

        let next = ratio(13, 32);
        current.face(&next).unwrap();
        restored.face(&next).unwrap();
        assert_eq!(restored, current);
        assert_eq!(restored.encode_checkpoint(), current.encode_checkpoint());
        assert_eq!(restored.bits().unwrap(), current.bits().unwrap());

        let mut joined = PassageCode::new();
        joined.side(5, 3);
        current.join(&joined);
        restored.join(&joined);
        assert_eq!(restored, current);
        assert_eq!(restored.encode_checkpoint(), current.encode_checkpoint());
    }

    #[test]
    fn passage_checkpoint_refuses_bad_wire_shapes() {
        let bytes = PassageCode::new().encode_checkpoint();
        assert!(matches!(
            PassageCode::decode_checkpoint(&bytes[..bytes.len() - 1]),
            Err(PassageCodecError::Truncated { .. })
        ));
        let mut malformed = bytes.clone();
        malformed[8..24].fill(0);
        assert!(matches!(
            PassageCode::decode_checkpoint(&malformed),
            Err(PassageCodecError::Malformed { .. })
        ));
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(matches!(
            PassageCode::decode_checkpoint(&trailing),
            Err(PassageCodecError::Trailing { .. })
        ));
        let mut wrong_version = bytes;
        wrong_version[7] = 2;
        assert_eq!(
            PassageCode::decode_checkpoint(&wrong_version),
            Err(PassageCodecError::Version)
        );
    }
}
