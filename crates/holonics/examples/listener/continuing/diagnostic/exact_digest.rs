//! Compact identifiers for exact diagnostic matrices, never a substitute for an operand.
//!
//! Canonical v1 input is the domain below, rows and columns as unsigned 128-bit big-endian
//! integers, then row-major reduced ratios. Each numerator and positive denominator is a sign
//! byte (zero=0, positive=1, negative=2), a 128-bit big-endian magnitude byte count, and the
//! unsigned big-endian magnitude (zero has no bytes). Shape and signs are therefore unambiguous.
//! No Debug or decimal rendering enters the digest. Integer magnitudes are streamed one at a time.
//!
//! SHA-256 is shared with the boundary chart owner in sections/sha256.rs;
//! streaming avoids retaining a second serialization of an entire exact matrix.

use crate::sections::Sha256;
use holonics::ratio::Rat;
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::{BigInt, Sign};
use num_traits::Zero;
use std::fmt;

const MATRIX_DOMAIN: &[u8] = b"holonics.exact-rat-matrix.v1\0";

pub(super) struct MatrixSummary {
    rows: usize,
    columns: usize,
    nonzero: usize,
    numerator_max_bits: u64,
    denominator_max_bits: u64,
    numerator_total_bits: u128,
    denominator_total_bits: u128,
    canonical_bytes: u128,
    sha256: String,
}

impl fmt::Display for MatrixSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "rows={} columns={} entries={} nonzero={} operand_numerator_max_bits={} operand_denominator_max_bits={} operand_numerator_total_bits={} operand_denominator_total_bits={} canonical_bytes={} canonical_format=exact-rat-matrix-v1 sha256={}",
            self.rows,
            self.columns,
            self.rows * self.columns,
            self.nonzero,
            self.numerator_max_bits,
            self.denominator_max_bits,
            self.numerator_total_bits,
            self.denominator_total_bits,
            self.canonical_bytes,
            self.sha256
        )
    }
}

pub(super) fn matrix_summary(matrix: &ExactRatMatrix) -> MatrixSummary {
    matrix_summary_checked(matrix, || Ok::<(), std::convert::Infallible>(()))
        .unwrap_or_else(|never| match never {})
}

pub(super) fn matrix_summary_checked<E>(
    matrix: &ExactRatMatrix,
    mut checkpoint: impl FnMut() -> Result<(), E>,
) -> Result<MatrixSummary, E> {
    checkpoint()?;
    let mut digest = Sha256::new();
    digest.update(MATRIX_DOMAIN);
    digest.update(&(matrix.rows() as u128).to_be_bytes());
    digest.update(&(matrix.columns() as u128).to_be_bytes());
    let mut summary = MatrixSummary {
        rows: matrix.rows(),
        columns: matrix.columns(),
        nonzero: 0,
        numerator_max_bits: 0,
        denominator_max_bits: 0,
        numerator_total_bits: 0,
        denominator_total_bits: 0,
        canonical_bytes: 0,
        sha256: String::new(),
    };
    for operand in matrix.entries() {
        checkpoint()?;
        summary.numerator_max_bits = summary.numerator_max_bits.max(operand.numer().bits());
        summary.denominator_max_bits = summary.denominator_max_bits.max(operand.denom().bits());
        summary.numerator_total_bits += u128::from(operand.numer().bits());
        summary.denominator_total_bits += u128::from(operand.denom().bits());
        summary.nonzero += usize::from(!operand.is_zero());
        // Matrix construction accepts raw Rat values too; canonical identity is of the value,
        // whereas the bit widths above describe the actual operands passed to this reading.
        let value = Rat::new(operand.numer().clone(), operand.denom().clone());
        encode_integer(&mut digest, value.numer());
        encode_integer(&mut digest, value.denom());
    }
    checkpoint()?;
    summary.canonical_bytes = digest.bytes;
    summary.sha256 = digest.finish();
    Ok(summary)
}

fn encode_integer(digest: &mut Sha256, value: &BigInt) {
    let (sign, mut magnitude) = value.to_bytes_be();
    if sign == Sign::NoSign {
        magnitude.clear();
    }
    digest.update(&[match sign {
        Sign::NoSign => 0,
        Sign::Plus => 1,
        Sign::Minus => 2,
    }]);
    digest.update(&(magnitude.len() as u128).to_be_bytes());
    digest.update(&magnitude);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn digest(parts: &[&[u8]]) -> String {
        let mut sha = Sha256::new();
        for part in parts {
            sha.update(part);
        }
        sha.finish()
    }

    #[test]
    fn sha256_standard_vectors_and_stream_boundaries() {
        assert_eq!(
            digest(&[b""]),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            digest(&[b"abc"]),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        let long = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        let expected = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1";
        for boundary in 0..=long.len() {
            assert_eq!(digest(&[&long[..boundary], &long[boundary..]]), expected);
        }
        let million = vec![b'a'; 1_000_000];
        assert_eq!(
            digest(&million.chunks(63).collect::<Vec<_>>()),
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        );
    }

    #[test]
    fn canonical_matrix_identity_normalizes_values_and_preserves_shape_and_sign() {
        let m = |value| ExactRatMatrix::new(vec![vec![value]]).unwrap();
        let half = m(Rat::new(1.into(), 2.into()));
        let raw_half = m(Rat::new_raw(2.into(), 4.into()));
        assert_eq!(
            matrix_summary(&half).sha256,
            "af81ff1dc4bb3e17e1aea9a6aabc21593f4268469baacf69454e805c181f42a4"
        );
        assert_eq!(matrix_summary(&half).canonical_bytes, 97);
        assert_eq!(
            matrix_summary(&half).sha256,
            matrix_summary(&raw_half).sha256
        );
        assert_eq!(matrix_summary(&raw_half).numerator_max_bits, 2);
        assert_eq!(matrix_summary(&raw_half).denominator_max_bits, 3);
        let negative = m(Rat::new((-1).into(), 2.into()));
        assert_ne!(
            matrix_summary(&half).sha256,
            matrix_summary(&negative).sha256
        );
        let empty_wide = ExactRatMatrix::zero(0, 2).unwrap();
        let empty_tall = ExactRatMatrix::zero(2, 0).unwrap();
        assert_ne!(
            matrix_summary(&empty_wide).sha256,
            matrix_summary(&empty_tall).sha256
        );
        let horizontal = ExactRatMatrix::new(vec![vec![
            Rat::from_integer(1.into()),
            Rat::from_integer(2.into()),
        ]])
        .unwrap();
        let vertical = horizontal.transpose().unwrap();
        assert_ne!(
            matrix_summary(&horizontal).sha256,
            matrix_summary(&vertical).sha256
        );
    }

    #[test]
    fn matrix_digest_checks_cutoff_during_operand_stream() {
        let matrix = ExactRatMatrix::zero(2, 2).unwrap();
        let mut checkpoints = 0;
        let result = matrix_summary_checked(&matrix, || {
            checkpoints += 1;
            if checkpoints == 3 {
                Err("cutoff")
            } else {
                Ok(())
            }
        });
        assert!(matches!(result, Err("cutoff")));
        assert_eq!(checkpoints, 3);
    }
}
