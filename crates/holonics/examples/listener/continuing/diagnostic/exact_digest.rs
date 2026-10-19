//! Compact identifiers for exact diagnostic matrices, never a substitute for an operand.
//!
//! Canonical v1 input is the domain below, rows and columns as unsigned 128-bit big-endian
//! integers, then row-major reduced ratios. Each numerator and positive denominator is a sign
//! byte (zero=0, positive=1, negative=2), a 128-bit big-endian magnitude byte count, and the
//! unsigned big-endian magnitude (zero has no bytes). Shape and signs are therefore unambiguous.
//! No Debug or decimal rendering enters the digest. Integer magnitudes are streamed one at a time.
//!
//! SHA-256 compression follows the existing workspace utility in holonics-cuda/build.rs;
//! streaming avoids retaining a second serialization of an entire exact matrix.

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

struct Sha256 {
    state: [u32; 8],
    buffer: [u8; 64],
    used: usize,
    bytes: u128,
}

impl Sha256 {
    fn new() -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            buffer: [0; 64],
            used: 0,
            bytes: 0,
        }
    }

    fn update(&mut self, mut input: &[u8]) {
        self.bytes += input.len() as u128;
        if self.used != 0 {
            let count = input.len().min(64 - self.used);
            self.buffer[self.used..self.used + count].copy_from_slice(&input[..count]);
            self.used += count;
            input = &input[count..];
            if self.used < 64 {
                return;
            }
            let block = self.buffer;
            self.compress(&block);
            self.used = 0;
        }
        while input.len() >= 64 {
            self.compress(&input[..64]);
            input = &input[64..];
        }
        self.buffer[..input.len()].copy_from_slice(input);
        self.used = input.len();
    }

    fn finish(mut self) -> String {
        // SHA-256 length field is the message length modulo 2^64 bits.
        let bits = (self.bytes as u64).wrapping_mul(8);
        self.update(&[0x80]);
        let zero_padding = [0; 64];
        if self.used > 56 {
            self.update(&zero_padding[..64 - self.used]);
        }
        self.update(&zero_padding[..56 - self.used]);
        self.update(&bits.to_be_bytes());
        self.state
            .iter()
            .map(|word| format!("{word:08x}"))
            .collect()
    }

    fn compress(&mut self, block: &[u8]) {
        const K: [u32; 64] = [
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
            0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
            0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
            0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
            0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
            0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
            0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
            0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
            0xc67178f2,
        ];
        let mut w = [0u32; 64];
        for (i, word) in block.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = self.state;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choice = (e & f) ^ (!e & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(choice)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(majority);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (slot, value) in self.state.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *slot = slot.wrapping_add(value);
        }
    }
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
