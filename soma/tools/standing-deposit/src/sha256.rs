//! Streaming SHA-256.
//!
//! Streaming rather than whole-file, because the closure of a founding includes its executable and
//! an executable is tens of megabytes. `soma/tools/record-index/src/sha256.rs` hashes a `&[u8]`,
//! which requires slurping the file first; that owner is not reused here for exactly that reason.
//!
//! The digest is emitted as lowercase hex so that a manifest row is greppable and so that the
//! closure construction — a hash of concatenated hex digests — reproduces CMake's
//! `file(SHA256)` / `string(SHA256)` pair octet for octet. That reproduction is what lets this
//! verifier read the archived C++ manifest natively.

use std::fs::File;
use std::io::{BufReader, Read};
use std::path::Path;

const INITIAL: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];

const K: [u32; 64] = [
    0x428a_2f98,
    0x7137_4491,
    0xb5c0_fbcf,
    0xe9b5_dba5,
    0x3956_c25b,
    0x59f1_11f1,
    0x923f_82a4,
    0xab1c_5ed5,
    0xd807_aa98,
    0x1283_5b01,
    0x2431_85be,
    0x550c_7dc3,
    0x72be_5d74,
    0x80de_b1fe,
    0x9bdc_06a7,
    0xc19b_f174,
    0xe49b_69c1,
    0xefbe_4786,
    0x0fc1_9dc6,
    0x240c_a1cc,
    0x2de9_2c6f,
    0x4a74_84aa,
    0x5cb0_a9dc,
    0x76f9_88da,
    0x983e_5152,
    0xa831_c66d,
    0xb003_27c8,
    0xbf59_7fc7,
    0xc6e0_0bf3,
    0xd5a7_9147,
    0x06ca_6351,
    0x1429_2967,
    0x27b7_0a85,
    0x2e1b_2138,
    0x4d2c_6dfc,
    0x5338_0d13,
    0x650a_7354,
    0x766a_0abb,
    0x81c2_c92e,
    0x9272_2c85,
    0xa2bf_e8a1,
    0xa81a_664b,
    0xc24b_8b70,
    0xc76c_51a3,
    0xd192_e819,
    0xd699_0624,
    0xf40e_3585,
    0x106a_a070,
    0x19a4_c116,
    0x1e37_6c08,
    0x2748_774c,
    0x34b0_bcb5,
    0x391c_0cb3,
    0x4ed8_aa4a,
    0x5b9c_ca4f,
    0x682e_6ff3,
    0x748f_82ee,
    0x78a5_636f,
    0x84c8_7814,
    0x8cc7_0208,
    0x90be_fffa,
    0xa450_6ceb,
    0xbef9_a3f7,
    0xc671_78f2,
];

/// An incremental SHA-256 state. Fixed size; it allocates nothing.
pub struct Sha256 {
    state: [u32; 8],
    block: [u8; 64],
    filled: usize,
    octets: u64,
}

impl Default for Sha256 {
    fn default() -> Self {
        Self::new()
    }
}

impl Sha256 {
    pub fn new() -> Self {
        Self {
            state: INITIAL,
            block: [0u8; 64],
            filled: 0,
            octets: 0,
        }
    }

    pub fn update(&mut self, mut bytes: &[u8]) {
        self.octets = self.octets.wrapping_add(bytes.len() as u64);
        while !bytes.is_empty() {
            let want = 64 - self.filled;
            let take = want.min(bytes.len());
            self.block[self.filled..self.filled + take].copy_from_slice(&bytes[..take]);
            self.filled += take;
            bytes = &bytes[take..];
            if self.filled == 64 {
                let block = self.block;
                compress(&mut self.state, &block);
                self.filled = 0;
            }
        }
    }

    pub fn finish(mut self) -> [u8; 32] {
        let bits = self.octets.wrapping_mul(8);
        self.update_raw(&[0x80]);
        while self.filled != 56 {
            self.update_raw(&[0x00]);
        }
        self.update_raw(&bits.to_be_bytes());

        let mut digest = [0u8; 32];
        for (slot, word) in digest.chunks_exact_mut(4).zip(self.state) {
            slot.copy_from_slice(&word.to_be_bytes());
        }
        digest
    }

    /// Padding bytes must not be counted into the message length.
    fn update_raw(&mut self, bytes: &[u8]) {
        let counted = self.octets;
        self.update(bytes);
        self.octets = counted;
    }

    pub fn finish_hex(self) -> String {
        hex(&self.finish())
    }
}

fn compress(state: &mut [u32; 8], block: &[u8; 64]) {
    let mut w = [0u32; 64];
    for (slot, chunk) in w[..16].iter_mut().zip(block.chunks_exact(4)) {
        *slot = u32::from_be_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
    }
    for i in 16..64 {
        let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16]
            .wrapping_add(s0)
            .wrapping_add(w[i - 7])
            .wrapping_add(s1);
    }

    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
    for i in 0..64 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ ((!e) & g);
        let t1 = h
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(K[i])
            .wrapping_add(w[i]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = s0.wrapping_add(maj);

        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }

    for (slot, value) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
        *slot = slot.wrapping_add(value);
    }
}

pub fn hex(digest: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(digest.len() * 2);
    for octet in digest {
        out.push(DIGITS[(octet >> 4) as usize] as char);
        out.push(DIGITS[(octet & 0x0f) as usize] as char);
    }
    out
}

pub fn digest_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.finish_hex()
}

/// Hash a file without holding it. Returns the hex digest and the octet count.
pub fn file_digest_hex(path: &Path) -> std::io::Result<(String, u64)> {
    let file = File::open(path)?;
    let mut reader = BufReader::new(file);
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 65536];
    let mut octets = 0u64;
    loop {
        let read = reader.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
        octets += read as u64;
    }
    Ok((hasher.finish_hex(), octets))
}

pub fn is_hex64(field: &str) -> bool {
    field.len() == 64
        && field
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

#[cfg(test)]
mod tests {
    use super::{digest_hex, Sha256};

    #[test]
    fn nist_vectors() {
        assert_eq!(
            digest_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            digest_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            digest_hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }

    #[test]
    fn streaming_agrees_with_whole_message_at_every_split() {
        let message: Vec<u8> = (0u16..1000).map(|i| (i % 251) as u8).collect();
        let whole = digest_hex(&message);
        for split in 0..message.len() {
            let mut hasher = Sha256::new();
            hasher.update(&message[..split]);
            hasher.update(&message[split..]);
            assert_eq!(hasher.finish_hex(), whole, "split at {split}");
        }
    }

    #[test]
    fn million_a_vector() {
        let mut hasher = Sha256::new();
        let chunk = [b'a'; 1000];
        for _ in 0..1000 {
            hasher.update(&chunk);
        }
        assert_eq!(
            hasher.finish_hex(),
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        );
    }
}
