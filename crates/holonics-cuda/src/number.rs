//! **The number header on the card, beside its host owner** (step 2 of the number record's build order;
//! `kernels/number.cuh`, its parity kernels `kernels/number.cu`; the host owner `holonics::number`).
//!
//! Each function runs one of the header's operations over arrays of cases and returns the card's words, for the parity
//! read against the host owner (`tests/number_parity.rs`): a word is `L` limbs of 32 places, little-endian.

use core::ffi::c_void;

use crate::cuda::{Dim3, Module, Stream};
use crate::ffi::CUdeviceptr;
use crate::hnn::DeviceError;
use crate::hnn::card::Card;

const IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/number.ptx"));

/// One case's words from `hn_parity_<L>`: the sum and its carry, the difference and its borrow, the signed sum's winding,
/// the unsigned and the signed products, the release's quotient and remainder, the bottom inverse of `a | 1` and its steps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParityCase {
    pub sum: Vec<u32>,
    pub carry: u32,
    pub difference: Vec<u32>,
    pub borrow: u32,
    pub winding: i32,
    pub product: Vec<u32>,
    pub signed_product: Vec<u32>,
    pub quotient: Vec<u32>,
    pub remainder: Vec<u32>,
    pub inverse: Vec<u32>,
    pub steps: u32,
}

fn launch(module: &Module, stream: &Stream, name: &str, threads: u32, blocks: u32, params: &mut [*mut c_void]) -> Result<(), DeviceError> {
    module.function(name)?.launch_on_shared(stream, Dim3 { x: blocks, y: 1, z: 1 }, Dim3 { x: threads, y: 1, z: 1 }, 0, params)?;
    stream.synchronize()?;
    Ok(())
}

/// **The header's per-thread operations** at `L` limbs (1, 2, 4 or 8) on cases `(a, b, k)`: `a` and `b` of `L` limbs each,
/// `k` the release's places (`0 < k < 32L`).
pub fn parity(card: &Card, limbs: usize, cases: &[(Vec<u32>, Vec<u32>, i32)]) -> Result<Vec<ParityCase>, DeviceError> {
    let name = match limbs {
        1 => "hn_parity_1",
        2 => "hn_parity_2",
        4 => "hn_parity_4",
        8 => "hn_parity_8",
        _ => return Err(DeviceError::Launch { entry: "number parity", clause: "the number header's parity is built at 1, 2, 4 and 8 limbs" }),
    };
    if cases.iter().any(|(a, b, k)| a.len() != limbs || b.len() != limbs || *k < 1 || *k as usize >= 32 * limbs) {
        return Err(DeviceError::Launch { entry: "number parity", clause: "a parity case outside its limbs or its release's places" });
    }
    card.current()?;
    let module = Module::load_ptx(IMAGE)?;
    let stream = Stream::create()?;
    let a: Vec<u32> = cases.iter().flat_map(|c| c.0.iter().copied()).collect();
    let b: Vec<u32> = cases.iter().flat_map(|c| c.1.iter().copied()).collect();
    let k: Vec<i32> = cases.iter().map(|c| c.2).collect();
    let words = 9 * limbs + 4;
    let (da, db, dk) = (card.upload(&a)?, card.upload(&b)?, card.upload(&k)?);
    let out = card.alloc::<u32>(cases.len() * words)?;
    let (mut pa, mut pb, mut pk, mut po) = (da.device_ptr(), db.device_ptr(), dk.device_ptr(), out.device_ptr());
    let mut n = cases.len() as i32;
    let mut params: [*mut c_void; 5] = [
        (&mut pa as *mut CUdeviceptr).cast(),
        (&mut pb as *mut CUdeviceptr).cast(),
        (&mut pk as *mut CUdeviceptr).cast(),
        (&mut n as *mut i32).cast(),
        (&mut po as *mut CUdeviceptr).cast(),
    ];
    launch(&module, &stream, name, 128, (cases.len() as u32).div_ceil(128).max(1), &mut params)?;
    let words_out = card.fetch(&out)?;
    let l = limbs;
    Ok(words_out
        .chunks_exact(words)
        .map(|w| {
            let mut o = 0;
            let mut take = |n: usize| {
                let v = w[o..o + n].to_vec();
                o += n;
                v
            };
            let sum = take(l);
            let carry = take(1)[0];
            let difference = take(l);
            let borrow = take(1)[0];
            let winding = take(1)[0] as i32;
            let product = take(2 * l);
            let signed_product = take(2 * l);
            let quotient = take(l);
            let remainder = take(l);
            let inverse = take(l);
            let steps = take(1)[0];
            ParityCase { sum, carry, difference, borrow, winding, product, signed_product, quotient, remainder, inverse, steps }
        })
        .collect())
}

/// **The cut add** on packed 32-place words: each case's `(x, y, H)`.
pub fn cut_add(card: &Card, cases: &[(u32, u32, u32)]) -> Result<Vec<u32>, DeviceError> {
    card.current()?;
    let module = Module::load_ptx(IMAGE)?;
    let stream = Stream::create()?;
    let x: Vec<u32> = cases.iter().map(|c| c.0).collect();
    let y: Vec<u32> = cases.iter().map(|c| c.1).collect();
    let h: Vec<u32> = cases.iter().map(|c| c.2).collect();
    let (dx, dy, dh) = (card.upload(&x)?, card.upload(&y)?, card.upload(&h)?);
    let out = card.alloc::<u32>(cases.len())?;
    let (mut px, mut py, mut ph, mut po) = (dx.device_ptr(), dy.device_ptr(), dh.device_ptr(), out.device_ptr());
    let mut n = cases.len() as i32;
    let mut params: [*mut c_void; 5] = [
        (&mut px as *mut CUdeviceptr).cast(),
        (&mut py as *mut CUdeviceptr).cast(),
        (&mut ph as *mut CUdeviceptr).cast(),
        (&mut n as *mut i32).cast(),
        (&mut po as *mut CUdeviceptr).cast(),
    ];
    launch(&module, &stream, "hn_parity_cut", 128, (cases.len() as u32).div_ceil(128).max(1), &mut params)?;
    card.fetch(&out)
}

/// **The warp's add** of 1,024-place words (32 limbs each): each case's sum limbs and its winding.
pub fn warp_add(card: &Card, cases: &[([u32; 32], [u32; 32])]) -> Result<Vec<([u32; 32], u32)>, DeviceError> {
    card.current()?;
    let module = Module::load_ptx(IMAGE)?;
    let stream = Stream::create()?;
    let a: Vec<u32> = cases.iter().flat_map(|c| c.0).collect();
    let b: Vec<u32> = cases.iter().flat_map(|c| c.1).collect();
    let (da, db) = (card.upload(&a)?, card.upload(&b)?);
    let out = card.alloc::<u32>(cases.len() * 33)?;
    let (mut pa, mut pb, mut po) = (da.device_ptr(), db.device_ptr(), out.device_ptr());
    let mut n = cases.len() as i32;
    let mut params: [*mut c_void; 4] = [
        (&mut pa as *mut CUdeviceptr).cast(),
        (&mut pb as *mut CUdeviceptr).cast(),
        (&mut n as *mut i32).cast(),
        (&mut po as *mut CUdeviceptr).cast(),
    ];
    // Four warps a block, one warp a case.
    launch(&module, &stream, "hn_parity_warp", 128, (cases.len() as u32).div_ceil(4).max(1), &mut params)?;
    let words = card.fetch(&out)?;
    Ok(words
        .chunks_exact(33)
        .map(|w| {
            let mut limbs = [0u32; 32];
            limbs.copy_from_slice(&w[..32]);
            (limbs, w[32])
        })
        .collect())
}
