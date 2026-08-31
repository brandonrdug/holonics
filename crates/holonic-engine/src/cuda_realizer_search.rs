//! The resident search for supported realizers on an elliptic quartic.
//!
//! The card owns the deed. A rational point of `y^2 = c4 x^4 + … + c0` at `x = n/d` is exactly an
//! integer pair whose homogeneous form `Q(n, d)` is a perfect square, so the search is integer
//! arithmetic end to end and no float enters at any point — not in the filter, not in the bound,
//! not in the admission.
//!
//! **The card returns refusals, never admissions.** A survivor is a pair `Q(n, d)` failed to be a
//! non-residue at any declared prime receiver; the exact square test happens here, on integers
//! wider than the kernel carries. The declared prime family is the aperture and it is reported
//! with the return, because a survivor population measures *that* family: widening it removes
//! survivors and never adds them.
//!
//! Why the quartic and not the Weierstrass model: for leaderboard curve #159 the minimal model's
//! `c4` is 190 bits while the quartic's coefficients are 55, and the realizers sit at `x` of
//! moderate height on the quartic. Searching the model the curve is *presented* in rather than the
//! model it is *published* in is the whole of the leverage.

use crate::mordell_weil_realizers::IntegralQuartic;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use std::ffi::{CStr, c_char, c_void};
use std::ptr;

const CUDA_SUCCESS: i32 = 0;
const DEVICE_MAX_THREADS_PER_BLOCK: i32 = 1;
const DEVICE_WARP_SIZE: i32 = 10;

const PTX: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/exact_quartic_realizers.ptx"));

type CuDevice = i32;
type CuContext = *mut c_void;
type CuModule = *mut c_void;
type CuFunction = *mut c_void;
type CuDevicePtr = u64;
type CuStream = *mut c_void;

#[link(name = "cuda")]
unsafe extern "C" {
    fn cuInit(flags: u32) -> i32;
    fn cuDeviceGetCount(count: *mut i32) -> i32;
    fn cuDeviceGet(device: *mut CuDevice, ordinal: i32) -> i32;
    fn cuDeviceGetAttribute(value: *mut i32, attribute: i32, device: CuDevice) -> i32;
    fn cuCtxCreate_v2(context: *mut CuContext, flags: u32, device: CuDevice) -> i32;
    fn cuCtxDestroy_v2(context: CuContext) -> i32;
    fn cuModuleLoadData(module: *mut CuModule, image: *const c_void) -> i32;
    fn cuModuleUnload(module: CuModule) -> i32;
    fn cuModuleGetFunction(function: *mut CuFunction, module: CuModule, name: *const c_char)
    -> i32;
    fn cuMemAlloc_v2(pointer: *mut CuDevicePtr, bytes: usize) -> i32;
    fn cuMemFree_v2(pointer: CuDevicePtr) -> i32;
    fn cuMemcpyHtoD_v2(destination: CuDevicePtr, source: *const c_void, bytes: usize) -> i32;
    fn cuMemcpyDtoH_v2(destination: *mut c_void, source: CuDevicePtr, bytes: usize) -> i32;
    fn cuMemsetD8_v2(destination: CuDevicePtr, value: u8, count: usize) -> i32;
    fn cuLaunchKernel(
        function: CuFunction,
        grid_x: u32,
        grid_y: u32,
        grid_z: u32,
        block_x: u32,
        block_y: u32,
        block_z: u32,
        shared_memory_bytes: u32,
        stream: CuStream,
        kernel_parameters: *mut *mut c_void,
        extra: *mut *mut c_void,
    ) -> i32;
    fn cuCtxSynchronize() -> i32;
    fn cuGetErrorName(error: i32, name: *mut *const c_char) -> i32;
    fn cuGetErrorString(error: i32, message: *mut *const c_char) -> i32;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RealizerSearchError {
    NoDevice,
    Driver {
        operation: &'static str,
        code: i32,
        name: String,
        message: String,
    },
    /// The survivor buffer filled. The aperture is too wide for the declared capacity; the return
    /// is refused rather than truncated, because a truncated population reads as a measurement.
    SurvivorOverflow {
        seen: u32,
        capacity: u32,
    },
}

impl std::fmt::Display for RealizerSearchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoDevice => write!(f, "no CUDA device answered"),
            Self::Driver {
                operation,
                code,
                name,
                message,
            } => write!(f, "{operation} failed: {name} ({code}): {message}"),
            Self::SurvivorOverflow { seen, capacity } => {
                write!(
                    f,
                    "survivor buffer overflowed: {seen} seen, {capacity} held"
                )
            }
        }
    }
}

impl std::error::Error for RealizerSearchError {}

fn driver_text(query: unsafe extern "C" fn(i32, *mut *const c_char) -> i32, code: i32) -> String {
    let mut text = ptr::null();
    // SAFETY: CUDA writes one driver-owned NUL-terminated string pointer.
    let status = unsafe { query(code, &mut text) };
    if status == CUDA_SUCCESS && !text.is_null() {
        // SAFETY: a successful query returns a live C string.
        unsafe { CStr::from_ptr(text) }
            .to_string_lossy()
            .into_owned()
    } else {
        "<no CUDA driver description>".to_owned()
    }
}

/// Free every live device allocation. Taken by value so no borrow outlives the call, which is why
/// this is a function rather than the closure the first draft used.
fn release(pointers: [CuDevicePtr; 4]) {
    // SAFETY: each pointer is either null or one this module allocated and has not yet freed.
    unsafe {
        for pointer in pointers {
            if pointer != 0 {
                let _ = cuMemFree_v2(pointer);
            }
        }
    }
}

fn driver(code: i32, operation: &'static str) -> Result<(), RealizerSearchError> {
    if code == CUDA_SUCCESS {
        Ok(())
    } else {
        Err(RealizerSearchError::Driver {
            operation,
            code,
            name: driver_text(cuGetErrorName, code),
            message: driver_text(cuGetErrorString, code),
        })
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct PackedReceiver {
    prime: u32,
    table_offset: u32,
    coefficient: [u32; 5],
}

const _: () = assert!(std::mem::size_of::<PackedReceiver>() == 28);

/// The declared prime family, with its quadratic-residue tables, reduced against one quartic.
#[derive(Debug, Clone)]
pub struct ReceiverFamily {
    packed: Vec<PackedReceiver>,
    tables: Vec<u8>,
    primes: Vec<u32>,
}

impl ReceiverFamily {
    /// Reduce a quartic at every prime in the family. A prime dividing every coefficient carries no
    /// refusal and is dropped, and that drop is part of the aperture the return reports.
    pub fn declare(quartic: &IntegralQuartic, primes: &[u64]) -> Self {
        let mut packed = Vec::new();
        let mut tables: Vec<u8> = Vec::new();
        let mut kept = Vec::new();
        for &p in primes {
            if p < 3 {
                continue;
            }
            let modulus = BigInt::from(p);
            let mut coefficient = [0u32; 5];
            let mut all_zero = true;
            for (slot, c) in coefficient.iter_mut().zip(quartic.coefficient.iter()) {
                let mut residue = c % &modulus;
                if residue.is_negative() {
                    residue += &modulus;
                }
                let value: u64 = residue.try_into().unwrap_or(0);
                *slot = value as u32;
                if *slot != 0 {
                    all_zero = false;
                }
            }
            if all_zero {
                continue;
            }
            let offset = tables.len() as u32;
            let mut table = vec![0u8; p as usize];
            table[0] = 1;
            for x in 1..=p / 2 {
                table[((x * x) % p) as usize] = 1;
            }
            tables.extend_from_slice(&table);
            packed.push(PackedReceiver {
                prime: p as u32,
                table_offset: offset,
                coefficient,
            });
            kept.push(p as u32);
        }
        Self {
            packed,
            tables,
            primes: kept,
        }
    }

    pub fn primes(&self) -> &[u32] {
        &self.primes
    }

    /// The refusal density the family can reach: one over two to the number of receivers. A
    /// survivor population much larger than the examined count divided by this is a defect in the
    /// tables, not a discovery.
    pub fn receiver_count(&self) -> usize {
        self.packed.len()
    }
}

/// What one resident sweep returned, with its aperture attached.
#[derive(Debug, Clone)]
pub struct SearchReturn {
    /// Pairs `(n, d)` no receiver refused. Not yet points: the exact square test is separate.
    pub survivors: Vec<(i64, i64)>,
    /// How many `(n, d)` the card actually examined.
    pub pairs_examined: u128,
    /// The prime family that did the refusing.
    pub receivers: Vec<u32>,
}

/// The mounted search. One context, one module, held across sweeps so a sectioned search does not
/// pay context creation per section.
pub struct ResidentRealizerSearch {
    context: CuContext,
    module: CuModule,
    rational: CuFunction,
    integral: CuFunction,
    wheel: CuFunction,
    surface: CuFunction,
    block: u32,
    max_grid: u32,
}

const DEVICE_MAX_GRID_DIM_X: i32 = 5;

impl ResidentRealizerSearch {
    pub fn mount() -> Result<Self, RealizerSearchError> {
        // SAFETY: the CUDA driver API is called in its documented order and every handle is
        // released on the failure path before the error leaves.
        unsafe {
            driver(cuInit(0), "cuInit")?;
            let mut count = 0i32;
            driver(cuDeviceGetCount(&mut count), "cuDeviceGetCount")?;
            if count <= 0 {
                return Err(RealizerSearchError::NoDevice);
            }
            let mut device = 0;
            driver(cuDeviceGet(&mut device, 0), "cuDeviceGet")?;
            let mut threads = 0i32;
            driver(
                cuDeviceGetAttribute(&mut threads, DEVICE_MAX_THREADS_PER_BLOCK, device),
                "cuDeviceGetAttribute(MAX_THREADS_PER_BLOCK)",
            )?;
            let mut warp = 0i32;
            driver(
                cuDeviceGetAttribute(&mut warp, DEVICE_WARP_SIZE, device),
                "cuDeviceGetAttribute(WARP_SIZE)",
            )?;
            let mut grid = 0i32;
            driver(
                cuDeviceGetAttribute(&mut grid, DEVICE_MAX_GRID_DIM_X, device),
                "cuDeviceGetAttribute(MAX_GRID_DIM_X)",
            )?;
            let warp = warp.max(1) as u32;
            let block = (threads.max(32) as u32 / warp).max(1) * warp;
            let mut context = ptr::null_mut();
            driver(cuCtxCreate_v2(&mut context, 0, device), "cuCtxCreate_v2")?;
            let mut image = PTX.to_vec();
            if !image.ends_with(&[0]) {
                image.push(0);
            }
            let mut module = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleLoadData(&mut module, image.as_ptr().cast()),
                "cuModuleLoadData",
            ) {
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut rational = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(&mut rational, module, c"quartic_realizer_refusal".as_ptr()),
                "cuModuleGetFunction(quartic_realizer_refusal)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut integral = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut integral,
                    module,
                    c"quartic_realizer_refusal_integral".as_ptr(),
                ),
                "cuModuleGetFunction(quartic_realizer_refusal_integral)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut wheel = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(&mut wheel, module, c"specialization_wheel_traces".as_ptr()),
                "cuModuleGetFunction(specialization_wheel_traces)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut surface = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(&mut surface, module, c"surface_realizer_refusal".as_ptr()),
                "cuModuleGetFunction(surface_realizer_refusal)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            Ok(Self {
                context,
                module,
                rational,
                integral,
                wheel,
                surface,
                block: block.min(256),
                max_grid: grid.max(1) as u32,
            })
        }
    }

    /// Sweep `d ∈ [denominator_low, denominator_low + denominator_count)` against
    /// `n ∈ [numerator_low, numerator_low + numerator_count)`.
    pub fn sweep_rational(
        &self,
        family: &ReceiverFamily,
        denominator_low: i64,
        denominator_count: i64,
        numerator_low: i64,
        numerator_count: i64,
        capacity: u32,
    ) -> Result<SearchReturn, RealizerSearchError> {
        self.sweep(
            family,
            Some((denominator_low, denominator_count)),
            numerator_low,
            numerator_count,
            capacity,
        )
    }

    /// The `d = 1` face, where the window is one dimensional and can run far.
    pub fn sweep_integral(
        &self,
        family: &ReceiverFamily,
        numerator_low: i64,
        numerator_count: i64,
        capacity: u32,
    ) -> Result<SearchReturn, RealizerSearchError> {
        self.sweep(family, None, numerator_low, numerator_count, capacity)
    }

    fn sweep(
        &self,
        family: &ReceiverFamily,
        denominators: Option<(i64, i64)>,
        numerator_low: i64,
        numerator_count: i64,
        capacity: u32,
    ) -> Result<SearchReturn, RealizerSearchError> {
        let receiver_count = family.packed.len() as u32;
        // SAFETY: every allocation below is freed on both paths; the kernel parameter block matches
        // the kernel signature declared in kernels/exact_quartic_realizers.cu.
        unsafe {
            let receiver_bytes = std::mem::size_of_val(family.packed.as_slice());
            let mut receiver_device: CuDevicePtr = 0;
            driver(
                cuMemAlloc_v2(&mut receiver_device, receiver_bytes.max(1)),
                "cuMemAlloc_v2(receivers)",
            )?;
            let mut table_device: CuDevicePtr = 0;
            let mut survivor_device: CuDevicePtr = 0;
            let mut counter_device: CuDevicePtr = 0;
            if let Err(e) = driver(
                cuMemAlloc_v2(&mut table_device, family.tables.len().max(1)),
                "cuMemAlloc_v2(tables)",
            ) {
                release([receiver_device, 0, 0, 0]);
                return Err(e);
            }
            if let Err(e) = driver(
                cuMemAlloc_v2(
                    &mut survivor_device,
                    (capacity as usize * 2 * std::mem::size_of::<i64>()).max(1),
                ),
                "cuMemAlloc_v2(survivors)",
            ) {
                release([receiver_device, table_device, 0, 0]);
                return Err(e);
            }
            if let Err(e) = driver(
                cuMemAlloc_v2(&mut counter_device, 4),
                "cuMemAlloc_v2(counter)",
            ) {
                release([receiver_device, table_device, survivor_device, 0]);
                return Err(e);
            }
            macro_rules! guarded {
                ($expr:expr) => {
                    if let Err(e) = $expr {
                        release([
                            receiver_device,
                            table_device,
                            survivor_device,
                            counter_device,
                        ]);
                        return Err(e);
                    }
                };
            }
            guarded!(driver(
                cuMemcpyHtoD_v2(
                    receiver_device,
                    family.packed.as_ptr().cast(),
                    receiver_bytes,
                ),
                "cuMemcpyHtoD_v2(receivers)",
            ));
            guarded!(driver(
                cuMemcpyHtoD_v2(
                    table_device,
                    family.tables.as_ptr().cast(),
                    family.tables.len(),
                ),
                "cuMemcpyHtoD_v2(tables)",
            ));
            guarded!(driver(
                cuMemsetD8_v2(counter_device, 0, 4),
                "cuMemsetD8_v2(counter)",
            ));

            let blocks_x = ((numerator_count as u64 + self.block as u64 - 1) / self.block as u64)
                .min(self.max_grid as u64)
                .max(1) as u32;
            let mut numerator_low_value = numerator_low;
            let mut numerator_count_value = numerator_count;
            let mut capacity_value = capacity;
            let mut receiver_count_value = receiver_count;

            let launch = match denominators {
                Some((low, count)) => {
                    let mut low_value = low;
                    let mut count_value = count;
                    let mut parameters: [*mut c_void; 10] = [
                        (&mut receiver_device as *mut CuDevicePtr).cast(),
                        (&mut receiver_count_value as *mut u32).cast(),
                        (&mut table_device as *mut CuDevicePtr).cast(),
                        (&mut low_value as *mut i64).cast(),
                        (&mut count_value as *mut i64).cast(),
                        (&mut numerator_low_value as *mut i64).cast(),
                        (&mut numerator_count_value as *mut i64).cast(),
                        (&mut survivor_device as *mut CuDevicePtr).cast(),
                        (&mut counter_device as *mut CuDevicePtr).cast(),
                        (&mut capacity_value as *mut u32).cast(),
                    ];
                    driver(
                        cuLaunchKernel(
                            self.rational,
                            blocks_x,
                            count as u32,
                            1,
                            self.block,
                            1,
                            1,
                            0,
                            ptr::null_mut(),
                            parameters.as_mut_ptr(),
                            ptr::null_mut(),
                        ),
                        "cuLaunchKernel(quartic_realizer_refusal)",
                    )
                }
                None => {
                    let mut parameters: [*mut c_void; 8] = [
                        (&mut receiver_device as *mut CuDevicePtr).cast(),
                        (&mut receiver_count_value as *mut u32).cast(),
                        (&mut table_device as *mut CuDevicePtr).cast(),
                        (&mut numerator_low_value as *mut i64).cast(),
                        (&mut numerator_count_value as *mut i64).cast(),
                        (&mut survivor_device as *mut CuDevicePtr).cast(),
                        (&mut counter_device as *mut CuDevicePtr).cast(),
                        (&mut capacity_value as *mut u32).cast(),
                    ];
                    driver(
                        cuLaunchKernel(
                            self.integral,
                            blocks_x,
                            1,
                            1,
                            self.block,
                            1,
                            1,
                            0,
                            ptr::null_mut(),
                            parameters.as_mut_ptr(),
                            ptr::null_mut(),
                        ),
                        "cuLaunchKernel(quartic_realizer_refusal_integral)",
                    )
                }
            };
            guarded!(launch);
            guarded!(driver(cuCtxSynchronize(), "cuCtxSynchronize"));

            let mut seen: u32 = 0;
            guarded!(driver(
                cuMemcpyDtoH_v2(
                    (&mut seen as *mut u32).cast(),
                    counter_device,
                    std::mem::size_of::<u32>(),
                ),
                "cuMemcpyDtoH_v2(counter)",
            ));
            if seen > capacity {
                release([
                    receiver_device,
                    table_device,
                    survivor_device,
                    counter_device,
                ]);
                return Err(RealizerSearchError::SurvivorOverflow { seen, capacity });
            }
            let mut raw = vec![0i64; seen as usize * 2];
            if seen > 0 {
                guarded!(driver(
                    cuMemcpyDtoH_v2(
                        raw.as_mut_ptr().cast(),
                        survivor_device,
                        std::mem::size_of_val(raw.as_slice()),
                    ),
                    "cuMemcpyDtoH_v2(survivors)",
                ));
            }
            release([
                receiver_device,
                table_device,
                survivor_device,
                counter_device,
            ]);
            let survivors = raw.chunks_exact(2).map(|pair| (pair[0], pair[1])).collect();
            let denominator_count = denominators.map(|(_, c)| c as u128).unwrap_or(1);
            Ok(SearchReturn {
                survivors,
                pairs_examined: denominator_count * numerator_count as u128,
                receivers: family.primes.clone(),
            })
        }
    }
}

impl Drop for ResidentRealizerSearch {
    fn drop(&mut self) {
        // SAFETY: both handles were produced by this type and are released once.
        unsafe {
            let _ = cuModuleUnload(self.module);
            let _ = cuCtxDestroy_v2(self.context);
        }
    }
}

/// `Q(n, d) = c4 n^4 + c3 n^3 d + c2 n^2 d^2 + c1 n d^3 + c0 d^4`, exactly.
pub fn homogeneous_value(quartic: &IntegralQuartic, n: &BigInt, d: &BigInt) -> BigInt {
    let n2 = n * n;
    let n3 = &n2 * n;
    let n4 = &n3 * n;
    let d2 = d * d;
    let d3 = &d2 * d;
    let d4 = &d3 * d;
    &quartic.coefficient[4] * n4
        + &quartic.coefficient[3] * n3 * d
        + &quartic.coefficient[2] * n2 * d2
        + &quartic.coefficient[1] * n * d3
        + &quartic.coefficient[0] * d4
}

/// The exact square test the card is not asked to do. Returns the non-negative square root when
/// the value is a square, and nothing otherwise.
pub fn exact_square_root(value: &BigInt) -> Option<BigInt> {
    if value.is_negative() {
        return None;
    }
    if value.is_zero() {
        return Some(BigInt::zero());
    }
    let root = value.sqrt();
    if &root * &root == *value {
        Some(root)
    } else {
        None
    }
}

/// One receiver's contribution to a wheel build: its prime, the five coefficient polynomials
/// already reduced there, and its residue-sign table.
#[derive(Debug, Clone)]
pub struct WheelReceiver {
    pub prime: u32,
    /// Five runs of `degree + 1` coefficients, ascending, concatenated.
    pub polynomials: Vec<u32>,
    pub degree: u32,
    pub signs: Vec<i8>,
}

impl ResidentRealizerSearch {
    /// Compute `a_p` for every residue class of every receiver.
    ///
    /// The work is `Σ p^2` and every cell is independent, so this is the part of the wheel that
    /// belongs on the card. The card returns integer traces; the host alone decides what receiver
    /// quotient to read off them.
    pub fn wheel_traces(
        &self,
        receivers: &[WheelReceiver],
    ) -> Result<Vec<i32>, RealizerSearchError> {
        if receivers.is_empty() {
            return Ok(Vec::new());
        }
        let degree = receivers[0].degree;
        let mut primes = Vec::with_capacity(receivers.len());
        let mut cell_offsets = Vec::with_capacity(receivers.len());
        let mut polynomial_offsets = Vec::with_capacity(receivers.len());
        let mut degrees = Vec::with_capacity(receivers.len());
        let mut polynomials: Vec<u32> = Vec::new();
        let mut signs: Vec<i8> = Vec::new();
        for receiver in receivers {
            primes.push(receiver.prime);
            cell_offsets.push(signs.len() as u32);
            polynomial_offsets.push(polynomials.len() as u32);
            degrees.push(receiver.degree);
            polynomials.extend_from_slice(&receiver.polynomials);
            signs.extend_from_slice(&receiver.signs);
        }
        let cells = signs.len();
        let widest = primes.iter().copied().max().unwrap_or(1);
        let _ = degree;

        // SAFETY: every allocation is freed before return on both paths, and the parameter block
        // matches `specialization_wheel_traces` in kernels/exact_quartic_realizers.cu.
        unsafe {
            let mut buffers: Vec<CuDevicePtr> = vec![0; 7];
            let sizes = [
                std::mem::size_of_val(primes.as_slice()),
                std::mem::size_of_val(cell_offsets.as_slice()),
                std::mem::size_of_val(polynomial_offsets.as_slice()),
                std::mem::size_of_val(degrees.as_slice()),
                std::mem::size_of_val(polynomials.as_slice()),
                std::mem::size_of_val(signs.as_slice()),
                cells * std::mem::size_of::<i32>(),
            ];
            for (slot, bytes) in buffers.iter_mut().zip(sizes.iter()) {
                if let Err(e) = driver(cuMemAlloc_v2(slot, (*bytes).max(1)), "cuMemAlloc_v2(wheel)")
                {
                    for pointer in buffers.iter() {
                        if *pointer != 0 {
                            let _ = cuMemFree_v2(*pointer);
                        }
                    }
                    return Err(e);
                }
            }
            let hosts: [*const c_void; 6] = [
                primes.as_ptr().cast(),
                cell_offsets.as_ptr().cast(),
                polynomial_offsets.as_ptr().cast(),
                degrees.as_ptr().cast(),
                polynomials.as_ptr().cast(),
                signs.as_ptr().cast(),
            ];
            let mut failure = None;
            for index in 0..6 {
                if let Err(e) = driver(
                    cuMemcpyHtoD_v2(buffers[index], hosts[index], sizes[index].max(1)),
                    "cuMemcpyHtoD_v2(wheel)",
                ) {
                    failure = Some(e);
                    break;
                }
            }
            if failure.is_none() {
                let mut receiver_count = receivers.len() as u32;
                let mut parameters: [*mut c_void; 8] = [
                    (&mut buffers[0] as *mut CuDevicePtr).cast(),
                    (&mut buffers[1] as *mut CuDevicePtr).cast(),
                    (&mut buffers[2] as *mut CuDevicePtr).cast(),
                    (&mut buffers[3] as *mut CuDevicePtr).cast(),
                    (&mut buffers[4] as *mut CuDevicePtr).cast(),
                    (&mut buffers[5] as *mut CuDevicePtr).cast(),
                    (&mut receiver_count as *mut u32).cast(),
                    (&mut buffers[6] as *mut CuDevicePtr).cast(),
                ];
                let blocks_x = ((widest + self.block - 1) / self.block).clamp(1, self.max_grid);
                failure = driver(
                    cuLaunchKernel(
                        self.wheel,
                        blocks_x,
                        receivers.len() as u32,
                        1,
                        self.block,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        parameters.as_mut_ptr(),
                        ptr::null_mut(),
                    ),
                    "cuLaunchKernel(specialization_wheel_traces)",
                )
                .err()
                .or_else(|| driver(cuCtxSynchronize(), "cuCtxSynchronize").err());
            }
            let mut traces = vec![0i32; cells];
            if failure.is_none() {
                failure = driver(
                    cuMemcpyDtoH_v2(
                        traces.as_mut_ptr().cast(),
                        buffers[6],
                        std::mem::size_of_val(traces.as_slice()),
                    ),
                    "cuMemcpyDtoH_v2(traces)",
                )
                .err();
            }
            for pointer in buffers.iter() {
                if *pointer != 0 {
                    let _ = cuMemFree_v2(*pointer);
                }
            }
            match failure {
                Some(e) => Err(e),
                None => Ok(traces),
            }
        }
    }
}

/// What one surface sweep returned: realizer candidates addressed by the fibre they fell into.
#[derive(Debug, Clone)]
pub struct SurfaceReturn {
    /// Pairs `(x, T)`. Not yet realizers: the exact square test is the caller's.
    pub survivors: Vec<(i64, i64)>,
    pub pairs_examined: u128,
    pub receivers: Vec<u32>,
}

impl ResidentRealizerSearch {
    /// Sweep the surface `y^2 = r(x, T)` over a box of fibres and abscissae in one launch.
    ///
    /// This is the deed the fibration exists for: the family is one body, and the population that
    /// decides a fibre's rank is measured by partitioning the surface's own realizers, not by
    /// scoring the fibre and searching it afterwards.
    pub fn sweep_surface(
        &self,
        prepared: &[WheelReceiver],
        fibre_low: i64,
        fibre_count: i64,
        abscissa_low: i64,
        abscissa_count: i64,
        capacity: u32,
    ) -> Result<SurfaceReturn, RealizerSearchError> {
        if prepared.is_empty() || fibre_count <= 0 || abscissa_count <= 0 {
            return Ok(SurfaceReturn {
                survivors: Vec::new(),
                pairs_examined: 0,
                receivers: Vec::new(),
            });
        }
        let degree = prepared[0].degree;
        let mut primes = Vec::new();
        let mut table_offsets = Vec::new();
        let mut polynomial_offsets = Vec::new();
        let mut polynomials: Vec<u32> = Vec::new();
        let mut tables: Vec<u8> = Vec::new();
        for receiver in prepared {
            primes.push(receiver.prime);
            table_offsets.push(tables.len() as u32);
            polynomial_offsets.push(polynomials.len() as u32);
            polynomials.extend_from_slice(&receiver.polynomials);
            // the refusal table: 1 where the residue is a square or zero
            tables.extend(receiver.signs.iter().map(|s| u8::from(*s >= 0)));
        }

        // SAFETY: allocations are released on both paths; the parameter block matches
        // `surface_realizer_refusal` in kernels/exact_quartic_realizers.cu.
        unsafe {
            let mut buffers: Vec<CuDevicePtr> = vec![0; 7];
            let sizes = [
                std::mem::size_of_val(primes.as_slice()),
                std::mem::size_of_val(table_offsets.as_slice()),
                std::mem::size_of_val(polynomial_offsets.as_slice()),
                std::mem::size_of_val(polynomials.as_slice()),
                std::mem::size_of_val(tables.as_slice()),
                capacity as usize * 2 * std::mem::size_of::<i64>(),
                std::mem::size_of::<u32>(),
            ];
            for (slot, bytes) in buffers.iter_mut().zip(sizes.iter()) {
                if let Err(e) = driver(
                    cuMemAlloc_v2(slot, (*bytes).max(1)),
                    "cuMemAlloc_v2(surface)",
                ) {
                    for pointer in buffers.iter() {
                        if *pointer != 0 {
                            let _ = cuMemFree_v2(*pointer);
                        }
                    }
                    return Err(e);
                }
            }
            let hosts: [*const c_void; 5] = [
                primes.as_ptr().cast(),
                table_offsets.as_ptr().cast(),
                polynomial_offsets.as_ptr().cast(),
                polynomials.as_ptr().cast(),
                tables.as_ptr().cast(),
            ];
            let mut failure = None;
            for index in 0..5 {
                if let Err(e) = driver(
                    cuMemcpyHtoD_v2(buffers[index], hosts[index], sizes[index].max(1)),
                    "cuMemcpyHtoD_v2(surface)",
                ) {
                    failure = Some(e);
                    break;
                }
            }
            if failure.is_none() {
                failure = driver(cuMemsetD8_v2(buffers[6], 0, 4), "cuMemsetD8_v2(counter)").err();
            }
            if failure.is_none() {
                let mut receiver_count = prepared.len() as u32;
                let mut degree_value = degree;
                let mut fibre_low_value = fibre_low;
                let mut fibre_count_value = fibre_count;
                let mut abscissa_low_value = abscissa_low;
                let mut abscissa_count_value = abscissa_count;
                let mut capacity_value = capacity;
                let parameters: [*mut c_void; 13] = [
                    (&mut buffers[0] as *mut CuDevicePtr).cast(),
                    (&mut buffers[1] as *mut CuDevicePtr).cast(),
                    (&mut buffers[2] as *mut CuDevicePtr).cast(),
                    (&mut degree_value as *mut u32).cast(),
                    (&mut buffers[3] as *mut CuDevicePtr).cast(),
                    (&mut buffers[4] as *mut CuDevicePtr).cast(),
                    (&mut receiver_count as *mut u32).cast(),
                    (&mut fibre_low_value as *mut i64).cast(),
                    (&mut fibre_count_value as *mut i64).cast(),
                    (&mut abscissa_low_value as *mut i64).cast(),
                    (&mut abscissa_count_value as *mut i64).cast(),
                    (&mut buffers[5] as *mut CuDevicePtr).cast(),
                    (&mut buffers[6] as *mut CuDevicePtr).cast(),
                ];
                // the capacity is the fourteenth argument; CUDA takes the block as one array
                let mut all: Vec<*mut c_void> = parameters.to_vec();
                all.push((&mut capacity_value as *mut u32).cast());
                let blocks_x = (((abscissa_count as u64 + self.block as u64 - 1)
                    / self.block as u64)
                    .min(self.max_grid as u64)
                    .max(1)) as u32;
                failure = driver(
                    cuLaunchKernel(
                        self.surface,
                        blocks_x,
                        fibre_count as u32,
                        1,
                        self.block,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        all.as_mut_ptr(),
                        ptr::null_mut(),
                    ),
                    "cuLaunchKernel(surface_realizer_refusal)",
                )
                .err()
                .or_else(|| driver(cuCtxSynchronize(), "cuCtxSynchronize").err());
            }
            let mut seen: u32 = 0;
            if failure.is_none() {
                failure = driver(
                    cuMemcpyDtoH_v2(
                        (&mut seen as *mut u32).cast(),
                        buffers[6],
                        std::mem::size_of::<u32>(),
                    ),
                    "cuMemcpyDtoH_v2(counter)",
                )
                .err();
            }
            let mut raw = Vec::new();
            if failure.is_none() {
                if seen > capacity {
                    failure = Some(RealizerSearchError::SurvivorOverflow { seen, capacity });
                } else if seen > 0 {
                    raw = vec![0i64; seen as usize * 2];
                    failure = driver(
                        cuMemcpyDtoH_v2(
                            raw.as_mut_ptr().cast(),
                            buffers[5],
                            std::mem::size_of_val(raw.as_slice()),
                        ),
                        "cuMemcpyDtoH_v2(survivors)",
                    )
                    .err();
                }
            }
            for pointer in buffers.iter() {
                if *pointer != 0 {
                    let _ = cuMemFree_v2(*pointer);
                }
            }
            match failure {
                Some(e) => Err(e),
                None => Ok(SurfaceReturn {
                    survivors: raw.chunks_exact(2).map(|p| (p[0], p[1])).collect(),
                    pairs_examined: fibre_count as u128 * abscissa_count as u128,
                    receivers: primes,
                }),
            }
        }
    }
}
