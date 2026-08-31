//! The eta boundary on the card: the `O(N)` head of every boundary jet at once, the certification
//! law and the winding on the CPU.
//!
//! [`relational_geometry::eta_boundary_winding`] certifies a receiver box by walking its boundary,
//! evaluating the eta jet at every segment midpoint, and subdividing until every segment's image
//! excludes the origin; the polygon of the images then winds, and the winding is the zero count.
//! With the Euler--Maclaurin start derived from the height that evaluation is `O(tau)` series per
//! point, and the walk is depth-first, so every point pays serially. Measured 2026-08-27: ten
//! milliseconds per `(point, term)`, a zero-bearing band at height sixty not closing under the
//! process aperture.
//!
//! This owner keeps the law and moves the population. The head `sum_(n<N) n^(-s)` and its
//! derivative are formed for **every pending midpoint of one depth** in one launch of
//! `kernels/exact_eta_head.cu`, in exact fixed-point interval arithmetic at ninety-six fractional
//! bits; the tail, the corrections, the certified remainder, the `eta` factor, the transport disc
//! and the winding are the serial owner's own functions, called with the head supplied. The
//! certification walk is breadth-first — one launch per depth rather than one evaluation per
//! segment — and the segments are flattened back into boundary order before the polygon is read,
//! so the returned [`WindingReceipt`] has the same shape as the serial one and verifies under the
//! same law.
//!
//! **What the card testifies to and what it does not.** The card returns enclosures. They are
//! sets, and the CPU widens them further; a card enclosure and a serial enclosure of the same
//! point must intersect, and the driver checks that they do. Nothing semantic is decided on the
//! card: no subdivision, no winding, no start.

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::{
    ComplexInterval, ComplexReceiverBox, ExactAnalysisError, ExactSeriesConfig, HeadJet,
    HeadSource, Rat, RatInterval, log_integer_interval,
};
use std::ffi::{CStr, c_char, c_void};
use std::ptr;
use std::time::Instant;

const CUDA_SUCCESS: i32 = 0;
const FRAC: u32 = 96;
const BLOCK: u32 = 128;

const PTX: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/exact_eta_head.ptx"));

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

#[derive(Debug)]
pub enum EtaHeadError {
    NoDevice,
    Driver {
        operation: &'static str,
        code: i32,
        name: String,
        message: String,
    },
    /// A coordinate did not fit the card's fixed-point carrier: thirty-one integer bits.
    CarrierOverflow,
    Analysis(ExactAnalysisError),
}

impl std::fmt::Display for EtaHeadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoDevice => write!(f, "no CUDA device answered"),
            Self::Driver {
                operation,
                code,
                name,
                message,
            } => write!(f, "{operation} failed: {name} ({code}): {message}"),
            Self::CarrierOverflow => write!(f, "a coordinate exceeded the Q31.96 carrier"),
            Self::Analysis(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for EtaHeadError {}

impl From<ExactAnalysisError> for EtaHeadError {
    fn from(error: ExactAnalysisError) -> Self {
        Self::Analysis(error)
    }
}

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

fn driver(code: i32, operation: &'static str) -> Result<(), EtaHeadError> {
    if code == CUDA_SUCCESS {
        Ok(())
    } else {
        Err(EtaHeadError::Driver {
            operation,
            code,
            name: driver_text(cuGetErrorName, code),
            message: driver_text(cuGetErrorString, code),
        })
    }
}

// --- the Q31.96 codec: exact in both directions ---------------------------------------------

fn floor_div(numerator: &BigInt, denominator: &BigInt) -> BigInt {
    let quotient = numerator / denominator;
    let remainder = numerator - &quotient * denominator;
    if !remainder.is_zero() && (remainder.is_negative() != denominator.is_negative()) {
        quotient - BigInt::one()
    } else {
        quotient
    }
}

fn fixed_floor(value: &Rat) -> Result<i128, EtaHeadError> {
    let scaled = value.numer() << FRAC;
    floor_div(&scaled, value.denom())
        .to_i128()
        .filter(|v| v.unsigned_abs() < (1u128 << 127))
        .ok_or(EtaHeadError::CarrierOverflow)
}

fn fixed_ceil(value: &Rat) -> Result<i128, EtaHeadError> {
    Ok(-fixed_floor(&(-value.clone()))?)
}

fn from_fixed(value: i128) -> Rat {
    Rat::new(BigInt::from(value), BigInt::one() << FRAC)
}

/// The mounted head evaluator: one context, one module, and the logarithm table of the widest
/// start seen so far, kept resident because it is receiver-independent.
pub struct ResidentEtaHead {
    context: CuContext,
    module: CuModule,
    function: CuFunction,
    logs_device: CuDevicePtr,
    logs_host: Vec<i128>,
    logs_start: u32,
    logs_key: (u32, u32),
    /// How many head launches this mount has performed, for the receipt.
    pub launches: u64,
    /// How many `(point, term)` lanes those launches covered.
    pub lanes: u128,
    /// Wall time spent between the first upload and the last read-back of each launch.
    pub device_seconds: f64,
}

impl ResidentEtaHead {
    pub fn mount() -> Result<Self, EtaHeadError> {
        // SAFETY: documented driver-API order; every handle released on the failure path.
        unsafe {
            driver(cuInit(0), "cuInit")?;
            let mut count = 0i32;
            driver(cuDeviceGetCount(&mut count), "cuDeviceGetCount")?;
            if count <= 0 {
                return Err(EtaHeadError::NoDevice);
            }
            let mut device = 0;
            driver(cuDeviceGet(&mut device, 0), "cuDeviceGet")?;
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
            let mut function = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(&mut function, module, c"eta_head_jets".as_ptr()),
                "cuModuleGetFunction(eta_head_jets)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            Ok(Self {
                context,
                module,
                function,
                logs_device: 0,
                logs_host: Vec::new(),
                logs_start: 0,
                logs_key: (0, 0),
                launches: 0,
                lanes: 0,
                device_seconds: 0.0,
            })
        }
    }

    fn ensure_logs(&mut self, config: &ExactSeriesConfig) -> Result<(), EtaHeadError> {
        let start = config.euler_maclaurin_start;
        let key = (config.log_terms, config.dyadic_bits);
        if self.logs_key != key {
            self.logs_host.clear();
            self.logs_start = 0;
            self.logs_key = key;
        }
        if self.logs_device != 0 && self.logs_start >= start {
            return Ok(());
        }
        // extend the host table from the memoized series; nothing already formed is re-summed
        let known = (self.logs_host.len() / 2) as u32 + 1;
        for base in known..start {
            let logarithm = log_integer_interval(base, config.log_terms, config.dyadic_bits)?;
            self.logs_host.push(fixed_floor(&logarithm.lower)?);
            self.logs_host.push(fixed_ceil(&logarithm.upper)?);
        }
        // SAFETY: the old table is freed before the pointer is overwritten; the new allocation is
        // sized to the table actually copied.
        unsafe {
            if self.logs_device != 0 {
                let _ = cuMemFree_v2(self.logs_device);
                self.logs_device = 0;
            }
            let bytes = std::mem::size_of_val(self.logs_host.as_slice()).max(16);
            let mut pointer: CuDevicePtr = 0;
            driver(cuMemAlloc_v2(&mut pointer, bytes), "cuMemAlloc_v2(logs)")?;
            if let Err(error) = driver(
                cuMemcpyHtoD_v2(
                    pointer,
                    self.logs_host.as_ptr().cast(),
                    bytes.min(self.logs_host.len() * 16),
                ),
                "cuMemcpyHtoD_v2(logs)",
            ) {
                let _ = cuMemFree_v2(pointer);
                return Err(error);
            }
            self.logs_device = pointer;
        }
        self.logs_start = start;
        Ok(())
    }

    /// The head jets of many receivers in one launch.
    pub fn head_jets(
        &mut self,
        receivers: &[ComplexReceiverBox],
        config: &ExactSeriesConfig,
    ) -> Result<Vec<HeadJet>, EtaHeadError> {
        if receivers.is_empty() {
            return Ok(Vec::new());
        }
        self.ensure_logs(config)?;
        let mut points: Vec<i128> = Vec::with_capacity(4 * receivers.len());
        for receiver in receivers {
            points.push(fixed_floor(&receiver.sigma.lower)?);
            points.push(fixed_ceil(&receiver.sigma.upper)?);
            points.push(fixed_floor(&receiver.tau.lower)?);
            points.push(fixed_ceil(&receiver.tau.upper)?);
        }
        let mut raw = vec![0i128; 12 * receivers.len()];
        let launched = Instant::now();
        // SAFETY: allocations sized to the slices copied; the parameter block matches the kernel
        // signature in kernels/exact_eta_head.cu; both allocations freed on every path.
        unsafe {
            let point_bytes = std::mem::size_of_val(points.as_slice());
            let out_bytes = std::mem::size_of_val(raw.as_slice());
            let mut points_device: CuDevicePtr = 0;
            driver(
                cuMemAlloc_v2(&mut points_device, point_bytes),
                "cuMemAlloc_v2(points)",
            )?;
            let mut out_device: CuDevicePtr = 0;
            if let Err(error) = driver(
                cuMemAlloc_v2(&mut out_device, out_bytes),
                "cuMemAlloc_v2(out)",
            ) {
                let _ = cuMemFree_v2(points_device);
                return Err(error);
            }
            let release = |a: CuDevicePtr, b: CuDevicePtr| {
                let _ = cuMemFree_v2(a);
                let _ = cuMemFree_v2(b);
            };
            macro_rules! guarded {
                ($expr:expr) => {
                    if let Err(error) = $expr {
                        release(points_device, out_device);
                        return Err(error);
                    }
                };
            }
            guarded!(driver(
                cuMemcpyHtoD_v2(points_device, points.as_ptr().cast(), point_bytes),
                "cuMemcpyHtoD_v2(points)",
            ));
            let mut point_count = receivers.len() as u32;
            let mut logs_device = self.logs_device;
            let mut start = config.euler_maclaurin_start;
            let mut exp_terms = config.exponential_terms;
            let mut trig_terms = config.trigonometric_terms;
            let mut parameters: [*mut c_void; 7] = [
                (&mut points_device as *mut CuDevicePtr).cast(),
                (&mut point_count as *mut u32).cast(),
                (&mut logs_device as *mut CuDevicePtr).cast(),
                (&mut start as *mut u32).cast(),
                (&mut exp_terms as *mut u32).cast(),
                (&mut trig_terms as *mut u32).cast(),
                (&mut out_device as *mut CuDevicePtr).cast(),
            ];
            guarded!(driver(
                cuLaunchKernel(
                    self.function,
                    point_count,
                    1,
                    1,
                    BLOCK,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    parameters.as_mut_ptr(),
                    ptr::null_mut(),
                ),
                "cuLaunchKernel(eta_head_jets)",
            ));
            guarded!(driver(cuCtxSynchronize(), "cuCtxSynchronize"));
            guarded!(driver(
                cuMemcpyDtoH_v2(raw.as_mut_ptr().cast(), out_device, out_bytes),
                "cuMemcpyDtoH_v2(out)",
            ));
            release(points_device, out_device);
        }
        self.device_seconds += launched.elapsed().as_secs_f64();
        self.launches += 1;
        self.lanes +=
            receivers.len() as u128 * (config.euler_maclaurin_start.saturating_sub(1)) as u128;
        let interval = |lo: i128, hi: i128| RatInterval::new(from_fixed(lo), from_fixed(hi));
        Ok(raw
            .chunks_exact(12)
            .map(|c| HeadJet {
                value: ComplexInterval::new(interval(c[0], c[1]), interval(c[2], c[3])),
                derivative: ComplexInterval::new(interval(c[4], c[5]), interval(c[6], c[7])),
                second: ComplexInterval::new(interval(c[8], c[9]), interval(c[10], c[11])),
            })
            .collect())
    }
}

impl HeadSource for ResidentEtaHead {
    fn heads(
        &mut self,
        receivers: &[ComplexReceiverBox],
        config: &ExactSeriesConfig,
    ) -> Result<Option<Vec<HeadJet>>, String> {
        self.head_jets(receivers, config)
            .map(Some)
            .map_err(|error| error.to_string())
    }

    fn apparatus(&self) -> String {
        "resident head on the card (kernels/exact_eta_head.cu, Q31.96 interval fixed point), serial tail".to_owned()
    }
}

impl Drop for ResidentEtaHead {
    fn drop(&mut self) {
        // SAFETY: handles produced by this type, released once.
        unsafe {
            if self.logs_device != 0 {
                let _ = cuMemFree_v2(self.logs_device);
            }
            let _ = cuModuleUnload(self.module);
            let _ = cuCtxDestroy_v2(self.context);
        }
    }
}
