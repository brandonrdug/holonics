//! Hand-written minimal bindings to libcuda (the CUDA Driver API). No external crates.
//! The whole unsafe surface lives here; `cuda.rs` builds the safe typed layer above it.
//!
//! We bind the `_v2` ABI entry names directly (the driver headers `#define` the plain names
//! onto these). `CUresult` is carried as a raw `i32`; `CUDA_SUCCESS == 0`.
#![allow(non_camel_case_types, non_snake_case)]

use core::ffi::{c_char, c_int, c_uint, c_void};

/// Opaque driver handles.
pub type CUdevice = c_int;
pub type CUdeviceptr = u64;
pub type CUcontext = *mut c_void;
pub type CUmodule = *mut c_void;
pub type CUfunction = *mut c_void;
pub type CUstream = *mut c_void;
pub type CUmemGenericAllocationHandle = u64;

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct CUmemLocation {
    pub location_type: c_int,
    pub id: c_int,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct CUmemAllocationFlags {
    pub compression_type: u8,
    pub gpu_direct_rdma_capable: u8,
    pub usage: u16,
    pub reserved: [u8; 4],
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct CUmemAllocationProp {
    pub allocation_type: c_int,
    pub requested_handle_types: c_int,
    pub location: CUmemLocation,
    pub win32_handle_metadata: *mut c_void,
    pub allocation_flags: CUmemAllocationFlags,
}

impl Default for CUmemAllocationProp {
    fn default() -> Self {
        Self {
            allocation_type: 0,
            requested_handle_types: 0,
            location: CUmemLocation::default(),
            win32_handle_metadata: core::ptr::null_mut(),
            allocation_flags: CUmemAllocationFlags::default(),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct CUmemAccessDesc {
    pub location: CUmemLocation,
    pub flags: c_uint,
}

/// The driver result code. 0 is success; every other value names a fault.
pub type CUresult = c_int;
pub const CUDA_SUCCESS: CUresult = 0;

#[link(name = "cuda")]
extern "C" {
    pub fn cuInit(flags: c_uint) -> CUresult;

    pub fn cuDeviceGetCount(count: *mut c_int) -> CUresult;
    pub fn cuDeviceGet(device: *mut CUdevice, ordinal: c_int) -> CUresult;
    pub fn cuDeviceGetName(name: *mut c_char, len: c_int, dev: CUdevice) -> CUresult;

    pub fn cuCtxCreate_v2(pctx: *mut CUcontext, flags: c_uint, dev: CUdevice) -> CUresult;
    pub fn cuCtxSetCurrent(ctx: CUcontext) -> CUresult;
    pub fn cuCtxDestroy_v2(ctx: CUcontext) -> CUresult;
    pub fn cuCtxSynchronize() -> CUresult;
    pub fn cuCtxGetLimit(pvalue: *mut usize, limit: c_int) -> CUresult;
    pub fn cuCtxSetLimit(limit: c_int, value: usize) -> CUresult;

    pub fn cuStreamCreate(stream: *mut CUstream, flags: c_uint) -> CUresult;
    pub fn cuStreamDestroy_v2(stream: CUstream) -> CUresult;
    pub fn cuStreamSynchronize(stream: CUstream) -> CUresult;

    pub fn cuModuleLoadData(module: *mut CUmodule, image: *const c_void) -> CUresult;
    pub fn cuModuleUnload(module: CUmodule) -> CUresult;
    pub fn cuModuleGetFunction(
        func: *mut CUfunction,
        module: CUmodule,
        name: *const c_char,
    ) -> CUresult;

    pub fn cuMemAlloc_v2(dptr: *mut CUdeviceptr, bytesize: usize) -> CUresult;
    pub fn cuMemFree_v2(dptr: CUdeviceptr) -> CUresult;
    pub fn cuMemAddressReserve(
        ptr: *mut CUdeviceptr,
        size: usize,
        alignment: usize,
        address: CUdeviceptr,
        flags: u64,
    ) -> CUresult;
    pub fn cuMemAddressFree(ptr: CUdeviceptr, size: usize) -> CUresult;
    pub fn cuMemCreate(
        handle: *mut CUmemGenericAllocationHandle,
        size: usize,
        properties: *const CUmemAllocationProp,
        flags: u64,
    ) -> CUresult;
    pub fn cuMemRelease(handle: CUmemGenericAllocationHandle) -> CUresult;
    pub fn cuMemMap(
        ptr: CUdeviceptr,
        size: usize,
        offset: usize,
        handle: CUmemGenericAllocationHandle,
        flags: u64,
    ) -> CUresult;
    pub fn cuMemUnmap(ptr: CUdeviceptr, size: usize) -> CUresult;
    pub fn cuMemSetAccess(
        ptr: CUdeviceptr,
        size: usize,
        descriptors: *const CUmemAccessDesc,
        count: usize,
    ) -> CUresult;
    pub fn cuMemGetAllocationGranularity(
        granularity: *mut usize,
        properties: *const CUmemAllocationProp,
        option: c_uint,
    ) -> CUresult;
    pub fn cuMemcpyHtoD_v2(dst: CUdeviceptr, src: *const c_void, bytes: usize) -> CUresult;
    pub fn cuMemcpyDtoH_v2(dst: *mut c_void, src: CUdeviceptr, bytes: usize) -> CUresult;
    pub fn cuMemcpyDtoD_v2(dst: CUdeviceptr, src: CUdeviceptr, bytes: usize) -> CUresult;

    pub fn cuLaunchKernel(
        f: CUfunction,
        gridDimX: c_uint,
        gridDimY: c_uint,
        gridDimZ: c_uint,
        blockDimX: c_uint,
        blockDimY: c_uint,
        blockDimZ: c_uint,
        sharedMemBytes: c_uint,
        stream: CUstream,
        kernelParams: *mut *mut c_void,
        extra: *mut *mut c_void,
    ) -> CUresult;

    pub fn cuGetErrorName(err: CUresult, pStr: *mut *const c_char) -> CUresult;
    pub fn cuGetErrorString(err: CUresult, pStr: *mut *const c_char) -> CUresult;
}
