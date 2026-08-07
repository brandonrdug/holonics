//! mount — CUDA Driver API boundary scaffolding for soma's headless production mount.
//!
//! Vulkan is convicted for production (headless Xid faults on the big genesis); the recut keeps the
//! law in Rust: `rustc` emits PTX for `nvptx64-nvidia-cuda`, and this crate loads/launches it over
//! the CUDA Driver API (libcuda). CUDA C is NOT selected. Nothing here is engine law — it is the
//! mount's boundary: a thin, safe wrapper and a smoke that proves the full path once.
//!
//! Layout: `ffi` holds the whole raw libcuda surface; `cuda` builds the safe typed layer
//! (`Device`, `Context`, `Module`, `Function`, `DeviceBuffer<T>`) with driver-named `Result`s.

pub mod cuda;
pub mod ffi;
pub mod live_event_launch;
pub mod register_carrier;
pub mod register_launch;
pub mod register_recast;

pub use cuda::{
    Context, CudaError, Device, DeviceBuffer, Dim3, Function, LinearLaunch, Module, Result, Stream,
    VirtualDeviceBuffer, VirtualDeviceGrowth,
};
pub use live_event_launch::{
    LiveEventArguments, LiveEventKernel, LiveEventSpan, RegionalContactArguments,
    RegionalContactKernel,
};
pub use register_carrier::{
    launch_register_carrier_rebase, RegisterCarrierRebase, RegisterCarrierRebaseOutput,
};
pub use register_launch::{
    RegisterCarrierRebaseArguments, RegisterCarrierRebaseKernel, RegisterRecastArguments,
    RegisterRecastFinishKernel, RegisterRecastKernel, RegisterScopeArguments, RegisterScopeKernel,
    RegisterScopeSurfaceArguments, RegisterScopeSurfaceKernel, RegisterSpan,
};
pub use register_recast::{
    launch_register_own_recast, RegisterOwnRecast, RegisterOwnRecastOutput, REGISTER_LANE_WORDS,
    REGISTER_RECAST_COMPLETE, REGISTER_RECAST_INCOMPLETE, REGISTER_STATUS_WORDS,
};

/// The committed CUDA spelling of soma's shared body and receiving entries. Production and gates
/// load the same bytes; rebuilding remains an explicit repository operation.
pub const SOMA_PTX: &[u8] = include_bytes!("../soma-kernel-cuda/soma_kernel_cuda.ptx");

/// The odd fold constant the `atomic_fold` kernel adds once per thread (mirrors the kernel's
/// `FOLD_CONSTANT`; kept here so the host's exact check needs no re-derivation). 2^61 - 1.
pub const FOLD_CONSTANT: u64 = 2_305_843_009_213_693_951;

#[cfg(test)]
mod tests {
    use super::SOMA_PTX;

    /// The committed PTX boundary artifact, checked host-side (no GPU) so the workspace test
    /// gates that the artifact is present, sm_89, and carries both entry points.
    const SMOKE_PTX: &[u8] = include_bytes!("../mount-smoke-kernel/mount_smoke_kernel.ptx");
    /// The CUDA smoke boundary. This check is deliberately static: it validates
    /// the committed artifact without loading a driver or rebuilding PTX behind the user's back.
    #[test]
    fn ptx_artifact_is_sm89_with_both_entries() {
        let text = std::str::from_utf8(SMOKE_PTX).expect("PTX is text");
        assert!(text.contains(".target sm_89"), "PTX must target sm_89");
        assert!(
            text.contains(".entry fill_identity"),
            "PTX must expose fill_identity"
        );
        assert!(
            text.contains(".entry atomic_fold"),
            "PTX must expose atomic_fold"
        );
        // The exact 64-bit atomic lowering the mount depends on.
        assert!(
            text.contains("atom.global.add.u64"),
            "expected atom.add.u64"
        );
        assert!(
            text.contains("atom.global.max.u64"),
            "expected atom.max.u64"
        );
    }

    #[test]
    fn soma_ptx_artifact_is_sm89_with_all_twenty_three_entries_and_required_atomics() {
        let text = std::str::from_utf8(SOMA_PTX).expect("the soma PTX artifact is text");
        assert!(text.contains(".target sm_89"), "soma PTX must target sm_89");
        for entry in [
            "link_grain",
            "link_sum",
            "link_finish",
            "link_founded_grain",
            "link_founded_sum",
            "link_register_grain",
            "link_register_sum",
            "link_register_finish",
            "chart_mark",
            "chart_register_mark",
            "chart_count",
            "chart_recast",
            "register_own_recast",
            "register_own_recast_finish",
            "register_carrier_rebase",
            "scope_felt",
            "scope_founded",
            "scope_register",
            "scope_register_surface",
            "regional_contacts",
            "lineage_event",
            "text_incidence_select",
            "text_section_restrict",
        ] {
            assert!(
                text.contains(&format!(".entry {entry}")),
                "soma PTX must expose {entry}"
            );
        }
        assert!(
            text.contains("atom.global.add.u64"),
            "soma PTX must carry the exact wide-hand add"
        );
        assert!(
            text.contains("atom.global.max.u64"),
            "soma PTX must carry the Cog-grain max"
        );
        assert!(
            text.contains("atom.global.max.u32"),
            "soma PTX must carry the touch/arm-grain max"
        );
        assert!(
            text.contains("bar.warp.sync \t32767"),
            "the fifteen-lane contact surface must carry its exact partial-warp barrier"
        );

        fn parameter_count(text: &str, entry: soma_abi::register::Entry) -> usize {
            let mouth = format!(".entry {}(", entry.symbol());
            let body = text
                .split_once(&mouth)
                .unwrap_or_else(|| panic!("PTX carries {}", entry.symbol()))
                .1;
            let signature = body
                .split_once(')')
                .unwrap_or_else(|| panic!("PTX closes {} signature", entry.symbol()))
                .0;
            signature
                .lines()
                .filter(|line| line.contains(".param "))
                .count()
        }
        for entry in [
            soma_abi::register::Entry::Scope,
            soma_abi::register::Entry::ScopeSurface,
            soma_abi::register::Entry::Recast,
            soma_abi::register::Entry::RecastFinish,
            soma_abi::register::Entry::CarrierRebase,
        ] {
            assert_eq!(
                parameter_count(text, entry),
                entry.cuda_parameter_words(),
                "{} PTX parameter count remains the shared typed mouth",
                entry.symbol(),
            );
        }
    }

    #[test]
    fn fold_constant_is_odd() {
        // Odd by construction so add==count*FOLD_CONSTANT cannot alias an even overlap.
        assert_eq!(super::FOLD_CONSTANT & 1, 1);
    }
}
