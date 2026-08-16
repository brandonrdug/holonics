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
/// `FOLD_CONSTANT`; kept here so the cpu's exact check needs no re-derivation). 2^61 - 1.
pub const FOLD_CONSTANT: u64 = 2_305_843_009_213_693_951;

#[cfg(test)]
mod tests {
    use super::SOMA_PTX;

    /// The committed PTX boundary artifact, checked cpu-side (no GPU) so the workspace test
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

    /// Entries compiled into the artifact AND resolved by a Rust launcher.
    ///
    /// Each name here is reachable: some caller resolves it through `Module::function`, either by
    /// a literal in a `soma/mount/src/bin/mount-*-gate.rs`, by a `soma_abi::*::ENTRY_SYMBOL`
    /// constant, or through `soma_abi::register::Entry::symbol`.
    const LAUNCHED_ENTRIES: &[&str] = &[
        "link_grain",
        "link_sum",
        "link_finish",
        "link_founded_grain",
        "link_founded_sum",
        "chart_mark",
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
        "lineage_event_population",
        "material_shadow_read",
        "text_incidence_select",
        "text_section_restrict",
        "returned_contact_group",
        "morphological_suffix_condition",
        "morphological_prefix_condition",
        "morphological_conduct_group",
        "recurrent_law_found",
        "recurrent_law_evaluate",
        "recurrent_law_fold",
    ];

    /// Entries compiled into the artifact and reachable by NOTHING. Measured 2026-08-15.
    ///
    /// These four are defined as `extern "ptx-kernel"` in `soma-kernel-cuda/src/lib.rs`, listed in
    /// `soma-kernel-cuda/build-ptx.sh`, and emitted into the PTX. They have **no `soma_abi` entry
    /// symbol, no `Module::function` resolution, and no launcher** anywhere in `soma/` or
    /// `crates/` — `soma_abi::register::Entry` names five register entries and none of these is
    /// among them. The `link` family has three cpu gates (`mount-link-gate` for
    /// `link_{grain,sum,finish}`, `mount-founded-gate` for the founded pair); the *registered*
    /// third arm was compiled but its gate was never built, and `mount-chart-gate` resolves
    /// `chart_{mark,count,recast}` without `chart_register_mark`. The same four are orphaned
    /// identically at `reference/engine-a07ff376/`, so this was inherited rather than introduced.
    ///
    /// They are NOT deleted: the PTX is a committed boundary artifact bound to its closure and
    /// guarded by the `boundary-artifacts` gate, and orphanhood is a missing join, not evidence
    /// the kernel is wrong. Wiring a launcher retires a name from this list into
    /// `LAUNCHED_ENTRIES`; the completeness assertion below forces that move to be deliberate.
    const UNLAUNCHED_ENTRIES: &[&str] = &[
        "link_register_grain",
        "link_register_sum",
        "link_register_finish",
        "chart_register_mark",
    ];

    #[test]
    fn soma_ptx_artifact_is_sm89_with_all_thirty_two_entries_and_required_atomics() {
        let text = std::str::from_utf8(SOMA_PTX).expect("the soma PTX artifact is text");
        assert!(text.contains(".target sm_89"), "soma PTX must target sm_89");

        // PRESENCE ONLY. `.entry <name>` proves the symbol was compiled in. It says nothing
        // whatever about whether any Rust code can reach it, and this assertion cannot fail once
        // the kernel compiles — which is exactly why the population is split above and closed
        // below. Reachability is carried by `LAUNCHED_ENTRIES`/`UNLAUNCHED_ENTRIES`, not by this
        // loop.
        for entry in LAUNCHED_ENTRIES.iter().chain(UNLAUNCHED_ENTRIES) {
            assert!(
                text.contains(&format!(".entry {entry}")),
                "soma PTX must expose {entry}"
            );
        }

        // The closure that makes the split load-bearing: the two declared populations must be
        // exactly the artifact's own `.entry` population. Without this the lists could drift from
        // the PTX in either direction — a new kernel could be compiled in and go unnamed, or a
        // name could persist here after its entry was dropped — and nothing would notice.
        let declared = LAUNCHED_ENTRIES
            .iter()
            .chain(UNLAUNCHED_ENTRIES)
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            declared.len(),
            LAUNCHED_ENTRIES.len() + UNLAUNCHED_ENTRIES.len(),
            "an entry is named twice across the launched/unlaunched split"
        );
        let compiled = text
            .lines()
            .filter_map(|line| line.strip_prefix(".visible .entry "))
            .map(|rest| rest.trim_end_matches(['(', ' ']))
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            compiled, declared,
            "the PTX entry population and the declared launched/unlaunched split disagree; \
             a kernel was added or removed without recording whether anything can reach it"
        );
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

        let returned_mouth = ".entry returned_contact_group(";
        let returned = text
            .split_once(returned_mouth)
            .expect("PTX carries returned_contact_group")
            .1;
        let returned_signature = returned
            .split_once(')')
            .expect("PTX closes returned_contact_group signature")
            .0;
        assert_eq!(
            returned_signature
                .lines()
                .filter(|line| line.contains(".param "))
                .count(),
            7,
            "the returned-contact entry retains three pointer/extent pairs plus x_stride",
        );
        let returned_body = returned
            .split_once("\n.visible .entry ")
            .map_or(returned, |(body, _)| body);
        for float_spelling in [".f16", ".f32", ".f64"] {
            assert!(
                !returned_body.contains(float_spelling),
                "returned_contact_group carries forbidden {float_spelling}"
            );
        }

        let morph_mouth = ".entry morphological_conduct_group(";
        let morph = text
            .split_once(morph_mouth)
            .expect("PTX carries morphological_conduct_group")
            .1;
        let morph_signature = morph
            .split_once(')')
            .expect("PTX closes morphological_conduct_group signature")
            .0;
        assert_eq!(
            morph_signature
                .lines()
                .filter(|line| line.contains(".param "))
                .count(),
            11,
            "the morphological-conduct entry retains five pointer/extent pairs plus x_stride",
        );
        let morph_body = morph
            .split_once("\n.visible .entry ")
            .map_or(morph, |(body, _)| body);
        for float_spelling in [".f16", ".f32", ".f64"] {
            assert!(
                !morph_body.contains(float_spelling),
                "morphological_conduct_group carries forbidden {float_spelling}"
            );
        }
    }

    #[test]
    fn fold_constant_is_odd() {
        // Odd by construction so add==count*FOLD_CONSTANT cannot alias an even overlap.
        assert_eq!(super::FOLD_CONSTANT & 1, 1);
    }
}
