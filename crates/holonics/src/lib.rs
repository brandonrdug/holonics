//! Public framework entry point. Implementations retain their existing owners.
//!
//! `hna` runs the current native recurrence. `soulkiller` consumes admitted excitation
//! material. `interop` exposes existing package containers; it does not claim that those
//! containers are standard executable neural graphs. See docs/INTEROPERABILITY.md.

pub use holonics_hna as hna;

pub mod soulkiller {
    pub use holonic_engine::native_ecology::holonic_intelligence::{
        NativeConeRestrictedEcology, NativeFamilyInsufficiency, ResidentExcitationDismantling,
    };
    pub use holonic_engine::soulkiller::{
        SoulkillerDismantlingInput, SoulkillerDismantlingReturn, dismantle,
    };
}

pub mod interop {
    pub use holonic_engine::foreign_map::{ForeignContainer, manifest_safetensors};
    pub use holonic_engine::native_ecology::holonic_intelligence::{
        ForeignConfigurationChart, ForeignOnnxChart, ShardedWeightIndexChart,
    };

    /// Reversible Holonics package containers, not standard executable graph compilation.
    pub mod packages {
        pub use life::native_intelligence::{
            ExportCodecKind, ExportPurpose, MorphologyExportRequest, MorphologyExportReturn,
            NativeMorphologyArtifact, export_morphology, import_exact_export,
        };
    }
}
