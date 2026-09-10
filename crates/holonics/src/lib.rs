//! Public Holonics framework entry point. Implementations retain their existing owners.
//!
//! [`structure`] exposes causal/relational carriers and [`geometry`] exposes exact frames,
//! receiver maps and projection fibres. These are available without the default `native`
//! feature, independently of the desktop device runtime. They do not encompass every
//! mathematical construction in the repository; further executable owners live in `engine`.
//!
//! The default `native` feature preserves the existing `hna`, `soulkiller` and `interop`
//! interfaces and exposes their `engine` owner. The HNN API contains several explicitly scoped
//! realizations. In particular, `hna::alpha` is experimental byte-field apparatus, not an
//! attained general-language model. Package containers are distinct from standard executable
//! model graphs; see docs/INTEROPERABILITY.md.

pub use holonic_structure as structure;
pub use relational_geometry as geometry;

#[cfg(feature = "native")]
pub use holonic_engine as engine;
#[cfg(feature = "native")]
pub use holonics_hna as hna;

#[cfg(feature = "native")]
pub mod soulkiller {
    pub use holonic_engine::native_ecology::holonic_intelligence::{
        NativeConeRestrictedEcology, NativeFamilyInsufficiency, ResidentExcitationDismantling,
    };
    pub use holonic_engine::soulkiller::{
        SoulkillerDismantlingInput, SoulkillerDismantlingReturn, dismantle,
    };
}

#[cfg(feature = "native")]
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
