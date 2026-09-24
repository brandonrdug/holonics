//! Typed CUDA launch mouths for the five REGISTER entries.
//!
//! Scheduling remains with the conductor, while this module owns each entry symbol and the exact
//! `(device pointer, element extent)` argument order presented to the CUDA driver.  Life and the
//! independent gates therefore name transported faces instead of rebuilding raw argument arrays.
//!
//! **Every launch here crosses [`crate::launch_law`].**  Each entry declares its
//! [`LaunchRequirement`] — argument names, residency, element width and access, read off the
//! kernel's own signature in `accelerators/cuda-kernel/src/lib.rs` — and the call site proves it
//! before any driver call.  Two mouths are offered per entry:
//!
//! * `cover(evidence, extent, arguments)` derives the covering shape from the device evidence the
//!   caller declares and returns a [`LawfulLaunch`] whose receipt carries the proved `x_stride` the
//!   kernel's parameter buffer must repeat.  `enact` then issues it.  Under
//!   [`LaunchEvidence::Device`] nothing is deferred; under [`LaunchEvidence::Census`] the three
//!   clauses a census cannot carry are named in the receipt.  It formerly took a bare
//!   `LaunchCensus`, so those three were deferred whether or not the caller held the card.
//! * `launch(evidence, grid, block, extent, arguments)` is for a caller that derived its shape
//!   elsewhere.  It takes the element extent and the device evidence **explicitly**, so the
//!   coverage and device clauses are proved rather than deferred; it returns the receipt it
//!   earned rather than discarding it.  The former shape — `launch(grid, block, arguments)`,
//!   which silently fell back to `LaunchLimits::from_function` and a `Coverage::Undeclared`
//!   requirement — deferred the coverage and every device clause without the caller choosing to,
//!   and is gone.
//!
//! **Write exclusivity is a type here.**  A `*const` face of the entry is a `Copy`
//! [`RegisterSpan`]; a `*mut` face is a [`RegisterWriteSpan`], which is neither `Copy` nor `Clone`
//! and holds `PhantomData<&'a mut DeviceBuffer<T>>`.  That is D2's `DeviceWriteSpan` exclusivity
//! carried into the launchers the repository actually ships.

use core::marker::PhantomData;

use crate::cuda::LaunchCensus;
use crate::launch_law::{
    Access, ArgumentRequirement, ArgumentSpan, Extent, LaunchEvidence, LaunchLimits, LaunchReceipt,
    LaunchRequirement, LaunchShape, LawfulLaunch,
};
use crate::{CudaError, DeviceBuffer, Dim3, Function, LinearLaunch, Module, Result};

fn boundary(context: &'static str, message: impl Into<String>) -> CudaError {
    CudaError {
        code: -1,
        name: String::from("REGISTER_LAUNCH_BOUNDARY"),
        message: message.into(),
        context,
    }
}

/// The carving arithmetic shared by the shared and exclusive REGISTER spans: bounds, whole-word
/// element width, and alignment, all checked.
fn carve_u32_words<T>(
    backing_pointer: u64,
    backing_len: usize,
    word_base: usize,
    elements: usize,
) -> Result<u64> {
    let element_bytes = core::mem::size_of::<T>();
    if element_bytes == 0 || !element_bytes.is_multiple_of(core::mem::size_of::<u32>()) {
        return Err(boundary(
            "RegisterSpan::from_u32_words",
            "a carved REGISTER span consists of whole u32 words",
        ));
    }
    let element_words = element_bytes / core::mem::size_of::<u32>();
    let span_words = elements.checked_mul(element_words).ok_or_else(|| {
        boundary(
            "RegisterSpan::from_u32_words",
            "the carved REGISTER span word extent overflows usize",
        )
    })?;
    let end = word_base.checked_add(span_words).ok_or_else(|| {
        boundary(
            "RegisterSpan::from_u32_words",
            "the carved REGISTER span end overflows usize",
        )
    })?;
    if end > backing_len {
        return Err(boundary(
            "RegisterSpan::from_u32_words",
            format!("word span {word_base}..{end} exceeds backing extent {backing_len}"),
        ));
    }
    let byte_base = word_base
        .checked_mul(core::mem::size_of::<u32>())
        .ok_or_else(|| {
            boundary(
                "RegisterSpan::from_u32_words",
                "the carved REGISTER byte origin overflows usize",
            )
        })?;
    let byte_base = u64::try_from(byte_base).map_err(|_| {
        boundary(
            "RegisterSpan::from_u32_words",
            "the carved REGISTER byte origin exceeds the CUDA address wire",
        )
    })?;
    let pointer = backing_pointer.checked_add(byte_base).ok_or_else(|| {
        boundary(
            "RegisterSpan::from_u32_words",
            "the carved REGISTER device address overflows",
        )
    })?;
    if pointer % core::mem::align_of::<T>() as u64 != 0 {
        return Err(boundary(
            "RegisterSpan::from_u32_words",
            "the carved REGISTER span does not preserve element alignment",
        ));
    }
    Ok(pointer)
}

/// **One typed device span a REGISTER entry *reads*.**
///
/// It is `Copy` and holds `PhantomData<&'a DeviceBuffer<T>>`, so several read spans of the same
/// allocation may coexist — which is exactly the D2 rule that read spans may alias one another.
/// It cannot be presented for a `Write` argument: [`RegisterSpan::argument`] declares
/// [`Access::Read`] and there is no other way out of the type.
#[derive(Clone, Copy)]
pub struct RegisterSpan<'a, T> {
    pointer: u64,
    elements: usize,
    _borrow: PhantomData<&'a DeviceBuffer<T>>,
}

impl<'a, T: Copy> RegisterSpan<'a, T> {
    pub fn whole(buffer: &'a DeviceBuffer<T>) -> Self {
        Self {
            pointer: buffer.device_ptr(),
            elements: buffer.len(),
            _borrow: PhantomData,
        }
    }

    /// View an exact element span inside a `u32` allocation without manufacturing a second
    /// allocation.
    pub fn from_u32_words(
        backing: &'a DeviceBuffer<u32>,
        word_base: usize,
        elements: usize,
    ) -> Result<Self> {
        let pointer =
            carve_u32_words::<T>(backing.device_ptr(), backing.len(), word_base, elements)?;
        Ok(Self {
            pointer,
            elements,
            _borrow: PhantomData,
        })
    }

    /// Present this proved span to the launch law as the entry's `*const` face.  The element width
    /// comes from `T`, so a span's declared and presented widths cannot disagree.
    pub const fn argument(&self, name: &'static str) -> ArgumentSpan {
        ArgumentSpan::device_raw(
            name,
            self.pointer,
            self.elements,
            core::mem::size_of::<T>(),
            Access::Read,
        )
    }
}

/// **One typed device span a REGISTER entry *writes*.**
///
/// [definition] This is D2 carried into the launchers.  It holds
/// `PhantomData<&'a mut DeviceBuffer<T>>` and is neither `Copy` nor `Clone`, so the borrow checker
/// refuses — *at compile time* — a second write span or any read span of the same allocation while
/// it lives.  The shipped launchers formerly presented `Access::Write` arguments through the
/// `Copy` [`RegisterSpan`], which carried no compile-time exclusivity at all and left
/// [`crate::launch_law::AliasAudit`] — a within-one-launch check — as the only guard.
pub struct RegisterWriteSpan<'a, T> {
    pointer: u64,
    elements: usize,
    _borrow: PhantomData<&'a mut DeviceBuffer<T>>,
}

impl<'a, T: Copy> RegisterWriteSpan<'a, T> {
    /// Borrow a whole allocation exclusively for writing.
    pub fn whole(buffer: &'a mut DeviceBuffer<T>) -> Self {
        Self {
            pointer: buffer.device_ptr(),
            elements: buffer.len(),
            _borrow: PhantomData,
        }
    }

    /// Carve an exclusive element span inside a `u32` allocation.  This is the cooperative
    /// completion / contact sheet face.
    pub fn from_u32_words(
        backing: &'a mut DeviceBuffer<u32>,
        word_base: usize,
        elements: usize,
    ) -> Result<Self> {
        let pointer =
            carve_u32_words::<T>(backing.device_ptr(), backing.len(), word_base, elements)?;
        Ok(Self {
            pointer,
            elements,
            _borrow: PhantomData,
        })
    }

    /// Present this proved span to the launch law as the entry's `*mut` face.
    pub const fn argument(&self, name: &'static str) -> ArgumentSpan {
        ArgumentSpan::device_raw(
            name,
            self.pointer,
            self.elements,
            core::mem::size_of::<T>(),
            Access::Write,
        )
    }
}

/// The ten common arguments of `scope_register` and `scope_register_surface`, in the exact order
/// and with the exact `*const`/`*mut` character of the kernel's own signature
/// (`accelerators/cuda-kernel/src/lib.rs`, `scope_register`).
fn scope_argument_law(params: Extent) -> Vec<ArgumentRequirement> {
    vec![
        ArgumentRequirement::device("standing", Access::Read, 4, Extent::Any),
        ArgumentRequirement::device("owns", Access::Write, 4, Extent::Any),
        ArgumentRequirement::device("carriers", Access::Write, 4, Extent::Any),
        ArgumentRequirement::device("bytes", Access::Read, 4, Extent::Any),
        ArgumentRequirement::device("lanes", Access::Read, 4, Extent::Any),
        ArgumentRequirement::device("counts", Access::Write, 8, Extent::Any),
        ArgumentRequirement::device("params", Access::Read, 4, params),
        ArgumentRequirement::device("radiation", Access::Write, 4, Extent::Any),
        ArgumentRequirement::device("completion", Access::Write, 4, Extent::Any),
        ArgumentRequirement::device("statuses", Access::Write, 4, Extent::Any),
    ]
}

/// The cooperative entry's eleventh argument: one transient contact sheet.
fn scope_surface_argument_law(params: Extent) -> Vec<ArgumentRequirement> {
    let mut law = scope_argument_law(params);
    law.push(ArgumentRequirement::device(
        "contact_words",
        Access::Write,
        4,
        Extent::Any,
    ));
    law
}

/// The seven arguments shared by `register_own_recast` and `register_own_recast_finish`.
fn recast_argument_law(params: Extent) -> Vec<ArgumentRequirement> {
    vec![
        ArgumentRequirement::device("old_owns", Access::Read, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("fresh_owns", Access::Write, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("old_lanes", Access::Read, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("new_lanes", Access::Read, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("requests", Access::Read, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("completions", Access::Write, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("params", Access::Read, 4, params),
    ]
}

/// The seven arguments of `register_carrier_rebase`.
fn carrier_argument_law(params: Extent) -> Vec<ArgumentRequirement> {
    vec![
        ArgumentRequirement::device("old_carriers", Access::Read, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("fresh_carriers", Access::Write, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("old_lanes", Access::Read, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("new_lanes", Access::Read, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("requests", Access::Read, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("completions", Access::Write, 4, Extent::AtLeast(1)),
        ArgumentRequirement::device("params", Access::Read, 4, params),
    ]
}

/// The ten common pairs carried by `scope_register` and `scope_register_surface`.
///
/// The `*const` faces are [`RegisterSpan`]s and the `*mut` faces are [`RegisterWriteSpan`]s, read
/// off the entry's own signature.  The struct is therefore neither `Copy` nor `Clone`: one
/// argument population is one exclusive borrow of each written allocation.
pub struct RegisterScopeArguments<'a> {
    pub standing: RegisterSpan<'a, u32>,
    pub owns: RegisterWriteSpan<'a, u32>,
    pub carriers: RegisterWriteSpan<'a, u32>,
    pub bytes: RegisterSpan<'a, u32>,
    pub lanes: RegisterSpan<'a, u32>,
    pub counts: RegisterWriteSpan<'a, u64>,
    pub params: RegisterSpan<'a, u32>,
    pub radiation: RegisterWriteSpan<'a, u32>,
    pub completion: RegisterWriteSpan<'a, u32>,
    pub statuses: RegisterWriteSpan<'a, u32>,
}

impl RegisterScopeArguments<'_> {
    fn spans(&self) -> [ArgumentSpan; holonics_portable::wire::register::Entry::Scope.buffer_pairs()] {
        [
            self.standing.argument("standing"),
            self.owns.argument("owns"),
            self.carriers.argument("carriers"),
            self.bytes.argument("bytes"),
            self.lanes.argument("lanes"),
            self.counts.argument("counts"),
            self.params.argument("params"),
            self.radiation.argument("radiation"),
            self.completion.argument("completion"),
            self.statuses.argument("statuses"),
        ]
    }
}

/// The cooperative REGISTER entry adds one transient contact sheet after the common pairs.
pub struct RegisterScopeSurfaceArguments<'a> {
    pub common: RegisterScopeArguments<'a>,
    pub contact_words: RegisterWriteSpan<'a, u32>,
}

impl RegisterScopeSurfaceArguments<'_> {
    fn spans(&self) -> [ArgumentSpan; holonics_portable::wire::register::Entry::ScopeSurface.buffer_pairs()] {
        let common = self.common.spans();
        [
            common[0],
            common[1],
            common[2],
            common[3],
            common[4],
            common[5],
            common[6],
            common[7],
            common[8],
            common[9],
            self.contact_words.argument("contact_words"),
        ]
    }
}

/// The seven pairs shared by the ordered recast cell and finish entries.
pub struct RegisterRecastArguments<'a> {
    pub old_owns: RegisterSpan<'a, u32>,
    pub fresh_owns: RegisterWriteSpan<'a, u32>,
    pub old_lanes: RegisterSpan<'a, u32>,
    pub new_lanes: RegisterSpan<'a, u32>,
    pub requests: RegisterSpan<'a, u32>,
    pub completions: RegisterWriteSpan<'a, u32>,
    pub params: RegisterSpan<'a, u32>,
}

impl RegisterRecastArguments<'_> {
    fn spans(&self) -> [ArgumentSpan; holonics_portable::wire::register::Entry::Recast.buffer_pairs()] {
        [
            self.old_owns.argument("old_owns"),
            self.fresh_owns.argument("fresh_owns"),
            self.old_lanes.argument("old_lanes"),
            self.new_lanes.argument("new_lanes"),
            self.requests.argument("requests"),
            self.completions.argument("completions"),
            self.params.argument("params"),
        ]
    }
}

/// The seven exact pairs carried by the device-local carrier rebase entry.
pub struct RegisterCarrierRebaseArguments<'a> {
    pub old_carriers: RegisterSpan<'a, u32>,
    pub fresh_carriers: RegisterWriteSpan<'a, u32>,
    pub old_lanes: RegisterSpan<'a, u32>,
    pub new_lanes: RegisterSpan<'a, u32>,
    pub requests: RegisterSpan<'a, u32>,
    pub completions: RegisterWriteSpan<'a, u32>,
    pub params: RegisterSpan<'a, u32>,
}

impl RegisterCarrierRebaseArguments<'_> {
    fn spans(&self) -> [ArgumentSpan; holonics_portable::wire::register::Entry::CarrierRebase.buffer_pairs()] {
        [
            self.old_carriers.argument("old_carriers"),
            self.fresh_carriers.argument("fresh_carriers"),
            self.old_lanes.argument("old_lanes"),
            self.new_lanes.argument("new_lanes"),
            self.requests.argument("requests"),
            self.completions.argument("completions"),
            self.params.argument("params"),
        ]
    }
}

/// Prove a caller-supplied shape **against a declared element extent and declared device
/// evidence**, then enact it.  Nothing is deferred that the caller's evidence carries.
fn launch_declared(
    function: &Function<'_>,
    kernel: &'static str,
    law: Vec<ArgumentRequirement>,
    evidence: LaunchEvidence<'_>,
    shape: LaunchShape,
    extent: u64,
    spans: &[ArgumentSpan],
) -> Result<LaunchReceipt> {
    let limits = LaunchLimits::from_evidence(evidence, function)?;
    let requirement = LaunchRequirement::guarded(kernel, extent, law);
    LawfulLaunch::prove(&requirement, &limits, shape, spans)?.enact(function, None, &[])
}

/// The one-dimensional shape a caller-derived `grid`/`block` names, with no dynamic shared surface.
const fn offered(grid: Dim3, block: Dim3) -> LaunchShape {
    LaunchShape {
        grid,
        block,
        shared_bytes: 0,
    }
}

/// Derive the covering shape from **the device evidence the caller declares** and prove it.
///
/// This took a bare `LaunchCensus`, which meant every covering mouth deferred the three clauses a
/// census cannot carry — `BlockDimensionWithinDevice`, `SharedWithinDevice` and, for an entry that
/// declares one, `BlockWarpMultiple` — whether or not the caller held a device handle. It now takes
/// the same declared `LaunchEvidence` the non-covering mouths take, so a caller holding the card
/// gets a completely proved receipt and a caller holding only a census still says so aloud.
fn prove_cover(
    function: &Function<'_>,
    kernel: &'static str,
    law: Vec<ArgumentRequirement>,
    evidence: LaunchEvidence<'_>,
    extent: u64,
    spans: &[ArgumentSpan],
) -> Result<LawfulLaunch> {
    let limits = LaunchLimits::from_evidence(evidence, function)?;
    let requirement = LaunchRequirement::guarded(kernel, extent, law);
    Ok(LawfulLaunch::cover(&requirement, &limits, spans)?)
}

/// The exact `scope_register` entry.
pub struct RegisterScopeKernel<'m>(Function<'m>);

impl RegisterScopeKernel<'_> {
    pub fn linear_launch(&self, census: LaunchCensus, work: u64) -> Result<LinearLaunch> {
        self.0.linear_launch(census, work)
    }

    /// Prove and issue a caller-derived shape over `extent` elements, against the device evidence
    /// the caller declares.  Returns the receipt it earned.
    pub fn launch(
        &self,
        evidence: LaunchEvidence<'_>,
        grid: Dim3,
        block: Dim3,
        extent: u64,
        arguments: RegisterScopeArguments<'_>,
    ) -> Result<LaunchReceipt> {
        launch_declared(
            &self.0,
            holonics_portable::wire::register::Entry::Scope.symbol(),
            scope_argument_law(Extent::AtLeast(1)),
            evidence,
            offered(grid, block),
            extent,
            &arguments.spans(),
        )
    }

    /// Derive and prove the covering launch for `extent` lanes.  The proof's `x_stride` is what
    /// the entry's parameter buffer must carry; fill it, then [`RegisterScopeKernel::enact`].
    pub fn cover(
        &self,
        evidence: LaunchEvidence<'_>,
        extent: u64,
        arguments: RegisterScopeArguments<'_>,
    ) -> Result<LawfulLaunch> {
        prove_cover(
            &self.0,
            holonics_portable::wire::register::Entry::Scope.symbol(),
            scope_argument_law(Extent::AtLeast(1)),
            evidence,
            extent,
            &arguments.spans(),
        )
    }

    /// Issue a proved launch.  The entry declares no scalar parameters.
    pub fn enact(&self, proof: LawfulLaunch) -> Result<LaunchReceipt> {
        proof.enact(&self.0, None, &[])
    }
}

/// The exact `scope_register_surface` entry.
pub struct RegisterScopeSurfaceKernel<'m>(Function<'m>);

impl RegisterScopeSurfaceKernel<'_> {
    pub fn block_launch(
        &self,
        census: LaunchCensus,
        work: u64,
        block_x: u32,
    ) -> Result<LinearLaunch> {
        self.0.block_launch(census, work, block_x)
    }

    pub fn local_size_bytes(&self) -> Result<usize> {
        self.0.local_size_bytes()
    }

    /// Prove and issue a caller-derived shape over `extent` elements, against the device evidence
    /// the caller declares.  Returns the receipt it earned.
    pub fn launch(
        &self,
        evidence: LaunchEvidence<'_>,
        grid: Dim3,
        block: Dim3,
        extent: u64,
        arguments: RegisterScopeSurfaceArguments<'_>,
    ) -> Result<LaunchReceipt> {
        launch_declared(
            &self.0,
            holonics_portable::wire::register::Entry::ScopeSurface.symbol(),
            scope_surface_argument_law(Extent::AtLeast(1)),
            evidence,
            offered(grid, block),
            extent,
            &arguments.spans(),
        )
    }
}

/// The exact `register_own_recast` entry.
pub struct RegisterRecastKernel<'m>(Function<'m>);

impl RegisterRecastKernel<'_> {
    pub fn linear_launch(&self, census: LaunchCensus, work: u64) -> Result<LinearLaunch> {
        self.0.linear_launch(census, work)
    }

    /// Prove and issue a caller-derived shape over `extent` elements, against the device evidence
    /// the caller declares.  Returns the receipt it earned.
    pub fn launch(
        &self,
        evidence: LaunchEvidence<'_>,
        grid: Dim3,
        block: Dim3,
        extent: u64,
        arguments: RegisterRecastArguments<'_>,
    ) -> Result<LaunchReceipt> {
        launch_declared(
            &self.0,
            holonics_portable::wire::register::Entry::Recast.symbol(),
            recast_argument_law(Extent::AtLeast(1)),
            evidence,
            offered(grid, block),
            extent,
            &arguments.spans(),
        )
    }

    /// Derive and prove the covering launch over `extent` cells.
    pub fn cover(
        &self,
        evidence: LaunchEvidence<'_>,
        extent: u64,
        params: Extent,
        arguments: RegisterRecastArguments<'_>,
    ) -> Result<LawfulLaunch> {
        prove_cover(
            &self.0,
            holonics_portable::wire::register::Entry::Recast.symbol(),
            recast_argument_law(params),
            evidence,
            extent,
            &arguments.spans(),
        )
    }

    /// Issue a proved launch.  The entry declares no scalar parameters.
    pub fn enact(&self, proof: LawfulLaunch) -> Result<LaunchReceipt> {
        proof.enact(&self.0, None, &[])
    }
}

/// The exact `register_own_recast_finish` entry.
pub struct RegisterRecastFinishKernel<'m>(Function<'m>);

impl RegisterRecastFinishKernel<'_> {
    pub fn linear_launch(&self, census: LaunchCensus, work: u64) -> Result<LinearLaunch> {
        self.0.linear_launch(census, work)
    }

    /// Prove and issue a caller-derived shape over `extent` elements, against the device evidence
    /// the caller declares.  Returns the receipt it earned.
    pub fn launch(
        &self,
        evidence: LaunchEvidence<'_>,
        grid: Dim3,
        block: Dim3,
        extent: u64,
        arguments: RegisterRecastArguments<'_>,
    ) -> Result<LaunchReceipt> {
        launch_declared(
            &self.0,
            holonics_portable::wire::register::Entry::RecastFinish.symbol(),
            recast_argument_law(Extent::AtLeast(1)),
            evidence,
            offered(grid, block),
            extent,
            &arguments.spans(),
        )
    }

    /// Derive and prove the covering launch over `extent` lanes.
    pub fn cover(
        &self,
        evidence: LaunchEvidence<'_>,
        extent: u64,
        params: Extent,
        arguments: RegisterRecastArguments<'_>,
    ) -> Result<LawfulLaunch> {
        prove_cover(
            &self.0,
            holonics_portable::wire::register::Entry::RecastFinish.symbol(),
            recast_argument_law(params),
            evidence,
            extent,
            &arguments.spans(),
        )
    }

    /// Issue a proved launch.  The entry declares no scalar parameters.
    pub fn enact(&self, proof: LawfulLaunch) -> Result<LaunchReceipt> {
        proof.enact(&self.0, None, &[])
    }
}

/// The exact `register_carrier_rebase` entry.
pub struct RegisterCarrierRebaseKernel<'m>(Function<'m>);

impl RegisterCarrierRebaseKernel<'_> {
    pub fn linear_launch(&self, census: LaunchCensus, work: u64) -> Result<LinearLaunch> {
        self.0.linear_launch(census, work)
    }

    /// Prove and issue a caller-derived shape over `extent` elements, against the device evidence
    /// the caller declares.  Returns the receipt it earned.
    pub fn launch(
        &self,
        evidence: LaunchEvidence<'_>,
        grid: Dim3,
        block: Dim3,
        extent: u64,
        arguments: RegisterCarrierRebaseArguments<'_>,
    ) -> Result<LaunchReceipt> {
        launch_declared(
            &self.0,
            holonics_portable::wire::register::Entry::CarrierRebase.symbol(),
            carrier_argument_law(Extent::AtLeast(1)),
            evidence,
            offered(grid, block),
            extent,
            &arguments.spans(),
        )
    }

    /// Derive and prove the covering launch over `extent` lanes.
    pub fn cover(
        &self,
        evidence: LaunchEvidence<'_>,
        extent: u64,
        params: Extent,
        arguments: RegisterCarrierRebaseArguments<'_>,
    ) -> Result<LawfulLaunch> {
        prove_cover(
            &self.0,
            holonics_portable::wire::register::Entry::CarrierRebase.symbol(),
            carrier_argument_law(params),
            evidence,
            extent,
            &arguments.spans(),
        )
    }

    /// Issue a proved launch.  The entry declares no scalar parameters.
    pub fn enact(&self, proof: LawfulLaunch) -> Result<LaunchReceipt> {
        proof.enact(&self.0, None, &[])
    }
}

impl Module {
    pub fn register_scope(&self) -> Result<RegisterScopeKernel<'_>> {
        self.function(holonics_portable::wire::register::Entry::Scope.symbol())
            .map(RegisterScopeKernel)
    }

    pub fn register_scope_surface(&self) -> Result<RegisterScopeSurfaceKernel<'_>> {
        self.function(holonics_portable::wire::register::Entry::ScopeSurface.symbol())
            .map(RegisterScopeSurfaceKernel)
    }

    pub fn register_recast(&self) -> Result<RegisterRecastKernel<'_>> {
        self.function(holonics_portable::wire::register::Entry::Recast.symbol())
            .map(RegisterRecastKernel)
    }

    pub fn register_recast_finish(&self) -> Result<RegisterRecastFinishKernel<'_>> {
        self.function(holonics_portable::wire::register::Entry::RecastFinish.symbol())
            .map(RegisterRecastFinishKernel)
    }

    pub fn register_carrier_rebase(&self) -> Result<RegisterCarrierRebaseKernel<'_>> {
        self.function(holonics_portable::wire::register::Entry::CarrierRebase.symbol())
            .map(RegisterCarrierRebaseKernel)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::launch_law::AliasAudit;

    fn span<T>(pointer: u64, elements: usize) -> RegisterSpan<'static, T> {
        RegisterSpan {
            pointer,
            elements,
            _borrow: PhantomData,
        }
    }

    fn write_span<T>(pointer: u64, elements: usize) -> RegisterWriteSpan<'static, T> {
        RegisterWriteSpan {
            pointer,
            elements,
            _borrow: PhantomData,
        }
    }

    fn scope_arguments() -> RegisterScopeArguments<'static> {
        RegisterScopeArguments {
            standing: span(1 << 20, 101),
            owns: write_span(2 << 20, 102),
            carriers: write_span(3 << 20, 103),
            bytes: span(4 << 20, 104),
            lanes: span(5 << 20, 105),
            counts: write_span(6 << 20, 106),
            params: span(7 << 20, 107),
            radiation: write_span(8 << 20, 108),
            completion: write_span(9 << 20, 109),
            statuses: write_span(10 << 20, 110),
        }
    }

    #[test]
    fn scope_span_order_is_the_kernel_signature() {
        let spans = scope_arguments().spans();
        let expected = [
            ("standing", Access::Read),
            ("owns", Access::Write),
            ("carriers", Access::Write),
            ("bytes", Access::Read),
            ("lanes", Access::Read),
            ("counts", Access::Write),
            ("params", Access::Read),
            ("radiation", Access::Write),
            ("completion", Access::Write),
            ("statuses", Access::Write),
        ];
        for (at, span) in spans.iter().enumerate() {
            assert_eq!(span.name(), expected[at].0, "argument {at} keeps its name");
            assert_eq!(span.access(), expected[at].1, "argument {at} keeps its access");
            assert_eq!(span.address(), ((at as u64) + 1) << 20);
            assert_eq!(span.elements(), at + 101);
        }
        // `counts` is the one `u64` face of the entry.
        assert_eq!(spans[5].element_bytes(), 8);
        assert_eq!(spans[0].element_bytes(), 4);

        let surface = RegisterScopeSurfaceArguments {
            common: scope_arguments(),
            contact_words: write_span(11 << 20, 111),
        }
        .spans();
        assert_eq!(surface[10].name(), "contact_words");
        assert_eq!(surface[10].elements(), 111);
        assert_eq!(surface[10].access(), Access::Write);
    }

    /// The declared accesses are read off `accelerators/cuda-kernel/src/lib.rs`, not guessed: the
    /// `*const` faces are `Read` and the `*mut` faces are `Write`.
    #[test]
    fn the_declared_accesses_are_the_kernel_signature() {
        let law = scope_argument_law(Extent::Any);
        let spans = scope_arguments().spans();
        assert_eq!(law.len(), spans.len());
        for (declared, presented) in law.iter().zip(spans.iter()) {
            assert_eq!(declared.name, presented.name());
            assert_eq!(declared.access, presented.access());
            assert_eq!(declared.element_bytes, presented.element_bytes());
        }
        assert_eq!(
            law.iter().filter(|a| a.access == Access::Read).count(),
            4,
            "standing, bytes, lanes and params are the entry's const faces"
        );
    }

    #[test]
    fn recast_span_order_is_shared_by_both_ordered_entries() {
        let arguments = RegisterRecastArguments {
            old_owns: span(1 << 20, 11),
            fresh_owns: write_span(2 << 20, 12),
            old_lanes: span(3 << 20, 13),
            new_lanes: span(4 << 20, 14),
            requests: span(5 << 20, 15),
            completions: write_span(6 << 20, 16),
            params: span(7 << 20, 17),
        };
        let names = [
            "old_owns",
            "fresh_owns",
            "old_lanes",
            "new_lanes",
            "requests",
            "completions",
            "params",
        ];
        for (at, presented) in arguments.spans().iter().enumerate() {
            assert_eq!(presented.name(), names[at]);
            assert_eq!(presented.address(), ((at as u64) + 1) << 20);
            assert_eq!(presented.elements(), at + 11);
        }

        let carrier = RegisterCarrierRebaseArguments {
            old_carriers: span(1 << 20, 11),
            fresh_carriers: write_span(2 << 20, 12),
            old_lanes: span(3 << 20, 13),
            new_lanes: span(4 << 20, 14),
            requests: span(5 << 20, 15),
            completions: write_span(6 << 20, 16),
            params: span(7 << 20, 17),
        };
        let carrier_names = [
            "old_carriers",
            "fresh_carriers",
            "old_lanes",
            "new_lanes",
            "requests",
            "completions",
            "params",
        ];
        for (at, presented) in carrier.spans().iter().enumerate() {
            assert_eq!(presented.name(), carrier_names[at]);
            assert_eq!(presented.elements(), at + 11);
        }
    }

    /// The register entries present disjoint allocations, so the aliasing audit admits them.  A
    /// carved span that overlapped a written one would be refused before any driver call.
    #[test]
    fn the_register_argument_population_passes_the_aliasing_audit() {
        AliasAudit::admit_all(&scope_arguments().spans()).expect("distinct allocations");

        let mut aliased = scope_arguments();
        aliased.owns = write_span(1 << 20, 101); // the same address as the read-only `standing`
        let refusal = AliasAudit::admit_all(&aliased.spans())
            .expect_err("a written OWN face may not alias the standing it reads");
        assert_eq!(
            refusal.clause,
            crate::launch_law::PartitionClause::Aliasing
        );
    }
}
