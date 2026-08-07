//! Typed CUDA launch mouths for the four REGISTER entries.
//!
//! Scheduling remains with the conductor, while this module owns each entry symbol and the exact
//! `(device pointer, element extent)` argument order presented to the CUDA driver.  Life and the
//! independent gates therefore name transported faces instead of rebuilding raw argument arrays.

use core::ffi::c_void;
use core::marker::PhantomData;

use crate::cuda::LaunchCensus;
use crate::{CudaError, DeviceBuffer, Dim3, Function, LinearLaunch, Module, Result};

fn boundary(context: &'static str, message: impl Into<String>) -> CudaError {
    CudaError {
        code: -1,
        name: String::from("REGISTER_LAUNCH_BOUNDARY"),
        message: message.into(),
        context,
    }
}

/// One typed device span carried by a REGISTER entry.
///
/// The lifetime keeps the backing allocation borrowed through argument construction.  The only
/// carved constructor accepts a `u32` backing and proves bounds, element width, and alignment.
#[derive(Clone, Copy)]
pub struct RegisterSpan<'a, T> {
    pointer: u64,
    elements: usize,
    _borrow: PhantomData<&'a T>,
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
    /// allocation. This is used by the cooperative completion/contact sheet only.
    pub fn from_u32_words(
        backing: &'a DeviceBuffer<u32>,
        word_base: usize,
        elements: usize,
    ) -> Result<Self> {
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
        if end > backing.len() {
            return Err(boundary(
                "RegisterSpan::from_u32_words",
                format!(
                    "word span {word_base}..{end} exceeds backing extent {}",
                    backing.len()
                ),
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
        let pointer = backing.device_ptr().checked_add(byte_base).ok_or_else(|| {
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
        Ok(Self {
            pointer,
            elements,
            _borrow: PhantomData,
        })
    }

    fn raw(self) -> RawPair {
        RawPair {
            pointer: self.pointer,
            elements: self.elements,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RawPair {
    pointer: u64,
    elements: usize,
}

fn launch_pairs(function: &Function<'_>, grid: Dim3, block: Dim3, pairs: &[RawPair]) -> Result<()> {
    let mut values = Vec::with_capacity(pairs.len() * 2);
    for pair in pairs {
        values.push(pair.pointer);
        values.push(u64::try_from(pair.elements).map_err(|_| {
            boundary(
                "REGISTER CUDA argument extent",
                "a REGISTER buffer extent exceeds its 64-bit ABI word",
            )
        })?);
    }
    let mut arguments: Vec<*mut c_void> = values
        .iter_mut()
        .map(|value| value as *mut u64 as *mut c_void)
        .collect();
    function.launch(grid, block, &mut arguments)
}

/// The ten common pairs carried by `scope_register` and `scope_register_surface`.
#[derive(Clone, Copy)]
pub struct RegisterScopeArguments<'a> {
    pub standing: RegisterSpan<'a, u32>,
    pub owns: RegisterSpan<'a, u32>,
    pub carriers: RegisterSpan<'a, u32>,
    pub bytes: RegisterSpan<'a, u32>,
    pub lanes: RegisterSpan<'a, u32>,
    pub counts: RegisterSpan<'a, u64>,
    pub params: RegisterSpan<'a, u32>,
    pub radiation: RegisterSpan<'a, u32>,
    pub completion: RegisterSpan<'a, u32>,
    pub statuses: RegisterSpan<'a, u32>,
}

impl RegisterScopeArguments<'_> {
    fn pairs(self) -> [RawPair; soma_abi::register::Entry::Scope.buffer_pairs()] {
        [
            self.standing.raw(),
            self.owns.raw(),
            self.carriers.raw(),
            self.bytes.raw(),
            self.lanes.raw(),
            self.counts.raw(),
            self.params.raw(),
            self.radiation.raw(),
            self.completion.raw(),
            self.statuses.raw(),
        ]
    }
}

/// The cooperative REGISTER entry adds one transient contact sheet after the common pairs.
#[derive(Clone, Copy)]
pub struct RegisterScopeSurfaceArguments<'a> {
    pub common: RegisterScopeArguments<'a>,
    pub contact_words: RegisterSpan<'a, u32>,
}

impl RegisterScopeSurfaceArguments<'_> {
    fn pairs(self) -> [RawPair; soma_abi::register::Entry::ScopeSurface.buffer_pairs()] {
        let common = self.common.pairs();
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
            self.contact_words.raw(),
        ]
    }
}

/// The seven pairs shared by the ordered recast cell and finish entries.
#[derive(Clone, Copy)]
pub struct RegisterRecastArguments<'a> {
    pub old_owns: RegisterSpan<'a, u32>,
    pub fresh_owns: RegisterSpan<'a, u32>,
    pub old_lanes: RegisterSpan<'a, u32>,
    pub new_lanes: RegisterSpan<'a, u32>,
    pub requests: RegisterSpan<'a, u32>,
    pub completions: RegisterSpan<'a, u32>,
    pub params: RegisterSpan<'a, u32>,
}

impl RegisterRecastArguments<'_> {
    fn pairs(self) -> [RawPair; soma_abi::register::Entry::Recast.buffer_pairs()] {
        [
            self.old_owns.raw(),
            self.fresh_owns.raw(),
            self.old_lanes.raw(),
            self.new_lanes.raw(),
            self.requests.raw(),
            self.completions.raw(),
            self.params.raw(),
        ]
    }
}

/// The seven exact pairs carried by the device-local carrier rebase entry.
#[derive(Clone, Copy)]
pub struct RegisterCarrierRebaseArguments<'a> {
    pub old_carriers: RegisterSpan<'a, u32>,
    pub fresh_carriers: RegisterSpan<'a, u32>,
    pub old_lanes: RegisterSpan<'a, u32>,
    pub new_lanes: RegisterSpan<'a, u32>,
    pub requests: RegisterSpan<'a, u32>,
    pub completions: RegisterSpan<'a, u32>,
    pub params: RegisterSpan<'a, u32>,
}

impl RegisterCarrierRebaseArguments<'_> {
    fn pairs(self) -> [RawPair; soma_abi::register::Entry::CarrierRebase.buffer_pairs()] {
        [
            self.old_carriers.raw(),
            self.fresh_carriers.raw(),
            self.old_lanes.raw(),
            self.new_lanes.raw(),
            self.requests.raw(),
            self.completions.raw(),
            self.params.raw(),
        ]
    }
}

/// The exact `scope_register` entry.
pub struct RegisterScopeKernel<'m>(Function<'m>);

impl RegisterScopeKernel<'_> {
    pub fn linear_launch(&self, census: LaunchCensus, work: u64) -> Result<LinearLaunch> {
        self.0.linear_launch(census, work)
    }

    pub fn launch(
        &self,
        grid: Dim3,
        block: Dim3,
        arguments: RegisterScopeArguments<'_>,
    ) -> Result<()> {
        launch_pairs(&self.0, grid, block, &arguments.pairs())
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

    pub fn launch(
        &self,
        grid: Dim3,
        block: Dim3,
        arguments: RegisterScopeSurfaceArguments<'_>,
    ) -> Result<()> {
        launch_pairs(&self.0, grid, block, &arguments.pairs())
    }
}

/// The exact `register_own_recast` entry.
pub struct RegisterRecastKernel<'m>(Function<'m>);

impl RegisterRecastKernel<'_> {
    pub fn linear_launch(&self, census: LaunchCensus, work: u64) -> Result<LinearLaunch> {
        self.0.linear_launch(census, work)
    }

    pub fn launch(
        &self,
        grid: Dim3,
        block: Dim3,
        arguments: RegisterRecastArguments<'_>,
    ) -> Result<()> {
        launch_pairs(&self.0, grid, block, &arguments.pairs())
    }
}

/// The exact `register_own_recast_finish` entry.
pub struct RegisterRecastFinishKernel<'m>(Function<'m>);

impl RegisterRecastFinishKernel<'_> {
    pub fn linear_launch(&self, census: LaunchCensus, work: u64) -> Result<LinearLaunch> {
        self.0.linear_launch(census, work)
    }

    pub fn launch(
        &self,
        grid: Dim3,
        block: Dim3,
        arguments: RegisterRecastArguments<'_>,
    ) -> Result<()> {
        launch_pairs(&self.0, grid, block, &arguments.pairs())
    }
}

/// The exact `register_carrier_rebase` entry.
pub struct RegisterCarrierRebaseKernel<'m>(Function<'m>);

impl RegisterCarrierRebaseKernel<'_> {
    pub fn linear_launch(&self, census: LaunchCensus, work: u64) -> Result<LinearLaunch> {
        self.0.linear_launch(census, work)
    }

    pub fn launch(
        &self,
        grid: Dim3,
        block: Dim3,
        arguments: RegisterCarrierRebaseArguments<'_>,
    ) -> Result<()> {
        launch_pairs(&self.0, grid, block, &arguments.pairs())
    }
}

impl Module {
    pub fn register_scope(&self) -> Result<RegisterScopeKernel<'_>> {
        self.function(soma_abi::register::Entry::Scope.symbol())
            .map(RegisterScopeKernel)
    }

    pub fn register_scope_surface(&self) -> Result<RegisterScopeSurfaceKernel<'_>> {
        self.function(soma_abi::register::Entry::ScopeSurface.symbol())
            .map(RegisterScopeSurfaceKernel)
    }

    pub fn register_recast(&self) -> Result<RegisterRecastKernel<'_>> {
        self.function(soma_abi::register::Entry::Recast.symbol())
            .map(RegisterRecastKernel)
    }

    pub fn register_recast_finish(&self) -> Result<RegisterRecastFinishKernel<'_>> {
        self.function(soma_abi::register::Entry::RecastFinish.symbol())
            .map(RegisterRecastFinishKernel)
    }

    pub fn register_carrier_rebase(&self) -> Result<RegisterCarrierRebaseKernel<'_>> {
        self.function(soma_abi::register::Entry::CarrierRebase.symbol())
            .map(RegisterCarrierRebaseKernel)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span<T>(pointer: u64, elements: usize) -> RegisterSpan<'static, T> {
        RegisterSpan {
            pointer,
            elements,
            _borrow: PhantomData,
        }
    }

    #[test]
    fn scope_pair_order_is_the_kernel_signature() {
        let arguments = RegisterScopeArguments {
            standing: span(1, 101),
            owns: span(2, 102),
            carriers: span(3, 103),
            bytes: span(4, 104),
            lanes: span(5, 105),
            counts: span(6, 106),
            params: span(7, 107),
            radiation: span(8, 108),
            completion: span(9, 109),
            statuses: span(10, 110),
        };
        assert_eq!(
            arguments.pairs(),
            core::array::from_fn(|at| RawPair {
                pointer: (at + 1) as u64,
                elements: at + 101,
            })
        );
        let surface = RegisterScopeSurfaceArguments {
            common: arguments,
            contact_words: span(11, 111),
        };
        assert_eq!(
            surface.pairs()[10],
            RawPair {
                pointer: 11,
                elements: 111
            }
        );
    }

    #[test]
    fn recast_pair_order_is_shared_by_both_ordered_entries() {
        let arguments = RegisterRecastArguments {
            old_owns: span(1, 11),
            fresh_owns: span(2, 12),
            old_lanes: span(3, 13),
            new_lanes: span(4, 14),
            requests: span(5, 15),
            completions: span(6, 16),
            params: span(7, 17),
        };
        assert_eq!(
            arguments.pairs(),
            core::array::from_fn(|at| RawPair {
                pointer: (at + 1) as u64,
                elements: at + 11,
            })
        );

        let carrier = RegisterCarrierRebaseArguments {
            old_carriers: span(1, 11),
            fresh_carriers: span(2, 12),
            old_lanes: span(3, 13),
            new_lanes: span(4, 14),
            requests: span(5, 15),
            completions: span(6, 16),
            params: span(7, 17),
        };
        assert_eq!(
            carrier.pairs(),
            core::array::from_fn(|at| RawPair {
                pointer: (at + 1) as u64,
                elements: at + 11,
            })
        );
    }
}
