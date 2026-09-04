//! Typed CUDA launch mouth for one contemporary live-current event.

use core::ffi::c_void;
use core::marker::PhantomData;

use crate::cuda::LaunchCensus;
use crate::{CudaError, DeviceBuffer, Dim3, Function, Module, Result};

fn boundary(context: &'static str, message: impl Into<String>) -> CudaError {
    CudaError {
        code: -1,
        name: String::from("LIVE_EVENT_LAUNCH_BOUNDARY"),
        message: message.into(),
        context,
    }
}

#[derive(Clone, Copy)]
pub struct LiveEventSpan<'a, T> {
    pointer: u64,
    elements: usize,
    _borrow: PhantomData<&'a T>,
}

impl<'a, T: Copy> LiveEventSpan<'a, T> {
    pub fn whole(buffer: &'a DeviceBuffer<T>) -> Self {
        Self {
            pointer: buffer.device_ptr(),
            elements: buffer.len(),
            _borrow: PhantomData,
        }
    }

    pub fn prefix(buffer: &'a DeviceBuffer<T>, elements: usize) -> Result<Self> {
        if elements > buffer.len() {
            return Err(boundary(
                "LiveEventSpan::prefix",
                format!(
                    "logical extent {elements} exceeds device allocation {}",
                    buffer.len()
                ),
            ));
        }
        Ok(Self {
            pointer: buffer.device_ptr(),
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

#[derive(Clone, Copy)]
pub struct LiveEventArguments<'a> {
    pub standing: LiveEventSpan<'a, u32>,
    pub control: LiveEventSpan<'a, u32>,
    pub relations: LiveEventSpan<'a, u32>,
    pub owns: LiveEventSpan<'a, body::manifold::SparseOwnCell>,
    pub carriers: LiveEventSpan<'a, u32>,
    pub overflow_nodes: LiveEventSpan<'a, u32>,
    pub overflow_counts: LiveEventSpan<'a, u32>,
    pub directed_events: LiveEventSpan<'a, u32>,
    pub directed_contacts: LiveEventSpan<'a, u32>,
    pub emissions: LiveEventSpan<'a, u32>,
    pub emanation: LiveEventSpan<'a, u32>,
}

impl LiveEventArguments<'_> {
    fn pairs(self) -> [RawPair; 11] {
        [
            self.standing.raw(),
            self.control.raw(),
            self.relations.raw(),
            self.owns.raw(),
            self.carriers.raw(),
            self.overflow_nodes.raw(),
            self.overflow_counts.raw(),
            self.directed_events.raw(),
            self.directed_contacts.raw(),
            self.emissions.raw(),
            self.emanation.raw(),
        ]
    }
}

pub struct LiveEventKernel<'m>(Function<'m>);

/// The co-present population mouth: one lane per current of one contemporary event.
pub struct LiveEventPopulationKernel<'m>(Function<'m>);

impl LiveEventPopulationKernel<'_> {
    pub fn local_size_bytes(&self) -> Result<usize> {
        self.0.local_size_bytes()
    }

    /// Enact `count` currents in **one** crossing, one lane each.
    ///
    /// **The launch shape is derived, never authored.** `Function::linear_launch` takes it from the
    /// function's own `CU_FUNC_ATTRIBUTE_MAX_THREADS_PER_BLOCK` and the device's census, folds X
    /// into Y when X saturates, and refuses rather than clipping. This mouth adds nothing to that:
    /// the work extent is `count`, which is the material's own population, and every per-current
    /// stride is derived inside the kernel as `len / count`.
    pub fn launch(
        &self,
        census: LaunchCensus,
        arguments: LiveEventArguments<'_>,
        count: usize,
    ) -> Result<()> {
        if count == 0 {
            return Err(boundary(
                "live event population extent",
                "a contemporary population carries one or more currents",
            ));
        }
        let launch = self.0.linear_launch(census, count as u64)?;
        let pairs = arguments.pairs();
        let mut values = Vec::with_capacity(pairs.len() * 2 + 1);
        for pair in pairs {
            values.push(pair.pointer);
            values.push(u64::try_from(pair.elements).map_err(|_| {
                boundary(
                    "live event CUDA argument extent",
                    "a buffer extent exceeds its 64-bit ABI word",
                )
            })?);
        }
        values.push(count as u64);
        let mut arguments: Vec<*mut c_void> = values
            .iter_mut()
            .map(|value| value as *mut u64 as *mut c_void)
            .collect();
        self.0.launch(launch.grid, launch.block, &mut arguments)
    }
}

#[derive(Clone, Copy)]
pub struct RegionalContactArguments<'a> {
    pub standing: LiveEventSpan<'a, u32>,
    pub standing_axis: u32,
    pub receiver: LiveEventSpan<'a, u32>,
    pub directed_events: LiveEventSpan<'a, u32>,
    pub directed_contacts: LiveEventSpan<'a, u32>,
    pub statuses: LiveEventSpan<'a, u32>,
}

pub struct RegionalContactKernel<'m>(Function<'m>);

impl LiveEventKernel<'_> {
    pub fn local_size_bytes(&self) -> Result<usize> {
        self.0.local_size_bytes()
    }

    pub fn launch(&self, arguments: LiveEventArguments<'_>) -> Result<()> {
        let pairs = arguments.pairs();
        let mut values = Vec::with_capacity(pairs.len() * 2);
        for pair in pairs {
            values.push(pair.pointer);
            values.push(u64::try_from(pair.elements).map_err(|_| {
                boundary(
                    "live event CUDA argument extent",
                    "a buffer extent exceeds its 64-bit ABI word",
                )
            })?);
        }
        let mut arguments: Vec<*mut c_void> = values
            .iter_mut()
            .map(|value| value as *mut u64 as *mut c_void)
            .collect();
        self.0.launch(Dim3::x(1), Dim3::x(1), &mut arguments)
    }
}

impl RegionalContactKernel<'_> {
    pub fn launch(&self, arguments: RegionalContactArguments<'_>) -> Result<()> {
        let standing = arguments.standing.raw();
        let receiver = arguments.receiver.raw();
        let directed = arguments.directed_events.raw();
        let contacts = arguments.directed_contacts.raw();
        let statuses = arguments.statuses.raw();
        let row_words = soma_abi::live_event_cuda::DIRECTED_EVENT_WORDS;
        if directed.elements == 0 || directed.elements % row_words != 0 {
            return Err(boundary(
                "regional contact CUDA work extent",
                "the directed population must contain one or more whole rows",
            ));
        }
        let work = directed.elements / row_words;
        if contacts.elements != work * soma_abi::live_event_cuda::DIRECTED_CONTACT_WORDS
            || statuses.elements != work
        {
            return Err(boundary(
                "regional contact CUDA result extent",
                "contact and status populations must match the directed work",
            ));
        }
        let block = 128u32;
        let work = u32::try_from(work).map_err(|_| {
            boundary(
                "regional contact CUDA work extent",
                "the contact population exceeds the one-dimensional grid",
            )
        })?;
        let grid = work
            .checked_add(block - 1)
            .map(|extent| extent / block)
            .ok_or_else(|| {
                boundary(
                    "regional contact CUDA work extent",
                    "the contact grid overflows",
                )
            })?;

        let mut standing_pointer = standing.pointer;
        let mut standing_elements = standing.elements as u64;
        let mut standing_axis = arguments.standing_axis;
        let mut receiver_pointer = receiver.pointer;
        let mut receiver_elements = receiver.elements as u64;
        let mut directed_pointer = directed.pointer;
        let mut directed_elements = directed.elements as u64;
        let mut contact_pointer = contacts.pointer;
        let mut contact_elements = contacts.elements as u64;
        let mut status_pointer = statuses.pointer;
        let mut status_elements = statuses.elements as u64;
        let mut params = [
            &mut standing_pointer as *mut u64 as *mut c_void,
            &mut standing_elements as *mut u64 as *mut c_void,
            &mut standing_axis as *mut u32 as *mut c_void,
            &mut receiver_pointer as *mut u64 as *mut c_void,
            &mut receiver_elements as *mut u64 as *mut c_void,
            &mut directed_pointer as *mut u64 as *mut c_void,
            &mut directed_elements as *mut u64 as *mut c_void,
            &mut contact_pointer as *mut u64 as *mut c_void,
            &mut contact_elements as *mut u64 as *mut c_void,
            &mut status_pointer as *mut u64 as *mut c_void,
            &mut status_elements as *mut u64 as *mut c_void,
        ];
        self.0.launch(Dim3::x(grid), Dim3::x(block), &mut params)
    }
}

impl Module {
    pub fn lineage_event(&self) -> Result<LiveEventKernel<'_>> {
        self.function(soma_abi::live_event_cuda::ENTRY_SYMBOL)
            .map(LiveEventKernel)
    }

    pub fn lineage_event_population(&self) -> Result<LiveEventPopulationKernel<'_>> {
        self.function(soma_abi::live_event_cuda::POPULATION_ENTRY_SYMBOL)
            .map(LiveEventPopulationKernel)
    }

    pub fn regional_contacts(&self) -> Result<RegionalContactKernel<'_>> {
        self.function(soma_abi::live_event_cuda::REGIONAL_CONTACT_ENTRY_SYMBOL)
            .map(RegionalContactKernel)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span<T>(pointer: u64, elements: usize) -> LiveEventSpan<'static, T> {
        LiveEventSpan {
            pointer,
            elements,
            _borrow: PhantomData,
        }
    }

    #[test]
    fn pair_order_is_the_kernel_signature() {
        let arguments = LiveEventArguments {
            standing: span(1, 101),
            control: span(2, 102),
            relations: span(3, 103),
            owns: span(4, 104),
            carriers: span(5, 105),
            overflow_nodes: span(6, 106),
            overflow_counts: span(7, 107),
            directed_events: span(8, 108),
            directed_contacts: span(9, 109),
            emissions: span(10, 110),
            emanation: span(11, 111),
        };
        assert_eq!(
            arguments.pairs(),
            core::array::from_fn(|at| RawPair {
                pointer: (at + 1) as u64,
                elements: at + 101,
            })
        );
    }
}
