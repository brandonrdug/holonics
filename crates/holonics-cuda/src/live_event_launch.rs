//! Typed CUDA launch mouth for one contemporary live-current event.
//!
//! **Every launch here crosses [`crate::launch_law`].**  Each entry declares its argument names,
//! residency, element width and access read off the kernel's own signature in
//! `accelerators/cuda-kernel/src/lib.rs`, and the shape is proved before any driver call.  The
//! single-current entry is an exact one-thread cover; the population entry is a guarded cover over
//! the material's own current population; the regional-contact entry is a guarded cover at the
//! entry's declared cooperative block.  The two mouths that receive no device census prove every
//! arithmetic, function and residency clause and **name the deferred device clauses in the
//! receipt** rather than assuming a grid aperture.

use core::marker::PhantomData;

use crate::launch_law::{
    Access, ArgumentRequirement, ArgumentSpan, BlockConstraint, Extent, LaunchEvidence, LaunchLimits,
    LaunchReceipt, LaunchRequirement, LaunchShape, LawfulLaunch, ScalarArgument, ScalarRequirement,
    ScalarWidth,
};
use crate::{CudaError, DeviceBuffer, Dim3, Function, Module, Result};

fn boundary(context: &'static str, message: impl Into<String>) -> CudaError {
    CudaError {
        code: -1,
        name: String::from("LIVE_EVENT_LAUNCH_BOUNDARY"),
        message: message.into(),
        context,
    }
}

/// **One typed device span a live-event entry *reads*.**  `Copy`, because read spans may alias one
/// another; it can only ever be presented as an [`Access::Read`] argument.
#[derive(Clone, Copy)]
pub struct LiveEventSpan<'a, T> {
    pointer: u64,
    elements: usize,
    _borrow: PhantomData<&'a DeviceBuffer<T>>,
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

    /// The span's element population.
    pub const fn elements(&self) -> usize {
        self.elements
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

/// **One typed device span a live-event entry *writes*.**
///
/// [definition] D2's `DeviceWriteSpan` exclusivity, carried into the live-event launchers: it
/// holds `PhantomData<&'a mut DeviceBuffer<T>>` and is neither `Copy` nor `Clone`, so a second
/// write span or any read span of the same allocation is a compile error while it lives.
pub struct LiveEventWriteSpan<'a, T> {
    pointer: u64,
    elements: usize,
    _borrow: PhantomData<&'a mut DeviceBuffer<T>>,
}

impl<'a, T: Copy> LiveEventWriteSpan<'a, T> {
    /// Borrow a whole allocation exclusively for writing.
    pub fn whole(buffer: &'a mut DeviceBuffer<T>) -> Self {
        Self {
            pointer: buffer.device_ptr(),
            elements: buffer.len(),
            _borrow: PhantomData,
        }
    }

    /// Borrow an exact prefix of an allocation exclusively for writing.
    pub fn prefix(buffer: &'a mut DeviceBuffer<T>, elements: usize) -> Result<Self> {
        if elements > buffer.len() {
            return Err(boundary(
                "LiveEventWriteSpan::prefix",
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

    /// The span's element population.
    pub const fn elements(&self) -> usize {
        self.elements
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

/// The eleven arguments of `lineage_event` and `lineage_event_population`, in the exact order and
/// with the exact `*const`/`*mut` character of the kernel's own signature.  `control` is declared
/// as whole `CONTROL_WORDS` rows because the kernel itself silently returns when that extent is
/// wrong — the launch law turns that silence into a construction refusal.
fn live_event_argument_law() -> Vec<ArgumentRequirement> {
    vec![
        ArgumentRequirement::device("standing", Access::Read, 4, Extent::Any),
        ArgumentRequirement::device(
            "control",
            Access::Write,
            4,
            Extent::Rows(holonics_portable::wire::live_event_cuda::CONTROL_WORDS),
        ),
        ArgumentRequirement::device("relations", Access::Read, 4, Extent::Any),
        ArgumentRequirement::device(
            "owns",
            Access::Write,
            core::mem::size_of::<holonics_portable::manifold::SparseOwnCell>(),
            Extent::Any,
        ),
        ArgumentRequirement::device("carriers", Access::Write, 4, Extent::Any),
        ArgumentRequirement::device("overflow_nodes", Access::Write, 4, Extent::Any),
        ArgumentRequirement::device("overflow_counts", Access::Write, 4, Extent::Any),
        ArgumentRequirement::device("directed_events", Access::Read, 4, Extent::Any),
        ArgumentRequirement::device("directed_contacts", Access::Write, 4, Extent::Any),
        ArgumentRequirement::device("emissions", Access::Write, 4, Extent::Any),
        ArgumentRequirement::device("emanation", Access::Write, 4, Extent::Any),
    ]
}

/// The five buffer arguments of `regional_contacts`.  The `standing_axis` scalar sits between the
/// first pair and the second; it is a declared [`ScalarRequirement`]
/// (`regional_contact_scalar_law`) so the parameter block is generated from the proved receipt
/// rather than assembled by hand at the call site.
///
/// `work * DIRECTED_CONTACT_WORDS` is checked: `work` is derived from a caller-presented device
/// extent, so its product with the row width is hostile input and a wrapping multiply here would
/// declare a *smaller* contact extent than the kernel writes.
fn regional_contact_argument_law(work: usize) -> Result<Vec<ArgumentRequirement>> {
    let contact_words = work
        .checked_mul(holonics_portable::wire::live_event_cuda::DIRECTED_CONTACT_WORDS)
        .ok_or_else(|| {
            boundary(
                "regional contact CUDA work extent",
                format!(
                    "{work} rows of {} contact words overflow usize",
                    holonics_portable::wire::live_event_cuda::DIRECTED_CONTACT_WORDS
                ),
            )
        })?;
    Ok(vec![
        ArgumentRequirement::device("standing", Access::Read, 4, Extent::Any),
        ArgumentRequirement::device("receiver", Access::Read, 4, Extent::Any),
        ArgumentRequirement::device(
            "directed_events",
            Access::Read,
            4,
            Extent::Rows(holonics_portable::wire::live_event_cuda::DIRECTED_EVENT_WORDS),
        ),
        ArgumentRequirement::device(
            "directed_contacts",
            Access::Write,
            4,
            Extent::Exactly(contact_words),
        ),
        ArgumentRequirement::device("statuses", Access::Write, 4, Extent::Exactly(work)),
    ])
}

/// `regional_contacts` declares one scalar, `standing_axis`, after its first buffer pair.
fn regional_contact_scalar_law() -> Vec<ScalarRequirement> {
    vec![ScalarRequirement::at("standing_axis", ScalarWidth::U32, 1)]
}

/// `lineage_event_population` declares one trailing scalar, `count`, after all eleven pairs.
fn live_event_population_scalar_law() -> Vec<ScalarRequirement> {
    vec![ScalarRequirement::trailing("count", ScalarWidth::U64, 11)]
}

/// The eleven faces of `lineage_event` and `lineage_event_population`, `*const` ones as shared
/// spans and `*mut` ones as exclusive spans.  Neither `Copy` nor `Clone`: one argument population
/// is one exclusive borrow of each written allocation.
pub struct LiveEventArguments<'a> {
    pub standing: LiveEventSpan<'a, u32>,
    pub control: LiveEventWriteSpan<'a, u32>,
    pub relations: LiveEventSpan<'a, u32>,
    pub owns: LiveEventWriteSpan<'a, holonics_portable::manifold::SparseOwnCell>,
    pub carriers: LiveEventWriteSpan<'a, u32>,
    pub overflow_nodes: LiveEventWriteSpan<'a, u32>,
    pub overflow_counts: LiveEventWriteSpan<'a, u32>,
    pub directed_events: LiveEventSpan<'a, u32>,
    pub directed_contacts: LiveEventWriteSpan<'a, u32>,
    pub emissions: LiveEventWriteSpan<'a, u32>,
    pub emanation: LiveEventWriteSpan<'a, u32>,
}

impl LiveEventArguments<'_> {
    fn spans(&self) -> [ArgumentSpan; 11] {
        [
            self.standing.argument("standing"),
            self.control.argument("control"),
            self.relations.argument("relations"),
            self.owns.argument("owns"),
            self.carriers.argument("carriers"),
            self.overflow_nodes.argument("overflow_nodes"),
            self.overflow_counts.argument("overflow_counts"),
            self.directed_events.argument("directed_events"),
            self.directed_contacts.argument("directed_contacts"),
            self.emissions.argument("emissions"),
            self.emanation.argument("emanation"),
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
    /// Enact `count` currents in one crossing, returning the receipt it earned.  The shape is
    /// derived from the device evidence the caller declares and the entry's own lowered block cap
    /// and then proved.  It took a bare `LaunchCensus`, so it deferred the three clauses a census
    /// cannot carry whether or not the caller held the card; the
    /// trailing `count` scalar is declared on the requirement and supplied by name, so the
    /// parameter block comes out of the receipt.
    pub fn launch(
        &self,
        evidence: LaunchEvidence<'_>,
        arguments: LiveEventArguments<'_>,
        count: usize,
    ) -> Result<LaunchReceipt> {
        if count == 0 {
            return Err(boundary(
                "live event population extent",
                "a contemporary population carries one or more currents",
            ));
        }
        let limits = LaunchLimits::from_evidence(evidence, &self.0)?;
        let requirement = LaunchRequirement::guarded(
            holonics_portable::wire::live_event_cuda::POPULATION_ENTRY_SYMBOL,
            count as u64,
            live_event_argument_law(),
        )
        .with_scalars(live_event_population_scalar_law());
        let spans = arguments.spans();
        LawfulLaunch::cover(&requirement, &limits, &spans)?.enact(
            &self.0,
            None,
            &[ScalarArgument::new("count", count as u64)],
        )
    }
}

/// The five buffer faces and the one declared scalar of `regional_contacts`.
pub struct RegionalContactArguments<'a> {
    pub standing: LiveEventSpan<'a, u32>,
    pub standing_axis: u32,
    pub receiver: LiveEventSpan<'a, u32>,
    pub directed_events: LiveEventSpan<'a, u32>,
    pub directed_contacts: LiveEventWriteSpan<'a, u32>,
    pub statuses: LiveEventWriteSpan<'a, u32>,
}

pub struct RegionalContactKernel<'m>(Function<'m>);

impl LiveEventKernel<'_> {
    pub fn local_size_bytes(&self) -> Result<usize> {
        self.0.local_size_bytes()
    }

    /// The single-current entry acts on lane zero alone, so its declared cover is **exact**: one
    /// element, one thread, no guarded tail.  The caller declares the device evidence it holds, so
    /// the device clauses are proved when it holds a census and deferred — by the caller's own
    /// statement, not silently — when it declares [`LaunchEvidence::FunctionOnly`].
    pub fn launch(
        &self,
        evidence: LaunchEvidence<'_>,
        arguments: LiveEventArguments<'_>,
    ) -> Result<LaunchReceipt> {
        let limits = LaunchLimits::from_evidence(evidence, &self.0)?;
        let requirement = LaunchRequirement::exact(
            holonics_portable::wire::live_event_cuda::ENTRY_SYMBOL,
            1,
            Dim3::x(1),
            live_event_argument_law(),
        );
        let spans = arguments.spans();
        let shape = LaunchShape {
            grid: Dim3::x(1),
            block: Dim3::x(1),
            shared_bytes: 0,
        };
        LawfulLaunch::prove(&requirement, &limits, shape, &spans)?.enact(&self.0, None, &[])
    }
}

/// The cooperative block width `regional_contacts` is written for.  It is a property of the
/// entry, declared here and proved against the lowered function's own cap — never a device limit.
const REGIONAL_CONTACT_BLOCK: u32 = 128;

impl RegionalContactKernel<'_> {
    /// Prove and issue the regional-contact launch, returning the receipt it earned.
    ///
    /// The declared element extent is the directed-event row population; the coverage, block,
    /// argument and access clauses are proved before any driver call.  `standing_axis` is a
    /// **declared scalar** at parameter-block position one, so the whole parameter array — every
    /// pointer, every extent and the scalar — is generated from the proved receipt rather than
    /// assembled by hand.  The device clauses are proved from whatever evidence the caller
    /// declares.
    pub fn launch(
        &self,
        evidence: LaunchEvidence<'_>,
        arguments: RegionalContactArguments<'_>,
    ) -> Result<LaunchReceipt> {
        let row_words = holonics_portable::wire::live_event_cuda::DIRECTED_EVENT_WORDS;
        let directed_elements = arguments.directed_events.elements();
        if directed_elements == 0 || !directed_elements.is_multiple_of(row_words) {
            return Err(boundary(
                "regional contact CUDA work extent",
                "the directed population must contain one or more whole rows",
            ));
        }
        let work = directed_elements / row_words;
        let limits = LaunchLimits::from_evidence(evidence, &self.0)?;
        let requirement = LaunchRequirement {
            block: BlockConstraint::exactly(Dim3::x(REGIONAL_CONTACT_BLOCK)),
            ..LaunchRequirement::guarded(
                holonics_portable::wire::live_event_cuda::REGIONAL_CONTACT_ENTRY_SYMBOL,
                work as u64,
                regional_contact_argument_law(work)?,
            )
        }
        .with_scalars(regional_contact_scalar_law());
        let spans = [
            arguments.standing.argument("standing"),
            arguments.receiver.argument("receiver"),
            arguments.directed_events.argument("directed_events"),
            arguments.directed_contacts.argument("directed_contacts"),
            arguments.statuses.argument("statuses"),
        ];
        LawfulLaunch::cover(&requirement, &limits, &spans)?.enact(
            &self.0,
            None,
            &[ScalarArgument::new(
                "standing_axis",
                arguments.standing_axis as u64,
            )],
        )
    }
}

impl Module {
    pub fn lineage_event(&self) -> Result<LiveEventKernel<'_>> {
        self.function(holonics_portable::wire::live_event_cuda::ENTRY_SYMBOL)
            .map(LiveEventKernel)
    }

    pub fn lineage_event_population(&self) -> Result<LiveEventPopulationKernel<'_>> {
        self.function(holonics_portable::wire::live_event_cuda::POPULATION_ENTRY_SYMBOL)
            .map(LiveEventPopulationKernel)
    }

    pub fn regional_contacts(&self) -> Result<RegionalContactKernel<'_>> {
        self.function(holonics_portable::wire::live_event_cuda::REGIONAL_CONTACT_ENTRY_SYMBOL)
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

    fn write_span<T>(pointer: u64, elements: usize) -> LiveEventWriteSpan<'static, T> {
        LiveEventWriteSpan {
            pointer,
            elements,
            _borrow: PhantomData,
        }
    }

    #[test]
    fn span_order_is_the_kernel_signature() {
        let arguments = LiveEventArguments {
            standing: span(1 << 20, 101),
            control: write_span(2 << 20, 102),
            relations: span(3 << 20, 103),
            owns: write_span(4 << 20, 104),
            carriers: write_span(5 << 20, 105),
            overflow_nodes: write_span(6 << 20, 106),
            overflow_counts: write_span(7 << 20, 107),
            directed_events: span(8 << 20, 108),
            directed_contacts: write_span(9 << 20, 109),
            emissions: write_span(10 << 20, 110),
            emanation: write_span(11 << 20, 111),
        };
        let names = [
            "standing",
            "control",
            "relations",
            "owns",
            "carriers",
            "overflow_nodes",
            "overflow_counts",
            "directed_events",
            "directed_contacts",
            "emissions",
            "emanation",
        ];
        for (at, presented) in arguments.spans().iter().enumerate() {
            assert_eq!(presented.name(), names[at]);
            assert_eq!(presented.address(), ((at as u64) + 1) << 20);
            assert_eq!(presented.elements(), at + 101);
        }
    }

    /// The declared law and the presented spans agree name for name, width for width and access
    /// for access; the accesses are the kernel's own `*const`/`*mut` character.
    #[test]
    fn the_declared_live_event_law_matches_the_presented_spans() {
        let law = live_event_argument_law();
        assert_eq!(law.len(), 11);
        assert_eq!(law[0].access, Access::Read);
        assert_eq!(law[2].access, Access::Read);
        assert_eq!(law[7].access, Access::Read);
        assert_eq!(law[1].access, Access::Write);
        assert_eq!(
            law[3].element_bytes,
            core::mem::size_of::<holonics_portable::manifold::SparseOwnCell>()
        );
        // `control` is declared as whole CONTROL_WORDS rows; a short control face is a refusal
        // rather than a kernel that silently returns.
        assert!(law[1]
            .extent
            .eq(&Extent::Rows(holonics_portable::wire::live_event_cuda::CONTROL_WORDS)));
    }

    /// The regional-contact entry's result extents are declared against its work, so a mismatched
    /// contact or status population is a construction refusal.
    #[test]
    fn the_regional_contact_law_ties_its_results_to_its_work() {
        let law = regional_contact_argument_law(7).expect("7 rows is a lawful work extent");
        assert_eq!(law.len(), 5);
        assert_eq!(
            law[3].extent,
            Extent::Exactly(7 * holonics_portable::wire::live_event_cuda::DIRECTED_CONTACT_WORDS)
        );
        assert_eq!(law[4].extent, Extent::Exactly(7));
        assert_eq!(
            law[2].extent,
            Extent::Rows(holonics_portable::wire::live_event_cuda::DIRECTED_EVENT_WORDS)
        );
    }
}
