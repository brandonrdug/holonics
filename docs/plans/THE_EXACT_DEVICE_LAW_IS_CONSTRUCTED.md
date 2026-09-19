# The exact device law is constructed

[definition] This is a construction contract subordinate to [THE_ROADMAP](THE_ROADMAP.md). It
states the engineering intentions for how the carrier's operations are realized on device, and what
is extracted from exterior GPU technology into our own construction. External toolchains are
reference and comparison material; the device law we execute is built here.

## What exists

[established-bounded; source-inspected] Sixty-nine top-level kernel files, about fourteen thousand
lines, compiled to PTX by `nvcc` from [`build.rs`](../../crates/holonic-engine/build.rs), with a
further eleven headers under `kernels/refine_shell/`. The virtual architecture is read off the
mounted device rather than authored, falling back to a declared floor and saying so aloud through a
build warning. Sixty-five of the sixty-nine top-level files contain no floating type at all: `exact_integer.cuh` carries multi-limb signed-magnitude integers with an explicit
overflow flag and widening to a 128-bit signed coefficient. The hot operation is exact integer and
interval arithmetic with branch-on-exact-comparison, not numerical tensor work.

[established-bounded; source-inspected] `kernels/field_source_reflection.cuh` factors the scalar,
shared-section forward and fixed-D joint adjoint entry points into one application of the same map,
with `producer.rs::pushforward` and `::pullback` carrying the forward and pullback of a single
`R_D = 2 P_D - I`.
The cross-check comparing the collective covector against the independent host pullback is present
and ignored, so that identity is source-verified and unmeasured.

## The arithmetic-regime split

[definition] Irregular exact work and dense regular work want different abstractions, and the
boundary is named here rather than rediscovered later. Exact integer and interval law — carry
propagation, early exit on exact comparison, topology decided by a branch — stays in the explicit
single-instruction-multiple-thread form where indexing, residency and refusal are ours. Dense
regular tensor work, should any be constructed, belongs to a tile-shaped abstraction where
partition determines layout. Neither regime is permitted to silently adopt the other's tooling, and
no exterior scheduler may decide a committed current, topology, coefficient or branch.

## What is extracted

[definition] **D1 — The launch is a passage and owes a receipt.** A kernel declares the grid, block,
shared-memory and residency it requires; the call site proves it. The architecture discipline in
`build.rs` already does exactly this for one property, read off the device and spoken; extending it
from architecture to launch shape makes an unlawful launch a construction error rather than a
runtime surprise.

[established-bounded; formal-checked; implemented-exact] **D1 is Returned.** Owners:
[`crates/holonic-mount/src/launch_law.rs`](../../crates/holonic-mount/src/launch_law.rs) with
[its tests](../../crates/holonic-mount/src/launch_law/tests.rs), paired with
[`DeviceLaunchLaw.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/DeviceLaunchLaw.lean)
(`Soma.Holonics.Foundation.DeviceLaunchLaw`); each cites the other by declaration name. A
`LaunchRequirement` declares the element extent, the coverage relation, the block constraint, the
dynamic shared surface **as a function of the block shape**, and every argument's name, residency,
element width, access and extent. Constructing a `LawfulLaunch` proves, with checked arithmetic
throughout, that the offered `LaunchShape` covers the declared extent exactly or with a guarded
tail below one block, that every block, grid, shared and per-dimension bound holds, that
`grid.x * block.x` fits the kernel's `u32` stride wire and the thread product fits `u64`, that each
argument's residency, element width, extent, address and octet product are as declared, and that no
writable argument aliases another of the same residency. An unlawful launch is a typed
`LaunchRefusal` naming exactly one violated `LaunchClause`, raised before any driver call; a lawful
one returns a `LaunchReceipt` carrying the kernel, shape, extents, guard, stride, shared extent,
stream, the proved arguments and scalars, and the clause list. **No bound is authored.** `LaunchLimits::read` takes every limit from
`cuDeviceGetAttribute` and `cuFuncGetAttribute`; `from_census` completes an existing
`Device::launch_census`; `from_function` carries only the lowered entry's own caps. A bound the
caller's evidence does not carry is **deferred and named in the receipt**, never defaulted — the
literals 1024 and 65535 appear nowhere in the owner outside `cfg(test)` fixtures. The Lean side
carries `cover_covers`, `cover_tail`, `threads_lt_wire`, `guarded_of_le` and `foldl_guarded_cover`,
the last proving that a covering guarded launch over `range (grid * block)` yields *exactly* the
unguarded effect over `range extent`. The one-thread-per-element correspondence is stated at two
strengths and the Rust doc table now says which is which: `exists_unique_thread` is the **weak**
form (a declared element is named by one *flat* index below the thread population — near
tautological, since `Fin s.threads` is by construction `[0, s.threads)`), and the content-carrying
forms quantify over the launch's own linearization
`LaunchShape.linearIndex = blockIdx * blockDim + threadIdx`: `linear_thread_bijective` proves that
map is a **bijection** onto `[0, n)` under an exact cover, and `linear_thread_injective_guarded`
proves it is injective under a guarded cover, that every declared element is named exactly once,
and that the in-range guard turns off **exactly** `threads - n` threads — the tail the Rust receipt
records as `guard_threads`, accounted for rather than assumed small. Negative tests
cover zero extent, grid past the device aperture, `u32` stride and `u64` thread-product overflow,
`usize` overflow in an argument's octet extent, an undersized buffer, a wrong residency, a
shared-memory mismatch, a block past the lowered function cap, an argument count/name mismatch, a
null device address, a misdeclared argument access, a scalar declared past the entry's buffer
pairs, and both over- and under-covering shapes. Mount's four launcher modules
(`register_launch.rs`, `live_event_launch.rs`, `register_recast.rs`, `register_carrier.rs`) are
migrated onto it; the raw `Function::launch` family in `cuda.rs` is left in place for the engine's
own callers. `#print axioms` on every main theorem returns only `propext`, `Classical.choice` and
`Quot.sound`.

Evidence after the second and third passes below: **106 cpu tests, 5 device tests and 5 doctests**
pass for `mount` on the mounted RTX 4080 SUPER, where the law reads grid `2147483647x65535x65535`,
block `1024x1024x64`, 49152 shared octets per block and a 32-lane warp off the card;
`mount-register-gate` (1031 device launches across five runs, EXACT) and
`mount-register-remount-gate` (EXACT) pass through the migrated path, both now on
`LaunchEvidence::Device` with a declared extent and both asserting that the receipt **deferred
nothing at all** rather than that it proved two named clauses. Clippy is clean in every file this
owner touches.

[established-bounded; implemented-exact] **D1 second pass — what the review found and what now
holds.** Six defects in the returned D1 are repaired, and the guarantee is restated to match the
mechanism rather than the intention.

* **The enactment no longer accepts a caller-built parameter array.** `LawfulLaunch::enact` was
  `pub` and took `params: &mut [*mut c_void]`, so a caller could prove one launch and enact a
  different one. There is now exactly one public enactment,
  `enact(function, stream, scalars: &[ScalarArgument])`, and it **generates** the whole CUDA
  parameter block from the receipt: each proved address and element extent, with every declared
  scalar emitted at the parameter-block position its `ScalarRequirement` names. Scalars are part of
  the requirement and of the receipt (`ScalarRequirement::at { name, width, after_arguments }`,
  `ScalarReceipt`), so `regional_contacts`' interleaved `standing_axis` — the one entry that
  previously assembled its array by hand — and `lineage_event_population`'s trailing `count` are
  both built from the receipt. A scalar presented under an unknown name, in the wrong order, or
  past its declared width is a `LaunchClause::ScalarArguments` refusal.
* **`LawfulLaunch` is no longer `Clone`, and is `#[must_use]`.** One proof, one enactment: `enact`
  consumes `self`, and a cloneable proof could have issued two launches over spans the aliasing
  audit proved disjoint *within one* launch only.
* **A declared-versus-presented access mismatch has its own clause.** It was reported as
  `ArgumentAliasing`, which is a different fault; it is now `LaunchClause::ArgumentAccess`.
* **`ArgumentSpan` is no longer authorable.** Its fields are private with accessors, and
  `ArgumentSpan::device_raw` — a safe `pub const fn` over public fields whose precondition (a live,
  mapped device range) is not checkable — is `pub(crate)`. The public constructors all take the
  address and extent from a live borrow.
* **A completely proved receipt is a different type from a deferred one.** `LaunchReceipt`'s clause
  lists are private (so a receipt is always one this owner issued, and cannot be edited into
  looking complete), and `LaunchReceipt::fully_proved()` returns `Option<FullyProvedReceipt>`,
  whose only constructor refuses a receipt carrying any deferred clause; `proof_scope()` is the
  total split into `FullyProvedReceipt` / `DeferredReceipt`. A consumer that needs the complete
  proof can now say so in its signature.
* **The device evidence a mouth holds is declared, not defaulted.** The five `.launch(grid, block,
  arguments)` mouths of `register_launch.rs` silently used `LaunchLimits::from_function` and a
  `Coverage::Undeclared` requirement, so they deferred coverage *and every device clause* without
  the caller ever choosing to, and then discarded the receipt. They now take
  `launch(evidence: LaunchEvidence, grid, block, extent, arguments)` and return the receipt.
  `LaunchEvidence` is `Device(&Device) | Census(LaunchCensus) | FunctionOnly`, so a mouth offered
  no device reading says so as the caller's own declaration. The same parameter is threaded into
  `LiveEventKernel::launch` and `RegionalContactKernel::launch`.

**The public argument and signature types changed**, and the earlier claim that they did not is
corrected here: the launcher output structs had already gained receipt fields; the `.launch(…)`
mouths now take the declared evidence and extent and return `LaunchReceipt`; and, under D2's second
pass, every `*mut` face takes an exclusive span type rather than the `Copy` shared one. Every
caller in `crates/holonic-mount` (both gate binaries, `register_recast.rs`, `register_carrier.rs`)
and in `crates/holonic-life` (`src/live_current_cuda/executor.rs`, three call sites) is migrated;
`crates/holonic-life/src/live_current_cuda/` was clean in the working tree, so it was migrated
rather than given a shared-span compatibility entry.

[established-bounded; implemented-exact] **D1 third pass — the census deferral is closed: no
production mouth defers any clause.** The former `[open]` named `BlockDimensionWithinDevice`,
`SharedWithinDevice` and `BlockWarpMultiple` as deferred at every mouth crossed with
`LaunchEvidence::Census`, and offered two ways to close it. The second is taken, because it needs no
new census field and because the deferral was never about what a card *can* report — it was about a
call site holding a card and presenting a summary of it. **Every one of those mouths now presents
`LaunchEvidence::Device`.** The covering mouths were the obstacle: `RegisterScopeKernel::cover`,
`RegisterRecastKernel::cover`, `RegisterRecastFinishKernel::cover` and
`RegisterCarrierRebaseKernel::cover` took a bare `LaunchCensus` rather than the declared evidence
their `launch` siblings already took, so they deferred those three whatever the caller held; they
now take `LaunchEvidence`, as do `launch_register_own_recast`, `launch_register_carrier_rebase` and
`LiveEventPopulationKernel::launch`. `mount-register-gate` and `mount-register-remount-gate` thread
their own `&Device` to the five register mouths, and `CudaLiveCurrentExecutor` retains the `Device`
it already took at mount and presents it at all three live-event mouths (the `LaunchCensus` it also
retains is now only the source of the reported multiprocessor population, and its dead
`device_census` accessor is removed). Both gates assert `receipt.is_fully_proved()` in place of the
two named clauses and both still pass EXACT. `LaunchEvidence::Census` and
`LaunchEvidence::FunctionOnly` remain in the law — they are the honest declarations for a caller
that holds no card, and `launch_law/tests.rs` still exercises the deferral they produce — but no
production path in `crates/holonic-mount` or `crates/holonic-life` takes them. The remaining
`[open]` of the former paragraph, growing `LaunchCensus` by the three readings, is **not** done and
is not needed for any present caller; it stays available for a future caller that must pass a
summary across a boundary a `&Device` cannot cross.

[definition] **D2 — Exclusive access is a type.** One continuing ecology has one move owner, and
that rule holds at thread granularity. Per-thread exclusive spans are currently enforced by
convention and review; expressing them as a type carries the ownership law the repository already
states for Holons down into device memory, and makes aliasing a refusal rather than a defect.

[established-bounded; formal-checked; implemented-exact] **D2 is Returned.** Same paired owners as
D1. A `DisjointPartition` is constructed only from a proof-carrying description — a uniform
stride/width form (`width <= stride`, `regions * stride <= span`, checked) or an explicit offsets
table validated exactly as monotone and in bounds — so that `region(i) ∩ region(j) = ∅` for
`i ≠ j` and `⋃ region(i) ⊆ span`; `verify_pairwise_disjoint` witnesses both executably. The Lean
counterparts are `DisjointPartition`, `uniform`, `ofOffsets`, `offsets_mono`, `region_disjoint` and
`region_subset`. `verify_pairwise_disjoint` does this without quadratic work over a caller-declared region
population: for the two address-ordered forms, checking each **adjacent** pair *is* the complete
proof (that is exactly the Lean `separated` field `i < j → hi i ≤ lo j`, with `offsets_mono` the
statement that adjacent validation implies the general ordering), and for an injective scatter the
complete check is that the sorted address list has no repeat. The quadratic all-pairs comparison is
retained as a `cfg(test)` reference and a test holds the two against each other on every fixture,
so the linear argument is not taken on trust.
Exclusivity is carried by the borrow checker: `DeviceWriteSpan` holds
`PhantomData<&'a mut DeviceBuffer<T>>` and is neither `Copy` nor `Clone`, so a `DeviceReadSpan` of
the same allocation cannot coexist with it — a `compile_fail` doctest proves that refusal is a
compile error. Where the borrow checker sees only one backing borrow, because several spans are
carved out of one allocation, `AliasAudit` supplies the construction-time half: read spans may
alias one another, a writable span may alias nothing of the same residency, and the audit runs
inside every `LawfulLaunch::prove`. The launch's write borrow is tied to stream synchronization
rather than to the host call, and the **mechanism** by which that holds is stated below rather
than asserted: `PartitionedWrite::scope(&mut self, on, |open| …)` is the `std::thread::scope`
shape, and it is the only shape in which the release is a type-level guarantee. The same
discipline `crates/holonic-engine/src/streamed_standing.rs` applies to a pinned slot, whose
`PinnedHost::as_mut_octets` takes `&mut self` and is taken only after the copy that last read the
slot has completed. No accessor producing `&mut [T]` from `&self` exists or is introduced. The deleted
accessor is `PinnedHost::as_octets_unchecked`, an `unsafe fn(&self) -> &mut [u8]` whose doc
comment asked the caller to have proved by construction that no copy was reading the slot; it is
removed in the working tree and nothing of that shape is reintroduced here, because the proof it
asked for in prose is exactly what `DeviceWriteSpan` and `PartitionedWrite::scope` carry in types. Race freedom is proved at two strengths and the docstrings and this paragraph
now say which is which. **The coarse theorem** is `DisjointPartition.raceFree`: thread updates
under a disjoint partition commute (`write_right_comm`), so any *permutation of the threads* yields
the same final device state, with `foldl_write_mem` / `foldl_write_notMem` pinning that state down
exactly rather than merely consistently. It models a thread as **one atomic write over its whole
region**, which is not what a kernel does. **The fine theorem** is
`DisjointPartition.shuffleWrites_eq_sequential`, added in the second pass: a `Store` is one
single-address write, a thread's program is a *list* of them all addressed inside its own region
(`Programmed`), an interleaving is any merge of those lists preserving each thread's internal order
(`Interleaves`, stated as: filtering the merged list by thread recovers that thread's list), and
the theorem proves the final state equals the one the **sequential** schedule leaves —
`raceFreeInterleaved` for any two interleavings, `foldl_store_apply` pinning the state down exactly
(at every address, what the last store there wrote). The earlier docstring said "any interleaving
of the threads" while modelling atomic whole-region writes under permutation; that gap is closed.
The executable witness applies the per-region writes in forward, reverse and shuffled
order and asserts one final state. The declared per-argument `Access` values in the migrated
launchers are **read off the kernels' own `*const`/`*mut` signatures** in
`accelerators/cuda-kernel/src/lib.rs`, not guessed, and are asserted against the presented spans by
test.

[established-bounded; formal-checked; implemented-exact] **D2 second pass — the borrow-release
guarantee is now real, and D2 reaches the launchers that ship.** The review found two defects.

* **`InFlightWrite` guaranteed nothing.** It had no `Drop` and was not `#[must_use]`, so
  `drop(in_flight)` — with no `settle()` — released the exclusive write borrow immediately while
  the kernel might still be running, after which the buffer could be re-spanned or freed. The
  module doc and this plan both claimed the borrow was released only by stream synchronization;
  that was false as a type-level guarantee. **A `Drop` impl alone would not have fixed it**:
  `mem::forget` ends a borrow statically without running `Drop` (the scoped-thread
  "leakpocalypse"). The repair is the closure-scoped form, `PartitionedWrite::scope(&mut self, on,
  |open| …)`. What it guarantees, and by what mechanism: the exclusive borrow of the allocation is
  the `&mut self` held for the whole of `scope`'s **own** frame, so the allocation cannot be
  re-spanned, read-spanned, moved or dropped between the first enqueued launch and `scope`'s
  return; `scope` does not return until the apparatus has been synchronized, propagating the
  driver's error on the ordinary path and waiting via a guard **in its own frame** on an unwind;
  and there is **no caller-held value whose forgetting could end the borrow early**. The closure
  receives an `OpenWrite`, and because the closure's return type is fixed before the handle's
  lifetime is chosen, nothing borrowed from it escapes. `in_flight(on)` survives as an explicitly
  weaker escape hatch: `#[must_use]`, with a `Drop` that synchronizes (silently, never panicking)
  as a second line, documented as defeated by `mem::forget`. What the apparatus is asked to
  synchronize on is a **sealed** `Settles` trait whose only implementors outside `cfg(test)` are
  `Stream` and `Context`, so no caller can substitute a no-op. Four `compile_fail` doctests carry
  the receipts — the allocation cannot be re-spanned (`E0500`), read-spanned (`E0502`) or dropped
  (`E0505`) while a scope is open — together with a **positive control** that compiles, because
  `rustdoc` does not in fact enforce the error code written after `compile_fail` and a stale import
  would otherwise pass unnoticed. The settle discipline is now tested at all: waits exactly once
  and after the closure, propagates the apparatus's failure, and still waits on an unwind.
* **The shipped launchers had no compile-time write exclusivity.** `RegisterSpan` and
  `LiveEventSpan` were `Clone + Copy` with `PhantomData<&'a T>` and were used for `Access::Write`
  arguments, so `DeviceWriteSpan`'s exclusivity — described in this paragraph in the same breath as
  those launchers — did not reach them, leaving `AliasAudit`, a within-one-launch check, as the
  only guard. D2 is now carried into them: a `*const` face takes the `Copy` shared span, and a
  `*mut` face takes `RegisterWriteSpan` / `LiveEventWriteSpan`, which hold
  `PhantomData<&'a mut DeviceBuffer<T>>` and are neither `Copy` nor `Clone`. The argument structs
  lose `Copy`/`Clone` accordingly, and every written device allocation in both gate binaries, in
  `register_recast.rs` / `register_carrier.rs`, and at the three `holonic-life` call sites is bound
  `mut` and borrowed exclusively for the launch that writes it.

[definition] **D3 — Partition generates layout.** The shared-section work already performs, by
hand and per kernel, a gather by region incidence into a local source, a shared local material
application, and a transposed scatter. That is a tile abstraction specialized to exact arithmetic.
The intention is one general owner in which declared incidence generates the gather, residency and
scatter, so that a new section operator is a declaration rather than another hand-written kernel.

[established-bounded; formal-checked; implemented-exact] **The seam D2 hands D3 is exact, and it is
the scatter arm.** The gather arm needs nothing new: a gather reads, read spans may alias, and
`DisjointPartition` already expresses an incidence-indexed read. The scatter arm splits on one
property of the index map. Through an **injective** map the writes are disjoint and the final state
is order-independent (`DisjointPartition.scatter_perm`), and
`DisjointPartition::scatter(.., ScatterLaw::Injective)` admits exactly that case, refusing a
colliding table and naming the colliding pair. Through a **non-injective** map with plain stores the
final state is order-*dependent*; this is not a conservatism but a counterexample,
`DisjointPartition.scatter_order_dependent`, and its executable witness shows two interleavings of
three threads leaving 30 and 10 in the same slot. Such a scatter is admissible only under a
declared associative-commutative accumulation, where order-independence is restored for **any**
index map, injective or not (`DisjointPartition.scatterAdd_perm`), which is what
`ScatterLaw::Accumulated` declares. D3's general owner therefore owes, per declared incidence, one
of exactly two receipts on its scatter arm: an injectivity proof over the incidence table, or a
named accumulation whose associativity and commutativity are themselves stated — and for this
construction the accumulation must be exact (an integer or interval sum, a max), because a
floating-point accumulation is not associative and would make the scatter order-dependent again
through the back door. Neither receipt is implied by the gather or by the local application, so the
incidence declaration that generates the layout must carry it.

[established-bounded; formal-checked; implemented-exact] **D3 is Returned**, at the scope stated
here. Owners:
[`crates/holonic-mount/src/section_layout.rs`](../../crates/holonic-mount/src/section_layout.rs)
with [its tests](../../crates/holonic-mount/src/section_layout/tests.rs), paired with
[`SectionLayout.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/SectionLayout.lean)
(`Soma.Holonics.Foundation.SectionLayout`); each cites the other by declaration name, and the shared
device wire is `soma_abi::section_layout_cuda`. **The declaration is an `IncidenceDeclaration`** — a
global address extent, a strictly increasing offsets table and a flat region-major address table —
and everything else is derived from it: the gather index table (which *is* the address table), the
`TileExtents` (region and slot populations, the widest region, the common width when there is one,
and the dynamic shared octets as a checked function of the tile), the `LaunchRequirement` of each
arm, the `DisjointPartition` of each write span, the transposed scatter table, and — for an
accumulating scatter — the region colouring. Validation is exact and complete: the extent is
positive and inside the `u32` index wire the entries read, the offsets table starts at zero and
ends exactly at the address table's length, no region is empty, every address is below the declared
extent, and every region and slot population fits its wire; each failure is a `SectionRefusal`
naming one `SectionClause` and the offending slot or region. **No allocation is sized by a declared
number**: the two tables arrive by value, so their lengths are facts about the caller's own
allocations, and the transpose is built by *sorting* the `(address, slot)` pairs rather than by a
counting sort indexed by the declared global extent, which would have been exactly such an
allocation.

[established-bounded; implemented-exact] **The scatter receipt is exactly one of two, and there is
no third.** `ScatterRequest` has two constructors and no default, so a declaration must say which
claim it is making. `ScatterRequest::Injective` is verified exactly against the generated transpose
and a collision is refused **naming both slots and the shared address**;
`ScatterRequest::Accumulated(law)` carries a named exact accumulation. A non-injective incidence
with no accumulation cannot be constructed. **A floating accumulation is refused by type, not by a
check**: `AccumulationLaw` has `IntegerAdd` (exact `ℤ` in `i64`, refusing rather than wrapping) and
`ModularAdd { modulus }`, and no variant names a float — the Lean owner states every law over a
`CommSemiring`, and floating addition is not associative. `AccumulationLaw::IntegerAdd` is host
only and says so: a kernel cannot raise the overflow refusal that law owes, so `SectionKernels::enact`
refuses it with `SectionClause::AccumulationOnDevice` rather than wrapping silently.

[established-bounded; formal-checked] **The mathematics.** The Lean owner proves, over any
commutative semiring: `Incidence.adjoint`, that **scatter is the transpose of gather**
(`⟨gather x, y⟩ = ⟨x, scatterAdd y⟩`) — the law that makes the generated scatter table *the*
transpose rather than a second authored map; `Incidence.assembled_apply`, that
`scatterAdd ∘ applyLocal ∘ gather` **is** the assembled global operator applied as a matrix;
`Incidence.assembled_sum_regions`, that this matrix is `Σ_r P_rᵀ L_r P_r`, the finite-element
assembly identity, when the local operator is block diagonal over the regions;
`Incidence.assembled_symm` (with `symm_of_blocks`), that it is symmetric when every local block is;
`Incidence.scatterAdd_of_injective`, that through an injective incidence the accumulation degenerates
to a plain store; and the two colouring statements — `Incidence.colour_schedule`, that launching
colour class by colour class, each adding its own partial scatter into the running device state,
leaves exactly `σ + scatterAdd y`, the sequential result, and
`Incidence.colour_fiber_single_region`, that under a proper colouring two slots of one colour
reaching one address belong to the same region, so each colour launch is an *injective* scatter and
`DeviceLaunchLaw.DisjointPartition.scatter_perm` governs it internally. `#print axioms` on all nine
returns only `propext`, `Classical.choice` and `Quot.sound`. On the Rust side
`SectionLayout::verify_adjoint` witnesses the adjoint identity executably, and
`SectionLayout::apply_reference` — the exact CPU reference for the whole generated operator — is
tested against `SectionLayout::assemble_dense`, which builds the global matrix by the **textbook
assembly loop** (for each region, for each local `(j, k)`, add `L[j][k]` at
`(addr(lo+j), addr(lo+k))`) and never through the gather/scatter machinery. The dense assembly's
`n²` allocation is bounded by a declared `entry_ceiling` checked before a single element is
allocated.

[established-bounded; implemented-exact] **The device realization.** Four new nvptx entries in
[`accelerators/cuda-kernel/src/lib.rs`](../../accelerators/cuda-kernel/src/lib.rs) — `section_gather`,
`section_apply`, `section_scatter_store`, `section_scatter_add` — compiled into the committed PTX
artifact and validated by `ptxas -arch=sm_89`. The arithmetic is `Z/(2^61 - 1)`, a Mersenne prime
chosen so the whole ring operation is exact with no division: a 128-bit product folds back by shift
and mask. `soma_abi::section_layout_cuda::{add, mul, reduce}` is **one mouth** — the same code
`accelerators/cuda-kernel` compiles for nvptx and `ModularWords::DEVICE` dispatches to on the host —
so the bit-for-bit agreement below is a property of one piece of code, not of two transcriptions;
a cpu test additionally holds it against the ordinary 128-bit remainder path. `section_apply` runs
one block per region, staging the region's tile into **dynamic shared memory** and barriering once
before the local matvec; rustc has no attribute placing a `static` in address space 3, so the tile
is declared `.extern .shared` at module scope through `global_asm!` and reached with
`cvta.shared.u64`, which is what CUDA C's `extern __shared__` lowers to. Every launch crosses the
D1 law with `LaunchEvidence::Device` and returns a `FullyProvedReceipt` — a deferred receipt is
refused, not reported — and every write span is opened through D2's `PartitionedWrite::scope` bound
to **the partition generated from the incidence**: the uniform-stride (or offsets) partition for the
gather and apply arms, the injective-scatter partition for an injective scatter, and one
injective-scatter partition per colour class for an accumulating one. **No atomic appears in any of
the four bodies.** That is the colouring's work: within a colour class each global address has
exactly one writing thread, so the accumulating read-modify-write is not a race, and successive
colours are successive stream-ordered launches whose composition is the sequential scatter. The
colouring is computed exactly by greedy colouring of the region conflict graph, which is never
materialized — it is read through the generated transpose — and its cost `Σ_a deg(a)²` is computed
with checked arithmetic and compared against a declared ceiling **before the colouring loop runs**,
so an incidence concentrating every slot on one address is a `WorkCeiling` refusal rather than an
exhausted machine. `RegionColouring::verify_proper` witnesses the Lean `Proper` predicate
executably in `O(slots log slots)`, never by a quadratic comparison over a declared region
population.

[established-bounded; implemented-exact] **Device evidence and measured cost.** On the mounted
RTX 4080 SUPER the device result equals the exact CPU reference **bit for bit** on all four cases,
and every receipt deferred nothing. `mount` cannot take the engine's own contact complex: the engine
already depends on `mount`, so a dependency either way — including a dev-dependency — would be a
cycle through the crate this owner lives in; case (c) therefore builds an *equivalent* irregular
incidence in the test (ragged widths, unordered addresses inside a region, uneven address
multiplicity, regions sharing addresses with several others), and that substitution is stated rather
than implied. Costs are host `Instant` wall time in a **debug-profile** test binary, with the clocks
named and separated: *setup* is the context, the `Module::load_ptx` of the whole soma PTX, entry
resolution, colouring, table staging and the source upload; *resident execution* is
`SectionKernels::enact`, which is the three arms plus one scatter launch per colour and includes
each arm's stream synchronization and excludes the readback; *readout* is the device-to-host copy of
the global field; *end to end* spans all of it. Setup is dominated by loading the entire committed
PTX module, not by anything this owner generates.

Two runs are reported rather than one, because a single wall-clock reading of a debug binary
is not a measurement of anything stable: setup moves by tens of percent between runs and the
resident clock by a third, which is what the two columns say aloud.

| case | regions | slots | extent | tile | shared | colours | setup | resident | readout | end to end |
|---|---|---|---|---|---|---|---|---|---|---|
| (a) 1D chain of overlapping tiles | 512 | 8192 | 5126 | 16 | 128 B | 2 | 56.40 / 26.35 ms | 6.10 / 4.60 ms | 26.3 / 38.8 µs | 62.52 / 30.99 ms |
| (b) 2D grid, 4-neighbour overlap | 3844 | 19220 | 4096 | 5 | 40 B | 7 | 45.19 / 37.07 ms | 13.88 / 15.50 ms | 49.4 / 24.9 µs | 59.12 / 52.59 ms |
| (c) irregular contact incidence | 1024 | 4094 | 4096 | 6 | 48 B | 6 | 21.88 / 23.86 ms | 2.98 / 2.89 ms | 42.3 / 37.6 µs | 24.90 / 26.79 ms |
| injective control | 512 | 4096 | 4096 | 8 | 64 B | — | 18.87 / 19.84 ms | 1.02 / 1.11 ms | 35.1 / 18.3 µs | 19.93 / 20.97 ms |

Evidence: **106 cpu tests, 5 device tests and 5 doctests** pass for `mount`; `cargo build -p
holonic-engine -p life` is clean; `mount-register-gate` and `mount-register-remount-gate` are EXACT;
`lake build` returns only the three admissible axioms. Clippy is clean in every file this owner
writes or changes.

[definition] **The migration map: which hand-written section kernels are instances of the generated
triple.** The engine's kernels are another session's uncommitted work and are **not touched here**;
this is the declaration each would become when that work lands. Read with the correction that
`section` in those file names means *resident section* — a batched row set in global scratch — and
not shared memory: of the four kernels D3 was framed against, none uses `__shared__`, and the true
shared-tile population is a different, larger file set.

* **`normal_enclosure_ports.cuh` · `section_normal_enclosure_scatter_section`** — the one true
  index-map scatter in the set, and the cleanest instance. Incidence: one destination row per source
  row, `destination = d[row] * count`, with `d` a declared `ResidentSection` of width 1. Local
  operator: the identity restricted to the window `[start, start + count)` — a coordinate projection,
  `L = I`. Receipt: `ScatterRequest::Injective`. Its collision policy *is* D3's, arrived at
  independently — a duplicate destination is refused, never accumulated — but it is enforced at run
  time on device by an occupancy flag in the unpublished hi buffer, non-atomically, under a thread-0
  guard; the generated receipt refuses the same table **at construction**, names the colliding pair,
  and needs no flag, no serialization and no `REFUSED_MALFORMED` path. The sibling
  `section_normal_enclosure_restrict_section` is the same projection with an injective-by-row
  destination.

  [established-bounded; implemented-exact; measured] **This one is now declared and cross-checked,
  September 18**, in the engine's own crate against this owner's public declaration:
  [`crates/holonic-engine/src/section_layout_adoption.rs`](../../crates/holonic-engine/src/section_layout_adoption.rs)
  with [its tests](../../crates/holonic-engine/src/section_layout_adoption/tests.rs).
  `enclosure_scatter_incidence` returns the `IncidenceDeclaration` and `window_placement_operator`
  the local block; on the RTX 4080 SUPER the generated triple's device result equals its own exact
  reference bit for bit **and** equals, word for word, what
  `ResidentNormalEnclosureSection::scatter_components` wrote for the same four rows of engine
  enclosure material. **The correction the declaration forced:** a `(region, slot) → global index`
  incidence carries **one** address space, because the gather index *is* the address table and the
  scatter is its transpose. The engine's scatter maps a source section into a *different*
  destination field, so it is declared by embedding both in one extent — source section flat, then
  destination field — and putting the map inside the region's local block: region `r` is its source
  window followed by its destination window, `2·count` slots, and `L[count + j][j] = 1` is the
  window projection composed with the placement. A source→destination map is therefore not outside
  D3; it is a `2c × 2c` block on a common field, and the migration map's `L = I` above is the
  *shape* of the arm, not the block that realizes it. Two things the current generated ring does not
  carry are stated in the `[open]` paragraph below.
* **`exact_packet_linear.cuh`** — the cleanest instance of the *shared-tile* form. Incidence: a
  uniform affine row gather (region = row, width = the row length). Local operator: a dense matvec
  accumulated into `scratch[r]`, followed by `fibre_normalize`. Scatter: plain stores, injective by
  row. Its Hadamard variant is the same declaration with a diagonal `L`.
* **`coupled_constitutive_family.cuh`, `coupled_joint_compile.cuh`** — incidence: the direction
  incidence block `dirs = family + pk + 4`, which is already an address table. Local operator: the
  family's per-direction combination. Scatter: plain, injective.
* **`constitutive_context_section.cuh`, `constitutive_condition_contact.cuh`,
  `constitutive_condition_preimage.cuh`, `constitutive_condition_image.cuh`** — incidence: the
  column/condition-indexed gathers (`mixed = 2(ns + nc) + 2(column/2)·ns` and its siblings). Local
  operator: exact elimination or a dense `directions[j·c + n]` product. Scatter: plain, injective.
  These are instances of the triple's *shape*; their local arm is an elimination rather than a
  matvec, so they need a local-operator family wider than the dense table D3 carries today.
* **`field_reflection_target.cuh` · `section_field_reflection_target`** — incidence: **exactly an
  injective declaration**, the two-range map `at = j < d ? 2(4n + j) : 2(10n + j − d)`, which D3
  generates and proves injective at construction. Local arm: a per-coordinate dyadic-scaled residual
  interval `(t_j − y_j)/2^s` with an exact remainder and an outward-rounded radius — **not** a
  linear operator, so the incidence migrates and the local arm does not.
* **`field_source_reflection.cuh`** — the only genuine operator in the four: `R_D = 2 P_graph(D) − I`
  in resolvent form. Its selector is a *dense complex material map* `D` of shape `count × d`, not an
  incidence table, so the region is the whole section and the incidence is the identity on its
  addresses; the local operator is the cached LDL factor's solve. Expressible as a declaration, but
  the generic `section_apply` performs a dense matvec and would have to grow a factored-solve local
  arm.
* **`normal_material_section.cuh` · `section_normal_material_enclosed_batch`** — **not an instance,
  and named as such.** Its gather is through a table of raw *device pointers* (six `int64` per row:
  `x_lo, x_hi, x_off, y_lo, y_hi, y_off`), so the global address is a pointer plus an offset rather
  than an index into one field. A `(region, slot) → global index` declaration cannot express it
  without a base-pointer registry, which D3 does not have and which is the concrete absent object if
  this one is wanted.

[open] **What D3 does not yet carry.** Four things, each named rather than implied. **One local
operator per layout**: `LocalOperator` is a single dense `w × w` table shared by every region, which
is the "shared local material application" the plan describes and which the migration map shows is
what most of the candidate set wants — but `field_source_reflection`'s cached factor solve and
`normal_material_section`'s accumulated normal equations want a per-region operator *family* and a
richer local arm than a matvec. **One device ring**: the device arm realizes exactly
`Z/(2^61 - 1)`; the engine's kernels carry `__int128` multi-limb exact integers and interval
enclosures that publish a radius in their last slot, and the generated triple carries no enclosure
radius word. **`AccumulationLaw::IntegerAdd` has no device arm**, for the stated reason.
**The engine side is not migrated**, and cannot be from here: `mount` cannot depend on
`holonic-engine`, so adopting the triple is a change in the engine's own crate against this owner's
public declaration.

[open] **What the first engine-side declaration measured the ring gap to be.** The cross-check
above holds the coordinate arm exactly and names three obligations, each now a measured fact rather
than an expectation.

1. **The word, precisely.** The engine's coordinate is a 128-bit signed `wide` held as an `int64`
   low/high pair with a `REFUSED_CARRIER` overflow refusal; the generated arm is one `u64` in
   `Z/(2^61 - 1)`. They agree **bit for bit** exactly while a coordinate word is non-negative and
   below `2^61 - 1`, because a placement block is a permutation and no ring operation but `x·1 + 0`
   reaches a gathered word. Outside that window the generated arm folds a residue where the engine
   keeps an exact integer. What a general adoption owes is therefore **not a wider modulus** but a
   second device ring: signed 128-bit words carried as two device words, with the engine's own
   carrier refusal raised from the kernel. That is four new nvptx entries and a refusal slot in the
   generated triple's ABI, not a change to `ExactRing`'s host side, and it is **not** a contained
   change to `section_layout`.
2. **The radius is a second, accumulating address.** Every engine enclosure carries one radius word
   after its coordinates, and the scattered output's radius is the *sum of the participating source
   radii* — an address every region adds into, under exact integer addition with an overflow
   refusal. That is `AccumulationLaw::IntegerAdd`, which `SectionKernels::enact` refuses on device.
   So even the cleanest instance is, in full, an injective coordinate scatter **plus** one
   accumulating address whose law has no device arm; the declaration carries the coordinates and
   says so.
3. **One context, unresolved.** Enacting the generated triple inside the engine's adopted
   `ResidentReadout` context — same device, same thread, every receipt fully proved — leaves the
   gather arm's tile and the target field **entirely zero**; the identical call in a context from
   `mount::Context::create` reproduces the exact reference. The cross-check therefore uses its own
   context, and the cause is not identified. This is the first obstacle a real migration must
   clear, because a migrated kernel must share the engine's context with the engine's own.

[definition] **D4 — A generator may compile its own device law.** A generator is a situated
mathematical transformation, and a model that emits source is one application of that. A Holon that
assembles and compiles its device law at first use, with the emitted law carrying its source
relation, applicability and cost receipt, is the native reading of just-in-time kernel construction.
This is held as an intention with a stated obligation: the emitted law owes the same exactness,
refusal and receipt discipline as an authored kernel, and an emitted kernel that cannot state its
source relation is not admitted.

[definition] **D5 — Refusal remains ours.** Exterior kernel frameworks provide aliasing safety and
scheduling. They do not provide the refusals this construction depends on: a malformed enclosure, a
non-conserving event, an energy increase under zero source, a rational check that fails, a
disagreement between a collective and a per-row path. Those refusals are the mathematical content
and are written here regardless of what a toolchain checks.

## Measurement discipline

[definition] Report the actual operation and receiver: delivered faces, completed owner updates,
latency distribution, exact work and bit growth, memory, transfer and scoped information rate. Name
each clock and separate setup, resident execution, readout and end-to-end delivery. An ignored
cross-check is source evidence and not a measurement; promoting it requires running it and saying
so. Installed capacity and a vendor rating are not measured bandwidth or power.

## Immediate work

[definition] Un-ignore and measure the collective-versus-per-row adjoint cross-check, so the shared
`R_D` identity carries a measurement rather than an inspection. Then D1 and D2 against the existing
kernel set, since both are contracts over calls that already exist. D3 is Returned at the scope
stated above; its remaining work is the engine-side adoption named in its `[open]`, which belongs to
the crate that owns those kernels and whose first declaration and device cross-check now exist in
`holonic-engine::section_layout_adoption`. D4 remains an intention until a consuming construction asks for
it.
