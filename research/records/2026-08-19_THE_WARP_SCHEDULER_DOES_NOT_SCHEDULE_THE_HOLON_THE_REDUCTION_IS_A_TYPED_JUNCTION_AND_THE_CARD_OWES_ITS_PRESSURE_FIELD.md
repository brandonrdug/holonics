# The warp scheduler does not schedule the holon, the reduction is a typed junction, and the card owes its pressure field

**Date:** 2026-08-19
**Kind:** foundational hardware-surface audit and mathematical derivation. Evidence for the
replacement construction blueprint; this record promotes no executable station.
**Truth discipline:** **established-bounded** for inspected code, artifacts, hardware census and the
bounded live-process sample; **proved-standard** for documented CPU/CUDA execution semantics and
elementary parallel algebra; **proved-derived** for algebra first derived here; **interpretation**
for the holonic pressure/lightning correspondence; **conditional** for proposed realization
contracts; **open** for unbuilt joins.

## Primary external sources

**Truth status: established-bounded.**

1. NVIDIA, [CUDA programming
   model](https://docs.nvidia.com/cuda/cuda-programming-guide/01-introduction/programming-model.html).
2. NVIDIA, [CUDA hardware
   multithreading](https://docs.nvidia.com/cuda/cuda-programming-guide/03-advanced/advanced-kernel-programming.html).
3. NVIDIA, [CUDA compute-capability
   tables](https://docs.nvidia.com/cuda/cuda-programming-guide/05-appendices/compute-capabilities.html).
4. NVIDIA, [Nsight Compute Profiling
   Guide](https://docs.nvidia.com/nsight-compute/ProfilingGuide/).
5. NVIDIA, [RTX 4080 SUPER
   specifications](https://www.nvidia.com/en-us/geforce/graphics-cards/40-series/rtx-4080-family/).
6. Rust, [native operating-system
   threads](https://doc.rust-lang.org/stable/std/thread/index.html) and
   [available_parallelism](https://doc.rust-lang.org/std/thread/fn.available_parallelism.html).
7. Linux kernel, [fair scheduler
   design](https://docs.kernel.org/scheduler/sched-design-CFS.html).

Standing repository doctrine and owners: THE_SURFACES_ARE_PATHS, TABLET_THE_CAUSAL_PROFILE,
TABLET_THE_FLOW, TABLET_THE_MANIFOLD, TABLET_THE_TURN, TABLET_THE_COMPRESSION, hardware_cover,
interchange, exact_work, receiver_current, front_passage, resident_section, resident_law,
analytic_field, traversible_chain, running_integral, leader_quadrature,
receiver_exact_compression and reconstruction_fiber.

---

## 0. Verdict

**Truth status: established-bounded.**

The repaired Phoenix passage solved a correctness failure: one source-layer operation complex is
captured as a CUDA graph, launched once, synchronized once and returned once, without CPU semantic
dispatch between its graph nodes. Stations A through D returned genuine bounded artifacts.

It did **not** solve hardware utility:

- the tower is 42 source-layer graphs plus a final graph, with CPU construction, mount, bind,
  launch, synchronization, inspection and release at every boundary;
- the exact contraction gives one output coordinate to one CUDA thread and performs the complete
  inner product serially inside that thread;
- no Tensor Core, WMMA, CUTLASS, cuBLAS, cooperative inner-dimension tiling or multi-device
  collective is present;
- the launch rule chooses the largest legal whole-warp block, not a resource/occupancy/extent
  receiver;
- graph permission proves that nodes may overlap, not that the device actually overlapped them;
- the Station D dissection replayed a complete base tower, a complete determinism tower and a
  complete tower for every intervention sibling.

The scientific Station D atlas stands inside its declared midpoint receiver. The hardware
realization does not license Station E, native morphology, condensation, cultivation, frozen
runtime, or the mathematics-codec deed.

**Truth status: conditional.**

The correction is not a Scheduler, Planner, Interpreter, SurfaceManager or global pressure score.
It is the composition of existing front, cover, interchange, work, current, reflection and
compression owners into two missing returns:

1. a **typed tensor/section partition and reduction receipt**; and
2. a **surface utility and local pressure-field receipt**.

---

## 1. The hardware actually present

**Truth status: established-bounded.**

Measured locally on 2026-08-19:

~~~sh
lscpu
lscpu -e=CPU,CORE,SOCKET,NODE,CACHE,ONLINE,MAXMHZ
nvidia-smi --query-gpu=name,compute_cap,memory.total,clocks.max.sm,clocks.max.memory,power.limit,pstate,pcie.link.gen.current,pcie.link.width.current --format=csv,noheader,nounits
nvidia-smi topo -m
nvcc --version
~~~

| apparatus face | returned declaration |
|---|---|
| CPU | AMD Ryzen 9 7900X |
| physical CPU cores | 12 |
| logical CPU lanes | 24, SMT 2 |
| L3 domains | two 32 MiB domains |
| NUMA nodes | one |
| GPU | NVIDIA GeForce RTX 4080 SUPER |
| compute capability | 8.9 |
| SMs | 80 |
| warp width | 32 |
| GPU memory | 16,376 MiB reported |
| link | PCIe generation 4, width 16 |
| driver / CUDA | 595.71.05 / 13.2 |

NVIDIA documents 10,240 CUDA cores and 16 GB GDDR6X for this card. Compute capability 8.9 admits
at most 1,536 resident threads and 48 resident warps per SM, 64K 32-bit registers per SM, and
100 KiB shared memory per SM. These are ceilings, not achieved occupancy.

Neither Nsight Systems nor Nsight Compute is installed. NVIDIA-SMI supplies only a coarse receiver;
it cannot return eligible/issued warps, register pressure, shared-memory occupancy, instruction mix,
cache misses, atomic serialization or kernel overlap.

---

## 2. Three schedulers were being called one thing

### 2.1 Causal topology

**Truth status: definition.**

Let the admitted operation complex be

\[
\mathcal C=(V,E,\mathsf P,\mathsf W,\mathsf R),
\tag{H.1}
\]

where \(V\) are occurrences, \(E\) typed predecessor bonds, \(\mathsf P\) ports,
\(\mathsf W\) exact work and \(\mathsf R\) the receiver family. One depth receiver is

\[
d(v)=
\begin{cases}
0,&\operatorname{pred}(v)=\varnothing,\\
1+\max_{u\prec v}d(u),&\text{otherwise},
\end{cases}
\qquad
F_k=\{v:d(v)=k\}.
\tag{H.2}
\]

The \(F_k\) are causal fronts. A front is not a worker count, launch batch or transformer layer.

### 2.2 Apparatus realization

**Truth status: definition.**

The hardware cover maps each front cell, with full extent and read/write footprint, onto an
apparatus chart. CUDA streams/events realize dependency edges. Grid and block dimensions realize a
kernel's local population. This is a cover of one deed, never its semantic authority.

### 2.3 Physical issue

**Truth status: proved-standard.**

CUDA assigns blocks to SMs in unspecified order. Each block is partitioned into 32-thread warps.
A hardware warp scheduler chooses an **eligible** warp whose next instruction, operands and
execution unit are ready. The program does not select the warp or its issuing cycle.

~~~text
Eros owns                  graph/apparatus owns          NVIDIA hardware owns
causal incidence           streams and events           block-to-SM assignment
typed fronts               grid/block geometry          eligible-warp selection
junction/reconvergence     barriers and reductions      instruction issue/interleave
receiver return            graph launch boundary        cache/memory arbitration
~~~

Schedule::CoPresent permits overlap by withholding unnecessary graph edges. Schedule::Serialized
adds validation edges. Neither controls the physical warp scheduler.

---

## 3. What the live Phoenix realization does

### 3.1 The bounded repair that stands

**Truth status: established-bounded.**

ResidentSurface creates one origin stream, one lane stream and one event per occurrence, uploads
the predecessor lineage, captures semantic and census kernels, instantiates the graph, launches
once, synchronizes once and reads one census population. A kernel reads only declared predecessor
slots. Equal return under co-present and serialized controls tests semantic interchange; it does
not measure physical overlap.

### 3.2 The tower boundary is still a CPU foreman

**Truth status: established-bounded.**

~~~text
for each of 42 source layers:
    construct material plan on CPU
    authenticate/admit material
    read and mount that layer's maps
    build and instantiate one CUDA graph
    launch and synchronize it
    parse census and requested faces
    release residual/K/V standing
    free that layer's maps
then construct and launch the final graph
~~~

The residual and K/V standing stay on the card, so this is not CPU arithmetic fallback. But the CPU
still determines the next semantic macro-occurrence and waits at every layer. Station C measured
43 graph launches and 43 synchronizations per input.

### 3.3 The contraction is output-parallel and inner-serial

**Truth status: established-bounded.**

The kernel computes

\[
y_{t,o}=\sum_{i=0}^{K-1}W_{o,i}x_{t,i}
\tag{H.3}
\]

by assigning one \((t,o)\) coordinate to one CUDA thread. That thread loops through all \(K\)
coordinates in an integer-wide accumulator. Therefore:

- outputs are parallel but the inner/K axis is serial inside each thread;
- a warp reads different weight rows at the same \(i\), separated by the row stride;
- one input row is reread for every output instead of cooperatively staged;
- short prompts expose too few warps to hide wide-integer and memory latency on 80 SMs.

No tensor accelerator appears. The carrier is signed 64-bit interval endpoints with 128-bit
products and directed rounding.

### 3.4 The launch derivation proves legality, not utility

**Truth status: established-bounded.**

DerivedLaunch takes

\[
b=
\left\lfloor
\frac{\min(b_{\mathrm{device}},b_{\mathrm{kernel}})}{w}
\right\rfloor w.
\tag{H.4}
\]

This removes an authored 256 and produces a legal whole-warp block on this card. It ignores
registers/thread, shared memory/block, resident blocks/SM, total work, eligible warps, memory
coalescence, atomic contention and the constitutive tile. For a hypothetical function admitting
fewer threads than one warp, the current max(1) times warp spelling may exceed the admitted limit.

---

## 4. The bounded live-process sample

**Truth status: established-bounded.**

During Station D, a ten-second NVIDIA-SMI sample returned GPU SM activity from 0 to 32 percent and
reported memory activity from 0 to 4 percent. At the inspected point:

~~~sh
nvidia-smi dmon -s pucm -d 1 -c 10
ps -L -p PID -o pid,tid,psr,pcpu,stat,wchan:32,comm
cat /proc/PID/io
cat /proc/PID/sched
~~~

- the process held five OS threads, with one carrying almost all user computation;
- approximately 22 GB had been read from storage;
- the active thread was allowed on all 24 logical CPUs;
- its scheduler record showed 1,912 CPU migrations in roughly 65 seconds;
- GPU residency repeatedly fell to a few hundred MiB between layer deeds.

This is not a kernel profile. It is consistent with repeated source read, map mount, graph bind,
launch, synchronization and release and refutes a claim of continuous card saturation.

Station D constructs one complete base, a second complete base for determinism, and one complete
tower per intervention sibling. The atlas is useful; immutable prefixes and weights were not shared
as apparatus work.

---

## 5. Threads do not automatically weave results together

**Truth status: proved-standard.**

Control-flow reconvergence and mathematical recombination are distinct.

- A diverged warp may reconverge at a later instruction; no values are added by that event.
- A block-local join requires shared memory/warp exchange and a barrier/reduction.
- A grid-wide join requires atomics, cooperative structure or another kernel.
- A graph-wide join requires dependency edges and a consumer kernel.

The resident path uses block tree reductions for RMS/contact, integer OR/MAX/ADD atomics for census
faces and graph events for cross-kernel predecessors. Atomics testify only for the exact
commutative/associative receiver they implement. Their contention order is not path lineage.

---

## 6. Tensor partition is a geometric decomposition

### 6.1 Disjoint output partition

**Truth status: proved-standard.**

For \(O=\bigsqcup_aO_a\),

\[
y_{O_a}=W_{O_a,:}x,
\qquad
y=\bigoplus_a\iota_a y_{O_a}.
\tag{H.5}
\]

Outputs are disjoint. Their gluing is direct sum/concatenation after address and port agreement.

### 6.2 Inner/K partition

**Truth status: proved-standard.**

For \(K=\bigsqcup_aK_a\),

\[
y^{(a)}=W_{:,K_a}x_{K_a},
\qquad
y=\sum_aT_{a\to y}y^{(a)}.
\tag{H.6}
\]

Every partition writes the same logical output. It owes a junction carrying:

- every \(K_a\) coordinate region;
- each partial interval/limb population;
- the rebase \(T_{a\to y}\);
- fixed reduction tree or certified commutative quotient;
- intermediate widths, overflow and directed rounding;
- dependency span, traffic, obstruction and remainder lineage.

### 6.3 Row, branch and attention partitions

**Truth status: proved-standard.**

Disjoint rows are independent only when the law does not couple them. Attention couples positions
through K/V contact, so sequence/sibling batches must carry boundaries forbidding cross-batch
contact. Heads remain disjoint through head-local contact but may become a shared-output reduction
when the output projection mixes them.

### 6.4 Returned loss and orientation

**Truth status: proved-derived.**

For

\[
y=\sum_aT_a y_a,
\tag{H.7}
\]

the dual return is

\[
\bar y_a=T_a^\ast\bar y.
\tag{H.8}
\]

Chart phase/orientation returns through the adjoints. Calling the forward join merely “additive
parallelism” deletes the gyration/precession required by the receiver.

---

## 7. Exact tiled contraction

### 7.1 Resource equation

**Truth status: proved-derived.**

For block size \(b\), registers/thread \(r\), shared bytes/block \(s\):

\[
B_{\mathrm{res}}(b)=
\min\left(
B_{\max},
\left\lfloor\frac{T_{\mathrm{SM}}}{b}\right\rfloor,
\left\lfloor\frac{R_{\mathrm{SM}}}{rb}\right\rfloor,
\left\lfloor\frac{S_{\mathrm{SM}}}{s}\right\rfloor
\right).
\tag{H.9}
\]

CUDA's occupancy API remains the apparatus authority because allocation granularity matters.
Occupancy is one constraint, not performance itself.

### 7.2 Required tile

**Truth status: conditional.**

~~~text
one block owns a disjoint output tile
load x K-tile cooperatively
load contiguous W output-by-K tiles
form exact signed interval/limb partials
reduce K through a fixed tree
round outward once at the declared boundary
write the output tile
~~~

The scalar kernel remains an independent exact reference. Multiple legal tile shapes and reversed
reduction controls must agree coordinate by coordinate.

### 7.3 Tensor accelerator boundary

**Truth status: open.**

Tensor Cores do not directly implement arbitrary signed 64 by 64 to 128 interval arithmetic.
Possible lawful routes are cooperative CUDA-core wide-integer tiles, small-limb integer MMA with
certified carry reconstruction, or approximate tensor proposals followed by exact residual
correction. Approximation may never choose semantic state.

---

## 8. Pressure is a local covector population

### 8.1 Existing exact current face

**Truth status: established-bounded.**

receiver_current returns site capacity, co-present population, service rounds, characteristic
delay, arrivals and deferred arrivals:

\[
R_v=\left\lceil\frac{N_v}{C_v}\right\rceil.
\tag{H.10}
\]

This is service dilation, not a global pressure governor.

### 8.2 Typed partial pressure

**Truth status: interpretation.**

For site \(v\), resource species \(\alpha\):

\[
\Pi_v^\alpha=
\left(
N_v^\alpha,C_v^\alpha,R_v^\alpha,D_v^\alpha,Q_v^\alpha,\mathcal R_v^\alpha
\right),
\tag{H.11}
\]

where \(Q\) is deferred current and \(\mathcal R\) reflected/refused residue. Across
\(e:u\to v\),

\[
\Delta_e\Pi^\alpha
=
\Pi_u^\alpha-T_{v\to u}^{\ast}\Pi_v^\alpha,
\tag{H.12}
\]

and a constitutive passage may answer

\[
J_e^\alpha
=
K_e^\alpha(\Delta_e\Pi^\alpha;\text{boundary, mode, morphology}).
\tag{H.13}
\]

Register, shared-memory, DRAM, copy-engine, PCIe and CPU-I/O pressure are different covectors. They
cannot be summed until a receiver supplies a common metric.

---

## 9. Utility is a product, not a percentage

**Truth status: conditional.**

~~~text
SurfaceUtilityReceipt
  deed/source/mode lineage
  front extents and footprints
  cover grain, occupied and idle lanes
  ExactWork and dependency span
  partition and reduction complexes
  registers, shared memory, resident blocks/warps
  active, eligible and issued warps
  instruction/pipeline mix
  cache/DRAM/copy/PCIe traffic
  graph nodes, launches, synchronizations, allocations
  service rounds, deferred current and reflection
  calibrated time/power/thermal telemetry
~~~

Keep semantic work, cover/current, apparatus traffic and physical telemetry product-ordered.
A scalar utilization, speedup or energy score is a receiver quotient and cannot schedule semantics.

For work \(W\), span \(S\), lanes \(P\):

\[
T_P\ge\max\left(S,\frac WP\right).
\tag{H.14}
\]

Memory, instruction cost and synchronization strengthen this bound. Wide integer work is not priced
by floating-point peak throughput.

---

## 10. CPU staging and complete circulation

**Truth status: proved-standard.**

Rust threads are native OS threads. available_parallelism approximates logical capacity; it does
not expose physical cores, cache domains, current load or optimal worker count. Linux may preempt
and migrate runnable threads.

**Truth status: conditional.**

The CPU may overlap exterior I/O and graph preparation:

~~~text
card buffer A conducts current layer
CPU/pinned standing prepares next source region
copy engine fills card buffer B
graph dependency swaps A/B after compute and copy return
~~~

The graph, not a CPU semantic callback, carries layer succession. A whole-tower graph with
asynchronous copy nodes and two weight buffers is one candidate. A persistent instruction
interpreter is not.

Worker populations must follow I/O fronts, physical cores/cache topology and measured apparatus
receivers. Twenty-four logical CPUs are not a lawful constant.

---

## 11. Station D should share branches

**Truth status: conditional.**

For intervention at layer \(\ell\):

~~~text
base prefix 0 .. ell-1       execute once
immutable standing at ell   shared
intervention delta          branch-local
suffix ell .. final         per branch/cohort
~~~

Several siblings may cross one mounted layer as a disconnected cohort if the contact kernel carries
a batch boundary preventing cross-sibling K/V. Weights mount once; sections remain disjoint and
receive one interchange receipt. This is prefix/apparatus factorization, not semantic compression.

---

## 12. Lightning and reflection

**Truth status: interpretation.**

The card enacts information through electromagnetic circuitry, but a CUDA thread is not one fixed
wire or atmospheric arc. PTX is JIT-compiled and work maps dynamically to execution resources. A
one-to-one electron-path claim needs calibrated microarchitecture.

~~~text
plural ready tips / causal fronts
  -> local conductance and capacity
  -> admitted channel growth
  -> junction/reduction
  -> reflected/deferred boundary residue
  -> completed return after contact
~~~

leader_quadrature supplies local growth; running_integral/reflection owners supply boundary return;
receiver_current supplies capacity/deferred current; CUDA graph supplies an apparatus realization.
The missing object is their composed receipt.

Warp scheduling hides latency by issuing an eligible sibling when another meets a dependency or
memory boundary. This is structurally resonant with reflected current, but becomes a physical
identity only through scheduler-state and traffic calibration.

---

## 13. Compression, autoencoding and phase

### 13.1 Tiling is not compression

**Truth status: definition.**

A lossless partition/reduction is apparatus factorization. Compression begins only when a declared
future receiver factors through a smaller carrier and the collapsed population is retained.

### 13.2 Naive low-rank weight compression is refuted

**Truth status: established-bounded.**

The deposited Gemma measurements found all 168 inspected 256 by 2,560 q/k/v/per-layer-gate
circuits full rank. Low-rank structure is architectural: QK/OV bottlenecks, grouped-query sharing,
ports and sparse/generator structure. Phoenix must not assume dense trained weights contain a free
low-rank chart.

### 13.3 Native morphology candidates

**Truth status: conditional.**

Compare sparse partial transport, sufficient state, group/gauge equivariance, Markov lumpability,
tree/scale generators, winding-bearing crystal transport and retained unresolved fibres.

The deposited longest-suffix carry monoid is aperiodic by construction. Periodic material cannot
make it crystalline. A crystal candidate must add real turn/winding transport and exhibit a
nontrivial group return.

### 13.4 Manifold and phase receipts

**Truth status: conditional.**

GDL/manifold research requires rank, chart, action, gauge and coarsening receipts. A native quotient
carries rank/singular locus where applicable, connection/gauge transition, successor factorization
and ReconstructionFiber. Block size, latent width or spectrum is not topology or phase.

---

## 14. Station disposition

### Stations A through D

**Truth status: established-bounded.**

Stations A-D remain frozen evidence:

- A: lineage-local refusal, typed admission and resident source-layer passage;
- B: complete source manifest and potential tower;
- C: active text tower under midpoint quotient, with composed interval obstruction carried;
- D: intervention source taxonomy, matched siblings and controls.

Hardware inefficiency does not erase those returns. It prevents them licensing the next native
construction on the same realization.

### Unfinished Station E

**Truth status: open.**

The uncommitted native_law.rs/native_occurrence.rs and Athena walk/future kernel work begins native
ecology on the convicted substrate: one-thread flat kernels, maximum-legal-block launch, no typed
tiling/reduction, no utility/pressure return and no complete circulation. It is quarantined
material, not an admitted station, and must be rederived after the hardware foundation.

**Truth status: established-bounded.** A focused architecture-lint reading on this dirty Station E
tree returned **10 new ownership/materialization occurrence classes**: clone/collect/map/vector
growth in both new native files, two added vector occurrences in resident_section, and four in
source_occurrence. The gate is red. These counts are a required owner-by-owner disposition after
rederivation, not permission to re-seed the ledger or delete the work blindly.

---

## 15. Missing joins

**Truth status: open.**

1. General TensorPartition and ReductionComplex receipts.
2. Per-kernel resource/occupancy candidate family.
3. Exact tiled contraction and fixed reduction lineage.
4. Actual overlap/scheduler-state profile.
5. SurfaceUtilityReceipt joining work, cover, current and telemetry.
6. Cross-surface calibration receipt.
7. Whole-tower graph with double-buffered streamed weights.
8. Prefix-sharing and sibling-cohort dissection.
9. Tensor-accelerator limb/residual research, if exactness survives.
10. Native morphology selection using structural, GDL, Markov, phase and winding research.

---

## 16. Falsifiers

**Truth status: conditional.**

The replacement foundation refuses when:

1. graph permission is reported as measured overlap;
2. NVIDIA-SMI substitutes for scheduler/resource telemetry;
3. maximum legal block is called optimal;
4. a long inner loop is called tensor-tiled;
5. shared-output shards are called independent;
6. reduction deletes partial widths/orientation/lineage;
7. atomics testify for ordered path history;
8. CPU work occurs between semantic macro-steps of a claimed resident circulation;
9. transfer is serialized with compute without a returned obstruction;
10. matched siblings replay immutable prefixes/weights without a measured reason;
11. a cohort permits cross-sibling contact;
12. logical CPU count becomes a worker constant;
13. scalar pressure/utilization governs the path;
14. physical telemetry is inferred;
15. Tensor Core approximation commits semantic state without exact reconciliation;
16. tiling is called compression;
17. full-rank weights receive an assumed low-rank native chart;
18. crystal is claimed without winding/group return;
19. unfinished Station E is promoted before the new foundation; or
20. Station A-D evidence is discarded because its realization is replaced.

---

## 17. Final synthesis

**Truth status: interpretation.**

The holon is ordered by caused incidence. Hardware receives a typed front and returns how it
conducted; it receives no semantic authority.

~~~text
causal operation complex
  -> front and typed tensor/section regions
  -> exact work and local pressure population
  -> cover and interchange
  -> tiled local transport
  -> explicit reduction/gluing junction
  -> resident graph with streamed standing
  -> complete obstruction and utility return
  -> receiver-exact compression or reopening
~~~

The warp scheduler selects eligible physical warps inside that realization. It never selects the
holon's law. Lightning is local growth/return, reduction is the junction, pressure is local covector
reaction, and compression is the later receiver quotient. Those four objects are the foundation
Phoenix and the mathematics codec were missing.
