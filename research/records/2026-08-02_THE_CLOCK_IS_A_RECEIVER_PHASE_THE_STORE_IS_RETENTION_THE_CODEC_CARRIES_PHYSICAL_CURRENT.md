# The clock is a receiver phase; the store is retention; the codec carries physical current

**Status:** BRANDON-CORRECTED / REVIEWED ACTION BASIS / NO CONSTRUCTION IN THIS RECORD

**Date:** 2026-08-02

## Question under review

This record develops Brandon's proposed elementary computer-science ontology before the next Eros
construction. It takes the physical apparatus seriously without reducing its operation to either
transistor folklore or detached digital symbols.

The proposed elementary statement is:

> Computation and storage are physical trajectories through receiver-distinguishable states.
> Registers, caches, RAM, flash, and disks differ by constitutive mechanism, retention horizon,
> address relation, and energetic return—not by one class containing “active information” while
> another mysteriously contains inert data. A clock is a local phase-and-sampling membrane. A
> codec is a caused transducer which carries equivalence classes between physical and logical
> receiver charts.

The statement is ontological, not an assertion that DRAM, NAND, and magnetic disks have identical
physics. Their different material laws are precisely what must remain visible.

## 1. Information requires a distinction and a receiver

Let \(X\) be the physical state space of an apparatus, \(R\) a receiver with response map
\(q_R:X\to Q_R\), and \(\gamma:[t_0,t_1]\to X\) a caused physical trajectory. Information is not
an extra substance inside \(X\). A bit, word, tensor, or program exists for this receiver only
where physically distinct states are identified into stable response classes:

\[
x\sim_R y\iff q_R(x)=q_R(y).
\]

The encoded face is the equivalence class, the codec is the admitted response/transduction law,
and the event is the passage of \(\gamma\) between classes. A voltage scalar by itself is therefore
not a bit. It becomes a bit under a threshold, timing aperture, reference, error margin, and later
conduct which distinguish its class.

This also explains why “decoded” material remains encoded. UTF-8 bytes, Unicode scalar values,
graphemes, Lean syntax, an x86 instruction, a micro-operation, a gate transition, and a reported
architectural state are successive faces under successive codecs. Plain English is not outside
encoding; it is another receiver chart.

## 2. Compute and store are one ontology with different retention

For a physical memory body with morphology \(m\), environment \(\theta\), internal state \(z\),
and receiver \(R\), define a retention relation rather than an absolute storage class:

\[
\operatorname{Retain}_{R}(x,\mathcal H\mid m,\theta,z)
\]

when the receiver will return the same response class throughout the requested horizon
\(\mathcal H\), absent a declared write or destructive event. A useful scalar quotient may be a
retention time \(\tau_{\rm retain}(m,\theta,z,R)\), but the complete object is a survival relation
with failure modes and lineage.

Under this ontology:

- a CMOS register or SRAM cell retains a powered bistable feedback state;
- DRAM retains capacitor charge, leaks, refreshes, and commonly restores after a destructive read;
- NAND flash retains trapped or floating-gate charge as threshold-voltage windows, with program,
  erase, retention, and wear dynamics;
- a hard disk retains magnetic orientation and requires an electromechanical addressing and read
  channel;
- an in-flight logic value is a shorter-lived electromagnetic and charge configuration whose
  receiver aperture is a later gate, latch, or port.

They are not interchangeable devices. They are distinct constitutive realizations of retained
receiver distinctions. “Volatile” and “persistent” are comparisons between their retention body
and a requested horizon, not a metaphysical division between computation and information.

The practical hierarchy called registers, cache, RAM, and storage is consequently a hierarchy of
locality, bandwidth, address formation, retained morphology, energy, and expected return. A cache
is most rigorously a locally retained effective response for a declared future receiver family.
It need not be understood as a copied semantic answer, and it is lawful only while its dependency
and invalidation lineage remain current.

## 3. A tick is a receiver phase, not a universal instant

A synchronous processor clock distributes a reference phase. Local sequential elements sample or
launch state relative to admissible phase windows. Wire delay, buffering, clock-tree geometry,
jitter, skew, voltage, and temperature make that phase receiver-local. There is no chip-wide
physical simultaneity hidden behind the integer cycle count.

An architectural tick is therefore a quotient over many local events:

\[
[\gamma]_{\text{cycle},R}
=
\{\text{local transitions admitted between two receiver phase boundaries}\}.
\]

The clock coordinates work but is not itself the work. Asynchronous micropipelines demonstrate
the more elementary relation: a stage acts when an upstream result is present and a downstream
stage can receive it. Rising and falling transitions may both be causal events; a globally
privileged high level is unnecessary. This is close to the existing Swing: conduct follows caused
local readiness and return rather than a display or host loop inventing time.

The phrase “electrons carry the bit through the processor” needs one correction. Conduction
electrons have slow average drift, while changes in the electromagnetic field and circuit state
propagate through the interconnect much faster, bounded by the medium and geometry. The carrier
population, field, impedance, and receiving circuit jointly constitute the signal. Relativity
enters first as finite causal propagation and the absence of absolute simultaneity, not as a claim
that ordinary software needs a cosmological coordinate chart.

Quantum mechanics likewise does not switch on only during a clock cycle. Semiconductor band
structure, tunneling, charge trapping, thermal noise, and magnetic retention are quantum-founded
throughout active and retained states. The useful systems distinction is active transition,
metastability, retention, and environmental coupling—not “quantum compute” versus “classical
store.”

## 4. The codec tower is a tower of transducers

A conventional execution may cross

```text
source language
  -> syntax and type faces
  -> intermediate representations
  -> ISA instructions
  -> decoded micro-operations
  -> gate and interconnect transitions
  -> architectural return
  -> application receiver response
```

Each arrow is a codec only because an ecology implements and agrees upon an admissible relation
between source and target response classes. Some arrows are frozen in hardware, some are software,
some are microcode, and some may be conditioned or reflectively revised. None is a mystical
semantic bridge.

A codec body should therefore contain:

\[
K_v=(X_v,Y_v,E_v,D_v,\mathcal I_v,\mathcal O_v,\ell_v),
\]

where \(X_v,Y_v\) are source and target faces, \(E_v,D_v\) are enacted encoding and decoding
relations, \(\mathcal I_v\) is the admitted invariant family, \(\mathcal O_v\) its open or
obstructed alternatives, and \(\ell_v\) its lineage. Encoding and decoding need not be inverses on
all possible physical states. Their lawful domain, losses, ambiguity, calibration, and returned
revision must be explicit.

This grounds the earlier learnable-codec proposal. An unfamiliar image file need not receive an
application-specific pipeline forever. A reflective machine may recruit byte, compression,
language, geometric, and image transducers; enact candidate decodings; compare returned
invariants; retain plural alternatives; and condition a new codec version. It may detach the
original mounted source only after the continuing ecology carries the response necessary for its
declared future questions.

## 5. Algorithm and apparatus

An algorithm is an exact causal diagram of admissible occurrences, incidences, branches,
obstructions, and returns. Execution is a physical trajectory which realizes that diagram through
an apparatus morphology. The same algorithm may admit CPU and GPU realizations, but those
realizations do not have identical schedules, memory traffic, energy, or local horizons.

Represent an admitted apparatus chart as

\[
\mathcal A_v=(C,\partial,M_v,\Sigma_v,K_v,\Pi_v,\ell_v),
\]

where:

- \(C,\partial\) are caused logical cells and incidence;
- \(M_v\) is the current physical morphology and retained state;
- \(\Sigma_v\) is schedule and placement;
- \(K_v\) is the codec tower;
- \(\Pi_v\) is the set of physical ports and resource receivers;
- \(\ell_v\) is complete realization lineage.

CPU and GPU parity means that their diagrams commute at the declared semantic boundary. It does
not mean their interiors must be traversed twice. Full host/card equality is required to admit a
new realization and may be sampled again by a declared audit; the hot path should carry exact
local or delta receipts.

## 6. Algorithmic folding and unfolding

Let \((C,\partial)\) be a caused cellular presentation and \((\bar C,\bar\partial)\) a more compact
body. A lawful fold is not arbitrary deduplication. It is a receiver-declared map
\(\pi:C\to\bar C\) satisfying at least

\[
\bar\partial\,\pi=\pi\,\partial
\]

on the admitted chains and preserving the relevant boundary response:

\[
\Lambda_{C,R}=\Lambda_{\bar C,R}.
\]

Compilation, circuit minimization, caching, common-subexpression retention, Schur condensation,
and the laboratory's recurrent support families can all be viewed as different folds only when
they preserve their declared receiver consequences. The quotient is not absolute. A proof
receiver, a timing receiver, and an energy receiver may distinguish interiors which a terminal
value receiver identifies.

Unfolding is likewise receiver-relative. A later question may require one fiber
\(\pi^{-1}(\bar c)\) to be refined or enacted. It does not recover a uniquely privileged global
interior, because several interiors may have had the same prior boundary response. The lineage of
the fold, its open alternatives, and the new return determine which refinement becomes caused.

This gives “large number” a precise physical correction. The mathematical value is a face; its
binary expansion, residue coordinates, factors, symbolic polynomial, or shared circuit are
different codecs and apparatus morphologies. The work owed by a receiver is closer to the caused
cells its requested consequence must traverse than to the printed magnitude of the value:

\[
W_R(C)=\#\{\text{caused cell passages required by the admitted response of }R\}.
\]

A factorized or residue representation can absorb scale into a chart change and dramatically
reduce \(W_R\). It does not make conversion, carry, storage, or reconstruction free; those are
codec passages which remain in the receipt. This is the hardware expression of the laboratory's
mode shifts between topological domains.

For a physical trajectory \(q_0,\ldots,q_N\), one conservative chart may carry a discrete action

\[
\mathcal S_d[q]=\sum_{k=0}^{N-1}L_d(q_k,q_{k+1};m_k).
\]

Driven and dissipative hardware requires the corresponding port forces or a port-Hamiltonian
chart; it cannot be derived from a closed least-action statement alone. Electron charge, thermal
scale, and material constants supply physical units and constraints, but they do not determine a
program's energy from source syntax. Capacitance, resistance, inductance, interconnect geometry,
voltage/frequency state, memory traffic, regulator behavior, and enacted schedule are part of the
apparatus morphology. Accessible specifications and telemetry can calibrate that morphology; they
cannot replace it.

## 7. Energy and action

For one capacitive node charged from \(0\) to \(V\), the supply delivers \(CV^2\). In the elementary
resistive charging model, \(\tfrac12CV^2\) is stored in the capacitor and \(\tfrac12CV^2\) is
dissipated; a later ordinary discharge dissipates the stored half. A complete
\(0\to1\to0\) activity therefore costs approximately \(CV^2\), before leakage, short-circuit
current, clock distribution, interconnect, memory, regulator, and I/O losses.

The familiar quotient

\[
P_{\rm dyn}=\sum_e \alpha_e C_eV_e^2f_e
\]

is statistical only because \(\alpha_e\) summarizes switching activity. An exact execution trace
may instead count admitted transitions:

\[
E_{\rm switch}=\sum_e N^{01}_e C_eV_e^2,
\]

with the transition and supply convention stated. A fuller apparatus receipt is

\[
E_{\rm trace}=E_{\rm switch}
+\int_{t_0}^{t_1}
(P_{\rm leak}+P_{\rm short}+P_{\rm clock}+P_{\rm link}+P_{\rm memory})\,dt.
\]

The exact event count does not make the physical energy exact unless capacitance, voltage,
leakage, regulator loss, and measurement aperture are known. Unknown energy must remain unknown,
not be set to zero or inferred from utilization.

The common holonic balance is the open-system port relation

\[
\Delta H=W_{\rm ports}-D_{\rm internal}-W_{\rm exported}.
\]

A conservative action principle may describe a subsystem, but ordinary CMOS execution is powered,
dissipative, thermal, and open. Action, ports, constitutive loss, and return must therefore remain
distinct. Landauer's \(k_BT\ln2\) bound concerns logically irreversible erasure under its physical
assumptions; it is not the measured cost of an arbitrary instruction or proof.

## 8. Resource return changes later conduct

The apparatus is not a passive executor. Voltage droop, temperature, DVFS, throttling, queue
occupancy, cache state, page residency, memory pressure, and device synchronization change which
later trajectories are admitted and how long they take. These are physical or operating-system
receiver returns into the same effective machine morphology.

A resource obstruction is consequently a typed return such as

\[
o=(\text{port},\text{requested support},\text{available horizon},
\text{measured state},\text{lineage}).
\]

It must either cause a lawful new \(M_{v+1}\) or \(\Sigma_{v+1}\)—partition, placement,
factorization, residency, voltage/frequency state, or receiver restriction—or remain open. A
larger integer limit that retries the identical traversal is not a morphology change.

## 9. Present apparatus and available testimony

The current laboratory machine was inspected read-only on 2026-08-02:

| receiver | observed apparatus |
|---|---|
| CPU | AMD Ryzen 9 7900X, 12 cores / 24 threads, reported maximum near 5.65 GHz, 64 MiB L3 |
| discrete GPU | NVIDIA GeForce RTX 4080 SUPER, 16,376 MiB reported device memory, 320 W limit |
| system RAM | 32,746,160,128 bytes installed |
| active laboratory store | WD_BLACK SN850X 2 TB NVMe |

Other enumerated drives are outside the active laboratory apparatus by Brandon's correction and
must not be treated as available cache, spill, persistence, or training tiers in later plans.

At the observation instant the 4080 SUPER was in P8 at 210 MHz graphics, 405 MHz memory,
approximately 11.7 W, 47 °C, and 0% utilization. These are sampled receiver readings, not a claim
about a later experiment or individual kernel transition. NVIDIA documents that the reported
power value on this generation is averaged over a sampling window.

The present Linux environment exposes temperatures and some device sensors but no usable CPU
package energy counter through `/sys/class/powercap`; `perf` is absent. NVML exposes GPU power,
clock, utilization, and memory testimony. No whole-wall meter is attached. Therefore a current
experiment can report:

- exact logical/card work and transfer receipts from the machine;
- sampled GPU power, clocks, utilization, temperature, and memory;
- sampled CPU/memory/device telemetry where exposed;
- elapsed time under a declared measurement aperture.

It cannot yet report exact whole-system joules, exact CPU-package energy, regulator loss, or
per-event physical energy. Hardware specifications calibrate admissible ranges; they do not
substitute for contemporary measurements.

## 10. Required physical-machine owner

The constitutive-port body in the companion audit should eventually admit a hardware
specialization, provisionally `ExactPhysicalMachinePortBundle`. It is not yet implemented. It
must carry:

1. physical carrier cells and declared apparatus ports;
2. retained physical/effective state and its receiver horizon;
3. exact logical transition and placement relation;
4. local clock, handshake, and phase charts without a global-instant fiction;
5. codec lineage from application face through device ABI and back;
6. switch, memory, link, synchronization, and obstruction receipts;
7. measured energy/thermal/resource testimony with calibration and aperture;
8. unknown physical quantities as open fibers;
9. returned pressure capable of changing later scheduling and morphology;
10. CPU/GPU/device realizations of one reified semantic current with lifecycle parity.

It extends the same constitutive idea; it is not another application-local hardware wrapper.

## 11. Review propositions

Before construction, the following propositions should be either ratified or corrected:

1. **State proposition:** information is a receiver-relative distinction over physical state,
   never a detached scalar substance.
2. **Retention proposition:** compute and storage share one transition/retention ontology while
   preserving distinct material constitutive laws.
3. **Clock proposition:** a processor cycle is a distributed receiver-phase quotient, not an
   absolute time slice or the source of causation.
4. **Signal proposition:** electromagnetic/circuit change propagates; electron drift alone is not
   the speed or identity of the signal.
5. **Codec proposition:** every representation boundary is an enacted, lineaged transducer whose
   law may be inherited, inspected, and conditionally revised.
6. **Energy proposition:** exact algorithmic events and sampled physical energy are coupled but
   distinct receivers; neither may fabricate the other.
7. **Backreaction proposition:** resource and thermal return must alter the same continuing body or
   remain obstruction.
8. **Realization proposition:** CPU and GPU are distinct morphology charts over one admitted causal
   program; hot-path host replay is not parity.

## Primary sources

- R. Landauer, [*Irreversibility and Heat Generation in the Computing Process*](https://www.dna.caltech.edu/courses/cs191/paperscs191/landauer1961.pdf)
- I. E. Sutherland, [*Micropipelines*](https://arc.cecs.pdx.edu/wp-content/uploads/2023/04/Sutherland_Micropipelines_TuringAward_ACM_1989.pdf)
- M. Horowitz, [*Computing's Energy Problem (and what we can do about it)*](https://gwern.net/doc/cs/hardware/2014-horowitz-2.pdf)
- OpenStax, [conduction and the distinction between drift and signal propagation](https://openstax.org/books/university-physics-volume-2/pages/9-2-model-of-conduction-in-metals)
- E. G. Friedman, [clock distribution networks](https://www.hajim.rochester.edu/ece/sites/friedman/papers/ProIEEE.pdf)
- [Linux powercap framework](https://docs.kernel.org/6.8/power/powercap/powercap.html)
- [NVIDIA NVML device telemetry](https://docs.nvidia.com/deploy/nvml-api/group__nvmlDeviceQueries.html)
- Y. Cai et al., [threshold-voltage distributions in NAND flash](https://users.ece.cmu.edu/~omutlu/pub/flash-memory-voltage-characterization_date13.pdf)
- MIT 6.004, [SRAM bistability](https://ocw.mit.edu/courses/6-004-computation-structures-spring-2017/pages/c14/c14s1/)
- Micron, [DRAM cell and refresh overview](https://www.micron.com/content/dam/micron/educatorhub/memory/how-dram-memory-works/micron-how-dram-memory-works-quiz.pdf)
- IBM Research, [magnetic recording as a coupled channel](https://research.ibm.com/publications/high-speed-magnetic-recording)
- [Port-Hamiltonian systems on discrete manifolds](https://arxiv.org/abs/1111.6403)
- [Structure-preserving port-Hamiltonian discretization](https://arxiv.org/abs/2202.04390)
- [AMD Ryzen 7000 specifications](https://ir.amd.com/news-events/press-releases/detail/1089/amdlaunches-ryzen-7000-series-desktop-processors-with-zen-4-architecture-the-fastest-core-in-gaming)
- [NVIDIA RTX 4080 SUPER specifications](https://www.nvidia.com/en-us/geforce/graphics-cards/40-series/rtx-4080-family/)
- Samsung, [970 EVO Plus data sheet](https://download.semiconductor.samsung.com/resources/data-sheet/Samsung_NVMe_SSD_970_EVO_Plus_Data_Sheet_Rev.3.0_10129514071343.pdf)
