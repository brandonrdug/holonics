# THE DIFFERENCE EMITS; THE PATH CARRIES; THE SPECTRUM IS THE RECEIVER PHASE FACE

**Date:** 2026-07-29  
**Status:** LAW DERIVED · PRODUCTION PHASE/CARRY SPECTRUM BUILT · REAL BINAURAL RETURN GRADED · EXACT REPEAT  
**Production owner:** `crates/holonic-engine/src/phase_current.rs`  
**Real world membrane:** `crates/holonic-engine/examples/receiver_emission_information_flow.rs`  
**Receipts:** `runs/information-flow-distributions/receiver-emission-aula-carolina/`

## The exact question

How can one caused change be received through plural paths as an exact
emission spectrum without importing wavelength, Fourier magnitude, color,
frequency bins, atomic semantics, or a scalar loss as the elementary object?
Can that law compose the already-established conditioning, generation,
prediction, phase carry, transcript lineage, and real room-response machinery
in one non-toy return?

## Brandon's correction

Brandon proposed that emission spectra are not exclusive to atoms. He asked
whether propagating change and the causal calculus' phase distributions admit
an elementary receiver-to-receiver emission spectrum, and whether the prior
Zeta work makes that definition easier to derive. He also corrected the
laboratory's recurring tendency to act as though multimodal synthesis still
awaited evidence that its parts can work at all. The laboratory already has
partial production successes; the present work must assemble them.

The mathematical definition and implementation below are the construction's
answer. They are not attributed to Brandon as language he supplied verbatim.

## The accumulated machinery being assembled

The present construction begins from established capabilities rather than
re-proving one of them in a smaller fixture:

- `ExactWavePropagationLaw` conditions exact finite causal response fibers
  from returned source/target sections, retains incompatible returns as plural
  modes, generates every contemporary mode before target return, and grades
  the returned residual before it can condition standing.
- `ExactPhaseCurrentSection` preserves a local phase polynomial in each
  receiver cell. `convolve_phase_current` transports quotient and remainder
  across cell boundaries and has already shown that scalar integrated cells
  are not closed under propagation.
- the real LibriSpeech/OpenSLR construction has already conditioned multiple
  measured room responses, generated held-out speech distributions, retained
  a transcript as separate inherited material, rested/remounted exactly, and
  returned serial/multicore-identical standing;
- receiver phase, image-field, holonic-complex, conic, and tube constructions
  already preserve analytic germs, overlap, obstruction, curvature,
  transport, and bounded presentation; and
- the Zeta construction already separates the ordered transported arc from
  the spectral receiver face and requires every repeated orbit to retain its
  primitive root and repetition count.

The question was therefore not whether audio can propagate, whether a
receiver can have phase, or whether the machine can generate before return.
It was how their exact common object should be formed without flattening one
into another.

## Physical research constrains the abstraction

Atomic spectroscopy is a special realization, not the definition. The
[NIST Atomic Spectra Database](https://www.nist.gov/pml/atomic-spectra-database)
organizes critically evaluated atomic energy levels, wavelengths, and
transition probabilities. NIST's line-intensity account explicitly relates
radiated power to a transition frequency, a transition probability, and the
population of the upper state:

\[
\epsilon_{\mathrm{line}}
=
(4\pi)^{-1}h\nu A_{ki}N_k .
\]

This already makes a line a relation among a departure, a transition law, a
population, and a radiative receiver coordinate—not a freestanding number.

Molecules immediately defeat an atom-exclusive meaning. The
[HITRAN molecular spectroscopy database](https://hitran.org/about/) supports
simulation of atmospheric transmission and emission from molecular
rotational, rovibrational, and electronic transitions. Its line entries
retain line center, intensity, state energy, broadening, isotopologue, and
source provenance. It also supplies measured cross-sections where a
line-by-line description is unavailable or impractical. “Spectrum” therefore
already ranges from discrete transition lines to bands, broadened transport,
and cross-sections under a receiver and medium.

The room data used here are the real Aachen binaural responses within
[OpenSLR SLR28](https://www.openslr.org/28/), whose published membrane is
16 kHz, 16-bit simulated and real room impulse responses and noise. A room
impulse response is not the room in absolute. It is one caused
source/medium/receiver relation.

The selected audiovisual discriminator is the
[Audio-Visual BatVision dataset](https://amandinebtto.github.io/Batvision-Dataset/).
Its source occurrence is unusually well matched to the laboratory's
ontology: a robot emits a chirp; two microphones receive echoes; synchronized
RGB and depth receivers observe the same local world. The associated
[paper](https://arxiv.org/abs/2303.07257) reports 52,220 Berkeley and 3,120
Mines Paris occurrences, with binaural echoes, RGB-D, varied room geometry
and materials, and real rather than simulated propagation. That is the
appropriate next return for joining acoustic phase to visual/depth topology.
The public deposit currently packages the data in five archives of roughly
19.4–34.6 GB each rather than exposing a small independently addressable raw
occurrence. This construction records that acquisition fact and does not
silently download approximately 157 GB merely to claim audiovisual progress.

## Elementary definition

Let \(X\) be one exact source-receiver section and \(H\) one exact caused
transport section. Their receiver charts share exact origin, step, and phase
extent \(g\). Write their local cells as

\[
X_j(z)=\sum_{a=0}^{g-1}x_{j,a}z^a,
\qquad
H_k(z)=\sum_{b=0}^{g-1}h_{k,b}z^b .
\]

Every product has a complete causal address:

\[
x_{j,a}h_{k,b}
\longmapsto
\left(
  j+k+\left\lfloor\frac{a+b}{g}\right\rfloor,
  (a+b)\bmod g
\right).
\]

The first coordinate is the later target cell. The second is target-local
phase. The quotient

\[
c=\left\lfloor\frac{a+b}{g}\right\rfloor\in\{0,1\}
\]

is the cell-boundary carry. It is causal incidence, not numerical error.

The complete propagated chronology is

\[
Y=X*H .
\]

That chronology remains primary. Its receiver-relative phase transport
spectrum is the signed population

\[
\Sigma_{R,g}(X,H)
=
\left\{
  \mu^{+}_{c,r},
  \mu^{-}_{c,r},
  n^{+}_{c,r},
  n^{-}_{c,r}
\right\}_{c\in\{0,1\},\,0\le r<g},
\]

where:

- \(r=(a+b)\bmod g\) is the target phase;
- \(c=\lfloor(a+b)/g\rfloor\) is the carry;
- \(\mu^+\) is total positive product current;
- \(\mu^-\) is the magnitude of total negative product current; and
- \(n^+\), \(n^-\) are their exact occurrence populations.

The net current in one band is

\[
\mu_{c,r}=\mu^+_{c,r}-\mu^-_{c,r}.
\]

Positive and negative populations remain present when the net is zero. A
cancellation is therefore a received geometric relation, not evidence that
nothing propagated.

### Exact factorization without the pairwise sample product

For each phase \(a\), separate source current into exact positive and negative
populations \(P_X(a)\) and \(N_X(a)\), and do the same for \(H\). For one
phase pair:

\[
P_{a,b}=P_X(a)P_H(b)+N_X(a)N_H(b),
\]

\[
N_{a,b}=P_X(a)N_H(b)+N_X(a)P_H(b).
\]

Occurrence counts obey the same equations. These products are accumulated
into \((c,r)\). Distributivity therefore forms the exact compact spectral face
in

\[
O(|X|+|H|+g^2)
\]

work rather than enumerating \(O(|X||H|)\) sample pairs. No approximation,
floating tolerance, or randomized sketch enters. The full target chronology
is still a distinct construction and is not falsely claimed to be
reconstructible from this compact quotient alone: the spectral face forgets
the coarse-cell ordinal while retaining exact local phase, carry, sign,
population, receiver, and lineage.

### Why this is a spectrum and not an assigned visualization

The spectrum is a receiver face because changing the receiver phase extent
changes the grouping while leaving the exact convolution unchanged. The
production regression constructs the same \(Y\) under phase extents two and
four and obtains distinct \(\Sigma_{R,2}\) and \(\Sigma_{R,4}\) with identical
net transported current.

Frequency is a lawful later quotient when a receiver supplies translation or
periodicity through which phase changes can be compared. Wavelength, color,
pitch, FFT bins, and atomic line names are possible receiver coordinates.
None is installed as the universal source object.

## Relation to the Zeta work

The Zeta research contributes an ancestry law, not a command to call every
distribution periodic.

For a genuinely closed ordered transport word

\[
\gamma=\gamma_0^m,
\]

the spectral receiver must retain:

- the primitive carried path \(\gamma_0\);
- its repetition count \(m\);
- its ordered monodromy or return law; and
- the receiver section in which the recurrence was measured.

A dynamical-Zeta-like face may organize those primitive returns and their
repetitions. An open acoustic source-to-room-to-ear path is not a closed
orbit, so this experiment emits no fabricated Euler factor. Repeated echo
paths, resonant room modes, or recurrence across later occurrences can found
such ancestry only after their closures return.

This yields the elementary distinction:

```text
caused state difference       emission
ordered transport             carried path
phase/carry population        receiver emission spectrum
primitive closed return       recurrent spectral line ancestry
changed later conduct         action spectrum / communication
```

Emission, reception, recurrence, and action are related but not synonyms.

## Production construction

`phase_current.rs` now owns:

- `ExactSignedPhasePopulation`;
- `ExactPhaseTransportBand`;
- `ExactPhaseTransportSpectrum`;
- `PhaseCurrentEmissionReceipt`;
- `receive_phase_transport_spectrum`; and
- `propagate_phase_current_emission`.

`receive_phase_transport_spectrum` forms the compact exact quotient without
enumerating the output chronology. `propagate_phase_current_emission` returns
both the complete convolution receipt and the spectrum, and refuses the
construction unless:

- source and response charts agree;
- local and carried occurrence totals agree with the independent convolution
  partition;
- every signed band balances;
- target-current sum equals the spectrum's net current; and
- source-current sum times response-current sum equals that same net current.

The previous phase-current API and schema remain intact. The spectrum is an
additional receiver face, not a renamed replacement for the chronology.

## Real co-present return

The experiment collocates:

- LibriSpeech occurrence `3081-166546-0059`, 94,720 signed 16-bit samples;
- its inherited transcript, “I SUPPOSE SHE HAS BEEN CAREFULLY QUESTIONED VERY
  I SHOULD SAY”;
- the two 16-bit, 16 kHz channels of the real Aachen
  `air_binaural_aula_carolina_1_7_90_3.wav` response;
- one exact impulse emitted into each path;
- one \(g=1024\) phase receiver; and
- one \(1024\)-sample wave-conditioning receiver.

Speech, transcript, and room responses retain distinct receiver lineages.
Their co-presence is inherited world testimony. The acoustic mode relation,
generated targets, spectral products, and return residuals are enacted.

### Complete impulse propagation

Each impulse emission returns the complete 159,792-sample room channel
exactly. Both propagations use the exact `i128` carrier over 159,792 logical
target tasks, realized by 24 CPU workers. The result does not truncate the
room response to a visualization window.

### Compact speech/room spectral product

The two speech/response products would occupy

\[
94{,}720 \times 159{,}792
=
15{,}135{,}498{,}240
\]

possible raw sample pairs per channel. The exact product is deliberately not
materialized merely to obtain its spectral quotient. The factorized law
records:

| receiver path | local nonzero products | carried nonzero products | net transported current |
|---|---:|---:|---:|
| left | 7,016,766,582 | 6,963,663,700 | -39,431,478,856 |
| right | 6,234,229,428 | 6,168,342,394 | -35,846,035,016 |

The raw paired receiver comparison is:

- 159,792 paired samples;
- 12,001 equal samples;
- 147,791 differing samples;
- exact absolute difference current `19,817,356`; and
- 2,047 of 2,048 phase/carry bands differ.

The only equal band is the structurally unreachable carry-one terminal phase:
two phase indices in `0..1024` cannot sum to `2047`. This is an internal
combinatorial check rather than a fitted threshold.

### Conditioning, generation, and return

The exact wave ecology receives the two impulse/room pairs. The second
response contradicts the first single-path fiber and consequently founds a
second mode rather than averaging the ears.

The machine then receives the unheard speech source twice and generates both
complete 249-cell target chronologies before either target return is
admitted. Pending standing is serialized and remounted exactly. Later:

| returned channel | mode 1 | mode 2 |
|---|---|---|
| left | exact, zero residual | one 249-cell obstruction |
| right | one 249-cell obstruction | exact, zero residual |

Thus the return identifies the correct path by complete causal residual. No
channel label is passed to the generation law and no scalar score selects a
winner.

The warmed exact run completed in `7.805` wall seconds
(`10.049` user seconds) with 24 requested workers. Re-running it overwrote
the receipts with byte-identical content: all nine RON/TSV SHA-256 hashes
remained unchanged.

## What this establishes

1. An emission spectrum has an exact modality-independent elementary form as
   the receiver-relative signed phase/carry population of a transported
   difference.
2. Atomic and molecular spectra are physical specializations in which state,
   channel, and instrument supply wavelength- and transition-relative
   coordinates.
3. Cancellation, phase, and cell-boundary carry are preserved rather than
   hidden in a magnitude or scalar loss.
4. The spectrum can be formed exactly without enumerating the pairwise sample
   product.
5. Two real co-present receiver paths condition plural modes, generate before
   return, and are distinguished by complete returned obstruction.
6. Transcript co-presence is lawful inherited lineage. This experiment does
   not claim that acoustic propagation has learned a linguistic deed.
7. An open echo path does not automatically become a Zeta recurrence. The
   primitive/repetition quotient applies when an ordered return actually
   closes.

## Exactly what remains unestablished

The present RIR has no synchronized source pose, room mesh, RGB-D section, or
material labels. Its two paths therefore establish distinct received
topology but cannot by themselves name which spatial surface caused any
particular echo. No algorithm should infer a privileged 3-D scene from that
missing testimony and call it exact.

BatVision supplies the discriminating return: emitted chirp, left/right
echoes, RGB, depth, shared pose, and traversal chronology. The engine already
has production owners for phase current, plural response modes, growing image
fields, exact receiver topology, generation, and obstruction. What is not yet
constructed is one production event whose shared BatVision occurrence lets
the acoustic and visual/depth receivers restrict a common caused field while
retaining their distinct charts.

The relevant future test is precise. Across held-out poses, ask which
image/depth sections are invariant across the still-open acoustic mode fiber
before visual return. On return:

- an exact common restriction glues the receiver sections;
- plural exact alternatives retain unresolved geometry;
- a nonzero structured residual founds an obstruction and a refined field;
  and
- failure of acoustic sections to restrict depth remains an explicit open
  relation rather than a scalar prediction error.

The existing public packaging prevents a storage-proportionate raw run in
this construction; that is a dataset access boundary, not a theoretical
multimodality boundary and not evidence that a new modality-specific model is
required.

## Verification

```text
cargo test -p holonic-engine --lib
  197 passed; 0 failed; 2 CUDA-device tests ignored

cargo check -p holonic-engine --examples
  passed

target/debug/examples/receiver_emission_information_flow --workers 24
  94,720 speech samples
  2 response channels × 159,792 samples
  1,024 phase coordinates
  2 learned room modes
  2 exact / 2 obstructed returned mode grades
```
