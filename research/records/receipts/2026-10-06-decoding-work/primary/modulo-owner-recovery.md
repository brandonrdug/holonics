# Modulo/phase-unfolding owner recovery

**Scope:** read-only recovery in the swept-transport worktree, 2026-10-06. No compiler, native run, network fetch, or owner edit. The prior AGENTS/core/lessons readings persist. The computational object remains the helical pair interaction: this lane touches helix, faces/placement, and tube; pair contact, cell holonomy, and tower restriction stay attached.

## Exact representation and current owners

For a positive period `Λ` in the same units as `x`, the lawful exact split is

```text
n := floor(x / Λ) : ℤ
 y := Λ · Int.fract(x / Λ) = x − Λ n
0 ≤ y < Λ
x = y + Λ n
D(y,n) := y + Λ n = x.
```

This is an algebraic adapter of the existing floor/remainder laws, not an existing modulo-audio decoder. In `lean/Holonics/Aeon/Clock/Winding.lean`, `windings t := ⌊t⌋`, `openPhase t := Int.fract t`, `reading_split` proves `windings t + openPhase t = t` and `0 ≤ openPhase t < 1`, while `split_unique` proves uniqueness. Apply it to `t=x/Λ`, then scale the remainder by positive `Λ`. For discrete natural modulus `d>0`, `lean/Holonics/Geometry/PhaseCarry.lean::phase_add_winding` and `value_digits` prove `x = (x mod d) + d·(x/d)` and reconstruct exactly. The matching Rust owner `crates/holonics/src/geometry/winding.rs::{phase,winding}` returns exact integer remainder and quotient; zero modulus is a typed refusal. Atlas entries: `objects.tsv::ratio.div-rem`, `geometry.tsv::winding.carry-cocycle`, `geometry.tsv::winding.universal-cover`.

A modulo face `y` by itself has no decoder for `x`: its preimage is `{y + Λk | k∈ℤ}`. The integer carry `n` is part of the state whenever an admitted future receiver distinguishes those lifts. The exact phase-carrier analogue already has that obstruction: `Objects/Ratio.amplitude_eq_iff_winding` says equal complex amplitudes iff lifts differ by `2πk`; `winding_separates_liftedCrossEntropy` exhibits equal amplitude/principal-log faces but distinct lifted cross-entropy. `Aeon/Clock/Winding.lift_retains_winding` gives a loop witness: three forward steps on a period-three circle and rest reach the same torus point, but read one and zero whole windings. This is the actual counterexample to declaring a folded phase current sufficient for every future.

The active native material decoder is narrower. `crates/holonics/src/physics/wave/chain.rs::WaveChain::{configuration,decode_configuration,return_material}` uses stored charge/flux coordinates `(q,φ)=(C V,L I)` and decodes as `V=q/C`, `I=φ/L`; its comment/equation states `configuration(decode_configuration(z))=z`. `return_material` derives the successor reader law, returns the reached point, then decodes it using the successor's current capacitance/inductance, and rechecks exact re-encoding. `physics/wave/continuation.rs::repeated_wave_material_returns_preserve_charge_flux_and_continue_the_native_joint_law` is the existing consumer witness, including a changed material and differing predecessor/successor readings. This recovers native wave coordinates after material change; it does not recover a modulo-aliased frequency or phase from samples.

Future sufficiency is owned by `lean/Holonics/Foundation/Standing/Law.lean`: `StandingLaw.sufficient` requires `reopen receiver word (retain source)` to equal the observation after every admitted transport word, and `standingLaw_exists_iff_future_factors` characterizes a lawful statistic by equal retention implying equal complete causal signatures. The concrete finite linear descent contract is `lean/Holonics/HNN/ModeQuotient.lean::{descended_run,descended_run_reads,descended_costate,descended_gain,gain_fibre_invariant}`: require `V T_t = T̄_t V`, every admitted reading `ρ_t=ρ̄_t V`, and material variation `φ_t=φ̄_t V`; then the descended run reads identically and its comparison/gain covectors factor. These laws offer a future-descent check for a proposed retained modulo statistic; they do not supply a temporal/spatial predictor or prove the moduloADC source conditions.

## Acoustic/Fourier caller boundary

`lean/HolonicsResearch/Foundation/AcousticReceiver.lean` owns the exact discrete resonator bank, its Cayley step, `run_causal`, `run_add`, and the order “co-present modes superpose, then quadratic colour/timbre response, then quantization.” Its actual counterexamples are `colour_does_not_distribute`, `quantize_then_superpose_ne_superpose_then_quantize`, `metamer_sounds_different`, and `unison_looks_different`. It contains no sampled-frequency alias decoder or wrap-count recovery. The module is brought in by `HolonicsResearch.lean`; no Rust caller appears in `rg AcousticReceiver lean crates`. The file itself records that the separate Rust mirror at history `1a6299e4:crates/holonic-engine/src/acoustic_receiver.rs` was retired in R1 for no live caller. Existing Fourier owners in this repository address Fourier reconstruction/transport (for example periodic-fluid coefficient reconstruction); the bounded source search found no acoustic modulo-sampling owner/caller.

The existing 2026-10-06 voice/medium record is the real physical consumer map: loaded `hnn/ring` returns effort/flow power; `WaveChain` is the native medium and material decoder; `AcousticReceiver.Bank` is a declared causal receiver whose physical pole/weight calibration is additional. Its exact pressure and volume-flow return requires a calibrated port. Its own retention clause requires future equality across every admitted action and receiver. That record does not establish frequency unfolding from alias samples.

## Primary source input supplied by the parent (not independently read here)

Parent's verified-source update identifies Ordentlich, Tabak, Hanumolu, Singer & Wornell, moduloADC, DOI `10.1109/JSTSP.2018.2863189`, full text `https://sia.mit.edu/wp-content/uploads/2018/09/2018-ordentlich-tabak-hanumolu-singer-wornell-jstsp.pdf`: voltage → ring-oscillator phase → modulo-`2π` read → quantization → temporal/spatial prediction recovering wraps under source conditions, with nonzero distortion/high-probability guarantees rather than arbitrary lossless-wave recovery. Parent corrected related unlimited paper identifiers to Bhandari, Krahmer & Raskar arXiv `1707.06340` and `1905.03901`. These are parent-verified source inputs, not source claims read or verified by this worker; no bandwidth or sampling result is inferred below.

## Recovery boundary and exact 13f8 history

`git grep` at `13f8c734` locates the pre-reset ratio/winding owners at `formal/elementary-holonics/ElementaryHolonics/{Geometry/PhaseCarry.lean,Objects/Ratio.lean}` and `crates/holonics/src/geometry/winding.rs`; the quotient/carry split and winding-loss witness were already explicit there. It does not locate a moduloADC or acoustic sample-unfolding caller. The current AcousticReceiver Lean owner is Research-only and the historical Rust mirror is separately retired; neither is the moduloADC predictor. Thus the new decoder equation above is the exact lawful chart composition of existing quotient/remainder plus carried integer, while recovery of `n` from modulo samples remains owned by the cited primary algorithm and its stated signal assumptions.

The key failure boundary is exact: if a proposed folded current face identifies `x` with `x+Λ`, but some admitted future action/receiver distinguishes these (as the lift/amplitude counterexamples show), then `StandingLaw.separating_future_refutes_the_standing` forbids retaining that face alone. The repair belongs at the actual signal decoder/receiver consumer and must carry the wrap/side information its source theorem needs; it cannot be supplied by an authored predictor or by calling modulo an invertible encoding.

## Source SHA256 (files actually inspected)

Current swept-transport source bytes:

- `lean/Holonics/Geometry/PhaseCarry.lean`: `878de52e93d8f1244f15238ed24a3e270820a74a77af819d2968dd90b69a9209`
- `lean/Holonics/Aeon/Clock/Winding.lean`: `14cdcbae7729c67dd194832dc1db3ff7a513d8fd63449649e87b3b31c88804fc`
- `lean/Holonics/Objects/Ratio.lean`: `4489aeb3acffda2df6329e64d5955e434d5a7f6d10ba9a9cc9db4d8f3a07b71a`
- `lean/HolonicsResearch/Foundation/AcousticReceiver.lean`: `963ac5e4de974aa3a74094da6f87f70d2297d6ae6155302fc1ca271084b62cbe`
- `lean/Holonics/Foundation/Standing/Law.lean`: `d29d9293eeac54ed0f13d282731e85d1609a4961e6e3d1ddce4db4e1190d9d9d`
- `lean/Holonics/HNN/ModeQuotient.lean`: `573493a7fd07cd3ae8dce6b7f406158f889c14b8519b36e829fe0e87feb474a`
- `crates/holonics/src/geometry/winding.rs`: `ca5a8f4417b638edc922cd6ef12d1b8e6ac0ad04b4e446d4ab2cd271a8fb72c0`
- `crates/holonics/src/physics/wave/chain.rs`: `3130272d662e592f72601253ad7aac21a2ebd1a2670fb6bd7f9d70f17532265a`
- `crates/holonics/src/physics/wave/continuation.rs`: `fef87716fa785bb372693885adacb91b4cf07164b0d5c421f1a45b0dc0e18674`

At `13f8c734`, `formal/elementary-holonics/ElementaryHolonics/Geometry/PhaseCarry.lean` hashes to `132e969d1f3b1980191c8ee50c8105ec4736e1f7376ac7323c249b8b6bd90e40`, and `crates/holonics/src/geometry/winding.rs` hashes to `151545bd902bb8f0f29155d70186cff26bd17a5f3339487ad2f5146e1869c844`.
