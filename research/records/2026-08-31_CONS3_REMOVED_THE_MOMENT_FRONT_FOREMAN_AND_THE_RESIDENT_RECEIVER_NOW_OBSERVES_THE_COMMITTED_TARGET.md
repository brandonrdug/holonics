# CONS3 removed the moment-front foreman and the resident receiver now observes the committed target

Date: 2026-08-31  
Status: construction evidence under `blueprint/THE_ROADMAP.md`; this record schedules nothing.

## Source return

[established-bounded; implemented-exact; source-inspected] The final CONS3 hotspot was
`ResidentMembraneInteriorWord::conduct_quadratic_moment_front_inner`: 2,783 lines inside the
4,386-line `cuda_refine.rs`. It mixed plan consumption, CUDA pointer/wire assembly, dense and
factorized contraction, optional relational transport, boundary radiation, phase and situated
receiver selection, the terminal synchronization, host readback, decoding, memory accounting,
buffer release, and return assembly.

[established-bounded; implemented-exact; source-inspected] The method is now a narrow coordinator.
One owned `MomentFrontExecution` keeps the plan and every device buffer together; raw pointers
cannot outlive their buffers. The three active phases are:

- `membrane_moment_contraction.rs`, 1,104 lines;
- `membrane_moment_receiver.rs`, 765 lines; and
- `membrane_moment_readback.rs`, 1,063 lines.

The execution carrier is 23 lines and `cuda_refine.rs` is 1,681 lines. Every new owner remains
below the 1,500-line new-Rust-owner aperture. No extracted phase calls `cuCtxSetCurrent`; allocation
retains the one context placement. Receiver formation retains the one unconditional terminal
`cuCtxSynchronize`; the pre-existing factorized profiling-only synchronization remains explicitly
conditional.

[proved-derived; implemented-exact; measured] The split preserves operand and launch order:
admission and allocation precede contraction; contraction precedes complete boundary radiation;
phase and situated receivers consume the complete current; balance precedes terminal
synchronization; and only then does readback decode receiver faces. No phase uses a zero scalar face
to delete a current buffer or reconstruction fibre.

## The stale resident equality control was corrected

[counterexample; measured] In a detached clean worktree at commit `5e85ec49`, the ignored RTX
control `quadratic_moment_front_equals_the_enumerated_boundary_law` already failed before this
refactor: the direct dense word executed nine kernels while its stale assertion expected ten. When
that assertion was corrected, the resident fixture supplied unaddressed source contexts and no
causal-adjoint relational fibre, although the production path had come to require both before it
could observe a completed target.

[definition] A direct/factorized diagnostic contraction and a production resident passage agree on
the same pre-transition receiver shadow only where they read the same occurrence. Once the resident
passage commits an off-diagonal target, its later receiver must not be required to equal the source
diagnostic. That would identify two causal occurrences merely because an older test expected one
surface.

[proved-derived; implemented-exact; measured] The repaired control now:

- assigns the two source contexts their exact boundary states;
- mounts a two-row relational reconstruction fibre before production observation;
- proves dense and factorized direct receiver equality, including chunked versus unchunked runs;
- proves the resident return differs from the pre-transition diagnostic and checks its exact
  post-transition port values;
- returns both transition target states `{0, 1}` in the slot and target populations; and
- retains zero intermediate host egress, no invariant re-upload, no CPU semantic replay, and the
  declared context/synchronization receipts.

## Verification

[established-bounded; measured] `cargo check -p holonic-engine` completed without a Rust warning.
`cargo test -p holonic-engine --lib` returned 1,984 passed, zero failed, and 30 ignored. The repaired
RTX control returned one passed and zero failed. CUDA symbol parity returned one passed and zero
failed. `python3 tools/source_shape.py` reported 624 live files, 447 inherited baselines, and zero
violations.

[counterexample; measured] The first complete release invocation passed sixteen non-test receivers
but the old workspace-wide test subprocess crossed its 180-second boundary before Cargo emitted a
single result line. The failure summary therefore said zero tests even though the separately bounded
package populations were green. The gate was a hidden process foreman.

[established-bounded; implemented-exact; measured] `tools/gates.sh` now derives the exact package
and target-kind population from Cargo metadata. Every package receives its own 180-second test
boundary; binary-only packages are not falsely invoked with `--lib`; the workspace example closure
remains a separate bounded check. The corrected test gate returned 2,972 passed, zero failed, and 49
ignored over 33 result lines. One subsequent complete `bash tools/gates.sh` invocation returned all
17 gates passed, including the 3,765-job Lean umbrella, source shape, architecture, manifests, and
document law.

[definition] CONS3 is closed. The Lean production closure already satisfies CONS4 through the
single `HolonicQuantumTransport.lean` umbrella; CONS5 is the remaining release junction.
