# Listener diagnostic wrapper contract

`listener_diagnostic_receipts.py` wraps `listener_diagnostic_stage.py`. It runs
one pinned command from one externally SHA-256-pinned JSON configuration. This
is an exterior process/receipt contract; it changes no native Holonics law.

## The invoked input

The configuration must pin exactly one input file. The command must have
exactly one separate `--learn PATH` argument. Missing, repeated, malformed or
mismatched declarations refuse launch. The input pin resolves relative to
`repo_root`; the command's input resolves relative to its actual configured
child `cwd`. Both must name the same resolved path. The receipt records this
binding alongside the preflight and postflight file hashes and the pinned
argv. The wrapper launches that checked argv without a shell.

The positive synthetic control starts a harmless Python child with this
argument form. The child opens the invoked path and writes its resolved path,
SHA-256 and synthetic contents into its output. The parent verifies those
against the input pin. Negative controls verify that a different input, a
missing/duplicate declaration, and incorrect cwd resolution cannot reach the
supervisor. These are code controls, not a listener dataset experiment.

The wrapper also binds the executing wrapper and imported supervisor to their
file pins, binds `argv[0]` to the binary pin, and checks Cargo.lock, repository
HEAD/tree/clean state and configuration bytes before and after the process.
The input binding establishes which file the command names; a future native
run's scientific results remain unavailable until that run actually occurs.

## One clock and its finish boundary

One `CLOCK_MONOTONIC` origin is sampled before configuration/preflight and the
first receipt write. All deadlines derive from that origin:

| Boundary | Offset from the single origin |
| --- | ---: |
| Native cutoff | 290 s |
| Process-group TERM | 295 s |
| Process-group KILL and cleanup cutoff | 299 s |
| Work, log finalization and evidence deadline | 300 s |

The final second is reserved inside the 300 s total for evidence. A native
report reserve narrows its phase allowance further; it never moves any outer
deadline. Preflight time consumes this same budget. There is no new deadline
at launch, no second cleanup grace period, no retry and no cap increase.

Deadline checks and process signals are cooperative with OS scheduling and
filesystem calls. The receipt's `finished_monotonic_ns` / `elapsed_wall_ns`
measure work and native-log finalization **before the terminal receipt
write/flush/fsync**. The terminal receipt explicitly names that boundary.
Its own final write latency is unmeasured by those fields. After that write's
fsync returns, the wrapper samples the same monotonic clock once more and
writes a create-only, one-line, fsynced landing sidecar. The sidecar records
that post-fsync observation and whether it is within the original 300 s total.
An observation after the total marks receipt landing late; it does not turn
otherwise completed work into incomplete work. A missing sidecar leaves
receipt landing unknown. The observation is an upper bound on the main
receipt's durable landing, not the exact instant of the underlying fsync.
The sidecar cannot certify its own final write latency. The initial and
intermediate receipt writes occur after the origin, so their elapsed time
consumes the work budget.

This is not a guarantee that every filesystem write or the entire wrapper
invocation finishes within 300 s. A future proposal must state this boundary
and obtain the required review; it must not advertise a strict end-to-end
300 s guarantee or use receipt I/O to extend native work or cleanup. Reaching
the work deadline, unavailable integrity evidence, a live group at return, or
uncertain cleanup cannot produce a complete result. A final-write failure or
partial receipt is incomplete evidence.

## Resource limits and evidence

- The launched process inherits affinity to exactly three visible logical CPUs
  and `RAYON_NUM_THREADS=1`. Fewer than three available CPUs refuses launch.
- `RLIMIT_AS=8 GiB` is a **per-process address-space** limit. Process-group RSS
  is a **sampled aggregate threshold**, normally every 50 ms; an observed cap
  breach triggers termination. Sampling and termination latency can permit a
  transient aggregate overshoot. This is not a cgroup limit or a guaranteed
  hard aggregate peak bound, and escaped descendants are outside process-group
  accounting. No cgroup or security-setting change is made by the wrapper.
- GPU visibility variables are empty. The exact command must select the CPU
  route; these environment variables alone are not a GPU security boundary.
- Free disk must be at least 512 MiB at preflight and each process sample.
  This is a sampled floor, not a filesystem reservation.
- Outputs, native log and receipt are create-only and outside the pinned
  repository. The stable native log is hashed and sized only after group death.
- Samples carry process-group RSS and user/system CPU ticks at the host's
  reported `SC_CLK_TCK`. Samples can miss exited descendants and short peaks;
  unavailable values remain unavailable. Waited-child CPU is recorded
  separately, before postflight Git commands can contaminate that counter.

A fixed proposal must carry the exact accepted source/tree, wrapper/stage,
binary, input, Cargo.lock and configuration hashes; exact argv/cwd/output paths;
the transaction accounting; these deadline/resource boundaries; and cleanup
and incomplete-result criteria, including a separate receipt-landing verdict.
A receipt, peer message or code-control pass
does not authorize a scientific run.
