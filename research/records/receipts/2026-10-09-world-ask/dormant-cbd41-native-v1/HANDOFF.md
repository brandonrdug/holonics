# Dormant successor scoped native measurement

**FAIL**, scoped hypothesis gate. Exact clean `cbd41c47dde1a2b44f50912b9e5d7dba5e8a6e60`, tree `31ae29cb3e038fad17ae29a6465ce343ed72d859`. Typecheck passed; the one runtime fixture exited 101. Every measured port 0 through 3 was already excited by passive history; no dormant pair at a port at least 1 was reached by the actuator. The family declaration and later separating encounter were not reached. The original c65 failures remain untouched. No fixture/filter repair or retuning occurred.

Complete per-port output and diagnostics are in `.local/native-feedback-continuation-20261009/dormant-test/native/compiler.stdout` and `compiler.stderr`.

Source stayed clean and unchanged. The jobs overlapped with distinct source/target paths and CPU assignments under the unchanged combined 8 GiB cap. No memory, pressure or time stop caused a result. Time windows were observations. All leases released; no source edits or publication. `VALIDATION.json` names and hashes full stdout/stderr, source/command/executable identities, exact wall/CPU/RSS/charged-memory readings and resource/cleanup seals.
