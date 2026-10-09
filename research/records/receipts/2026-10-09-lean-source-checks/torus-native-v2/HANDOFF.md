# Finite torus subgroup repaired-source receipt

**FAILED** at exact SHA256 `f71efe93d0dacd7e29b0f1d33d881284605eae7c5fd0c12b4e2b3eadefc6679e`.

The owner repaired the proof bodies and expanded the axiom queries to all 37 public theorems. Thirty-six statement headers are byte-identical; `mFourier_integerTorusMap` is identical after expanding matrix-vector notation to `Matrix.mulVec`. The failed predecessor `190b46e8d9cb19a238cb101417dd832fb0985eb63cb835219c236519daa0dd19` and its `torus-native-v1` receipt remain preserved.

Command: `lake env lean -j1 HolonicsResearch/Geometry/FiniteTorusSubgroupReceiver.lean`, from `<torus-worktree>/lean`, one CPU and existing cached providers. Compiler exit 1; all 37 submitted public-theorem queries reported. Standard axioms only: False; `sorryAx` present: True.

Compiler wall 16290268458 ns; guarded wall 16721050352 ns; aggregate CPU 9129579000 ns; peak child RSS 3864344 KiB. Fixed deadline 91287144808 ns, unchanged from the predecessor. Measured reservation 4294967296 bytes; enforced ceiling 8589934592 bytes. No limit raised after launch.

Source and sealed local provider metadata remained unchanged. Exact target, transitive Holonics source and cached provider parts, toolchain executables/libraries, Lake manifest; foreign dependency closure is version-declared and consumed from existing cache, not an exhaustive byte seal. Full stdout/stderr, command/source/provider hashes, axiom reports and lifecycle/resource receipts are retained. The lease is released, the owned unit is quiescent and no native process remains. Failed service metadata remains; it owns no process or lease. No scientific source edit, dependency build or publication. This receipt certifies only the exact source check; it makes no HNN or new operator acceptance claim.
