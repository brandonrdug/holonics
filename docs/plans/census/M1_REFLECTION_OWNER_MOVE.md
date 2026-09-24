# M1 reflection owner move

Issue: #69. This is an owner move, not a new language layer.

`holonic-language` held one source-neutral transition law: a continuation presents a caused face
to its current codec; the codec advances, rests, or requests reflection; reflection retains the
codec and instruction; the return either installs a parented codec and resumes at that instruction
or resumes unchanged. The environment remains owned by the continuation. Its checked formal peer
is `Transport/ReflectiveContinuation.lean`.

The Rust implementation now lives at `holonics::generator::reflection`. It is part of generator
transport/continuation, has no language syntax or application codec semantics, and retains its
existing refusal values, IDs, lineage rules and rest/remount validation. `life::agentic_language`
and `life::decomposing_codec` call the main-library owner directly. The former crate and its
forwarding surface are removed; its focused integration tests move to `crates/holonics/tests`.

Verified after rebase onto the portable owner rename: the moved integration tests pass 2/2,
`life::agentic_language::tests` pass 17/17, `life::decomposing_codec::tests` pass 27/27, and the
locked workspace all-target check passes. The root README now counts 12 workspace packages (9
libraries and 3 applications). These gates establish compilation and preserved focused behavior;
no behavioral change or wire/version change is intended.
