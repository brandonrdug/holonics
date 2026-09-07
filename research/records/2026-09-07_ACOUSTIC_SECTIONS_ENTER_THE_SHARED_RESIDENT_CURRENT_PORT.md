# Acoustic sections enter the shared resident current port

[definition] September 7, 2026, following Apple `b041e462`. This closes the acoustic ingress
adapter identified during the shared conditional-generator port. It introduces no new learner
and does not complete AS4–AS5.

[established-bounded; implemented-exact] `AcousticFieldChart::mount_cell` in
`crates/holonics-hna/src/native/acoustic_field.rs` mounts a chosen temporal coefficient cell into
the existing `ResidentSurface`. Every sample is an exact point numerator in the declared digital
amplitude chart `(sample/divisor, 0)`. One common denominator, zero quadratures and structural
padding are retained. `AcousticFieldCell::rational` supplies the existing
`ResidentConstitutiveCurrent`, usable by the shared relation without a numerical host readout.

[established-bounded; implemented-exact] The immutable cell borrows its complete source chart.
Its exact source occurrence, coefficient support, receiver, lineage, sample step and origin
remain accessible. The chart also retains the decoded occurrence's locator, WAV digest and byte
count as exterior delivery lineage. Complete PCM remains recoverable. Mounting changes neither
the chart cursor nor any native ecology, and declares no contact or inferred condition. Cell
extent remains a caller-declared aperture rather than native acoustic grain.

[established-bounded; measured] All five `native::acoustic_field::tests` passed on Metal after
the final changes. Existing controls cover signed-word PCM extremes, zeros, padding, separating
temporal fibres and recovery of refused source handles. New controls verify exact nonzero-origin
support, invalid-index refusal before allocation, retained source metadata and native consumption
of the rational cell. An identity-receiver control carries a new `9/32768` source magnitude through
the relation while preserving its zero coordinates, with zero numerical readouts, numerical
egress or ingress during the two native operations. Cold readout subsequently verifies the entire
mounted numerator/denominator section. This is codec/current composition evidence, not acoustic
recognition or generative learning.

```sh
cargo test -p holonics-hna --lib native::acoustic_field::tests:: -- --include-ignored --test-threads=1
```

[established-bounded; process-audit] The final HNA test build and `git diff --check` passed.
An accidental workspace formatting pass was removed from 156 unrelated files before publication;
the prior unstaged patch was preserved at `/tmp/holonics-september7-unintended-formatting.patch`.
Only the intended source, tests and documentation are committed. Existing untracked `.DS_Store`
files remain untouched. No corpus cultivation, Lean build or physical acoustic measurement ran.

[established-bounded; source-inspected] The local AMI subset retains four mono PCM16/16-kHz
meeting recordings and exact source/target annotation pointers. Its speaker channel metadata
does not identify separate waveform channels. The existing source loader reads complete mono
recordings; no current Rust owner loads those exact annotation links as native interactions.
The [preparation guide](../experiments/apple_silicon/README_AMI_CONVERSATION.md) and
`prepare_ami_conversation_subset.py` retain the source annotation and refusals.

[open] Next attach independently addressed recording intervals to the actual annotation
source/target roles and exact clock supports. Retain the parent recording and pointer lineage,
overlap, gaps and unresolved annotation cases; do not use proximity, speaker IDs, transcript
spelling or response-type labels to author a native condition. Compose admitted conditions and
their complete Preimage Fibres with the shared relation, then develop retained sound and English
conduct and its acoustic receiver. The resident ingress port does not yet supply that interaction,
the general forward image of plural conditions, or useful produced sound.
