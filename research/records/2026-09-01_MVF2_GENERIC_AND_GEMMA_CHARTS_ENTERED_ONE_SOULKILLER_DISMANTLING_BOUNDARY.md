# MVF2 generic and Gemma charts entered one Soulkiller dismantling boundary

**Date:** 2026-09-01  
**Phase:** MVF2  
**Truth status:** established-bounded; implemented-exact; source-inspected; measured

[established-bounded; implemented-exact] `soulkiller::dismantle` is now the sole public
dismantling entry. `SoulkillerDismantlingInput` consumes one exterior chart and returns
`SoulkillerDismantlingReturn<ColdWitness>`: productive `NativeTransportScaffold`, chart-specific
cold witness, and native `ReceiverInsufficiency`. The generic return alone implements the borrowed
and move-owned HIF dismantling traits.

[established-bounded; implemented-exact] `ReachableSectionDismantling` carries the standing
reachable-section/anatomy/closed-execution chart. `Bf16ExcitationDismantling` carries the faithful
factorized Gemma excitation chart. Both enter the same generic function; their cold witnesses differ
without changing productive type, admission, hot rest, or inference law.

[established-bounded; implemented-exact; source-inspected] The public
`dismantle_reachable_section`, `lift_bf16_excitations`, `SoulkillerScrapyardReturn`, and
`MultimodalScaffoldLiftReturn` surfaces departed. Their policy is private to the input
implementations. No alias, fallback, dual schema, or decoder was retained. The standing K2 example,
SCF/MVF examples, repeated circulation tests, hot handoff, and cultivation controls all use the one
boundary.

[established-bounded; implemented-exact; measured] A type-level control proves both chart types
implement the one admitted input trait. Focused generic/BF16/handoff controls passed. The engine
library returned 2,006 passed, zero failed, and 32 ignored; life returned 468 passed, zero failed,
and 14 ignored. Every engine/life target type-checked.
