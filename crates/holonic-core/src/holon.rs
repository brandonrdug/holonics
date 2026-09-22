//! **The Holon: the law and its ports, not its state.**
//!
//! [definition] A port Holon (`Holon/Element.lean::PortHolon`) joins its Dirac structure and
//! element relations; interconnecting two through shared ports is a Holon
//! (`Holon/Law.lean::PortHolon.interconnect`, `Holon/Law.lean::PortHolon.mem_interconnect`), which
//! is the recursion. A passive coholon is the zero-storage receiver
//! (`Holon/Law.lean::passiveCoholon`). Existing owner: `holonic_interaction::HolonicInteraction`.
//!
//! Empty in phase 2; `Holon`, `HolonState` and `interconnect` arrive in phase 3.
