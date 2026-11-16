# Receipts: the line's saved states restore cold and write their own bytes (November 16)

Athena alpha's cold-restart box (#404) was ticked on the host's October library, which retired with the consolidation (#603). This is the
engine's receipt, on the store line's own states.

- **The reading** (`crates/athena/src/store.rs`, `restore-store STATE STATE_SHA`). A fresh process reads a saved state into a learner and
  writes it back as text; its bytes are compared with the file's. It writes nothing.
- **Read on the host, 16:05 UTC**, on three of the four-lane line's states (`STORE_RESTORE`):
  - lap 67's end state (`STATE.3000`): 15,848,190 octets written back equal; 392,505 material entries, 593,408 key draws; 94 ms;
  - lap 64's end state (the pass's close, `STATE.632`): 15,992,008 octets, equal; 92 ms;
  - lap 67's mean (`MEAN.3000`): 15,848,105 octets, equal; 95 ms.
- **The reads after a restart.** Every lap of the line opens as a new process from the previous lap's saved state, and gate 3 holds the
  rest of the box at each build: from a saved state a cold process codes 3 and 24 of the line's sections with section lines equal to the
  line's own and reads the line's cavity table byte for byte (`GATE_REPRO sections=24 equal=24`, `GATE_READ cavity.tsv EQUAL`; the
  receipts of November 16, for example `../2026-11-16_colgather/hold.txt`).
- So a restart keeps what the line learned: the state's bytes are its own, and the codes and reads from it are the line's.
