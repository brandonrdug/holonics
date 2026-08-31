import ElementaryHolonics.RH.GlobalWeilFinishLine
import ElementaryHolonics.Millennium.OfficialBSDReceiver
import ElementaryHolonics.Millennium.HodgeOfficialReceiver
import ElementaryHolonics.Millennium.NavierStokesOfficialBridge
import ElementaryHolonics.Millennium.YangMillsOfficialReceiver
import ElementaryHolonics.Millennium.PVersusNPOfficialBridge
import ElementaryHolonics.Millennium.PoincareOfficialBridge

/-!
# Source-specific Millennium finish lines

[definition] This is the single import surface for the seven receiver constructions.  It does not
assert an open conjecture and it does not identify the seven source theories.  Each imported owner
retains the terminal proposition, the source construction still owed, and the exact adapter which
would return that terminal proposition:

* [definition] RH ends at `RH.Statement`; its construction witness retains a cofinal xi-contour
  family, the global explicit-formula limits, arithmetic positivity, and an off-line Weil
  separator using the same receiver.
* [definition] BSD ends at a universally quantified rational-elliptic-curve ledger; its source
  construction retains the Hasse--Weil datum, Mordell--Weil group and rank, canonical-height
  regulator, Tamagawa and period factors, and the Tate--Shafarevich group whose finiteness is part
  of the conclusion.
* [definition] Hodge has a repository construction finish line which separately requires the
  classical source theory and its universal primitive algebraicity conclusion.  It is not claimed
  equivalent to the classical conjecture until canonical analytification and comparison maps are
  constructed.
* [definition] Navier--Stokes ends literally at the periodic alternative `StatementB`; its bridge
  retains local solutions, overlap uniqueness, a cofinal atlas, pressure normalization, terminal
  control, and globalization.
* [definition] Yang--Mills uses structured compact connected simple gauge groups and continuum
  Hilbert/Hamiltonian theories.  Its finite-to-continuum bridge requires a uniform separator and
  an exact spectral reconstruction law rather than a finite-stage gap alone.
* [definition] P versus NP ends at the fixed-TM2 propositions `PEqualsNP` or `PNotEqualsNP`; the
  two construction witnesses are respectively a uniform verifier compiler and one concrete NP
  language outside P, with `PSubsetNP` kept as an explicit unfinished closure theorem.
* [proved-standard; external-only] Poincare is the solved regression.  Its local finish-line
  certificate retains Ricci flow, noncollapse, singularity recognition, surgery lineage,
  extinction, and reconstruction into the exact homeomorphism required by
  `PoincareConjecture.ThePoincareConjecture`.

[project-postulate] Importing this module is the integration gate for receiver compatibility; it
is not a proof of any open terminal proposition and does not advance the live Rust roadmap.
-/
