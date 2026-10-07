# The native contact consumes the Holon element relation

October 7. Refs #62, #63, #73. **Source-prepared; native validation pending.**
This is an ownership correction, not new learning, generalization, physical stability or an
artifact-release result. No build, training, generation or scientific run was performed by the
source owner. The separate contact validation successor is `ade009f3a`, following the v71
test-build failure at `59bb966b3`; its eight controls remained unrun at that failure.

## Recover the objects before choosing the migration

The source inventory is pinned to `ade009f3ae949ea63f1c590261e7c63809947745`. Its
[declarations](receipts/hnn-holon-ownership-20261007/DECLARATIONS.tsv) contain 269 line-start
public or restricted-public declarations in 30 non-test native Rust files: 228 structs,
35 enums, five traits and one type alias. There are 257 unrestricted-public and 12
restricted-public declarations. This is a declaration census, not an AST completeness proof or
a verdict that 269 mathematical objects are needed. Twenty-two core declarations have an
individual source/consumer disposition; the other rows explicitly retain their provisional
module mapping and pending detailed review. The [source pins](receipts/hnn-holon-ownership-20261007/SOURCE_INVENTORY.json)
keep that distinction.

The September reset did not authorize deleting a type from its name or static reference count.
The R0 census at `0e860129d` records #64 and says actual object/operation consumers take precedence
over counts. The #68 retirement at `e4e93d22f` removes compatibility readers and aliases.
Those are precedents for recovering and migrating a consuming law, then retiring its old owner.
They are not evidence that today's native scopes are already unified. Current issue/guide
maintenance belongs to the coordinating owner; this change edits neither shared guide nor issue.

| Existing owner | Actual composition and consuming call | Disposition |
|---|---|---|
| `holon::Holon` | The port law, element relations, navigators and restrictions. `Field::holarchy` joins the declared rings and contacts. | Keep the law object; its name alone proves no conformance of a runtime. |
| `holon::HolonState<C>` | A generic current configuration at a material commit; `receiver::reception::JointLaw` already consumes its exact-vector instance. | Existing runtime facet, not an absent primitive. A native use must match its configuration and commit. |
| `Field` plus `ConstitutionRead` | Incidence, source/receiver declarations and contemporary material form the joined Holarchy; `Reference::mount_with_family` certifies its gluing and keeps its parametric orientation. | Keep the declaration and adaptive material once. The mount certificate does not alone prove every scattering/descriptor consumer implements the complete joined law. |
| `Current` | Source navigator lift and selective/located clock; ingestion advances it. | Keep as a clock view. It has no wave/contact/resonator current. |
| `SourceMoment` | Bounded phase and offset counts with producing partition and clock; `open_storage` enters source moments into the material. | Keep the source quotient; it is not a packet or occurrence archive. Encoding/conduct/clock and opening pullbacks still govern each consumer. |
| `Encoded` | Producing chart, decoder, labels, fibre and conduct; `Field::step_occurrence` consumes its actual step and checks its square. | Keep the complete boundary chart. Class-count equality cannot substitute for it. |
| `Word` | An executed clocked passage on one material cut: junction, element, transit, resonator and actual paired transpose. | A bounded tube traversal, not arbitrary bits. Its opening rest-only header is stale; received/carry constructors already execute. Do not erase carry to make the header true. |
| `EndChange` and `ReceptionCarry` | The current wave/contact/resonator configuration, canonical momenta, port references, tick and pump phase; the next opening crosses those references. | Necessary runtime configuration. The generic library point cannot replace these coordinates with `Current` alone. |
| `ContactCut` | Ephemeral reached current plus the producing identity and bound observed return; consumed once by `continue_deposited`. | A lifecycle state, not a second retained resident or a journal. |
| `Reference::Resident` | Material, source clocks/moments, charts, reception carry, admitted family and execution-port state. `refine` writes carry; a later refine opens it. | Existing execution owner. No new resident wrapper is introduced here. |
| `PhysicalResident` | Exact encoded-section current plus fixed producing chart and declaring face; blind forward precedes optional teaching and publication. | A parallel continuing owner whose consolidation needs its actual source/chart/comparison contracts. |
| `ChartedPhysicalResident` | Physical receiving current with explicit chart/error/remainder contracts. | A third current scope. Preserve representation and error fibres during consolidation; equality of state-field names is insufficient. |
| `Faces` and `HolonRatio` | Receiver-relative complex faces, grain fibres, target clock and phase branch. | Legitimate views/comparisons. They are not global scalar progress or an independent-symbol model. |
| `Diamond` | Intersection of source/current reach with receiver observation, on executed windows. | Causal support, including carried opening support. No crystal spectrum, heat or convergence follows from the label. |
| `ContactOperands` | Contact constitutive forms plus geometry, cached rows, chart and executed transpose. | Migrate its physical element relation into the library; keep the certified realization in the native owner. |

The general `ReferenceHolon` solves the complete Dirac system at each step. The native transit
instead charts a descriptor-midpoint solve once per material cut. It admits singular `C`,
including pure transmission, and its return uses the chart actually executed. This distinction
is already stated in `hnn/propagation.rs` and checked for nonsingular storage by
`a_stored_transit_is_the_reference_holons_midpoint_advance`. Calling the general full solve at
every hop would change the realization and still would not state the singular descriptor law.
Conversely, keeping a second local physical material owner because the general solver differs
repeats the recorded failure of carrying an identified cause into a new consumer unrepaired.

## One migrated constitutive relation with its consumer

[agent-inferred] `holon::element::ContactConstitution` now owns the descriptor contact's actual
symmetric `C,K,D` forms. It is the contact facet of the element relations: momentum is `Cw`,
elastic effort `Ku`, resistive effort `Dw`, and storage is `(u^T Ku+w^T Cw)/2`. It does not own
the adaptive factors, deposition statistics, source occurrences or another continuing state.
Those remain in the existing constitution and current. Its constructor admits equal square
symmetric forms; it assumes no definiteness and does not invert `C`. A signed stiffness remains
subject to the existing native boost certification before an executed solve is formed.

`ContactOperands::build` constructs that library relation from the producing factors, reads its
forms to construct the cached native rows, and consumes its operator:

```text
m(C,K,D;G,h) = I + (G/(2h))(2C + hD + (h^2/2)K),
M = (2h/G)m,
right = h(alpha_from-alpha_to) + 2Cw - hKu,
zeta = X_executed right,   omega = (G/(2h)) zeta,
w_next = 2omega-w,        u_next = u+h omega.
```

The normalized operator's sole arithmetic owner is now `holon::element::contact_operator`.
The native boost certificate, native contact build, physics control and card publication import
that owner. The old `hnn::propagation::contact_operator` is removed, with no forwarding alias.
The card hunk changes its import and owner citation only; its cache, conversion, kernel and
runtime body remain as they were. This is source migration, not established device parity.

The former three `ContactOperands` matrix fields are removed and replaced by the library
relation. Cached integer rows and a certified inverse/chart are representations of those same
forms, not independent learned material. Their construction order and the native forward,
adjoint, held-momentum and work consumers remain. This preserves the mathematical transit
equations on admitted inputs; runtime equality still needs the queued native controls. The
library also gives a nonpositive hop a typed refusal before division. A small prepared control
checks malformed forms and zero hop; it is unrun.

The inherited formal counterparts are `HNN/Propagation.transit_balance`,
`HNN/Propagation.tick_well_defined`, `Holon/Element.midpoint_balance`, and the declared native
descriptor/scattering relations. Moving their Rust owner creates no new proof of passivity,
global equivalence or adaptive retention. The full descriptor realization-to-Holarchy/current
conformance remains an explicit #62 obligation; no trait marker is used as a proof of it.

## Follow the same circuit to the actual boundary

The frozen contact path is `Word::compare_contact_storage` through the same executed return,
all reached storage factors, bound `ContactCut`, deposition, held momentum and the successor
`Word` at the next tick. `Word::reception_end` already reads an unended full-tick continuation,
including the zero-recorded-tick opening after that deposit. This is the existing way to retain
the successor current rather than replaying a transient word or creating a new current owner.

The production execution-port path is `Reference::refine` to native receiving faces and the
resident's carry, then `Reference::release` on the contemporary material and its declared
receiving fibre/tolerance. That releases a receiver view; it does not certify a joint unknown
artifact or a decoded creative result. `PhysicalResident::communicate` exposes a whole native
complex boundary; `communicate_one_future` uses the existing one-common-label completion law
and retains actual Held/absent-domain results. Multiple unknown stations still owe their joint
mixed-slot law. The contact reaction is not yet consumed by those resident boundaries. This
consolidation does not claim that missing join complete.

Learning reusable composition requires a returned comparison to change the circuit that a
different admitted interaction subsequently meets, with its source/clock/frame/decoder/carry
contracts preserved. Examples may supply observed consequences after a blind forward. They
must not become a receiver's authored answer, a copied completed composition, an index of
training contexts or a new symbol-stream objective. The actual receiving changes, work and
retained admissible relations are the evidence. A phase gap, a changed contact or an attractive
mode name alone does not establish useful composition.

The exact finite changed-solve, held-momentum and next-receiving relations are recorded by the
geometry owner in `2026-10-07_A_CARRIED_COMMA_REACHES_THE_NEXT_RECEIVER_THROUGH_THE_SAME_CONTACT.md`
at `b2ef656cd`. They require actual source/clock/receiving operands and retain frame, work and
coarse defects. No universal comparison decrease, smoothness preference, quench condition,
latent-heat identification, Bragg-peak acquisition or music-training task is introduced.

## Source receipt and remaining gate

The [preparation receipt](receipts/hnn-holon-ownership-20261007/PREPARATION.json) records exact
source hashes, a syntax-only parse and whitespace check. These checks are not a typecheck,
native result or device verification. Validation belongs to the sole existing execution queue;
the new source needs a fresh artifact, cache/config preflight and a fixed measured projection
under its existing caps. Do not replay spent classification cohorts or raise a failed limit.
The resident/artifact consumer remains frozen while the shared source-scope consolidation is
reconciled. Shared guide/issue changes and final integration belong to the coordinator.
