# The reception carries the interior change, the source port imposes the moment, and rest is complete absorption (pinned before any code)

**Date.** October 3. **Issues.** #73, #63 (THE_REBUILD U6), #62 (the owed Lean). **Grade.**
[definition; agent-inferred] for the carry law and its choices (§2, §3); [proved-derived;
implemented-exact] for the owners it reuses, held by their tests (§1); the build of October 3 and
its tests are §6 [implemented-exact]; the chained balance and the law it satisfies are §2.3
[proved-derived; implemented-exact; formal-checked, `HNN/ChainedBalance` (#293)]; the contact's
crossing of the reception (§2.3a) is [proved-derived from its owners; implemented-exact], with the
reflection's release agent-inferred.
Code follows this record. The production default stays rest.

**Occasion.** The review of October 3 located that every production reception opens at rest. The
path is `Reference::refine` (`reference.rs:1147`) → `PendingRatio::read_charted` → `open_charted`
(`pending.rs:184`, `:152`) → `Word::open_charted` (`word.rs:770`) → `Word::on_operands` →
`EndChange::rest` (`word.rs:809`). `tests/word.rs:33` pins it ("nothing of the earlier change
persists"). The card does the same: the device word zeroes its resonator states on every
invocation (`holonics-cuda/src/hnn/readout.rs:421-423`). So window `k`'s end change never becomes
window `k+1`'s opening.

The momentum the [throw](2026-10-02_THE_TRANSPORT_MODULUS_JOINS_THE_RECEIVERS_MINIMUM_ENERGY_MOVE.md)
carries (#240's `Flight`) lives between U6's parameter moves, not between receptions. The native
continuation (`word/continuation.rs:48`→`:354`) carries motion only within a refinement, across a
contact deposit. It is consumed only in a test (`reference.rs:4347`), refuses every non-contact
deposit (`continuation.rs:265-286`) and deposits nothing at `R = 0`. This record derives what must
carry from one reception to the next, and how, so that today's behaviour is the exact limit.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects it touches three:
- **the tube**: the receptions become one clocked span instead of a sequence of fresh impulses;
- **the pair**: the contact states `[u, w]` and the arriving waves carry across the boundary;
- **the helix**: a declared resonator's pump phase reads the field's own elapsed ticks.

Faces and placement (the moment's placement), the cell holonomy and the tower thread stay attached
unchanged.

## 0. The recorded failures this could repeat, and how each is avoided

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **2, an index of contexts or a window.** The carried change is the field's own state, of the
  field's fixed shape, overwritten at every reception. It is not a list of past windows, and no
  depth enters.
- **3, text as the exception.** Nothing here reads a codec; the carry is the same for any boundary
  chart.
- **5, an uncertified deposition.** A deposit between two receptions does work on the carried
  change. That work is read exactly by the owner that already reads it (§2.3). The chain's balance
  is read exactly at every reception, and the law it satisfies is derived and stated (§2.3), with
  the stronger reading that fails it, never assumed.
- **6 and 7, seen as unseen; bits as progress.** Exposure stays prequential (the corrected §7 of
  [the refit record](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md)).
  No score decides the carry: it is a declared opening whose laws are derived and checked exactly
  (§2.3, §4), and the production default stays rest.
- **The retention law (no tape).** The adjoint stops at the opening (§2.5). No word outlives its
  compare, and nothing of a consumed word is kept except the end change it leaves.

## 1. What the owners already state

- **The rest limit is a theorem of the owner.** `Word::continuing(field, operands,
  &EndChange::rest(..), injection, 0)` equals `Word::on_operands(field, operands, injection)` in
  change and in every tick balance (`tests/prediction.rs:66`). Today's reception is therefore the
  continuing word opened on the rest change at tick zero.
- **The change is the whole state.** `EndChange` (`word.rs:333`) holds the storage waves per ring,
  the arriving waves per contact, the contact states `[u, w]`, the resonator states and the phase
  each resonator's form is read at. Two words of two ticks, the second opened on the first's change
  with nothing injected, end on the change of one word of four ticks (`tests/prediction.rs:93`).
- **The commit's work on the end change is already read.** `WordBalance::commit` (`word.rs:612`)
  carries every word's balance across the deposit that follows it: the deposition work
  `½⟨x, ΔΘ x⟩` on the end change `x`, and `x`'s power under the committed constitution
  (`CommitWork`; Lean `HNN/Word.field_commit_deposition`). Exposure reads the form before the
  deposit at the word's cut for exactly this (`reference.rs:4006`).
- **The source enters as a state.** The opening storage `s_g(0) = P_g^(τ_g) m̃_g` is the
  normalized, phase-binned moment of the whole passage ingested so far (`moment.rs`, module
  header). It is the source's sufficient quotient, not an increment: exposure keeps one moment over
  the whole cut and ingests each window into it (`reference.rs:3869`, `:4075`).

## 2. The carry law

### 2.1 What carries

[definition; agent-inferred] At reception `k+1` the word opens on

```text
x_(k+1)(0) = Π_int x_k(end)  +  s_(k+1)(0)
```

where:
- `x_k(end)` is the end change of reception `k`'s word, taken when its compare consumes it;
- `Π_int` keeps every interior coordinate (the storage of the non-source rings, every arriving wave,
  every contact state, every resonator state) and sets each source ring's storage to zero;
- `s_(k+1)(0)` is today's open storage from the moment after window `k`'s ingest. It is nonzero
  only on the source rings.

**Why the source rings are replaced and not added.** The moment is the whole passage's normalized
state, re-read at every reception. Adding it to the source ring's evolved storage would count the
passage once per reception: the history would enter both through the carried motion and through the
moment. The source port is an imposed port. Its ring takes the moment's storage, and the ring's
outgoing end storage is absorbed by the source. The interior has no such source, so its motion
carries.

[definition] **Realization through the existing owner.** Zero the source rings' storage in
`x_k(end)`, then call `Word::continuing(field, operands_(k+1), &that, &s_(k+1)(0), t_(k+1))`.
Since `s_(k+1)(0)` is zero off the source rings, the addition there leaves the carried storage
unchanged, and on the source rings it imposes. `Word::continuing` itself does not change.

### 2.2 The exact limit

Let `A` be the absorption of the boundary at a word's end:
- `A = I` (complete absorption): every interior coordinate is emitted at the end, as today's
  release states (`word.rs`, module header, "release").
- `A = 0`: nothing is absorbed beyond what the field's own conductances dissipate within the ticks.

The opening is `(I − A) Π_int x_k(end) + s_(k+1)(0)`. At `A = I` it is `EndChange::rest` plus the
injection, at tick zero, which is today's word exactly by `tests/prediction.rs:66` on a field
with no declared resonator (§2.4).

[agent-inferred] The law built is `A = 0`. An intermediate absorption would need a declared exterior
admittance at the receiver's section, a new locus of the constitution with its own deposition. None
exists, and choosing a value for it would be an unjustified literal. It stays unbuilt unless a
measurement under `A = 0` locates the need for it.

### 2.3 How the carried change crosses the deposit and the ingest

Between the end of word `k` and the opening of word `k+1` the medium changes twice. Both are read on
the same physical coordinates of the carried change, by one owner, `PowerForm` (`word.rs:352`):
1. **The deposit**: `Θ → Θ'` at the lift `λ`. Its work on the carried change is
   `P_(Θ',λ)(x′) − P_(Θ,λ)(x)`, with `x′` the change held at each contact's momentum (§2.3a,
   [the deposit record](2026-10-03_THE_DEPOSIT_HOLDS_THE_CARRIED_MOMENTUM_AND_THE_ACCRETED_MASS_IS_THE_THROWS_DAMPING.md)
   §3); at rest the commit still reads `CommitWork::deposition = P_(Θ',λ)(x) − P_(Θ,λ)(x)` (§1).
   - Deposits on `E`, on the transport modulus `ρ`, on the receiving tree and on landmarks change
     only the injection or the reading. Their work on the carried change is zero.
   - Deposits on a contact's storage, stiffness or dissipation, and on a resonator's gains, do work.
2. **The ingest**: `λ → λ'` at `Θ'`. Each cell's selective step moves the lift point, which moves
   every contact's conductance at the lift. Its work on the carried change is
   `P_(Θ',λ')(x″) − P_(Θ',λ)(x′)`, with `x″` the held change's arriving waves crossed at the
   reference change (§2.3a). The step is the exterior source acting, so this work is the source
   port's, entered in the balance beside the source's imposition.

[definition; proved-derived] **The chained balance, on one baseline.** Let `x = x_k(end)` be the
carried change, `y = Π_int x` its interior, `s = s_(k+1)(0)` the moment the source port imposes, and
`E_S(z) = (h/4) Σ_(g∈𝒮) Y_g |z_g|²` the source rings' storage. The power form is additive by ring
and the ring admittances are field constants, so `P_(Θ,λ)(x) = P_(Θ,λ)(y) + E_S(x)` under every
form, and the deposit and the ingest act only on the contacts, so they read `x` and `y` alike. The
source rings' end storage `E_S(x)` is absorbed through the source port at the reception and is
subtracted once:

```text
P_open(k+1) = P_(Θ,λ)(y) + deposition_k + ingest_k + E_S(s)
E_end(k+1)  = P_open(k+1) − L_(k+1) + Π_c + pump + interconnection + residual,   |residual| ≤ bound
```

with `L = dissipation − resist + resonator dissipation ≥ 0` the next word's certified loss (each term
signed by its own owner). The first line is exact by the two decompositions above; the second is the
word's own balance (`WordBalance::closes`). Written on the whole end power instead, the same identity
is `P_open(k+1) = P_(Θ,λ)(x) + deposition_k + ingest_k + E_S(s) − E_S(x)`: the two forms are one
baseline, and an earlier draft of this section, which wrote `P(y)` and also subtracted `E_S(x)`,
subtracted it twice. At `A = I` the carried change is the rest, so the interior and the work on it
vanish, the whole end power is absorbed, and the opening is `E_S(s)` alone: today's opening power,
so today's balance is the limit of this one.

[proved-derived] **The law the carry satisfies: dissipativity with respect to its declared supply.**
The ingest is the source port's work (2. above), and the deposition, the imposition, the contrast,
the pump and the interconnection are each a declared port's. From the two lines and `L ≥ 0`, at
every reception

```text
E_end(k+1) ≤ P_(Θ,λ)(y) + deposition_k + ingest_k + E_S(s) + Π_c + pump + interconnection + bound
```

and summed over a chain, the end storage never exceeds the first interior plus everything the ports
supplied plus the residuals' bounds. Nothing enters except through a declared port.
[formal-checked] `HNN/ChainedBalance` (#293) states this section: the split at the source port and
the one baseline (`power_split`, `opening_one_baseline`, `draft_subtracts_twice`), the rest limit
(`rest_opens_at_imposed`, and `carry_enters_additively` on `HNN/Retention.word_opens_at_zero`), each
reception's dissipativity (`reception_dissipative`), and the chain's telescoping and dissipativity
(`chain_telescopes`, `chain_dissipative`, and `chain_dissipative_certified` with the opening split
within its certified bound). `L ≥ 0`, the residual's bound and the absorbed storages `≥ 0` are
hypotheses read from their owners.

[measured-exact on the carry as first built (#280), which kept the waves `a`; superseded by
§2.3a] **The stronger reading failed on that carry.** It was stated here before the read as the
sufficient condition: at every reception, `deposition_k + ingest_k ≤ L_(k+1)`, the
work done on the carried change between the words within the next word's loss. On the chain fixture
(`chain_of(cut_length())`, source `source(length, 81)`, a 24-window deadline, `Carry(Nothing)`;
nine compares, so eight chained readings) the deposition is zero at every reception, and:

| Reception | `deposition + ingest` | `L` | Holds |
|---|---|---|---|
| 1 | `0` | `0` | yes |
| 2 | `0` | `18142115297891599265251270759039205961/2¹²⁸` | yes |
| 3 | `10531030011859400337/2⁷⁵` | `57557220820183899053671/2⁸¹` | yes |
| 4 | `0` | `255451355697484121789559/2⁸²` | yes |
| 5 | `−2448376125/2⁴²` | `81862029179669344589161/2⁸¹` | yes |
| 6 | `1144389765/2⁴²` | `234498858861794171536969/2⁸²` | yes |
| 7 | `5048657427/2³²` | `2104128050508906045512109/2⁸²` | **no**, by `3580154876230715732256339/2⁸²` |
| 8 | `−15407359260789375224895/2⁷⁶` | `357753753096119191965200943566167177049/2¹³⁰` | yes |

Summed, the work is `73408221214458413523171/2⁷⁶` against the loss's
`1238976393826823334276250846524291252349/2¹³⁰`, so the summed reading also fails from reception 7
on. The cause is the ingest: each cell's selective step moves the lift and re-reads every contact's
conductance at the lift, and at reception 7 that re-reading does more work on the carried arriving
waves than the next word dissipates. The work is the source port's, so the reading that fails is the
one that counted it as interior. An earlier pass of this read compared the work with the dissipation
alone, omitting the element's passive term `−resist`; it failed at receptions 3, 6 and 7. That was
a slip in the loss, not a property of the carry. Both checks are now receipts
(`ChainedBalance::{dissipative, within_loss}`), and the fixture's test pins the failure of the
stronger one, exactly, rather than tuning anything to make it pass.

[measured-exact; agent-inferred] **Keeping the momentum instead does not make the stronger reading
a law.** On this fixture the ingest changes only the one contact's conductance, `G_0 = 2^(n_0) Y_0`
at the lift. So the ingest is exactly `(h/4)(G' − G)|a|²`, the energy of the conductance jump at the
kept arriving waves `a`: the term `½ vᵀ F v` of the throw's join (#281), in this form's
normalisation. It is the work, not the excess; the excess is the work minus the loss. #281 bounds
the momentum-kept energy by `(M + F)⁻¹ ⪯ M⁻¹`, which needs `F ⪰ 0`. The lift moves the conductance
by powers of two in both directions here: `2 → 2⁻⁵¹` at receptions 2 and 8, `2⁻⁵¹ → 2⁻⁹` at
reception 3, `2⁻⁹ → 2⁻¹⁷` at reception 5, `2⁻¹⁷ → 2⁻⁹` at reception 6, and `2⁻⁹ → 2` at
reception 7. Carrying the momentum `G a` instead, the jump does `(h/4)(G²/G' − G)|a|²`:

| Reception | Kept waves `a` (built) | Kept momentum `G a` | Momentum `≤ L` |
|---|---|---|---|
| 3 | `10531030011859400337/2⁷⁵` | `−10531030011859400337/2¹¹⁷` | yes |
| 5 | `−2448376125/2⁴²` | `2448376125/2³⁴` | **no**, by `262716277201981247154839/2⁸¹` |
| 6 | `1144389765/2⁴²` | `−1144389765/2⁵⁰` | yes |
| 7 | `5048657427/2³²` | `−5048657427/2⁴²` | yes |
| 8 | `−15407359260789375224895/2⁷⁶` | `15407359260789375224895/2²⁴` | **no**, by `1249993485751783345298914315909973265141760265707096231/2¹³⁰` |

(Receptions 1, 2 and 4 carry no arriving wave on a moved contact, so both forms give zero.) Keeping
the momentum moves the failure to the receptions where the conductance falls. At reception 8 a
contact shielded by `2⁻⁵¹` would carry the current it held unshielded, amplifying its wave by
`2⁵²`. Both carries are dissipative with respect to the declared supply. Neither law was derived;
§2.3a derives the crossing from the junction's owner and replaces the kept waves.

### 2.3a The contact's wave crosses the reception through the junction's reference change

[proved-derived from the owners; agent-inferred where marked] **What the lift's move is.** A
contact's conductance is `G_a = 2^(s_a) Y_a` with `s_a = −β_a Q_a / 2`, where `Q_a` is the pair
quadrance of the two rings' screws situated at their lifts (`propagation::contact_exponent`,
`field::Contact::pair`). The lift is the rings' clock state, which the ingest's selective step
advances. So a move of `G_a` is a change of the pair's slip, the rings' relative configuration.

It is not a change of chart. A change of chart would leave every later reading unchanged. A move of
`G_a` moves the junction's participation anchor: `∂v*/∂G_p = (a_p − v*)/S` (atlas
`hnn.conductance-covector-executed-potential`, `hnn.junction-participation-anchor`). It also moves
the transit's resistance `2/G_a`, and with them every later tick. The carried energy therefore has no
reason to be invariant across it, and the power-normalised carry `√G a`, which would make it
invariant, is excluded on this ground, not on its outcome.

**What the move is in the word's own geometry.** One tick is one contact hop
(`propagation.rs`, "One tick is one contact hop"), and a word's operands are fixed at its cut. A
reception therefore joins two segments of one clocked span (the tube) along the hop coordinate: the
consumed word's medium, with channel conductance `G`, and the next word's, with `G'`. A wave in
flight on the channel meets that step on its next hop. The field already owns the law of a wave
meeting a change of reference admittance: the junction's two-port at a zero held wave (Lean
`HNN/Ring.two_port_reference_balance` over `HolonicConstitutiveCirculation.{emitted, successorHeld,
weighted_square_energy}`; the propagation owner is `HNN/Propagation.junctionScattering_twoPort`).
For `G, G' > 0`:

```text
a' = (1 + Γ) a  carried in G',      r = Γ a  emitted in G,      Γ = (G − G')/(G + G')
G'|a'|² = T·G|a|²,   G|r|² = Γ²·G|a|²,   T = 4GG'/(G + G')²,   Γ² + T = 1
```

Each moved contact's two arriving waves cross this way. The ring storage waves (admittances are
field constants) and the contact states `[u, w]` (constitution, not lift) are unchanged by the lift.

[agent-inferred] **The reflection is emitted.** The reflected wave travels back into the consumed
word's medium, which no longer exists after the compare. It therefore leaves with that word's
emitted exchange, as the word's unread change does (`Released::power`), and is never carried.

**Consequence for the chained balance.** The lift's inter-word work on the carried change becomes
`−(h/4) Σ_a Γ_a² G_a (|a_(g←a)|² + |a_(h←a)|²) ≤ 0`, exactly the emitted power. The ingest can no
longer raise the carried energy, in either direction of the move, so the stronger reading's
remaining term is the deposition alone. [proved-derived; formal-checked] The stronger reading holds
at a reception wherever the deposition does no positive work and the ingest only emits
(`HNN/ChainedBalance.{ingest_emits, ingest_nonpos, reception_within_loss}`, #293). It is proved for
one deposition: the held work of an accreting contact mass, `C ⪰ 0`, `F ⪰ 0`, `C′ = C + F`, with no
other coordinate of the constitution moved (`HNN/HeldDeposition.{held_deposition_work,
held_deposition_nonpos, reception_within_loss_of_accretion}`). The commit's deposition also carries
the same-state work `½⟨x, ΔΘ x⟩` of every other coordinate (`PowerForm::held`), so a deposit that
lowers a mass (which a production deposit can, §2.3b), or whose stiffness, admittance or
conductance move does positive same-state work, is not covered: there the chained balance holds
only in its dissipative form, with respect to the declared supply, at every reception. At `G' = G` the wave crosses unchanged.
[proved-derived; formal-checked] Each coordinate's identity `G'|a'|² = G|a|² − G|Γ a|²` is the
fifth conjunct of `two_port_reference_balance` (`HNN/Ring.reference_carry_change`). Summed over
coordinates and contacts, the lift's work is `−(h/4) Σ_a Γ_a² G_a |a_a|²`, at most zero for `h ≥ 0`,
and zero for `h > 0` exactly when no nonzero carried wave meets a moved conductance
(`HNN/Ring.{reference_lift_work, reference_lift_work_nonpos, reference_lift_work_eq_zero_iff}`,
#290). Its identification with the chained balance's ingest is the Rust owner's join, checked at
every reception by `ChainedBalance::lift_emits` (#286); it is not a Lean statement.

This is neither of the two exchange laws proposed beside #281. Mass arriving at rest keeps the
momentum `G a`, and mass leaving at the carrier's speed keeps the velocity `a`; neither is one of the
three coordinates first listed here. Both describe a passive exchange with a reservoir. The
reference change instead transmits `2G/(G + G')·a`. That lies strictly between `a` and `(G/G')a`
when `G' > G`, and between `a` and `2a` when `G' < G`. The difference is emitted rather than
absorbed.

**The deposition's half is the deposit record's law** (#281, merged as #284). The transit advances
on `(u, p = C_a w)` (`propagation.rs`, the transit as the reference Holon's midpoint advance), so a
deposit that changes `C_a` holds the contact's momentum: the rate after it solves `C′_a w′ = π_a`,
`π_a = C_a w_a` with word `k`'s storage. [agent-inferred] The solve fixes `w′` modulo `ker C′_a`,
which no later tick reads; the built rate is `w + δ` with `δ` the reduced solve's particular point
of `C′_a δ = π_a − C′_a w`, so the rate is unchanged exactly where no mass moved. A momentum outside
`range C′_a` is refused, naming the contact. [proved-derived; formal-checked] The refusal is the
law at held momentum: a symmetric `C′_a` holds `π` exactly when `π` pairs to zero with its kernel,
every hold reads one energy, and a momentum with a kernel component has no hold while its holds at
`C′_a + εI` read above every bound as `ε` falls
(`HNN/ChainedBalance.{hold_iff_kernel_free, held_energy_unique, singular_hold_energy,
singular_hold_unbounded}`, #293).

**Built (October 3).**
- `ReceptionCarry` carries, beside the end change, each contact's conductance `G_a` and momentum
  `π_a` at word `k`'s cut (`Word::reception_end`), written in the saved carry as its `reference`
  line and one momentum line per contact.
- `ReceptionCarry::crossed` transmits each contact's arriving waves at the next cut's conductances
  and holds its rate at momentum against the next cut's storage; `ReceptionCarry::reflected` is the
  emitted power. `Word::open_received` and the exposure's chained read both open through
  `ReceptionCarry::opening`, one owner.
- The commit under the carry reads its work at held momentum (`PowerForm::held`,
  `WordBalance::commit_held`), from the deposit record's identity
  `½⟨w′, C′w′⟩ − ½⟨w, Cw⟩ = −½⟨w′, ΔC w′⟩ − ½⟨w − w′, C(w − w′)⟩`; the commit at rest is unchanged.
- [agent-inferred] A transmitted wave or a held rate need not lie on the word's transient lattice.
  The opening splits every arriving wave and contact state at that lattice, as it already split the
  storage, and the remainders open the word's error feedback (`Word::on_change`). A change on the
  lattice splits to itself, so every earlier opening is unchanged. The chained balance reads the
  opening's split exactly, `split = P(opening) − P(its representative)`, as an executed residual.
- `ChainedBalance` reads `reflected` and `split` beside its terms; `lift_emits` checks
  `ingest + reflected = 0`.

[measured-exact; this carry's own run] **The chain fixture read again, nothing tuned** (the same
fixture and deadline as §2.3; eight chained readings). Every reception closes, is dissipative with
respect to its declared supply, and the lift only emits. The deposition is zero at every reception:
no deposit on this fixture moves a contact's storage, so the momentum hold is exercised here only by
its unit test (`tests/word.rs`, `a_carried_change_crosses_the_next_openings_references`), and the
work between the words is the lift's alone. The stronger reading holds at all eight; the excess is
zero.

| Reception | reflected `= −ingest` | opening split | `L` |
|---|---|---|---|
| 1 | `0` | `0` | `0` |
| 2 | `0` | `0` | `18142115297891599265251270759039205961/2¹²⁸` |
| 3 | `46315959801979220365916592441711/(2⁷⁵·(2⁴²+1)²)` | `2394479/(2³¹·(2⁴²+1)²)` | `57098551254434724028511/2⁸¹` |
| 4 | `0` | `0` | `257159359338988997670991/2⁸²` |
| 5 | `10548810675/(2³¹·(2⁸+1)²)` | `−215431293/(2⁴³·(2⁸+1)²)` | `163725364095216116449671/2⁸²` |
| 6 | `615659626125/(2⁴³·(2⁸+1)²)` | `950789/(2³⁵·(2⁸+1)²)` | `117873298028166605879837/2⁸¹` |
| 7 | `3441151657053/(2³⁵·5³·41²)` | `−494093/(2²³·5³·41²)` | `83163959690503562684611/2⁸²` |
| 8 | `1484327582024039537461868631154564575/(2²⁴·(2⁵²+1)²)` | `−659173863059710090719/(2⁷⁴·(2⁵²+1)²)` | `62587632561350452267109439670114075243/2¹³⁰` |

The denominators are the reference changes' own: `(G + G')²` for the moves `2⁴²`, `2⁸`, `2⁸`, `2¹⁰`
and `2⁵²` of contact 0's conductance listed in §2.3 (at reception 7, `(2¹⁰ + 1)² = 5⁴·41²` with one
`5` cancelled). The test pins the closure, the dissipativity, `lift_emits` and the zero excess at all
eight (`the_chained_balance_closes_and_the_chain_is_dissipative`).

[proved-derived; formal-checked] The chained balance, its dissipativity and the rest case as its
limit are `HNN/ChainedBalance` (#293; §2.3 above). The opening's split is
`½⟨r, Q(2z − r)⟩` for any symmetric block form `Q`, within
`½ Σ_i c_i (2|(Qz)_i| + Σ_j |Q_ij| c_j)` when every remainder lies in its half cell `c_i`, and zero
on the lattice (`opening_split_eq`, `opening_split_le`, `splitBound`, `opening_split_on_lattice`).

### 2.3b A deposit can lower a contact's mass; the momentum holds either way, and the rise is the deposit's work

[proved-derived; measured-exact where marked] The question (October 3, after #293): #293 proves the
stronger reading, deposition plus ingest at most the next word's loss, only for deposits that add
mass (`ΔC ⪰ 0`) and move no other coordinate of the constitution (§2.3a). Can a production deposit
lower a contact's mass? If it can, does the remaining mass keep its momentum, or does the leaving
mass carry its own momentum away?

1. **A production deposit can lower the mass.** The contact's storage is a Gram, `C_a = c cᵀ`
   (`hnn/constitution.rs`, module header, "Loci"). The factor step moves the factor,
   `Δc = η G / h′` ("Deposition", `h′` the carried successor statistic), so
   `ΔC = c Δcᵀ + Δc cᵀ + Δc Δcᵀ`. Neither the step's sign nor its certificate confines this to
   `⪰ 0`: `C′ = c′c′ᵀ` stays passive, but `ΔC` need not. A shrink of the factor, `Δc = −εc`, gives
   `ΔC = −(2ε − ε²) C ⪯ 0` for `0 < ε < 2`, and a turn of the factor gives an indefinite `ΔC`.
   [measured-exact] Astra's control deposit is
   `ΔC = [[0, −2^(−13)], [−2^(−13), 24577/2^26]]`, from the
   [storage-resolution record](2026-10-02_A_STORAGE_DEPOSIT_IS_FELT_ONLY_THROUGH_THE_RATE_S_JUMP_AND_THE_WORD_HOLDS_IT_BELOW_ONE_UNIT.md)
   §5, the native comparison's own return. Its determinant is `−2^(−26)`, so it lowers the mass
   along one direction and raises it along another.
2. **The momentum hold does not rest on mass arriving at rest.** The
   [deposit record](2026-10-03_THE_DEPOSIT_HOLDS_THE_CARRIED_MOMENTUM_AND_THE_ACCRETED_MASS_IS_THE_THROWS_DAMPING.md)
   item 3 derives the hold from the transit's canonical state. `u̇ = ∂P/∂π` and `π̇ = −∂P/∂u` stay
   bounded across a jump of `C`, so `(u, π)` is continuous for either sign of `ΔC`. The sticking
   mass (`accretion_loss`) is the scalar case that record illustrates, not its premise.
3. **No mass leaves at the carrier's speed, because no mass is carried.** The ejection law, in which
   the rest keeps its velocity and the leaving part takes `½|Δm| v²` away, needs a departing body
   with its own momentum and a port it leaves through. The junction's reflection (§2.3a) has both:
   the reflected wave is a wave of the tube, and it leaves on the `G` side. A deposit has neither.
   It is the one law that changes a constitution (the
   [elementary objects](../../docs/ELEMENTARY_OBJECTS.md) §8). It changes the factor `c` through
   which the contact's coordinates store, and the field's state stays the contact's `(u, π)`. The
   constitution is the material law, not a substance moving with the motion, and no port carries a
   part of it away. A storage law that changes under a motion held at its momentum is the parametric
   case. The constitution's change does work on the motion, as a pump does: in the elementary
   objects, a pump is a modulation of the constitution, and it boosts through the storage's own
   motion. Shrinking a pendulum's length at held angular momentum is the same law.
4. **So the carried energy can rise, and the rise is the deposit's work.** With `C′ = C + ΔC` and
   the held rate `C′w′ = Cw`, the change is
   `½⟨w′, C′w′⟩ − ½⟨w, Cw⟩ = −½⟨w′, ΔC w′⟩ − ½⟨w − w′, C(w − w′)⟩` (`held_momentum_loss`). It is
   positive exactly when `⟨w′, ΔC w′⟩ < −⟨w − w′, C(w − w′)⟩`. That work is supply from the deposit,
   entered in the chained balance as `deposition_k`, which the commit reads exactly
   (`PowerForm::held`).
   - The chain stays dissipative with respect to its declared supply at every reception (#293).
   - The stronger reading is a law for deposits with `ΔC ⪰ 0` that move no other coordinate of the
     constitution (#293, §2.3a), not for every production reception.
   - Under a shrink the bound is the mass certified from below:
     `C′ ⪰ C/(1 + ε)` gives `½⟨w′, C′w′⟩ ≤ (1 + ε) ½⟨w, Cw⟩` (`held_momentum_bound`).
5. [measured-exact] **The sign is the motion's.** On the control, the work at held momentum was
   `−7³·13·34403/(2^23·5²·31²·37²)` (storage-resolution record §9.4), so it fell even though `ΔC`
   is indefinite: along `w′` the deposit added mass. The work's sign does not fix that by itself,
   since the jump's energy also enters; the reading does. With §9.4's opening rate
   `w = (−1/16, 39/1024)` and jump `δ`, `½⟨w, ΔC w⟩ = 3·13·2007079/2^47` is the work at the held
   rate, and `⟨w′, ΔC w′⟩ = 3·7²·13·41·109·8599·429259/(2^20·5^6·31^4·37^4) > 0` at `w′ = w + δ`.
   On the chain fixture no deposit moves a contact's storage, which is why the stronger reading's
   8 of 8 there is the lift's alone.
6. **Code.** Unchanged. The carry (`ReceptionCarry::crossed`), the commit (`PowerForm::held`) and
   the continuation (`ContactCut::continue_deposited`) already hold momentum for either sign, and
   they read the deposit's work exactly. No new law enters: the derivation uses
   `held_momentum_loss`, `held_momentum_bound` and #293. [agent-inferred] The deposit record's §5
   item 4, a per-reception reading of `ε′` with `C_(k+1) ⪰ C_k/(1 + ε′_k)`, stays a proposed reading,
   not a refusal. A refusal of shrinking deposits would author a sign the constitution does not
   carry.

### 2.4 The clock

[definition; agent-inferred] The carried state is read on the field's own elapsed ticks.
`Word::continuing` takes `opened_at`. Under the carry, `t_(k+1)` is the sum of the ticks every
earlier word of the chain executed, so a declared resonator's pump phase continues across
receptions.

Today every reception re-phases the pump to zero, a reset of the pump clock that the carry removes.
The rest case of `tests/prediction.rs:66` opens at tick zero, while the carry opens at the
cumulative tick. On a field with a declared resonator the two differ in the pump's phase even when
the carried change is at rest, unless the cumulative tick at the opening is a multiple of every
pump period.

[definition; agent-inferred] **The exact limit is claimed for fields with no declared resonator.**
That is U6's default (`resonator none` in `hnn_exposure.rs`) and every field the exposure and the
U6 reads run today. There `A = I` is today's word exactly, whatever the cumulative tick. On a field
with a declared resonator the carry keeps the cumulative clock, and no exact limit is claimed: the
pump phase is a second carried quantity, and a read under such a field compares it as such. A
clock reset at every opening is not taken: it would restore the hidden restart of the pump that
the carry exists to remove.

### 2.5 The adjoint stops at the opening

[definition] Each word's return reads its own ticks only. The covector reaching the carried
opening, `∂ℓ/∂x(0)`, would continue into reception `k`'s word, but that word was consumed at its
compare. So it is returned as a reading and deposited nowhere: deposition reads only covectors that
reached their locus, and no tape of words is kept. Learning shapes the carry through `Θ`, which
governs every word's motion, including the motion the next word carries.

### 2.6 Where the carried change lives

- **The resident, not the current.** Guard 16 ("`Current` holds the lift point and nothing else";
  `mod.rs:104`) stays. Under the carry, the resident holds one `EndChange` and its tick. The
  refinement's return writes them when it consumes its word (a compare, or a discard at the budget
  stop: the motion happened either way, and a discard carries no deposition work).
- **One chain.** A refinement opened while another refinement is pending would have no defined
  predecessor, so under the carry the refine refuses that opening. Exposure holds one pending at a
  time.
- **The saved state.** The carried change and its tick are part of the continuing state, written
  inside its check (built, §6). A state at rest writes none, so every state written before the carry
  reads back at rest, which is today's law.
- **The card.** The device word owes the same opening: the carried change resident on the card,
  read by the next word, with host-card parity. Receptions were already sequential (a deposit
  separates each pair), so carrying them costs no co-presence.

## 3. What it is not

- **Not the throw.** The throw carries momentum `P = dH` in the parameter coordinates between U6
  moves. The reception carry is the field's motion between receptions. They compose, and neither
  replaces the other.
- **Not `ContactCut::continue_deposited`.** That owner continues within one refinement across a
  contact deposit, certifies by the native unit certificate, and refuses other loci. The reception
  carry crosses every deposit. Loci that leave the power form unchanged do zero work, and the rest
  is read by `CommitWork`, so it needs neither the refusal nor the unit certificate's same-locus
  restriction.
- **Not a context.** Nothing about which windows preceded is carried, only the field's present
  motion. Two passages that leave the same end change open the next reception identically.

## 4. The claim fixed before the code

- At `A = I`, the carry path reproduces today's exposure receipt on the gate state byte for byte:
  every reading, deposit and balance.
- At `A = 0`, the chained balance (§2.3) closes exactly at every reception, and the chain is
  dissipative with respect to its declared supply within the residuals' certified bounds.
- Under the carry, a saved carry restores the chain's next opening exactly, and a damaged one is
  refused.

No score, seed or held-out read decides the carry. The production default stays rest; a change of
the default is a derivation and its exact checks, together with the device word's parity (§6).

## 5. Owners touched when built

`word.rs`'s module header ("Continuing motion within a refinement" becomes "within and across
receptions") and its law table row "the word opens at zero" (`mod.rs:121`, which then reads "at the
rest limit"); `pending.rs` and `reference.rs`'s refine (open on the resident's carried change);
`constitution.rs`'s `ContinuingState`; the device word; `tests/word.rs:33` (it states today's law and
becomes the `A = I` case); Lean `HNN/Retention.word_opens_at_zero` (the rest case) with the chained
balance in `HNN/ChainedBalance` (#293). The atlas rows for these owners update in the same commit as
the code.

## 6. Built (October 3), and what the read needs first

[implemented-exact; agent-inferred where marked] The carry is built through the production path, not
a test path. Today's reception is unchanged unless a carry is declared.
- **The switch.** `Reference::with_reception(Reception::Carry(absorption))`; the default is
  `Reception::Rest`, which keeps `Word::open_charted` exactly. `Absorption::{Complete, Nothing}` are
  `A = I` and `A = 0` (§2.2); nothing in between is built.
- **The opening.** `Reference::refine` → `PendingRatio::read_on` → `Word::open_received`, which
  zeroes each source ring's storage in the carried change (`Π_int`) and calls the unchanged
  `Word::continuing` with the moment's open storage at the carried tick (§2.1, §2.4). The compare's
  re-read at a later commit, the deposit's re-read at the successor (`Arrived`) and `release` open on
  the same opening, which the pending slot holds beside the ratio, never inside it (guard 3).
- **The carry.** The compare writes the resident's one carried change (`Resident::carried`) from the
  word its return consumes (`Word::reception_end`: the end change and `opened_at` plus the word's
  junction steps), after the boundary's absorption (`ReceptionCarry::absorbed`). A discarded pending
  ratio carries its refine's word's end (§2.6). A refinement opened while another is pending is
  refused (one chain). The resident's state bits count the carried change's nonzero values and its
  tick.
- [agent-inferred] **A declared resonator under `A = 0` is refused.** The last junction step
  advances the hop clock without a pump step, so the carried resonator state, measured at its last
  pump tick's phase, does not fit the next opening's clock (`Word::continuing`'s check). The pump's
  carry across receptions is owed; under `A = I` a resonator opens at rest in the carried clock.
**The acceptance read** (`crates/holonics/src/hnn/tests/reference.rs`, "the reception carry";
`tests/lock_face.rs`):
- at `A = I` the prequential exposure on the chain field returns every reading, deposit, balance
  and curve point of the exposure at rest, bit for bit; only the resident's state bits read more, by
  the carried tick;
- under `A = 0` every compare writes its consumed word's end at the summed junction steps, and the
  next refine's faces are exactly the read on that opening, opened from the carry as written and
  read back (`ReceptionCarry::{write, read}`); the carried interior moves the read;
- under `A = 0` the chained balance (`ChainedBalance`, read in `expose_from` at every reception
  opened on the previous word's end) closes exactly at all eight readings, the chain is dissipative
  at all eight, the lift only emits at all eight, and the stronger reading holds at all eight
  (§2.3a; on the carry first built, which kept the waves, it failed at reception 7, §2.3);
- `ContinuingState` carries the reception's end (`with_carry`, `carry`) inside its check, before its
  clock line, so the stamp still replaces only what follows the storage product; a state at rest
  writes no carry and reads back at rest; one byte changed inside the carry is refused as damage;
  `Constitution::continued` does not read the carry, which is resident motion, and
  `Reference::mount_carried` mounts it beside the declared constitution, refused at rest or on
  another field's shape.

[agent-inferred] The carry's restore is exact at the word it opens, which is what the carry
determines. The rest of the reference resident (its open moments and the aeon in progress) is not a
saved object of this path; it is restored only where the executed path's continuing state already
restores it.

The chained balance's Lean statement is `HNN/ChainedBalance` (#293). The device word is built with
host-card parity (§7). The within-refinement continuation (`ContactCut::continue_deposited`) now
holds the momentum across its contact deposit as well (the deposit record §5 item 2). Its law is
redone at held momentum in the
[storage-resolution record](2026-10-02_A_STORAGE_DEPOSIT_IS_FELT_ONLY_THROUGH_THE_RATE_S_JUMP_AND_THE_WORD_HOLDS_IT_BELOW_ONE_UNIT.md)
§9; its Lean is `HNN/StorageResolution` §5 (#290). Guard 16 of
[THE_MACHINE](../../docs/THE_MACHINE.md) reads that no change outlives its word or its refinement;
under `A = 0` the end change outlives its refinement into the next reception's opening, as this
record derives. The guard is amended to say so, with rest as the default that keeps it as stated.

## 7. The device word (October 3)

[implemented-exact; agent-inferred where marked] The card's word opens on the carry exactly as the
host word does (`holonics-cuda`: `hnn::carry`, `hnn::port`, `hnn::execute`, `kernels/hnn_word.cuh`).
- **The carried change stays on the card.** The consumed word's storage, arrivals and states are
  copied into a buffer of their own on the card (`ResidentWord::end_words`); the next word copies them
  into its own change before its open. The host keeps the reference's carry as a mirror read from the
  consumed word's record (`CardCarry::ended`: the end change, the elapsed ticks, the cut's
  conductances and the momenta `C_a w_a`), which the chained balance, the state's bits and a saved
  continuing state read. `Resident::mount_carried` uploads a restored carry.
- **The crossing runs in the card's open** (§2.3a, the deposit record §3). Each carried wave is
  transmitted, `a′ = 2G/(G + G′)·a`, from the plan's reduced gain; each rate is held,
  `w′ = w + δ`, where `δ` is read from the host owner `ReceptionCarry::crossed` against the
  publication's storage forms (agent-inferred: the card's words carry no exact preimage solve).
  Both leave the dyadics, so the card splits them onto `L_w` over their denominators
  (`hnn_split_over`: `s = q·D·2^k + r`, ties upward, the host's `Lattice::div_rem` at `s/(D·2^k)`)
  and carries each remainder over its denominator through every later split of the word. At rest
  every denominator is one and the word's path is unchanged.
- [agent-inferred] **The card refuses a declared resonator on a received opening**: under `A = 0`
  as the host does; under `A = I` because the card's pump phase reads the word's own ticks from
  zero, not the field's elapsed ticks. That phase offset on the card is owed (#76).

**The parity read** (`crates/holonics-cuda/src/hnn/port_tests.rs`, alone on the card): on the
chain with no pair offset (the host's carry fixture, 18 cells, 9 windows, the campaign-one
declarations), every return of the lockstep is the reference's and the carried end is
byte-identical as saved text after every compare:
- under `A = 0`, all 8 receptions open on a carry; on this cut the lift moves a carried wave's
  conductance at 4 of them and a deposit moves a carried rate off its momentum at 2, so both
  crossings and their denominators run; the card's whole exposure equals the reference's, its
  chained balance closing at all 8 with a nonzero opening split; a carry saved as text and restored
  on both ports opens the next word alike;
- under `A = I`, all 8 receptions, every return the reference's;
- under `A = 0` from the generic constitutions 5 and 11 on the chain with `Δ = {1}`, 11 receptions
  each, every return the reference's;
- at rest, the existing locksteps unchanged. Zeroing either opening remainder on the card fails the
  first test at its first refine on a crossed carry.
