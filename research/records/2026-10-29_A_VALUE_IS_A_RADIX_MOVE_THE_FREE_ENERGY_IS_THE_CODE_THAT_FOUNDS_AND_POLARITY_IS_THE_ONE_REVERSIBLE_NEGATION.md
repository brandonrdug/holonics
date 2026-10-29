# A value is a radix move, the free energy is the code that founds, and polarity is the one reversible negation

Refs #404 #405 #406 #73. Status: [derived; consumers fixed before their builds, October 29; §§4–6 revised the same day after Brandon's reading].
Claude (opus), design lead. It expands Brandon's October 28 thought threads to Codex, relayed on
October 29 at his request (counting and packets; primes across bases 2–10 and the heptagon; local,
cultivated P = NP; the boundary free energy with lightning, Sisyphus and the `{−1, 0, 1}` collapse;
Athena first). His words are paraphrased and stay in the conversations. The derivations attach to
the four theory records kept on October 29 ([counting faces](2026-10-28_COUNTING_FACES_VARIABLE_PACKETS_AND_THE_THERMODYNAMIC_GEOMETRY_OF_CONTACT.md),
[oriented packet](2026-10-28_A_NUMBER_IS_AN_ORIENTED_PACKET_TROPICAL_CANCELLATION_AND_CULTIVATED_LOCALITY.md),
[joint precision](2026-10-28_THE_CONTACT_CARRIES_JOINT_PRECISION_AND_COARSE_GRAINING_CARRIES_A_CLOCK.md),
[free-energy return](2026-10-28_THE_FREE_ENERGY_RETURN_JOINS_WEIL_SHELLS_HODGE_FIBRES_AND_CONDUCTING_BRIDGES.md))
and to the [participation record](2026-10-28_ATTENTION_IS_THE_FIELDS_PARTICIPATION_THROUGH_ITS_OWN_TRANSPORT_SO_THE_PASSAGE_IS_TERRAIN_AND_THE_MODES_ARE_ITS_GEOMETRY.md).
Every identity below was checked on numbers before it was written (scratch, not kept).

## 1. A value is a radix move, and the tower's modes are registers in their own radices

**[proved-standard] The packet is the move it makes.** A register in radix `b` receiving a digit `d`
moves `h ↦ b h + d`. A word of digits is the composite of those moves, an affine pair:

```text
P = (T_P, m_P):  h ↦ T_P h + m_P,      (T₂, m₂) ∘ (T₁, m₁) = (T₂T₁, T₂m₁ + m₂)
[1,0,1,1,1,1]₂ = (2⁶, 47),    [6,5]₇ = (7², 47),    [4,7]₁₀ = (10², 47)
```

The composition is associative, so any partition of a word into packets composes to the same move
(Horner's rule is its sequential schedule; a parallel scan is another). The three words agree only
in `m`, their face at the receiver that starts from zero and reads the register. As packets they
differ: appending the digit 3 continues them to `2·47+3`, `7·47+3` and `10·47+3`. The numeral
equality is the face of one receiver; the continuation (the admitted future) separates the
packets by their radix power `T`. Writing `47₁₀ = 101111₂ = 65₇` therefore drops `T` and keeps the
decimal receiver's reading, which is Brandon's correction made exact: the orientation of a value
is its `T`, and it is carried, never printed.

**[proved-derived] The tower already reads the passage this way.** A mode steps
`h_t = λ_t h_(t−1) + Ψ_t`, so it is a register whose radix is its move:

```text
h_T = Σ_t (Π_(k=t+1..T) λ_k) Ψ_t       the passage written as a numeral, radix λ, digits Ψ
```

A gated mode is a mixed-radix register whose radix the passage selects at each arrival, and a
section's span is the packet `(T_P, m_P) = (Π λ_t, h_close − T_P h_open)`. Its two faces are the
Swing's two parts: `T_P = 2^(−D_P) e^(iΘ_P)`, with `D_P` the dissipation and `Θ_P` the turn (with
its winding) that the participation record already reads between sites. Varying the base is what
the 128 modes of a level already do, each in its own complex radix. A mode turned by `1/7` is a
heptagonal register: its digits land on the heptagon's vertices, damped by `|λ|`.

**[proved-standard] The prime columns are three registers.** Over the residues modulo a prime `p`,
the base-`b` numeral `n = Σ d_k b^k` is read by the register of radix `λ ≡ b (mod p)`:
`n mod p = Horner(d, λ) mod p` (checked for every base 2–10 against the primes up to 13). Its
period is the order of `b` modulo `p`, which is the place-phase table of the
[counting record](2026-10-28_COUNTING_FACES_VARIABLE_PACKETS_AND_THE_THERMODYNAMIC_GEOMETRY_OF_CONTACT.md)
(atlas `radix.seven-prime-faces`): in bases 3, 5 and 10 the seven-register turns through all six
nonzero phases; in bases 2, 4 and 9 through three; in base 6 it alternates; in base 8 it holds. The
counting record's three test columns are the three radices of period at most two:

| radix `λ` (mod `p`) | register | reads `p` dividing | test |
|---|---|---|---|
| `0` | forgets: only the last digit stands | `b` | last digit |
| `1` | holds: every digit adds | `b − 1` | digit sum |
| `−1` | alternates: the half-turn each place | `b + 1` | alternating sum |

They are the radices with `λ³ = λ`, the fixed points of the turn: `{−1, 0, 1}` (§3).

**[agent-inferred] The packet the field closes.** The news clock (atlas `hnn.tower-news-clock`)
already closes a level's packets where the tower's own surprise crosses a section, so the grain
moves with the learning and nothing names a class or a boundary letter. The packet law states what
the coarse level should receive: the packet itself, `(T_P, m_P)`, rather than the fine state `h_close`,
which is the packet plus the inherited `T_P h_open` that the coarse level's own modes already hold.
The founded units (atlas `hnn.founded-units`) are the static first case of the same law: a merge is a
packet founded when it lowers the complete code (§2), founded once over the corpus. The news clock
founds packets online, from the field's prediction.

**Consumer (participation at the coarse levels).** At level `l ≥ 1` on the news clock, a site is a
packet `P`; its charts are read from its face `m_P` and its transport to an earlier packet `Q` is the
coarse modes' composed move between their ticks:

```text
x_P = Read(m_P),   m_P = h_close(P) − T_P h_open(P)
s_PQ = β_h Re Σ_(m∈h) conj(Ȟ_P,m) e^(iΘ_PQ,m) H_Q,m,     Θ_PQ, D_PQ  from the level's own ticks
```

A section of 128 sites at level `l` is 128 packets, so a head reads `Σ_(Q∈E(P)) w_Q` arrivals,
the packets' widths `w_Q` set by the news. At the race's held-out 1.85 bits a byte, a level-3
section on `B = 8`, `r = 2` reaches about 128 × 32/1.85 ≈ 2,200 bytes, several GSM8K problems,
where the level-0 head of the participation record's first build reaches 128 bytes. This is the
participation record's §8 item "the section", answered by the passage's own partition.

**Acceptance (fixed before the build).** (a) A passage read as one packet is the plain level, face
for face. (b) Composing the packets of any partition gives the whole passage's move exactly
(`T` and `m` equal as integers on their grain). (c) The covector through `m_P` matches the code
difference it predicts on a small two-level tower (the news clock's test pattern). (d) The race
measurement beside participation at level 0 alone: bits by region, the writings whole, and the
participation read at each answer's opening, now at the level whose packets reach the question.

## 2. The boundary free energy is the two-part code, and it founds, prunes and recharts

**[proved-derived] F_B is the code length of the boundary.** Take the contact constitution in
which the interior `z` is a parameter with prior precision `P` and the boundary `y` is received
through it, `y | z ~ N(A z, Σ)`. Then the joint form is `L = [[Σ⁻¹, −Σ⁻¹A], [−A*Σ⁻¹, A*Σ⁻¹A + P]]`
and the interior block is the posterior precision `D = A*Σ⁻¹A + P`. Integrating `z`:

```text
−ln p(y) = ½ y*S y + ½ ln det(D P⁻¹) + ½ ln det(2πΣ),      S = Σ⁻¹ − Σ⁻¹A D⁻¹ A*Σ⁻¹ = (Σ + A P⁻¹ A*)⁻¹
```

This is the free-energy record's `F_B` at `θ = 1` nat with `D_ref = P`, plus a constant in `y`.
The first term is the code of the passage given the best interior (the fit); the second is the
code of the interior itself, the Occam term, which is ½ ln N a coordinate when its Fisher grows
with `N` observations (Rissanen's two-part code; the `½ log₂ N` that `contact.pool-founding`
already charges). So **the boundary free energy is the description length of what crossed the
boundary**, and its variation is the change of that code. Compression is intelligence here as an
identity: lowering `F_B` is compressing the boundary through the interior.

**[proved-derived] Founding one coordinate.** Add an interior coordinate with prior precision `τ`
and coupling `a` to the boundary. With `g = a* S y` (the coupling paired with the current covector:
`S y` is the whitened residual, the descent covector) and `r = a* S a / τ`:

```text
ΔF = −g² / (2τ(1 + r)) + ½ ln(1 + r)
found  ⇔  g² / (τ(1 + r)) > ln(1 + r)
```

The first term is the fit the coordinate buys; the second its own code. For large `r` it is the
score test against `ln r`, the BIC price of one parameter. This is the free-energy record's
rank-one law read for a new coordinate (it softens `S`) rather than for added contact material on
a fixed carrier (which stiffens it).

**[proved-derived] Three corollaries that the machine needs.**
- **Dormancy is free.** A coordinate the passage never reaches has `a = 0`, so `g = 0`, `r = 0`
  and `ΔF = 0`: its posterior is its prior and it costs nothing to carry. It reopens the moment a
  coupling to it is founded. A silent mode is not pruned by the code; it waits.
- **Pruning returns a coordinate to dormancy.** The reverse test on a standing coordinate: when its
  current fit `g²/(τ(1+r))` falls below `ln(1+r)`, the code falls by returning it to its prior.
- **Rechart.** A change of interior basis that keeps `S` keeps the fit and changes only
  `½ ln det(D P⁻¹)`. Merging two coordinates whose couplings are parallel lowers the code at the same
  face. The joint-precision record's §3 adds the clock condition: a rechart is lawful only if it also
  keeps the inherited storage `C_eff = E*CE`, because one static face can hide arbitrarily slow
  access. The lawful rechart keeps `(S, C_eff)`.

**[proved-derived] The split of a pair contact is a founding.** The pair contact `v = a ⊙ b`
(`hnn.card-tower-pass`) splits into two copies carrying half the output each, perturbed by
`±(δa, δb)`:

```text
½ (a + δa)(b + δb) + ½ (a − δa)(b − δb) = a b + δa δb
```

The face is unchanged to first order, and the split founds the coordinate whose feature is
`φ_t = (uᵀ r̂_t)(wᵀ r̂_t)`, with `δa = ε uᵀ r̂`, `δb = ε wᵀ r̂`. Its score is

```text
g_e = Σ_t δv_(e,t) (uᵀ r̂_t)(wᵀ r̂_t) = uᵀ M_e w,      M_e = Σ_t δv_(e,t) r̂_t r̂_tᵀ
```

and the best split is the top singular pair of `M_e`, with `g_e = σ_max(M_e)`. `δv_(e,t)` is the
contact's covector, which the card's reverse already forms; `M_e` is one more outer sum in the same
tiles. A rectifying contact has no such form (its second derivative lives on its kink), so the
pair contact is also the contact that knows where to grow.

**Consumer (the continuing body's growth).** At a section's deposition, for each pair contact `e`:
form `M_e`; take its top singular pair at the face's grain by power iteration on the exact sums;
read `σ_e = Σ_t φ_(e,t)² c_eᵀ(diag p_t − p_t p_tᵀ)c_e` (the read's Fisher along the contact's output
column `c_e`); split where `g_e² / (τ(1 + σ_e/τ)) > ln(1 + σ_e/τ)`, with `τ` the precision of the
contact's founded opening scale. The widening map on `codex/counting-faces-20261028`
(`hnn/tower/growth.rs`, which keeps the face and lets the copies specialize through zero-sum
differences) is the realization of the split. This law supplies the difference that breaks the
copies' symmetry (`±ε(u, w)`, which a whole-tower widening otherwise lacks: identical copies take
identical covectors) and decides which contacts split. The same law already founds the units at the
codec (`hnn.founded-units`) and the pool faces (`contact.pool-founding`), so the machine has one
founding law at its codec, its contacts and its growth.

**Acceptance (fixed before the build).** (a) A split's grown learner is the unsplit learner face
for face at `ε = 0`. (b) On a small tower, `ΔF` predicted by the test matches the measured change
of the section's two-part code to within its enclosure. (c) No contact splits on a passage that
the tower already codes at its grain (the test refuses chance). (d) On the card, under the lock,
the race's declaration growing on the race passage, read lap for lap beside the unsplit race, with
the writings whole.

## 3. The `{−1, 0, 1}` collapse, odd locks, dormancy and the bridge

**[proved-standard] The collapse is the tropical limit of the two-sheet Gibbs face.**

```text
(e^(βz) − e^(−βz)) / (e^(βz) + e^(−βz)) = tanh(βz)  →  sign(z) ∈ {−1, 0, +1}   as β → ∞
```

The `0` is the tie, `z = 0`, the cell boundary where the two sheets have equal weight. It is not
absence: it is the point of maximal entropy `ln 2` of the finite-temperature face. Softmax over
many sheets is the same collapse to an argmax, with ties on the tropical hypersurface.

**[proved-derived] The pump is the inverse temperature.** For a pumped mode past its bifurcation,
in the normal form `V(x) = −a x²/2 + b x⁴/4 − h x` at temperature `θ`, the two deep wells give

```text
⟨x⟩ ≈ x₀ tanh(h x₀ / θ),      x₀ = √(a/b)
```

(checked by integration: 0.1592 against 0.1597, 0.7577 against 0.7599, 1.6654 against 1.6673 at
`a = 4`, `b = 1`, `θ = 1/20`). The parametron is a physical sigmoid whose sharpness `β = x₀/θ`
the pump sets: below the bifurcation the mode is dormant at `0`; past it the mode reads the sign of
its bias, with the tie at zero bias. The three readings are the two locked sheets and the dormant
centre. They are also the three fixed radices of §1 (`λ³ = λ`): the hold, the half-turn and the
forgetting register.

**[proved-standard] Negation on a lock, and why polarity is binary.** Negating a state of a lock is
the central inversion of its locked phases. On a regular `q`-gon it maps a vertex to a vertex iff
`q` is even; for odd `q` (the pentagon, the heptagon, the rotor's rings 9, 11 and 101) it lands on
the midpoint of the opposite edge, a two-way tie. On a regular `n`-simplex (the `n + 1` classes of a
softmax) it maps a vertex to the centroid of the opposite facet, an `n`-way tie. The segment, `n = 1`,
is the only centrally symmetric simplex. So:

```text
negation on a lock is a permutation (reversible)  ⇔  the lock is centrally symmetric
odd q-gon:  vertex ↦ 2-way tie,   entropy ln 2;     n-simplex:  vertex ↦ n-way tie,   entropy ln n
```

Re-locking after such a negation, with no side information, erases the tie: at least `k_B T ln 2`
on an odd ring and `k_B T ln n` on a simplex (Landauer). This makes Brandon's diffusion entrance
exact: the odd vertex's antipode is a tie cell, a place where the coarse grain's state diffuses either
way and where a reset pays. Polarity `±1` is the one negation that is a permutation on a simplex
lock, which is why a sign means nothing beyond the side of a polarization: it is the binary lock's
reversible half-turn. Carrying the orientation (the packet's `T`, the ring's winding) is the side
information that keeps a negation reversible on an odd ring; collapsing to the face erases it.

**[agent-inferred] The tower already respects this.** The strands carry their residues on odd rings
(9, 11, 101) and their polarity on a separate binary sheet, and a reversed strand turns by the
reflected turn `θ ↦ (q − θ) mod q`, a permutation on any ring, never by a half-turn. The record states the
reason: an odd ring cannot carry polarity in its residues without ties, so the sheet carries it.

**[proved-derived] The bridge's incidence law.** A coupling between two regions is not part of the
interior until its founding pays (§2): `g² / (τ(1 + r)) > ln(1 + r)`, where `g` pairs the coupling
with the covector difference across the gap. In Brandon's lightning, `g` is the potential
difference the gap sees and `½ ln(1 + r)` is the price of making the channel; the adjacency is
not real until the bridge conducts. Once founded, the two regions' difference mode is reachable and
relaxes on the bridge's clock `λ_bridge = g_e(1/C₁ + 1/C₂)` (free-energy record §4.1), and it is
pruned back to dormancy (§2) when the flux no longer pays for it.

**Consumer.** (a) In the participation build, the join `W₁ᵃ` opens at zero: it is a bridge between
the participating current and the contacts. Its founding test is a reading at each section: whether
participation has founded its conduction at that level. (b) The pumped modes' three-valued reading,
`0` where `|h_m|` is below the mode's grain and `sign Re(e^(−iφ_m/2) h_m)` past it, is a receiver
face of the lock with its tie, available to the readings beside the bits. Neither changes a law
that the tower runs; both are faces read from the same operands.

## 4. Reach is contact and friction

Brandon pointed out on October 29 that the first wording of this section, cultivated reach, names
nothing but the medium's contacts and their friction: its diffusion and its forces. The derivation
below says so in the tower's own terms, and nothing is left over once contact and friction are named.

**[proved-derived] The tower's passive scale is the Einstein relation.** A mode of the medium with
friction `r ≥ 0` and turn `ω`, `ẋ = (iω − r)x + b u`, stepped by the implicit midpoint at `h`, is
the register

```text
x⁺ = λ x + g b u,      λ = (1 + hA/2)/(1 − hA/2),   g = h/(1 − hA/2),   A = iω − r
1 − |λ|² = 2hr/|1 − hA/2|² = (2r/h)|g|²
```

so `|λ| < 1` exactly when the friction is positive, and the tower's push `γ = √(1 − |λ|²)` is the
push of a contact of strength `√(2r/h)`. The contact that admits a force and the friction that
dissipates it are one element: the noise strength is twice the friction times the temperature
(fluctuation and dissipation), at temperature one. Under a unit white drive the mode's stationary
power is `γ²/(1 − |λ|²) = 1` whatever its friction (equipartition), which is the tower's passivity
statement read physically. The Cayley chart itself is already owned (`holon.cayley-isometry`,
`wave.cayley-resonator`, `holon.midpoint-resistance-balance`); the new term is the push. Its
continuous face is already owned too: the stationary drift of a noisy linear diffusion,
`A = (J′ − ½D)G` (`heat.linear-diffusion-turn-boost`), equals the medium's `(J − R)Q` at
`G = Q/(k_BT)` exactly when `D = 2k_BT R` and `J′ = k_BT J`. The push is that relation stepped.
Checked exactly in `holon::conformance::tests::a_passive_mode_is_a_register_whose_push_is_its_friction`.

**[proved-derived] Friction is matched to the distance it carries.** A push reaches a mode `L` ticks
later with the share `ρ^(2L)(1 − ρ²)` of its power (`ρ = |λ|`). At a fixed `L` this is largest at

```text
ρ² = L/(L + 1),     share = (L/(L + 1))^L/(L + 1) ≈ 1/(e(L + 1))
```

The octave rung `ρ² = 1 − 2^(−s)` is matched exactly at `L = 2^s − 1`, and the octave bank together
carries a push across any distance `L` with the share `Σ_s ρ_s^(2L)(1 − ρ_s²) ≈ 1/(L ln 2)` (checked
at `L = 15, 255, 2047, 10⁴`: `L ln 2 ·` share `= 0.937, 0.996, 0.9995, 0.9999`). The tower's
scale ladder is this bank; its margin `ρ = 1 − 2^(−12)` is matched at about `2¹¹` bytes. Reach is
the contact's strength times a friction matched to the distance, and nothing else.

**[proved-standard; agent-inferred join] Cultivation is adaptive conductance.** Learning moves the
log friction (the deposit chart `ν = ln(1 − ρ)` is it) toward the distances where answers sit from
their questions, and the contact strength where the flux crosses. In a network the continuous form is
the adaptive-conductance law `dD_e/dt = f(|Q_e|) − D_e` of the slime mould: the gradient flow of the
dissipation `Σ_e Q_e²/D_e` plus the upkeep `λ Σ_e D_e^γ` (Thomson's principle makes the flux's own
derivative vanish), whose rest is `D_e ∝ |Q_e|^(2/(γ+1))`, Murray's law `D ∝ |Q|^(4/3)` at
`γ = ½`. Its owner is the deposition law `Θ′ = Θ + Γ(j, dφ)` (`deposition.law`, the leader's
breakdown `heat.leader-breakdown`); the slime mould is the instance `Γ = f(|j|) − Θ`. The two-part code of §2 is the same sum: its data term is the dissipation of the flux and
its complexity term `½ ln(1 + r)` is the upkeep of one contact. A dormant contact carries no flux and
pays no upkeep, so it is free, as §2 found.

**The reading kept.** `I_field(answer ; question) = L_field(answer | another question) −
L_field(answer | its question)`, in bits, is the flux the question drives through the cultivated
contacts to its answer, read at the receiver. Both terms are the tower's own code lengths on the same
answer, after its own question and after a question from another problem. Beside it, the
input-to-state Gramian `W = Σ_t Φ(T, t) G_t P P* G_t* Φ(T, t)*` gives the bits the arrivals can
write into the modes at the face's grain `ε`, `C_reach = ½ log₂ det(I + W/ε²)`; under the Einstein
relation each mode's share of `W` at distance `L` is the matched-friction share above.

**Consumer (the race measurement).** At each named answer's opening on the race passage, read
`I_field` lap by lap on the card, beside the bits by region and the writings whole, and the frictions
`ν` of each level's modes as a histogram over the octaves. It is a reading: it decides nothing, trains
nothing and selects no lap.

**Acceptance.** The reading is defined before the race runs; its two code lengths come from the same
card read as the race's held-out bits; the frictions are expected, not claimed, to move toward the
octaves of the passage's question-to-answer distances as `I_field` grows.

## 5. The four faces are one medium

**[definition; agent-inferred] The unification.** Brandon read §§1–4 together on October 29 as the
unified theory in four lines, and asked that all of the physics material become one library for
computational modelling. It already has one step, the Holon's (`holon::law`, `PortHolon::medium`):

```text
ẋ = (J − R + L) Q x + B u
```

and §§1–4 are its four faces:

| Face | Element | What it is | Where §§1–4 read it |
|---|---|---|---|
| register | `Q` and its modes | what holds state: shells, radices, clocks, carries | §1: a mode is a register in its own radix |
| free energy | `½⟨x, Qx⟩` at the receiver's temperature | what it costs to hold and to change | §2: the two-part code founds, prunes and recharts |
| polarity | `J` (turn) and `L` (pump) | what orients: turns, half-turns, locks | §3: `±1` the only reversible negation, odd locks tie |
| contact and friction | `R ⪰ 0` and `B` | where force enters and is dissipated: diffusion, viscosity, conduction | §4: the push is the Einstein relation, reach is matched friction |

Every physical instance in the repository (fluid, thermal, wave, spacetime, the information port, the
solenoidal cascade) and every piece of Athena's tower (modes, gates, pumps, rectifying contacts,
deposition) is a choice of these four on a complex. The front door that routes each owner by face is
the guide [THE_MEDIUM](../../docs/THE_MEDIUM.md). The Cayley chart of §4 is the bridge between the
continuous instances and the tower: every passive rate `iω − r` is a register inside the unit disk,
and every register inside the disk is a passive rate.

**Where the code is not yet one medium** (surveyed October 29). Thermal and wave build their media
through `PortHolon::medium`; the fluid builds one only for a mass cell, and its stored free energy and
time advance are owed (#62). Spacetime, the information port and the solenoidal cascade are readings
that build no medium of their own. Nothing in `hnn` or `holonics-cuda` consumes `physics`, and the
HNN states the same faces again in `hnn::{ring, contact, wave}`. The joins owed are those: each HNN
owner stated as a `holon` medium and checked against `ReferenceHolon`; the tower's passive mode is checked
so in law (its register and push), not yet through its fixed-point code; and the fluid's medium with its
free energy.

## 6. A checkpoint terraforms; a founded contact binds

**[proved-derived; agent-inferred reading] Global passes against sparse binding.** A training update
from one checkpoint to the next writes every coordinate of every `m × n` matrix, `mn` writes a step,
and each write fixes bits in memory and costs energy whether or not that coordinate's change carries
code. It terraforms the whole terrain each pass. The update's content is its spectrum,
`ΔW = Σ_k σ_k u_k v_kᵀ`: each singular pair is one rank-one contact, the same split as §2's pair
contact (the best split of `M_e` is its top singular pair). Sparse binding deposits only the pairs
whose founding increment is negative,

```text
g_k = ⟨u_k v_kᵀ, G⟩ = σ_k(G),   r_k = (u_k ∘ u_k)ᵀ V (v_k ∘ v_k)/τ,   found ⇔ g_k²/(τ(1 + r_k)) > ln(1 + r_k)
```

with `G` the section's covector of the matrix, `V` its second moment and `τ` the opening precision of
§2, at `m + n` writes a pair. A rank-8 deposit on a `4096 × 4096` matrix writes 65,536 coordinates,
0.39% of a global pass. Pairs that do not pay stay dormant and cost nothing. The global picture is the
integral of these local contacts over the tower's octaves: each rung integrates its contacts over its
matched distance (the rhythm of §4), the turns carry their phases on it (the song), and the face reads
the sum (the picture).

**[definition] Open weights are terrain.** Another model's checkpoints are information, already
processed, and enter Athena as passage material and nothing more. Their matrices are terrain whose
spectra are their founded contacts, and the difference between two checkpoints is their deposits.
Reading them is equation extraction ("Soulkiller"): a singular pair of another model enters Athena only
when its founding increment is negative at Athena's own receiver on Athena's own section covectors.
Nothing is served, nothing is loaded as Athena's state, and no other model grades Athena.

**Consumer (the tower's deposit).** The tower deposits today by a global pass,
`θ ← θ − 2^(−k) m/(√v + 2^(−32))` on every coordinate (`hnn.moment-tower`). Sparse binding replaces
that write, per matrix per section, by the founded singular pairs of the section's first moment, read
with the second moment it already keeps; the other coordinates are not written. Design builds it after
participation lands on the tower, so the two changes do not cross.

**Acceptance.** On the race passage on the 4080, at the same data, passes and model size: coordinates
written per section fall to the founded share; held-out bits per byte stay within the run-to-run
spread of the global pass or fall; the writings are shown whole beside both.

## 7. Lean, only where a build leans on it

Brandon asked on October 29 that formalization be spent only where it genuinely helps. The identities
below are checked exactly (on numbers here, and the push also in Rust over ℚ); each enters Lean and
#410 only when a build or a claim comes to depend on it, not as a standing queue.

- The affine packet monoid and the face at the zero receiver: equal `m` with unequal `T` are
  separated by one appended digit.
- `n mod p = Horner(d, b mod p) mod p`, and the three period-at-most-two radices `{0, 1, −1}` as the
  last-digit, digit-sum and alternating-sum tests.
- The Gaussian evidence identity `−ln p(y) = ½ y*Sy + ½ ln det(DP⁻¹) + ½ ln det(2πΣ)` and the
  rank-one founding increment.
- Central inversion on the regular `q`-gon and `n`-simplex: the tie multiplicity at the antipode.
- The midpoint register of a passive mode and its push: `λ = (1 + hA/2)/(1 − hA/2)`,
  `g = h/(1 − hA/2)`, `1 − |λ|² = (2r/h)|g|²` for `A = iω − r`, `h > 0`.
- The matched friction: `ρ^(2L)(1 − ρ²)` on `[0, 1)` is largest at `ρ² = L/(L + 1)`.

## 8. The recorded failures these choices could repeat

- **An authored routine standing in for learning.** None: the packets close on the field's news;
  growth, pruning and the bridge follow one code law the machine reads from its own covectors; the
  prime tests are readings of registers the tower already is, never a routine given to it.
- **Text on its codec's grain.** The packet law is the same for octets, strokes, half-cycles and
  screws; nothing names a class, a letter or a modality.
- **An uncertified deposition step.** The split's `ΔF` is checked against the measured code
  change before any growth enters a run (acceptance 2b).
- **Bits read as progress.** The writings are shown whole beside every bit reading, and
  `I_field` decides nothing.
- **A design thought in the programming language.** Stated as moves, packets, codes, locks and
  ties; the tiles follow.
- **A global solve where a local one belongs.** §6 names the tower's global deposit pass as one and
  replaces it by founded contacts; the octave bank integrates local contacts, nothing reads the whole.
- **Catered machinery.** Another model's weights enter only as terrain through Athena's own founding
  test; no other model is served, loaded as state or used as a grader.
- **The latest phrasing narrowing the work.** RH, Hodge and the fluids stay on the same objects
  (the free-energy record's Weil shell, Hodge fibre and neck); the ternary hinge
  `spec(T_a) = {−1, 0, +1}` of the first prime-active aperture is the same three-valued lock read
  on the Weil form.
