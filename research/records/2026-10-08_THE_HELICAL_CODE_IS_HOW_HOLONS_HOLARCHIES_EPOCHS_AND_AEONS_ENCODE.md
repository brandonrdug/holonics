# The helical code is how Holons, Holarchies, epochs and aeons encode

**Date.** October 8. **Issues.** #63, #73, #62. **Grade.** Definition and lens record. The proved
parts name their Lean owners, and the owed parts are listed in §5. The definition lives in the
[elementary objects](../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode).

## 1. The lens

Brandon, October 8: screw words into resonating code lengths about helices along flux patterns, the
encoding technique of the double helix, independent of any organism. Intersecting partitions along
strings, and knots intertwining and crossing. The Enigma's wire matching and the Bombe, the retina
and the lens. "The helical code object would be what I'm trying to do with Holons, Holarchies,
Epochs, and Aeons … please perfect it and please raise this to such critical importance."

[definition] It is raised: the helical code is the critical object of the rebuild. It changes the
forward plan's order, because the encoding of every Holon is stated through it: the HNN's source
placement, its receivers' frames, its decoders' kernels, and its aeons' conserved charges.

## 2. The object

[definition] A helical code is the composition of five objects. The guide states it with each
proved part's hypotheses:
1. a **strand** on a navigator's helix, with face `m = Σ_k Ĝ(τ(k))⁻¹E(u_k)`, whose repeats
   resonate when their period is whole turns;
2. a **pairing** by a fixed-point-free involution `σ` through helical pair contacts, read backward:
   the reflection of the dihedral group `⟨S, U | U² = 1, USU = S⁻¹⟩` of the screw `S` and the dyad
   half-turn `U`, lifted by `σ`;
3. **frames**: receivers' residue partitions, read together with the whole winding and the epoch
   (an interval between section arrivals, across which a residue recurs). The dihedral group acts
   simply transitively on a duplex's frames;
4. a **decoder** with its declared channel. The pairing is an inner repetition code that locates
   single-strand defects. The receiver's quotient is the outer code: its kernel is fixed by the
   admitted future, and the placement is designed to put likely defects' reached differences in
   it. Coordinated substitutions outside the kernel are the residual;
5. a **topology**: the linking number of closed strands, split as twist plus writhe and changed
   only by crossings.

Its roles: the Holon is the addressed current, the Holarchy the paired and nested duplex, an epoch
an interval between a receiver's section arrivals (across which a residue recurs), and the aeon the
passage whose charge on closed strands is the linking number.

## 3. What is already proved, and under which hypotheses (owners)

Epime read the owners' exact scope on October 8; this section states it.

[formal-checked] `Transport/HelicalPairInteraction`:
- the phase transport `S⁻ᵈPSᵈ` (rotor stepping and the helix step), with its period and carry laws;
- `reflectedReturn A F = A⁻¹FA`, involutive at each fixed frame when `F` is
  (`reflectedReturn_involutive`; a stepping machine also evolves its frame), and without fixed
  points when `F` has none (`reflectedReturn_no_fixed_point`): the Enigma's two properties;
- `boundary_involution_reciprocal` and `menu_loop_closure`: the Bombe's loop closure;
- `lock_iff_zero_power`: on a pair face of positive weight with null-definite material, the
  integer rates `q, p` read zero power exactly when `q v_a = p v_b`. This is a synchronization of
  velocities. Complementarity read as zero slip needs the consumer's declared embedding of letters
  into contact velocities (§5).

[formal-checked] `Aeon/Clock/CarryWord`: the carry word as the epoch reading of two clocks. It never
recurs exactly at an irrational rate (`never_locks_iff_irrational`), so the code's placement can be
kept from resonating with itself.

[formal-checked; conditional] `Foundation/TopologicalReceiver`. The linking number of a crossing
family under a declared direction:
- it is symmetric (`linkingNumber_comm`);
- it is unmoved by the viewing side and by positive rescaling (`linkingTotal_neg_direction`,
  `linkingTotal_smul_direction`);
- it is an integer under `HalvesAgree` (`linking_is_an_integer`).

`HalvesAgree` and invariance under admissible projections (`LinkingIsProjectionInvariant`) are open
`Prop`s. No current crate reads the linking number. The retired Rust owner checked both half-sums at
every reading and tested declared directions
(`13f8c734:crates/holonics-cuda/src/topological_receiver.rs`: `linking_number`, with its half-sums;
`linking_under_directions`). The Lean module's docstrings now name that owner as retired (this
delta). The projected writhe is not
projection invariant (`projectedWrithe_is_not_projection_invariant`), and it is not the ribbon
writhe that `Lk = Tw + Wr` needs. The Reidemeister colouring laws are local Swing transports, and a
full-turn phase forgets the writhe (`Geometry/HolonicUnknotting`). Topological conservation alone
supplies no stored-energy or access theorem.

[formal-checked] The meet of coprime frames already has owners:
- `HNN/Prediction.joint_residue_determines_position`: two addresses below the product with equal
  residues are equal;
- `Geometry/PairResonance.diagonal_step_generates_the_coprime_torus`;
- `HNN/Prediction.joint_class_not_additive`: a joint class is not a sum of per-factor functions.

The meet is unique only modulo the product of the periods. The absolute position needs the whole
winding, and on class-dependent steps the actual source-to-clock relation.

[built] The HNN's source moments are the strand's face (`SourceMoment`). The located transport
reads residues and carries (`compression::keys::transport`, `CarryHelix`), and the HNN's encoding
squares (`hnn/encoding.rs`) are its conduct. The compression kernel is the greatest
navigator-invariant blind subgroup (`Foundation/CausalRelevance`).

## 4. The laws, kernel-checked

[formal-checked; conditional where marked] `Transport/HelicalCode`
(`lean/Holonics/Transport/HelicalCode.lean`, imported from `lean/HolonicsResearch.lean`, outside the
`Framework` closure) states the following, building on the owners above and duplicating none of
them. The sole queue accepted it at `0669655169b8`: the compiler exited zero, and all 81 declarations
carry only `propext`, `Classical.choice` and `Quot.sound`. A narrow consumer of the research root's
new import passed 8 queries. The full research library and the HNN were not rerun. Receipt:
[native-v2](receipts/2026-10-08-helical-code/native-v2/HANDOFF.md). The first attempt, `12fcee787`,
failed at one statement (an inferred `Group (α → α)`); [native-v1](receipts/2026-10-08-helical-code/native-v1/VALIDATION.json)
keeps it unrewritten. The module states:
- the complement-reverse: an anti-homomorphism of words for every `σ`, and an involution, hence an
  anti-automorphism, when `σ` is one;
- the fixed words of a fixed-point-free pairing have even length and correspond to their first
  halves;
- the pairing read through every frame is a fixed-point-free involution;
- one crossing change moves the signed crossing sum by `−2sᵢ` and its half by `−sᵢ`: by 2 and 1 in
  magnitude when `sᵢ ∈ {±1}`.

Its atlas rows are `helical.*` in `geometry.tsv`. The accepted scope is the review's:
- the partner's face holds under a uniform clock with constant openings;
- the crossing laws are arithmetic on declared signed diagrams;
- two repairs are proved distinct, not exhaustive;
- letter-level freedom is not carrier-level freedom.

Its second part states the perfected laws:
- **resonance on a strand:** a repeat's face is a geometric sum of the period's face, with
  `(1 − Ĝ⁻ᵖ) m_{Np} = (1 − Ĝ⁻ᴺᵖ) m_p`. This holds for any monoid acting distributively (a ring on a
  module for the `1 − x` form), and a fixed face `x^p m_p = m_p` gives `m_{Np} = N·m_p`. The
  off-resonance norm bound and the bend reading need a norm, an isometric `Ĝ` and an invertible
  `1 − Ĝ⁻ᵖ`, and are not part of the module;
- **the partner's face:** for an additive carrier involution `J` with `J E = E σ` and
  `JĜJ = Ĝ⁻¹`, under the declared uniform tick with constant openings `α, β`:
  `m_β(σ̄(u)) = JĜⁿ⁻¹⁺ᵅ⁺ᵝ m_α(u)`, an involution. Epime's composition read found that the two maps
  need this equivariant join: the phase transport conjugates at a fixed phase, while placement acts
  on a carrier. The recurrence carrier `q = Ĝⁿ⁻¹ f` reads the same join as `JĜ⁻⁽ⁿ⁻¹⁾` in the
  ending frame. Epime's finite witness, with ticks `(0, 2)`, shows the uniform-tick hypothesis is
  needed. Letter-selected screws need `J S_a J = S_{σ(a)}⁻¹`, and then `J F′_k J = F_n⁻¹ F_{n−k}`;
- **the dihedral pairing:**
  - on the index line, the half-turn `k ↦ c−k` inverts the shift;
  - the half-turns of `⟨S, U⟩` are the `SʲU`;
  - on a duplex's frames (`2p` of them when `p > 0`), the group acts simply transitively;
- **four letters:**
  - the fixed-point-free involutions of a four-element set, with the identity, are a Klein group
    acting regularly;
  - every substitution has one type, and the pairing preserves it;
- **the inner code:** for equal-length substitutions with the partner intact, the slipped indices
  are exactly the substituted ones, and the two proposed repairs are distinct. Exhaustive
  repair-family support is the native consumer's;
- **the duplex passage:** for the declared ribbon sign pattern `(s, es, es, s)`, the inter-strand
  sum moves by `−4es` and `Lk` by `−2es`. This is arithmetic of the declared pattern; the ribbon
  geometry is owed with `Lk = Tw + Wr`.

## 5. Owed

1. `Lk = Tw + Wr` (Călugăreanu–White–Fuller), first for polygonal ribbons, with the ribbon writhe
   as the core's Gauss sum (#62). The closure law `ΔLk = Lk − (Tw₀ + Wr₀) = ΔTw + ΔWr`
   (supercoiling as the closure remainder; `Wr₀ = 0` for a planar relaxed core) consumes it.
2. Projection invariance of `Lk` and `HalvesAgree` (the open `Prop`s of `TopologicalReceiver`), so
   that conservation without crossings is a theorem.
3. The energy split between twist and writhe as a constitutive law, with its buckling threshold (#62).
4. **The consumer.** It is not a separate subsystem: it is the paired chart and lift on the existing
   native path `LocatedTransport::reflected`/`reflect_key` → `PassageChart` → `Encoding::squares`
   → `Encoded`/`SourceMoment` (Epime's read). It adds:
   - the two strand contact ports, `v₋ = v₊ ∘ σ` with `v₊` injective on the admitted contact
     alphabet;
   - the declared reversed incidence `k ↔ n−1−k`. The offset-chain repair support handles its
     certified forest, but a constant offset is not this cyclic gluing;
   - the lift `B` where `σ` descends through the founded fibre. Otherwise the duplex is paired
     before that quotient.

   [agent-inferred; read from the owner] **Where the pairing sits on the native path.**
   - `LocatedTransport::reflected` (`A ↦ −A`, `λ ↦ λ∘(c ↦ −c)`, `reflect_key`) is the dihedral
     **gauge** of the receiving chart. It is the mirror chart that regenerates the same passage, an
     ambiguity of location kept in each fibre. It is not the pairing.
   - The pairing reverses the passage. Its navigator is the dyad-conjugated inverse of the strand's
     step: `F′ = R∘F⁻¹∘R` with `F(ℓ) = ℓ + A(λ(c(ℓ)))` and `R` the gauge's reflection. This is
     `USU = S⁻¹` on the navigator, with complemented labels `σ∘λ`.
   - With class-dependent advances, the partner's step `ℓ′_k → ℓ′_{k+1}` advances by
     `A(u_{n−1−k}) = A(σ(p_k))`, a function of its own letter `p_k`. That letter is read at the
     step's arrival `ℓ′_{k+1}`, not at its departure, so the partner is the arrival-read transport
     with advances `A∘σ`. This is the reversed relation the native path declares.
   - Where `F` is not injective, the reversal has a preimage fibre. The paired strand's actual lifts
     resolve it: each strand is the other's key.
   - The labels enter no chart (the relabelling law), so `σ` acts only on the boundary decoder.
   - Each transport `T_c` is a cyclic shift, a permutation matrix, so `T_c⁻¹ = T_cᵀ` in the
     canonical native coordinates, and there the partner's coordinate chart is the transpose chart.
     A physical adjoint, meaning a power or learning return, is fixed by the reversal and
     reflection, the producing frames and the material metric. This kinematic step does not
     establish one.

   [agent-inferred] **The chart.** On a rotation carrier the dyad is conjugation: `BUB = U⁻¹` for
   `U` multiplication by a unit `ζ`. So complements embed as conjugates off the real axis, and a
   letter on the axis would be its own complement. For four letters, the vertices `±2 ± i` of a
   rectangle in `ℤ[i]` have exactly the Klein symmetry: conjugation is `σ`, and negation and
   `−conj` are the other two types. The square `±1 ± i` would add a quarter-turn merging the types.
   The turn is a Pythagorean unit such as `ζ = (3+4i)/5`. Its angle is irrational, since the only
   roots of unity in `ℚ(i)` are `±1, ±i`, so it never locks and stays exact. In space, the same
   chart is the dyad `diag(1, −1, −1)` about `x`, the helix about `z`, and the letters at
   `(±2, ±1, 0)`.

   **Its two invariants** (Epime's read):
   1. pairing, placement and receiver transport commute, with `Encoding::squares` and the admitted
      successor quotient keeping every separator;
   2. under the declared channel, the actual antecedent lies in the compatible repair family, and
      release requires the receiver's quotient to be constant over that whole family.

   With `s` unmarked slipped contacts the family is factored into `s` binary choices, `2^s` words.
   Storing the factors does not make an arbitrary receiver's class image cheap. The round trip
   `decode(read_R(pair(place(u)))) = class_R(u)` holds for template-assisted single-strand repairs
   and coordinated in-kernel defects. Ambiguous families are held or refused. Coordinated
   out-of-kernel changes are the declared residual, for which the equation guarantees nothing.
   The source moment's coordinates stay bounded while its exact count bits grow, and neither it nor
   the CRT recovers a whole word past its admitted capacity. The decoder, fibre, clock and carry
   residuals are kept. A grain split is not a corruption witness.

   **The first consumer, step 1** (`agent-inferred`). It was designed from a read-only survey of the
   native path at `f12fb506c`, then corrected by Epime's source review (proceed, with five
   corrections and the carried support). Its owned slice:
   - `compression/keys/duplex.rs` and its tests;
   - the `pub mod duplex` export in `compression/keys.rs`;
   - two methods in `compression/keys/transport.rs`;
   - the `helical.*` atlas owners.

   It consumes `LocatedTransport`, `PairContact`/`pair_lock`, `Encoding::{found, encode}` and
   `width_over_readings` → `LawfulOptions::assemble` → `release`, and founds no subsystem. Its
   equations at the consumer:
   - **Lifts, with the carry.** `LocatedTransport::lifts(key, u)` gives the `n + 1` absolute lifts
     `ℓ₀ = key mod D`, `ℓ_{k+1} = ℓ_k + A(u_k)`, unreduced: phase `ℓ mod D`, whole winding
     `ℓ div D`. `CarryHelix::of_residues(r)` gives the unique `ℓ ∈ [0, D)` with `residues(ℓ) = r`
     (Lean `joint_residue_determines_position`); the absolute position keeps the winding.
   - **Fit first.** The clean strand must be a passage of the transport,
     `emit(ℓ_k mod D) = u_k` for every `k < n`. Otherwise the consumer returns the located defect,
     never a duplex. No inverse branch of a non-injective `F` is chosen.
   - **The partner, paired before the quotient.**
     - `Pairing::new(σ)` refuses fixed points and non-involutions, and `σ̄(w)_k = σ(w_{n−1−k})`.
     - The partner's `n + 1` absolute lifts are `ℓ′_k = R(ℓ_n mod D) + (ℓ_n − ℓ_{n−k})`,
       `k = 0..n`, with `R` the gauge's `reflect_key`. Their phases are `R(ℓ_{n−k} mod D)`. The
       absolute endpoint is `ℓ′_n = R(ℓ_n mod D) + ℓ_n − ℓ_0`, and only its phase equals
       `reflect_key(key)`.
     - Partner letter `k` is carried by the step `ℓ′_k → ℓ′_{k+1}` and read at its arrival
       phase. For every `k < n` the consumer checks, on phases,
       `lt.reflected().step(ℓ′_{k+1} mod D) = Some(ℓ′_k mod D)` and
       `lt.reflected().emit(ℓ′_{k+1} mod D).map(σ) = Some(σ̄(u)_k)`.
     - This is `F′ = R∘F⁻¹∘R`, the reversed step keyed by arrival. `T_c⁻¹ = T_cᵀ` holds in the
       native coordinates only; a physical paired return keeps `R`, the reversed order, the
       complemented labels and the producing frames.
   - **Contacts, kinematic only.** A declared injective chart `v₊` with `v₋ = v₊∘σ`. The unit-rate
     slip `v₊(a) − v₋(b)` vanishes exactly when `b = σ(a)`, read through `PairContact` and
     `pair_lock`. A power claim needs a declared positive-weight `ContactMaterial` that is definite
     on the attained slips; none is made in this step.
   - **The receiver's class** is `class_R(w) = ((E e_{ℓ_k mod D})_{k=0..n}, ℓ_n div D)`: every
     receiving state, the terminal included, and the terminal carry probe. It is a read-only
     receipt tuple, never retained as a per-occurrence chain; the continuing retained object
     stays the future-sufficient quotient. `E` is founded from the development keys' chart and is
     the receiver's own quotient, never an authored table.
   - **The channel and inner code.** Substitutions at declared contacts on either strand, at
     equal length: single-strand, or coordinated and complementary. The slipped contacts are
     `{k : p′_{n−1−k} ≠ σ(u′_k)}`.
   - **The repair family, exact and carried.** For the independent factors `F_k` (the clean letter,
     or the two candidates at a slipped contact), the support keeps full carried positions:
     `X_0 = {key}`, `X_{k+1} = {x + A(a) : x ∈ X_k, a ∈ F_k}`, with back-pointers to actual
     members.
     - `E` reads `x mod D`, and the carry probe reads the division with remainder of `x`. The
       quotient is taken only after every admitted terminal and carry receiver is included.
     - Since `0 ≤ A(a) < D` with at most two candidates a contact, `|X_k| ≤ k(D − 1) + 1`. A
       rolling exact support needs at most two such sets, and the transition work is bounded by
       `Σ_k |X_k||F_k|`. This is polynomial for this declared independent channel, not a general
       claim that families are cheap.
     - When fitting the transport couples the factors, only supported extendable prefixes count
       (forward and backward support), and that added cost is stated.
   - **Release.** Readings at different positions are never pooled: one trajectory's readings
     legitimately vary from position to position. Each receipt coordinate is compared across the
     supported alternatives, and under the declared supremum norm
     `diameter(class_R(F)) = max(diameter(E(X_0)), …, diameter(E(X_n)), diameter(winding(X_n)))`.
     The equality holds because every supported state extends to an actual member, in the
     fit-constrained variant after backward pruning. A coordinate attaining the maximum supplies
     two witness members.
     - Release happens exactly when the family is nonempty and every coordinate's set is a
       singleton. It is never certified from a sample.
     - Otherwise the consumer holds, naming the slipped contacts and two actual witness members
       with their differing classes.
     - A declared template side collapses each factor.
     - The owners' routes are distinct. `width_over_readings` (`receiver/face.rs:771`) computes
       the exact diameter of a provided finite family and enforces its family ceiling, so it may
       read each coordinate's complete support. `ReceiverWidth::declared` (`:555`) checks only the
       structural coherence of an owner-computed aggregate, so it may carry the computed maximum.
       The consumer owes the complete-support/diameter equation and the witness extensions.
     - An empty fit-constrained family returns the typed no-compatible-source defect. The two
       witness members are owed only for a nonempty, nonconstant family.
   - **Coverage.** The truth round trip is conditional on the channel's coverage. On the covered
     repairable channel, at most one strand changed at each contact, the truth lies in the supported
     family and release is exactly constancy of that family. A coordinated complementary change
     leaves no slip, so its local family is the observed letter alone, and release returns the
     observed class, which may differ from the truth. The binary local factors are therefore never
     the complete preimage family of a channel that also admits unwitnessed coordinated
     substitutions.
   - **Absorption, against known truth only.** A coordinated substitution is absorbed exactly when
     the damaged word's class equals the truth's class. Its carried shift `Δ = A(u′_i) − A(u_i)` is
     a signed representative that moves every later absolute lift. The count stays on the
     acceptance side, never inside the decoder.

   **Accepted** (`implemented-exact`; `measured`, October 8 PDT). The sole queue accepted the corrected
   source `02658c6c2` with a fresh compile. Gate 1 passed: the workspace check, the guard lints and
   all 57 library guard doctests. All 21 duplex tests passed in one process, which took 2,228,496,495 ns
   of wall time against a fixed projection of 30,917,577,474 ns, at a peak child RSS of 48,780 KiB.
   The receipt is [native-v2](receipts/2026-10-09-helical-duplex/native-v2/HANDOFF.md). The first seal,
   `c6fcc82a1`, is preserved unexecuted. Its two gaps were fixed before any run: a partner contact
   reversed before it was bounded, and a receiver bound only to its helix.

   Readings on unseen keys, per chart (text digits, pitch classes, levels):
   - free family: released/held 3/21, 0/24 and 3/21;
   - a template frame: all 24 released in each chart, every class equal to the truth's;
   - fit-constrained: the transport alone resolves 24 of 24 in each chart. This is forced, because
     the key is known;
   - coordinated complementary changes, outside the coverage and counted against truth:
     absorbed/residual 16/152, 12/540 and 11/349;
   - an exterior model predicted every one of these counts before the run.

   Scope: a known-truth calibration of the chart/contact/quotient composition only. It establishes
   no key discovery, no generalization to unseen constitution families, no wider channel coverage,
   no material power, no HNN partner return and no ribbon geometry.

   **The three boundary charts**, each with `σ` as its own half-turn. Each is a known-truth
   `SteppedTerrain` over the chart's alphabet. Placement uses the terrain's truth transport, so
   location's cost of `D^|A|` is not spent; location is a separate, built capability.
   - Text bytes in base four, two bits a digit, with `σ(x) = 3 − x` (bit complement) and the
     rectangle chart `v₊ ∈ {(±2, ±1, 0)}`, where `σ` is the dyad `diag(1, −1, −1)`.
   - Twelve pitch classes, with `σ(x) = x + 6 mod 12` (the tritone).
   - Eight signed amplitude levels, with `σ(x) = 7 − x` (phase inversion).

   Byte passages themselves stay refused on the located route (`Unencoded`); the text chart is
   their base-four boundary chart. The acceptance reads exact counts on unseen keys and words:
   located slips, released and held families, absorbed and residual coordinated substitutions
   against truth, and CRT recovery.

   **Step 2: the partner face on the HNN carrier** (`agent-inferred` design, corrected by Epime's
   source review of `f034a7225` and `6269cc5af`; built at `083640894`, native PASS,
   [receipt](receipts/2026-10-09-actual-h-r/PUBLICATION.md)). Three objects are named apart:
   - `F_g`, the ring's port permutation;
   - `B_g`, its realified carrier lift, `(B_g v)[2F_g(i)+r] = v[2i+r]`;
   - `σ`, the class pairing.

   The HNN carries no dyad. `F_g` is checked only for `F_g² = 1` (`hnn/field.rs:730`) and read only
   as the Bombe stage `ρ⁻ᵐFρᵐ`. The generic reflector keeps promising only that. The dihedral
   relation `F_g(F_g(i)+1) = i−1`, which makes `B_g P_g B_g = P_g⁻¹`, is checked at the admission
   and certificate of a **paired carrier**, never by tightening `Ring::declare`.

   **The pairing needs an even family.** `FieldDeclaration::campaign_1` has five classes, so no
   fixed-point-free involution exists on its one alphabet. The common alphabet is not changed to
   fit. A paired carrier declares either an even admitted paired class family, or a typed pairing
   between two partner charts or roles, the free swap on their disjoint union. Any other pairing is
   refused.

   The terms still missing, each with its equation:
   1. the paired carrier's admission, which certifies `F_g² = 1`, the dihedral relation and the
      declared `σ`;
   2. the source port's equivariance `B_g E_g = E_g Σ_σ`, and its descent through the quotient.
      The founded sign matrix `E_0` has neither;
   3. the tick: a uniform tick for the recurrence law. For letter-selected serial screws the law is
      `J S_a J = S_{σ(a)}⁻¹`. That reduces to `A∘σ = A` only on a common fixed-generator rotor
      chart with its conjugacy declared;
   4. no pair ports, or a pair-port reversal law;
   5. a located moment chart, `T_t = P^t ⊗ 1` for `t ∈ 0..=d_g`, closed under the dyad,
      `B T_t B = T_{d_g−t}`. Today `PassageChart::moment` admits only `t ≤ 2`;
   6. the Lean bridge `moment l = U^{n−1}·strandFace U⁻¹ (I∘E) l`, and the partner law at
      `SourceMoment::encode` and `open_storage`. That consumer joins the phase counts, the
      normalization and rounding, the pair ports, the learned contemporary encoder and the modulus
      refusal: a uniform exact recurrence is not automatically their law.

   **What step 2 built** (`implemented-exact`: `hnn::paired` at `083640894`, 16 tests, native
   PASS with the all-targets check, the guard clippy and the 57 guard doctests). Each missing term
   above now has an owner or a typed refusal:
   - Terms 1 and 2. `PairedCarrier::admit` certifies `F² = 1` and the dihedral relation, which holds
     for exactly the `d` reflections `F(i) = F(0) − i`. It also certifies the typed pairing and
     `B E = E Σ_σ` column by column. The carrier keeps no port: every partner read re-certifies the
     port the constitution holds now, and names the first failing column.
   - Term 3. The unit tick is certified from the field: every class of the family fits the source
     ring's lock, and no earlier ring of the carry chain ticks. Letter-selected clocks are refused.
   - Term 4. Declared pair offsets are refused at the moment; the moment's pair-port reversal is owed
     (the deposit's reversal law is step 3, below).
   - Term 5. Located moments are refused; the located moment chart is owed.
   - Term 6. The partner law is read at `SourceMoment::encode` and `open_storage`, through
     `SourceMoment::dyad`. The dyad reflects the counts in phase and complements them in class,
     with `c₀ = s + s′ + n + 1`. It gives `m̃(σ̄u) = B P^(c₀) m̃(u)` and
     `s(0)(σ̄u) = B P^(−(n−1)) s(0)(u)`, with exact residual zero on every admitted read (162 words
     over three settings). The Lean bridge is owed (#62).
   - **Information: redundancy.** At the retained quotient of this undamped carrier the partner face
     is a function of the forward face and `n`. Over 1,365 words, no group of equal length and
     forward face had two partner faces. The partner is a check, not new information.
   - **Step 3, the equivariant deposition** (`implemented-exact`, `measured`, October 9; Lean
     `HNN/PairedDeposit` kernel-checked; the
     [receipt](receipts/2026-10-09-paired-deposit/PUBLICATION.md); the owner's header, `hnn::paired`,
     "The paired deposit").
     - Loop 1 ran the derived defect: one forward `pair_deposit` moves `E − E₀` at its consequence's
       column alone, and the partner read then refuses at that column against its partner.
     - Loop 2 built the pair-port reversal law. With `B E₀ = E₀ Σ`, `B E = E Σ` and `B P B = P⁻¹`, the
       lift of a located pair's slip is the slip of its dyad image read against the clock,
       `B Δ_y = P^(−δ) E₀ e_(σy) − (E − E₀) e_(σf(y))`. `PairedCarrier::deposit` reads that image by its
       own law at `−δ`, checks the identity at every pair, puts both orientations into one certified
       step and re-admits the successor.
     - On a duplex whose strands move disjoint columns, one deposit closed both strands' slips (8 to 0
       at `η = 2`) with the port equivariant and the partner face exact, while the forward deposit
       alone left the subspace.
     - Where a law's dyad images share columns with its forward reads, three deposits descended toward
       10, the law's incompatibility with the pairing (remainders `715827883/2³⁰`, `57264483/2³¹`,
       `5260321/2³⁰` above it).
     - Mirrored columns are not this law: the image is read, never copied.
     - Loop 3 made the pairing a constraint of the source law, so it holds on every route.
       - On the general route, the Word's partner return is the dyad image only in a field that
         commutes with the dyad.
       - So a source law that declares the pairing projects each deposit onto the subspace,
         `Π_V(G) e_a = ½(G e_a + B G e_(σa))`, with its Gram's arrivals and its chart symmetrized
         exactly.
       - Every slip reader reads one founding prior, the field's declared port completed by the
         law's symmetry.
     - Measured on the pair routes and on general features at the normal law:
       - the forward deposit alone keeps the port on the subspace;
       - the release's closed contacts through the founding prior are `[1, 3]`;
       - a save restores the law, its prior and its contacts.

       It is not an end-to-end participating world's comparison. The quadratic's invariance is owed
       in Lean (#62).

   **The general partner law and its scope** (`proved-derived` for the identity, owed in Lean).
   - **The identity.** For a uniform tick, an involution `B` and `B E = E σ`, the recurrence face
     `moment_U(w) = Σ_k U^{n−1−k} E(w_k)` gives
     `moment_U(σ̄u) = Σ_j U^j B E(u_j) = B Σ_j (BUB)^j E(u_j)`.
   - **The redundant case.** When `BUB = U⁻¹` (a stated conjugacy, not implied by orthogonality
     alone), the partner's face is `B U^{−(n−1)} moment_U(u)`: redundant, a pure check.
   - **The adjoint case.** For `U = ρP` with `BPB = P⁻¹`, `BUB = ρP⁻¹`. This is `Uᵀ` only in the
     declared Euclidean carrier. In a material metric `G` the physical adjoint is `G⁻¹UᵀG`, and
     the actual word, material and clock return carry further terms. Within the Euclidean scope,
     the partner's face is the strand read through `Uᵀ` in forward order: the backward fading,
     the shape of the covector's return.
   - **Information is not established by damping.** The differing weights `ρ^{2k−(n−1)}` rule
     out a common linear map only under sufficient independent variation at each position. An
     injective forward face can still admit a nonlinear decoder. The acceptance is therefore
     fixed at the actual retained, grain-level quotient:
     - either two admitted sources with the same forward retained face and distinct partner faces,
       with exact residuals;
     - or a report of redundancy.

   **Deferred to later steps, named.**
   - Step 3, the equivariant deposition, is built (above): the pair route, and the paired source law
     that holds the port on its subspace on every route.
   - Step 4: the linking reading of a closed duplex and its crossing changes. No current crate
     reads the linking number, and the retired owner is at `13f8c734`. Its consumer in the machine
     is named before it is built.

   **A runnable example** (`implemented-exact`; a known-truth smoke run, not a regression or product
   gate). `crates/holonics/examples/helical_duplex.rs` (`9e8041d0a`), run with
   `cargo run -p holonics --example helical_duplex`, prints one fixed-key duplex on the carry
   regression fixture: the navigator and its cell labels, the partner and lifts, the receiver's
   class, an intact release, a one-sided hold with two actual witnesses, and a coordinated change
   released with a residual that only the harness labels
   ([receipt](receipts/2026-10-09-helical-duplex-demo/PUBLICATION.md)).

   **The support and diameter laws, kernel-checked** (`formal-checked`). `Transport/HelicalRepair`
   was accepted at `5efbb1cc0`: 56 declarations using only standard axioms, and a narrow
   research-root import check of 8 queries ([receipt](receipts/2026-10-09-helical-repair/native-v1/HANDOFF.md)).
   - The carried support is exactly the members' prefix lifts, for nonempty factors and `k ≤ n`.
   - Its size is at most `min(∏_{j<k}|F_j|, k(D−1)+1)` when `A < D`.
   - The class diameter equals the maximum over the coordinates of each coordinate's diameter on its
     support, with the terminal carry as one coordinate. It is bottom exactly when every
     coordinate's reading is constant on its support.

   Accepted scope: independent nonempty factors only. These remain separate: the fit-constrained
   (pruned) exactness, channel truth coverage, the realization of the actual quotient and receiver,
   attaining witnesses, work/memory/overflow realization, and the general partner law.

5. **The designed-placement law** (Epime's typed form over `Foundation/CausalRelevance`'s additive
   carrier). `q(P(T_{i,v}u)) = q(P(u))` iff `δ_{i,v}(u) = P(T_{i,v}u) − P(u) ∈ K`, for every admitted
   background `u`. The type `v` is a substitution operator, and the kernel holds its reached
   difference. The law is owed to #62 with the consumer, and its types and hypotheses are kept
   when the consumer is built.

## 6. Acceptance (fixed before any build; the channel revised the same day)

Epime's clarification (October 8) fixed what the receiver must read. A quotient proves class
invariance for in-kernel changes. A corruption that carries one valid codeword to another of a
different class cannot be refused by any decoder that round-trips the undamaged word. So the
admitted channel and its separation are declared operands.

- **Lean.** `Transport/HelicalCode` passes the queue's check with no axiom, `sorry` or
  `native_decide`, and its laws are in the atlas.
- **The consumer.** On known-truth terrains in at least three boundary charts (text bytes, notes on
  a pitch helix, sampled waves), generated by exact routines. Every reading is an exact count, on
  unseen words:
  - single-strand substitutions at contacts with intact partners are located exactly (the slipped
    contacts are the substituted ones);
  - on the covered repairable channel (at most one strand changed at each contact), the truth lies
    in the supported family. With a template frame the repair is unique and the round trip holds.
    Without one, the class is released exactly when it is constant over the complete supported
    family, and otherwise the decoder holds, naming the contacts, two witness members and their
    classes;
  - coordinated in-kernel substitutions keep the class;
  - coordinated out-of-kernel substitutions are counted against the known truth as the residual,
    never claimed as refused (online they have no witness);
  - two frames of coprime periods recover each position from its residue pair;
  - a crossing change moves the linking reading by exactly its sign, and a duplex passage by two.
- **No catered machinery.** No authored decoder table. The kernel is the receiver's own quotient,
  and the pairing is the declared involution of the code's own kind.

**Recorded failures checked.**
- An authored routine standing in for learning: the decoder is a quotient of the machine's own
  receivers.
- Text run as the exception: three boundary charts in the acceptance.
- Seen material graded as unseen: unseen words only.
- Bits read as progress: exact counts, not code length.
- An unbounded guarantee claimed past its channel: the residual is declared and counted.
