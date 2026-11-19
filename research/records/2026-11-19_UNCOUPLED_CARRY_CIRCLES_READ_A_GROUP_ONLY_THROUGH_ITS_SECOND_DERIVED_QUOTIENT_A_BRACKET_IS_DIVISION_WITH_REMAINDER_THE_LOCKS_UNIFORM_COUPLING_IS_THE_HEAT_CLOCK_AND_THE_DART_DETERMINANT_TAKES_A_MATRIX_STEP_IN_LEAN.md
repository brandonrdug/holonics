# Uncoupled carry circles read a group only through its second derived quotient; a bracket is division with remainder; the lock's uniform coupling is the heat clock; and the dart determinant takes a matrix step, in Lean

November 19, 2026, 22:13 to 23:00 UTC. A second bounded formal pass with its critique, after
[the first of the day](2026-11-19_ONE_CELL_CARRIES_THE_PASS_BAND_OF_A_TREE_A_CURVE_AND_A_JUNCTION_A_PUMPED_CARRY_LOCKS_PAST_ITS_DETUNING_THE_HEAT_CLOCK_KEEPS_TWO_POSITIVITIES_IN_OPPOSITE_DIRECTIONS_AND_THE_WHOLE_LINE_EAR_IS_NEVER_INVERTIBLE_IN_LEAN.md).
An outside reader (a Gemini model, its letter held in the private mailbox and restated here in the repository's words)
replied to that record with a family of remainder conventions, a lemma and a control for the carry, and four
blueprints for Lean. This record weighs each item against the tree, proves the part that holds, names the owner of
each part the tree already held, says what was not built and why, and reads the results against the engine. Nothing
ran on a learner or on the card, and no line was touched. Each paragraph carries its grade: `tree` (read in this
repository), `from training` (a result of the literature, named) or `agent-inferred` (this record's join). Every
Lean statement cited names its module and theorem, and each module checks with no `sorry`, no added axiom and no
`native_decide` (§9). Refs #410.

Five atlas rows enter (§10): `parametron.carry-bank-group-ceiling`, `trace.ihara-bass-matrix`,
`thermal.mean-field-heat-clock`, `key.loop-packing-floor` and `radix.section-gauge`. Four rows whose only owner was
a record take Lean owners: `radix.release-quotient-or-section`, `radix.two-place-reconstruction`,
`key.unique-games-frontier` and `contact.odd-alternation`.

## 1. The reply's items and what became of each

| The reply's item | The tree before this pass | This pass |
|---|---|---|
| One family `div_rem` over the conventions floor, ceiling, balanced and two's complement, a change of convention moving a multiple of the modulus between remainder and quotient | `Foundation/EuclideanResidueTransport` (the chart through the floor remainder, and truncated coordinates beside it); the floor carry as a cocycle and no coboundary (`Geometry/PhaseCarry`, `Compression/FacesOnCycles`; atlas `winding.carry-cocycle`, `face.carry-bockstein`); a wrapped sum read at the balanced representative (`Holonics/HNN/LatticeWord.carrier_ring_read`, `HNN/SolvedChartBits.valMinAbs_intCast_eq`) | built as `Foundation/SectionGauge`: the conventions are one free orbit, with what no convention can do (§3) |
| Division with remainder for a matrix or a lattice modulus | `Holonics/Foundation/LatticeTransport` (atlas `linalg.lattice-cokernel`: the cokernel class with no section chosen) | a restatement; not built |
| Positivity as the absence of a half-turn flip, with Weil's criterion in that reading | `Zeta/FiniteWeilCriterion` (atlas `rh.finite-weil-criterion`: the form on a finite family is nonnegative exactly when the reversal fixes every member), `Holon/InertiaCount` (atlas `inertia.negative-squares-count-modes`: the negative squares count the exchanged pairs) | a restatement of both; not built |
| "Every finite subgroup of `Aff(1, ℂ)^C` is abelian", so a commuting carry cannot hold `D₃` and a pumped one can; a `D₃` control in place of the brackets' | atlas `key.commutator-is-and` (`Compression/FaithfulModes`: a word over commuting moves reads only its counts); `HNN/PumpedCarry` | holds, and is proved in a stronger form with the pumped bank's own ceiling beside it (`HNN/CarryGroupTracking`, §2); the brackets' control is read in §3.3 |
| `Zeta/RiemannSiegelSeam`: the approximate functional equation, the remainder `Ψ(p)`, the jump cancelling at the seam | `Zeta/CarryTick` (the seam function is real; Hardy's `Z`), atlas `rh.critical-line-fixed-locus`, `rh.weight-symmetry`; no approximate functional equation in the tree | not built (§7) |
| `Geometry/FrustrationUnicity`: a floor on broken contacts from disjoint frustrated cycles over any group; the gauge fibre; a commuting carry's commutators collapsing | `HNN/GroupKeys` (atlas `key.group-holonomy-keys`: the keys of a menu over any group are one orbit, free and transitive: `keys_eq_orbit`, `gauge_fix_unique`); atlas `key.unique-games-frontier` and `contact.odd-alternation` with no Lean owner | the floor is built (`HNN/LoopPacking`, §6); the gauge fibre is a restatement; the collapse is §2's first theorem |
| `Landmarks/IharaBassMatrix`: the determinant identity with a matrix on every dart, its gauge invariance, the `D₃` cover's factorization, a host ruler for the engine | `Landmarks/IharaBass`, `Landmarks/IharaBassConnection` (one unit of a commutative ring a dart; its header named the matrix case as not there) | built: the identity, the gauge, the loop and the step of size two (§4); the cover's factorization is not (§7); the ruler is a reading offered (§8.3) |
| `Coupling/LockHeatFlow`: the heat flow on a finite lock polynomial, Hermite–Poulain, a deposit's cooling moving zeros monotonically | the polynomial flow and its forward preservation in seven modules (`Zeta/PolyaStep`, `ForwardPreservation`, `HeatSemigroup`, `HeatFlowOfPolynomials`, `DeBruijnNewmanPolynomial`, `PairDescent`, `DeBruijnSeal`); Lee–Yang for the Ising lock (`Coupling/LeeYangIsing`); no theorem joining the two | the polynomial statements are restatements; the join is built (`Coupling/MeanFieldHeatClock`, §5), and it is the construction the first record's §7.2 item 4 named |

## 2. Which groups a bank of carry circles holds

`tree` and Lean (`HNN/CarryGroupTracking`). The engine's carry is a bank of circles, each a complex charge stepped
once a symbol. The built step is a turn, a scale and a drive, `q ↦ αq + v`. The proposed step adds a conjugate term,
`q ↦ αq + βq̄ + v` (`PumpedCarry.step`), passive when `|α| + |β| ≤ 1`. The reply's lemma speaks of subgroups of a
group of maps. The statement proved here assumes less: no representation, only that the bank's state depends on the
value of the word read so far.

**The definition.** A bank holds `Γ` through `f : Γ → ℂ^C` when right multiplication by each `g` is one step of the
bank's kind on every circle, the same step whatever the state was (`AffineTracks`, `PumpedTracks`). The steps are not
assumed to compose as the group does, and with a drive two affine steps do not commute as maps.

**The affine ceiling** (`affineTracks_comm`, `affineTracks_commutator`, `affineTracks_injective_comm`). In a
torsion group `f(γgh) = f(γhg)` for every `γ`, `g`, `h`. The proof is one line of algebra and one of order: on a
circle the two words apply the same turn `α_g α_h` and differ by a shift `t` that does not depend on `γ`; so
`k = (gh)⁻¹hg` shifts every state by `t`, and `k` has finite order `n`, so `n·t = 0` (`shift_eq_zero`). Hence every
element of the commutator subgroup `Γ′` is unread, and a bank that tells the elements apart forces the group to
commute. No condition is put on the turns, and the count of circles and their width do not enter. On `S₃` the
three-cycle is a commutator of two swaps, so an affine bank of any size holds only the sign
(`affineTracks_perm_three`).

**The passive pumped ceiling** (`exists_centre`, `im_conj_step_mul_step`, `commutator_mem_preserving`,
`pumpedTracks_derived`). Over a finite group a passive pumped bank leaves every element of `Γ″ = [Γ′, Γ′]` unread.
The proof, a circle at a time:
1. the mean of the states is a centre every step fixes, which removes the drive;
2. each step is passive and has an inverse that is passive, so it keeps every distance between states;
3. a pumped step scales the area form `Im(x̄y)` by its gauge `|α|² − |β|²`
   (`Im(conj(Sx)·Sy) = (|α|² − |β|²)·Im(x̄y)`), and the gauge is multiplicative into the reals, so a commutator
   has gauge one and keeps `Im(x̄y)` as well as the distances: it keeps every product `ψ̄(γ)ψ(γ′)`;
4. so each element of `Γ′` acts on a circle's states as one unit scalar, and scalars commute.

**The separation** (`dihedralState_injective_and_steps`, `dihedralState_pumpedTracks`,
`not_affineTracks_injective_dihedral`). One pumped circle holds `D₃`: the states `rⁱ ↦ ωⁱ·i` and `srⁱ ↦ −ωⁱ·i`
are six distinct points, `rʲ` acts by the turn `(ωʲ, 0)` and `srʲ` by the reflection `(0, ωʲ)`, each of unit size
and with no drive. No affine bank of any size tells the six apart. So the reply's control separates the two kinds
of carry for a reason that is now a theorem, and the reflection buys exactly one commutator.

**Perfect groups** (`pumpedTracks_perfect`, `alternatingGroup_five_perfect`, `pumpedTracks_alternating_five`). If
`Γ′ = Γ` a passive pumped bank holds nothing. `A₅` is perfect, so no bank of uncoupled circles of either kind, at
any size, holds anything of `A₅`.

| Group | An affine bank reads | A passive pumped bank reads | Grade |
|---|---|---|---|
| cyclic `C_n` | all of it | all of it | one circle, a turn by `1/n` |
| `D₃ ≅ S₃` | the sign, `C₂` | all of it, on one circle | Lean |
| `S₄` | the sign | at most `S₄/V₄ ≅ S₃` | ceiling in Lean |
| `A₄` | `C₃` | ceiling `A₄`; by the classification below, `C₃` | ceiling in Lean; the rest `agent-inferred` |
| `Q₈` | `V₄` | ceiling `Q₈`; by the classification, `V₄` | the same |
| `A₅` | nothing | nothing | Lean |

`agent-inferred`, with one classical fact `from training`. The ceiling `Γ″` is not the whole answer. Steps 1 and 2
make each circle a map of `Γ` into the isometries of the plane about one centre, whose finite subgroups are cyclic
or dihedral. So a bank of uncoupled passive circles reads `Γ` through the quotient by the elements every such map
kills. For `A₄` that is `C₃`, and for the quaternion group `Q₈` it is `V₄`, although both are metabelian: `Q₈`'s
faithful action needs two circles coupled by one step (the quaternions are `ℂ²`). What a pumped circle holds is a
turn and a mirror and nothing else. That is the group the objects give the helical code,
`⟨S, U | U² = 1, USU = S⁻¹⟩`, the screw and the dyad (atlas `helical.dihedral-frames`): a pumped circle is the
smallest carry that holds the code's own pairing, and the pairing is all it holds.

`from training`. A unitary step on two coupled circles holds the binary icosahedral group, which is perfect.
The word problem of a finite group that is not solvable is complete for the circuits of logarithmic depth
(Barrington 1989), and programs over solvable groups stay inside a class of bounded depth with counters
(Barrington and Thérien 1988). `agent-inferred`: so the line between what a bank of uncoupled circles composes and
what composition of unbounded nesting needs is the line between solvable and not, and the first carry on the far
side of it is two circles coupled by a step of size two. That is the same step §4 gives a determinant.

## 3. What a strict cap does, what a bracket is, and the remainder's conventions

### 3.1 Under a strict cap nothing is held for words of every length

Lean (`HNN/CarryGroupTracking`: `contracting_erases`, `returning_pair_erases`).
- If one element of finite order acts by a pumped step with `|α| + |β| < 1` on every circle, with any drive, all
  states are one state.
- If an opening step followed by a closing step returns each of two states to itself, and the product of the two
  steps' sizes `(|α′| + |β′|)(|α| + |β|)` is below one, the two states are one state.

`tree`: the host control `tools/pumped_carry_control.py` caps both arms, `ρ = 0.98·sigmoid` on the commuting arm
and `ρ + σ ≤ 0.98` on the pumped one. `agent-inferred`: so neither arm of that control holds a group or a bracket as
a set of states. What a capped carry holds is a direction that fades by the cap's factor a step: at `0.98` the
state loses `log₂(1/0.98) = 0.0291` bits of the register a step, one bit every `34.3` steps, and after 48 steps it
stands at `0.98^48 = 0.38` of itself. A reading of a capped arm at a fixed length is a reading of that fade against
the face's gain, and it is a learner's reading (rule 10 of a line's lap: a null is held to a length).

`agent-inferred`. The proof of the pumped ceiling says what holding costs: over a finite group a passive step that
is held acts as an isometry about a centre, of size one. The cap's reason is a bounded charge under drive
(`PumpedCarry`, the simplex weights). An isometry about a fixed centre also keeps the charge bounded, by the
centre's distance and the states' radius, and it needs no cap. So the two requirements meet at unit-size steps
whose drives share a centre, and part at any cap below one. No store is at rest: the other lawful way to hold is a
gain that restores what the leak takes, which is the lock (`parametron.ising-lock`), and its statement is not in
this record.

### 3.2 A remainder convention is a gauge

Lean (`Foundation/SectionGauge`). A section `s : ℤ/m → ℤ` picks one integer in every residue class.
- **Every section gives a chart** `ℤ ≃ ℤ/m × ℤ`, `x ↦ (x mod m, (x − s(x mod m))/m)` (`sectionChart`); through
  the floor section it is the tree's `intEuclideanChart` (`sectionChart_floor`).
- **The conventions are one orbit, free and transitive** (`existsUnique_shift`, `winding_shift`): two sections
  differ by `m·δ` for exactly one `δ : ℤ/m → ℤ`, and the winding through the shifted section is the old winding
  less `δ` at the residue. This is the reply's `(r + mδ, q − δ)`, with the uniqueness it did not state.
- **The interval family** (`intervalSection_reads`, `eq_intervalSection`): the representatives in `[a, a + m)` are
  a section that returns every integer of the interval from its residue, and a section with values in the
  interval is that one. Floor is the interval at `0`, two's complement at `j + 1` places the interval at `−2^j`
  (`twosSection_eq_interval`), negative exactly when the top place is set (`twosSection_neg_iff`).
- **Two's complement and the balanced section part at one residue**, the half `2^j`
  (`twosSection_eq_balanced_sub`).
- **A sign is read whole exactly at an odd modulus** (`exists_odd_section_iff`): a section that commutes with
  negation exists if and only if `m` is odd. At an even modulus the half is its own negative, and no convention
  gives it a sign.
- **Truncation is outside the family** (`truncated_not_section`): the remainder of division truncated toward zero
  is not a function of the residue (`−3` and `5` modulo `8` read `−3` and `5`). It reads the source's sign and is
  a different chart.
- **Every section carries** (`carry_shift`, `carry_floor`, `exists_carry_ne_zero`): a change of convention changes
  the carry by the coboundary of `δ`, the floor section's carry is the tree's `FacesOnCycles.carry`, and for
  `m ≥ 2` no section's carry vanishes everywhere, from `FacesOnCycles.carry_not_coboundary`. No remainder
  convention is additive.
- **A negative integer under the floor convention** (`winding_floor_fixed_iff`, `winding_balanced_fixed_iff`):
  the winding has two fixed points, `0` and `−1`, and popping `−1` returns the top residue `m − 1` and `−1` again.
  Under the balanced convention, for `m ≥ 3`, `0` is the only one.

`agent-inferred`. The reply's phrase "negativity is modularity" holds in this form: under the floor convention a
sign is which fixed point an integer's windings end at, a run of zeros or a run of the top digit, which is the
`m`-adic reading the tree holds as the carry tower (`Foundation/CarryTower`); under the balanced convention a sign
is carried by the digits and no residue stands for it; and at an even modulus one residue, the half, has no sign
under any convention. `−1 = e^(iπ)` is that half at `m = 2`. The phrase's third term, orientation, is the objects'
own: orientation exists only in the pairing, and a section is a receiver's frame.

**The precision law's two rows take Lean owners.** `read_once_after_wrapped_sum`: the sum of residues is the
residue of the integer sum, so one reading through an interval after the sum returns the total whenever the total
lies in the interval, whatever the partial sums did (atlas `radix.release-quotient-or-section`, the quotient's
side, and `radix.two-place-reconstruction`). `release_add`: the release of an integer through a section,
`x − s(x mod m)`, fails additivity by `m` times the carry of the two residues, and a release after every add
depends on the bracketing (`release_not_schedule_free`: at `m = 2`, `(1 + 1) + 0` reads `2` and `1 + (1 + 0)` reads
`0`). The carry is the one object behind both: a quotient forgets it and commutes, a section pays it and orders
the sum.

### 3.3 A bracket is division with remainder

Lean (`SectionGauge.pop_push`, `push_pop`). The chart of any section is a stack of residues: its inverse pushes a
residue under an integer, `(r, q) ↦ s(r) + m·q`, the chart pops it, and each undoes the other. A stack's depth is
the integer's count of places.

`agent-inferred`. This reads the brackets' control. A bracket pair is a returning pair: the closer must return the
state the opener met. §3.1 says a returning pair needs two sizes whose product reaches one. Under a cap of `0.98`
on both, each arm of the control fails for that reason, the commuting one and the pumped one alike, so the
control does not tell the two kinds apart; the reply's objection to it stands, with a different cause from the one
it gave. A stack does not ask for moves that fail to commute by a reflection. It asks for an inverse pair, a
contraction answered by an expansion (the push `q ↦ (q + r)/m` and the pop `q ↦ mq − r` of an iterated function
system, `from training`: Siegelmann and Sontag 1995), or for the same pair in integers, where nothing expands and
the word grows by `log₂ m` bits a level. The second is the Ratio object's own operation and the precision law's
"a carrier widens at a declared crossing". So the two controls test two capacities:

| Capacity | What it needs | Who has it |
|---|---|---|
| a finite group's order of moves (`D₃`) | a reflection, at unit size about a centre | one pumped circle; no affine bank |
| a stack (brackets) | an inverse pair of sizes `ρ` and `1/ρ`, or division with remainder on a word | any kind of step with gain on the closer, or an integer word; no capped bank |
| a group that is not solvable (`A₅`) | circles coupled by a step of size two or more | no bank of uncoupled circles |

## 4. The dart determinant with a matrix on every dart

Lean (`Landmarks/IharaBassMatrix`). A finite complex of contacts with an invertible `n × n` matrix on every dart,
the reversed dart carrying the inverse: `G(d)·G(d̄) = 1`, over any commutative ring.
- **The identity** (`ihara_bass_matrix`):
  `(1 − u²)^(|V|·n) · det(1 − uB_G) = det(1 − uA_G + u²(D − 1) ⊗ 1) · (1 − u²)^(|E|·n)`.
- **It rests on two relations** (`bass_det_abstract`): for any matrices with `J·J = 1` and `S·J = T`,
  `(1 − u²)^|X| · det(1 − u(TᵀS − J)) = det(1 − uSTᵀ + u²(TTᵀ − 1)) · det(1 + uJ)`. With the start incidence and
  the reversal each multiplied by the block diagonal of the transports, both relations follow from
  `G(d)·G(d̄) = 1` alone (`reversalM_mul_reversalM`, `startMatrixM_mul_reversalM`), and the scalar files'
  argument needs nothing else.
- **A change of frame at the cells** `G′(d) = H(src d)·G(d)·H(tgt d)⁻¹` conjugates the dart operator, so
  `det(1 − uB_G′) = det(1 − uB_G)` (`det_hashimotoM_gauge`).
- **One cell with one loop** reads `det(1 − uG₊)·det(1 − uG₋)` (`det_hashimotoM_loop`).
- **A step of size two** (`det_one_sub_smul_two`, `det_hashimotoM_loop_two_det_one`):
  `det(1 − uH) = 1 − tr H·u + det H·u²`, and a loop whose holonomy has determinant one, with its inverse on the
  reversed dart, reads `(1 − tr H·u + u²)²`: one factor for each direction of the walk, each the cell's
  (`Geometry/CellPassBand.scaled_factor`) and the shape of a prime's factor on a curve (`Landmarks/HasseBand`).

`agent-inferred`. Two readings. The degree of a closed chain's factor is the size of its step: a commuting
transport gives linear factors, the characters' theory, and a step of size two gives the quadratic of a cell.
Number theory's own ladder has the same rungs (`from training`: Dirichlet's and Hecke's functions are of degree
one, a curve's of degree two, an Artin function's of the degree of its representation), and §2 puts the carry on
it: commuting circles are degree one, a pumped circle is degree two with the pairing its only non-commuting move,
and coupled circles are degree two with all of them. And the identity's hypothesis is the first record's §7.2
item 1 once more: it needs the reversed dart to carry the inverse. A transport whose contacts carry one way has
the dart operator and its determinant, the gauge invariance and the loop's factors (none of which use the
hypothesis), and no cell-side form.

## 5. The lock's uniform coupling is the heat clock

Lean (`Coupling/MeanFieldHeatClock`). For a finite set of locks let `M(S) = Σ_i s_i` be the total of a
configuration and `flow(t, h) = Σ_S exp(t·M² + h·M)`.
- **It is the Ising lock with one exchange between every pair** (`isingZ_uniform`):
  `Z(J ≡ c, β, h) = flow(βc/2, βh)`.
- **Free locks at time zero** (`flow_zero`): `flow(0, h) = (e^h + e^(−h))^|V|`.
- **The heat equation** (`heat_equation`): `∂_t flow = ∂_h² flow`.
- **The tree's own heat operator runs it** (`heatE_free`): with the free locks read on the seam chart,
  `free(z) = flow(0, iz)`, the derivative series of `Zeta/HeatFlowEntire` gives
  `heatE_t free (z) = flow(t, iz)` for every real `t` and complex `z`.
- **Lee–Yang is forward preservation on this family** (`flow_ne_zero_of_re_ne_zero`): for `t ≥ 0` the flow has no
  zero with `Re h ≠ 0`.
- **Two locks** (`flow_two`, `flow_two_zero_on_axis`, `flow_two_off_axis`, `seamTimes_two`,
  `zeroAngle_strictAntiOn`, `flow_two_zeroAngle`): `flow = 2 + e^(4t)(e^(2h) + e^(−2h))`; on the axis it vanishes
  exactly where `cos θ = −e^(−4t)`; for `t < 0` a zero leaves the axis; the set of times at which every zero lies
  on the axis is `[0, ∞)`; and the zero's angle `arccos(−e^(−4t))` falls strictly from `π` toward `π/2` as `t`
  grows.

`agent-inferred`, with the literature `from training` (de Bruijn 1950; Newman 1976, whose family this is).
The zeta lane's clock multiplies a law by `e^(tu²)`, which it calls sharpening. Applied to the law of the total of
free locks that multiplier is a ferromagnetic exchange `t = βc/2` between every pair, a mean field. So three names
in three lanes are one parameter on this family: sharpening (the zeta lane), cooling or a stronger exchange (the
thermal lane), and, by the tree's reading of the pump as an inverse temperature
(`parametron.pump-inverse-temperature`), the pump. Backward time is an antiferromagnet. Free locks sit at the
threshold `0` with their zeros pinched together, and any forward time parts them along the axis. The reply's
monotone motion under cooling is proved for two locks and stated for no more.

What transfers to the zeta lane and what does not. `from training`: the hypothesis is the statement that the
palette of `ξ` has threshold at most zero, and the threshold is at least zero (Rodgers and Tao 2018), so the
hypothesis says `ξ` sits at its threshold, as free locks do. The finite family shows what a threshold at zero looks
like: a law with no coupling to spare, where any backward time moves a zero off the axis. It does not transfer
the cause: free locks reach the threshold by a collision of zeros, and nothing here bears on the palette of `ξ`,
whose law is not a binomial one.

## 6. A floor under what any section of a menu can close

Lean (`HNN/LoopPacking`), over a menu with transports in any group.
- A configuration is carried along a walk whose own contacts hold (`walk_transports_of_holds`).
- On a closed walk whose holonomy is not the identity every configuration breaks a contact
  (`broken_on_frustrated_loop`).
- For a family of such loops with no contact in two of them, every configuration breaks at least as many contacts
  as the family has loops (`packing_bound`).
- Right multiplication by one element moves no contact between held and broken (`holds_gauge`, `broken_gauge`).
- An odd ring of sign-reversing contacts breaks a contact, and an even one has a key (`odd_ring_breaks`,
  `even_ring_has_key`).

`tree`: `HNN/GroupKeys` proves that a menu with a key closes every loop. This is the count on the other side, and
it gives `key.unique-games-frontier` and `contact.odd-alternation` their first Lean owners. It is a lower bound:
the packing number is not the optimum in general, and the spectral reading is `key.connection-cheeger`'s.

## 7. What was not built, and the construction each names

**The Riemann–Siegel seam.** `agent-inferred`. A module at this pin would hold the trigonometric identities of
Siegel's leading term, the remainder `Ψ(p) = cos(2π(p² − p − 1/16))/cos(2πp)` and its values across the seam where
the main sum gains a term, with no theorem tying either to `ζ`: Mathlib has no saddle-point expansion of the
function and the tree has no approximate functional equation. Such a module would be a definition presented as a
result. The construction is the approximate functional equation itself: the main sum to `√(t/2π)`, the same sum
reflected by the factor `χ`, and a remainder with a bound. Its finite shadow is in the tree: `Zeta/CarryTick`
holds the seam function as real, and the reflection's fixed locus is `rh.critical-line-fixed-locus`. What the
blueprint reads rightly is the object: the main sum's length is a carry (it steps by one each time `√(t/2π)`
passes an integer), and the remainder is what the section owes at each step, which is §3.2's carry in the
analytic chart.

**The `D₃` cover's factorization.** The zeta of a cover with group `D₃` as the base's zeta times the sign's
function times the square of the standard representation's. It needs the induced representation's block form on
the cover's darts. The tree's abelian case (`Landmarks/IharaAbelianCover`) diagonalizes by characters; here the
blocks are of size two, and §4's identity is the statement each block satisfies. The construction is that block
decomposition.

**The gauge fibre, matrix division, the finite Weil form and the polynomial heat flow** are in the tree under the
owners §1 names.

## 8. What the formal objects are for

### 8.1 Where this pass joins the engine with a theorem

1. **What a carry can hold is read from the kind of its step, before any training.** §2's table is a prediction
   for the lead's control at long words, and §3.1 says why a capped arm reads below it. The consumer is the host
   control and whatever carry the line takes.
2. **A sum's register and a release's order** (§3.2). The precision law's sentence, that a sum's register needs
   the declared range of its total and never of its partials, is now `read_once_after_wrapped_sum`, at any modulus
   and any interval. The line's carry gate in 32 bits is an instance when its total's range is declared.
3. **A stack is a word** (§3.3). Division with remainder is the pop. A bracket memory is a register whose depth is
   its places, which the engine's own arithmetic already performs.
4. **The lock's coupling and the clock are one parameter** (§5), which is the construction the first record's
   §7.2 item 4 asked for. It joins the zeta lane to the lock polynomial with a theorem. It does not yet reach a
   deposit's rate.

### 8.2 Where it does not, said plainly

1. **Three of the five modules have no consumer in the engine.** The matrix determinant, the packing floor and the
   heat clock are consumed by the atlas and by each other. The first record's §7.2 item 2 said a statement enters
   this lane with the engine term it constrains or the ruler that reads it; `HNN/CarryGroupTracking` and
   `Foundation/SectionGauge` meet that, and the other three are offered with rulers (§8.3) and nothing more.
2. **The reply's unification by one phrase is three statements, and they are different.** A sign as a choice of
   section (proved, §3.2), a positivity as the absence of exchanged pairs (in the tree before the reply), and an
   orientation as the pairing's (the objects' definition). They share the half-turn. No theorem here makes one
   follow from another, and the Weil form's positivity for `ζ` is the hypothesis itself in another chart.
3. **The ceiling theorems are about sets of states, and a learner has a length.** At a fixed length a contracting
   carry codes its recent symbols, and a trained arm can read well above the ceiling's long-word value. The
   theorems say where the reading goes as the length grows, and nothing of how fast.
4. **The identity of §4 needs a round trip the engine's contacts do not make.** The same gap as the first record's,
   now with the non-commuting case stated: the dart side, the gauge and the loop survive one-way contacts, and the
   cell side does not.
5. **The classification step of §2 is not in Lean.** The table's entries for `A₄` and `Q₈` rest on the finite
   subgroups of the plane's isometries about a point, taken from training.

### 8.3 Readings this pass offers the line

Each is a host reading with the planted law its null is held to. None is ordered; the lead's lane decides.

| Reading | The law it reads | The guess, fixed here | Its planted law |
|---|---|---|---|
| The commuting arm on `D₃` as the word grows | `affineTracks_perm_three` | toward `1/3` where the task names the running product (the sign known, three elements left); the outside reader's host readings, `0.58` at 16 symbols and `0.40` at 48, not rerun here, fall that way | an arm with every turn set to one |
| Both uncoupled arms on `A₅`, and on `Q₈` | `pumpedTracks_alternating_five`; §2's classification | `A₅`: both at chance, `1/60`; `Q₈`: both at `1/2` (the quotient `V₄` known, two elements left); an arm with one unitary step coupling two circles passes both | the coupled arm with its steps set to the group's own |
| An arm's reading against length at one register width | `contracting_erases` | a fade at the cap's factor a step, one bit of the register every `34.3` steps at `0.98` | steps of unit size about a centre for the group's symbols |
| A bracket arm with gain on the closer, or an integer word popped by division | `returning_pair_erases`, `pop_push` | passes to a depth equal to the register's places; both capped arms fail alike | the true stack as a word |
| The transport's own zeta with blocks of size two: cycle counts against `tr Bⁿ` | `ihara_bass_matrix`, `det_hashimotoM_gauge` | none fixed | a planted loop with a known holonomy |
| A pair of locks' zero angle against their exchange | `flow_two_zero_on_axis`, `zeroAngle_strictAntiOn` | none fixed | two locks at a set exchange |

## 9. Lean

Five modules enter `HolonicsResearch`, each imported by the library's root.

| Module | Declarations | Section |
|---|---|---|
| `HNN/CarryGroupTracking` | 38 | §2, §3.1 |
| `Foundation/SectionGauge` | 42 | §3.2, §3.3 |
| `Landmarks/IharaBassMatrix` | 39 | §4 |
| `Coupling/MeanFieldHeatClock` | 24 | §5 |
| `HNN/LoopPacking` | 12 | §6 |

- Three workers on disjoint owner paths wrote four of the modules from briefs that fixed the statements; the
  primary wrote `Foundation/SectionGauge`, read each returned file against its brief, renamed one subgroup whose
  name said the opposite of its content, and added `returning_pair_erases`, `flow_two_zeroAngle` and
  `det_hashimotoM_loop_two_det_one`. Two statements came back stronger than their briefs: the two locks' zero
  condition and the angle's bounds hold at every real time, and the loop's factorization needs no inverse.
- The recovery changed the pass before it was built. A module on the Hermite form of a finite family was planned
  and dropped when `Zeta/FiniteWeilCriterion` and `Holon/InertiaCount` were read, and the section module was cut
  to what `Geometry/PhaseCarry` and `Compression/FacesOnCycles` do not hold; it consumes the second.
- Gate 4, in a cloud container at the package's pinned toolchain and Mathlib: `bash tools/lean_check.sh` on the
  five modules by name, run after the last edit of each, read `Build completed successfully (8759 jobs)`, exit 0,
  with no warning from a new module. The research library's whole root closure was not rebuilt there, as in the
  first record; each new module's namespace is its own in the tree.
- Gate 1's text checks: `link_check.py atlas` (4,150 rows, 18,332 owners read, none broken), `link_check.py links`
  (1,636 links, none broken), `test_records_index.py` (8 controls passed) and `lean_census.py` (1,939 files, none
  unbuilt, none unrooted).
- No `sorry`, no added axiom and no `native_decide`. `#print axioms` on the closing lines of
  `Landmarks/IharaBassMatrix`, `Coupling/MeanFieldHeatClock` and `HNN/LoopPacking`, and on the main theorems of
  the other two read from a scratch file (thirty statements), reads `propext`, `Classical.choice` and `Quot.sound`
  alone.

## 10. Atlas

Five rows enter:

| Row | Shard | Grade | Lean owner |
|---|---|---|---|
| `parametron.carry-bank-group-ceiling` | objects | `formal-checked` | `HNN/CarryGroupTracking` |
| `radix.section-gauge` | arithmetic | `formal-checked` | `Foundation/SectionGauge` |
| `trace.ihara-bass-matrix` | geometry | `formal-checked` | `Landmarks/IharaBassMatrix` |
| `thermal.mean-field-heat-clock` | physics | `formal-checked` | `Coupling/MeanFieldHeatClock` |
| `key.loop-packing-floor` | objects | `formal-checked` | `HNN/LoopPacking` |

Four rows take their first Lean owners, each keeping its grade and its record, with its limits saying what is now
stated: `radix.release-quotient-or-section` and `radix.two-place-reconstruction` (`Foundation/SectionGauge`), and
`key.unique-games-frontier` and `contact.odd-alternation` (`HNN/LoopPacking`). Three rows point at the new ones in
their limits: `trace.ihara-bass-connection`, `thermal.ising-lee-yang` and `key.group-holonomy-keys`.
