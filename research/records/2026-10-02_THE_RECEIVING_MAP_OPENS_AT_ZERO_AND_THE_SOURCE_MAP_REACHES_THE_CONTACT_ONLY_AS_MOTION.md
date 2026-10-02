# The receiving map opens at zero, and the source map reaches the contact only as motion

October 2. Refs #73, #63, #62. No run beyond one test. Lean `HNN/ReceivingReach`; test
`a_zero_receiving_map_returns_no_covector_to_the_contact` (`hnn::reference::continuation`).

The refit-ingredients record §7 found every logit zero when a word reads the U6 states, because the
receiving map `R` is zero and the U6 chain deposits only into the source map `E`. This record
answers three questions about that.
- Is `R = 0` a declaration or a law?
- Through which owner does a change in `E` reach the receiving face and the next contact: the
  storage's returned state, the capacitor's current of #239, or the contact cut's passage?
- What does a move that changes `E` deposit at the contact, per #239's response
  `m′(ζ′ − ζ) = ΔC(w − w⁺)`?

## 1. `R₀ = 0` is an opening value; what holds it at zero along U6 is the comparison's routing

[definition; agent-inferred] `Constitution::initial` opens `R` at zero. Its stated reason is in the
docstring: the face then opens exactly at the landmark tree's, and the wave earns every bit it
moves. The located failure was the old prior's reading `R₀z`, which alone carried a share in
`[51/56, 3713/4077]` of the held-out logits' energy. `R`'s normal law moves it at the first deposit
any comparison sends it (test `r_opens_at_zero_and_learns_from_the_first_deposit`). So `R₀ = 0` is
an initial condition with a derivation, not a quantity the law holds.

Along U6, `R` stays at zero for a different reason. The chain's comparison is the declared bank's,
and its move steps the source port alone (`stepped_source`). Astra's native contact return,
`compare_contact_storage`, keeps only the contact storage step. Neither sends `R` a step. "`R = 0`
at m6 and w16" is therefore a consequence of which comparison deposits, not a law. Releasing it
means letting the receiver's own comparison deposit into `R`. That is the next loop that §7
already decides.

One declared quantity of `R`'s law remains: the unit prior Gram `H₀ = I`, with `B₀ = 0`. It sets
how far the first deposit moves (§2's chart `X̂ ≈ (I + Σ w f fᵀ)⁻¹`). This record does not derive
it; the obligation is carried in #62.

## 2. The first deposit reads features by their overlap

The receiving map's normal law moves `R` by its unit step `D = Σ_t w_t g_t (X̂ f_t)ᵀ` at the
certified `η` (module header, "Deposition"). From `R₀ = 0`:

```text
R₁ f = Σ_t η w_t ⟨X̂ f_t, f⟩ g_t                                (first_deposit_read)
```

The formed map reads a later feature `f = P_R^(τ_R) v_R` as the comparison covectors `g_t`, each
weighted by its feature's overlap with `f` in the chart's metric. At `R₀ = 0` the face is the empty
tree's, and the tree reads no wave. So the first covectors `g_t = q_t − p_t` do not depend on `E`.

Two receivers formed on the same requests from two source maps (m6 and w16) therefore differ, at
the first deposit, only through their features and the chart those features carry. §7's gate asks
whether w16's features separate the targets in that Gram better than m6's do. From the second
deposit on, `p_t` carries `R₁`, and the covectors depend on `E` too.

## 3. A source-map change reaches the next contact only as motion, through the contact cut's passage

`E` is not in the power form. `PowerForm::read` holds the ring admittances, the contacts'
conductances, `C`, `K` and the loaded resonators. `E` enters the passage only at an open
(`SourceMoment::open_storage`, `s_g(0) = P_g^(τ_g) m̃_g`). The contact operator
`m = 1 + (G/2h)(2C + hD + ½h²K)` does not contain it.

So a word opened on a successor that differs only in `E` solves every transit with the same `m`,
and the change of its solve is `m⁻¹` of the change of the right side `h(α_g − α_h) + 2Cw − hKu`,
that is, of the arrivals and the state. A comparison covector `λ` on the solve reads that change
through the adjoint solve `rᵀm = λ`:

```text
⟨λ, ζ′ − ζ⟩ = ⟨r, b′ − b⟩                                      (passage_reach_of_unmoved_material)
```

Of the three owners named:
- **The contact cut's passage carries it.** The change is motion: the injected state propagates to
  the contact and moves `b`.
- **The capacitor's current of #239 carries nothing.** It is `ΔC(w − w⁺)`, and an `E` move has
  `ΔC = 0`.
- **The storage's returned state does not carry it either.** A continuing word continues from its
  end change; the source is injected only at an open, so a continuing word is not re-injected.
  Astra's continuation states this boundary: source-map changes "need their own transported return
  and are not silently treated as contact-coordinate changes" (`hnn::word::continuation`).

An `E` change therefore reaches only the words opened after it is committed.

## 4. A move that changes `E` deposits nothing at the contact; what `C` learns from is the rate's jump

With `ΔC = 0`, #239's response `m′(ζ′ − ζ) = ΔC(w − w⁺)` is zero. The commit's deposition work
`½⟨x, ΔΘ x⟩` over the power form is zero at every reached point (§7). An `E` move changes the
passage's motion and deposits no material.

`C` changes only from a covector that reaches it. `compose_contact` pulls the storage covector
`C̄ = Σ 2 r̄ (w − ω)ᵀ`, with `ω` the midpoint rate. Since `w⁺ = 2ω − w`, `2(w − ω) = w − w⁺`
(`slip_is_half_jump`), so `C̄ = Σ r̄ (w − w⁺)ᵀ`. This is the dual of #239's response:

```text
m′(ζ′ − ζ) = ΔC j ,  rᵀm′ = λ   ⇒   ⟨λ, ζ′ − ζ⟩ = Σ_ik ΔC_ik r_i j_k ,  j = w − w⁺   (storage_covector_dual)
```

The covector `C` learns from is the rate's jump, the one direction in which a storage change can
move the next passage. The identity is exact when `r` is the adjoint solve at the deposited
operator `m′`. The executed pull reads `r̄` at the producing `m`, and the two differ by `ΔC`'s own
term.

## 5. A covector reaches the contact only through `Rᵀ g`

Every covector the receiver's comparison sends into the passage is `Rᵀ g`. At `R = 0` the read is
zero whatever the feature (`zero_map_reads_nothing`). Every adjoint solve `r̄` is then zero, and so
are the storage pull and the opening covector.

The test `a_zero_receiving_map_returns_no_covector_to_the_contact` checks this on Astra's
continuation control with `R` set to zero. The face's covector `g` and the feature `f` are present,
so `R`'s step has its samples. Every transit's `r̄`, every opening covector and the storage
gradient are zero.

Two consequences:
- **At the U6 states, the native contact return deposits nothing on `C`.**
  `compare_contact_storage` at m6 or w16 returns a zero storage step.
- **On an opening constitution, the first comparison can move `R` alone.** `C` and `E` receive a
  covector only from the second comparison on. In §7's next loop (a passage of the 8 training
  requests), the first request's comparison forms `R₁`, and `C` learns from the second request on.

## 6. The interface `E`'s native learning needs from Astra's channel

**The forward reach needs nothing new.** `open_storage` on the committed successor already
carries it.

**The return already carries `E`'s covector.** `WordReturn::opening` is the covector on every
ring's opening storage. `SourceMoment::encoder_covector` turns it into `E`'s gradient without a
tape, as `hnn::reference`'s source block does.

The native continuation lacks two things:
1. **A source-port deposit composed from the native return.** It is the `Locus::SourcePort(g)`
   normal-law step with the same samples `hnn::reference` builds from `back.opening[g]` and the
   moment's covector, admitted beside the contact storage step.
2. **Its continuation rule.** `W_dep = 0`, since `E` is not in the power form. The continuing word's
   state is unchanged, nothing is transported into it, and `E′` takes effect at the next
   `open_storage`.

This needs `R ≠ 0` first: at `R = 0`, `back.opening` is zero (§5).
