# Discretizing quantum and fluid fields on a lattice / simplicial complex

Software design study. Part 1: what each source contains. Part 2: a consolidated, library-free
JavaScript specification. Part 3: disagreement and silence.

---

## 1. Per source

### 1.1 Brower, Fleming, Gasbarro, Howarth, Neuberger, Raviv, Tan, Weinberg — *Lattice φ⁴ Field Theory on Riemann Manifolds* (arXiv:1803.08512v1)

**Identity.** Quantum Finite Element (QFE) programme: Regge geometry + linear FEM + DEC + explicitly
computed quantum counterterms, tested against the exact 2-d Ising CFT on S². Continuum action being
discretized (Eq. 2.1):

    S = ∫_M d^d x √g [ ½ g^{μν} ∂_μφ ∂_νφ + ½(m² + ξ̃₀ Ric)φ² + λφ⁴ + hφ ] ,  ξ̃₀ = (d−2)/(4(d−1))

Discrete action on a simplicial complex (Eq. 2.2):

    S = ½ Σ_{⟨ij⟩} K_ij (φ_i − φ_j)²/l²_ij + Σ_i √g_i (½ m²_i φ_i² + λ_i φ⁴_i) + h Σ_i √g_i φ_i

The metric is *only* edge lengths, `g_{μν}(x) → g_σ = {l_ij}`, piecewise-flat interpolated (Regge).
In 2-d the linear-FEM kinetic term per triangle (Eq. 2.6) is

    I_σ = [(l²_31 + l²_23 − l²_12)/(8 A_123)] (φ_1 − φ_2)² + (23) + (31)

i.e. the cotangent form. Boundary operator (Eq. 2.9) `∂σ_n(i_0…i_n) = Σ_k (−1)^k σ_{n−1}(i_0…î_k…i_n)`,
with `∂∂ = 0`; DEC Stokes (Eq. 2.12) `⟨dω_k, σ_{k+1}⟩ = ⟨ω_k, ∂σ_{k+1}⟩`, hence `dd = 0` and
(Eq. 2.13) `⟨dφ, σ_1(ij)⟩ = φ_i − φ_j`. Hodge star (Eq. 2.15):

    ⟨ω*_k, σ*_k⟩ |σ_k| = ⟨ω_k, σ_k⟩ |σ*_k|

DEC Laplace–Beltrami (Eq. 2.16), the load-bearing equation:

    *d*dφ(i) = (|σ_0(i)|/|σ*_0(i)|) Σ_{j∈⟨i,j⟩} (|σ*_1(ij)|/|σ_1(ij)|)(φ_i − φ_j)
             = (1/√g_i) Σ_j (V_ij/l_ij)(φ_i − φ_j)/l_ij

with `√g_i = |σ*_0(i)|` the circumcentric dual volume and `V_ij = |σ_1(ij) ∧ σ*_1(ij)| = l_ij S_ij/d`
the hybrid cell (Eq. 2.10: `|σ_n ∧ σ*_n| = [n!(d−n)!/d!]|σ_n||σ*_n|`). Complete QFE-precursor action
(Eq. 2.19): `S = ½Σ_{⟨ij⟩}(V_ij/l²_ij)(φ_i−φ_j)² + λ₀Σ_i √g_i(φ_i² − μ²₀/2λ₀)² + hΣ_i√g_i φ_i`.

**Why naive FEM fails.** Sec. 2.4: FEM converges for classical PDEs, but the path integral is
sensitive to fluctuations *down to the lattice spacing*. On S² the FEM action gives no critical
surface and `⟨φ²_i⟩` is not uniform on the sphere. One-loop self-energy (Eq. 3.5):

    Σ_ij = −12λ_i [M^{-1}]_ii δ_ij + 96 λ_i λ_j [M^{-1}]³_ij + O(λ³₀)

The tadpole is *position-dependent* because the effective local cutoff `a_x` varies. Numerically
(Eq. 3.9) `[M^{-1}]_xx ≈ (√3/8π)log(1/m²a²_x) = (√3/8π)log N + (√3/8π)log(a²/a²_x) + O(1/N)`: the
divergent piece is position-*independent* (coefficient exactly the continuum `√3/(8π)`), the finite
piece is not. QFE counterterm (Eqs. 3.12–3.13):

    δG_xx = [M^{-1}]_xx − (1/N) Σ_x √g_x [M^{-1}]_xx
    S_FEM → S_QFE = S_FEM + 6 Σ_x √g_x λ₀ δG_xx φ²_x

Normalization (Eq. 3.7): `Σ_x√g_x = N`, `Σ_{⟨xy⟩}K_xy = (2/3)E`.

**Square-lattice reference.** Eq. 2.26: exact hypercubic spectrum
`E_n = Σ_μ 4sin²(k_μ/2) + m²₀ ≃ m²₀ + Σ_μ[k²_μ − k⁴_μ/12 + …]`, `k_μ = 2πn_μ/L`, `n_μ ∈ [−L/2, L/2−1]`,
eigenvectors `φ_n(x) = N^{-1/2}e^{−ik·x}`. The square lattice *is* a FEM realization: split each square
into two right triangles and Eq. (2.8) gives zero weight on the diagonals. Free propagator by mode sum
(Eq. 2.24): `G_xy(m²₀) = [1/M]_xy = Σ_n φ_n(x)φ*_n(y)/(E⁽⁰⁾_n + m²₀)`.

**Target observable.** Weyl-transformed CFT two-point function on S² (Eqs. 4.8 / 5.1):
`⟨φ(r̂_1)φ(r̂_2)⟩ = 1/(2 − 2cos θ_12)^Δ`, Δ = 1/8 for Ising; Binder cumulant (Eq. 4.3)
`U_4 = (3/2)(1 − Q_4/3)`, `Q_{2n} = ⟨M^{2n}⟩/⟨M²⟩ⁿ`, `M = ∫d²x√g φ`. QFE gives
`U_{4,cr} = 0.85020(58)(90)` vs continuum `0.8510207(63)`.

### 1.2 Gérard, Hiroshima, Panati, Suzuki — *Infrared divergence of a scalar QF model on a pseudo Riemannian manifold* (arXiv:0904.2805v4)

**Identity.** Continuum operator theory. A Nelson model (scalar field linearly coupled to a
non-relativistic particle) on a *static* pseudo-Riemannian spacetime, unitarily reduced to a flat-space
model with **variable mass** `v_m(x) = m(x)² ≥ 0`. No discretization anywhere. Hamiltonian (Eq. 1.7)
and equation of motion (Eqs. 1.8–1.9):

    H = ½p² + V(q) + ½∫[π(x)² + (∇φ(x))² + v_m(x)φ(x)²]dx + α φ(ρ_q)
    (□ + v_m(x))φ(x,t) = −α ρ_{q_t}(x)

Dispersion `ω̂ = √(−Δ + v_m)` (Eq. 1.6) replaces `ω̂_N = √(−Δ + m²₀)` (Eq. 1.2). Generalized
eigenfunctions (Eq. 2.8) `(−Δ + v_m)Ψ(k,x) = |k|²Ψ(k,x)` diagonalize it: `Fω̂F^{-1} = ω`, `ω(k) = |k|`
(Eqs. 2.11–2.12), so the *dispersion is exactly massless* however `v_m` is shaped; `v_m` only
deforms the eigenfunctions. Smeared coupling (Eq. 2.14): `ρ_x(·) = (2π)^{-3/2}∫Ψ(k,·)Ψ(k,x)χ(k)dk`.

**Metric conditions.** Sec. 2.5. Static metric `ds² = g_00(x)dt⊗dt − Σγ_ij(x)dx^i⊗dx^j`, `g_00 > 0`,
`g_{0j} = 0`, `g` independent of `t`. KG equation `□_gφ + (m² + ηR)φ = 0` (Eq. 2.34) with
`□_g = Σ_{μν}|det g|^{-1/2}∂_μ g^{μν}|det g|^{1/2}∂_ν` (Eq. 2.35) reduces to `∂²_tφ = Kφ`; the unitary
`Uf = ρ^{1/2}f`, `ρ = |det g|^{1/2}/g_00` (Eq. 2.37) gives (Lemma 2.9)

    U K U^{-1} = Σ_ij ∂_i g_00 γ^{ij} ∂_j − v ,   v = g_00(m² + ηR) + V₂

For the conformally flat example (Eq. 2.30) `ds² = e^{−θ(x)}dt⊗dt − e^{−θ(x)}Σdx^j⊗dx^j` one gets
`∂²_tφ = Δφ − vφ` with `v(x) = O(⟨x⟩^{−β−2})` (Lemma 2.8).

**Meaning of infrared divergence.** IR *regular* (Eq. 1.10) `∫_{R³}χ(k)²/|k|³dk < ∞`; IR *singular*
(Eq. 1.11) the same integral `= ∞`. Under Assumption 2.4 (`χ̌ ≥ 0`, `χ/√ω, χ/ω ∈ L²`), Remark 2.5
forces `χ(0) > 0` hence `∫χ²/ω³ = ∞` in 3 space dimensions. **Theorem 4.7**: for a short-range variable
mass (Assumption 4.5: `v_m = κw`, `|w(x)| ≤ C⟨x⟩^{−β}` with **β > 3**, `−Δ+w` with no non-positive
eigenvalues, κ small) **H has no ground state**. **Theorem 5.5**: with `R = ∫χ²/ω³dk` and
`(Ψ(0,·)φ_g, φ_g) ≠ 0`, `lim_{R→∞}(φ_g, Nφ_g) = ∞`, via (Eq. 5.15)
`(φ_g,Nφ_g) = (α²/2)∫dk[χ(k)²/ω(k)³](Ψ(k,·)φ_g, ω²(H+ω)^{-2}Ψ(k,·)φ_g)`. So "fluctuation" here means
*soft-quantum content of the ground state*, infinite exactly when the mass function decays fast enough
that the field is effectively massless in the IR.

### 1.3 Dang & Herscovich — *Renormalization of Quantum Field Theory on Riemannian manifolds*

**Identity.** Continuum, Euclidean, closed Riemannian manifolds. Existence proof of *covariant*
Epstein–Glaser renormalization via **extension of distributions**. No lattice, no scheme.

Objects: Green function (Def. 1.1) `G = Σ_{λ∈σ(−Δ_g)\{0}}λ^{-1}e_λ(x)⊗e_λ(y)` in `D'(M×M)`, smooth off
the diagonal, a parametrix of `Δ_g + m²` (Lemma 6.1). Feynman amplitude (Eq. 1.2)
`Π_{1≤i<j≤n}G(x_i,x_j)^{n_ij}` is smooth on `M^I \ D_I` only; renormalization = extending it across the
diagonals. Motivating example (Eqs. 1.3–1.5): `x^{-1}_+ = lim_{ε→0}∫_ε^∞ dx x^{-1} + log(ε)δ`, the
Hadamard finite part, where `log(ε)δ` is the **local counterterm**.

**What covariant renormalization requires** (Def. 1.3), the three axioms an implementation must
respect: (i) extension, `⟨R_{M^I}[g](t), φ⟩ = ⟨t, φ⟩` for `φ ∈ D(M^I \ D_I)`; (ii) **locality /
factorization**, for `dist(U,V) > 0`, `R_{M^{I⊔J}}[g]|_{U^I×V^J} = R_{M^I}[g]|_{U^I} ⊗ R_{M^J}[g]|_{V^J}`;
(iii) **covariance**, `R_{N^I}[Φ*g]((Φ^I)*t) = (Φ^I)*(R_{M^I}[g](t))` for any diffeomorphism Φ.

Engine: moderate growth (Def. 3.1) `|t(φ)| ≤ C(1 + d(supp φ, X)^{-s})sup_i p_{ℓ_i,m_i}(φ)`;
Theorem 4.1 — *t extendible ⟺ t has moderate growth ⟺ there are cutoffs `β_λ` and counterterms `c_λ`
supported on X with `lim_{λ→0}(tβ_λ − c_λ)` existing in `D'(M)`*. Tempered functions (Def. 5.1)
`sup_{|α|≤m}|∂^αf| ≤ C(1 + d(x,Ω^c)^{-s})`; Theorem 5.3 — `ft` is renormalizable for `f ∈ M(Ω)`,
`t ∈ D'(M)`. Main Theorem 1.5: such an `{R_{M^I}[g]}` exists and is **equivariant under the isometry
group of (M,g)**, by Weyl's unitarian trick averaging `P_Ω` over the group (Remark 4.2). Design
consequence: renormalization is a *choice of extension*, ambiguous by diagonal-supported counterterms,
and covariance is imposed by averaging that choice.

### 1.4 Carfora & Romano — *Quantum fluctuations and geometry: from graph counting to Ricci flow* (arXiv:0902.2061v3)

**Identity.** Continuum 2-d non-linear sigma model. "Graph counting" means **Feynman-graph counting**,
not simplicial graphs. I searched the full text: no triangulation, no simplicial complex, no Regge
calculus, no vertex curvature appears.

Classical action (Eq. 8): `S(φ, a^{-1}g) ≐ a^{-1}∫_Σ γ^{μν}∂_μφ^i∂_νφ^j g_ij dμ_γ`. Background field
`ψ ≐ cm{φ_1,…,φ_N}` (Eq. 9), the Riemannian centre of mass. **Fluctuation field** (Eq. 11):
`φ_k(x) = exp_{ψ(x)}(ψ_*ξ_k(x))`, sections of `ψ*TM` with `Σ_jξ_j = 0`; measure (Eq. 12)
`∫δ[Σξ_j]Π_k e^{−S_ψ[ξ_k;a^{-1}g]}D^ψ_g[ξ_k]`. **Graph expansion** of the characteristic functional
(Eq. 16):

    W_ψ(J) = −S_ψ[0; a^{-1}g] + Σ_{Υ∈G} (a)^{l(Υ)}/|Aut(Υ)| F_Υ(S_ψ, J) + ln(∫ e^{−½S^ψ_{μν}η^μη^ν} D^ψ_g[η])

G = isomorphism classes of connected graphs without external lines with `l(Υ)` loops; `n`-leg vertices
get `S^ψ_{α₁…α_n}[0]`, internal edges get the propagator from `S^ψ_{μν}[0]`. Gaussian propagator with
IR regulator `Λ' ≐ (2r)^{-1}` (Eq. 23): `⟨η^a(x)η^b(y)⟩ = 2a(δ^{ab}/π)∫d²k e^{ik·(x−y)}/(k² + Λ'²)`.
Three 2-leg vertices `(i) A^μ∂_μ`, `(ii) A^μA_μ`, `(iii) Rm ∂^μψ∂_μψ`; (i)+(ii) cancel, leaving
(Eq. 27) `F(Υ_{(iii)}) = ln(Λ²/Λ'²) ∫_Σ R_ij(ψ)∂^μψ^i∂_μψ^j dμ_γ`.

**One-loop metric renormalization** (Eq. 29): `g_ij(ψ) = g_ij(Λ/Λ') − 2a ln(Λ/Λ') R_ij(ψ) + O(a²)`,
whence with `τ ≐ ln(Λ/Λ')`, `t ≐ −aτ` (Eqs. 31–32) `∂_t g(t) = −2 Ric(g(t)) + O(a²)`; two loops
(Eq. 33) `∂_t g_ik = −2R_ik − a(R_{ilmn}R_k^{lmn})`; the `a→0` limit is Hamilton's Ricci flow (Eq. 34)
`∂_t g_ab(t) = −2R_ab(t)`. Renormalizability ⟺ backward Ricci flow to `t = −∞` without singularities.

### 1.5 Knill — *Chopping up Riemannian manifolds* (quantumcalculus.org)

**Identity.** Expository blog post, integral-geometric discrete curvature. No field theory.

(a) **Probability space of Morse functions**: via a Nash embedding, take linear functions on the
ambient Euclidean space; "already Morse knew that almost all such functions induce Morse functions on
M". Poincaré–Hopf index at a hyperbolic critical point is `(−1)^{m(x)}`, `m(x)` the Morse index.
(b) **Curvature = index expectation**: "taking a probability space of Morse functions produces a
curvature… It is just Fubini's theorem assuring that integrating over the probability space of Morse
functions and integration over the manifold can be interchanged." No tensors, forms, or bundles.
(c) **Gauss–Bonnet on a triangle via dual angles**: "the curvature is located on the vertices and given
by the dual angles π−α, π−β, π−γ. Summing up these curvature gives 2π. The sum of angle formulas is the
simplest known Gauss–Bonnet incarnation." (d) **Chopping up**: M is the geometric realization of a
finite abstract simplicial complex G (a finite set of non-empty sets closed under taking non-empty
subsets); topology survives, the metric is lost, curvature can be transported. A Morse function induces
an **energy** `h(x)` per simplex = sum of induced indices; every simplex is contractible with χ = 1, so
the "Bosonic" choice `h(x) = 1` gives total energy = number of simplices, while the "Fermionic" choice
`ω(x) = (−1)^{dim x}` sums to **Euler characteristic**. (e) The **counting matrix** `K(x,y)` = number of
simplices in `x ∩ y` is unimodular positive definite with an integer Green function `K^{-1}`.
(f) Negative result: the "new curvature" K (a d-point correlation of sectional curvatures) does **not**
integrate to χ — SU(3) has χ = 0 but K > 0 — and the naive discrete sum was not even
coordinate-independent.

---

## 2. Consolidated specification (plain JavaScript, no libraries)

### 2(a) Cell complex, incidence, Hodge stars

**Representation.** Vertices carry exact rational coordinates as BigInt `[num, den]` pairs (a small
`Rat` class with `add/mul/cmp` and gcd reduction). Cells are index arrays; orientation is array order:
`V` (0-cells), `E` (1-cells `[a,b]`, oriented a→b), `F` (2-cells, ordered vertex loop).

**Incidence, exact over ℤ.** Store `d0` and `d1` as sparse rows of `{col, sign}`:

    d0[e] = { [b]: +1, [a]: -1 }                     // (d0 φ)_e = φ_b − φ_a
    d1[f][e] = +1 if e traversed with its orientation in ∂f, −1 if against

Invariant to assert at construction, exactly, in integer arithmetic: **`d1 · d0 = 0`** (every row of the
product is identically zero). Also `χ = |V| − |E| + |F|` as an exact integer (Knill's Fermionic total
energy). These two are the only structural checks worth having and both are free of floating point.

**Regular square lattice, periodic, `L×L`, spacing `a ∈ ℚ`.** Vertex `(i,j) → (a·i, a·j)`. Edges:
`ex(i,j): (i,j)→(i+1,j)`, `ey(i,j): (i,j)→(i,j+1)`, indices mod L. Face `f(i,j)` boundary
`+ex(i,j) +ey(i+1,j) −ex(i,j+1) −ey(i,j)`. Circumcentre of a square = its centre, so the dual is the
shifted square lattice. **Every Hodge star is rational:**

    ⋆0 = |σ*_0(i)| = a²          (dual square area)
    ⋆1 = |σ*_1(e)| / |σ_1(e)| = a/a = 1
    ⋆2 = 1/|σ_2(f)| = a^{-2}

There are **no square roots at all** in the square-lattice geometry. The Laplacian
`Δ = ⋆0^{-1} d0ᵀ ⋆1 d0` reduces to the exact 5-point stencil `(Δφ)_i = a^{-2} Σ_{j~i}(φ_i − φ_j)`.

**Triangulated surface.** For each triangle `(p,q,r)` the circumcentre `c` solves a 2×2 linear system
with rational coefficients, so **`c` is rational whenever the vertices are**. The edge weight is the
DEC ratio, and the identity that makes it computable without any length is

    w_ij = |σ*_1(ij)| / |σ_1(ij)| = ½(cot α_ij + cot β_ij),
    cot θ_k = (u·v)/|u×v|  with u = r_i − r_k, v = r_j − r_k

Exactness ledger:

| quantity | planar, rational verts | in ℝ³, rational verts |
|---|---|---|
| circumcentre coords | **rational** | rational (in-plane) |
| triangle area `A` | **rational** | `½√(rational)` — **needs √** |
| `cot θ = (u·v)/(2A)` | **rational** | rational/√(rational) — **needs √** |
| edge length `l_ij` | **needs √** | **needs √** |
| dual edge length `|σ*_1|` | **needs √** | **needs √** |
| `w_ij = ⋆1` | **rational** | **needs √** |
| dual vertex area `√g_i = ⋆0` | **rational** | **needs √** |
| `d0, d1, χ` | exact ℤ | exact ℤ |

The useful fact: **on a planar rational triangulation the operators (`⋆0`, `⋆1`, the stiffness matrix)
are exactly rational even though the lengths defining them are not** — the square roots cancel in the
ratio. On a curved embedded surface they do not cancel.

**Normalization (see §3).** Use `S_kin = ½Σ_{⟨ij⟩} w_ij(φ_i − φ_j)²`, `w_ij = ½(cot α + cot β)`. This
equals `½∫_M|∇φ|²` for linear elements; on the square lattice `w = 1`, reducing to
`½Σ_xΣ_μ(φ_{x+μ̂} − φ_x)²`, whose spectrum is Brower Eq. (2.26). Brower's `V_ij/l²_ij` form is the same
object up to a normalization his own text and Fig. 2.3 caption disagree about; anchor on the
`∫|∇φ|²` check, not on the paper's letters.

### 2(b) Free scalar field: action, propagator, one vacuum sample, evolution

**Action and quadratic form.** `S[φ] = ½ φᵀ M φ`, `M = K + m² diag(√g_i)`, `K = d0ᵀ ⋆1 d0`.
`M` is symmetric; on a closed complex with `m = 0` it has exactly one zero mode (the constant).

**Two distinct covariances — do not conflate them.** On a periodic `L^d` lattice with `a = 1`, with
`k_μ = 2πn_μ/L`, `n_μ ∈ [0,L)`:

    Ê(k) = m² + Σ_μ 4 sin²(k_μ/2),      ω_k = √(Ê(k))

- **Euclidean / space-time propagator** (Brower Eqs. 2.24, 2.26), the thing whose modulus you plot:
  `G(x) = (1/N) Σ_k e^{ik·x} / Ê(k)`, `N = L^d`.
- **Equal-time vacuum covariance** (what a *snapshot* is drawn from):
  `C_φ(x) = (1/N) Σ_k e^{ik·x} / (2ω_k)` and `C_π(x) = (1/N) Σ_k e^{ik·x} ω_k/2`.

**Drawing ONE fluctuation sample.** Sample in Fourier space with Hermitian symmetry so the result is
real; no Cholesky is needed because the covariance is diagonal in `k`.

    function sampleVacuum(L, d, m2, gauss) {
      const N = L**d, w = new Float64Array(N);
      forEachMode(n => { let s = 0;
        for (let mu=0; mu<d; mu++) { const t = Math.sin(Math.PI*n[mu]/L); s += 4*t*t; }
        w[idx(n)] = Math.sqrt(m2 + s); });
      // independent half of the Brillouin zone: pair k with −k (mod L)
      for each k in half:
         const g1 = gauss(), g2 = gauss(), amp = Math.sqrt(1/(2*w[k])) / Math.SQRT2;
         phiRe[k] =  amp*g1; phiIm[k] =  amp*g2;
         phiRe[negk] = amp*g1; phiIm[negk] = -amp*g2;
      for each self-conjugate k (every n_mu ∈ {0, L/2}):
         phiRe[k] = Math.sqrt(1/(2*w[k])) * gauss(); phiIm[k] = 0;
      // π identically, with amplitude Math.sqrt(w[k]/2)
      return { phi: realIDFT(phiRe, phiIm), pi: realIDFT(piRe, piIm) };  // 1/√N convention
    }

Zero mode: at `m = 0`, `w[0] = 0` and the constant mode has infinite variance. **Set it to zero and say
so.** That deletion is the lattice image of the Gérard–Hiroshima infrared condition: the finite-volume
soft-mode content `(1/N)Σ_k|χ_k|²/ω_k³` is the discrete `∫χ(k)²/|k|³dk`, which diverges as `L → ∞` in
`d = 3` and worse below. It is physics, not a numerical artifact. Verify the sampler by averaging
`⟨φ_xφ_y⟩` over ~10⁴ draws against `C_φ(x−y)`; that check is the whole correctness argument.

**Evolution — Klein–Gordon leapfrog.** Split the vacuum sample into `(φ, π)` and integrate:

    π_x += dt * ( LapLat(φ)_x − m²φ_x );       // half-shifted momentum
    φ_x += dt * π_x;                            // LapLat = −K/⋆0, the 5-point stencil

Each Fourier mode is an exactly solvable discrete oscillator with `ω_Δt = (2/Δt)arcsin(Δt ω_k/2)`, real
**iff `Δt ω_k ≤ 2`**. CFL `Δt ≤ 2/ω_max`, `ω_max = √(m² + 4d)`; use `Δt = 0.4/√(m² + 4d)` for clean
phase error. The free vacuum Gaussian is *invariant* under this evolution, so an animated sample is
statistically stationary — it churns without drifting. That is the correct visual claim.

**Legitimately renderable.** (1) A **field sample** `φ_x`, labelled a sample, with `m` and `a` stated.
(2) `|G(x₀,x)|` from a fixed probe site — deterministic, no sampling; in `d = 2` at small `m` it is
`≈ −(1/2π)log(m|x|)`, and at `m = 0` it is defined only up to an additive divergent constant, so render
`G(x₀,x) − G(x₀,x_ref)`. (3) **Mode amplitudes** `|φ̃_k|²` of the drawn sample beside the ensemble mean
`1/(2ω_k)`. (4) The **dispersion** `ω_k` and its `O(a²)` deviation `−(1/12)Σ_μ k⁴_μ` from `√(m²+k²)`.
(5) Ensemble-averaged connected correlators from many samples, with error bars.

**Not renderable.**
- "The value of the vacuum" at a point. The vacuum is a *state* — a Gaussian measure on
  configurations — not a configuration. `⟨φ_x⟩ = 0` identically.
- A bare `⟨φ²_x⟩` as physical: it is `(1/N)Σ_k 1/(2ω_k)`, cutoff-dominated, log-divergent in 2-d and
  linearly in 3-d — precisely Brower's `[M^{-1}]_xx` (Eq. 3.9). Only the subtracted `δG_xx` (Eq. 3.12)
  is meaningful, and only on a *non-uniform* complex. Local energy density of a sample as an absolute
  number has the same defect.
- Any claim of cutoff-independence. Halve `a` and the picture changes at every scale.

### 2(c) 2-D incompressible Navier–Stokes, vorticity–streamfunction, DEC, periodic square lattice

**Placement.** `ψ`, `ω` are 0-forms on vertices; `dψ` is a 1-form on primal edges; `u = ⋆dψ` is a
1-form on **dual** edges (on a square lattice `⋆1 = 1`, so numerically identical to `dψ` up to the 90°
rotation relating an edge to its dual). Componentwise with spacing `h`:

    u_x(i+½,j) = ( ψ(i,j+1) − ψ(i,j) ) / h  →  u = +∂_yψ
    u_y(i,j+½) = −( ψ(i+1,j) − ψ(i,j) ) / h →  v = −∂_xψ

**Why DEC and not pressure projection.** `u = ⋆dψ` with `dd = 0` (Brower Eqs. 2.9, 2.12) makes the
discrete divergence `d0ᵀ⋆1 u ≡ 0` **identically**, with no Poisson projection on the velocity.
Incompressibility is structural. Equations:

    ω = −Δψ ,    u = ⋆dψ ,    ∂_t ω + u·∇ω = ν Δω ,    Δ = ⋆0^{-1} d0ᵀ ⋆1 d0

**Step loop.**

    for each frame:
      omega = omega − mean(omega)               // periodic solvability: Σω = 0
      psi   = poisson(omega)                    // solve −Δψ = ω, fix mean(ψ)=0
      u     = starD(psi)                        // exactly divergence-free
      w1    = advect(omega, u, dt)              // semi-Lagrangian or upwind
      omega = w1 + nu*dt*Lap(w1)                // explicit diffusion

Advection, semi-Lagrangian (unconditionally stable, first order; its numerical diffusion acts like an
extra `ν ≈ |u|h/2` — state that):

    xs = x − dt*u(x);  (RK2: xm = x − ½dt·u(x); xs = x − dt·u(xm))
    omega_new(x) = bilerp(omega, xs)            // periodic wrap on indices

Advection, first-order upwind (conservative-ish, cheap, honest CFL):

    dwdx = (u>0) ? (w[i]−w[i−1])/h : (w[i+1]−w[i])/h;   likewise dwdy
    omega_new = w − dt*(u*dwdx + v*dwdy)

**Stability.** Explicit diffusion on the 5-point Laplacian: `ν dt/h² ≤ 1/4` (2-D). Upwind advection:
`max(|u|,|v|)dt/h ≤ 1`, use `≤ 0.5`. Semi-Lagrangian removes the advective limit, but keep the
trace-back under ~3 cells or interpolation smears visibly. Practical: `dt = min(0.2h²/ν, 0.5h/max|u|)`.

**Poisson solve.** `A = −Δ` is symmetric positive semidefinite in the `⋆0`-weighted inner product
`⟨a,b⟩ = Σ_i √g_i a_i b_i`, because `⟨a, Ab⟩ = (d0 a)ᵀ ⋆1 (d0 b)`. That identity is what licenses CG on
a general triangulation, not only on the square lattice.

    function A(p) { // −Δp, DEC form; on the square lattice this is the 5-point stencil / h²
      for each vertex i: { let s=0; for each edge (i,j): s += w_ij*(p[i]−p[j]); out[i] = s/g[i]; }
    }
    function cgPoisson(omega, psi, tol, maxit) {
      let b = sub(omega, weightedMean(omega));           // project onto range(A)
      let r = sub(b, A(psi)); r = sub(r, weightedMean(r));
      let p = r.slice(), rs = dotG(r,r), bn = Math.sqrt(dotG(b,b));
      for (let it=0; it<maxit; it++) {
        const Ap = A(p); const den = dotG(p,Ap); if (den <= 0) break;
        const alpha = rs/den;
        axpy(psi, alpha, p); axpy(r, −alpha, Ap);
        r = sub(r, weightedMean(r));                     // keep the null space out
        const rs2 = dotG(r,r);
        if (Math.sqrt(rs2) < tol*bn) break;
        p = add(r, scale(p, rs2/rs)); rs = rs2;
      }
      return sub(psi, weightedMean(psi));                // fix the constant
    }

Multigrid V-cycle (square lattice only; needs a hierarchy `L, L/2, L/4, …`):

    function vcycle(psi, b, lvl) {
      smooth(psi, b, lvl, n1);                        // red-black Gauss-Seidel, ω=1
      const r = sub(b, A_lvl(psi, lvl));
      const b2 = restrict(r);                         // full weighting 1/16·[1 2 1; 2 4 2; 1 2 1]
      let e2 = zeros(size(lvl+1));
      if (lvl+1 === coarsest) e2 = solveDirect(b2); else e2 = vcycle(e2, b2, lvl+1);
      axpy(psi, 1, prolong(e2));                      // bilinear interpolation
      smooth(psi, b, lvl, n2);
      return psi;
    }

With `n1 = n2 = 2`, one V-cycle per frame cuts the residual ~10× and suffices for rendering; CG warm-
started from the previous frame is simpler and nearly as fast at `L ≤ 512`.

**Renderable, and worth rendering as a correctness check:** `ω`; streamlines (contours of `ψ` — exactly
right, since `u = ⋆dψ` makes `u` tangent to level sets of `ψ`); speed `|u|`; energy
`E = ½Σ w_ij(dψ)²_ij` and enstrophy `Z = ½Σ√g_i ω_i²`. With `ν > 0` and no forcing both must decrease
monotonically; if they don't, the time step is unstable.

### 2(d) Exact over ℚ versus floating-point faces

**Exact over ℚ (or ℤ) — BigInt rationals, assert equalities as equalities:** vertex coordinates;
`d0`, `d1`, `d1·d0 = 0`; `χ = V − E + F`; circumcentres; all square-lattice Hodge stars
(`⋆0 = a²`, `⋆1 = 1`, `⋆2 = a^{-2}`) and hence the whole square-lattice stiffness matrix and stencil;
on a **planar** rational triangulation the cotangent weights `w_ij`, circumcentric dual areas `√g_i`,
and the whole stiffness/mass pair; the row-sum identity `Σ_j w_ij·1 = 0`; the mean-subtraction making
`Σω = 0`; Knill's combinatorics (simplex counts, `h(x) = 1`, `ω(x) = (−1)^{dim x}`, the counting matrix
`K(x,y)` and its integer inverse).

**Floating-point faces — each needs a stated tolerance:** all primal and dual edge lengths; every
metric quantity on a **curved** triangulation, `w_ij` and `√g_i` included; `ω_k = √(m² + Σ4sin²(k/2))`
and every trig/DFT; Gaussian sampling (Box–Muller: `log`, `cos`, `sqrt`); the mode sums for `G` and
`C_φ`; the leapfrog trajectory; CG/multigrid iterates and residual thresholds; semi-Lagrangian
trace-back and bilinear interpolation; Brower's `δG_xx`, which needs `M` inverted numerically.

**Architecture.** Two layers, hard boundary. The *combinatorial-metric layer* is exact rational and
answers only structural questions (`d1 d0 = 0`, `χ`, `w_ij` and dual areas where rational). The
*analysis layer* is `Float64Array` throughout, validated at startup against exact identities from the
first layer: zero row sums, `Σ_i√g_i =` total area, `Δ` of a linear function zero on a planar mesh,
`div(⋆dψ) = 0` to machine precision. Converting rational to float is a one-way door: confine it to one
function.

---

## 3. Where the sources disagree, or are silent

**QFE counterterms are for curved complexes and are inert on a square lattice.** `δG_xx =
[M^{-1}]_xx − N^{-1}Σ_x √g_x[M^{-1}]_xx` vanishes identically on any translation-invariant lattice,
because `[M^{-1}]_xx` is then position-independent. So a flat periodic torus renderer needs no QFE
counterterm; a triangulated sphere does. Further, the counterterm is `O(λ₀)` — it is a property of the
*interacting* theory. **Nothing in the free-field fluctuation renderer of §2(b) requires it.** Brower's
own Sec. 2.3 shows the free FEM spectrum is already faithful without any counterterm.

**Brower has an internal factor-of-2 inconsistency.** Eq. (2.10) with `n=1, d=2` gives
`V_ij = ½ l_ij|σ*_1|`, so `V_ij/l²_ij = |σ*_1|/(2l_ij)`; but Eq. (2.16) equates `V_ij/l²_ij` with
`|σ*_1|/|σ_1|`, which requires `V_ij = l_ij|σ*_1|`. The Fig. 2.3 caption says `S_ij = 2V_ij/l_ij` while
the body text says `S_ij/(d−1)! = V_ij/l_ij`, i.e. `S_ij = V_ij/l_ij` at `d = 2`. Do not resolve this by
reading harder; resolve it by the independent check `½Σ w_ij(φ_i−φ_j)² = ½∫|∇φ|²`, giving
`w_ij = ½(cot α + cot β) = |σ*_1|/|σ_1|`, and on the square lattice `w = 1`.

**Gérard–Hiroshima never discretize.** Continuum, 3 spatial dimensions, with assumptions
(Kato-decomposable `V`, `sup|Ψ| < ∞`, `β > 3`, `κ` small) that have no lattice analogue. What transfers
is one statement: whether the soft-mode integral converges. The lattice version is a finite sum, always
finite at finite `L`; the divergence appears only as `L → ∞`. **No source in this set treats real-time
evolution of a sampled field**; the leapfrog in §2(b) is an addition, justified only by the invariance
of the free equal-time vacuum Gaussian under free evolution — verify it numerically, do not cite it.

**Dang–Herscovich give existence, not a scheme.** *Extension of distributions across diagonals* has no
lattice counterpart — a lattice has already regularized, and there is nothing singular to extend. Their
axioms (i)–(iii) are nevertheless the specification a lattice scheme must satisfy in the continuum
limit; covariance (iii) is obtained abstractly by Haar-averaging `P_Ω` over the isometry group, whereas
Brower's `δG_xx` is a concrete numerical realization of the same requirement (averaging over `SO(3)`,
Eq. 3.11). Neither paper cites the other; the alignment is ours to assert, not theirs.

**Carfora–Romano's "graphs" are not simplicial.** I searched their full text: no triangulation, no
simplicial complex, no Regge calculus, no deficit angle, no dual polytope. `G` in Eq. (16) is the set
of isomorphism classes of connected Feynman graphs. Their fluctuation `η` is a section of `ψ*TM` with
an IR regulator `Λ' = 1/(2r)` of purely geometric (geodesic-ball) origin, and their renormalization
(Eq. 29) renames the **target** metric, not the worldsheet lattice. **Their Ricci flow result cannot be
used to justify anything about a lattice or about rendered geometry.** It is a statement about the RG
of a continuum sigma model.

**Knill supplies curvature but no dynamics.** No propagator, action, or field. His triangle curvature
`π−α, π−β, π−γ` summing to `2π` lives on the **boundary vertices of a single polygon** (Poincaré–Hopf
for a Riemannian polyhedron); Regge's deficit angle `2π − Σθ` lives on **interior vertices of a closed
surface**. They differ in sign convention and in which cells carry the charge — do not conflate them.
Knill also retracts his strongest claim: `K` does **not** integrate to `χ` (SU(3): `χ = 0`, `K > 0`),
and the naive discrete sum was not coordinate-independent. So "curvature integrates to Euler
characteristic" may be rendered only in the Fermionic case `ω(x) = (−1)^{dim x}`, where it is a counting
identity, not a metric one.

**Silence on fluids.** None of the five sources treats Navier–Stokes, incompressibility, advection,
time stepping, or any solver. The §2(c) specification is standard DEC/CFD. The only structural
inheritance is `dd = 0` (Brower Eqs. 2.9, 2.12), which makes `u = ⋆dψ` divergence-free by construction,
and the `⋆0`-weighted inner product from Eq. (2.15), which makes `−Δ` symmetric positive semidefinite
and therefore CG-solvable on an irregular triangulation.

**Silence on exactness.** No source discusses rational arithmetic, floating point, or numerical
representation. The ℚ-versus-float ledger in §2(a)/§2(d) — in particular that cotangent weights are
exactly rational on a planar rational triangulation while the lengths defining them are not — is
derived here, not sourced.
