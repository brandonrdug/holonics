#import "schema.typ": entry

#let computation-information = (
  entry(
    id: "H.0400",
    kind: "Definition",
    grade: "definition",
    title: [Formal language and automaton],
    depends: ("H.0100", "H.0140"),
    statement: [
      A formal language is a subset of finite words over an alphabet. A finite
      automaton is a finite state transition system with initial and accepting
      states; it recognizes exactly the words whose induced path ends in an
      accepting state.
    ],
    transformations: [
      Alphabet symbols, state path, and acceptance are distinct receiver
      layers. Regular languages are closed under Boolean operations and inverse
      homomorphism.
    ],
    boundary: [
      A recognized word does not reconstruct its state path in a nondeterministic
      automaton, and a language is not a semantic ontology.
    ],
    source: [Classical automata theory.],
  ),
  entry(
    id: "H.0401",
    kind: "Definition",
    grade: "definition",
    title: [Turing computation and partial function],
    depends: ("H.0103", "H.0400"),
    statement: [
      A Turing machine has a finite control and an unbounded finite-support tape.
      Its transition relation generates configurations. It computes a partial
      function when every accepted input has a unique halting output and
      divergence denotes undefinedness.
    ],
    transformations: [
      The partial input/output function is one receiver of the complete
      configuration path.
    ],
    boundary: [
      The model does not prescribe physical hardware, energy, representation
      cost, interaction with an open world, or semantic meaning.
    ],
    source: [Turing-machine definition.],
  ),
  entry(
    id: "H.0402",
    kind: "Boundary",
    grade: "project-postulate",
    title: [Church--Turing thesis boundary],
    depends: ("H.0110", "H.0401"),
    statement: [
      The Church--Turing thesis identifies effectively calculable number
      functions with Turing-computable functions. Equivalent formal models
      include lambda-definability and partial recursion.
    ],
    transformations: [
      Simulation theorems relate formal machine presentations. The thesis
      relates those formal classes to the preformal notion of effective method.
    ],
    boundary: [
      It is not a theorem derived from holonics and does not claim that every
      physical, interactive, stochastic, or semantic process is one closed
      function.
    ],
    source: [Church--Turing thesis and classical equivalence theorems.],
  ),
  entry(
    id: "H.0403",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Decidability, enumeration, and the halting boundary],
    depends: ("H.0401",),
    statement: [
      A set is decidable when a total machine returns its characteristic
      function and computably enumerable when a partial machine halts exactly
      on its members. The halting set is computably enumerable but not
      decidable.
    ],
    transformations: [
      Diagonalization constructs an exact open boundary for a universal
      machine's self-prediction receiver.
    ],
    boundary: [
      Undecidable does not mean random, physically impossible, or unsolvable for
      every bounded instance.
    ],
    source: [Turing undecidability theorem.],
  ),
  entry(
    id: "H.0404",
    kind: "Definition",
    grade: "definition",
    title: [Reduction and complexity class],
    depends: ("H.0401",),
    statement: [
      A polynomial-time many-one reduction $A<=_p B$ is a polynomial-time
      computable $f$ with $x in A$ exactly when $f(x) in B$.
      $"P"$ contains polynomial-time decidable languages; $"NP"$ contains
      languages with polynomially checkable polynomial-size witnesses.
    ],
    transformations: [
      A reduction transports instances and yes/no consequences while retaining
      a resource bound.
    ],
    boundary: [
      $"P"="NP"$ is open. “Localized P=NP,” starvation, analogy, or one fast
      instance is not the standard proposition.
    ],
    source: [Classical computational complexity theory.],
  ),
  entry(
    id: "H.0405",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Rewrite relation, termination, and confluence],
    depends: ("H.0022", "H.0021"),
    statement: [
      A rewrite system is a relation $arrow.r$ on terms. It is terminating when
      no infinite rewrite path exists and confluent when every fork
      $a arrow.r^* b,c$ has a join. Termination plus local confluence implies
      confluence.
    ],
    transformations: [
      A commuting diamond is an exact join of two causal rewrite paths; a failed
      diamond is OPEN at that law grain.
    ],
    boundary: [
      Confluence does not imply termination, efficiency, semantic correctness,
      or equality of the interior paths.
    ],
    source: [Newman's lemma and Church--Rosser theory.],
  ),
  entry(
    id: "H.0406",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Lambda calculus and Curry--Howard],
    depends: ("H.0020", "H.0405"),
    statement: [
      Simply typed lambda terms obey beta reduction and subject reduction.
      Under Curry--Howard, propositions correspond to types and normal proof
      terms to derivations in the matching intuitionistic logic.
    ],
    transformations: [
      Substitution is computational transport; normalization presents a proof
      or program through another exact syntax path.
    ],
    boundary: [
      The laboratory symbol `Lambda` names a parameterized transition family,
      not automatically the lambda calculus. Curry--Howard depends on the chosen
      logic and type theory.
    ],
    source: [Simply typed lambda calculus and Curry--Howard correspondence.],
  ),
  entry(
    id: "H.0407",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Directed completeness and recursive fixed point],
    depends: ("H.0140", "H.0406"),
    statement: [
      In a pointed directed-complete partial order, a Scott-continuous
      $F:D arrow.r D$ has least fixed point
      $
        "lfp"(F)=sup_n F^n(⊥).
      $
    ],
    transformations: [
      Finite unfoldings form a directed lineage whose supremum receives a
      recursive computation, including partial or infinite behavior.
    ],
    boundary: [
      The theorem requires directed completeness and Scott continuity; not every
      recursive system has this domain model.
    ],
    source: [Kleene fixed-point theorem in domain theory.],
  ),
  entry(
    id: "H.0408",
    kind: "Definition",
    grade: "definition",
    title: [Typed hypergraph and double-pushout rewrite],
    depends: ("H.0025", "H.0294",),
    statement: [
      A typed hypergraph has vertices and hyperedges incident to ordered or
      typed vertex families. A double-pushout rewrite presents a rule as a span
      $L arrow.l K arrow.r R$, matches $L$ into a host, removes only the
      complement permitted by the gluing condition, and adjoins $R$ by pushout.
    ],
    transformations: [
      The interface $K$ is the retained seam between the old and new incidence
      regions.
    ],
    boundary: [
      A graph-rewrite formalism is not identical to a physical universe,
      simplicial manifold, or computational algorithm until translations are
      supplied.
    ],
    source: [Algebraic graph transformation by double pushout.],
  ),
  entry(
    id: "H.0409",
    kind: "Definition",
    grade: "definition",
    title: [Cellular automaton and spacetime diagram],
    depends: ("H.0108", "H.0294"),
    statement: [
      A cellular automaton on a regular cell complex has a finite local state
      set, a finite neighborhood, and one translation-compatible local update
      law applied synchronously. Iteration produces a discrete spacetime
      diagram.
    ],
    transformations: [
      Global propagation is generated by repeated local incidence. A simplicial
      or asynchronous generalization must explicitly replace regular cells,
      neighborhood, clock, and update compatibility.
    ],
    boundary: [
      Scalar state per regular cell and synchronous time are model choices, not
      universal requirements of discrete dynamics.
    ],
    source: [Classical cellular automata; generalized-cell boundary stated explicitly.],
  ),
  entry(
    id: "H.0410",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Kolmogorov description complexity],
    depends: ("H.0111", "H.0401"),
    statement: [
      For a fixed universal prefix machine $U$,
      $
        K_U(x)=min{abs(p):U(p)=x}.
      $
      For universal prefix machines $U,V$, there is a constant $c$ with
      $abs(K_U(x)-K_V(x))<=c$ for every $x$.
    ],
    transformations: [
      Description length is receiver-relative to a universal interpreter class;
      invariance is additive, not identity of programs.
    ],
    boundary: [
      $K$ is uncomputable in general and does not retain execution path,
      runtime, meaning, or causal provenance.
    ],
    source: [Invariance theorem for prefix Kolmogorov complexity.],
  ),
  entry(
    id: "H.0411",
    kind: "Definition",
    grade: "definition",
    title: [Entropy, conditional information, and mutual information],
    depends: ("H.0019", "H.0240"),
    statement: [
      For a finite distribution $p$ and one fixed logarithm base,
      $
        H(X)=-sum_x p(x)log p(x),
      $
      with $0 log 0=0$. Conditional entropy and mutual information obey
      $
        I(X;Y)=H(X)-H(X|Y)=D_("KL")(p_(X,Y) norm p_X p_Y)>=0.
      $
    ],
    transformations: [
      Entropy is a receiver of a declared recurrence law; mutual information is
      the residual from product factorization.
    ],
    boundary: [
      These scalars do not identify occurrences, semantic meaning, topology, or
      the causal path that produced the distribution.
    ],
    source: [Shannon entropy and Gibbs inequality.],
  ),
  entry(
    id: "H.0412",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Data-processing inequality],
    depends: ("H.0411",),
    statement: [
      For a Markov chain $X arrow.r Y arrow.r Z$,
      $
        I(X;Z)<=I(X;Y).
      $
      More generally relative entropy contracts under a stochastic kernel.
    ],
    transformations: [
      A downstream receiver cannot increase the distinctions measured by this
      information divergence without new incidence.
    ],
    boundary: [
      The inequality is relative to the selected distributions and divergence.
      It does not forbid a receiver from making a task-specific feature more
      accessible.
    ],
    source: [Data-processing inequality.],
  ),
  entry(
    id: "H.0413",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Source and channel coding boundary],
    depends: ("H.0411", "H.0412"),
    statement: [
      For an independent identically distributed finite-alphabet source,
      entropy is the sharp asymptotic lossless coding rate. For a declared
      finite-alphabet memoryless channel,
      capacity is
      $
        C=max_(p(x)) I(X;Y),
      $
      with reliable rates below $C$ and converse obstruction above $C$.
    ],
    transformations: [
      Encoding, channel transport, and decoding are a complete declared
      communication relation; capacity is its asymptotic rate receiver.
    ],
    boundary: [
      Coding theorems do not define semantic meaning or claim that every
      ecological source is independent, stationary, or memoryless.
    ],
    source: [Shannon source and noisy-channel coding theorems.],
  ),
  entry(
    id: "H.0414",
    kind: "Definition",
    grade: "definition",
    title: [Stochastic kernel and Markov transport],
    depends: ("H.0019", "H.0240"),
    statement: [
      A stochastic kernel $K(x,d y)$ assigns a probability measure to each
      source occurrence measurably. Composition is
      $
        (L K)(x,A)=integral L(y,A)K(x,d y).
      $
      A stationary measure satisfies $pi K=pi$.
    ],
    transformations: [
      Kernels are receiver-relative conditional transport laws; their
      composition is exact integration over the intermediate occurrence.
    ],
    boundary: [
      A deterministic law is a Dirac-kernel specialization. Stationarity is not
      equilibrium, reversibility, or ergodicity without further conditions.
    ],
    source: [Standard Markov-kernel theory.],
  ),
  entry(
    id: "H.0415",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Convex duality and separating receiver],
    depends: ("H.0140", "H.0242"),
    statement: [
      In a locally convex Hausdorff real topological vector space, a nonempty
      closed convex set and an exterior point can be strictly separated by a
      continuous linear functional. For proper lower-semicontinuous convex
      $f,g$ and a continuous linear $A$, Fenchel--Rockafellar duality relates
      $
        inf_x (f(x)+g(A x))
      $
      to its conjugate dual; equality holds, for example, when some
      $x_0 in "dom" f$ has $g$ continuous at $A x_0$.
    ],
    transformations: [
      Convex geometry turns an infeasible incidence into a linear witness and
      relates primal and dual objective faces.
    ],
    boundary: [
      Dual equality, attainment, uniqueness, and algorithmic efficiency each
      require separate hypotheses.
    ],
    source: [Hahn--Banach separation and Fenchel--Rockafellar duality.],
  ),
  entry(
    id: "H.0416",
    kind: "Boundary",
    grade: "proved-derived",
    title: [Exact computation and certificate],
    depends: ("H.0005", "H.0251", "H.0401"),
    statement: [
      A bounded computation may carry integers, rationals, algebraic numbers,
      symbolic expressions, formal series coefficients, or certified rational
      enclosures. Every emitted claim must be an exact identity, a checked
      certificate, or a completely quantified relation to one of these
      carriers.
    ],
    transformations: [
      Exact-arithmetic algorithms may emit progressively refined certified
      faces without collapsing the denoted construction.
    ],
    boundary: [
      A finite display is testimony only. A certificate must still be checked
      against its algorithm and hypotheses.
    ],
    source: [Computable analysis and exact-real arithmetic boundary.],
  ),
  entry(
    id: "H.0417",
    kind: "Definition",
    grade: "definition",
    title: [Unitary circuit and measurement receiver],
    depends: ("H.0029", "H.0241"),
    statement: [
      A finite quantum circuit is a composition and tensoring of unitary maps on
      finite-dimensional complex Hilbert spaces. A measurement is a positive
      operator-valued measure whose Born probabilities are
      $
        p(i)=chevron.l psi,E_i psi chevron.r,
        quad
        sum_i E_i=I.
      $
    ],
    transformations: [
      State evolution, subsystem tensor structure, and measurement distribution
      are distinct mathematical receivers.
    ],
    boundary: [
      This formalism does not make every probabilistic, parallel, or
      information-geometric algorithm physically quantum.
    ],
    source: [Finite-dimensional quantum information theory.],
  ),
  entry(
    id: "H.0418",
    kind: "Definition",
    grade: "definition",
    title: [Statistical learning problem],
    depends: ("H.0019", "H.0411", "H.0415"),
    statement: [
      A statistical learning problem declares a hypothesis family $cal(H)$, a
      data law on occurrences, a loss receiver $ell(h,z)$, and population risk
      $R(h)=EE[ell(h,Z)]$. Generalization bounds relate empirical and population
      receivers through a capacity measure and sampling law.
    ],
    transformations: [
      Parameters, data ecology, prediction face, and loss comparison are
      separately typed. Optimization selects a member under the declared risk;
      it does not define truth.
    ],
    boundary: [
      No universal learning law follows from this portal. Model class, ecology,
      receiver, dependence, and objective determine the theorem.
    ],
    source: [Statistical learning theory; laboratory loss regrade.],
  ),
  entry(
    id: "H.0419",
    kind: "Boundary",
    grade: "proved-standard",
    title: [Formal provability, finite witnesses, and incompleteness],
    depends: ("H.0106", "H.0401", "H.0403"),
    statement: [
      Let $T$ be an effectively axiomatized formal theory containing enough
      arithmetic to verify finite computations. For a decidable predicate
      $R(n)$, the universal sentence
      $
        Phi = forall n in NN, R(n)
      $
      has $Pi^0_1$ form. Its negation has a finite witness:
      $
        not Phi
        arrow.l.r
        exists n in NN, not R(n).
      $
      Equivalently, a machine which enumerates $n$ and halts at the first failed
      check halts exactly when $Phi$ is false.

      Gödel incompleteness says that every consistent, effectively axiomatized,
      sufficiently expressive $T$ leaves some arithmetic sentence undecided. It
      does not say that any named open sentence is independent of $T$.
    ],
    transformations: [
      The same object has three typed faces: a universal arithmetic assertion,
      a nonhalting assertion, and the absence of a finite counterexample
      certificate. If $Phi$ is false, its standard finite witness can be checked
      inside an arithmetically adequate $T$. If $Phi$ is true, a finite proof may
      still establish its universal invariant; otherwise independence from $T$
      is a separate metatheorem about the proof system.
    ],
    boundary: [
      "Unresolvable" is not an absolute third truth value. Independence must
      name $T$ and prove both $T$ does not prove $Phi$ and $T$ does not prove
      $not Phi$, ordinarily under a stated consistency or soundness assumption.
      Long computation, emergent complexity, and quantification over infinitely
      many integers do not by themselves prove independence.
    ],
    source: [
      Gödel incompleteness and computability theory; finite-witness
      classification of $Pi^0_1$ sentences.
    ],
  ),
  entry(
    id: "H.0420",
    kind: "Theorem",
    grade: "proved-derived",
    title: [Loss is non-commutation; recovery adjoins a channel; the three species differ only by remainder],
    depends: ("H.0012", "H.0016", "H.0106", "H.0210", "H.0219", "H.0411"),
    statement: [
      For a compression $q:X arrow.r Q$ and receiver $rho:X arrow.r Y$, H.0016's
      factorization $rho=overline(rho) compose q$ *is* commutativity of the
      receiver square, so loss is its failure and is witnessed by a pair
      $
        q(x)=q(x') " and " rho(x) != rho(x').
      $
      Where $Y$ admits subtraction, the residual
      $r=rho(x)-overline(rho)(q(x))$ measures the failure and is a holonomy of
      the square (H.0210). For a further declared receiver $s:X arrow.r S$,
      $(q,s)$ is injective exactly when $s$ separates every fibre of $q$; and if
      $q$ is not injective, no left inverse $Q arrow.r X$ exists at all.
    ],
    derivation: [
      The factorization is the universal property of the quotient. A left
      inverse would force injectivity. Separation of fibres is exactly
      injectivity of the pair.
    ],
    transformations: [
      Three species of change of form differ only in what remainder they carry,
      and the corpus already types all three: *rebase* (H.0106) is an invertible
      conjugacy with **zero** remainder; *condensation* replaces a far population
      by a compact realizer with a **certified** remainder; *compression*
      (H.0016) is a quotient whose remainder is the collapsed population,
      **relative to a declared family**. Recovery of a "lossy" transformation is
      therefore never recovery from the image: it is recovery from image
      $xor$ channel, and the channel is purchased. A classical loss
      function is one receiver's scalar face of the residual and never the
      residual itself. A system admitting no local quotient must couple globally
      -- which is H.0219's barrier, and why an incompressibility constraint
      forces a nonlocal solve.
    ],
    boundary: [
      This does not make loss unreal; it makes it relative to a declared family
      and makes recovery a purchase with a stated price. Between bare sets there
      is no residual and no holonomy -- only the presence or absence of a filler
      -- and reading curvature into a set-level failure is an overreach. Nothing
      here supplies a family, a channel, or a constraint.
    ],
    source: [Universal property of the quotient; the identification and the trichotomy are the laboratory's.],
  ),
  entry(
    id: "H.0480",
    kind: "Equivalence",
    grade: "proved-derived",
    title: [The kernel is the collapsed-pair population, and the compression trichotomy classifies reversibility],
    depends: ("H.0016", "H.0106", "H.0262", "H.0420"),
    statement: [
      For a linear receiver $A$: $A x = A y$ exactly when $x - y in ker(A)$,
      so the kernel is the collapsed-pair population and rank plus nullity
      counts the passages that survive plus the passages that collapse.
      Reversibility of a transport is membership in the rebase species:
      rebase has remainder zero and is invertible; condensation is invertible
      up to its certified remainder; a quotient is irreversible with the
      collapsed population as its exact, exhibitable loss. Parity is a
      property of the boundary operator, chronology of the lineage, and
      reversibility of one specific transport, decided by its collapsed
      population; reconstruction of a departed interior is available only to
      the extent of a receiver-indexed limit, and the attribution of what was
      collapsed is a declared quotient.
    ],
    boundary: [
      Reversal is never guaranteed by parity or by chronology: a
      forward-deterministic semigroup (diffusion) is ill-posed backward, and
      nothing here supplies an inverse where the collapsed population is
      nonempty.
    ],
    source: [Standard linear algebra and semigroup theory; the three-way split of parity, chronology, and reversibility is Brandon's, 2026-08-11, `canon/TABLET_THE_OPERATIONS.md`.],
  ),
  entry(
    id: "H.0481",
    kind: "Definition",
    grade: "definition",
    title: [Proof-transport atlas],
    depends: ("H.0362",),
    statement: [
      A proof-transport node is a declaration read as a formulation node
      $(D,E,cal(H),v,rho)$: $D$ its parameter domain with binder kinds and
      types, $E$ the term or tactic realising it, $cal(H)$ its hypotheses and
      branch data, $v$ its conclusion's principal relation, and $rho$ the
      declared receiver family. An edge is a tactic whose application a kernel
      admits, carrying one node to another while preserving $v$. Admissibility
      is decided from $(D,v)$ **before** the kernel runs, and the recognition is
      graded against what the kernel then says.
    ],
    transformations: [
      Substitution demands $v in {=, <->}$ and is realised by rewriting;
      conjugacy applies the node in its own frame, positionally over $D$;
      recurrence is realised by induction. A closing tactic that reads an
      ordering or a normal form is a face, not an edge: it carries no node to
      another. Measured on a seven-declaration corpus, gating substitution on
      $v$ and building every application over $D$ took structurally refused
      paths from 147 to 0 while the admitted family was unchanged.
    ],
    boundary: [
      Shared output does not supply an edge, so a partition of nodes by equal
      observation is a coarsening and never an atlas row. Admissibility is a
      coverage claim and not a completeness one: a conclusion exposing no single
      relation at depth zero is treated as carrying none, and an edge whose
      tactic rewrites a hypothesis in place is inadmissible while $cal(H)$ is
      untracked. Neither exclusion is evidence that no such edge exists.
    ],
    source: [Specialisation of H.0362 to proof transport; measured 2026-08-14 against a real Lean kernel.],
  ),
)
