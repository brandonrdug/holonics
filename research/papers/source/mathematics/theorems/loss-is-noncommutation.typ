#let loss-is-noncommutation = (
  key: "theorem:loss-is-noncommutation",
  kind: [Theorem],
  title: [Loss is the non-commutation of a compression with a receiver, and recovery adjoins a channel],
  status: [Exact; the counting bound and the factorization are elementary, and the identification is the project's],
  depends: (
    "definition:receiver",
    "lemma:receiver-nonreconstruction",
    "definition:comparison-face",
    "theorem:limit-receiver-noncommutation",
  ),
  claim: [
    Let $q:X -> Q$ be a compression and $rho:X -> Y$ a receiver.

    *(EXACT IS COMMUTING)* $q$ is exact for $rho$ exactly when the square
    $
      mat(delim: #none,
        X, -->^q, Q;
        |, , |;
        rho, , overline(rho);
        |, , |;
        Y, ==, Y)
      quad "commutes for some" overline(rho),
      quad "(THE RECEIVER SQUARE)"
    $
    that is, when $rho=overline(rho) compose q$. It is exact for a *family*
    $cal(R)$ when every member's square commutes. So **exactness is
    commutativity and loss is its failure**, and the two are not analogies for
    one another.

    *(THE LOSS IS A PAIR, NOT A QUANTITY)* The square fails exactly when there
    exist $x,x'$ with
    $
      q(x)=q(x')
      quad "and" quad
      rho(x) != rho(x').
      quad "(THE COLLAPSED PAIR)"
    $
    The loss is that population of pairs together with the receiver that sees
    each one. It is not a magnitude, and a magnitude is a later face of it.

    *(THE RESIDUAL AND ITS TWO GRADES)* Between sets, ("THE RECEIVER SQUARE")
    either admits a filler or it does not, and non-existence is the whole return.
    When $Y$ carries a group or module structure, the failure is measured rather
    than only detected: for any chosen $overline(rho)$ the residual
    $
      r_(rho,q)(x)=rho(x)-overline(rho)(q(x))
      quad "(THE RESIDUAL)"
    $
    is the disagreement of two transports with common boundary, and its value
    around a closed comparison is a holonomy. *Loss is therefore a curvature of
    the compression, and a classical loss function is one receiver's scalar face
    of that residual, never the residual itself.*

    *(RECOVERY ADJOINS A CHANNEL)* Let $s:X -> S$ be a further declared receiver.
    Then
    $
      (q,s):X -> Q times S
      quad "is injective"
      quad &lt;==&gt; quad
      s "separates every fibre of" q,
      quad "(RECOVERY)"
    $
    and in that case $x$ is recovered from the pair $(q(x),s(x))$.

    *(AND IT NEVER RECOVERS FROM THE IMAGE ALONE)* If $q$ is not injective there
    is no left inverse $Q -> X$ whatsoever, by cardinality when $X$ is finite and
    by the collapsed pair in general. Hence every recovery of a "lossy"
    transformation is a recovery from $"image" xor "channel"$, and the
    missing information is supplied by the channel. Solving $x^2=4$ recovers $x$
    from $4$ *together with* a declared constraint such as $x&gt;0$ -- one bit,
    which is exactly the half turn the squaring erased. The bit is supplied, not
    retrieved.

    *(THE MINIMAL CHANNEL IS COMPUTABLE)* For a compression whose receivers act
    on input histories, the coarsest channel separating a collapsed pair is the
    *shortest distinguishing word* for that pair, and refining until no such word
    remains is the Nerode congruence reached by partition refinement. The
    recovery certificate is therefore an exhibitable object and not an estimate.
  ],
  proof: [
    ("EXACT IS COMMUTING") is the universal property of the quotient: $rho$
    factors through $q$ iff $rho$ is constant on fibres of $q$, which is
    ("THE COLLAPSED PAIR") negated.

    ("RECOVERY"): if $s$ separates every fibre then $q(x)=q(x')$ and
    $s(x)=s(x')$ force $x=x'$; conversely a fibre containing two points on which
    $s$ agrees is a pair on which $(q,s)$ fails to be injective.

    ("AND IT NEVER RECOVERS..."): a left inverse $ell$ with $ell compose q=id_X$
    would make $q$ injective, since $q(x)=q(x')$ gives
    $x=ell(q(x))=ell(q(x'))=x'$.
  ],
  boundary: [
    *This does not say loss is unreal.* It says loss is *relative to a declared
    family* and that recovery is *purchase of a channel*. The purchase has a
    price -- the channel is itself information that must be carried, declared, or
    supplied by a constraint -- and a construction that recovers without naming
    what it adjoined has hidden the cost rather than avoided it.

    ("THE RESIDUAL") requires enough structure on $Y$ to subtract. Between bare
    sets there is no residual and no holonomy, only the presence or absence of a
    filler. Reading a curvature into a set-level failure is an overreach.

    Nothing here supplies a receiver family, a channel, or a constraint. Which
    family is declared is the modelling act, and every statement above is
    conditional on it.
  ],
)
