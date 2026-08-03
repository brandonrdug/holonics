#let exact-receiver-turn-return = (
  key: "theorem:exact-receiver-turn-return",
  kind: [Theorem],
  title: [Exact local receiver turns close while their ordered interiors remain distinct],
  status: [Exact algebraic theorem with a bounded joint-receiver witness],
  depends: (
    "definition:joint-decorated-path-carrier",
    "theorem:source-diagram-loop-separation",
  ),
  claim: [
    Fix a rational two-dimensional receiver $r$. For nonzero consecutive
    projected source-chord directions $v,w in QQ^2$, define the exact turn
    quotient
    $
      tau_r(v,w)
      =
      (
        (v dot w)/(v dot v),
        op("det")(v,w)/(v dot v)
      )
      in QQ(i),
    $
    where pairs multiply by
    $
      (a,b)(c,d)=(a c-b d,a d+b c).
    $

    For every closed lawful source path
    $P=(d_1,...,d_n)$ whose receiver chords $v_1,...,v_n$ are nonzero,
    $
      product_(j=1)^n tau_r(v_j,v_(j+1))=(1,0),
      quad v_(n+1)=v_1.
    $

    This return is invariant under every regular change which leaves the path
    closed, but the ordered word
    $
      (
        d_j,
        Pi_(d_j),
        "crossings"_r(d_j),
        "metrics"_r(d_j),
        tau_r(v_j,v_(j+1))
      )_(j=1)^n
    $
    need not remain equal. The closed return alone therefore cannot identify
    the path, receiver, or contemporary source cut.
  ],
  proof: [
    Identify $(x,y) in QQ^2$ with $x+i y in QQ(i)$. Direct expansion gives
    $
      tau_r(v,w)=w/v.
    $
    Hence the ordered product around a closed path telescopes:
    $
      (v_2/v_1)(v_3/v_2) dots (v_1/v_n)=1.
    $

    In the bounded tetrahedral witness, the source path population through
    length four remains the same before and after moving one source height
    from $1$ to $1/4$. All receiver returns remain $(1,0)$. Nevertheless the
    source metric words, receiver turn words, and crossing subdivisions
    change. In particular, one precessed receiver initially presents
    $"AC" times "BD"$ at source parameters $21/47$ and $36/47$. Those common cuts
    also subdivide a direct receiver which sees no crossing. After the source
    emanation the crossing and both common cuts depart, although the direct
    receiver's complete projected chords remain equal.

    The exact path records are deposited in
    `observations/joint-decorated-path-atlas-01`.
  ],
  boundary: [
    $tau_r$ is an exact turn law for rational planar chord directions. It is
    not a general bundle connection or physical holonomy. Its product being
    one is a conservation-like closure identity, not positivity, path
    equivalence, compression, an RH theorem, or proof that the local turn
    word may be discarded.
  ],
)
