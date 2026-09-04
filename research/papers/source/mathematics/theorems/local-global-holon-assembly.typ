#let local-global-holon-assembly = (
  key: "theorem:local-global-holon-assembly",
  kind: [Theorem],
  title: [Every lawful global face is transported local assembly],
  status: [Exact consequence of the sheaf and naturality laws],
  depends: (
    "definition:receiver-indexed-holonic-system",
  ),
  claim: [
    Let $cal(O)$ be the observation sheaf of a receiver-indexed holonic system
    on a site $(cal(R),J)$, and let
    $
      {u_i:U_i arrow.r U}_(i in I)
    $
    be a $J$-cover of one boundary-defined region $U$.

    A face $s in cal(O)(U)$ determines the compatible local family
    $s_i=u_i^*s$. Conversely, every family $s_i in cal(O)(U_i)$ whose
    restrictions agree on every admitted overlap has one unique gluing
    $s in cal(O)(U)$. Therefore
    $
      "global over U"
      quad "iff" quad
      "compatible local sections transported across a cover of U".
    $

    If the compatibility data carries nontrivial return around an overlap
    cycle, no such section exists. That return is an obstruction resident in
    the covered local system, not evidence for an absolute exterior field.

    If a quantity $c_i:X|_(U_i) arrow.r C$ is natural under every admitted
    local evolution and the $c_i$ agree on overlaps, the glued
    $c:X|_U arrow.r C$ is an invariant over the complete contemporary region
    $U$. Thus global invariance emerges exactly when local standings transport
    across the whole declared region.
  ],
  proof: [
    Restriction of a section is compatible by functoriality of the presheaf.
    Existence and uniqueness of the converse gluing are the sheaf axiom.
    Naturality of the local invariant family and agreement on overlaps allow
    the same sheaf gluing in the arrow presheaf. A nontrivial overlap
    holonomy contradicts the equality required of restrictions of one
    section, so it obstructs a global gluing.
  ],
  boundary: [
    The theorem quantifies over a supplied cover of a supplied region. It
    neither postulates a greatest region nor identifies the total category of
    all fibers with one global state. A presheaf which is not a sheaf can
    retain compatible local testimony without admitting this assembly.
  ],
)
