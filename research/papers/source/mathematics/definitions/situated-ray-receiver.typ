#let situated-ray-receiver = (
  key: "definition:situated-ray-receiver",
  kind: [Definition],
  title: [Situated ray receiver of an implicit geometry],
  status: [Classical ray intersection; receiver-relative formulation],
  depends: (
    "definition:receiver",
    "definition:comparison-face",
  ),
  claim: [
    Let an intrinsic real affine face be given by
    $
      X_F={x in RR^n:F(x)=0}.
    $
    A ray receiver is the declared tuple
    $
      R=(o,d,I,chi,L),
    $
    where $o$ is its source, $d$ its oriented direction, $I$ the admissible
    parameter interval, $chi$ its root-selection and occlusion law, and $L$
    its lighting or measurement law.  It observes roots of
    $
      F(o+t d)=0,
      quad t in I,
    $
    selects a visible occurrence $t_R$ through $chi$, and may evaluate the
    regular normal $nabla F(o+t_R d)$.  The rendered face is therefore
    $
      Pi_R(X_F)=L(o,d,t_R,nabla F(o+t_R d),dots),
    $
    whenever these terms exist.
  ],
  proof: none,
  boundary: [
    $Pi_R(X_F)$ is not the whole intrinsic geometry.  It depends on an affine
    chart, a real slice, source, direction, root selection, occlusion, and
    measurement law.  At a singular occurrence
    $F=0$ and $nabla F=0$ the regular normal is unavailable; the singularity belongs
    to the intrinsic discriminant rather than being a shading defect.
  ],
)
