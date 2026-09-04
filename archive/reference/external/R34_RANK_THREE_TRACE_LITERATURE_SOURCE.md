# R34 exterior literature source

`truth_status=proved-standard`

William M. Goldman, *Trace Coordinates on Fricke Spaces of Some Simple
Hyperbolic Surfaces*, Handbook of Teichmüller Theory II (2009),
[arXiv:0901.1404](https://arxiv.org/abs/0901.1404), describes the
`SL(2,C)` character ring of the rank-three free group. With

```text
x1=tr(A), x2=tr(B), x3=tr(C),
x12=tr(AB), x13=tr(AC), x23=tr(BC),
x123=tr(ABC), x132=tr(ACB),
```

the introduction and Section 5.1 give the two triple-trace relations

```text
x123 + x132 = x12*x3 + x13*x2 + x23*x1 - x1*x2*x3
x123*x132 = x1^2+x2^2+x3^2+x12^2+x13^2+x23^2
               -x1*x2*x12-x1*x3*x13-x2*x3*x23+x12*x23*x13-4.
```

The paper states that the two triple traces are the roots of a monic quadratic
over the six lower traces and that the rank-three character variety is a
double branched cover of six-dimensional affine trace space. These names and relations
were unavailable to the sealed R34 executables.

Source locator: PDF pages 5 and 58--60 (document pages 4 and 57--59), especially
the displayed sum relation (5.1.1), product relation (5.1.2), and the resulting
quadratic/hypersurface discussion.
