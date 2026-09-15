#import "../../holonics/computational-holon.typ": *
#let eq(m)=block(width:100%,above:2mm,below:2mm,align(center,math.equation(m.body,block:true)))
#let fig(name,height)=align(center,image("../../../../experiments/athena_engine_blueprint/"+name+".svg",width:285mm,height:height,fit:"contain"))
#pagebreak()
#chemistry-title("14","Athena executes one constituted HNN model","The field operator, its learned material and receiving charts belong to the same engine construction.")
#fig("network",112mm)
#eq(holon-generation-equation)
#eq(scattering-equation)
#chemistry-note([*Assembly contract.* `NativeCoupledBody` must own and execute the operative `NativeConstitutiveField` path, compose its local learned reaction, and expose the joint boundary through the requested receiver. The dashed join is this concrete application attachment. The linked tori show shared circulating support; their pictured count is not a prescribed native architecture. Source: `docs/ATHENA_ENGINE_BLUEPRINT.md`.])
#v(2mm)#chemistry-note([Established-bounded · source-inspected: the field scattering, material response and coupled-wave owners exist. The direct field-backed public body assembly is specified here; it is not claimed to have been completed by this diagram.])

#pagebreak()
#chemistry-title("15","Learning reaches the material that generated the field","A whole generated section supplies a receiving difference; the complete adjoint returns to its producing currents and contacts.")
#fig("training",98mm)
#eq(scattering-adjoint-equation)
#eq[$g_u=2lambda-g_w, quad g_("in")=2D^*lambda-g_b, quad Theta^+=cal(R)_Theta(Theta,G_Theta)$]
#grid(columns:(1fr,1fr),gutter:12mm,
 chemistry-note([*Existing direct learning operation.* `respond_to_material_observation` selects the actual producing/receiving cut, forms the current or normalized covector, invokes `material_contact_response`, and commits with `apply_material_contact_realization`. The finite material change recomputes its mixed terms. Its declared metric/update law is separate from any claim of global loss convergence.]),
 chemistry-note([*The next model application.* Generate a joint section from partial boundary data; compare it to an actual external target; update this same D/Θ; inspect the next generated section. Existing conditional/normal learning is a local constituent. Fitting another predictor to this field's outputs would be a different application, not this assembly.]),
)
#v(2mm)#chemistry-note([Proved-derived for the displayed adjoint in the declared real pairing of complex currents; implemented-exact local owners in `field/junction/producer.rs` and `operative/response`. The blueprint joins them to Athena's model invocation. Mode reuse retains the actual interior and pending comparison through `E_next T=U E` and `D_dec E=rho`.])

#pagebreak()
#chemistry-title("16","The half-centred face retains transverse and complex motion","The critical line is the fixed locus of reflection; its paired currents supply a quantitative upper-bound construction.")
#fig("centered-quartet",77mm)
#eq(centered-face-equation)
#eq[$2 Re(1/(s-s^dagger))=1/d, quad 2 Re(1/(s-(1-s)))=d/(d^2+y^2)$]
#eq(transverse-current-equation)
#grid(columns:(1fr,1fr),gutter:12mm,
 chemistry-note([*Source and sign.* In the repository's seam clock, $G_tau=op("heatE")(-tau,xi)$ and $partial_tau G=G_(s s)$, so a simple zero moves with $v=-G_(s s)/G_s$. The same-height partner contributes the inward term $-1/d$. The remaining divisor current $J_R$ and its finite tail $epsilon_R$ must be retained. The quartet is a general symmetry orbit, not a claimed off-line zero of xi.]),
 chemistry-note([*What sharpens the bound.* If the actual source family supplies $d(J_R-epsilon_R)gt.eq a gt.eq 0$, the squared-width inequality excludes a positive transverse trajectory beyond its stated clock. The repository already has a finite Foster tail estimate; the new source binding uses it. A uniform all-height comparison is still required for a stronger global threshold. $Lambda_("std")=4Lambda_("DN")$; the half-centre itself is not an upper-bound proof.]),
)
#v(2mm)#chemistry-note([Proved-derived · formal-checked at the explicit local/source hypotheses: `RH/TransverseCurrentBound`, `RH/FiniteZeroCurrent`, `RH/CriticalChart`. These analytic constructions and the HNN engine develop in parallel; no Millennium endpoint is an admission condition for training.])
