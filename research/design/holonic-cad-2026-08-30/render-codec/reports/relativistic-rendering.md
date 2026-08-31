# Exact Rendering Mathematics for Special-Relativistic Visualization

Sources read in full: three papers from `$S/pdfs/`, the OpenRelativity tree at
`$S/refs/openrelativity` (HEAD `35b806a`), and the AJP paper documenting it (fetched to
`$S/pdfs/openrelativity-ajp-2016.pdf`). Notation: `β = v/c`, `γ = 1/√(1−β²)`, `θ` from the boost
direction, primes = observer frame.
**Sign trap, stated once:** every source writes aberration as `cos θ′ = (cos θ ∓ β)/(1 ∓ β cos θ)`;
the sign depends on whether `θ` is the *photon's propagation direction* or the *direction from
observer to source*. The two differ by `cos θ → −cos θ`, flipping both signs. Weiskopf's body text
and Jarabo use propagation; Weiskopf's appendix and OpenRelativity's shader use source-direction.

---

## 1. Sources

### 1.1 Weiskopf, Kobras, Ruder — *Real-World Relativity: Image-Based Special Relativistic Visualization*

IEEE Visualization 2000, pp. 303–310. Institute for Astronomy and Astrophysics, U. Tübingen.

**Model.** Image-based, refusing 3D modelling. The plenoptic function `P(x,y,z,t,θ,φ,λ)` reduces, per
snapshot, to `P̃(θ,φ,λ)` at the camera's event, which carries all the camera can register because "the
process of image generation is localized at the observer's position" and "there is no direct
interaction between the camera and the outside objects." The entire relativistic content is therefore
one Lorentz transformation *of the plenoptic function*, appended to an unmodified image-based
pipeline. Scene = a real 4π-steradian panorama filmed on a fork-arm DV rig; motion is *exocentric*.
No depth, no geometry, no retarded time.

**Aberration (Eqs. 1–2)**, `θ` = ray direction in `S`, `S′` moving with `v = βc` along `+z`:

```
cos θ′ = (cos θ − β) / (1 − β cos θ)              (1)
φ′ = φ                                            (2)
```

**Doppler (Eqs. 3–4)**, with `γ = 1/√(1−β²)`, `β = v/c`:

```
λ′ = D λ                                          (3)
D = 1 / (γ (1 − β cos θ)) = γ (1 + β cos θ′)      (4)
```

The two forms of `D` are identical given (1) — world-frame vs observer-frame angles.

**Searchlight — wavelength-dependent radiance (Eq. 5)**, derived in Weiskopf–Kraus–Ruder,
*ACM TOG* 18(3):278–292, 1999 ("the subscript λ is only attached to indicate wavelength dependency
of radiance; it is not a parameter"):

```
L′_λ(λ′, θ′, φ′) = D^(−5) L_λ(λ, θ, φ)            (5)
```

**Combined plenoptic transform (Eq. 6)** — the central result. The `+β` inside `arccos` is the
*inverse* aberration, because the renderer works backwards from an observer pixel to a world sample:

```
P̃′(θ′, φ′, λ′) = D^(−5) P̃( arccos( (cos θ′ + β)/(1 + β cos θ′) ), φ′, λ′/D )     (6)
```

**Solid-angle Jacobian (Eq. 7)**:

```
dΩ′/dΩ = (sin θ′ dθ′ dφ′)/(sin θ dθ dφ) = d(cos θ′)/d(cos θ) = D²    (7)
```

Hence magnification behind, shrinkage ahead, and anisotropic filtering by rectangular axis-aligned
(SAT-style) footprints, since aberration "can generate prolate, anisotropic, and distorted
footprints."

**Spectra.** Fully spectral: `L′_λ(λ′) = P̃′(θ′,φ′,λ′)`, then `c_i = ∫ L′_λ(λ′) f_λi(λ′) dλ′`,
`i = R,G,B`, `f_λi` the CIE colour-matching functions. From RGB the spectrum must be reconstructed,
non-uniquely (metamerism); they use the **dominant-wavelength model** — a spike at the dominant
wavelength plus a white pedestal, levels from luminance and excitation purity — with one relativistic
change: "the uniform part of the spectrum is not restricted to the range of visible wavelengths… the
spectrum is still present after Doppler-shifting."

**Boost and past light cone (Appendix A).** `x^μ = (ct,x,y,z)`; for `v = βc` along `+z`,

```
x^μ′ = ( γ(ct − βz), x, y, γ(z − βct) )           (8)
```

A point source's emission event lies on the observer's past cone, so its time component is fixed by
light travel time:

```
x^μ_E = ( −√(x_E²+y_E²+z_E²), x_E, y_E, z_E )
      = ( −r_E, r_E cos φ_E sin θ_E, r_E sin φ_E sin θ_E, r_E cos θ_E )      (9)
```

Applying (8) gives `x^μ_E′ = ( −γ(r_E + β z_E), x_E, y_E, γ(z_E + β r_E) )`, hence
`r_E′ = γ(r_E + β z_E)` and aberration in *source-direction* convention:

```
cos θ′ = (cos θ + β) / (1 + β cos θ)        (10)
φ′ = φ                                      (11)
```

This is the form an implementation wants (retarded position → apparent direction), and exactly the
map OpenRelativity realizes implicitly.

**Visibility invariance** (A.3): `x^μ_{E2} = a x^μ_{E1}` (`a>1`) in `S_obj` implies
`x^μ_{E2}′ = a x^μ_{E1}′` — occlusion is Lorentz-invariant, so a world-frame z-buffer is valid in the
camera frame.

**Terrell–Penrose** (A.4, qualitative, no angle formula): "In the exocentric view, the observer is
already behind the object and can thus see its back. However… the object seems to still be ahead
because of the aberration of the incoming light." The quantitative content is a corollary of (10):
the map is a Möbius transformation of the celestial sphere, hence conformal (circles→circles, so
spheres stay spherical); a small object at world-frame angle `θ` appears rotated by `α = θ′ − θ`, and
at `θ = 90°`, `cos θ′ = β`, giving **`α = arcsin β`**.

### 1.2 Savage, Searle, McCalman — *Real Time Relativity*

ANU, arXiv `physics/0607223` (2006); PDF metadata `Physicist-RTR.doc` — the *Australian Physicist*
write-up. Peer-reviewed companion: *AJP* 75, 791 (2007).

**Model.** Ray-direction-based, entirely in the pixel shader. The static world is rendered by the GPU
into a **world-frame cube map** — "a data structure in which the image pixels are addressed by line
of sight direction, rather than by spatial position." Per screen pixel the camera-frame photon
4-vector is boosted into the world frame; its spatial part addresses the cube-map texel. With a
static world no retarded-time solve exists: the light-cone problem collapses into the direction map.
DirectX 9 / HLSL, ~24 million Lorentz transforms/sec.

Photon 4-vector, `h` Planck's constant, `f` frequency, `n̂` unit propagation 3-vector:

```
P = h f (1, n̂) / c
P_W = L P_C
```

"A 4×4 matrix represents the Lorentz transformation `L`. It is calculated before each frame is
rendered, using the current camera velocity… The spatial parts of these vectors address the cube map
pixel." The aberration formula is never written: aberration *is* the spatial part of the boosted null
4-vector, renormalized. Doppler likewise needs none — "The Doppler shift of the photon frequency is
given by the **ratio of the time components** of the photon energy-momentum 4-vector,"
`f_C/f_W = P⁰_C/P⁰_W`.

Searchlight: "aberration concentrates the incident light into a narrow cone centred on the direction
of motion. In addition, time dilation increases the photon flux in the camera frame… **The detected
intensity scales as the fourth power of the Doppler shift**" (McKinley, *AJP* 47, 602, 1979). With
"Doppler shift" = `f_C/f_W = 1/D`, this is `I ∝ D^(−4)`: the **integrated** radiance law (§3.1).

Colour is flagged as defective: "the spectrum is specified at just three frequencies; red, green, and
blue. Hence a simple interpolation is used… This simple approach is a significant limitation."
Pipeline order: user input → GPU renders the world into a world-frame cube map → GPU Lorentz
transforms into the camera frame → display.

### 1.3 Jarabo, Masia, Velten, Barsi, Raskar, Gutierrez — *Rendering Relativistic Effects in Transient Imaging*

CEIG — Spanish Computer Graphics Conference 2013, pp. 1–9. U. Zaragoza / MIT Media Lab.

**Model.** The only source where the scene's own illumination varies at light-transport time scale.
Input is femto-photography (streak camera, exposure < 2 ps, giving an `x-y-t` cube) or a transient
path tracer. An image-based renderer projects `x-y` slices onto reconstructed geometry, stores the
cube as a GPU 3D texture in *world* time, and per frame re-warps it into the camera's time;
relativistic transforms are applied per vertex on re-tessellated geometry. Stated contribution:
lifting the constant-irradiance and purely-translational assumptions of prior work.

**Time-resolved rendering equation (Eq. 1)**, `x` shaded point, `n` normal, `ω_i`/`ω_o` in/out
directions, `L_e` emitted radiance, `ρ` the BRDF, `Ω+` the hemisphere about `n`:

```
L(x, ω_o, t) = L_e(x, ω_o, t) + ∫_{Ω+} L_i(x, ω_i, t) ρ(x, ω_i, ω_o) (−ω_i · n) dω_i     (1)
```

**The propagation delay is not written into Eq. (1)**; it lives in the prose: "computed by Montecarlo
ray tracing, taking into account the distance traveled by a ray from its origin to the next
intersection, as well as the index of refraction `η` of the medium. This affects the speed of light
`v` in the medium according to the equation `v = c/η`." The term the solver implements is
`L_i(x,ω_i,t) = L(x_M, −ω_i, t − ‖x−x_M‖·η/c)`.

**"Camera receives at time t" (Eq. 2)** — the past-cone condition for a pinhole sensor with per-pixel
depth `z_ij`, `t′` camera time, `t` world time:

```
t′_ij = t_ij + z_ij / (c/η)                       (2)
```

Every frame re-warps the original data because "the distance from each geometry point to the center
of projection of the camera varies for each frame."

**Combined relativistic transform (Eq. 3)** (`O′` = sensor, `v = βc` w.r.t. `O`, `β ∈ [0..±1)`) —
Weiskopf Eq. (6) verbatim, with `D` in observer-frame form:

```
L′(θ′, φ′, λ′) = D^(−5) L( arccos( (cos θ′ + β)/(1 + β cos θ′) ), φ′, λ′/D )     (3)
D = γ(1 + β cos θ′),   γ = 1/√(1 − β²)
```

**Components.** Time dilation `Δt′ = γΔt`, glossed "making time in the stationary frame (the world)
advance faster than in the moving frame (the camera)" — *as printed this contradicts their own
prime = camera convention; the intended relation is `Δt_world = γ Δt_camera`.* Aberration
(propagation convention):

```
cos θ′ = (cos θ − β)/(1 − β cos θ)      (4)        φ′ = φ      (5)
λ′ = D λ                                (6)
L′(θ′, φ′, λ′) = D^(−5) L(θ, φ, λ)      (7)
```

Two transient consequences, unique to this paper: "the frame rate of the time-varying irradiance `f`
in world frame is Doppler shifted, making the perceived frame rate `f′` in camera frame become
**`f′ = f/D`**", and "irradiance from several frames in world time interval `dt` is integrated over
the same camera differential time `dt′`, such that **`dt = dt′/D`**. Note that the `D^(−5)` factor
only is valid for the case in which the directions of the velocity vector `v` and the normal to the
detector are parallel." — the clause that forces their rotation hack.

**Relativistic rotation** (their claimed first): "there is no universally accepted theory of
relativistic rotation." Approximation — limit rotation to very small angles per frame; the finite
sensor's differential surfaces then move at different speeds, so "it creates a continuous linear
velocity field `Ψ` on the sensor, with a zero-crossing at the axis of rotation." Divide `S` into
regions `s` with velocity `ψ_s` — this "effectively turns each of them into a different translational
frame" — and apply Eq. (3) per region with its own `β_s`.

**Implementation.** OpenGL. Geometry **re-tessellated offline on the CPU** because aberration curves
straight lines; image-space warping is rejected on disocclusion grounds. Doppler by one laser
wavelength through a 1D wavelength→RGB texture. Searchlight by **pre-integrating irradiance in the
temporal domain and using anisotropic mipmapping, with `dt` selecting the mipmap level in the time
dimension**.

### 1.4 OpenRelativity — MIT Game Lab

Repo `github.com/MITGameLab/OpenRelativity` (MIT License). Documented in Sherin, Cheu, Tan,
Kortemeyer, "Visualizing relativity: The OpenRelativity project," *AJP* **84**(5), 369–374 (2016),
doi 10.1119/1.4938057.

**Model.** Geometry-based, per-vertex, and the only source that genuinely solves the past light cone
for moving world-lines. The player is pinned at the origin of camera frame `C`: "instead of moving
the player, we are moving the world-frame `W` underneath the player — the world literally revolves
around the player." Per frame: rotate axes so the boost is `+z`; intersect each vertex's world-line
(constant velocity, straight, infinite) with the past cone by a quadratic; boost the retarded
position into `C`; let Unity's projection rasterize. Aberration is never coded — it *emerges* from
the boost.

**Operation order (AJP Eqs. 1–8).** Time dilation, per-step axis realignment, then a world update
keeping the camera at the origin:

```
Δt_W = Δt_C / √(1 − v²_{C,W}/c²)                  (1)
ṽ_{C,W} → R̃ ṽ_{C,W}   (now in z)   (2)      ṽ_{i,W} → R̃ ṽ_{i,W}   (3)      r̃_{i,W} → R̃ r̃_{i,W}   (4)
r̃_{i,W} → r̃_{i,W} + (ṽ_{i,W} − ṽ_{C,W}) Δt_W     (5)
```

**Past-light-cone quadratic** — "the invariant four-distance needs to be light-like, and due to the
invariance we can calculate it in the `W`-frame":

```
c² t²_{i,S,W} = r̃²_{i,S,W} = (r̃_{i,W} + ṽ_{i,W} t_{i,S,W})²        (6)
r̃_{i,S,W} = r̃_{i,W} + ṽ_{i,W} t_{i,S,W}                            (7)
r̃_{i,S,C} = Λ(ṽ_{C,W}) r̃_{i,S,W}                                   (8)
```

"the time `t_{i,S,W}` can be calculated analytically using the quadratic equation. We will get two
solutions, and **we need to choose the past one**." For (8): "we can use the standard configuration
for `Λ` with the boost in the z-direction, having the `C` and `W` origins at same position at
`t = 0`."

**The quadratic as written**, verbatim from
`$S/refs/openrelativity/Assets/OpenRelativity/Shaders/relativity.shader` (vertex shader, 176–201):

```hlsl
float c = -(riw.x*riw.x + riw.y*riw.y + riw.z*riw.z); //first get position squared (position doted with position)

float b = -(2 * ( riw.x*rotateViw.x + riw.y*rotateViw.y + riw.z*rotateViw.z)); //next get position doted with velocity, should be only in the Z direction

float d = (_spdOfLight*_spdOfLight) - (rotateViw.x*rotateViw.x + rotateViw.y*rotateViw.y + rotateViw.z*rotateViw.z);

float tisw = (float)(((-b - (sqrt((b * b) - ((float)float(4)) * d * c))) / (((float)float(2)) * d)));

//Check to make sure that objects that have velocity do not appear before they were created
if (_wrldTime + tisw > _strtTime || _strtTime==0) { o.draw = 1; } else { o.draw = 0; }

//get the new position offset, based on the new time we just found
riw.x += rotateViw.x * tisw;   riw.y += rotateViw.y * tisw;   riw.z += rotateViw.z * tisw;
```

This solves `(c² − |v|²)t² − 2(r·v)t − |r|² = 0`, i.e. Eq. (6); the `(−b − √(b²−4dc))/(2d)` branch
selects the **negative** (retarded) root, reducing to `t_isw = −|r|/c` for a static vertex.
`_strtTime`/`deathTime` gate visibility when the cone hit falls outside the object's lifetime;
`RelativisticObject.cs` duplicates the same quadratic on the CPU.

**The boost** (lines 206–219), followed by the inverse axis rotation:

```hlsl
float newz = (((float)speed*_spdOfLight) * tisw);
newz = riw.z + newz;
newz /= (float)sqrt(1 - (speed*speed));
riw.z = newz;
```

The realigning rotation uses `a = -acos(-_vpc.z/speed)` about axis `(_vpc.y, −_vpc.x, 0)`, with
`_vpc` set C#-side as `SetGlobalVector("_vpc", new Vector4(-playerVelocityVector.x,…)/(float)c)`.
Net effect on a **static** vertex at relative position `r`, `R = |r|`, `r_∥` along the boost:

```
r′_⊥ = r_⊥ ,   r′_∥ = γ(r_∥ + βR)   ⇒   |r′| = γ(R + β r_∥)   ⇒   cos θ′ = (cos θ + β)/(1 + β cos θ)
```

— Weiskopf's appendix Eq. (10). **This is OpenRelativity's aberration: never coded, it is the boost
of the retarded position.** Order: *rotate → advance world → solve light cone → boost → un-rotate →
project*, with `UnityObjectToClipPos` supplying direction→pixel.

**Doppler** (fragment shader, 333–338):

```hlsl
float x1 = i.pos2.x * 2*xs;   float y1 = i.pos2.y * 2*xs/xyr;   float z1 = i.pos2.z;

// ( 1 - (v/c)cos(theta) ) / sqrt ( 1 - (v/c)^2 )
float shift = (1-((x1*i.vr.x + y1*i.vr.y + z1*i.vr.z)/sqrt( x1 * x1 + y1 * y1 + z1 * z1)))/i.svc;
```

`i.svc = sqrt(1-speedr*speedr)` is cached from the vertex stage; `i.vr` is the relativistically
composed relative velocity `(_vpc − u_∥ − √(1−β²)u_⊥)/(1 + v·u)`; `i.pos2` is the *already boosted*
position, so `shift = γ_r(1 − β_r·r̂′)`. AJP Eqs. 9–10:

```
D = (1 − (v/c) cos θ) / √(1 − (v/c)²)      (9)          λ_C = D λ_W      (10)
```

The AJP text calls `θ` "the angle between the velocities of the source and the observer," wrong as
written: the code uses the angle between the relative velocity and the *aberrated* line of sight,
making `D` identical to Weiskopf's `γ(1 + β cos θ′)`.

**Searchlight** (lines 366–368, `yf`/`zf` identical):

```hlsl
float xf = pow((1/shift),3)*(getXFromCurve(rParam, shift) + getXFromCurve(gParam,shift) + getXFromCurve(bParam,shift) + getXFromCurve(IRParam,shift) + getXFromCurve(UVParam,shift));
```

AJP: "this effect decreases the frequency-dependent luminosity by a factor of `1/D³`."

**RGB approximation.** `RGBToXYZC` → `weightFromXYZCurves` yields three weights; the source spectrum
is five Gaussian lines — R 615 nm (σ 8), G 550 nm (σ 4), B 463 nm (σ 5), IR at `700+400·IR`, UV at
`0+380·UV` (amplitude 0.02, σ 5, from greyscale textures). Doppler multiplies **both centre and
width** by `shift`. `getXFromCurve` etc. are closed-form Gaussian-overlap integrals against Gaussian
fits to CIE `x̄ȳz̄` (`x̄` needs two lobes): `top/bottom` is exactly
`A√(2π)(σ₁σ₂/√(σ₁²+σ₂²))exp(−(μ₁−μ₂)²/(2(σ₁²+σ₂²)))`. Then `XYZToRGBC` + `constrainRGB`.
`skybox.shader` runs Doppler + searchlight **only** — no aberration, no contraction — hence the
mandated solid-colour skybox.

---

## 2. Consolidated pseudocode: receiver-relative rendering on a lattice, `c = 1`

Integer lattice, signal speed `c = 1` lattice unit per tick. Receiver at `r_cam` with velocity `β`,
`γ = 1/√(1−β·β)`. A vertex has world-line `x(t) = x₀ + u(t−t₀)`, constant `u`; "now" is tick `T`.
Plain JavaScript, no libraries. *(Verified numerically: identities agree to ~1e-15, and step 1
reproduces the shader's `tisw` exactly.)*

```js
// ---------- 0. helpers ----------
const sub=(a,b)=>[a[0]-b[0],a[1]-b[1],a[2]-b[2]];
const add=(a,b)=>[a[0]+b[0],a[1]+b[1],a[2]+b[2]];
const mul=(a,s)=>[a[0]*s,a[1]*s,a[2]*s];
const dot=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2];

// ---------- 1. RETARDED EVENT on the receiver's past light cone ----------
// Solve |r + u t|^2 = t^2 with c = 1  =>  (1 - u.u) t^2 - 2 (r.u) t - r.r = 0
function retarded(posNow, u, camPos) {
  const r = sub(posNow, camPos);                // world-frame offset at tick T
  const A = 1 - dot(u, u), B = -2*dot(r, u), C = -dot(r, r);
  const disc = B*B - 4*A*C;                     // = 4[(r.u)^2 + (1-|u|^2) r.r] >= 0
  const t = (-B - Math.sqrt(disc)) / (2*A);     // PAST root: t <= 0
  return { t, rRet: add(r, mul(u, t)), n: -t }; // n = |rRet| = -t EXACTLY, since c = 1
}

// ---------- 2. ABERRATED DIRECTION ----------
// Boost the retarded (null) offset; only the component parallel to beta changes.
// Scalar equivalent: cos th' = (cos th + beta)/(1 + beta cos th), phi' = phi, th measured from
// beta to the DIRECTION OF THE SOURCE. Inverse map is beta -> -beta.
function aberrate(rRet, n, beta, gamma) {
  const b2 = dot(beta, beta);
  if (b2 === 0) return rRet.slice();
  const bhat = mul(beta, 1/Math.sqrt(b2));
  const rPar = dot(rRet, bhat);
  const rPerp = sub(rRet, mul(bhat, rPar));
  return add(rPerp, mul(bhat, gamma * (rPar + Math.sqrt(b2) * n)));   // |r'| = gamma(n + beta.rRet)
}

// ---------- 3. DOPPLER FACTOR and SEARCHLIGHT WEIGHT ----------
// D = lambda_obs/lambda_emit = n/(gamma (n + beta.rRet)) = gamma(1 - beta.rHat')
function doppler(rRet, n, beta, gamma) { return n / (gamma * (n + dot(beta, rRet))); }

// Exponent must match the radiometric quantity carried. Solid angle: dOmega'/dOmega = D^2.
const searchlight = (D, mode) =>
  mode === 'perWavelength' ? Math.pow(D,-5)   // Weiskopf Eq.5, Jarabo Eq.7
: mode === 'perFrequency'  ? Math.pow(D,-3)   // L_nu/nu^3 invariant; OpenRelativity/AJP
:                            Math.pow(D,-4);  // band-integrated; RTR "fourth power"
// Time-resolved sources (Jarabo): lambda' = D*lambda ; f' = f/D ; dt = dt'/D.

// ---------- 4. SCREEN COORDINATE ----------  (basis orthonormal, in the RECEIVER frame;
//                                               f = (W/2)/tan(hfov/2) in pixels)
function project(rPrime, right, up, fwd, f, W, H) {
  const z = dot(rPrime, fwd);
  if (z <= 0) return null;                      // behind the receiver
  return { x: W/2 + f*dot(rPrime,right)/z, y: H/2 - f*dot(rPrime,up)/z, depth: z };
}

// ---------- 5. WHOLE PIPELINE, one vertex ----------
function renderVertex(v, cam, cfg) {
  const {t, rRet, n} = retarded(v.posAtT, v.vel, cam.pos);
  if (t + cam.tick < v.tBorn || t + cam.tick > v.tDies) return null;   // light-cone gating
  const g = 1 / Math.sqrt(1 - dot(cam.beta, cam.beta));
  const rP = aberrate(rRet, n, cam.beta, g);
  const D  = doppler(rRet, n, cam.beta, g);
  const px = project(rP, cam.right, cam.up, cam.fwd, cfg.f, cfg.W, cfg.H);
  return px && { px, D, weight: searchlight(D, cfg.radiometry), retardedTick: cam.tick + t };
}
```

Two notes. (a) Step 1 is skippable *only* for a static, time-invariant scene — the exemption Weiskopf
and RTR take. (b) Steps 2–4 are a nonlinear map; per-vertex evaluation with linear interpolation
turns straight edges into polylines, which is why OpenRelativity (`ObjectMeshDensity.cs`) and Jarabo
subdivide meshes.

### 2.1 Which steps are exact under rational inputs

Assume integer lattice positions, rational velocities, rational camera basis.

- **`γ` is rational** iff `1 − β·β` is a rational square — a "Pythagorean speed". Axis-aligned
  `β = p/q` needs `q²−p²` square: `3/5, 4/5, 5/13, 12/13, 8/17, 7/25, 24/25, 20/29, 40/41, …`.
  Otherwise `γ` is the first floating face.
- **The light-cone root is the one genuine irrationality.** `t = [(r·u) − √Δ]/(1 − u·u)` with
  `Δ = (r·u)² + (1−u·u)(r·r)`, an integer after clearing denominators. `t ∈ ℚ(√Δ)`, rational only
  when `Δ` is a perfect square. **The retarded tick is an integer** exactly when `Δ` is a perfect
  square and the division closes; for a *static* vertex `Δ = r·r`, so the tick is integral iff `r·r`
  is a perfect square — a Pythagorean lattice point relative to the receiver. Checked: `r = (3,4,12)`
  gives `t = −13` exactly; `r = (1,1,1)` gives `−√3`.
- **Everything downstream stays in that single quadratic field `ℚ(√Δ)`.** Because `n = −t`, no second
  square root is introduced: `rRet ∈ ℚ(√Δ)³`, `|r′| = γ(n + β·rRet) ∈ ℚ(√Δ)`,
  `D = n/(γ(n + β·rRet)) ∈ ℚ(√Δ)`, `r′ ∈ ℚ(√Δ)³`, `f(r′·right)/(r′·fwd) ∈ ℚ(√Δ)`. All representable
  as pairs `(a,b)` meaning `a + b√Δ`; comparisons against rationals (pixel bins, depth tests, clip
  planes) are exact by sign-of-`a` plus one squaring. **So the retarded event, the aberration, the
  Doppler factor and the screen coordinate are all exact in a degree-2 extension of ℚ, per vertex,
  with `√Δ` the only algebraic irrationality.** Integer-power searchlight weights stay in the field.
- **Floating faces, unavoidable:** (i) `√Δ` as a decimal, though not as an algebraic object; (ii) `γ`
  for non-Pythagorean receiver speeds; (iii) velocity composition for non-Pythagorean object speeds;
  (iv) camera orientation unless the basis comes from rational rotations (Cayley transform of a
  rational skew matrix) rather than `sin/cos`; (v) **all spectral work** — Gaussians, CIE integrals,
  wavelength→RGB, tone mapping are transcendental and float regardless of geometric exactness;
  (vi) per-vertex linear interpolation across a triangle, an approximation of a nonlinear map rather
  than a rounding error.

---

## 3. What each source deliberately omits, and where they disagree

### 3.1 The searchlight exponent: an apparent three-way disagreement that reconciles

| Source | Written law | Applies to |
|---|---|---|
| Weiskopf Eq. 5, Jarabo Eq. 7 | `L′_λ = D^(−5) L_λ` | spectral radiance **per wavelength** |
| OpenRelativity / AJP | "decreases the frequency-dependent luminosity by a factor of `1/D³`" | spectral radiance **per frequency** |
| RTR | "intensity scales as the fourth power of the Doppler shift" | **band-integrated** radiance (`ν′/ν = 1/D`) |

All three are one law: `L_ν/ν³` is Lorentz-invariant, so `ν′ = ν/D` ⇒ `L′_ν = D^(−3)L_ν`;
`dν′ = dν/D` ⇒ `L′ = D^(−4)L`; and `L_λ = L_ν c/λ²`, `λ′ = Dλ` ⇒ `L′_λ = D^(−5)L_λ`.

**But OpenRelativity's implementation lands on none of them.** The shader models the spectrum as
Gaussians in **wavelength**, scales centre *and* width by `shift` (so the modelled density's integral
grows by `D`), then multiplies the tristimulus by `D^(−3)`. Net integrated-radiance law implemented:
`D^(−2)`, not the exact `D^(−4)`. The AJP prose correctly names the `L_ν` form; the code applies that
exponent to a `λ`-parametrized density. This residual `D²` is the most consequential numerical
discrepancy among the four sources.

### 3.2 Whether the past light cone is solved at all

- **Weiskopf: deliberately not.** A dynamic scene "would use images which are instantaneously
  transported from the object to the camera, instead of the correct, retarded images which take into
  account the reduced speed of light." He restricts to a static world, where aberration alone
  suffices: "The aberration of light is sufficient to completely describe the apparent geometry."
- **RTR: deliberately not.** "limited to static worlds in which the objects do not move." AJP reads
  this as the problem RTR ducked: "the significant challenges encountered when trying to trace the
  history of an object to find out when it would have emitted photons that are momentarily visible."
- **OpenRelativity: yes**, per vertex per frame, but only for straight infinite world-lines: "our
  engine is limited to *calculating* rather than *remembering* the location of objects in the past.
  For performance reasons, this is only implemented along straight trajectories."
- **Jarabo: yes**, but as a *data* operation (Eq. 2, per-pixel depth time-unwarp), not a world-line
  intersection — his geometry is static and the *illumination* moves.

### 3.3 Where the transform sits in the pipeline

Weiskopf and RTR put it at the **end** (image-based, per-pixel): cost independent of scene
complexity, no re-tessellation, pipeline "otherwise left unchanged." OpenRelativity and Jarabo put it
at the **front** (per-vertex): buys moving objects and correct dynamic occlusion, but forces mesh
subdivision and renders straight lines as polylines. Jarabo rejects image-space warping on
disocclusion grounds; Weiskopf rejects geometry-based rendering on photorealism and cost grounds.

### 3.4 Constant irradiance

Jarabo against Weiskopf: "the authors assume light incoming from infinitely far away light sources
with constant radiance, so both the effects of distance and time-varying irradiance are ignored…
which no longer hold in the context of time-resolved data." He adds `f′ = f/D`, `dt = dt′/D` and the
world/camera `Δt` split, and asserts the same gap in OpenRelativity: "to our knowledge, they do not
deal with time-varying irradiance either."

### 3.5 Rotation and acceleration

Weiskopf handles arbitrary boost directions by pre/post Euclidean rotations and acceleration by
discretizing the trajectory — legitimate because "the generation of a single image is only determined
by the position and velocity of the viewer… not by the 'history' of the trajectory or the
acceleration." OpenRelativity does the same (momentarily-comoving inertial frame; velocities composed
relativistically, capping speed below `c`). Jarabo alone treats a *rotating sensor*. Nobody models
Thomas–Wigner precession.

### 3.6 Terrell–Penrose

Weiskopf: qualitative only (§A.4). AJP: asserted as known — "spheres always appear spherical,
regardless of relative speed (however, surface textures appear to stretch around the spherical
shape)" — but never derived. RTR and Jarabo: not mentioned. **No source here writes a Terrell rotation
angle.** It is a corollary of their shared aberration map, a Möbius transformation of the celestial
sphere and therefore conformal; the transverse angle is `arcsin β`.

### 3.7 Colour

Spectral fidelity descends monotonically: Weiskopf (full spectrum, else dominant-wavelength
reconstruction) → OpenRelativity (five Gaussians R/G/B/IR/UV, because the alternative "would have
been to store the full emission spectrum for every vertex in the scene") → RTR (three frequencies
plus interpolation, "a significant limitation") → Jarabo (one laser wavelength via a LUT).

### 3.8 Everything else nobody models

**Lighting and shadows** — OpenRelativity: "all shadows depicted must be permanent… A fully
relativistic, dynamic treatment of lighting and shadows is possible but would greatly add to the
complexity." Jarabo: Lambertian only, disoccluded surfaces "we simply render them black."
**Polarization** — Weiskopf: "neglected because it is not registered by standard cameras"; nobody
else mentions it. **Gravity** — "Gravity is not modeled in the game"; none of the four is
general-relativistic. **Non-inertial third parties** — OpenRelativity requires constant straight
world-lines from `−∞` to `+∞`; RTR forbids moving objects; Weiskopf requires a static world.
**Other frames** — OpenRelativity: "the player only functions in first-person view; the scene cannot
be viewed from any other reference frame." **Backgrounds** — OpenRelativity's skybox gets no
aberration, forcing a solid colour; Weiskopf's entire scene *is* the sky, so his aberration handles
it natively — the exact inverse trade. **Egocentric vs exocentric** — Weiskopf argues for exocentric
because "it is closer to physics to transform the photons which have reached the observer than to
transform emission events far away from the camera"; OpenRelativity does the opposite, which his
Appendix A proves equivalent for apparent geometry.
