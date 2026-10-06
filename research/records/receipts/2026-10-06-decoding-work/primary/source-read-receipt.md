# Thermodynamics primary-source recovery receipt

Date: 2026-10-06 UTC
Scope: bounded recovery of Bennett, arXiv cond-mat/0212499, and Reeb & Wolf, arXiv:1306.4352, for the non-biological geometry/compression/medium lane.

## Network attempts and source status

- Requested Bennett source URL attempted: https://arxiv.org/pdf/cond-mat/0212499
- Requested Reeb–Wolf source URL attempted: https://arxiv.org/pdf/1306.4352
- Both `curl` invocations used `--max-time 20`, `--max-filesize 8388608`, one process/thread, and ended immediately with `curl: (6) Could not resolve host: arxiv.org` (exit 6; measured wall time reported ~0.00002 s). The two unchanged URLs were not retried.
- No source PDF or extracted text was obtained. Neither paper was read; no page/section claims can be attributed to either paper. Source hashes: not available (no file received). The supplied identifiers/title descriptions were not independently verified, so their metadata remains unverified in this receipt.
- A local `rg --files` search found no local copies named for either identifier or author. The repository does contain secondary research records citing Landauer (listed below), but these are not substitutes for either requested primary paper.

## Existing local owner facts (read from the named owners; not attributed to the unread papers)

- `lean/Holonics/Physics/Information/PortWork.lean` states its actual assumptions and protocol: finite nonempty energy-level set; port scale `θ = k_B T`; canonical Gibbs state `exp(−Eᵢ/θ)/Z`; freeze population while shifting levels `E → E+δ` (work), relax at shifted levels (heat by fixed-level energy balance), then restore levels quasi-statically. The proved production is `D(p‖q′) ≥ 0`; extracted work is free-energy drop minus `θ D(p‖q′)`. For the matched shift `δᵢ = θ log(qᵢ/pᵢ)`, relaxation production is zero and the full free-energy drop is extracted. The owner says its phase component is not consumed by this thermal port.
- `lean/Holonics/Physics/Thermal/Exchange.lean` specifies its separate physical medium: two cells with `U = C T`, `C₁,C₂ > 0`; contact heat `q = h κ (T₁−T₂)` for `κ ≥ 0`; cell entropy `S=C log U` up to a unit-chart constant. The exact rational tick conserves cell energy except admitted port work. Continuous Clausius production is `κ(T₁−T₂)²/(T₁T₂) ≥ 0`; nonnegative finite-tick production requires the explicit stability condition `hκ(1/C₁+1/C₂) ≤ 1`.
- `lean/Holonics/Foundation/Standing/Law.lean` defines retention as a quotient through which every admitted future receiver/history face factors. Injectivity and reconstruction of passage history are not required; an admitted future that separates two sources forces distinct retained values. This is an information/causal law, not a thermal entropy or heat identity.
- `docs/THE_MACHINE.md` says overlap alone implies no friction, conservative exchange, or heat; those need explicit material terms. `docs/ELEMENTARY_OBJECTS.md` says erasure is the scope of the historical Landauer floor, and energy/erasure axes remained owed in the retired Rust owner; do not price transport or reversible rebase as erasure.

## Existing secondary local references (not primary-source recovery)

- `research/records/2026-07-15_THE_SWING_CARRIES_THE_FAMILY_THE_DEED_STANDS_AS_MASS.md` cites Rolf Landauer, “Irreversibility and Heat Generation in the Computing Process,” IBM Journal of Research and Development 5(3), 183–191 (1961), DOI https://doi.org/10.1147/rd.53.0183, and explicitly bounds the claim to many-to-one logical operations physically realized under the paper's assumptions; it says this is not passive-retention cost.
- `research/records/2026-07-17_THE_CHANNEL_GROWS_THROUGH_THE_MESSAGE_THE_PROOF_IS_PRACTICED_CONDUCT.md` cites the same 1961 paper and distinguishes information, archive bytes, semantic loss, and thermodynamic entropy. These local summaries are not the requested Bennett/Reeb–Wolf sources.

## Consequence for the delegated join

This lane supplies no new primary-source theorem. Keep reset/erasure work tied to an explicitly declared many-to-one physical protocol and its bath/contact; do not identify a logical collapse with heat or entropy production without that constitutive map. The actual finite-bath correction, correlations/side information, reversible-computation construction details, and source-stated unit conventions remain unverified because the designated primaries were unavailable.

Computational object remains the helical pair/contact joined to its actual material medium. The lane touches faces/placement and tube/tower restriction; helix, carry, and circuit holonomy remain attached.
