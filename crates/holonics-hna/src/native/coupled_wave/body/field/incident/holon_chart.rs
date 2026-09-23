//! **`ResidentHolonChart`: the core Holon of a fixed generator machine, and its chart square.**
//!
//! [definition; agent-inferred] Plan phase 8 (`docs/plans/THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md`):
//! the resident incident word is a chart of a core Holon, owing "exact reference value ∈ returned
//! dyadic ball", not equality. Compiled from a `CompiledGeneratorMachine`:
//!
//! - **storage**: every ring (site) carries its `2n` real resident coordinates under the unit
//!   pairing `E = ½|x|²` (the pairing the reaction deposit leaves unchanged);
//! - **resistive**: per site the reaction's resistive element `R = −herm W_s` on its own ring,
//!   and per arc the helical pair contact `w D` on the relative slip (`HelicalPairInteraction::
//!   contact_element`), whose flow is `J_pair C` read on the receiver and source rings through the
//!   real-coded embedding (original coordinate `i` ↦ the real face of native channel `i`);
//! - **interconnection**: the skew graph `f_S = −Ω e_S − Gᵀ e_R − B e_P`, `f_R = G e_S`,
//!   `f_P = Bᵀ e_S`, with `Ω` the modulated skew interconnection `realify(skew W_s + J(c))`
//!   at each ring's contrast `c`, `G` the resistive incidence above and `B = realify W_c`;
//! - **ports**: each ring's real contrast coordinates (the reaction's port `W_c c`);
//! - **generators**: each site's core `Generator` (`CompiledGeneratorSite::core_generator`).
//!
//! The implicit-midpoint advance of the ring-local reaction Holon is exactly the device Cayley
//! stage's law, `y − p = K(c) x̄ + W_c c` (`Holon/Law.lean::advance_law`,
//! `Holon/Cayley.lean::midpoint_reaction_balance`); [`ResidentHolonChart::reaction_holon`] is that
//! Holon, and the chart-square test checks that its exact advance lies in the ball the device word
//! returned. Scope: the square is stated and tested for the reaction stage; the participation drive
//! (an exterior receiver), the `S_D` reflection and the held relaxation are not yet charted here.
#![allow(dead_code)] // consumed by its conformance square; `NativeCoupledBody` delegation is owed
use super::*;
use crate::native::field_geometry::machine::CompiledGeneratorMachine;
use holonic_core::dirac::DiracStructure;
use holonic_core::element::ResistiveRelation;
use holonic_core::exact_linear::ExactRatMatrix;
use holonic_core::holon::{Holon, PortCounts, PortHolon};
use holonic_core::inertia::SymmetricForm;
use holonic_core::law::{ReferenceHolon, Scheme};
use holonic_engine::native_ecology::constitutive_fibre::PowerNeutralCertificate;
use num_traits::{One, Zero};
use relational_geometry::Rat;

/// One arc's contact in the resident chart.
#[derive(Clone, Debug)]
pub struct ChartContact {
    pub receiver: usize,
    pub source: usize,
    /// `w D` on the three slip coordinates, certified passive.
    pub resistance: ResistiveRelation,
    /// `J_pair C` read on the resident rings: `3 × (sites · width)`.
    pub slip: ExactRatMatrix,
}

/// [definition] The compiled chart (see the module header).
#[derive(Clone, Debug)]
pub struct ResidentHolonChart {
    sites: usize,
    /// Real resident coordinates per ring (`2n`).
    width: usize,
    contacts: Vec<ChartContact>,
    generators: Vec<holonic_core::generator::Generator>,
}

/// One ring's reaction at a contrast: the exact executed coefficients (`n × F` integers at
/// `2^-grain`, `F = n + k/2 + n·k`) and the real contrast coordinates `c`.
pub struct RingReaction<'a> {
    pub n: usize,
    pub k: usize,
    pub grain: u32,
    pub coefficients: &'a [Vec<(num_bigint::BigInt, num_bigint::BigInt)>],
    pub contrast: &'a [Rat],
}
impl<'a> RingReaction<'a> {
    /// The reaction of a certified resident cut.
    pub fn certified(certificate: &'a PowerNeutralCertificate<'_>, contrast: &'a [Rat]) -> Self {
        Self {
            n: certificate.n,
            k: certificate.k,
            grain: certificate.grain,
            coefficients: &certificate.coefficients,
            contrast,
        }
    }
}

fn rat_err(e: impl ToString) -> NativeSessionError {
    invalid(e.to_string())
}

impl ResidentHolonChart {
    /// Compile the machine's rings, contacts and generators; `width` is the resident real width of
    /// one ring (`12` for the six native complex channels).
    pub fn compile(
        machine: &CompiledGeneratorMachine,
        width: usize,
    ) -> Result<Self, NativeSessionError> {
        let sites = machine.sites().len();
        if width < 12 || width % 2 != 0 {
            return Err(invalid("resident ring width"));
        }
        let sigma = sites * width;
        let mut contacts = Vec::with_capacity(machine.arcs().len());
        for arc in machine.arcs() {
            let interaction = arc.interaction();
            let resistance = interaction.contact_element().map_err(rat_err)?;
            let slip = interaction.effective_slip();
            if slip.rows() != 3 || slip.columns() != 12 {
                return Err(invalid("pair slip is not 3 × (6 receiver + 6 source)"));
            }
            // Blocks: [receiver(6), source(6)] original real coordinates; original coordinate i
            // is the real face of native channel i, resident real index 2i.
            let mut rows = vec![vec![Rat::zero(); sigma]; 3];
            for (row, target) in rows.iter_mut().enumerate() {
                for i in 0..6 {
                    target[arc.receiver_index() * width + 2 * i] +=
                        slip.get(row, i).map_err(rat_err)?;
                    target[arc.source_index() * width + 2 * i] +=
                        slip.get(row, 6 + i).map_err(rat_err)?;
                }
            }
            contacts.push(ChartContact {
                receiver: arc.receiver_index(),
                source: arc.source_index(),
                resistance,
                slip: ExactRatMatrix::shaped(3, sigma, rows).map_err(rat_err)?,
            });
        }
        let generators = machine
            .sites()
            .iter()
            .map(|site| site.core_generator().map_err(rat_err))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            sites,
            width,
            contacts,
            generators,
        })
    }

    pub fn sites(&self) -> usize {
        self.sites
    }
    pub fn contacts(&self) -> &[ChartContact] {
        &self.contacts
    }

    /// `(Ω, R, B)` of one ring's reaction on the interleaved real chart: `Ω = realify(skew W_s +
    /// J(c))` (real skew), `R = −realify(herm W_s)` (PSD by the certificate) and `B = realify W_c`
    /// on the `k` real contrast coordinates.
    fn ring_blocks(
        &self,
        reaction: &RingReaction<'_>,
    ) -> Result<(ExactRatMatrix, ExactRatMatrix, ExactRatMatrix), NativeSessionError> {
        let (n, k) = (reaction.n, reaction.k);
        if 2 * n != self.width
            || reaction.contrast.len() != k
            || reaction.coefficients.len() != n
            || reaction
                .coefficients
                .iter()
                .any(|row| row.len() != n + k / 2 + n * k)
        {
            return Err(invalid("ring reaction extent"));
        }
        let unit = Rat::from_integer(num_bigint::BigInt::from(1) << reaction.grain);
        let coefficient = |a: usize, j: usize| -> (Rat, Rat) {
            let (re, im) = &reaction.coefficients[a][j];
            (
                Rat::from_integer(re.clone()) / &unit,
                Rat::from_integer(im.clone()) / &unit,
            )
        };
        // K = W_s + J(c) as complex entries.
        let k_entry = |a: usize, b: usize| -> (Rat, Rat) {
            let (mut re, mut im) = coefficient(a, b);
            for (r, c) in reaction.contrast.iter().enumerate() {
                let (sr, si) = coefficient(a, n + k / 2 + r * n + b);
                re += c * sr;
                im += c * si;
            }
            (re, im)
        };
        let realify = |m: &dyn Fn(usize, usize) -> (Rat, Rat), columns: usize| {
            let mut rows = vec![vec![Rat::zero(); 2 * columns]; 2 * n];
            for a in 0..n {
                for b in 0..columns {
                    let (x, y) = m(a, b);
                    rows[2 * a][2 * b] = x.clone();
                    rows[2 * a][2 * b + 1] = -y.clone();
                    rows[2 * a + 1][2 * b] = y;
                    rows[2 * a + 1][2 * b + 1] = x;
                }
            }
            ExactRatMatrix::shaped(2 * n, 2 * columns, rows).map_err(rat_err)
        };
        let kr = realify(&k_entry, n)?;
        let half = Rat::new(1.into(), 2.into());
        let kt = kr.transpose().map_err(rat_err)?;
        // Ω = (K − Kᵀ)/2, R = −(K + Kᵀ)/2 in the realified chart (the slices are exactly skew,
        // so the symmetric part is that of W_s).
        let omega = kr.subtract(&kt).map_err(rat_err)?.scaled(&half);
        let resistance = kr.add(&kt).map_err(rat_err)?.scaled(&(-half));
        // B maps real contrast coordinate c_(2m) ↦ W_c[:,m], c_(2m+1) ↦ i W_c[:,m].
        let mut b_rows = vec![vec![Rat::zero(); k]; 2 * n];
        for a in 0..n {
            for m in 0..k / 2 {
                let (x, y) = coefficient(a, n + m);
                b_rows[2 * a][2 * m] = x.clone();
                b_rows[2 * a + 1][2 * m] = y.clone();
                b_rows[2 * a][2 * m + 1] = -y;
                b_rows[2 * a + 1][2 * m + 1] = x;
            }
        }
        Ok((
            omega,
            resistance,
            ExactRatMatrix::shaped(2 * n, k, b_rows).map_err(rat_err)?,
        ))
    }

    /// **The ring-local reaction Holon** at its contrast, stepped by the exact implicit midpoint
    /// at `h = 1`: its advance from the drive `p` with input `c` is the device Cayley stage's law.
    pub fn reaction_holon(
        &self,
        reaction: &RingReaction<'_>,
    ) -> Result<ReferenceHolon, NativeSessionError> {
        let (omega, resistance, input) = self.ring_blocks(reaction)?;
        let port = PortHolon::medium(
            &omega,
            &resistance,
            SymmetricForm::from_diagonal(vec![Rat::one(); self.width]),
            &input,
            false,
        )
        .map_err(rat_err)?;
        ReferenceHolon::new(
            Holon::new(port).map_err(rat_err)?,
            Rat::one(),
            Scheme::Midpoint,
        )
        .map_err(rat_err)
    }

    /// **The machine Holon**: every ring's storage and reaction, every arc's contact, the rings'
    /// contrast ports, on one skew interconnection (see the module header), with the sites'
    /// generators attached.
    pub fn holon(&self, reactions: &[RingReaction<'_>]) -> Result<Holon, NativeSessionError> {
        if reactions.len() != self.sites {
            return Err(invalid("one reaction per ring"));
        }
        let w = self.width;
        let sigma = self.sites * w;
        let blocks = reactions
            .iter()
            .map(|r| self.ring_blocks(r))
            .collect::<Result<Vec<_>, _>>()?;
        let mu: usize = blocks.iter().map(|b| b.2.columns()).sum();
        let rho = sigma + 3 * self.contacts.len();
        let total = sigma + rho + mu;
        let mut s = vec![vec![Rat::zero(); total]; total];
        let mut port_at = sigma + rho;
        let mut resistance = vec![vec![Rat::zero(); rho]; rho];
        for (site, (omega, r, b)) in blocks.iter().enumerate() {
            let o = site * w;
            for i in 0..w {
                for j in 0..w {
                    s[o + i][o + j] = -omega.get(i, j).map_err(rat_err)?.clone();
                    resistance[o + i][o + j] = r.get(i, j).map_err(rat_err)?.clone();
                }
                // Reaction resistive incidence G = I on its own ring.
                s[o + i][sigma + o + i] = -Rat::one();
                s[sigma + o + i][o + i] = Rat::one();
                for m in 0..b.columns() {
                    let v = b.get(i, m).map_err(rat_err)?;
                    s[o + i][port_at + m] = -v.clone();
                    s[port_at + m][o + i] = v.clone();
                }
            }
            port_at += b.columns();
        }
        for (index, contact) in self.contacts.iter().enumerate() {
            let at = sigma + sigma + 3 * index;
            for row in 0..3 {
                for column in 0..sigma {
                    let g = contact.slip.get(row, column).map_err(rat_err)?;
                    if !g.is_zero() {
                        s[column][at + row] = -g.clone();
                        s[at + row][column] = g.clone();
                    }
                }
                for column in 0..3 {
                    resistance[sigma + 3 * index + row][sigma + 3 * index + column] = contact
                        .resistance
                        .resistance()
                        .get(row, column)
                        .map_err(rat_err)?
                        .clone();
                }
            }
        }
        let structure = ExactRatMatrix::shaped(total, total, s).map_err(rat_err)?;
        let port = PortHolon::new(
            DiracStructure::skew_graph(&structure).map_err(rat_err)?,
            PortCounts {
                storage: sigma,
                resistive: rho,
                external: mu,
                active: 0,
            },
            SymmetricForm::from_diagonal(vec![Rat::one(); sigma]),
            ResistiveRelation::new(ExactRatMatrix::shaped(rho, rho, resistance).map_err(rat_err)?)
                .map_err(rat_err)?,
        )
        .map_err(rat_err)?;
        let mut holon = Holon::new(port).map_err(rat_err)?;
        for generator in &self.generators {
            holon = holon.with_generator(generator.clone());
        }
        Ok(holon)
    }
}

#[cfg(test)]
mod tests {
    use super::super::machine_tests::spec;
    use super::*;
    use holonic_core::holon::HolonState;
    use holonic_core::law::HolonLaw;

    fn r(v: i64) -> Rat {
        Rat::from_integer(v.into())
    }

    /// A deterministic exactly power-neutral certificate-shaped coefficient set (host only): skew
    /// slices, a passive `W_s` (negative diagonal plus a skew part), a nonzero `W_c`.
    fn coefficients(
        n: usize,
        k: usize,
        grain: u32,
    ) -> Vec<Vec<(num_bigint::BigInt, num_bigint::BigInt)>> {
        let f = n + k / 2 + n * k;
        let mut w = vec![vec![(num_bigint::BigInt::zero(), num_bigint::BigInt::zero()); f]; n];
        let unit = 1i64 << grain;
        for a in 0..n {
            w[a][a] = ((-(unit / 2) - a as i64).into(), ((a as i64 + 1) * 3).into());
            for b in a + 1..n {
                let (x, y) = ((a * 7 + b) as i64 - 20, (a + 2 * b) as i64);
                w[a][b] = (x.into(), y.into());
                w[b][a] = ((-x).into(), y.into());
            }
            for m in 0..k / 2 {
                w[a][n + m] = (
                    ((a + m) as i64 * 5 - 9).into(),
                    (m as i64 - a as i64).into(),
                );
            }
            for rr in 0..k {
                let base = n + k / 2 + rr * n;
                w[a][base + a] = (0.into(), ((rr + a) as i64 * 11 - 30).into());
                for b in a + 1..n {
                    let (x, y) = ((rr * 3 + a * b) as i64 - 7, (b as i64 - rr as i64) * 13);
                    w[a][base + b] = (x.into(), y.into());
                    w[b][base + a] = ((-x).into(), y.into());
                }
            }
        }
        w
    }

    /// The machine Holon is Dirac, its midpoint advance closes the core balance exactly (zero
    /// residual, zero defect), dissipates through the reaction resistance and the contacts, and
    /// its skew interconnection does no work.
    #[test]
    fn the_machine_holon_advances_with_an_exact_balance() {
        let machine = spec().machine.compile().unwrap();
        let chart = ResidentHolonChart::compile(&machine, 12).unwrap();
        assert_eq!((chart.sites(), chart.contacts().len()), (2, 1));
        let n = 6;
        let k = 12;
        let grain = 8;
        let w = coefficients(n, k, grain);
        let contrasts: Vec<Vec<Rat>> = (0..2)
            .map(|s| {
                (0..k)
                    .map(|i| Rat::new(((i * 3 + s) as i64 - 10).into(), 16.into()))
                    .collect()
            })
            .collect();
        let reactions: Vec<RingReaction> = contrasts
            .iter()
            .map(|c| RingReaction {
                n,
                k,
                grain,
                coefficients: &w,
                contrast: c,
            })
            .collect();
        let holon = chart.holon(&reactions).unwrap();
        assert!(holon.port_holon().dirac().form().is_dirac().unwrap());
        let law = ReferenceHolon::new(holon, r(1), Scheme::Midpoint).unwrap();
        let x: Vec<Rat> = (0..24).map(|i| r((i * 5 % 11) as i64 - 5)).collect();
        let input = contrasts.concat();
        let advance = law.advance(&HolonState::new(x), &input).unwrap();
        assert!(advance.balance.is_exact());
        assert!(advance.balance.discretization_defect.is_zero());
        assert!(advance.balance.dissipated > Rat::zero());
        assert!(advance.balance.active.is_zero());
    }

    fn rational_rows<'c>(
        surface: &'c holonic_engine::resident_section::ResidentSurface<'c>,
        rows: &[Vec<i64>],
        denominator: i64,
        grain: holonic_engine::resident_section::ResidentGrain,
    ) -> ResidentNormalEnclosureSection<'c> {
        use holonic_engine::native_ecology::constitutive_fibre::ResidentConstitutiveSection;
        use holonic_engine::resident_section::{ResidentGrain, ResidentSectionRest};
        let width = rows[0].len();
        let values = rows
            .iter()
            .flat_map(|row| {
                row.iter()
                    .map(|v| (*v, *v))
                    .chain([(denominator, denominator)])
                    .collect::<Vec<_>>()
            })
            .collect();
        let raw = surface
            .mount_section_rest(
                &ResidentSectionRest::found(rows.len(), width + 1, ResidentGrain(0), 64, values)
                    .unwrap(),
            )
            .unwrap();
        ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::rationals(&raw).unwrap(),
            grain,
        )
        .unwrap()
    }

    fn lcg(seed: &mut u64, span: i64) -> i64 {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((*seed >> 33) as i64).rem_euclid(2 * span + 1) - span
    }

    fn real(center: &[holonic_engine::ExactComplexWaveCurrent]) -> Vec<Rat> {
        center
            .iter()
            .flat_map(|z| [z.real.clone(), z.imaginary.clone()])
            .collect()
    }

    /// Install trained, projected power-neutral reaction materials in every owner of `body`.
    fn install_trained_reactions<'c>(
        body: &mut NativeCoupledBody<'c>,
        surface: &'c holonic_engine::resident_section::ResidentSurface<'c>,
        grain: holonic_engine::resident_section::ResidentGrain,
        seed: u64,
    ) {
        use holonic_engine::native_ecology::constitutive_fibre::ResidentNormalMaterial;
        let surface = surface;
        let mut seed = seed;
        {
            let BodyState::Incident(model) = body.state_mut().unwrap() else {
                panic!("incident chart");
            };
            for member in 0..model.materials.len() {
                let (n, k) = model.reaction_extent(member).unwrap();
                let features = n + k / 2 + n * k;
                let rows = 24;
                let s: Vec<Vec<i64>> = (0..rows)
                    .map(|_| (0..2 * n).map(|_| lcg(&mut seed, 40)).collect())
                    .collect();
                let t: Vec<Vec<i64>> = (0..rows)
                    .map(|_| (0..2 * n).map(|_| lcg(&mut seed, 60)).collect())
                    .collect();
                let s = rational_rows(surface, &s, 16, grain);
                let phi = if k == 0 {
                    s
                } else {
                    let c: Vec<Vec<i64>> = (0..rows)
                        .map(|_| (0..k).map(|_| lcg(&mut seed, 40)).collect())
                        .collect();
                    s.realified_bilinear_enclosed_features(&rational_rows(surface, &c, 16, grain))
                        .unwrap()
                };
                let trained = ResidentNormalMaterial::found_features(surface, features, n, grain)
                    .unwrap()
                    .stage_receive_enclosed_section(&phi, &rational_rows(surface, &t, 16, grain))
                    .unwrap();
                let (projected, _, _) = trained
                    .project_power_neutral_reaction_certified(n, k)
                    .unwrap();
                model.materials[member] = projected;
            }
        }
    }

    /// **The chart square** (`reference ∈ resident ball`): on the two-ring machine under the
    /// power-neutral law, with trained and projected reaction materials installed (ring `a` has no
    /// contrast, `k = 0`; ring `b` has one arc contrast, `k = 12`), every row of the device word's
    /// Cayley stage contains the exact implicit-midpoint advance of the ring's core reaction Holon
    /// from the same drive and contrast centres, whose core balance closes exactly with zero
    /// active power. Committing the word publishes its exterior energy balance: the reaction
    /// (skew) term is exactly `0` and the telescoped residual is exactly `0`.
    #[test]
    #[ignore = "requires CUDA; chart square of the Cayley reaction stage and the committed energy balance"]
    fn the_reference_reaction_advance_lies_in_the_device_ball() {
        use holonic_engine::embedding_fiber::ResidentReadout;
        use holonic_engine::resident_section::{ResidentGrain, ResidentSurface};
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let grain = ResidentGrain(48);
        let mut declared = spec();
        declared.reaction_law = ReactionLaw::PowerNeutral;
        let mut body = NativeCoupledBody::found_generator_field(&surface, declared, grain).unwrap();
        install_trained_reactions(&mut body, &surface, grain, 41);
        let anchor = super::super::machine_tests::make_machine_anchor(&surface, grain, 0);
        let held = vec![false; anchor.view().components() / 2];
        let prepared = body.prepare_incident_field(anchor.view(), &held).unwrap();
        let word = std::rc::Rc::clone(&prepared.word);
        let chart = ResidentHolonChart::compile(word.machine.as_ref().unwrap(), 12).unwrap();
        let mut checked = 0;
        let mut contrasted = 0;
        for step in &word.steps {
            for stage in &step.sites {
                let cayley = stage.cayley.as_ref().expect("power-neutral stage");
                let drives = stage.phase.output().inspect_rows().unwrap();
                let steps = cayley.step.inspect_rows().unwrap();
                let contrasts = match &stage.condition {
                    Some(c) => c.inspect_rows().unwrap(),
                    None => vec![],
                };
                for (row, (p, y)) in drives.iter().zip(&steps).enumerate() {
                    let c = contrasts
                        .get(row)
                        .map(|b| real(&b.center))
                        .unwrap_or_default();
                    contrasted += usize::from(!c.is_empty());
                    let law = chart
                        .reaction_holon(&RingReaction::certified(&cayley.certificate, &c))
                        .unwrap();
                    let advance = law.advance(&HolonState::new(real(&p.center)), &c).unwrap();
                    assert!(advance.balance.is_exact());
                    assert!(advance.balance.active.is_zero());
                    assert!(advance.balance.dissipated >= Rat::zero());
                    let square: Rat = advance
                        .state
                        .configuration
                        .iter()
                        .zip(real(&y.center))
                        .map(|(a, b)| (a - &b) * (a - &b))
                        .sum();
                    assert!(
                        square <= &y.radius * &y.radius,
                        "reference outside the resident ball (row {row})"
                    );
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 2);
        assert_eq!(contrasted, 1);
        body.publish_incident_field(prepared, true, false).unwrap();
        let current = body.inspect_current().unwrap();
        let balance: IncidentEnergyBalance =
            serde_json::from_value(current["energy_balance"].clone()).unwrap();
        assert!(balance.reaction.is_zero());
        assert!(balance.residual.is_zero());
        assert!(balance.reaction_balance_exact);
        assert!(balance.reaction_dissipated >= 0.0);
        assert!(balance.projection <= 0.0);
        eprintln!(
            "CHART-SQUARE-BALANCE {}",
            serde_json::to_string(&balance).unwrap()
        );
    }

    /// **The Cayley word's complete adjoint** (anchor return through `S_D`, the relaxation, the
    /// projection, the Cayley stage's `2u − g`, the participation and the contrast return through
    /// `Wᴴu` at the midpoint) pairs with the word's central difference on the two-ring machine with
    /// trained power-neutral materials, and the material return deposits and recertifies.
    #[test]
    #[ignore = "requires CUDA; full-word adjoint of the Cayley reaction against its central difference"]
    fn the_cayley_word_adjoint_pairs_with_its_central_difference() {
        use num_traits::Signed;
        use holonic_engine::embedding_fiber::ResidentReadout;
        use holonic_engine::resident_section::{ResidentGrain, ResidentSurface};
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let grain = ResidentGrain(48);
        let mut declared = spec();
        declared.reaction_law = ReactionLaw::PowerNeutral;
        let mut body = NativeCoupledBody::found_generator_field(&surface, declared, grain).unwrap();
        install_trained_reactions(&mut body, &surface, grain, 43);
        let machine_anchor = super::super::machine_tests::make_machine_anchor;
        let anchor = machine_anchor(&surface, grain, 0);
        let held = vec![false; anchor.view().components() / 2];
        let prepared = body.prepare_incident_field(anchor.view(), &held).unwrap();
        let generated = body.publish_incident_field(prepared, false, true).unwrap();
        let comparison = generated.comparison_id().unwrap();
        let output = generated.joint_output().inspect().unwrap();
        let (plus, minus) = (
            machine_anchor(&surface, grain, 1),
            machine_anchor(&surface, grain, -1),
        );
        let out_plus = body
            .prepare_incident_field(plus.view(), &held)
            .unwrap()
            .joint_output()
            .inspect()
            .unwrap();
        let out_minus = body
            .prepare_incident_field(minus.view(), &held)
            .unwrap()
            .joint_output()
            .inspect()
            .unwrap();
        let pair = |a: &[holonic_engine::ExactComplexWaveCurrent],
                    b: &[holonic_engine::ExactComplexWaveCurrent]| {
            a.iter()
                .zip(b)
                .map(|(x, y)| &x.real * &y.real + &x.imaginary * &y.imaginary)
                .sum::<Rat>()
        };
        let half = Rat::new(1.into(), 2.into());
        let delta_out: Vec<_> = out_minus
            .center
            .iter()
            .zip(&out_plus.center)
            .map(|(a, b)| {
                holonic_engine::ExactComplexWaveCurrent::new(
                    (&b.real - &a.real) * &half,
                    (&b.imaginary - &a.imaginary) * &half,
                )
            })
            .collect();
        let base_source = anchor.inspect().unwrap();
        let delta_source: Vec<_> = base_source
            .center
            .iter()
            .zip(&plus.inspect().unwrap().center)
            .map(|(a, b)| b.subtract(a))
            .collect();
        let frozen = body.incident_comparison(comparison).unwrap();
        let returned = body
            .prepare_incident_material_return(comparison, frozen.joint_output(), 4)
            .unwrap();
        let forward = pair(&output.center, &delta_out);
        let adjoint = pair(
            &returned.anchor_covector().inspect().unwrap().center,
            &delta_source,
        );
        let scale = forward.abs().max(adjoint.abs());
        assert!(scale > Rat::zero());
        let residual = (&forward - &adjoint).abs();
        assert!(
            residual < &scale / r(1000),
            "Cayley word pairing residual {residual}, forward {forward}, adjoint {adjoint}"
        );
        assert_eq!(returned.reaction_deposits().deposits, 1);
        body.publish_incident_material_return(returned).unwrap();
        // The deposited cuts carry their certificates: the next word needs no recertification.
        let again = body.prepare_incident_field(anchor.view(), &held).unwrap();
        assert!(again.word.steps[0].sites.iter().all(|s| s.cayley.is_some()));
    }
}
