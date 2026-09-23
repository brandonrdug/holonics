//! **The normal wave as a core Holon** (plan phase 9, motion facet): one `HolonLaw`.
//!
//! [definition; agent-inferred] The applied normal wave on its resident chart is the linear
//! word `x⁺ = T x` on the joint `x = (p, c)` (`kernels/normal_wave.cuh::normal_wave_entry`):
//!
//! ```text
//! T = [[0, I], [M_p − M_d, I + M_d + M_c]]        c⁺ = c + M φ(p, c),  φ = (c − p, c, p)
//! ```
//!
//! with `M = [M_d | M_c | M_p]` the constitution's applied coefficients (the learned `M`
//! predicts the difference `v − c`). Realified on interleaved `(Re, Im)` coordinates this is a
//! real `4n × 4n` map. It is the implicit-midpoint step of the medium `ẋ = A x` with unit
//! storage, `A = 2(T − I)(T + I)⁻¹` (the Cayley generator, defined exactly when `−1 ∉ spec T`):
//! `(I − A/2)⁻¹(I + A/2) = T`. So [`NormalWaveHolon`] is the core medium Holon with skew
//! interconnection `Ω = skew A`, zero resistance and the active relation `L = sym A` (declared
//! power, not assumed passive: a learned wave may amplify), and its `ReferenceHolon` advance is
//! exactly the applied wave word with the balance `½|x⁺|² − ½|x|² = ⟨x̄, L x̄⟩` and zero residual
//! (`Holon/Law.lean::advance_law`, `Holon/Cayley.lean::midpoint_reaction_balance`). External
//! ports are the current block (`B = [0; I]`): the free word reads them at zero, and two
//! normal Holons interact by joining those ports (`Holon/Law.lean::PortHolon.interconnect`).
//! The resident advance is a chart of this law, owing "exact advance ∈ returned device ball"
//! (the chart square, `holon_tests`). Scope: the free applied word; reception, actuation and
//! the normal-reference transport are device passages that are not charted here.
use super::*;
use holonic_core::element::ActiveRelation;
use holonic_core::exact_linear::ExactRatMatrix;
use holonic_core::holon::{Holon, HolonError, HolonState, PortHolon};
use holonic_core::inertia::SymmetricForm;
use holonic_core::law::{Advance, HolonLaw, ReferenceHolon, Scheme};

/// [definition] The normal wave Holon (see the module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalWaveHolon {
    roots: usize,
    transfer: ExactRatMatrix,
    reference: ReferenceHolon,
}

fn holon_error(e: impl std::fmt::Display) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(format!("normal wave holon: {e}"))
}

impl NormalWaveHolon {
    /// The realified word `T` of an `n`-root wave constitution (targets `n`, `3n` sources).
    pub fn transfer_of(
        constitution: &NormalConstitution,
    ) -> Result<ExactRatMatrix, ConstitutiveFibreError> {
        let m = &constitution.material.coefficients;
        let n = m.len();
        if n == 0 || m.iter().any(|row| row.len() != 3 * n) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let one = ExactComplexWaveCurrent::new(Rat::one(), Rat::zero());
        let zero = ExactComplexWaveCurrent::zero();
        // Complex T (2n × 2n).
        let entry = |row: usize, col: usize| -> ExactComplexWaveCurrent {
            if row < n {
                return if col == n + row {
                    one.clone()
                } else {
                    zero.clone()
                };
            }
            let r = row - n;
            let j = col % n;
            if col < n {
                m[r][2 * n + j].subtract(&m[r][j])
            } else {
                let v = m[r][j].add(&m[r][n + j]);
                if r == j { v.add(&one) } else { v }
            }
        };
        let d = 2 * n;
        let mut rows = vec![vec![Rat::zero(); 2 * d]; 2 * d];
        for a in 0..d {
            for b in 0..d {
                let z = entry(a, b);
                rows[2 * a][2 * b] = z.real.clone();
                rows[2 * a][2 * b + 1] = -z.imaginary.clone();
                rows[2 * a + 1][2 * b] = z.imaginary.clone();
                rows[2 * a + 1][2 * b + 1] = z.real;
            }
        }
        ExactRatMatrix::new(rows).map_err(holon_error)
    }

    /// Compile the Holon of a wave constitution; refuses when `T + I` is singular (no Cayley
    /// chart: `−1` is an eigenvalue of the word).
    pub fn compile(constitution: &NormalConstitution) -> Result<Self, ConstitutiveFibreError> {
        let transfer = Self::transfer_of(constitution)?;
        let sigma = transfer.rows();
        let n = sigma / 4;
        let identity = ExactRatMatrix::identity(sigma).map_err(holon_error)?;
        let inverse = transfer
            .add(&identity)
            .map_err(holon_error)?
            .inverse()
            .map_err(|e| holon_error(format!("T + I is singular, no Cayley chart: {e}")))?;
        let generator = transfer
            .subtract(&identity)
            .map_err(holon_error)?
            .multiply(&inverse)
            .map_err(holon_error)?
            .scaled(&Rat::from_integer(2.into()));
        let transpose = generator.transpose().map_err(holon_error)?;
        let half = Rat::new(1.into(), 2.into());
        let omega = generator
            .subtract(&transpose)
            .map_err(holon_error)?
            .scaled(&half);
        let active = generator
            .add(&transpose)
            .map_err(holon_error)?
            .scaled(&half);
        let mut input = vec![vec![Rat::zero(); 2 * n]; sigma];
        for (i, row) in input.iter_mut().enumerate().skip(2 * n) {
            row[i - 2 * n] = Rat::one();
        }
        let input = ExactRatMatrix::shaped(sigma, 2 * n, input).map_err(holon_error)?;
        let storage = SymmetricForm::from_rows(identity.to_rows()).map_err(holon_error)?;
        let port = PortHolon::medium(
            &omega,
            &ExactRatMatrix::zero(sigma, sigma).map_err(holon_error)?,
            storage,
            &input,
            true,
        )
        .map_err(holon_error)?;
        let holon = Holon::new(port)
            .and_then(|h| h.with_active(ActiveRelation::new(active)?))
            .map_err(holon_error)?;
        let reference =
            ReferenceHolon::new(holon, Rat::one(), Scheme::Midpoint).map_err(holon_error)?;
        Ok(Self {
            roots: n,
            transfer,
            reference,
        })
    }

    pub fn roots(&self) -> usize {
        self.roots
    }
    /// The realified word `T`.
    pub fn transfer(&self) -> &ExactRatMatrix {
        &self.transfer
    }
    /// The joint `(p, c)` of complex currents as a Holon state (interleaved real coordinates).
    pub fn state(joint: &[ExactComplexWaveCurrent], commit: u64) -> HolonState {
        HolonState {
            configuration: joint
                .iter()
                .flat_map(|z| [z.real.clone(), z.imaginary.clone()])
                .collect(),
            commit,
        }
    }
}

impl HolonLaw for NormalWaveHolon {
    fn holon(&self) -> &Holon {
        self.reference.holon()
    }
    /// The free applied word, `x⁺ = T x` at zero current-port input, with its exact balance.
    fn advance(&self, state: &HolonState, input: &[Rat]) -> Result<Advance, HolonError> {
        self.reference.advance(state, input)
    }
    fn interact(&self, other: &Self, joined: &[(usize, usize)]) -> Result<Self, HolonError> {
        let reference = self.reference.interact(&other.reference, joined)?;
        let transfer = holonic_core::scalar::block_diagonal(&self.transfer, &other.transfer)?;
        Ok(Self {
            roots: self.roots + other.roots,
            transfer,
            reference,
        })
    }
}

impl<'c, C> ResidentNormalWave<'c, C> {
    /// The core Holon of this wave's contemporary constitution (host decode of the material).
    pub fn holon_law(&self) -> Result<NormalWaveHolon, ConstitutiveFibreError> {
        NormalWaveHolon::compile(&self.material.inspect()?)
    }
}

#[cfg(test)]
mod holon_tests {
    use super::super::comparison_tests::{contains, current, point, witness};
    use super::*;
    use crate::embedding_fiber::ResidentReadout;

    /// The chart square: the exact core advance of the seed lies in the device ball the applied
    /// resident word returns, and the core balance closes with zero residual.
    #[test]
    #[ignore = "requires CUDA; the exact core advance lies in the resident applied word's ball"]
    fn the_core_advance_lies_in_the_resident_word_ball() {
        let readout = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&readout).unwrap();
        let mut body = witness(&s);
        body.set_transport(NormalWaveTransport::Applied).unwrap();
        let law = body.holon_law().unwrap();
        let seed = body.joint_source().joint().inspect().unwrap();
        assert!(seed.radius.is_zero(), "exact integer seed");
        let mut state = NormalWaveHolon::state(&seed.center, 0);
        for step in 1..=3u64 {
            let advanced = law.advance(&state, &vec![Rat::zero(); 2]).unwrap();
            assert!(advanced.balance.is_exact());
            assert_eq!(
                advanced.state.configuration,
                law.transfer().apply(&state.configuration).unwrap()
            );
            assert_eq!(
                advanced.balance.stored_change,
                advanced.balance.active.clone(),
                "the word's power is its declared active term"
            );
            let resident = body.advance().unwrap().inspect().unwrap().joint_current;
            let expected = advanced
                .state
                .configuration
                .chunks_exact(2)
                .map(|z| ExactComplexWaveCurrent::new(z[0].clone(), z[1].clone()))
                .collect::<Vec<_>>();
            contains(&resident, &expected);
            assert_eq!(advanced.state.commit, step);
            state = advanced.state;
        }
    }

    /// Two normal Holons joined at their current ports are one Holon whose free word is the
    /// block word, and the constitution's storage/deposition reading is the core's.
    #[test]
    #[ignore = "requires CUDA; interaction is core interconnection and deposition is core work"]
    fn interaction_and_deposition_are_the_core_facets() {
        let readout = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&readout).unwrap();
        let body = witness(&s);
        let law = body.holon_law().unwrap();
        let joined = law.interact(&law, &[]).unwrap();
        let x: Vec<Rat> = (1..=8).map(|v| Rat::from_integer(v.into())).collect();
        let free = joined
            .advance(
                &HolonState {
                    configuration: x.clone(),
                    commit: 0,
                },
                &vec![Rat::zero(); 4],
            )
            .unwrap();
        assert_eq!(
            free.state.configuration,
            joined.transfer().apply(&x).unwrap()
        );
        assert!(free.balance.is_exact());
        // Deposition: one observation's change of H is core deposition work at the successor W.
        let mut material = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(32)).unwrap();
        let before = material.inspect().unwrap();
        let phi = point(&s, &[1, 0, 1, 0, 0, 0]);
        let eta = point(&s, &[2, 0]);
        material.receive(current(&phi), current(&eta)).unwrap();
        let after = material.inspect().unwrap();
        let work = before.deposition_work(&after).unwrap();
        let direct: Rat = after
            .coefficient_rows()
            .iter()
            .map(|w| {
                holonic_core::element::storage_energy(&after.storage_form().unwrap(), w).unwrap()
                    - holonic_core::element::storage_energy(&before.storage_form().unwrap(), w)
                        .unwrap()
            })
            .sum();
        assert_eq!(work, direct);
        assert!(
            work > Rat::zero(),
            "an observed source strictly deposits storage"
        );
        assert!(matches!(
            after.element().unwrap(),
            holonic_core::element::ElementRelation::Storage { .. }
        ));
        // The receivers of the Holon declare their core element: passive readings.
        let family = body.read_family().unwrap();
        let receiver = family.read_receiver().unwrap();
        let element = receiver.receiver_element();
        assert!(element.is_passive());
        assert_eq!(element.read_ports(), receiver.target_width());
        let chart = NormalWaveBasisChart::identity(&s, 1).unwrap();
        assert!(
            body.read_basis_face(&chart)
                .unwrap()
                .receiver_element()
                .is_passive()
        );
    }
}
