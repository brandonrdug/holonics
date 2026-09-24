//! **Restrictions `π` to coarser grains: the scale square or a typed defect.**
//!
//! [definition] A port map `P` pushes flows forward `f' = P f` and pulls efforts back `e = Pᵀ e'`
//! (`Holon/Restriction.lean::pushforward`); it preserves power, `⟨e', P f⟩ = ⟨Pᵀ e', f⟩`
//! (`Holon/Restriction.lean::power_pushforward`, the pullback law `Holon/Law.lean::pullback_law`),
//! and a morphism lands the pushed structure inside the target
//! (`Holon/Restriction.lean::IsMorphism`), composing (`Holon/Restriction.lean::IsMorphism.comp`).
//! The pushforward of a Dirac structure along any port map is Dirac
//! (`Holon/Restriction.lean::pushforwardD_isDirac`), computed by
//! [`crate::dirac::DiracStructure::pushforward`].
//!
//! [definition] **The scale square** `π A_fine = A_coarse π` propagates to every horizon
//! (`Holon/Restriction.lean::scale_square_pow`); a failed square is retained as its typed defect
//! `π A_fine − A_coarse π` (`Holon/Restriction.lean::squareDefect`; witnesses
//! `Holon/Restriction.lean::shift_has_no_coarse_generator`,
//! `Holon/Restriction.lean::diagonal_square`). **Kron/Schur elimination** of a network's interior is
//! an exact restriction: interior-balanced states have boundary bonds on the graph of
//! `Λ_DN = L_BB − L_BI L_II⁻¹ L_IB`, the boundary power is the full power `⟨u, L u⟩`, and every
//! boundary value extends (`Holon/Restriction.lean::kron_exact`,
//! `Holon/Restriction.lean::boundaryBond`; witness `Holon/Restriction.lean::series_path_restriction`).
//!
//! | Lean | Rust |
//! |---|---|
//! | `pushforward`, `power_pushforward`, `pullback_law` | [`PortMap`] |
//! | `IsMorphism`, `IsMorphism.comp` | [`PortMap::is_morphism`], [`PortMap::then`] |
//! | `squareDefect`, `scale_square_pow` | [`SquareDefect`] |
//! | `kron_exact`, `boundaryBond` | [`KronReduction`] |
//! | `squareDefect_mulVec_eq_zero_iff` | `tube::SquareDefect::route_difference`, [`LinearTube`], [`square_descent`], [`tower_square_descent`] |
//! | `Descent`, `descent_total` | [`Descent`], [`factor_descent`], [`factor_descent_over`] |
//! | `Descent.defect`, `descent_defect_refutes_factoring` | [`FibreDefect`], [`Separation`], [`PreimageFibre`], [`ShortestSeparator`] |
//! | `affineFibre_mem` | [`AffineFibre`] |
//!
//! [definition] **Restriction is one owner** (plan phase 6). The transverse axis — towers, gluing,
//! the non-invertible [`tower::Transition`] with its residual, migrations — is [`tower`]
//! (`Foundation/ContinuingTower.lean`); the longitudinal axis — the stationed tower, its two-axis
//! commuting square, circuit holonomy and the wormhole receipt — is [`tube`]
//! (`Transport/ContinuingTube.lean`). Both moved here from `holonic-engine`, which re-exports them
//! at `continuing_tower` and `continuing_tube`. [`Descent`] reads every restriction square or
//! factoring as a witness or a typed defect built on [`tower::Transition::residual`]; the tube's
//! per-face `tube::SquareDefect` is the pointwise chart of the operator [`SquareDefect`] here
//! ([`LinearTube`], `tube::SquareDefect::route_difference`). The engine's coarsening, grain,
//! standing and receiver-exact quotients are instances (`receiver_release::CoarseningTower::descent`,
//! `continuing_tube::SquareVerdict::descent` on the grain tube, `standing::sufficiency_descent`,
//! `receiver_exact_compression::one_shot_descent`), and the engine's Schur boundary transfer
//! (`diffusion::compile_diffusion_transfer`) is a [`KronReduction`] reading.
//!
//! [definition] **A defect retains its fibre and its separator** (plan phase 10). A factor defect
//! is a [`FibreDefect`]: every fibre `π` merges ([`PreimageFibre`]) and every separated merged pair
//! ([`Separation`], the Lean `Descent.defect`). The tree's reconstruction and preimage fibres are
//! instances — a class fibre is a [`PreimageFibre`] under its wire's [`FieldNames`], a linear
//! preimage an [`AffineFibre`], a receiver-exact collapsed pair a [`ShortestSeparator`] — and the
//! remaining wire records read into them ([`fibre`]).

pub mod descent;
pub mod fibre;
pub mod linear;
pub mod tower;
pub mod tube;

pub use descent::{
    DESCENT_SOURCE_CEILING, Descent, DescentRefusal, FactorBreak, FactorBreaks, FactorDescent,
    FactorWitness, SquareBreak, SquareBreaks, SquareDescent, SquareWitness, TowerDescentRefusal,
    factor_descent, factor_descent_over, square_descent, tower_square_descent,
};
pub use fibre::{
    AffineFibre, AffineFibreDefect, FibreDefect, FieldNames, PreimageFibre, Separation,
    ShortestSeparator,
};
pub use linear::{LinearChart, LinearRestriction, LinearStation, LinearTower, LinearTube};

use num_traits::Zero;
use crate::geometry::Rat;
use serde::Serialize;

use crate::dirac::DiracStructure;
use crate::exact_linear::ExactRatMatrix;
use crate::holon::HolonError;
use crate::port::Bond;
use crate::scalar::{dot, is_zero, neg, submatrix};

/// [definition] **A port map** `P : ports → ports'` (`ports' × ports`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PortMap {
    map: ExactRatMatrix,
}

impl PortMap {
    pub fn new(map: ExactRatMatrix) -> Self {
        Self { map }
    }

    pub fn matrix(&self) -> &ExactRatMatrix {
        &self.map
    }

    /// Fine ports.
    pub fn source_ports(&self) -> usize {
        self.map.columns()
    }

    /// Coarse ports.
    pub fn target_ports(&self) -> usize {
        self.map.rows()
    }

    /// `f' = P f`.
    pub fn push_flow(&self, flow: &[Rat]) -> Result<Vec<Rat>, HolonError> {
        Ok(self.map.apply(flow)?)
    }

    /// `e = Pᵀ e'`: the learning covector travels on the effort side (`Holon/Law.lean::pullback_law`).
    pub fn pull_effort(&self, effort: &[Rat]) -> Result<Vec<Rat>, HolonError> {
        Ok(self.map.transpose()?.apply(effort)?)
    }

    /// Both sides of `Holon/Restriction.lean::power_pushforward`: `(⟨e', P f⟩, ⟨Pᵀ e', f⟩)`.
    pub fn power_pair(&self, flow: &[Rat], effort: &[Rat]) -> Result<(Rat, Rat), HolonError> {
        Ok((
            dot(effort, &self.push_flow(flow)?),
            dot(&self.pull_effort(effort)?, flow),
        ))
    }

    /// The pushed Dirac structure (`Holon/Restriction.lean::pushforwardD`).
    pub fn pushforward(&self, structure: &DiracStructure) -> Result<DiracStructure, HolonError> {
        structure.pushforward(&self.map)
    }

    /// `Holon/Restriction.lean::IsMorphism`: the pushforward lies in `target`. Both are Dirac and
    /// of equal dimension, so inclusion is equality of the canonical forms, and the basis check
    /// below decides it exactly.
    pub fn is_morphism(
        &self,
        source: &DiracStructure,
        target: &DiracStructure,
    ) -> Result<bool, HolonError> {
        let pushed = self.pushforward(source)?;
        for bond in pushed.basis()? {
            if !target.contains(&bond)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// `P' ∘ P` (`Holon/Restriction.lean::IsMorphism.comp`).
    pub fn then(&self, next: &Self) -> Result<Self, HolonError> {
        Ok(Self::new(next.map.multiply(&self.map)?))
    }
}

/// [definition] **The scale square and its defect** `π A_fine − A_coarse π`
/// (`Holon/Restriction.lean::squareDefect`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SquareDefect {
    defect: ExactRatMatrix,
}

impl SquareDefect {
    pub fn new(
        restriction: &ExactRatMatrix,
        fine: &ExactRatMatrix,
        coarse: &ExactRatMatrix,
    ) -> Result<Self, HolonError> {
        let defect = restriction
            .multiply(fine)?
            .subtract(&coarse.multiply(restriction)?)?;
        Ok(Self { defect })
    }

    pub fn defect(&self) -> &ExactRatMatrix {
        &self.defect
    }

    /// The square closes: the defect is zero.
    pub fn closes(&self) -> bool {
        is_zero(self.defect.entries())
    }

    /// The defect read at a fine state.
    pub fn at(&self, state: &[Rat]) -> Result<Vec<Rat>, HolonError> {
        Ok(self.defect.apply(state)?)
    }
}

/// Whether `π A_fineⁿ = A_coarseⁿ π` (`Holon/Restriction.lean::scale_square_pow`).
pub fn square_holds_at_horizon(
    restriction: &ExactRatMatrix,
    fine: &ExactRatMatrix,
    coarse: &ExactRatMatrix,
    horizon: u64,
) -> Result<bool, HolonError> {
    let left = restriction.multiply(&fine.power_reduced(horizon)?)?;
    let right = coarse.power_reduced(horizon)?.multiply(restriction)?;
    Ok(left == right)
}

/// [definition] **Kron/Schur reduction** of a network `L` on `interior ⊕ boundary`
/// (`Holon/Restriction.lean::kron_exact`): `Λ_DN = L_BB − L_BI L_II⁻¹ L_IB`, refusing a singular
/// interior block.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct KronReduction {
    network: ExactRatMatrix,
    interior: Vec<usize>,
    boundary: Vec<usize>,
    interior_inverse: ExactRatMatrix,
    dirichlet_to_neumann: ExactRatMatrix,
}

impl KronReduction {
    pub fn new(network: &ExactRatMatrix, interior: &[usize]) -> Result<Self, HolonError> {
        if !network.is_square() {
            return Err(HolonError::Shape {
                what: "network columns",
                expected: network.rows(),
                found: network.columns(),
            });
        }
        let n = network.rows();
        for (index, node) in interior.iter().enumerate() {
            if *node >= n || interior[..index].contains(node) {
                return Err(HolonError::PortOutside {
                    port: *node,
                    ports: n,
                });
            }
        }
        let boundary: Vec<usize> = (0..n).filter(|node| !interior.contains(node)).collect();
        let l_ii = submatrix(network, interior, interior)?;
        let l_ib = submatrix(network, interior, &boundary)?;
        let l_bi = submatrix(network, &boundary, interior)?;
        let l_bb = submatrix(network, &boundary, &boundary)?;
        let interior_inverse = if interior.is_empty() {
            ExactRatMatrix::zero(0, 0)?
        } else {
            l_ii.inverse().map_err(|_| HolonError::Singular {
                what: "interior block of the Kron reduction",
            })?
        };
        let dirichlet_to_neumann =
            l_bb.subtract(&l_bi.multiply(&interior_inverse)?.multiply(&l_ib)?)?;
        Ok(Self {
            network: network.clone(),
            interior: interior.to_vec(),
            boundary,
            interior_inverse,
            dirichlet_to_neumann,
        })
    }

    /// `Λ_DN`.
    pub fn dirichlet_to_neumann(&self) -> &ExactRatMatrix {
        &self.dirichlet_to_neumann
    }

    /// `L_II⁻¹` (the `0 × 0` matrix when the interior is empty).
    pub fn interior_inverse(&self) -> &ExactRatMatrix {
        &self.interior_inverse
    }

    /// The eliminated interior nodes, in declaration order.
    pub fn interior(&self) -> &[usize] {
        &self.interior
    }

    /// The boundary nodes: the complement of the interior, ascending.
    pub fn boundary(&self) -> &[usize] {
        &self.boundary
    }

    /// The network `L`.
    pub fn network(&self) -> &ExactRatMatrix {
        &self.network
    }

    /// The boundary bond of a network state: boundary injected currents and boundary potentials
    /// (`Holon/Restriction.lean::boundaryBond`).
    pub fn boundary_bond(&self, state: &[Rat]) -> Result<Bond, HolonError> {
        let current = self.network.apply(state)?;
        Bond::new(
            self.boundary.iter().map(|b| current[*b].clone()).collect(),
            self.boundary.iter().map(|b| state[*b].clone()).collect(),
        )
    }

    /// Interior balance `(L u)_I = 0`.
    pub fn is_interior_balanced(&self, state: &[Rat]) -> Result<bool, HolonError> {
        let current = self.network.apply(state)?;
        Ok(self.interior.iter().all(|i| current[*i].is_zero()))
    }

    /// The harmonic extension of boundary potentials: `u_I = −L_II⁻¹ L_IB u_B`.
    pub fn extend(&self, boundary_values: &[Rat]) -> Result<Vec<Rat>, HolonError> {
        if boundary_values.len() != self.boundary.len() {
            return Err(HolonError::Shape {
                what: "boundary values",
                expected: self.boundary.len(),
                found: boundary_values.len(),
            });
        }
        let l_ib = submatrix(&self.network, &self.interior, &self.boundary)?;
        let interior = neg(&self.interior_inverse.apply(&l_ib.apply(boundary_values)?)?);
        let mut state = crate::scalar::zeros(self.network.rows());
        for (k, i) in self.interior.iter().enumerate() {
            state[*i] = interior[k].clone();
        }
        for (k, b) in self.boundary.iter().enumerate() {
            state[*b] = boundary_values[k].clone();
        }
        Ok(state)
    }

    /// The three statements of `Holon/Restriction.lean::kron_exact` at one interior-balanced state:
    /// the boundary flow is `Λ_DN u_B`, the boundary power is `⟨u, L u⟩`, and the state is balanced.
    pub fn is_exact_at(&self, state: &[Rat]) -> Result<bool, HolonError> {
        let bond = self.boundary_bond(state)?;
        let graph = self.dirichlet_to_neumann.apply(bond.effort())? == bond.flow();
        let power = bond.power() == dot(state, &self.network.apply(state)?);
        Ok(self.is_interior_balanced(state)? && graph && power)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::restriction::tower::Transition;
    use crate::scalar::{int, integer_matrix, ints, rat};

    /// `Holon/Restriction.lean::shift_has_no_coarse_generator`, `Holon/Restriction.lean::diagonal_square`.
    #[test]
    fn the_shift_has_no_coarse_generator_and_the_diagonal_closes() {
        let read_first = integer_matrix(&[&[1, 0]]).unwrap();
        let shift = integer_matrix(&[&[0, 1], &[0, 0]]).unwrap();
        for a in [int(0), int(1), rat(-3, 2), int(7)] {
            let coarse = ExactRatMatrix::new(vec![vec![a]]).unwrap();
            let defect = SquareDefect::new(&read_first, &shift, &coarse).unwrap();
            assert_eq!(defect.at(&ints(&[0, 1])).unwrap(), vec![int(1)]);
            assert!(!defect.closes());
        }
        let diagonal = integer_matrix(&[&[3, 0], &[0, -5]]).unwrap();
        let coarse = integer_matrix(&[&[3]]).unwrap();
        assert!(
            SquareDefect::new(&read_first, &diagonal, &coarse)
                .unwrap()
                .closes()
        );
        assert!(square_holds_at_horizon(&read_first, &diagonal, &coarse, 6).unwrap());
    }

    /// `Holon/Restriction.lean::series_path_restriction` and `Holon/Restriction.lean::kron_exact`.
    #[test]
    fn the_series_path_restricts_to_two_thirds() {
        // Path 0 —(1)— 1 —(2)— 2, interior node 1.
        let network = integer_matrix(&[&[1, -1, 0], &[-1, 3, -2], &[0, -2, 2]]).unwrap();
        let kron = KronReduction::new(&network, &[1]).unwrap();
        let expected = ExactRatMatrix::new(vec![
            vec![rat(2, 3), rat(-2, 3)],
            vec![rat(-2, 3), rat(2, 3)],
        ])
        .unwrap();
        assert_eq!(kron.dirichlet_to_neumann(), &expected);
        let state = kron.extend(&ints(&[3, -6])).unwrap();
        assert!(kron.is_exact_at(&state).unwrap());
        let singular = KronReduction::new(&integer_matrix(&[&[0, 1], &[1, 0]]).unwrap(), &[0]);
        assert!(matches!(singular, Err(HolonError::Singular { .. })));
    }

    /// Phase 6: the tube's per-face square defect is the pointwise chart of the operator defect,
    /// on the Lean witnesses `Holon/Restriction.lean::shift_has_no_coarse_generator` and
    /// `Holon/Restriction.lean::diagonal_square`.
    #[test]
    fn the_tube_square_defect_is_the_operator_defect_read_at_a_face() {
        use tube::{SquareVerdict, check_commuting_square};
        let read_first = integer_matrix(&[&[1, 0]]).unwrap();
        let shift = integer_matrix(&[&[0, 1], &[0, 0]]).unwrap();
        let diagonal = integer_matrix(&[&[3, 0], &[0, -5]]).unwrap();
        let charts = [LinearChart::Coarse, LinearChart::Fine];
        let faces = [
            ints(&[1, 0]),
            ints(&[0, 1]),
            ints(&[4, -7]),
            vec![rat(1, 3), rat(-2, 5)],
        ];
        for (fine, coarse_entry) in [(&shift, int(0)), (&shift, rat(-3, 2)), (&diagonal, int(3))] {
            let coarse = ExactRatMatrix::new(vec![vec![coarse_entry]]).unwrap();
            let tube = LinearTube::new(&read_first, fine, &coarse).unwrap();
            let operator = tube.operator_defect().unwrap();
            assert_eq!(
                operator,
                SquareDefect::new(&read_first, fine, &coarse).unwrap()
            );
            let mut every_face_commutes = true;
            for face in &faces {
                let verdict = check_commuting_square(
                    &tube,
                    &LinearStation::Earlier,
                    &LinearStation::Later,
                    &charts,
                    &[(LinearChart::Fine, face.clone())],
                )
                .unwrap();
                match &verdict {
                    SquareVerdict::Defect(defect) => {
                        assert_eq!(defect.route_difference(), operator.at(face).unwrap());
                        assert!(!is_zero(&operator.at(face).unwrap()));
                        every_face_commutes = false;
                    }
                    SquareVerdict::Commutes(_) => {
                        assert!(is_zero(&operator.at(face).unwrap()));
                    }
                }
                let descends = verdict.clone().descent().descends();
                assert_eq!(descends, verdict.commutes());
            }
            // The faces span ℚ², so the tube commutes on all of them exactly when the operator
            // defect vanishes.
            assert_eq!(every_face_commutes, operator.closes());
        }
    }

    /// The square descent through the linear restriction breaks exactly where the operator defect
    /// is nonzero, its route difference is that defect, and the retained residual reopens the fine
    /// motion (the break is not a loss).
    #[test]
    fn the_square_descent_retains_the_fine_motion_and_equals_the_operator_defect() {
        let read_first = integer_matrix(&[&[1, 0]]).unwrap();
        let shift = integer_matrix(&[&[0, 1], &[0, 0]]).unwrap();
        let coarse = integer_matrix(&[&[2]]).unwrap();
        let restriction = LinearRestriction::new(read_first.clone()).unwrap();
        let operator = SquareDefect::new(&read_first, &shift, &coarse).unwrap();
        let sources = vec![ints(&[1, 0]), ints(&[0, 1]), ints(&[0, 0]), ints(&[5, 3])];
        let fine = |x: &Vec<Rat>| shift.apply(x).unwrap();
        let coarse_map = |y: &Vec<Rat>| coarse.apply(y).unwrap();
        let descent = square_descent(&restriction, fine, coarse_map, &sources).unwrap();
        let breaks = descent.defect().expect("the shift has no coarse generator");
        assert_eq!(breaks.checked(), sources.len());
        let broken: Vec<usize> = breaks.breaks().iter().map(SquareBreak::index).collect();
        let expected: Vec<usize> = sources
            .iter()
            .enumerate()
            .filter(|(_, x)| !is_zero(&operator.at(x).unwrap()))
            .map(|(k, _)| k)
            .collect();
        assert_eq!(broken, expected);
        for piece in breaks.breaks() {
            let difference =
                crate::scalar::sub(piece.fine_then_restricted(), piece.restricted_then_coarse());
            assert_eq!(difference, operator.at(piece.source()).unwrap());
            assert_eq!(piece.reopen_fine(&restriction), fine(piece.source()));
        }
        // The tower form of the same square returns the same breaks.
        let tower = LinearTower::new(restriction.clone());
        let tower_descent = tower_square_descent(
            &tower,
            &LinearChart::Coarse,
            &LinearChart::Fine,
            |x| Ok(fine(x)),
            |y| Ok(coarse_map(y)),
            &sources,
        )
        .unwrap();
        assert_eq!(tower_descent, descent);

        let diagonal = integer_matrix(&[&[2, 0], &[0, -5]]).unwrap();
        let closes = square_descent(
            &restriction,
            |x: &Vec<Rat>| diagonal.apply(x).unwrap(),
            coarse_map,
            &sources,
        )
        .unwrap();
        let witness = closes.witness().expect("the diagonal square closes");
        assert_eq!(witness.coarse_images()[3], ints(&[10]));
    }

    /// A rank-deficient restriction still reopens exactly; its residual is the kernel component,
    /// and a reading factors through it exactly when it is constant on its fibres.
    #[test]
    fn a_merging_restriction_reopens_and_a_reading_factors_or_breaks() {
        let merge = integer_matrix(&[&[1, 1, 0], &[2, 2, 0]]).unwrap();
        let restriction = LinearRestriction::new(merge.clone()).unwrap();
        let sources = vec![
            ints(&[1, 0, 0]),
            ints(&[0, 1, 0]),
            ints(&[0, 0, 1]),
            ints(&[3, -2, 7]),
        ];
        for x in &sources {
            assert!(restriction.check_reopen(x).is_ok());
            let residual = restriction.residual(x);
            assert!(is_zero(&merge.apply(&residual).unwrap()));
        }
        assert!(restriction.check_reopen(&ints(&[1, 2])).is_ok());

        let sum = |x: &Vec<Rat>| &x[0] + &x[1];
        let factored = factor_descent(&restriction, sum, &sources).unwrap();
        let witness = factored
            .witness()
            .expect("x₀ + x₁ factors through the merge");
        assert_eq!(witness.merged_pairs(), 3);

        let first = |x: &Vec<Rat>| x[0].clone();
        let broken = factor_descent(&restriction, first, &sources).unwrap();
        let breaks = broken.defect().expect("x₀ alone does not factor");
        let first_break = breaks.first().expect("a defect has a separator");
        assert_eq!(first_break.pair(), (0, 1));
        // The defect retains the fibre: (1,0,0), (0,1,0) and (3,-2,7) all restrict to (1, 2);
        // (0,0,1) sits alone. Its merged-pair count is the witness count of the factoring above.
        assert_eq!(breaks.fibres().len(), 1);
        assert_eq!(
            breaks.fibre_of(0).map(|f| f.members.clone()),
            Some(vec![0, 1, 3])
        );
        assert_eq!(breaks.merged_pairs(), 3);
        assert!(breaks.fibre_of(2).is_none());
        let (left, right) = first_break.residuals();
        assert_ne!(left, right);
        assert_eq!(
            restriction.separating_residuals(&sources[0], &sources[1]),
            Some((left.clone(), right.clone()))
        );
    }

    #[test]
    fn a_port_map_preserves_power() {
        let p = PortMap::new(integer_matrix(&[&[1, 2, 0], &[0, -1, 3]]).unwrap());
        let (pushed, pulled) = p.power_pair(&ints(&[1, 4, -2]), &ints(&[5, 7])).unwrap();
        assert_eq!(pushed, pulled);
    }
}
