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

use num_traits::Zero;
use relational_geometry::Rat;
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

    #[test]
    fn a_port_map_preserves_power() {
        let p = PortMap::new(integer_matrix(&[&[1, 2, 0], &[0, -1, 3]]).unwrap());
        let (pushed, pulled) = p.power_pair(&ints(&[1, 4, -2]), &ints(&[5, 7])).unwrap();
        assert_eq!(pushed, pulled);
    }
}
