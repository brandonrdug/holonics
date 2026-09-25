//! **Cells: reflect a square and a cube with the Swing, then join them** (battle test 1).
//!
//! [definition] A fluid's control volumes are **cubical cells** of the grid chart `ℚⁿ`, `n ≤ 3`:
//! a base corner `v` and a set `S` of directions, the box `v + [0,1]^S` ([`GridCell`]). Its oriented
//! boundary is the cubical formula (Lean `Physics/Fluid/Cells.faces`)
//!
//! ```text
//! ∂(v, S) = Σ_{i ∈ S} (−1)^pos(S,i) [ (v + eᵢ, S∖i) − (v, S∖i) ]        pos(S,i) = #{j ∈ S | j < i}
//! ```
//!
//! The **Swing** about an anchor `a` ([`crate::geometry::swing::swing`], `x ↦ 2a − x`) sends a cell
//! to the box whose base is the Swing of its far corner, and reverses each of its `|S|` directions:
//! it carries the cell's orientation with the **hand** `(−1)^|S|` ([`GridCell::swing`], Lean
//! `swingCell`, `swingChain`).
//!
//! | Lean `Physics/Fluid/Cells` | Rust |
//! |---|---|
//! | `Cell`, `faces`, `boundary` | [`GridCell`], [`GridCell::faces`] |
//! | `boundary_faces`, `boundary_boundary`, `incidence_dd`, `gridComplex` | [`CubicalComplex::of_tops`] (`CellComplex::new` checks `∂∂ = 0`) |
//! | `swingCell`, `swingChain`, `boundary_swingChain` | [`GridCell::swing`], [`CubicalComplex::chain_map`] |
//! | `swingCell_cube`, `swingCell_sharedFace`, `swingChain_cube` | [`reflect_across_face`] |
//! | `faces_cube_sharedFace`, `faces_neighbour_sharedFace`, `join_cancels`, `handed_push_cancels`, `joined_shared_face_cancels` | [`Reflection::join`], [`crate::holarchy::Holarchy::block_boundaries`] |
//! | `rawPush_sharedFace`, `square_rawPush_cancels`, `cube_rawPush_uncancelled` | [`Reflection::join`] returning [`GluingDefect::SharedFaceUncancelled`] |
//!
//! [definition] **The join is a Holarchy.** The cube and its Swing image are two Holons, each a
//! cell storing its mass with one port on the shared face, each placed on the cube's own complex;
//! the left embeds into the glued complex by the identity, the right by the Swing with its hand.
//! [`crate::holarchy`]'s `interconnect` checks the gluing: the embeddings commute with the
//! boundaries (the Swing is a chain map), the images meet only on the shared face, and the shared
//! face must enter the two pushed boundaries with opposite signs.

use std::collections::BTreeMap;

use num_traits::{One, Zero};

use crate::geometry::RatVec3;
use crate::geometry::complex::CellComplex;
use crate::geometry::swing::swing;
use crate::holarchy::{CellGluing, CellularMap, Gluing, GluingDefect, Holarchy};
use crate::holon::{Holon, PortHolon};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::vector::matrix;
use crate::ratio::{Rat, integer, rat};

use super::FluidError;

/// The largest grid chart the frame carrier holds.
const MAX_DIMENSION: usize = 3;

/// The component `i` of a point.
#[cfg(test)]
pub(crate) fn component(point: &RatVec3, i: usize) -> &Rat {
    match i {
        0 => &point.x,
        1 => &point.y,
        _ => &point.z,
    }
}

/// The unit step `eᵢ`.
pub(crate) fn unit(i: usize) -> RatVec3 {
    let mut step = RatVec3::zero();
    match i {
        0 => step.x = Rat::one(),
        1 => step.y = Rat::one(),
        _ => step.z = Rat::one(),
    }
    step
}

/// The far-corner offset `1_S`.
pub(crate) fn indicator(directions: &[usize]) -> RatVec3 {
    directions
        .iter()
        .fold(RatVec3::zero(), |sum, i| sum.add(&unit(*i)))
}

/// `(−1)^k`.
pub(crate) fn parity(k: usize) -> i64 {
    if k % 2 == 0 { 1 } else { -1 }
}

/// [definition] **A cubical cell** `v + [0,1]^S` of the grid chart (Lean `Physics/Fluid/Cells.Cell`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GridCell {
    base: RatVec3,
    directions: Vec<usize>,
}

impl GridCell {
    /// A cell; its directions must be distinct, increasing and below `3`.
    pub fn new(base: RatVec3, directions: Vec<usize>) -> Result<Self, FluidError> {
        if let Some(direction) = directions.iter().find(|i| **i >= MAX_DIMENSION) {
            return Err(FluidError::Direction {
                direction: *direction,
            });
        }
        if directions.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(FluidError::Directions);
        }
        Ok(Self { base, directions })
    }

    /// The unit cube `[0,1]ⁿ` of the chart of dimension `n ≤ 3` (Lean `cube`).
    pub fn unit_cube(dimension: usize) -> Result<Self, FluidError> {
        Self::new(RatVec3::zero(), (0..dimension).collect())
    }

    pub fn base(&self) -> &RatVec3 {
        &self.base
    }

    pub fn directions(&self) -> &[usize] {
        &self.directions
    }

    /// The degree `|S|`.
    pub fn degree(&self) -> usize {
        self.directions.len()
    }

    /// The far corner `v + 1_S`.
    pub fn far_corner(&self) -> RatVec3 {
        self.base.add(&indicator(&self.directions))
    }

    /// The centroid `v + ½·1_S`.
    pub fn centroid(&self) -> RatVec3 {
        self.base
            .add(&indicator(&self.directions).scale(&rat(1, 2)))
    }

    /// [definition] **The oriented faces** `(v + eᵢ, S∖i)` with `+(−1)^pos(S,i)` and `(v, S∖i)` with
    /// `−(−1)^pos(S,i)` (Lean `faces`).
    pub fn faces(&self) -> Vec<(GridCell, i64)> {
        let mut faces = Vec::with_capacity(2 * self.degree());
        for (position, i) in self.directions.iter().enumerate() {
            let rest: Vec<usize> = self.directions.iter().copied().filter(|j| j != i).collect();
            let sign = parity(position);
            faces.push((
                GridCell {
                    base: self.base.add(&unit(*i)),
                    directions: rest.clone(),
                },
                sign,
            ));
            faces.push((
                GridCell {
                    base: self.base.clone(),
                    directions: rest,
                },
                -sign,
            ));
        }
        faces
    }

    /// [definition] **The Swing of the cell** about `anchor` (Lean `swingCell`, `swingChain`): the
    /// box whose base is the Swing of the far corner, with the hand `(−1)^|S|`.
    pub fn swing(&self, anchor: &RatVec3) -> (GridCell, i64) {
        (
            GridCell {
                base: swing(anchor, &self.far_corner()),
                directions: self.directions.clone(),
            },
            parity(self.degree()),
        )
    }

    fn key(&self) -> (Rat, Rat, Rat, Vec<usize>) {
        (
            self.base.x.clone(),
            self.base.y.clone(),
            self.base.z.clone(),
            self.directions.clone(),
        )
    }
}

/// [definition] **The finite cubical complex of a set of top cells** (Lean `gridComplex`): every
/// degree from the vertices to the tops, the cells met by the boundaries, and the grid incidence as
/// the boundary matrices of a [`CellComplex`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CubicalComplex {
    cells: Vec<Vec<GridCell>>,
    complex: CellComplex,
}

impl CubicalComplex {
    /// [proved-derived; implemented-exact] **Build the complex of the tops**, closing them under
    /// faces; [`CellComplex::new`] checks `∂_k ∂_(k+1) = 0` (Lean `boundary_faces`,
    /// `incidence_dd`). The tops must share one degree `d ≥ 1`.
    pub fn of_tops(tops: &[GridCell]) -> Result<Self, FluidError> {
        let d = tops.first().map_or(0, GridCell::degree);
        if d == 0 || tops.iter().any(|top| top.degree() != d) {
            return Err(FluidError::NotATopCell {
                what: "set (the tops must share one degree at least one)",
            });
        }
        let mut cells: Vec<Vec<GridCell>> = vec![Vec::new(); d + 1];
        for top in tops {
            if !cells[d].contains(top) {
                cells[d].push(top.clone());
            }
        }
        for k in (1..=d).rev() {
            let mut lower = Vec::new();
            for cell in &cells[k] {
                for (face, _) in cell.faces() {
                    if !lower.contains(&face) {
                        lower.push(face);
                    }
                }
            }
            cells[k - 1] = lower;
        }
        let index: Vec<BTreeMap<_, usize>> = cells
            .iter()
            .map(|degree| {
                degree
                    .iter()
                    .enumerate()
                    .map(|(i, cell)| (cell.key(), i))
                    .collect()
            })
            .collect();
        let mut boundaries = Vec::with_capacity(d);
        for k in 1..=d {
            let mut entries = vec![vec![Rat::zero(); cells[k].len()]; cells[k - 1].len()];
            for (column, cell) in cells[k].iter().enumerate() {
                for (face, sign) in cell.faces() {
                    let row = index[k - 1][&face.key()];
                    entries[row][column] += integer(sign);
                }
            }
            boundaries.push(ExactRatMatrix::shaped(
                cells[k - 1].len(),
                cells[k].len(),
                entries,
            )?);
        }
        let counts = cells.iter().map(Vec::len).collect();
        let complex = CellComplex::new(counts, boundaries)?;
        Ok(Self { cells, complex })
    }

    pub fn complex(&self) -> &CellComplex {
        &self.complex
    }

    pub fn dimension(&self) -> usize {
        self.cells.len() - 1
    }

    /// The cells of one degree, in the complex's order.
    pub fn cells(&self, degree: usize) -> &[GridCell] {
        self.cells.get(degree).map_or(&[], Vec::as_slice)
    }

    /// The index of a cell in its degree.
    pub fn index(&self, cell: &GridCell) -> Option<usize> {
        self.cells
            .get(cell.degree())?
            .iter()
            .position(|other| other == cell)
    }

    /// [definition] **A cellular map from another cubical complex** into this one, degree by
    /// degree: each cell goes to `map(cell)` with its gauge (Lean `CellEmbedding`). Refused when an
    /// image is not a cell of this complex.
    pub fn chain_map(
        &self,
        own: &CubicalComplex,
        map: impl Fn(&GridCell) -> (GridCell, i64),
    ) -> Result<CellularMap, FluidError> {
        let mut degrees = Vec::with_capacity(own.cells.len());
        for (k, own_cells) in own.cells.iter().enumerate() {
            let mut images = Vec::with_capacity(own_cells.len());
            for cell in own_cells {
                let (image, gauge) = map(cell);
                let row = self.index(&image).ok_or(FluidError::NotATopCell {
                    what: "image (it is not a cell of the glued complex)",
                })?;
                images.push((row, gauge));
            }
            degrees.push(matrix(
                self.cells(k).len(),
                own_cells.len(),
                |row, column| {
                    let (image, gauge) = images[column];
                    if image == row {
                        integer(gauge)
                    } else {
                        Rat::zero()
                    }
                },
            )?);
        }
        Ok(CellularMap::new(degrees)?)
    }
}

/// [definition] **A cell as a Holon**: it stores its mass (a unit storage form, no internal
/// resistance) and exchanges it through one external port, the face flux on its port face
/// (`Holon/Conformance.mediumHolon` with one input), placed on `complex` with the oriented
/// interior chain `[orientation]`.
fn mass_cell(
    complex: CellComplex,
    orientation: Rat,
    port_face: usize,
) -> Result<Holon, FluidError> {
    let one = ExactRatMatrix::new(vec![vec![Rat::one()]])?;
    let port_holon = PortHolon::medium(
        &ExactRatMatrix::zero(1, 1)?,
        &ExactRatMatrix::zero(1, 1)?,
        SymmetricForm::from_rows(vec![vec![Rat::one()]]).map_err(crate::holon::HolonError::from)?,
        &one,
        false,
    )?;
    Ok(Holon::new(port_holon)?
        .with_complex(complex, None)
        .with_interior(vec![orientation])?
        .with_port_faces(vec![port_face])?)
}

/// [definition] **A reflection across a face and its declared join**: the unit cube and its Swing
/// image about the centre of the face `x_i = 1`, as two mass cells, and the gluing of the two into
/// the complex of the cube and its neighbour.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reflection {
    /// The anchor: the centre of the shared face.
    pub anchor: RatVec3,
    /// The cube's own complex, carried by both constituents.
    pub own: CubicalComplex,
    /// The complex of the cube and its neighbour.
    pub glued: CubicalComplex,
    /// The cube.
    pub left: Holon,
    /// Its Swing image.
    pub right: Holon,
    /// The shared port on the shared face, the glued complex and the two embeddings.
    pub gluing: Gluing,
    /// The shared face's index among the glued faces.
    pub shared_face: usize,
}

impl Reflection {
    /// [proved-derived; implemented-exact] **Join the cube to its Swing image** (Lean
    /// `joined_shared_face_cancels`, through `Holarchy/Join.interconnect`): a Holarchy exactly when
    /// the shared face cancels, otherwise [`GluingDefect::SharedFaceUncancelled`] (Lean
    /// `rawPush_sharedFace`).
    pub fn join(&self) -> Result<Holarchy, GluingDefect> {
        self.left.interconnect(&self.right, &self.gluing)
    }
}

/// [proved-derived; implemented-exact] **Reflect the unit cube of dimension `n ≤ 3` across its
/// face `x_i = 1`** (Lean `swingCell_cube`, `swingCell_sharedFace`, `swingChain_cube`).
///
/// The anchor is the face's centre. The right constituent is the cube's copy, embedded by the
/// Swing with its hand `(−1)^k` on `k`-cells (Lean `boundary_swingChain`: a chain map). Its interior
/// orientation is `(−1)ⁿ` when `corrected` (so the pushed interior is the neighbour's own positive
/// orientation), and `1` for the raw push.
pub fn reflect_across_face(
    dimension: usize,
    direction: usize,
    corrected: bool,
) -> Result<Reflection, FluidError> {
    if dimension == 0 || direction >= dimension {
        return Err(FluidError::Direction { direction });
    }
    let cube = GridCell::unit_cube(dimension)?;
    let others: Vec<usize> = (0..dimension).filter(|j| *j != direction).collect();
    let shared = GridCell::new(unit(direction), others.clone())?;
    let anchor = unit(direction).add(&indicator(&others).scale(&rat(1, 2)));
    let (neighbour, _) = cube.swing(&anchor);
    let own = CubicalComplex::of_tops(std::slice::from_ref(&cube))?;
    let glued = CubicalComplex::of_tops(&[cube.clone(), neighbour])?;
    let left_map = glued.chain_map(&own, |cell| (cell.clone(), 1))?;
    let right_map = glued.chain_map(&own, |cell| cell.swing(&anchor))?;
    let own_face = own.index(&shared).ok_or(FluidError::NotATopCell {
        what: "shared face (it is not a face of the cube)",
    })?;
    let shared_face = glued.index(&shared).ok_or(FluidError::NotATopCell {
        what: "shared face (it is not a face of the glued complex)",
    })?;
    let hand = if corrected {
        integer(parity(dimension))
    } else {
        Rat::one()
    };
    let left = mass_cell(own.complex().clone(), Rat::one(), own_face)?;
    let right = mass_cell(own.complex().clone(), hand, own_face)?;
    let gluing = Gluing::at_ports(vec![(0, 0)])?.with_cells(CellGluing::new(
        glued.complex().clone(),
        None,
        (left_map, right_map),
    ));
    Ok(Reflection {
        anchor,
        own,
        glued,
        left,
        right,
        gluing,
        shared_face,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::holarchy::{Block, Grain};

    fn point(x: i64, y: i64, z: i64) -> RatVec3 {
        RatVec3::from_i64(x, y, z)
    }

    /// A formal sum of cells with like terms collected and zero terms dropped.
    fn collect(chain: &[(GridCell, i64)]) -> Vec<(GridCell, i64)> {
        let mut sum: Vec<(GridCell, i64)> = Vec::new();
        for (cell, coefficient) in chain {
            match sum.iter_mut().find(|(other, _)| other == cell) {
                Some((_, value)) => *value += coefficient,
                None => sum.push((cell.clone(), *coefficient)),
            }
        }
        sum.retain(|(_, value)| *value != 0);
        sum
    }

    /// The chain `∂` of a formal sum of cells, collected by cell.
    fn boundary_of(chain: &[(GridCell, i64)]) -> Vec<(GridCell, i64)> {
        let faces: Vec<(GridCell, i64)> = chain
            .iter()
            .flat_map(|(cell, coefficient)| {
                cell.faces()
                    .into_iter()
                    .map(move |(face, sign)| (face, coefficient * sign))
            })
            .collect();
        collect(&faces)
    }

    /// Lean `Physics/Fluid/Cells.boundary_faces`, `incidence_dd`: `∂∂ = 0` for a cube of each
    /// dimension and for the joined pair; the complexes are accepted by `CellComplex::new`.
    #[test]
    fn the_boundary_of_a_boundary_is_zero() {
        for dimension in 1..=3 {
            let cube = GridCell::unit_cube(dimension).unwrap();
            assert!(boundary_of(&cube.faces()).is_empty());
            let complex = CubicalComplex::of_tops(std::slice::from_ref(&cube)).unwrap();
            let counts: Vec<usize> = (0..=dimension).map(|k| complex.cells(k).len()).collect();
            let expected: Vec<usize> = match dimension {
                1 => vec![2, 1],
                2 => vec![4, 4, 1],
                _ => vec![8, 12, 6, 1],
            };
            assert_eq!(counts, expected);
        }
        let reflection = reflect_across_face(3, 0, true).unwrap();
        let counts: Vec<usize> = (0..=3).map(|k| reflection.glued.cells(k).len()).collect();
        assert_eq!(counts, vec![12, 20, 11, 2]);
    }

    /// Lean `boundary_swingChain`: the Swing commutes with `∂` once each `k`-cell carries the hand
    /// `(−1)^k`, for every cell of the cube and an arbitrary anchor.
    #[test]
    fn the_swing_is_a_chain_map_with_its_hand() {
        let anchor = RatVec3::new(rat(3, 2), rat(-1, 3), integer(2));
        let cube = CubicalComplex::of_tops(&[GridCell::unit_cube(3).unwrap()]).unwrap();
        for k in 1..=3 {
            for cell in cube.cells(k) {
                let (image, hand) = cell.swing(&anchor);
                let lhs = boundary_of(&[(image, hand)]);
                let pushed: Vec<(GridCell, i64)> = cell
                    .faces()
                    .into_iter()
                    .map(|(face, sign)| {
                        let (image, hand) = face.swing(&anchor);
                        (image, sign * hand)
                    })
                    .collect();
                let rhs = collect(&pushed);
                assert!(!lhs.is_empty());
                assert_eq!(lhs.len(), rhs.len());
                for term in &lhs {
                    assert!(rhs.contains(term));
                }
            }
        }
    }

    /// Lean `swingCell_cube`, `swingCell_sharedFace`, `swingChain_cube`: the Swing about the centre
    /// of the face `x_i = 1` sends the cube to its neighbour with the hand `(−1)ⁿ` and fixes the
    /// face.
    #[test]
    fn the_swing_about_a_face_centre_reflects_the_cube_to_its_neighbour() {
        let reflection = reflect_across_face(3, 1, true).unwrap();
        let cube = GridCell::unit_cube(3).unwrap();
        let (image, hand) = cube.swing(&reflection.anchor);
        assert_eq!(image, GridCell::new(point(0, 1, 0), vec![0, 1, 2]).unwrap());
        assert_eq!(hand, -1);
        let face = GridCell::new(point(0, 1, 0), vec![0, 2]).unwrap();
        assert_eq!(face.swing(&reflection.anchor), (face.clone(), 1));
        let square = GridCell::unit_cube(2).unwrap();
        let square_anchor = RatVec3::new(integer(1), rat(1, 2), Rat::zero());
        assert_eq!(
            square.swing(&square_anchor),
            (GridCell::new(point(1, 0, 0), vec![0, 1]).unwrap(), 1)
        );
    }

    /// Lean `joined_shared_face_cancels`, `square_rawPush_cancels` (composing
    /// `Holarchy/View.shared_face_cancels`): the square and its Swing image join, the shared edge
    /// enters the two blocks' boundaries with opposite unit signs and is silent in the whole, and
    /// the whole's flux is the two cells' own fluxes.
    #[test]
    fn a_reflected_square_joins_and_its_shared_edge_cancels_once() {
        for corrected in [false, true] {
            let reflection = reflect_across_face(2, 0, corrected).unwrap();
            let holarchy = reflection
                .join()
                .expect("the square's Swing keeps its hand");
            let grain = Grain::new(vec![Block::from([0]), Block::from([1])]);
            let boundaries = holarchy.block_boundaries(&grain).unwrap();
            let f = reflection.shared_face;
            assert!(!boundaries[0][f].is_zero());
            assert_eq!(boundaries[0][f], -boundaries[1][f].clone());
            // Every other edge lies in exactly one block.
            for edge in 0..reflection.glued.cells(1).len() {
                if edge != f {
                    assert!(boundaries[0][edge].is_zero() || boundaries[1][edge].is_zero());
                }
            }
            let mut current = vec![Rat::zero(); reflection.glued.cells(1).len()];
            current[f] = integer(5);
            let split = holarchy.flux(&current).unwrap();
            assert!(split.whole.is_zero());
            assert_eq!(split.left, -split.right.clone());
            let current: Vec<Rat> = (0..reflection.glued.cells(1).len() as i64)
                .map(|e| rat(e * e - 3, e + 1))
                .collect();
            let split = holarchy.flux(&current).unwrap();
            assert_eq!(split.whole, split.left + split.right);
        }
    }

    /// Lean `cube_rawPush_uncancelled`, `joined_shared_face_cancels`: the cube's raw Swing image is
    /// refused with the shared face uncancelled (both coefficients `+1`), and the hand-corrected
    /// image joins with the shared face cancelling once.
    #[test]
    fn a_reflected_cube_joins_only_with_its_hand() {
        let raw = reflect_across_face(3, 2, false).unwrap();
        match raw.join() {
            Err(GluingDefect::SharedFaceUncancelled { left, right, .. }) => {
                assert_eq!(left, right);
                assert!(!left.is_zero());
            }
            other => panic!("the raw push must leave the shared face uncancelled: {other:?}"),
        }
        let corrected = reflect_across_face(3, 2, true).unwrap();
        let holarchy = corrected.join().unwrap();
        let grain = Grain::new(vec![Block::from([0]), Block::from([1])]);
        let boundaries = holarchy.block_boundaries(&grain).unwrap();
        let f = corrected.shared_face;
        assert_eq!(boundaries[0][f], -boundaries[1][f].clone());
        let shared_faces = (0..corrected.glued.cells(2).len())
            .filter(|face| !boundaries[0][*face].is_zero() && !boundaries[1][*face].is_zero())
            .count();
        assert_eq!(shared_faces, 1);
        assert!(holarchy.whole_interior().unwrap().iter().all(Rat::is_one));
    }
}
