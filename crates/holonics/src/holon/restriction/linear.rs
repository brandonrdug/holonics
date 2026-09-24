//! **The linear restriction: a port map as a [`Transition`], and the linear tube.**
//!
//! [definition] A linear restriction `π : ℚⁿ → ℚᵐ` transports `π x` and retains the kernel
//! component `x − σ π x`, where `σ = Vᵀ(VVᵀ)⁻¹(UᵀU)⁻¹Uᵀ` is built from the exact rank
//! factorization `π = U V` (`V` the nonzero rows of the reduced echelon form). Then `π σ π = π`,
//! so the residual lies in `ker π` and is its orthogonal component, and
//! `reopen(π x, x − σ π x) = x` exactly (`Foundation/ContinuingTower.Transition.reopen_apply`).
//! Nothing is required of `π`: a rank-deficient retention (a standing that merges) is admitted.
//!
//! [definition] **Totality.** [`Transition`] is total. A source whose extent is not `n` is outside
//! the declared chart: it transports the empty face and is retained whole as its residual, so
//! `reopen_apply` holds on every input and nothing is silently repaired. Callers that owe an
//! extent check ask [`LinearRestriction::check_source`] first.
//!
//! [definition] **The linear tube** carries the two-chart tower `Coarse ⊑ Fine` of `π` along one
//! step whose transports are `A_fine` and `A_coarse`. Its tube square defect at a fine face `x`
//! (`tube::SquareDefect::route_difference`) is exactly the operator defect
//! `(π A_fine − A_coarse π) x` of [`crate::holon::restriction::SquareDefect`]
//! (`Holon/Restriction.squareDefect`), which is how the two square defects are one object.

use crate::ratio::Rat;

use super::SquareDefect as OperatorDefect;
use super::tower::{
    Tower, TowerFaceOutcome, TowerOutcome, TowerRefusal, TowerRestrictTransition, Transition,
};
use super::tube::{StationedTower, TubeOutcome, TubeRefusal};
use crate::holon::HolonError;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, sub, zeros};

/// [definition] **A linear restriction** with its exact section `σ` (`π σ π = π`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearRestriction {
    map: ExactRatMatrix,
    section: ExactRatMatrix,
}

impl LinearRestriction {
    pub fn new(map: ExactRatMatrix) -> Result<Self, HolonError> {
        let (rows, columns) = (map.rows(), map.columns());
        let factors = map.rank_factorization()?;
        let section = if factors.derived_rank == 0 {
            ExactRatMatrix::zero(columns, rows)?
        } else {
            let u = &factors.left;
            let v = &factors.right;
            let ut = u.transpose()?;
            let vt = v.transpose()?;
            let u_plus = ut.multiply(u)?.inverse()?.multiply(&ut)?;
            let v_right = vt.multiply(&v.multiply(&vt)?.inverse()?)?;
            v_right.multiply(&u_plus)?
        };
        let certified = map.multiply(&section)?.multiply(&map)?;
        if certified != map {
            return Err(HolonError::ConformanceFailed {
                what: "the section of a linear restriction must satisfy π σ π = π",
            });
        }
        Ok(Self { map, section })
    }

    /// `π`.
    pub fn map(&self) -> &ExactRatMatrix {
        &self.map
    }

    /// `σ`, with `π σ π = π`.
    pub fn section(&self) -> &ExactRatMatrix {
        &self.section
    }

    /// Fine extent `n`.
    pub fn source_extent(&self) -> usize {
        self.map.columns()
    }

    /// Coarse extent `m`.
    pub fn target_extent(&self) -> usize {
        self.map.rows()
    }

    /// Refuse a source outside the declared chart.
    pub fn check_source(&self, source: &[Rat]) -> Result<(), HolonError> {
        if source.len() == self.source_extent() {
            Ok(())
        } else {
            Err(HolonError::Shape {
                what: "linear restriction source",
                expected: self.source_extent(),
                found: source.len(),
            })
        }
    }
}

impl Transition for LinearRestriction {
    type Source = Vec<Rat>;
    type Target = Vec<Rat>;
    type Residual = Vec<Rat>;

    fn apply(&self, source: &Vec<Rat>) -> Vec<Rat> {
        self.map.apply(source).unwrap_or_default()
    }

    fn residual(&self, source: &Vec<Rat>) -> Vec<Rat> {
        match self.map.apply(source).and_then(|t| self.section.apply(&t)) {
            Ok(lifted) => sub(source, &lifted),
            Err(_) => source.clone(),
        }
    }

    fn reopen(&self, target: &Vec<Rat>, residual: &Vec<Rat>) -> Vec<Rat> {
        if target.len() != self.target_extent() || residual.len() != self.source_extent() {
            return residual.clone();
        }
        match self.section.apply(target) {
            Ok(lifted) => add(&lifted, residual),
            Err(_) => residual.clone(),
        }
    }
}

/// The two charts of a linear restriction's tower.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LinearChart {
    Coarse,
    Fine,
}

/// The two stations of a linear tube's one step.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LinearStation {
    Earlier,
    Later,
}

/// The two-chart tower `Coarse ⊑ Fine` of a linear restriction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearTower {
    restriction: LinearRestriction,
}

impl LinearTower {
    pub fn new(restriction: LinearRestriction) -> Self {
        Self { restriction }
    }

    pub fn restriction(&self) -> &LinearRestriction {
        &self.restriction
    }

    fn extent(&self, chart: LinearChart) -> usize {
        match chart {
            LinearChart::Coarse => self.restriction.target_extent(),
            LinearChart::Fine => self.restriction.source_extent(),
        }
    }
}

impl Tower for LinearTower {
    type Index = LinearChart;
    type Face = Vec<Rat>;

    fn refines(&self, coarse: &LinearChart, fine: &LinearChart) -> bool {
        coarse <= fine
    }

    fn carries(&self, chart: &LinearChart, face: &Vec<Rat>) -> bool {
        face.len() == self.extent(*chart)
    }

    fn restrict(
        &self,
        coarse: &LinearChart,
        fine: &LinearChart,
        face: &Vec<Rat>,
    ) -> TowerFaceOutcome<Self> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        if !self.carries(fine, face) {
            return Err(TowerRefusal::FaceNotCarried {
                chart: *fine,
                face: face.clone(),
            });
        }
        Ok(if coarse == fine {
            face.clone()
        } else {
            self.restriction.apply(face)
        })
    }
}

/// `Foundation/ContinuingTower.Tower.restrictTransition` at the linear tower: the proper
/// restriction retains the kernel component; restricting a chart to itself drops nothing and
/// retains the empty residual.
impl TowerRestrictTransition for LinearTower {
    type RestrictionResidual = Vec<Rat>;

    fn restriction_residual(
        &self,
        coarse: &LinearChart,
        fine: &LinearChart,
        fine_face: &Vec<Rat>,
    ) -> TowerOutcome<Self, Vec<Rat>> {
        self.restrict(coarse, fine, fine_face)?;
        Ok(if coarse == fine {
            Vec::new()
        } else {
            self.restriction.residual(fine_face)
        })
    }

    fn restriction_reopen(
        &self,
        coarse: &LinearChart,
        fine: &LinearChart,
        coarse_face: &Vec<Rat>,
        residual: &Vec<Rat>,
    ) -> TowerFaceOutcome<Self> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        if !self.carries(coarse, coarse_face) {
            return Err(TowerRefusal::FaceNotCarried {
                chart: *coarse,
                face: coarse_face.clone(),
            });
        }
        Ok(if coarse == fine {
            coarse_face.clone()
        } else {
            self.restriction.reopen(coarse_face, residual)
        })
    }
}

/// [definition] **The linear tube**: the tower of `π` carried one step by `A_fine` and `A_coarse`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearTube {
    tower: LinearTower,
    fine: ExactRatMatrix,
    coarse: ExactRatMatrix,
}

impl LinearTube {
    pub fn new(
        restriction: &ExactRatMatrix,
        fine: &ExactRatMatrix,
        coarse: &ExactRatMatrix,
    ) -> Result<Self, HolonError> {
        let (m, n) = (restriction.rows(), restriction.columns());
        for (what, matrix, extent) in [("A_fine", fine, n), ("A_coarse", coarse, m)] {
            if matrix.rows() != extent || matrix.columns() != extent {
                return Err(HolonError::Shape {
                    what,
                    expected: extent,
                    found: if matrix.rows() != extent {
                        matrix.rows()
                    } else {
                        matrix.columns()
                    },
                });
            }
        }
        Ok(Self {
            tower: LinearTower::new(LinearRestriction::new(restriction.clone())?),
            fine: fine.clone(),
            coarse: coarse.clone(),
        })
    }

    pub fn tower(&self) -> &LinearTower {
        &self.tower
    }

    /// The operator defect `π A_fine − A_coarse π` of this tube's one square.
    pub fn operator_defect(&self) -> Result<OperatorDefect, HolonError> {
        OperatorDefect::new(self.tower.restriction.map(), &self.fine, &self.coarse)
    }

    /// `A_fine`.
    pub fn fine(&self) -> &ExactRatMatrix {
        &self.fine
    }

    /// `A_coarse`.
    pub fn coarse(&self) -> &ExactRatMatrix {
        &self.coarse
    }
}

impl StationedTower for LinearTube {
    type Station = LinearStation;
    type Section = LinearTower;

    fn follows(&self, earlier: &LinearStation, later: &LinearStation) -> bool {
        earlier <= later
    }

    fn section(&self, _station: &LinearStation) -> Option<&LinearTower> {
        Some(&self.tower)
    }

    fn declared_face_population(&self, _chart: &LinearChart, face: &Vec<Rat>) -> usize {
        face.len()
    }

    fn transport(
        &self,
        earlier: &LinearStation,
        later: &LinearStation,
        chart: &LinearChart,
        face: &Vec<Rat>,
    ) -> TubeOutcome<Self, Vec<Rat>> {
        if !self.follows(earlier, later) {
            return Err(TubeRefusal::NotAStep {
                earlier: *earlier,
                later: *later,
            });
        }
        if !self.tower.carries(chart, face) {
            return Err(TubeRefusal::Section(TowerRefusal::FaceNotCarried {
                chart: *chart,
                face: face.clone(),
            }));
        }
        if earlier == later {
            return Ok(face.clone());
        }
        let generator = match chart {
            LinearChart::Coarse => &self.coarse,
            LinearChart::Fine => &self.fine,
        };
        // Unreachable refusal: `carries` fixed the face's extent to the square generator's, so the
        // product composes; the zero face is never returned for a carried face.
        Ok(generator
            .apply(face)
            .unwrap_or_else(|_| zeros(generator.rows())))
    }
}
