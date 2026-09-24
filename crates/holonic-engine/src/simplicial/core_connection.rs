//! **The simplicial complex as the core complex and its hinge transports as the core connection**
//! (plan phase 4).
//!
//! [definition] [`SimplicialComplex`] is a chart of the core complex through its incidence migration
//! ([`SimplicialIncidenceReceipt::realize`] into [`crate::GradedCausalComplex`], then
//! [`crate::GradedCausalComplex::core_chart`]).
//!
//! [definition] A [`HingeTransportNetwork`] is a connection on the graph whose vertices are hinges
//! and whose edges are its relations. The core [`ConnectionIncidence`] is `ℚ^×`-valued
//! (`Holon/Complex.lean::connectionIncidence`), so it carries exactly the network's **scalar
//! dilation** turns `t ↦ λ t` (`ProjectiveTurn { a, 0, 0, d }`, `λ = a / d`), with `g_e = λ_e`. On
//! such a network the holonomy of a closed walk of along-crossings is the product of the `λ`
//! (`Holon/Complex.lean::walkTransport`), the hinge world's returned parameter is that product times
//! the entered one, and the core curvature face `hol − 1` (`Holon/Complex.lean::cell_curvature`) is
//! the displacement `(returned − entered) / entered` (tested on the engine's own cycle return). A
//! general `PGL(2, ℚ)` turn is a matrix-valued transport the scalar core connection does not carry;
//! it is refused by name ([`CoreChartRefusal::NotAScalarTransport`]) rather than projected. The
//! matrix-valued connection is a core obligation of the Holon plan (phase 4 "NOT DONE").
//!
//! [definition] The same statement for affine cell transports (`holonics::geometry::triangle_holonomy`,
//! the reading behind the fixed machine's `CompiledOrientedCell::holonomy`): scalar dilation
//! transports have holonomy `(∏ λ) · 1`, and for every transport the **determinant line** is a
//! `ℚ^×` connection whose core curvature is `det(hol) − 1`, a gauge-free class function (tested).

use holonics::complex::ConnectionIncidence;
use num_traits::Zero;

use super::{HingeId, HingeTransportId, HingeTransportNetwork, SimplicialComplex};
use crate::algebraic::{CoreCellChart, CoreChartRefusal, GraphChart, SimplicialIncidenceReceipt};

impl SimplicialComplex {
    /// [definition] **The complex as the core complex**: the incidence migration and its chart.
    pub fn core_chart(
        &self,
    ) -> Result<(SimplicialIncidenceReceipt, CoreCellChart), CoreChartRefusal> {
        let receipt = SimplicialIncidenceReceipt::realize(self)?;
        let chart = receipt.incidence.core_chart()?;
        Ok((receipt, chart))
    }
}

impl HingeTransportNetwork {
    /// [definition] **The scalar dilation connection of this network** on the hinges of `complex`:
    /// one core edge per relation (in relation order), `g_e = a / d`. A relation whose turn is not a
    /// dilation is refused with its position.
    pub fn core_connection(
        &self,
        complex: &SimplicialComplex,
    ) -> Result<(GraphChart<HingeId, HingeTransportId>, ConnectionIncidence), CoreChartRefusal>
    {
        let mut transports = Vec::with_capacity(self.relations.len());
        for (at, relation) in self.relations.values().enumerate() {
            let turn = &relation.turn;
            if !turn.b.is_zero() || !turn.c.is_zero() {
                return Err(CoreChartRefusal::NotAScalarTransport { edge: at });
            }
            transports.push(&turn.a / &turn.d);
        }
        let chart = GraphChart::new(
            complex.hinges.keys().copied(),
            self.relations
                .values()
                .map(|relation| (relation.id, relation.source, relation.target)),
        )?;
        let connection = chart.connection(transports)?;
        Ok((chart, connection))
    }
}

#[cfg(test)]
mod tests;
