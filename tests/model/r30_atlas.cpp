#include "r30_atlas.hpp"
#include <ostream>
namespace holonics::tests {
void write_r30_atlas(std::ostream &out,
                     const event::rederivation_observation &o,
                     const organ::rederivation_workspace &w) {
  out << "owner\tkind\trow\tcolumn\tvalue\tlineage\n";
  for (std::uint8_t side = 0; side < 2; ++side)
    for (std::uint16_t i = 0; i < o.inquiry.matching.injection_count[side];
         ++i) {
      const auto &x = w.injections[side][i];
      out << "matching\tinjection\t" << static_cast<unsigned>(x.subset) << '\t'
          << static_cast<unsigned>(x.forbidden) << '\t'
          << static_cast<unsigned>(x.size) << ':'
          << static_cast<unsigned>(x.image[0]) << ','
          << static_cast<unsigned>(x.image[1]) << ','
          << static_cast<unsigned>(x.image[2]) << ":weight=" << x.weight << '\t'
          << x.lineage.value() << '\n';
    }
  for (const auto &x : w.jacobian)
    out << "matching\tjacobian\t"
        << static_cast<unsigned>(x.alpha) * 7U + x.beta << '\t'
        << static_cast<unsigned>(x.row) * 7U + x.column << '\t' << x.value
        << ":factor=" << x.row_factor << '*' << x.p_evaluation << '*'
        << x.q_evaluation << '\t' << x.lineage.value() << '\n';
  for (const auto &x : w.factors)
    out << "matching\tfactor\t" << static_cast<unsigned>(x.alpha) << '\t'
        << static_cast<unsigned>(x.beta) << '\t' << x.p_leading << ','
        << x.q_leading << ',' << x.row_factor << ":nonzero=" << x.nonzero
        << '\t' << x.lineage.value() << '\n';
  out << "matching\tchanged_duplicate_q\t5\t6\t"
      << o.inquiry.matching.duplicate_q_vandermonde
      << ":dependence_undetermined="
      << o.inquiry.matching.changed_independence_undetermined << '\t'
      << o.inquiry.matching.lineage.value() + 1U << '\n';
  for (std::uint8_t p = 0; p < 4; ++p) {
    const auto &poly = o.inquiry.polygons[p];
    out << "polygon_" << static_cast<unsigned>(p) << "\tpolygon\t0\t-\t"
        << poly.double_area << ',' << poly.boundary << ',' << poly.interior
        << '\t' << poly.lineage.value() << '\n';
    for (std::uint8_t n = 0; n < 5; ++n)
      for (std::uint8_t x = 0; x < 21; ++x)
        for (std::uint8_t y = 0; y < 13; ++y) {
          const auto &point = w.lattice[p][n][x][y];
          if (point.in_box)
            out << "polygon_" << static_cast<unsigned>(p) << "\tlattice_point\t"
                << static_cast<unsigned>(n) << '\t'
                << static_cast<unsigned>(x) * 13U + y << '\t'
                << static_cast<unsigned>(x) << ',' << static_cast<unsigned>(y)
                << ":included=" << point.included
                << ":boundary=" << point.boundary << '\t'
                << point.lineage.value() << '\n';
        }
  }
  const auto &potential = o.inquiry.potential;
  for (std::uint8_t i = 0; i < 4; ++i)
    out << "potential\tlaplacian\t" << static_cast<unsigned>(i / 2U) << '\t'
        << static_cast<unsigned>(i % 2U) << '\t' << potential.matrix[i] << '\t'
        << potential.lineage.value() + i << '\n';
  out << "potential\tdisconnected_foil\t0\t-\tdeterminant="
      << potential.disconnected_determinant
      << ":obstructed=" << potential.disconnected_obstructed << '\t'
      << potential.lineage.value() + 5U << '\n';
  for (const auto &s : w.subsets)
    out << "cover\tsaturation\t" << static_cast<unsigned>(s.columns[0]) << '\t'
        << static_cast<unsigned>(s.columns[3]) << '\t'
        << static_cast<unsigned>(s.witness_row) << ":exact=" << s.saturated
        << '\t' << s.lineage.value() << '\n';
  for (const auto &p : w.pairs)
    out << "cover\tpair\t" << static_cast<unsigned>(p.x) << '\t'
        << static_cast<unsigned>(p.y) << '\t'
        << static_cast<unsigned>(p.witness) << ":left=" << p.left
        << ":right=" << p.right << '\t' << p.lineage.value() << '\n';
  out << "cover\twidth_collision\t1\t-\t"
      << static_cast<unsigned>(o.inquiry.cover.width_one_collision[0]) << ','
      << static_cast<unsigned>(o.inquiry.cover.width_one_collision[1]) << '\t'
      << o.inquiry.cover.lineage.value() + 1U << '\n'
      << "cover\twidth_collision\t2\t-\t"
      << static_cast<unsigned>(o.inquiry.cover.width_two_collision[0]) << ','
      << static_cast<unsigned>(o.inquiry.cover.width_two_collision[1]) << '\t'
      << o.inquiry.cover.lineage.value() + 2U << '\n'
      << "geometry\tself_crossing_foil\t1\t-\tobstructed="
      << o.inquiry.self_crossing_obstructed << '\t'
      << o.inquiry.polygons[1].lineage.value() + 1U << '\n';
  out << "ecology\tdependency\t0\t1\tgeometry_return->potential\t"
      << o.inquiry.theory.lineage.value() << '\n';
}
} // namespace holonics::tests
