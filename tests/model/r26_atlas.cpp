#include "r26_artifact.hpp"

#include <ostream>

namespace holonics::tests {
namespace {

void ratio(std::ostream& output, organ::phase_ratio value) {
  output << value.numerator << '/' << value.denominator;
}

void wide(std::ostream& output, const holonics::exact::rational<2>& value) {
  if (value.numerator().negative()) { output << '-'; }
  output << value.numerator().magnitude().limb(1) << ':'
      << value.numerator().magnitude().limb(0) << '/'
      << value.denominator().limb(1) << ':' << value.denominator().limb(0);
}

void phase_case(std::ostream& output, std::uint8_t slot,
    const organ::intrinsic_phase_case_receipt& value) {
  output << "case\t" << +slot << "\tphase_product\t"
      << value.presentation.first << ',' << value.presentation.second
      << "\tV=" << value.vertex_count << ",E=" << value.edge_count
      << ",F=" << value.face_count << ",flags=" << value.flag_count
      << "\ttours=" << +value.tour_count << 'x' << value.lcm
      << "\tprojection_fibers=" << value.projection_fiber_count
      << "\t" << value.lineage.value() << "\t" << value.exact << '\n';
  for (std::uint16_t vertex = 0; vertex < value.vertex_count; ++vertex) {
    const auto& item = value.vertices[vertex];
    output << "vertex\t" << +slot << "\t" << vertex << '\t';
    for (std::uint8_t coordinate = 0; coordinate < 4; ++coordinate) {
      if (coordinate != 0) { output << ','; } ratio(output, item.factor_coordinates[coordinate]);
    }
    output << "\tstar_edges=" << item.star_edges[0] << ',' << item.star_edges[1] << ','
        << item.star_edges[2] << ',' << item.star_edges[3]
        << ";star_faces=" << item.star_faces[0] << ',' << item.star_faces[1] << ','
        << item.star_faces[2] << ',' << item.star_faces[3]
        << ";link=" << item.link_vertices[0] << ',' << item.link_vertices[1] << ','
        << item.link_vertices[2] << ',' << item.link_vertices[3]
        << "\tsuccessor=" << item.successor << ",tour=" << +item.tour << ':'
        << item.tour_position << ",seam=" << static_cast<unsigned>(item.seam)
        << ",section=" << item.section_after[0] << ',' << item.section_after[1] << ','
        << item.section_after[2] << ',' << item.section_after[3] << "\tprojection=";
    ratio(output, item.projected.x); output << ','; ratio(output, item.projected.y);
    output << ",fiber=" << item.projection_fiber << '\t' << item.lineage << "\t1\n";
  }
  for (std::uint16_t edge = 0; edge < value.edge_count; ++edge) {
    const auto& item = value.edges[edge];
    output << "edge\t" << +slot << "\t" << edge << "\taxis=" << +item.axis
        << ",wrap=" << item.wraps << "\t" << item.source << "->" << item.target
        << "\tfaces=" << item.incident_faces[0] << ':'
        << +item.incident_orientation[0] << ',' << item.incident_faces[1] << ':'
        << +item.incident_orientation[1] << "\t-\t" << item.lineage << "\t1\n";
  }
  for (std::uint16_t face = 0; face < value.face_count; ++face) {
    const auto& item = value.faces[face];
    output << "face\t" << +slot << "\t" << face << "\tfilled=" << item.filled
        << "\tvertices=" << item.vertices[0] << ',' << item.vertices[1] << ','
        << item.vertices[2] << ',' << item.vertices[3] << "\tedges="
        << item.edges[0] << ':' << +item.orientations[0] << ',' << item.edges[1] << ':'
        << +item.orientations[1] << ',' << item.edges[2] << ':'
        << +item.orientations[2] << ',' << item.edges[3] << ':'
        << +item.orientations[3] << "\tboundary_closes=" << item.boundary_closes
        << '\t' << item.lineage << "\t1\n";
  }
  for (std::uint16_t flag = 0; flag < value.flag_count; ++flag) {
    const auto& item = value.flags[flag];
    output << "flag\t" << +slot << "\t" << flag << "\tvertex=" << item.vertex
        << "\tedge=" << item.edge << "\tface=" << item.face
        << ",orientation=" << +item.orientation << "\t-\t" << item.lineage << "\t1\n";
  }
  for (std::uint8_t row = 0; row < 4; ++row) {
    for (std::uint8_t column = 0; column < 4; ++column) {
      output << "transition\t" << +slot << "\t" << +row << "->" << +column
          << "\tpopulation=" << value.transition_population[row][column]
          << "\t-\t-\t-\t" << value.lineage.value() << "\t1\n";
    }
  }
  for (std::uint8_t tour = 0; tour < value.tour_count; ++tour) {
    const auto& item = value.tours[tour];
    output << "tour\t" << +slot << "\t" << +tour << "\tfirst=" << item.first_vertex
        << ",length=" << item.length << "\treturn=" << item.return_matrix[0] << ','
        << item.return_matrix[1] << ',' << item.return_matrix[2] << ','
        << item.return_matrix[3] << "\tword_fold=" << item.word_fold
        << "\tdeterminant_one=" << item.determinant_one << '\t'
        << value.lineage.value() << "\t1\n";
  }
}

}  // namespace

void write_r26_atlas(std::ostream& output,
    const event::intrinsic_hypergeometry_observation& value) noexcept {
  output << "kind\tcase\towner\tcoordinate\tincidence\ttransport\treceiver\tlineage\texact\n";
  for (std::uint8_t slot = 0; slot < organ::intrinsic_case_capacity; ++slot) {
    phase_case(output, slot, value.inquiry.cases[slot]);
  }
  phase_case(output, 10, value.changed_case);
  for (std::uint8_t square = 0; square < value.inquiry.supported.square_count; ++square) {
    const auto& item = value.inquiry.supported.squares[square];
    output << "cm_square\t-\t" << +square << "\tdirections=" << +item.directions[0]
        << ',' << +item.directions[1] << "\tvertices=" << +item.vertices[0] << ','
        << +item.vertices[1] << ',' << +item.vertices[2] << ',' << +item.vertices[3]
        << "\tedges=" << +item.edges[0] << ',' << +item.edges[1] << ','
        << +item.edges[2] << ',' << +item.edges[3] << "\tfilled=" << item.filled
        << '\t' << item.lineage << '\t' << item.boundary_closes << '\n';
  }
  for (std::uint8_t term = 0; term < value.inquiry.series.count; ++term) {
    output << "series\t-\tvariation\t" << +term << "\tcoefficient=";
    wide(output, value.inquiry.series.coefficients[term]);
    output << "\trecurrence\tlocal_chart\t" << value.inquiry.series.lineage.value()
        << '\t' << value.inquiry.series.recurrence_exact << '\n';
  }
  output << "control\t-\tarchetype\tequal_hull\tunequal_transport\t"
      << value.inquiry.controls.equal_hull_unequal_transport << "\tseam_receiver\t"
      << value.inquiry.theory.lineage.value() << '\t' << value.inquiry.controls.exact << '\n'
      << "control\t-\tarchetype\tequal_local_population\tunequal_order\t"
      << value.inquiry.controls.equal_local_population_unequal_order << "\tintrinsic\t"
      << value.inquiry.theory.lineage.value() << '\t' << value.inquiry.controls.exact << '\n'
      << "control\t-\tarchetype\tequal_spectrum\tunequal_support\t"
      << value.inquiry.controls.equal_spectrum_unequal_support << "\tcycle_port\t"
      << value.inquiry.theory.lineage.value() << '\t' << value.inquiry.controls.exact << '\n'
      << "control\t-\tarchetype\trechart\tconjugate\t"
      << value.inquiry.controls.conjugate_rechart << "\tlineage_retained\t"
      << value.inquiry.theory.lineage.value() << '\t' << value.inquiry.controls.exact << '\n';
}

}  // namespace holonics::tests
