#include "r22_artifact.hpp"

#include <ostream>

namespace holonics::tests {
namespace {

template<class Value, std::size_t Capacity>
void sequence(std::ostream& output, const Value (&values)[Capacity], std::size_t used) {
  for (std::size_t slot = 0; slot < used; ++slot) {
    if (slot != 0) { output << ','; }
    output << +values[slot];
  }
}

void factors(std::ostream& output, const organ::cm_graph_receipt& graph) {
  for (std::uint8_t slot = 0; slot < graph.factor_count; ++slot) {
    if (slot != 0) { output << ';'; }
    output << "m" << +graph.factors[slot].multiplicity << ':';
    sequence(output, graph.factors[slot].coefficients,
        static_cast<std::size_t>(graph.factors[slot].degree + 1U));
  }
}

}  // namespace

void write_r22_atlas(
    std::ostream& output, const organ::cm_incidence_receipt& value) noexcept {
  output << "kind\towner\tcoordinate\ttransport\tadmitted\tidentity\tlineage"
      "\tobstruction\texact\n";
  for (std::uint8_t slot = 0; slot < value.returned_translations; ++slot) {
    const auto& translation = value.translations[slot];
    output << "translation\t" << +slot << "\tvalue=";
    sequence(output, translation.value.coefficients, organ::cm_degree_capacity);
    output << ",conjugate=";
    sequence(output, translation.conjugate.coefficients, organ::cm_degree_capacity);
    output << ",norm=";
    sequence(output, translation.norm.coefficients, organ::cm_degree_capacity);
    output << "\tresidue_mask=" << +translation.residue_mask << '\t'
        << translation.norm_one << '\t' << translation.identity.value() << '\t'
        << translation.lineage << "\t0\t" << translation.exact << '\n';
  }
  const organ::cm_graph_receipt* graphs[2]{&value.periodic, &value.window};
  const char* names[2]{"periodic", "window"};
  for (std::uint8_t slot = 0; slot < 2; ++slot) {
    const auto& graph = *graphs[slot];
    output << "graph\t" << names[slot] << "\tedges=" << +graph.edge_count
        << "\ttraces=";
    sequence(output, graph.traces, organ::cm_point_capacity);
    output << ",characteristic=";
    sequence(output, graph.characteristic, organ::cm_characteristic_capacity);
    output << ",factors=";
    factors(output, graph);
    output << '\t' << graph.exact << '\t' << graph.identity.value() << '\t'
        << graph.lineage << "\t0\t" << graph.characteristic_exact << '\n';
    for (std::uint8_t edge = 0; edge < graph.edge_count; ++edge) {
      const auto& item = graph.edges[edge];
      output << "edge\t" << names[slot] << "\t" << +item.source << '-' << +item.target
          << "\tdirection=" << +item.direction << '\t' << item.retained << '\t'
          << item.identity.value() << '\t' << item.lineage << "\t0\t1\n";
    }
  }
  for (std::uint8_t edge = 0; edge < value.projection.lost_count; ++edge) {
    const auto& item = value.projection.lost[edge];
    output << "lost\taperture\t" << +item.source << '-' << +item.target
        << "\tdirection=" << +item.direction << "\t0\t" << item.identity.value()
        << '\t' << item.lineage << "\taperture\t1\n";
  }
  for (std::uint8_t axis = 0; axis < organ::cm_degree_capacity; ++axis) {
    output << "commutator\twindow\taxis=" << +axis << "\tnonzero="
        << +value.scattering.commutator_nonzero[axis] << ",square="
        << +value.scattering.commutator_square[axis] << "\t0\t"
        << value.scattering.identity.value() << '\t' << value.scattering.lineage
        << "\tinterchange\t" << value.scattering.exact << '\n';
  }
  for (const auto& candidate : value.candidates) {
    output << "candidate\t" << static_cast<unsigned>(candidate.kind)
        << "\texpected=" << +candidate.expected << "\treturned=" << +candidate.returned
        << ",contact=" << candidate.contact_exact << ",injective=" << candidate.injective
        << '\t' << candidate.admitted << '\t' << candidate.identity.value() << '\t'
        << candidate.lineage << "\trejected\t1\n";
  }
}

}  // namespace holonics::tests
