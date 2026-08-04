#include "r21_artifact.hpp"

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

const char* candidate_name(organ::blind_candidate_kind kind) noexcept {
  switch (kind) {
    case organ::blind_candidate_kind::shell_collapse: return "shell_collapse";
    case organ::blind_candidate_kind::unit_grid: return "unit_grid";
    case organ::blind_candidate_kind::lineage_transpose: return "lineage_transpose";
    case organ::blind_candidate_kind::incidence_product: return "incidence_product";
    case organ::blind_candidate_kind::hankel: return "hankel";
    case organ::blind_candidate_kind::toeplitz: return "toeplitz";
    case organ::blind_candidate_kind::reversed_hankel: return "reversed_hankel";
    case organ::blind_candidate_kind::collapsed_degree: return "collapsed_degree";
  }
  return "unknown";
}

void candidate(std::ostream& output, const organ::blind_candidate_receipt& value,
    std::size_t owner) {
  output << "candidate\t" << owner << '\t' << candidate_name(value.kind) << '\t'
      << "access=" << value.access_complete << ",recurrence=" << value.recurrence_exact
      << ",contact=" << value.contact_exact << ",order=" << value.source_order_exact
      << ",separable=" << value.separable << '\t' << value.admitted << '\t'
      << value.identity.value() << '\t' << value.lineage << "\t-\t-\n";
}

}  // namespace

void write_r21_atlas(std::ostream& output,
    const organ::blind_reconstruction_receipt& value) noexcept {
  output << "kind\towner\tcoordinate\ttransport\tadmitted\tidentity\tlineage"
      "\tobstruction\texact\n";
  output << "code\t" << value.mounted_code.occurrence.value() << "\tdimension="
      << +value.mounted_code.dimension << "\twords=";
  sequence(output, value.code.codewords, value.code.codeword_count);
  output << ",weights=";
  sequence(output, value.code.distance_distribution, organ::blind_distance_capacity);
  output << ",dual=";
  sequence(output, value.code.dual_distribution, organ::blind_distance_capacity);
  output << '\t' << value.code.exact << '\t' << value.code.identity.value() << '\t'
      << value.code.lineage << "\t0\t" << value.code.exact << '\n';
  for (std::size_t pair_slot = 0; pair_slot < organ::blind_pair_capacity; ++pair_slot) {
    const auto& pair = value.pairs[pair_slot];
    output << "pair\t" << pair_slot << "\tdistance=" << +pair.distance << ",shape="
        << +pair.left_size << 'x' << +pair.right_size << "\tcharacteristic_roots=";
    sequence(output, pair.characteristic_roots, organ::blind_distance_capacity);
    output << ",multiplicity=";
    sequence(output, pair.characteristic_multiplicity, organ::blind_distance_capacity);
    output << ",witness_eigenvalue=" << pair.witness_eigenvalue << '\t' << pair.exact << '\t'
        << pair.identity.value() << '\t' << pair.lineage << "\t0\t" << pair.exact << '\n';
    for (std::size_t cell = 0; cell < pair.cell_count; ++cell) {
      output << "cell\t" << pair_slot << "\t" << cell << ":mass=" << pair.population[cell]
          << ",witness=" << pair.witness_vector[cell] << "\tQ=";
      sequence(output, pair.quotient[cell], pair.cell_count);
      output << "\t1\t" << pair.identity.value() << '\t' << pair.lineage
          << "\t0\t" << pair.exact << '\n';
    }
    for (const auto& item : pair.candidates) { candidate(output, item, pair_slot); }
  }
  for (std::size_t slot = 0; slot < organ::blind_moment_case_capacity; ++slot) {
    const auto& moment = value.moments[slot];
    output << "moment\t" << slot << "\tdegree=" << +moment.degree << "\tH0=";
    for (std::size_t row = 0; row < moment.degree; ++row) {
      if (row != 0) { output << ';'; }
      sequence(output, moment.hankel[row], moment.degree);
    }
    output << ",H1=";
    for (std::size_t row = 0; row < moment.degree; ++row) {
      if (row != 0) { output << ';'; }
      sequence(output, moment.shifted[row], moment.degree);
    }
    output << ",pencil=";
    sequence(output, moment.pencil, static_cast<std::size_t>(moment.degree + 1U));
    output << ",newton=";
    sequence(output, moment.newton, static_cast<std::size_t>(moment.degree + 1U));
    output << ",roots=";
    sequence(output, moment.roots, moment.root_count);
    output << ",det=" << moment.hankel_determinant << ",disc=" << moment.discriminant
        << '\t' << moment.separable << '\t' << moment.identity.value() << '\t'
        << moment.lineage << '\t' << static_cast<unsigned>(moment.obstruction) << '\t'
        << moment.exact << '\n';
    if (moment.access_complete) {
      for (const auto& item : moment.candidates) { candidate(output, item, slot + 10U); }
    }
  }
}

}  // namespace holonics::tests
