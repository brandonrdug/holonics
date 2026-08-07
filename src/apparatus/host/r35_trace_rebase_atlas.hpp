#pragma once

#include <ostream>

#include <holonics/organ/trace_rebase_receipt.hpp>

namespace r35_atlas {
inline void matrix(std::ostream &out,
                   const holonics::organ::exact_matrix2 &matrix) {
  for (const auto value : matrix.value)
    out << value << ',';
}
inline void vector(std::ostream &out, const std::int64_t *values,
                   std::uint8_t count) {
  for (std::uint8_t i = 0; i < count; ++i)
    out << values[i] << ',';
}
inline void states(
    std::ostream &out,
    const holonics::organ::trace_rebase_discovery_receipt &receipt) {
  out << "ordinal\tsource\tseed\tdepth\tpath\tcoordinates\tmatrices\tbranch"
         "\tvalid\tlineage\n";
  for (std::uint16_t i = 0; i < receipt.state_count; ++i) {
    const auto &state = receipt.states[i];
    out << state.ordinal << '\t' << static_cast<unsigned>(state.source) << '\t'
        << static_cast<unsigned>(state.seed) << '\t'
        << static_cast<unsigned>(state.depth) << '\t';
    for (std::uint8_t step = 0; step < state.depth; ++step)
      out << static_cast<unsigned>(state.path[step]) << ',';
    out << '\t';
    vector(out, state.coordinates,
           holonics::organ::trace_rebase_coordinate_count);
    out << '\t';
    for (const auto &value : state.matrices)
      matrix(out, value);
    out << '\t' << state.branch << '\t' << state.valid << '\t'
        << state.lineage.value() << '\n';
  }
}
inline void edges(
    std::ostream &out,
    const holonics::organ::trace_rebase_discovery_receipt &receipt) {
  out << "edge\tstate\tmove\ttarget_coordinates\ttarget_matrices"
         "\tsource_branch\ttarget_branch\tvalid\n";
  for (std::uint16_t i = 0; i < receipt.edge_count; ++i) {
    const auto &edge = receipt.edges[i];
    out << i << '\t' << edge.state << '\t'
        << static_cast<unsigned>(edge.move) << '\t';
    vector(out, edge.target, holonics::organ::trace_rebase_coordinate_count);
    out << '\t';
    for (const auto &value : edge.target_matrices)
      matrix(out, value);
    out << '\t' << edge.source_branch << '\t' << edge.target_branch << '\t'
        << edge.valid << '\n';
  }
}
inline void tangents(
    std::ostream &out,
    const holonics::organ::trace_rebase_discovery_receipt &receipt) {
  out << "edge\tjacobian\tsource_gradient\ttarget_gradient\tsource_basis"
         "\ttransported_basis\tsource_rank\ttarget_rank\ttransported_rank"
         "\tsource_vertical\ttarget_vertical\tobstruction\tchain_exact\n";
  for (std::uint16_t i = 0; i < receipt.edge_count; ++i) {
    const auto &edge = receipt.edges[i];
    out << i << '\t';
    for (const auto &row : edge.jacobian)
      vector(out, row, holonics::organ::trace_rebase_coordinate_count);
    out << '\t';
    vector(out, edge.source_gradient,
           holonics::organ::trace_rebase_coordinate_count);
    out << '\t';
    vector(out, edge.target_gradient,
           holonics::organ::trace_rebase_coordinate_count);
    out << '\t';
    for (const auto &row : edge.tangent)
      vector(out, row, holonics::organ::trace_rebase_coordinate_count);
    out << '\t';
    for (const auto &row : edge.transported)
      vector(out, row, holonics::organ::trace_rebase_coordinate_count);
    out << '\t' << static_cast<unsigned>(edge.source_tangent_rank) << '\t'
        << static_cast<unsigned>(edge.target_tangent_rank) << '\t'
        << static_cast<unsigned>(edge.transported_rank) << '\t'
        << static_cast<unsigned>(edge.source_vertical_rank) << '\t'
        << static_cast<unsigned>(edge.target_vertical_rank) << '\t'
        << static_cast<unsigned>(edge.differential_obstruction) << '\t'
        << edge.chain_exact << '\n';
  }
}
inline void counts(std::ostream &out,
                   const holonics::organ::trace_rebase_counts &value) {
  out << value.regular_regular << ',' << value.regular_branch << ','
      << value.branch_regular << ',' << value.branch_branch;
}
inline void laws(
    std::ostream &out,
    const holonics::organ::trace_rebase_discovery_receipt &receipt) {
  out << "kind\tmove\ttarget\tdegree\tfeatures\trank\tnullity"
         "\tobstruction\tselected\tvalue\n";
  for (std::uint8_t move = 0;
       move < holonics::organ::trace_rebase_move_count; ++move)
    for (std::uint8_t target = 0;
         target < holonics::organ::trace_rebase_coordinate_count; ++target) {
      const auto &candidate = receipt.candidates[
          move * holonics::organ::trace_rebase_coordinate_count + target];
      out << "map\t" << static_cast<unsigned>(move) << '\t'
          << static_cast<unsigned>(target) << '\t'
          << static_cast<unsigned>(candidate.degree) << '\t'
          << static_cast<unsigned>(candidate.features) << '\t'
          << static_cast<unsigned>(candidate.rank) << '\t'
          << static_cast<unsigned>(candidate.nullity) << '\t'
          << static_cast<unsigned>(candidate.obstruction) << '\t'
          << candidate.selected << '\t';
      vector(out, candidate.coefficients,
             holonics::organ::trace_rebase_feature_count);
      out << '\n';
    }
  for (std::uint8_t move = 0;
       move < holonics::organ::trace_rebase_move_count; ++move) {
    out << "transition\t" << static_cast<unsigned>(move)
        << "\t255\t0\t0\t0\t0\t0\t1\t";
    counts(out, receipt.transitions[move]);
    out << '\n';
    for (std::uint8_t source = 0;
         source < holonics::organ::trace_rebase_source_count; ++source) {
      out << "source-transition\t" << static_cast<unsigned>(move) << '\t'
          << static_cast<unsigned>(source) << "\t0\t0\t0\t0\t0\t1\t";
      counts(out, receipt.source_transitions[move][source]);
      out << '\n';
    }
  }
  for (std::uint8_t source = 0;
       source < holonics::organ::trace_rebase_source_count; ++source) {
    out << "source-holdout-rank\t255\t" << static_cast<unsigned>(source)
        << "\t3\t120\t"
        << static_cast<unsigned>(receipt.source_holdout_ranks[source][3])
        << "\t0\t0\t1\t";
    for (std::uint8_t degree = 0; degree <= 3; ++degree)
      out << static_cast<unsigned>(receipt.source_holdout_ranks[source][degree])
          << ',';
    out << '\n';
  }
  for (std::uint8_t i = 0;
       i < holonics::organ::trace_rebase_witness_count; ++i) {
    const auto &witness = receipt.witnesses[i];
    out << "witness\t" << static_cast<unsigned>(witness.kind)
        << "\t255\t0\t0\t0\t0\t0\t" << witness.found << '\t'
        << witness.first << ',' << witness.second << ',';
    vector(out, witness.vector,
           holonics::organ::trace_rebase_coordinate_count);
    vector(out, witness.image,
           holonics::organ::trace_rebase_coordinate_count);
    out << witness.eigenvalue << '\n';
  }
  out << "degree-two\t" << static_cast<unsigned>(receipt.control_move)
      << '\t' << static_cast<unsigned>(receipt.control_target)
      << "\t2\t0\t" << static_cast<unsigned>(receipt.degree_two_rank)
      << "\t0\t" << static_cast<unsigned>(receipt.degree_two_obstruction)
      << "\t0\t-\n";
  for (std::uint8_t deleted = 0;
       deleted < holonics::organ::trace_rebase_coordinate_count; ++deleted)
    out << "coordinate-deleted\t0\t" << static_cast<unsigned>(deleted)
        << "\t3\t"
        << static_cast<unsigned>(receipt.coordinate_deleted_features[deleted])
        << '\t' << static_cast<unsigned>(receipt.coordinate_deleted_rank[deleted])
        << "\t0\t0\t0\t-\n";
  out << "target-deleted\t0\t6\t3\t120\t"
      << static_cast<unsigned>(receipt.target_deleted_rank)
      << "\t0\t0\t0\t-\nrow-deficient\t0\t6\t3\t121\t"
      << static_cast<unsigned>(receipt.row_deficient_rank)
      << "\t0\t0\t0\t-\nheight\t0\t6\t3\t0\t0\t0\t0\t1\t"
      << receipt.coefficient_height << ',' << receipt.coefficient_height_limit
      << '\n';
}
} // namespace r35_atlas
