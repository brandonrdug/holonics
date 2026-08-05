#include "r29_atlas.hpp"

#include <ostream>

namespace holonics::tests {
namespace {

void element(std::ostream& output, const organ::extension_field_element& value) {
  output << value.coefficient[0] << ',' << value.coefficient[1] << ','
      << value.coefficient[2] << ',' << value.coefficient[3];
}

[[nodiscard]] std::int64_t choose2(std::int64_t n) noexcept { return n * (n - 1) / 2; }
[[nodiscard]] std::int64_t choose3(std::int64_t n) noexcept { return n * (n - 1) * (n - 2) / 6; }
[[nodiscard]] std::int64_t choose4(std::int64_t n) noexcept {
  return n * (n - 1) * (n - 2) * (n - 3) / 24;
}

}  // namespace

void write_r29_atlas(std::ostream& output,
    const event::arithmetic_spectral_observation& observation,
    const organ::arithmetic_spectral_workspace& workspace) {
  const auto& inquiry = observation.inquiry;
  output << "owner\tkind\trow\tcolumn\tvalue\tlineage\n";
  for (std::uint8_t tower = 0; tower < organ::arithmetic_base_count; ++tower) {
    const auto& field_tower = inquiry.towers[tower];
    for (std::uint8_t degree = 0; degree < organ::arithmetic_degree_count; ++degree) {
      const auto& field = field_tower.fields[degree];
      output << "field_" << static_cast<unsigned>(tower) << "\tmodulus\t"
          << static_cast<unsigned>(field.degree) << "\t-\t";
      for (std::uint8_t slot = 0; slot <= field.degree; ++slot) {
        if (slot != 0) { output << ','; } output << field.modulus[slot];
      }
      output << "\t" << field.lineage.value() << '\n';
    }
    for (std::uint8_t slot = 0; slot < field_tower.candidate_count; ++slot) {
      const auto& candidate = field_tower.candidates[slot];
      output << "field_" << static_cast<unsigned>(tower) << "\tfield_candidate\t"
          << static_cast<unsigned>(candidate.degree) << '\t' << candidate.code << '\t';
      for (std::uint8_t coefficient = 0; coefficient <= candidate.degree; ++coefficient) {
        if (coefficient != 0) { output << ','; } output << candidate.coefficient[coefficient];
      }
      output << ":divisor=" << candidate.divisor_code << ":irreducible=" << candidate.irreducible
          << '\t' << candidate.lineage.value() << '\n';
    }
  }
  for (std::uint8_t curve = 0; curve < organ::arithmetic_curve_count; ++curve) {
    const auto& source = inquiry.curves[curve];
    output << "curve_" << static_cast<unsigned>(curve) << "\tsource\t0\t-\t"
        << source.source.prime << ',' << source.source.coefficient << ',' << source.discriminant
        << '\t' << source.source.lineage.value() << '\n';
    output << "curve_" << static_cast<unsigned>(curve) << "\tfrobenius\t0\t-\t"
        << source.frobenius.real << ',' << source.frobenius.imaginary << ":points="
        << source.pointwise_points << ":bound=" << source.correspondence_bound
        << '\t' << source.lineage.value() << '\n';
    for (std::uint8_t row = 0; row < 2; ++row) for (std::uint8_t column = 0; column < 2; ++column) {
      output << "curve_" << static_cast<unsigned>(curve) << "\toperator\t"
          << static_cast<unsigned>(row) << '\t' << static_cast<unsigned>(column) << '\t'
          << source.matrix[row][column] << '\t' << source.lineage.value() + row * 2U + column << '\n';
      output << "curve_" << static_cast<unsigned>(curve) << "\tpositive_form\t"
          << static_cast<unsigned>(row) << '\t' << static_cast<unsigned>(column) << '\t'
          << source.positive_pullback[row][column] << '\t'
          << source.lineage.value() + 10U + row * 2U + column << '\n';
      output << "curve_" << static_cast<unsigned>(curve) << "\talternating_form\t"
          << static_cast<unsigned>(row) << '\t' << static_cast<unsigned>(column) << '\t'
          << source.alternating_pullback[row][column] << '\t'
          << source.lineage.value() + 20U + row * 2U + column << '\n';
    }
    output << "curve_" << static_cast<unsigned>(curve) << "\tcharacteristic\t0\t-\t"
        << source.characteristic[2] << ',' << source.characteristic[1] << ','
        << source.characteristic[0] << ":discriminant=" << source.discriminant_characteristic
        << '\t' << source.lineage.value() + 30U << '\n';
    output << "curve_" << static_cast<unsigned>(curve) << "\tzeta_factor\t0\tnumerator\t"
        << "1," << source.characteristic[1] << ',' << source.characteristic[0]
        << '\t' << source.lineage.value() + 40U << '\n';
    output << "curve_" << static_cast<unsigned>(curve) << "\tzeta_factor\t0\tdenominator\t1,"
        << -(1 + source.source.prime) << ',' << source.source.prime
        << '\t' << source.lineage.value() + 41U << '\n';
    std::int64_t zeta[5]{1,0,0,0,0};
    zeta[1] = source.source.prime + 1 - source.power_traces[1];
    zeta[2] = (source.source.prime + 1) * zeta[1];
    for (std::uint8_t degree = 3; degree <= 4; ++degree) {
      zeta[degree] = (source.source.prime + 1) * zeta[degree - 1U] -
          source.source.prime * zeta[degree - 2U];
    }
    const auto b1 = static_cast<std::int64_t>(source.closed_places[0]);
    const auto b2 = static_cast<std::int64_t>(source.closed_places[1]);
    const auto b3 = static_cast<std::int64_t>(source.closed_places[2]);
    const auto b4 = static_cast<std::int64_t>(source.closed_places[3]);
    const std::int64_t euler[5]{1,b1,choose2(b1 + 1) + b2,
        choose3(b1 + 2) + b1 * b2 + b3,
        choose4(b1 + 3) + choose2(b1 + 1) * b2 + choose2(b2 + 1) + b1 * b3 + b4};
    for (std::uint8_t degree = 0; degree < organ::arithmetic_degree_count; ++degree) {
      const auto order = static_cast<unsigned>(degree + 1U);
      output << "curve_" << static_cast<unsigned>(curve) << "\tfixed_total\t" << order
          << "\t-\t" << source.fixed_counts[degree] << '\t'
          << source.lineage.value() + 100U + degree << '\n';
      output << "curve_" << static_cast<unsigned>(curve) << "\ttrace_recurrence\t" << order
          << "\t-\t" << source.power_traces[degree + 1U] << '\t'
          << source.lineage.value() + 110U + degree << '\n';
      output << "curve_" << static_cast<unsigned>(curve) << "\tclosed_place\t" << order
          << "\t-\t" << source.closed_places[degree] << '\t'
          << source.lineage.value() + 120U + degree << '\n';
      output << "curve_" << static_cast<unsigned>(curve) << "\tzeta_series\t" << order
          << "\trational\t" << zeta[degree + 1U] << '\t'
          << source.lineage.value() + 130U + degree << '\n';
      output << "curve_" << static_cast<unsigned>(curve) << "\tzeta_series\t" << order
          << "\teuler\t" << euler[degree + 1U] << '\t'
          << source.lineage.value() + 140U + degree << '\n';
    }
    for (std::uint8_t line = 0; line < 2; ++line) {
      output << "curve_" << static_cast<unsigned>(curve) << "\tprimary_line\t"
          << static_cast<unsigned>(line) << "\t-\t"
          << source.primary_eigenvectors[line][0][0] << ','
          << source.primary_eigenvectors[line][0][1] << ';'
          << source.primary_eigenvectors[line][1][0] << ','
          << source.primary_eigenvectors[line][1][1] << ":lambda="
          << source.primary_eigenvalues[line].real << ',' << source.primary_eigenvalues[line].imaginary
          << '\t' << source.lineage.value() + 200U + line << '\n';
    }
    output << "curve_" << static_cast<unsigned>(curve) << "\tprimary_gluing\t0\t-\t"
        << source.primary_gluing.real << ',' << source.primary_gluing.imaginary << ":norm=4"
        << '\t' << source.lineage.value() + 210U << '\n';
  }
  for (const auto& fixed : workspace.fixed) {
    output << "curve_" << static_cast<unsigned>(fixed.curve) << "\tfixed_x\t"
        << static_cast<unsigned>(fixed.degree) << '\t' << fixed.x_encoding << '\t'
        << fixed.rhs_encoding << ":chi=" << static_cast<int>(fixed.character)
        << ":points=" << static_cast<unsigned>(fixed.point_count)
        << '\t' << fixed.lineage.value() << '\n';
  }
  for (std::uint8_t curve = 0; curve < organ::arithmetic_curve_count; ++curve) {
    for (const auto& candidate : workspace.candidates[curve]) {
      output << "curve_" << static_cast<unsigned>(curve) << "\tcorrespondence_candidate\t"
          << static_cast<int>(candidate.real) << '\t' << static_cast<int>(candidate.imaginary)
          << '\t' << candidate.norm << ":tested=" << candidate.points_tested
          << ":mismatch=" << candidate.mismatches << ":selected=" << candidate.selected
          << '\t' << candidate.lineage.value() << '\n';
    }
  }
  for (const auto& point : workspace.points) {
    if (!point.on_curve) { continue; }
    output << "curve_" << static_cast<unsigned>(point.curve) << "\tpoint_image\t"
        << point.pair_encoding << "\t-\t"; element(output,point.source.x); output << ';';
    element(output,point.source.y); output << "->"; element(output,point.frobenius.x); output << ';';
    element(output,point.frobenius.y); output << "="; element(output,point.gaussian.x); output << ';';
    element(output,point.gaussian.y); output << ":infinity=" << point.source.infinite
        << ":equal=" << point.equal << '\t' << point.lineage.value() << '\n';
  }
  for (std::uint8_t curve = 0; curve < organ::arithmetic_curve_count; ++curve) {
    for (std::uint8_t slot = 0; slot < organ::arithmetic_trace_current_count; ++slot) {
      const auto& current = workspace.trace_currents[curve][slot];
      output << "curve_" << static_cast<unsigned>(curve) << "\ttrace_current\t"
          << static_cast<unsigned>(slot) << "\t-\t";
      for (const auto value : current.coefficient) { output << static_cast<int>(value) << ','; }
      output << "place=" << current.place_side << ":normal=" << current.normalization_side
          << ":spectral=" << current.spectral_side << ":residual=" << current.residual
          << '\t' << current.lineage.value() << '\n';
    }
    for (std::uint16_t slot = 0; slot < organ::arithmetic_norm_current_count; ++slot) {
      const auto& current = workspace.norm_currents[curve][slot];
      output << "curve_" << static_cast<unsigned>(curve) << "\tnorm_current\t"
          << slot << "\t-\t";
      for (const auto value : current.coefficient) { output << static_cast<int>(value) << ','; }
      output << "G=" << current.value.real << ',' << current.value.imaginary
          << ":norm=" << current.norm << '\t' << current.lineage.value() << '\n';
    }
  }
  output << "controls\ttransport\t0\t-\ttwist5=" << inquiry.controls.twist_5_exact
      << ":twist13=" << inquiry.controls.twist_13_exact
      << ":changed=" << inquiry.controls.changed_twist_exact
      << ":even_counts=" << inquiry.controls.even_counts_preserved
      << ":odd_counts=" << inquiry.controls.odd_counts_reversed
      << ":equal_factor=" << inquiry.controls.equal_factor_rechart
      << ":rechart_scale=" << inquiry.controls.rechart_scale
      << ":phase_separated=" << inquiry.controls.gaussian_phase_separated
      << ":source_lineage=" << inquiry.controls.source_lineage_retained
      << ":archimedean=inapplicable\t" << inquiry.controls.lineage.value() << '\n';
}

}  // namespace holonics::tests
