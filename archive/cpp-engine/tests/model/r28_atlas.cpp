#include "r28_atlas.hpp"

#include <ostream>

namespace holonics::tests {
namespace {

void polynomial(std::ostream& out, const char* owner, const char* kind,
    const organ::parameter_polynomial& value, std::uint64_t lineage) {
  for (std::uint8_t degree = 0; degree <= value.degree; ++degree) {
    out << owner << '\t' << kind << '\t' << static_cast<unsigned>(degree) << "\t-\t"
        << value.coefficients[degree] << '\t' << lineage << '\n';
  }
}

void factor_rows(std::ostream& out, std::uint8_t index,
    const organ::hodge_factor_receipt& factor) {
  const char* owners[2]{"factor_0","factor_1"}; const auto* owner = owners[index];
  for (std::uint8_t slot = 0; slot < factor.mounted.term_count; ++slot) {
    const auto& term = factor.mounted.terms[slot];
    out << owner << "\tsource_term\t" << static_cast<unsigned>(slot) << "\t-\t"
        << term.coefficient << ':' << static_cast<unsigned>(term.parameter_power) << ':'
        << static_cast<unsigned>(term.x_power) << ':' << static_cast<unsigned>(term.y_power)
        << '\t' << factor.mounted.lineage.value() << '\n';
  }
  for (std::uint8_t root = 0; root < 3; ++root) {
    out << owner << "\troot\t" << static_cast<unsigned>(root) << "\t-\t"
        << factor.roots[root].root.constant << '+' << factor.roots[root].root.parameter
        << "z\t" << factor.roots[root].lineage.value() << '\n';
  }
  polynomial(out, owner, "discriminant", factor.discriminant, factor.lineage.value());
  polynomial(out, owner, "denominator", factor.denominator, factor.lineage.value());
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      out << owner << "\tconnection\t" << static_cast<unsigned>(row) << '\t'
          << static_cast<unsigned>(column) << '\t' << factor.connection[row][column].constant
          << '+' << factor.connection[row][column].parameter << "z\t"
          << factor.lineage.value() << '\n';
    }
  }
}

void translation_rows(std::ostream& out, std::uint8_t index,
    const organ::hodge_translation_receipt& map) {
  const char* owners[4]{"translation_0","translation_1","translation_2","translation_3"};
  const auto* owner = owners[index];
  polynomial(out, owner, "root", map.root, map.lineage.value());
  polynomial(out, owner, "other_first", map.other_first, map.lineage.value());
  polynomial(out, owner, "other_second", map.other_second, map.lineage.value());
  polynomial(out, owner, "kappa", map.kappa, map.lineage.value());
  polynomial(out, owner, "x_numerator_0", map.x_numerator[0], map.lineage.value());
  polynomial(out, owner, "x_numerator_1", map.x_numerator[1], map.lineage.value());
  polynomial(out, owner, "x_denominator_0", map.x_denominator[0], map.lineage.value());
  polynomial(out, owner, "x_denominator_1", map.x_denominator[1], map.lineage.value());
  polynomial(out, owner, "y_scale", map.y_scale, map.lineage.value());
  for (std::uint8_t slot = 0; slot < 6; ++slot) {
    out << owner << "\tgraph_class\t" << static_cast<unsigned>(slot) << "\t-\t"
        << map.graph_class[slot] << '\t' << map.lineage.value() << '\n';
  }
  out << owner << "\tcertificates\t0\t0\t" << map.curve_identity << ':' << map.involution
      << ':' << map.differential_pullback_identity << ':' << map.distinct_support
      << ':' << map.h1_identity << '\t' << map.lineage.value() << '\n';
}

void blowup_rows(std::ostream& out, std::uint8_t index,
    const organ::hodge_blowup_receipt& blowup) {
  const char* owners[2]{"blowup_0","blowup_1"}; const auto* owner = owners[index];
  for (std::uint8_t row = 0; row < 7; ++row) {
    out << owner << "\texceptional\t" << static_cast<unsigned>(row) << "\t-\t"
        << blowup.exceptional[row] << '\t' << blowup.lineage.value() << '\n';
    for (std::uint8_t column = 0; column < 7; ++column) {
      out << owner << "\tpairing\t" << static_cast<unsigned>(row) << '\t'
          << static_cast<unsigned>(column) << '\t' << blowup.pairing[row][column]
          << '\t' << blowup.lineage.value() << '\n';
    }
    for (std::uint8_t column = 0; column < 6; ++column) {
      out << owner << "\tpullback\t" << static_cast<unsigned>(row) << '\t'
          << static_cast<unsigned>(column) << '\t' << blowup.pullback[row][column]
          << '\t' << blowup.lineage.value() << '\n';
    }
  }
  for (std::uint8_t row = 0; row < 6; ++row) {
    for (std::uint8_t column = 0; column < 7; ++column) {
      out << owner << "\tpushforward\t" << static_cast<unsigned>(row) << '\t'
          << static_cast<unsigned>(column) << '\t' << blowup.pushforward[row][column]
          << '\t' << blowup.lineage.value() << '\n';
    }
  }
  for (std::uint8_t graph = 0; graph < 4; ++graph) {
    for (std::uint8_t slot = 0; slot < 7; ++slot) {
      out << owner << "\tstrict_" << static_cast<unsigned>(graph) << '\t'
          << static_cast<unsigned>(slot) << "\t-\t" << blowup.strict_classes[graph][slot]
          << '\t' << blowup.lineage.value() << '\n';
    }
    out << owner << "\tsupport_" << static_cast<unsigned>(graph) << "\t0\t0\t"
        << blowup.through_center[graph] << ':' << blowup.self_intersections[graph]
        << '\t' << blowup.lineage.value() << '\n';
  }
  out << owner << "\tresidual\t0\t0\t" << blowup.pull_push_identity << ':'
      << blowup.projection_formula << ':' << blowup.mapping_cone_residual_exact << ':'
      << blowup.all_push_to_graph << '\t' << blowup.lineage.value() << '\n';
}

}  // namespace

void write_r28_atlas(std::ostream& out,
    const event::hodge_realization_observation& observation) {
  const auto& value = observation.inquiry;
  out << "owner\tkind\trow\tcolumn\tvalue\tlineage\n";
  for (std::uint8_t factor = 0; factor < 2; ++factor) { factor_rows(out, factor, value.factors[factor]); }
  for (std::uint8_t row = 0; row < 6; ++row) {
    out << "product\tbasis\t" << static_cast<unsigned>(row) << "\t-\t"
        << value.product.basis[row].value() << '\t' << value.product.lineage.value() << '\n'
        << "product\tpolarization\t" << static_cast<unsigned>(row) << "\t-\t"
        << value.product.polarization[row] << '\t' << value.product.lineage.value() << '\n';
    for (std::uint8_t column = 0; column < 6; ++column) {
      out << "product\tcup\t" << static_cast<unsigned>(row) << '\t'
          << static_cast<unsigned>(column) << '\t' << value.product.cup[row][column]
          << '\t' << value.product.lineage.value() << '\n'
          << "product\tconnection_t\t" << static_cast<unsigned>(row) << '\t'
          << static_cast<unsigned>(column) << '\t' << value.product.connection_t[row][column].constant
          << '+' << value.product.connection_t[row][column].parameter << "t\t"
          << value.product.lineage.value() << '\n'
          << "product\tconnection_u\t" << static_cast<unsigned>(row) << '\t'
          << static_cast<unsigned>(column) << '\t' << value.product.connection_u[row][column].constant
          << '+' << value.product.connection_u[row][column].parameter << "u\t"
          << value.product.lineage.value() << '\n';
    }
  }
  for (std::uint8_t slot = 0; slot < value.product.f1_rank; ++slot) {
    out << "product\tfiltration_f1\t" << static_cast<unsigned>(slot) << "\t-\t"
        << static_cast<unsigned>(value.product.f1_basis[slot]) << '\t'
        << value.product.lineage.value() << '\n';
  }
  out << "product\tfiltration_f2\t0\t-\t" << static_cast<unsigned>(value.product.f2_basis[0])
      << '\t' << value.product.lineage.value() << '\n';
  for (std::uint8_t slot = 0; slot < 6; ++slot) {
    out << "locus\tgraph\t" << static_cast<unsigned>(slot) << "\t-\t"
        << value.cycles.locus.graph_class[slot] << '\t' << value.cycles.locus.lineage.value() << '\n'
        << "locus\tprimitive\t" << static_cast<unsigned>(slot) << "\t-\t"
        << value.cycles.locus.primitive_class[slot] << '\t' << value.cycles.locus.lineage.value() << '\n';
  }
  out << "locus\tjet\t0\t1\t" << value.cycles.locus.quotient_obstruction[0] << ':'
      << value.cycles.locus.quotient_obstruction[1] << ':' << value.cycles.locus.multiplicity
      << '\t' << value.cycles.locus.lineage.value() << '\n';
  for (std::uint8_t translation = 0; translation < 4; ++translation) {
    translation_rows(out, translation, value.cycles.translations[translation]);
  }
  for (std::uint8_t generator = 0; generator < 7; ++generator) {
    for (std::uint8_t slot = 0; slot < 6; ++slot) {
      out << "cycles\tgenerator_" << static_cast<unsigned>(generator) << '\t'
          << static_cast<unsigned>(slot) << "\t-\t"
          << value.cycles.generators[generator].cycle_class[slot] << '\t'
          << value.cycles.generators[generator].lineage.value() << '\n';
    }
    out << "cycles\tgenerator_support\t" << static_cast<unsigned>(generator) << "\t-\t"
        << value.cycles.generators[generator].support_mask << ':'
        << value.cycles.generators[generator].effective << '\t'
        << value.cycles.generators[generator].lineage.value() << '\n';
  }
  for (std::uint8_t target = 0; target < 3; ++target) {
    const auto& fiber = value.cycles.fibers[target];
    out << "fiber_" << static_cast<unsigned>(target) << "\tsummary\t0\t0\t"
        << fiber.enumerated << ':' << static_cast<unsigned>(fiber.realizer_count) << ':'
        << static_cast<unsigned>(fiber.effective_count) << ':' << fiber.integral_member << ':'
        << fiber.outside_image << '\t' << fiber.lineage.value() << '\n';
    for (std::uint8_t slot = 0; slot < 6; ++slot) {
      out << "fiber_" << static_cast<unsigned>(target) << "\ttarget\t"
          << static_cast<unsigned>(slot) << "\t-\t" << fiber.target.numerator[slot] << '/'
          << static_cast<unsigned>(fiber.target.denominator) << '\t' << fiber.lineage.value() << '\n';
    }
    for (std::uint8_t realizer = 0; realizer < fiber.realizer_count; ++realizer) {
      for (std::uint8_t generator = 0; generator < 7; ++generator) {
        out << "fiber_" << static_cast<unsigned>(target) << "\trealizer_"
            << static_cast<unsigned>(realizer) << '\t' << static_cast<unsigned>(generator)
            << "\t-\t" << static_cast<int>(fiber.realizers[realizer].coefficients[generator])
            << '\t' << fiber.realizers[realizer].lineage.value() << '\n';
      }
      out << "fiber_" << static_cast<unsigned>(target) << "\trealizer_support\t"
          << static_cast<unsigned>(realizer) << "\t-\t"
          << fiber.realizers[realizer].support_mask << ':'
          << fiber.realizers[realizer].effective_single_graph << ':'
          << fiber.realizers[realizer].integral << '\t'
          << fiber.realizers[realizer].lineage.value() << '\n';
    }
  }
  blowup_rows(out, 0, value.blowup); blowup_rows(out, 1, observation.changed);
}

}  // namespace holonics::tests
