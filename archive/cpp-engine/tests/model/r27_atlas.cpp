#include "r27_atlas.hpp"

#include <ostream>

namespace holonics::tests {
namespace {

void polynomial(std::ostream& out, const char* family, std::uint8_t presentation,
    const char* kind, std::uint8_t owner,
    const organ::expression_parameter_polynomial& value) {
  for (std::uint8_t slot = 0; slot <= value.degree; ++slot) {
    out << family << '\t' << static_cast<unsigned>(presentation) << '\t' << kind << '\t'
        << static_cast<unsigned>(owner) << '\t' << static_cast<unsigned>(slot) << '\t'
        << value.coefficients[slot] << '\t' << value.exact << '\n';
  }
}

void presentation(std::ostream& out, const char* family, std::uint8_t index,
    const organ::expression_presentation_receipt& value) {
  for (std::uint8_t slot = 0; slot < value.mounted.term_count; ++slot) {
    const auto& term = value.mounted.terms[slot];
    out << family << '\t' << static_cast<unsigned>(index) << "\tterm\t"
        << static_cast<unsigned>(slot) << '\t' << term.coefficient << '\t'
        << static_cast<unsigned>(term.parameter_power) << ','
        << static_cast<unsigned>(term.x_power) << ','
        << static_cast<unsigned>(term.y_power) << '\t' << value.mounted.lineage.value() << '\n';
  }
  for (std::uint8_t variable = 0; variable < 3; ++variable) {
    const auto& partial = value.ideal.partials[variable];
    for (std::uint8_t slot = 0; slot < partial.term_count; ++slot) {
      const auto& term = partial.terms[slot];
      out << family << '\t' << static_cast<unsigned>(index) << "\tpartial\t"
          << static_cast<unsigned>(variable) << ':' << static_cast<unsigned>(slot) << '\t'
          << term.coefficient << '\t' << static_cast<unsigned>(term.parameter_power) << ','
          << static_cast<unsigned>(term.x_power) << ','
          << static_cast<unsigned>(term.y_power) << '\t' << partial.lineage.value() << '\n';
    }
  }
  for (std::uint8_t basis = 0; basis < 3; ++basis) {
    for (std::uint8_t slot = 0; slot < value.ideal.basis[basis].term_count; ++slot) {
      const auto& term = value.ideal.basis[basis].terms[slot];
      out << family << '\t' << static_cast<unsigned>(index) << "\tideal_basis\t"
          << static_cast<unsigned>(basis) << '\t' << term.coefficient << '\t'
          << static_cast<unsigned>(term.parameter_power) << ','
          << static_cast<unsigned>(term.x_power) << ','
          << static_cast<unsigned>(term.y_power) << '\t' << value.ideal.lineage.value() << '\n';
    }
  }
  for (std::uint8_t slot = 0; slot < value.ideal.reduction_count; ++slot) {
    const auto& step = value.ideal.reductions[slot];
    out << family << '\t' << static_cast<unsigned>(index) << "\treduction\t"
        << static_cast<unsigned>(slot) << '\t' << step.coefficient << '\t'
        << static_cast<unsigned>(step.source) << ',' << static_cast<unsigned>(step.target)
        << ',' << static_cast<unsigned>(step.x_power) << '\t' << step.lineage.value() << '\n';
  }
  polynomial(out, family, index, "resultant", 0, value.ideal.resultant);
  for (std::uint8_t slot = 0; slot < 9; ++slot) {
    out << family << '\t' << static_cast<unsigned>(index) << "\tresultant_sample\t"
        << static_cast<unsigned>(slot) << '\t' << value.ideal.resultant_samples[slot]
        << '\t' << ((value.ideal.resultant_sample_mask >> slot) & 1U) << '\t'
        << value.ideal.lineage.value() << '\n';
  }
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    polynomial(out, family, index, "bezout_f", slot, value.ideal.bezout_f[slot]);
  }
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    polynomial(out, family, index, "bezout_fx", slot, value.ideal.bezout_fx[slot]);
  }
  for (std::uint8_t sample = 0; sample < value.sample_count; ++sample) {
    const auto& point = value.samples[sample];
    for (std::uint8_t basis = 0; basis < 4; ++basis) {
      const auto& reduction = point.reductions[basis];
      for (std::uint8_t slot = 0; slot < 4; ++slot) {
        out << family << '\t' << static_cast<unsigned>(index) << "\tsample_p\t"
            << static_cast<unsigned>(sample) << ':' << static_cast<unsigned>(basis) << ':'
            << static_cast<unsigned>(slot) << '\t' << reduction.p[slot].numerator << '/'
            << reduction.p[slot].denominator << '\t' << point.parameter.numerator << '\t'
            << reduction.lineage.value() << '\n';
      }
      for (std::uint8_t slot = 0; slot < 5; ++slot) {
        out << family << '\t' << static_cast<unsigned>(index) << "\tsample_q\t"
            << static_cast<unsigned>(sample) << ':' << static_cast<unsigned>(basis) << ':'
            << static_cast<unsigned>(slot) << '\t' << reduction.q[slot].numerator << '/'
            << reduction.q[slot].denominator << '\t' << point.parameter.numerator << '\t'
            << reduction.lineage.value() << '\n';
      }
    }
  }
  for (std::uint8_t basis = 0; basis < 4; ++basis) {
    for (std::uint8_t slot = 0; slot < 4; ++slot) {
      polynomial(out, family, index, "reduction_p",
          static_cast<std::uint8_t>(4U * basis + slot),
          value.connection.reduction_p[basis][slot]);
    }
    for (std::uint8_t slot = 0; slot < 5; ++slot) {
      polynomial(out, family, index, "reduction_q",
          static_cast<std::uint8_t>(5U * basis + slot),
          value.connection.reduction_q[basis][slot]);
    }
  }
  for (std::uint8_t row = 0; row < 4; ++row) {
    for (std::uint8_t column = 0; column < 4; ++column) {
      polynomial(out, family, index, "connection", static_cast<std::uint8_t>(4U * row + column),
          value.connection.numerator[row][column]);
    }
  }
  for (std::uint8_t derivative = 0; derivative <= 4; ++derivative) {
    polynomial(out, family, index, "scalar", derivative, value.scalar.coefficients[derivative]);
  }
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    out << family << '\t' << static_cast<unsigned>(index) << "\tindicial\tfinite:"
        << static_cast<unsigned>(slot) << '\t' << value.indicial.finite_coefficients[slot]
        << "\texact\t" << value.indicial.lineage.value() << '\n'
        << family << '\t' << static_cast<unsigned>(index) << "\tindicial\tinfinity:"
        << static_cast<unsigned>(slot) << '\t' << value.indicial.infinity_coefficients[slot]
        << "\texact\t" << value.indicial.lineage.value() << '\n';
  }
  for (std::uint8_t front = 0; front < 4; ++front) {
    for (std::uint8_t slot = 0; slot < value.scalar.series_count; ++slot) {
      const auto coefficient = value.scalar.series[front][slot];
      out << family << '\t' << static_cast<unsigned>(index) << "\tseries\t"
          << static_cast<unsigned>(front) << ':' << static_cast<unsigned>(slot) << '\t'
          << coefficient.numerator << '/' << coefficient.denominator << "\tlocal\t"
          << value.scalar.lineage.value() << '\n';
    }
  }
  for (std::uint8_t row = 0; row < 4; ++row) {
    for (std::uint8_t column = 0; column < 4; ++column) {
      for (std::uint8_t degree = 0; degree < 5; ++degree) {
        const auto coefficient = value.residue.matrix[row][column].coefficients[degree];
        out << family << '\t' << static_cast<unsigned>(index) << "\tresidue\t"
            << static_cast<unsigned>(row) << ':' << static_cast<unsigned>(column) << ':'
            << static_cast<unsigned>(degree) << '\t' << coefficient.numerator << '/'
            << coefficient.denominator << "\t4a5=" << value.residue.relation_constant << '\t'
            << value.residue.lineage.value() << '\n';
      }
    }
  }
  out << family << '\t' << static_cast<unsigned>(index)
      << "\tlocal_module\t0\tgeneric_cotangent_rank:1,singular_cotangent_rank:2,hessian_unit:"
      << value.ideal.hessian_invertible << "\tsyzygy:" << value.ideal.syzygies_exact
      << '\t' << value.ideal.lineage.value() << '\n';
}

}  // namespace

void write_r27_atlas(std::ostream& out,
    const event::expression_geometry_observation& observation) {
  out << "family\tpresentation\tkind\towner\tcoefficient\tincidence\tlineage\n";
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    presentation(out, "baseline", slot, observation.inquiry.presentations[slot]);
  }
  for (std::uint8_t slot = 0; slot < 2; ++slot) {
    presentation(out, "changed", slot, observation.changed.presentations[slot]);
  }
  const auto& rational = observation.inquiry.rational_rechart;
  const auto& gaussian = observation.inquiry.gaussian_rechart;
  out << "baseline\t-\trational_rechart\t0\t" << static_cast<int>(rational.x_scale) << ','
      << static_cast<int>(rational.x_shift) << ',' << static_cast<int>(rational.y_square)
      << '\t' << rational.expression_identity << '\t' << rational.lineage.value() << '\n'
      << "baseline\t-\tgaussian_rechart\t0\t" << static_cast<int>(gaussian.x_scale) << ','
      << static_cast<int>(gaussian.x_shift) << ',' << static_cast<int>(gaussian.y_square)
      << '\t' << gaussian.field_dependency_retained << '\t' << gaussian.lineage.value() << '\n';
  const auto& changed = observation.changed.rechart;
  out << "changed\t-\trational_rechart\t0\t" << static_cast<int>(changed.x_scale) << ','
      << static_cast<int>(changed.x_shift) << ',' << static_cast<int>(changed.y_square)
      << '\t' << changed.expression_identity << '\t' << changed.lineage.value() << '\n';
  for (std::uint8_t slot = 0; slot < observation.inquiry.invariant_fiber.member_count; ++slot) {
    out << "baseline\t-\tinvariant_fiber\t" << static_cast<unsigned>(slot) << '\t'
        << observation.inquiry.invariant_fiber.members[slot].value()
        << "\tcomplete\t" << observation.inquiry.invariant_fiber.invariant.value() << '\n';
  }
}

}  // namespace holonics::tests
