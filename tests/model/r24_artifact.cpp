#include "r24_artifact.hpp"

#include <ostream>

namespace holonics::tests {
namespace {

void rational(std::ostream& output, exact::small_rational value) {
  output << value.numerator;
  if (value.denominator != 1) { output << '/' << value.denominator; }
}

void polynomial(std::ostream& output, const organ::parameter_polynomial& value) {
  for (std::uint8_t slot = 0; slot <= value.degree; ++slot) {
    if (slot != 0) { output << ','; }
    output << value.coefficients[slot];
  }
}

void matrix(std::ostream& output, const std::int64_t value[2][2]) {
  output << value[0][0] << ',' << value[0][1] << ';'
      << value[1][0] << ',' << value[1][1];
}

}  // namespace

void write_r24_artifact(std::ostream& output,
    const apparatus::variation_store_receipt& card_load,
    const apparatus::variation_store_receipt& rest_load,
    const apparatus::variation_store_receipt& rest_write,
    const apparatus::variation_executor_receipt& execution,
    const apparatus::variation_probe_receipt& probe,
    const organ::algebraic_variation_receipt& changed,
    const event::algebraic_variation_observation& value,
    const event::algebraic_variation_rest_record& handoff,
    std::size_t failures) noexcept {
  const auto& inquiry = value.inquiry;
  output << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
      << "variation_interpretation_status=proved-standard\n"
      << "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
      << "hodge_conjecture_status=outside-aperture\n"
      << "riemann_hypothesis_status=outside-aperture\n"
      << "program=r24_algebraic_variation_gauss_manin.sm_89\n"
      << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor
      << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nlaunched_threads=" << execution.launched_threads.value()
      << "\nsemantic_threads=" << execution.semantic_threads.value()
      << "\nbytes_to_device=" << execution.bytes_to_device.value()
      << "\nbytes_from_device=" << execution.bytes_from_device.value()
      << "\nresident_bytes=" << execution.resident_bytes.value()
      << "\nhost_semantic_events=" << execution.host_semantic_events.value()
      << "\nlogical_read_support=" << execution.logical.read_support.value()
      << "\nlogical_change_support=" << execution.logical.change_support.value()
      << "\nlogical_alternatives=" << execution.logical.alternatives_retained.value()
      << "\nlogical_obstructions=" << execution.logical.obstructions_retained.value()
      << "\nverification_failures=" << failures
      << "\nsource_card=bytes:" << card_load.bytes.value() << ",fold:" << card_load.byte_fold
      << ",path_fold:" << card_load.path_fold
      << "\nsource_aperture=degree:3,cover:2,discovery:5,holdout:2,root:-2:2,form:-2:2,"
         "series:6,expected_names:absent"
      << "\npredecessor=rest_bytes:" << rest_load.bytes.value() << ",head:14001020"
      << "\nfamily=roots:";
  for (std::uint8_t root = 0; root < inquiry.root_count; ++root) {
    if (root != 0) { output << ';'; }
    output << inquiry.roots[root].root.constant << '+' << inquiry.roots[root].root.parameter
        << "t@" << inquiry.roots[root].identity.value() << ':' << inquiry.roots[root].lineage.value();
  }
  output << ",discriminant:"; polynomial(output, inquiry.discriminant);
  output << ",vandermonde:"; polynomial(output, inquiry.vandermonde_square);
  output << "\ncollisions=";
  for (std::uint8_t slot = 0; slot < inquiry.collision_count; ++slot) {
    if (slot != 0) { output << ';'; }
    rational(output, inquiry.collisions[slot].parameter);
    output << ":multiplicity=" << +inquiry.collisions[slot].multiplicity
        << ":lineage=" << inquiry.collisions[slot].lineage.value();
  }
  output << "\nconnection=denominator:" << inquiry.connection.denominator_scale << "*(";
  polynomial(output, inquiry.connection.pole_polynomial); output << "),numerator:"
      << inquiry.connection.numerator[0][0].constant << '+'
      << inquiry.connection.numerator[0][0].parameter << "t,"
      << inquiry.connection.numerator[0][1].constant << '+'
      << inquiry.connection.numerator[0][1].parameter << "t;"
      << inquiry.connection.numerator[1][0].constant << '+'
      << inquiry.connection.numerator[1][0].parameter << "t,"
      << inquiry.connection.numerator[1][1].constant << '+'
      << inquiry.connection.numerator[1][1].parameter << "t,holdout:"
      << inquiry.connection.holdouts_exact << ",symbolic:"
      << inquiry.connection.symbolic_residual_zero << ",pole_support:"
      << inquiry.connection.pole_support_matches_discriminant
      << "\ninvariant=enumerated:" << inquiry.invariant.enumerated << ",survivors:"
      << inquiry.invariant.discovery_survivors << ",retained:"
      << +inquiry.invariant.retained_count << ",selected:";
  matrix(output, inquiry.invariant.selected);
  output << "\nscalar=second:" << inquiry.scalar.second[0] << ','
      << inquiry.scalar.second[1] << ',' << inquiry.scalar.second[2] << ",first:"
      << inquiry.scalar.first[0] << ',' << inquiry.scalar.first[1] << ",zeroth:"
      << inquiry.scalar.zeroth << ",constraint_rank:" << +inquiry.scalar.constraint_rank
      << ",series:";
  for (std::uint8_t slot = 0; slot < inquiry.scalar.series_count; ++slot) {
    if (slot != 0) { output << ','; } rational(output, inquiry.scalar.series[slot]);
  }
  output << "\nloops=M0:"; matrix(output, inquiry.loops.monodromy[0]);
  output << ",M1:"; matrix(output, inquiry.loops.monodromy[1]);
  output << ",Minf:"; matrix(output, inquiry.loops.monodromy[2]);
  output << ",pairing_preserved:" << inquiry.loops.pairing_preserved
      << ",ordered_product:" << inquiry.loops.ordered_product_identity
      << ",noncommuting:" << inquiry.loops.noncommuting
      << "\nselection=candidates:" << +inquiry.selection.candidate_count
      << ",selected:" << inquiry.selection.selected.value() << ",no_score:"
      << inquiry.selection.no_score << ",no_expected_statement:"
      << inquiry.selection.no_expected_statement << ",holdout_closed:"
      << inquiry.selection.holdout_closed << ",foils_closed:"
      << inquiry.selection.foils_closed
      << "\nprobe=returned:" << probe.returned() << ",obstruction:"
      << static_cast<unsigned>(changed.obstruction) << ",roots:" << +changed.root_count
      << ",theorem_selected:" << changed.selection.selected.value()
      << "\nchecker=exit:" << value.passage.raw.exit_status << ",stdout_bytes:"
      << value.passage.raw.stdout_bytes << ",stderr_bytes:" << value.passage.raw.stderr_bytes
      << ",produced_bytes:" << value.passage.raw.produced_artifact_bytes
      << "\nfinal_body=head:" << handoff.body.head << ",continuation:"
      << handoff.body.continuation << ",admitted_tally:" << handoff.body.regions[0].admitted_tally
      << ",mathematical:" << handoff.mathematical_admitted_tally << ",codec:"
      << handoff.codec_admitted_tally << ",variation:"
      << handoff.algebraic_variation_admitted_tally << ",rest_bytes:"
      << rest_write.bytes.value() << ",integrity:" << handoff.integrity
      << "\nphysical_telemetry=engine_time:unknown,checker_time:unknown,temperature:unknown,"
         "power:unknown,energy:unknown\nformal_begin\n";
  output.write(value.passage.formal.bytes, value.passage.formal.byte_count);
  output << "formal_end\nconversation_begin\n";
  output.write(value.passage.conversational.bytes, value.passage.conversational.byte_count);
  output << "conversation_end\nchecker_stdout_begin\n";
  output.write(value.passage.raw.standard_output, value.passage.raw.stdout_bytes);
  output << "checker_stdout_end\n";
}

void write_r24_atlas(std::ostream& output,
    const organ::algebraic_variation_receipt& value) noexcept {
  output << "kind\towner\tcoordinate\ttransport\tadmitted\tidentity\tlineage\tobstruction\texact\n";
  for (std::uint8_t root = 0; root < value.root_count; ++root) {
    output << "root\tfamily\t" << value.roots[root].root.constant << '+'
        << value.roots[root].root.parameter << "t\tcoefficientwise\t1\t"
        << value.roots[root].identity.value() << '\t' << value.roots[root].lineage.value()
        << "\t0\t" << value.roots[root].coefficientwise_zero << '\n';
  }
  for (std::uint8_t sample = 0; sample < value.mounted.sample_count; ++sample) {
    output << "connection\t" << (value.samples[sample].discovery ? "discovery" : "holdout")
        << "\t"; rational(output, value.samples[sample].parameter); output << "\t";
    for (std::uint8_t row = 0; row < 2; ++row) {
      if (row != 0) { output << ';'; }
      for (std::uint8_t column = 0; column < 2; ++column) {
        if (column != 0) { output << ','; } rational(output, value.samples[sample].connection[row][column]);
      }
    }
    output << "\t" << value.samples[sample].regular << '\t'
        << value.samples[sample].identity.value() << '\t' << value.samples[sample].lineage.value()
        << "\t" << (value.samples[sample].singular ? "singular" : "0") << '\t'
        << value.samples[sample].exact << '\n';
  }
  for (std::uint8_t candidate = 0; candidate < value.invariant.retained_count; ++candidate) {
    output << "form\tcandidate" << +candidate << "\t";
    matrix(output, value.invariant.candidates[candidate].form);
    output << "\tdiscovery=" << value.invariant.candidates[candidate].discovery_exact
        << ",holdout=" << value.invariant.candidates[candidate].holdout_exact << "\t"
        << value.invariant.candidates[candidate].orientation_selected << '\t'
        << value.invariant.candidates[candidate].identity.value() << '\t'
        << value.invariant.candidates[candidate].lineage.value() << "\tresidual_retained\t1\n";
  }
  for (std::uint8_t candidate = 0; candidate < value.selection.candidate_count; ++candidate) {
    output << "theorem_section\tcandidate" << +candidate << "\tdependencies="
        << value.selection.candidates[candidate].dependency_mask << "\tresiduals="
        << value.selection.candidates[candidate].residual_mask << "\t"
        << (value.selection.candidates[candidate].state == organ::theorem_candidate_state::selected)
        << '\t' << value.selection.candidates[candidate].identity.value() << '\t'
        << value.selection.candidates[candidate].lineage.value() << '\t'
        << static_cast<unsigned>(value.selection.candidates[candidate].state) << "\t1\n";
  }
}

}  // namespace holonics::tests
