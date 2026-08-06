#include "r18_artifact.hpp"

#include <ostream>

namespace holonics::tests {
namespace {

[[nodiscard]] const char* kind(organ::phase_case_kind value) noexcept {
  switch (value) {
    case organ::phase_case_kind::prime_pair: return "prime-pair";
    case organ::phase_case_kind::composite_coprime: return "composite-coprime";
    case organ::phase_case_kind::composite_shared_factor: return "shared-factor";
    case organ::phase_case_kind::reversed_dominance: return "reversed-dominance";
    case organ::phase_case_kind::exact_dilation: return "exact-dilation";
    case organ::phase_case_kind::exact_turn: return "exact-turn";
    case organ::phase_case_kind::reversed_pair: return "reversed-pair";
  }
  return "unknown";
}

void ratio(std::ostream& output, organ::phase_ratio value) noexcept {
  output << value.numerator << '/' << value.denominator;
}

}  // namespace

void write_r18_atlas(std::ostream& output, const organ::phase_crystal_receipt& value) noexcept {
  output << "case\tkind\tmoduli\tgcd\tlcm\torbits\torbit_length\tvertices\tedges\tcells\tseams"
      "\tfirst_edge_types\tsecond_edge_types\tcell_shape_types\ttransition_types"
      "\tmax_shape_population\tmax_transition_population\thull_corners\tcontracted_sides"
      "\thull_edge_types\tfirst_side_range\tsecond_side_range\treceiver_hull_side_range"
      "\tseries_terms\tshape_fold\ttransition_fold\texact\n";
  for (std::size_t slot = 0; slot < organ::phase_crystal_case_capacity; ++slot) {
    const auto& item = value.cases[slot];
    output << slot << '\t' << kind(item.definition.kind) << '\t'
        << item.definition.first_modulus << ',' << item.definition.second_modulus << '\t'
        << item.gcd << '\t' << item.lcm << '\t' << item.orbit_count << '\t'
        << item.orbit_length << '\t' << item.vertex_count << '\t' << item.phase_edge_count
        << '\t' << item.cell_count << '\t' << item.seam_count << '\t'
        << item.first_edge_types << '\t' << item.second_edge_types << '\t'
        << item.cell_shape_types << '\t' << item.shape_transition_types << '\t'
        << item.largest_shape_population << '\t' << item.largest_transition_population << '\t'
        << item.hull_corners << '\t' << item.contracted_sides << '\t'
        << item.hull_edge_types << '\t';
    ratio(output, item.first_shortest_side); output << ':'; ratio(output, item.first_longest_side);
    output << '\t'; ratio(output, item.second_shortest_side); output << ':';
    ratio(output, item.second_longest_side); output << '\t';
    ratio(output, item.receiver_shortest_hull_side); output << ':';
    ratio(output, item.receiver_longest_hull_side);
    output << '\t' << item.series_terms << '\t' << item.shape_population_fold << '\t'
        << item.transition_population_fold << '\t' << item.exact << '\n';
  }
}

void write_r18_artifact(std::ostream& output,
    const apparatus::phase_crystal_store_receipt& rest_load,
    const apparatus::phase_crystal_store_receipt& rest_write,
    const apparatus::phase_crystal_executor_receipt& execution,
    const event::phase_crystal_observation& value,
    const event::phase_crystal_rest_record& handoff,
    std::size_t failures) noexcept {
  const auto& inquiry = value.inquiry;
  output << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\n"
      << "formal_evidence=formal-checked\n"
      << "program=r18_phase_crystal_hypergeometry.sm_89\n"
      << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor
      << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nlaunched_threads=" << execution.launched_threads.value()
      << "\ncase_threads=" << execution.case_threads.value()
      << "\nbytes_to_device=" << execution.bytes_to_device.value()
      << "\nbytes_from_device=" << execution.bytes_from_device.value()
      << "\nresident_bytes=" << execution.resident_bytes.value()
      << "\nhost_semantic_events=" << execution.host_semantic_events.value()
      << "\nengine_source_reads=" << execution.engine_source_reads.value()
      << "\nexterior_retrieval_calls=" << execution.exterior_retrieval_calls.value()
      << "\nhistorical_renderer_bytes=" << execution.historical_renderer_bytes.value()
      << "\nverification_failures=" << failures
      << "\nquestion=identity:" << inquiry.question.identity.value()
      << ",receiver:" << inquiry.question.receiver.value()
      << ",material:" << inquiry.question.material.value()
      << "\nquestion_aperture=mode_field_absent:" << inquiry.mode_field_absent
      << ",expected_shape_absent:" << inquiry.expected_shape_absent
      << ",historical_renderer_absent:" << inquiry.historical_renderer_absent
      << "\nnative_input=rest_bytes:" << rest_load.bytes.value()
      << ",source_bytes:0,retrieval_handles:0\n"
      << "atlas=returned_cases:" << inquiry.returned_cases << ",prime_cases:"
      << inquiry.prime_cases << ",composite_cases:" << inquiry.composite_cases
      << ",shared_factor_cases:" << inquiry.shared_factor_cases << ",control_cases:"
      << inquiry.control_cases << ",shape_types:" << inquiry.total_shape_types
      << ",transition_types:" << inquiry.total_transition_types << '\n'
      << "controls=dilation:" << inquiry.dilation_control_exact << ",turn:"
      << inquiry.turn_control_exact << ",reversal:" << inquiry.reversal_control_exact << '\n'
      << "theory=passage:" << inquiry.theory.passage.value() << ",diagonal_lcm:"
      << inquiry.theory.diagonal_lcm << ",coprime_full_tour:"
      << inquiry.theory.coprime_full_tour << ",population_product:"
      << inquiry.theory.cell_population_product << ",seam_cancellation:"
      << inquiry.theory.seam_cancellation << ",gauss_transport:"
      << inquiry.theory.gauss_transport << ",projection_distinguished:"
      << inquiry.theory.projection_distinguished << '\n'
      << "checker=exit:" << value.raw.exit_status << ",stdout_bytes:"
      << value.raw.stdout_bytes << ",stderr_bytes:" << value.raw.stderr_bytes
      << ",produced_bytes:" << value.raw.produced_artifact_bytes << ",declarations:"
      << value.typed.produced_declarations << ",remaining_goals:"
      << value.typed.remaining_goal_count << ",kernel:" << value.typed.kernel_boundary_crossed
      << ",calls:" << execution.process.exterior_process_calls.value() << '\n'
      << "final_body=head:" << handoff.body.head << ",continuation:"
      << handoff.body.continuation << ",body_admitted_tally:"
      << handoff.body.regions[0].admitted_tally << ",mathematical:"
      << handoff.mathematical_admitted_tally << ",codec:" << handoff.codec_admitted_tally
      << ",geometry:" << handoff.geometry_admitted_tally << ",phase:"
      << handoff.phase_admitted_tally << ",rest_bytes:" << rest_write.bytes.value()
      << ",integrity:" << handoff.integrity << '\n'
      << "physical_telemetry=engine_time:unknown,checker_time:unknown,temperature:unknown,"
         "power:unknown,energy:unknown\nformal_begin\n";
  output.write(value.formal.bytes, value.formal.byte_count);
  output << "formal_end\nconversation_begin\n";
  output.write(value.conversational.bytes, value.conversational.byte_count);
  output << "conversation_end\nstdout_begin\n";
  output.write(value.raw.standard_output, value.raw.stdout_bytes);
  output << "stdout_end\nstderr_begin\n";
  output.write(value.raw.standard_error, value.raw.stderr_bytes);
  output << "stderr_end\n";
}

}  // namespace holonics::tests
