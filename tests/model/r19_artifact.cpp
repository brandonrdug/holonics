#include "r19_artifact.hpp"

#include <ostream>

namespace holonics::tests {

void write_r19_atlas(std::ostream& output,
    const organ::characteristic_receipt& value) noexcept {
  output << "case\tmoduli\tgcd\tlcm\tcharacteristic_factor\tminimal_factor"
      "\tshape_types\ttour\tformal_shape_monomial\tfold\texact\n";
  for (std::size_t slot = 0; slot < organ::characteristic_case_capacity; ++slot) {
    const auto& item = value.cases[slot];
    for (std::size_t tour = 0; tour < item.tours; ++tour) {
      output << slot << '\t' << item.definition.first_modulus << ','
          << item.definition.second_modulus << '\t' << item.gcd << '\t' << item.lcm
          << "\t(X^" << item.lcm << "-1)^" << item.gcd
          << "\tX^" << item.lcm << "-1\t" << item.shape_types << '\t' << tour << '\t';
      bool first = true;
      for (std::size_t shape = 0; shape < item.shape_types; ++shape) {
        const auto exponent = item.shape_exponents[tour][shape];
        if (exponent == 0) { continue; }
        if (!first) { output << '*'; }
        output << 's' << shape << '^' << exponent;
        first = false;
      }
      output << '\t' << item.shape_tour_folds[tour] << '\t' << item.exact << '\n';
    }
  }
}

void write_r19_artifact(std::ostream& output,
    const apparatus::characteristic_store_receipt& rest_load,
    const apparatus::characteristic_store_receipt& rest_write,
    const apparatus::characteristic_executor_receipt& execution,
    const event::characteristic_observation& value,
    const event::characteristic_rest_record& handoff,
    std::size_t failures) noexcept {
  const auto& inquiry = value.inquiry;
  const auto& matrix = inquiry.matrices;
  output << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\n"
      << "formal_evidence=formal-checked\n"
      << "program=r19_exact_characteristic_return.sm_89\n"
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
      << "\nquestion_aperture=expected_eigenvalue_absent:" << inquiry.no_expected_eigenvalue
      << ",prime_mode_label_absent:" << inquiry.no_prime_mode_label
      << ",renderer_source_absent:" << inquiry.no_renderer_source
      << "\nnative_input=rest_bytes:" << rest_load.bytes.value()
      << ",source_bytes:0,retrieval_handles:0\n"
      << "orbit_spectrum=returned_cases:" << inquiry.returned_cases
      << ",simple_mode_cases:" << inquiry.simple_mode_cases
      << ",repeated_mode_cases:" << inquiry.repeated_mode_cases
      << ",shape_tour_classes:" << inquiry.shape_tour_classes << '\n'
      << "scalar_control=first_product:" << inquiry.scalar.first_product
      << ",second_product:" << inquiry.scalar.second_product
      << ",characteristic_equal:" << inquiry.scalar.characteristic_equal
      << ",lineage_distinct:" << inquiry.scalar.lineage_distinct << '\n'
      << "matrix_order=first_trace:" << matrix.first_trace
      << ",second_trace:" << matrix.second_trace
      << ",first_determinant:" << matrix.first_determinant
      << ",second_determinant:" << matrix.second_determinant
      << ",first_lineage:" << matrix.first_lineage
      << ",second_lineage:" << matrix.second_lineage
      << ",lineage_distinct:" << matrix.order_lineage_distinct
      << ",changes_characteristic:" << matrix.order_changes_characteristic << '\n'
      << "matrix_rechart=trace:" << matrix.rechart_trace
      << ",determinant:" << matrix.rechart_determinant
      << ",lineage:" << matrix.rechart_lineage
      << ",preserves_characteristic:" << matrix.rechart_preserves_characteristic << '\n'
      << "equal_characteristic_control=independent_fixed_dimension:"
      << static_cast<unsigned>(matrix.independent_fixed_dimension)
      << ",coupled_fixed_dimension:" << static_cast<unsigned>(matrix.coupled_fixed_dimension)
      << ",unequal_conduct:" << matrix.equal_characteristic_unequal_conduct << '\n'
      << "indicial=zero:rho(rho+1),one:rho^2,infinity:(rho-1)^2,"
         "single_branch_incomplete:" << inquiry.indicial.recurrence_is_only_one_local_branch
      << "\ntheory=passage:" << inquiry.theory.passage.value()
      << ",diagonal_factor:" << inquiry.theory.diagonal_factor
      << ",weighted_cycle:" << inquiry.theory.weighted_cycle
      << ",matrix_controls:" << inquiry.theory.matrix_controls
      << ",discriminants_typed:" << inquiry.theory.discriminants_typed
      << ",gauss_indicial:" << inquiry.theory.gauss_indicial << '\n'
      << "checker=exit:" << value.raw.exit_status << ",stdout_bytes:"
      << value.raw.stdout_bytes << ",stderr_bytes:" << value.raw.stderr_bytes
      << ",produced_bytes:" << value.raw.produced_artifact_bytes << ",declarations:"
      << value.typed.produced_declarations << ",remaining_goals:"
      << value.typed.remaining_goal_count << ",kernel:" << value.typed.kernel_boundary_crossed
      << ",calls:" << execution.process.exterior_process_calls.value() << '\n'
      << "final_body=head:" << handoff.body.head << ",continuation:"
      << handoff.body.continuation << ",body_admitted_tally:"
      << handoff.body.regions[0].morphology << ",mathematical:"
      << handoff.mathematical_admitted_tally << ",codec:" << handoff.codec_admitted_tally
      << ",geometry:" << handoff.geometry_admitted_tally << ",phase:"
      << handoff.phase_admitted_tally << ",characteristic:"
      << handoff.characteristic_admitted_tally << ",rest_bytes:" << rest_write.bytes.value()
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
