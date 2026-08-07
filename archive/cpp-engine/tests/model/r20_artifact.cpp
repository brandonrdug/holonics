#include "r20_artifact.hpp"

#include <ostream>

namespace holonics::tests {
namespace {
void write_matrix(std::ostream& output, organ::matrix_two value) {
  output << "[[" << value.a << ',' << value.b << "],[" << value.c << ',' << value.d << "]]";
}

void write_period(std::ostream& output, organ::period_entry value) {
  output << value.constant;
  if (value.omega >= 0) { output << '+'; }
  output << value.omega << "*omega";
}

void write_period_matrix(std::ostream& output, organ::period_matrix_two value) {
  output << "[[";
  write_period(output, value.a);
  output << ',';
  write_period(output, value.b);
  output << "],[";
  write_period(output, value.c);
  output << ',';
  write_period(output, value.d);
  output << "]]";
}

}  // namespace

void write_r20_atlas(std::ostream& output,
    const organ::regular_singular_receipt& value) noexcept {
  output << "kind\tchart_or_degree\tresidue_or_zero_coefficient\tcharacteristic"
      "\teigenflag_or_one_channels\tresonant_source\tcokernel\tobstruction\tlineage\texact\n";
  constexpr const char* names[3]{"zero", "one", "infinity"};
  for (std::size_t slot = 0; slot < organ::regular_singular_chart_capacity; ++slot) {
    const auto& chart = value.charts[slot];
    output << "chart\t" << names[slot] << ":chart=" << chart.chart.value() << '\t';
    write_matrix(output, chart.residue);
    output << "\ttrace=" << chart.trace << ",det=" << chart.determinant
        << ",disc=" << chart.characteristic_discriminant
        << "\teigen=" << chart.lower_eigenvalue << ',' << chart.upper_eigenvalue
        << ",right=(" << chart.right_eigenvector[0] << ',' << chart.right_eigenvector[1]
        << "),generalized=(" << chart.generalized_vector[0] << ','
        << chart.generalized_vector[1] << ")\t(" << chart.resonant_source[0] << ','
        << chart.resonant_source[1] << ")\t(" << chart.recurrence_cokernel[0] << ','
        << chart.recurrence_cokernel[1] << ")\t" << chart.obstruction_scalar
        << "\t" << chart.lineage << '\t' << chart.exact << '\n';
  }
  for (std::size_t slot = 0; slot < organ::regular_singular_term_capacity; ++slot) {
    const auto& term = value.terms[slot];
    output << "frobenius\t" << term.degree << ":term=" << term.identity.value()
        << "\t" << term.zero_numerator << '/'
        << term.zero_denominator << "\tzero_step=" << term.zero_step_lhs << '-'
        << term.zero_step_rhs << "\tone_regular=" << term.one_regular
        << ",one_log=" << term.one_logarithmic << "\t-\t-\t"
        << term.one_step_residual << '\t' << term.lineage << '\t' << term.exact << '\n';
  }
  output << "connection\tzero_to_one:path=" << value.connection.overlap_path.value()
      << ",B0=" << value.connection.zero_basis.value()
      << ",B1=" << value.connection.one_basis.value() << "\t";
  write_matrix(output, value.connection.zero_to_one);
  output << "\tdet=" << static_cast<int>(value.connection.connection_determinant)
      << "\tbasis_swap\t-\t-\t0\t" << value.connection.connection_lineage
      << '\t' << value.connection.exact << '\n';
  output << "loop\tzero:word=" << value.connection.zero_loop.value() << "\t";
  write_period_matrix(output, value.connection.monodromy_zero);
  output << "\t(X-1)^2\tfixed=2,nilpotent_rank=0\t-\t-\t0\t"
      << value.connection.loop_lineages[0] << '\t' << value.connection.exact << '\n';
  output << "loop\tone:word=" << value.connection.one_loop.value() << "\t";
  write_period_matrix(output, value.connection.monodromy_one);
  output << "\t(X-1)^2\tfixed=1,nilpotent_rank=1\t-\t-\t0\t"
      << value.connection.loop_lineages[1] << '\t' << value.connection.exact << '\n';
  output << "loop\tinfinity:word=" << value.connection.infinity_loop.value() << "\t";
  write_period_matrix(output, value.connection.monodromy_infinity);
  output << "\t(X-1)^2\tfixed=1,nilpotent_rank=1\t-\t-\t0\t"
      << value.connection.loop_lineages[2] << '\t' << value.connection.exact << '\n';
  output << "loop_product\tzero*one*infinity\t";
  write_period_matrix(output, value.connection.loop_product);
  output << "\t(X-1)^2\tfixed=2\t-\t-\t0\t" << value.connection.loop_lineage
      << '\t' << value.connection.punctured_sphere_product_exact << '\n';
}

void write_r20_artifact(std::ostream& output,
    const apparatus::regular_singular_store_receipt& rest_load,
    const apparatus::regular_singular_store_receipt& rest_write,
    const apparatus::regular_singular_executor_receipt& execution,
    const event::regular_singular_observation& value,
    const event::regular_singular_rest_record& handoff,
    std::size_t failures) noexcept {
  const auto& inquiry = value.inquiry;
  const auto& zero = inquiry.charts[0];
  const auto& one = inquiry.charts[1];
  const auto& infinity = inquiry.charts[2];
  output << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\n"
      << "formal_evidence=formal-checked\n"
      << "analytic_truth_status=proved-standard\n"
      << "program=r20_regular_singular_continuation.sm_89\n"
      << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor
      << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nlaunched_threads=" << execution.launched_threads.value()
      << "\nchart_threads=" << execution.chart_threads.value()
      << "\ncoefficient_threads=" << execution.coefficient_threads.value()
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
      << "\nquestion_aperture=special_function_lookup_absent:"
      << inquiry.no_special_function_lookup
      << ",numerical_continuation_absent:" << inquiry.no_numerical_continuation
      << ",expected_logarithm_absent:" << inquiry.no_expected_logarithm
      << ",expected_eigenvector_absent:" << inquiry.no_expected_eigenvector
      << "\nnative_input=rest_bytes:" << rest_load.bytes.value()
      << ",source_bytes:0,retrieval_handles:0\noperator=second:0,1,-1,first:2,-3,zeroth:-1"
      << "\nsystem=A0:";
  write_matrix(output, inquiry.system.zero);
  output << ",A1:";
  write_matrix(output, inquiry.system.one);
  output << ",Ainf:";
  write_matrix(output, inquiry.system.infinity);
  output << ",derived:" << inquiry.system.derived
      << "\nzero_resonance=gap:" << static_cast<unsigned>(zero.eigenvalue_gap)
      << ",source:" << zero.resonant_source[0] << ',' << zero.resonant_source[1]
      << ",cokernel:" << zero.recurrence_cokernel[0] << ','
      << zero.recurrence_cokernel[1] << ",obstruction:" << zero.obstruction_scalar
      << ",log:" << zero.logarithmic_channel
      << "\none_resonance=gap:" << static_cast<unsigned>(one.eigenvalue_gap)
      << ",source:" << one.resonant_source[0] << ',' << one.resonant_source[1]
      << ",cokernel:" << one.recurrence_cokernel[0] << ','
      << one.recurrence_cokernel[1] << ",obstruction:" << one.obstruction_scalar
      << ",log:" << one.logarithmic_channel
      << "\ninfinity_characteristic=trace:" << infinity.trace
      << ",determinant:" << infinity.determinant
      << ",discriminant:" << infinity.characteristic_discriminant
      << ",eigenflag_dimension:" << static_cast<unsigned>(infinity.eigenflag_dimension)
      << ",nilpotent_rank:" << static_cast<unsigned>(infinity.nilpotent_rank)
      << "\nfrobenius=returned_terms:" << inquiry.returned_terms
      << ",zero_last:1/" << inquiry.terms[11].zero_denominator
      << ",one_regular:1,one_logarithmic:-1"
      << "\nconnection=determinant:"
      << static_cast<int>(inquiry.connection.connection_determinant)
      << ",inverse:" << inquiry.connection.inverse_exact
      << ",conjugacy:" << inquiry.connection.conjugacy_exact
      << ",lineage:" << inquiry.connection.connection_lineage
      << "\nmonodromy=period_symbolic:" << inquiry.connection.period_symbolic
      << ",M0_fixed:" << static_cast<unsigned>(inquiry.connection.zero_fixed_dimension)
      << ",M1_fixed:" << static_cast<unsigned>(inquiry.connection.one_fixed_dimension)
      << ",Minf_fixed:" << static_cast<unsigned>(inquiry.connection.infinity_fixed_dimension)
      << ",sphere_product:" << inquiry.connection.punctured_sphere_product_exact
      << ",M0_lineage:" << inquiry.connection.loop_lineages[0]
      << ",M1_lineage:" << inquiry.connection.loop_lineages[1]
      << ",Minf_lineage:" << inquiry.connection.loop_lineages[2]
      << ",lineage:" << inquiry.connection.loop_lineage
      << "\ntheory=passage:" << inquiry.theory.passage.value()
      << ",residue_algebra:" << inquiry.theory.residue_algebra
      << ",frobenius_steps:" << inquiry.theory.frobenius_steps
      << ",resonance_obstruction:" << inquiry.theory.resonance_obstruction
      << ",chamber_connection:" << inquiry.theory.chamber_connection
      << ",loop_product:" << inquiry.theory.loop_product
      << "\nchecker=exit:" << value.raw.exit_status << ",stdout_bytes:"
      << value.raw.stdout_bytes << ",stderr_bytes:" << value.raw.stderr_bytes
      << ",produced_bytes:" << value.raw.produced_artifact_bytes << ",declarations:"
      << value.typed.produced_declarations << ",remaining_goals:"
      << value.typed.remaining_goal_count << ",kernel:" << value.typed.kernel_boundary_crossed
      << ",calls:" << execution.process.exterior_process_calls.value() << '\n'
      << "final_body=head:" << handoff.body.head << ",continuation:"
      << handoff.body.continuation << ",rest_bytes:" << rest_write.bytes.value()
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
