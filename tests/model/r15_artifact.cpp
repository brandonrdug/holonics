#include "r15_artifact.hpp"

#include <ostream>

namespace holonics::tests {

void write_r15_artifact(std::ostream& output,
    const apparatus::theorem_rest_store_receipt& load,
    const apparatus::return_conditioning_executor_receipt& execution,
    const event::return_conditioning_observation& value,
    const event::theorem_production_rest_record& handoff,
    const event::dependent_theorem_setup& setup,
    std::size_t failures) noexcept {
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r15_return_conditioned_theorem_morphology.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "host_semantic_events=" << execution.host_semantic_events.value() << '\n'
         << "engine_source_reads=" << execution.engine_source_reads.value() << '\n'
         << "exterior_retrieval_calls=" << execution.exterior_retrieval_calls.value() << '\n'
         << "developmental_source_bytes=" << execution.developmental_source_bytes.value() << '\n'
         << "verification_failures=" << failures << '\n'
         << "native_load=bytes:" << load.bytes.value()
         << ",calls=" << load.read_calls.value()
         << ",integrity=" << load.integrity_exact
         << ",source_bytes=" << load.developmental_source_bytes.value()
         << ",retrieval_handles=" << load.retrieval_handles.value() << '\n'
         << "production=head:" << value.production_head.value()
         << ",fiber=" << value.production.used_returned_fiber.value()
         << ",consequence=" << value.production.consequence.value()
         << ",available=" << value.production.available
         << ",source_accesses=" << value.production.source_accesses << '\n'
         << "absent_fiber=withheld:" << value.absent_fiber.withheld_fiber.value()
         << ",exact=" << value.absent_fiber.exact
         << "ablation=head:" << value.ablation_head.value()
         << ",available=" << value.ablated.available
         << ",behavior_changed=" << value.behavior_changed
         << ",dependency_exact=" << value.dependency_exact << '\n'
         << "deed_b=question:" << setup.question.identity.value()
         << ",receiver=" << setup.question.receiver.value()
         << ",required_fiber=" << setup.question.required_returned_fiber.value()
         << ",statement=" << setup.statement.value()
         << ",proof=" << setup.proof.value()
         << ",passage=" << setup.passage.value()
         << ",route=" << setup.selected_route.value()
         << ",consequence=" << setup.predicted_consequence.value()
         << ",dependencies=" << setup.dependency_count
         << ",frozen=" << setup.frozen
         << ",source_absent=" << setup.complete_source_absent
         << ",factors=" << setup.factors_through_returned_fiber
         << ",integrity=" << setup.integrity << '\n'
         << "handoff=head:" << handoff.body.head
         << ",continuation=" << handoff.body.continuation
         << ",fiber=" << handoff.acquired.identity.value()
         << ",integrity=" << handoff.integrity
         << ",source_replayed=" << value.production_remount.source_replayed << '\n';
}

}  // namespace holonics::tests
