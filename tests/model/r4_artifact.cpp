#include "r4_artifact.hpp"

#include <cstddef>
#include <ostream>

namespace holonics::tests {

void write_r4_artifact(
    std::ostream& stream,
    const apparatus::body_lifecycle_executor_receipt& execution,
    const event::lifecycle_output& output,
    std::size_t failures) {
  stream << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r4_open+resume_commit_rest+remount+adversarial.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_body_bytes=" << execution.resident_body_bytes.value() << '\n'
         << "predecessor_head=" << output.predecessor.head << '\n'
         << "outbound_event=" << output.outbound.event << '\n'
         << "outbound_expected_return_port=" << output.outbound.expected_return_port << '\n'
         << "return_state=" << static_cast<unsigned>(output.resume_state) << '\n'
         << "delta_read_support=" << output.delta.read_support << '\n'
         << "delta_change_support=" << output.delta.change_support << '\n'
         << "delta_morphology=" << output.delta.admitted_tally_delta << '\n'
         << "successor_head=" << output.successor.head << '\n'
         << "successor_region_morphology="
         << output.successor.regions[output.delta.region].morphology << '\n'
         << "rest_integrity=" << output.rest.integrity.value() << '\n'
         << "remount_equal=" << (output.successor.head == output.remounted.head) << '\n'
         << "source_replays=" << output.source_replays << '\n'
         << "second_open_state=" << static_cast<unsigned>(output.adversarial.second_open) << '\n'
         << "foreign_return_state=" << static_cast<unsigned>(output.adversarial.foreign_return) << '\n'
         << "stale_return_state=" << static_cast<unsigned>(output.adversarial.stale_return) << '\n'
         << "double_return_state=" << static_cast<unsigned>(output.adversarial.double_return) << '\n'
         << "capacity_commit_state=" << static_cast<unsigned>(output.adversarial.capacity_commit) << '\n'
         << "capacity_predecessor_preserved="
         << output.adversarial.capacity_predecessor_preserved << '\n'
         << "capacity_capability_restored="
         << output.adversarial.capacity_capability_restored << '\n'
         << "interruption_predecessor_0=" << output.adversarial.interruption_predecessors[0] << '\n'
         << "interruption_predecessor_1=" << output.adversarial.interruption_predecessors[1] << '\n'
         << "interruption_predecessor_2=" << output.adversarial.interruption_predecessors[2] << '\n'
         << "interruption_successor=" << output.adversarial.interruption_successor << '\n'
         << "verification_failures=" << failures << '\n';
}

}  // namespace holonics::tests
