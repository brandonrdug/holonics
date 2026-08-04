#include <cstddef>

#include <holonics/event/resident_theorem_production.hpp>

#include "r14_cases.hpp"

namespace {

template<std::size_t Capacity, std::size_t Count>
void place(char (&target)[Capacity], std::uint16_t& used, const char (&source)[Count]) {
  static_assert(Count - 1U <= Capacity);
  for (std::size_t slot = 0; slot < Count - 1U; ++slot) { target[used++] = source[slot]; }
}

holonics::event::checker_raw_return raw_for(
    const holonics::event::checker_outbound_occurrence& outbound) {
  holonics::event::checker_raw_return raw{outbound.predecessor, outbound.event,
      outbound.expected_return_port, holonics::exact::word{outbound.lineage.value() + 1U},
      outbound.passage, outbound.source};
  raw.launched = true;
  raw.exited = true;
  raw.source_fold = 1;
  return raw;
}

}  // namespace

int main() {
  const auto mount = holonics::tests::r14_case();
  holonics::event::resident_theorem_production production{mount.foundation, mount.body_seed,
      mount.regions, mount.mathematical_morphology, mount.codec_morphology};
  holonics::event::theorem_production_observation observation{};
  observation.before = production.probe(mount.held_probe, false);
  if (observation.before.available ||
      !production.generate_and_stage(mount.question, observation)) { return 1; }
  auto accepted = raw_for(observation.outbound);
  accepted.exit_status = 0;
  accepted.produced_artifact_bytes = 64;
  accepted.produced_artifact_fold = 2;
  place(accepted.standard_output, accepted.stdout_bytes,
      "theorem Soma.Holonics.generated_trace_rebase_transports_composition : True := by trivial\n");
  if (!production.resume(accepted, observation) ||
      observation.typed.state != holonics::event::checker_return_status::accepted ||
      !production.acquired().accepted) { return 2; }
  holonics::event::theorem_production_rest_record rest{};
  const auto rested = production.rest(rest);
  if (!rested.returned || rest.integrity !=
      holonics::event::theorem_production_rest_integrity(rest)) { return 3; }
  holonics::event::theorem_production_remount_receipt remount{};
  holonics::event::resident_theorem_production returned{mount.foundation, rest, remount};
  const auto after = returned.probe(mount.held_probe, false);
  const auto ablated = returned.probe(mount.held_probe, true);
  if (!remount.same_body || !remount.acquired_return_preserved || remount.source_replayed ||
      !after.available || ablated.available || after.source_accesses != 0) { return 4; }

  holonics::event::resident_theorem_production rejected{mount.foundation,
      mount.body_seed + 1U, mount.regions, mount.mathematical_morphology,
      mount.codec_morphology};
  holonics::event::theorem_production_observation rejected_observation{};
  if (!rejected.generate_and_stage(mount.question, rejected_observation)) { return 5; }
  auto raw_rejected = raw_for(rejected_observation.outbound);
  raw_rejected.exit_status = 1;
  place(raw_rejected.standard_error, raw_rejected.stderr_bytes, "error: unsolved goals\n");
  if (!rejected.resume(raw_rejected, rejected_observation) ||
      rejected_observation.typed.state !=
          holonics::event::checker_return_status::remaining_goals ||
      rejected.acquired().accepted) { return 6; }
  holonics::event::theorem_production_rest_record refused_rest{};
  if (rejected.rest(refused_rest).returned) { return 7; }
  return 0;
}
