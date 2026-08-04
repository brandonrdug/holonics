#include <cstddef>

#include <holonics/codec/formal_math_renderer.hpp>
#include <holonics/event/resident_checker_current.hpp>

namespace {

template<std::size_t Capacity, std::size_t Count>
void place(char (&target)[Capacity], std::uint16_t& used, const char (&source)[Count]) {
  static_assert(Count - 1U <= Capacity);
  for (std::size_t slot = 0; slot < Count - 1U; ++slot) { target[used++] = source[slot]; }
}

holonics::codec::formal_math_face formal_face() {
  holonics::codec::formal_math_face face{};
  const holonics::codec::generated_math_surface surface{holonics::exact::word{150'100},
      holonics::exact::word{130'100}, holonics::exact::word{140'100},
      holonics::exact::word{112'070}, 1, 1};
  static_cast<void>(holonics::codec::render_formal_math_face(surface, face));
  return face;
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
  holonics::body::rest_region regions[holonics::body::live_region_capacity]{};
  regions[0] = {123, 150'100};
  auto source = formal_face();
  holonics::event::resident_checker_current accepted{13'001'000, regions, 40, 30};
  holonics::event::checker_observation accepted_observation{};
  if (accepted.stage(source, accepted_observation) !=
      holonics::event::checker_stage_status::exact) { return 1; }
  auto accepted_raw = raw_for(accepted_observation.outbound);
  accepted_raw.exit_status = 0;
  accepted_raw.produced_artifact_bytes = 64;
  accepted_raw.produced_artifact_fold = 2;
  place(accepted_raw.standard_output, accepted_raw.stdout_bytes,
      "theorem Soma.Holonics.generated_semantics_rebase_reverse : True := by trivial\n");
  if (!accepted.resume(accepted_raw, accepted_observation) ||
      accepted_observation.typed.state != holonics::event::checker_return_status::accepted ||
      accepted_observation.typed.produced_declarations != 1 ||
      accepted_observation.morphology.mathematical_after != 43 ||
      accepted_observation.morphology.codec_after != 32 ||
      !accepted_observation.passage_preserved) { return 2; }

  holonics::event::resident_checker_current rejected{13'002'000, regions, 40, 30};
  holonics::event::checker_observation rejected_observation{};
  if (rejected.stage(source, rejected_observation) !=
      holonics::event::checker_stage_status::exact) { return 3; }
  auto rejected_raw = raw_for(rejected_observation.outbound);
  rejected_raw.exit_status = 1;
  place(rejected_raw.standard_error, rejected_raw.stderr_bytes, "error: unsolved goals\n");
  if (!rejected.resume(rejected_raw, rejected_observation) ||
      rejected_observation.typed.state !=
          holonics::event::checker_return_status::remaining_goals ||
      rejected_observation.typed.remaining_goal_count != 1 ||
      rejected_observation.morphology.mathematical_after != 41 ||
      rejected_observation.morphology.codec_after != 33 ||
      !rejected_observation.morphology.returned_difference_applied) { return 4; }
  return 0;
}
