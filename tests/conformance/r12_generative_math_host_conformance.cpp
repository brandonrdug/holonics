#include <holonics/event/resident_generative_math_current.hpp>

#include "r12_cases.hpp"
#include "r12_oracle.hpp"
#include "r12_verify.hpp"

int main() {
  const auto mount = holonics::tests::r12_case();
  const auto expected = holonics::tests::r12_oracle();
  holonics::event::resident_generative_math_current current{
      mount.foundation, mount.body_seed, mount.regions, true};
  const auto returned = current.generate(mount.question);
  if (current.obstruction() != holonics::organ::generative_obstruction::none ||
      returned.generation.obstruction != holonics::organ::generative_obstruction::none ||
      returned.generation.expansion.open_count != 2 ||
      returned.generation.information.alternatives_after != 1 ||
      returned.generation.passage.statement != holonics::exact::word{expected.statement} ||
      returned.generation.passage.proof != holonics::exact::word{expected.proof} ||
      !returned.generation.exclusion.absent_before_generation ||
      !returned.same_closed_passage || !returned.continuation_valid ||
      !holonics::tests::same_generated_bytes(returned.formal.bytes,
          returned.formal.byte_count, expected.formal_source) ||
      !holonics::tests::same_generated_bytes(returned.conversational.bytes,
          returned.conversational.byte_count, expected.explanation)) {
    return 1;
  }
  return 0;
}
