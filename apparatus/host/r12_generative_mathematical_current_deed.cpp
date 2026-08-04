#include <fstream>

#include <holonics/apparatus/generative_math_executor.hpp>

#include "r12_artifact.hpp"
#include "r12_cases.hpp"
#include "r12_oracle.hpp"
#include "r12_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 4) { return 2; }
  const auto mount = holonics::tests::r12_case();
  holonics::apparatus::generative_math_observation observation{};
  const auto execution = holonics::apparatus::execute_generative_math(mount, observation);
  const auto expected = holonics::tests::r12_oracle();
  const auto failures = holonics::tests::r12_verification_failures(
      execution, observation, expected);
  std::ofstream source{argv[2], std::ios::binary | std::ios::trunc};
  std::ofstream explanation{argv[3], std::ios::binary | std::ios::trunc};
  if (!source || !explanation) { return 3; }
  source.write(observation.returned.formal.bytes, observation.returned.formal.byte_count);
  explanation.write(observation.returned.conversational.bytes,
      observation.returned.conversational.byte_count);
  source.close();
  explanation.close();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  if (!deed) { return 4; }
  holonics::tests::write_r12_artifact(deed, execution, observation, failures);
  return failures == 0 ? 0 : 1;
}
