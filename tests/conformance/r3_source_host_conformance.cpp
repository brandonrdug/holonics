#include <cstddef>

#include <holonics/apparatus/source_store_adapter.hpp>

#include "r3_verify.hpp"

int main(int argument_count, char** arguments) {
  constexpr std::size_t source_count = 3;
  if (argument_count != 5) {
    return 2;
  }
  const char* source_paths[source_count]{arguments[1], arguments[2], arguments[3]};
  auto original = holonics::apparatus::mount_source_store(source_paths, source_count);
  auto relocated = holonics::apparatus::mount_relocated_source_store(
      source_paths, source_count, arguments[4]);
  const auto expected = holonics::tests::r3_oracle(original.environment);
  const std::size_t failures = holonics::tests::r3_environment_failures(
      original.environment, relocated.environment, original.receipt, relocated.receipt);
  const auto& navigation = expected.variants[0].navigation;
  if (failures != 0 || navigation.preimage.occurrences_touched == 0 ||
      navigation.support.occurrence_count >= navigation.support.source_occurrence_count ||
      navigation.obstruction.state != holonics::receiver::navigation_status::empty_preimage) {
    return 1;
  }
  return 0;
}
