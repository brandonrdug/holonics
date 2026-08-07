#include "r20_cases.hpp"

int main() {
  const auto inherited = holonics::tests::r20_host_characteristic_rest();
  const auto mount = holonics::tests::r20_case(inherited);
  if (!holonics::organ::regular_singular_detail::valid_foundation(mount.foundation)) { return 1; }
  const auto system = holonics::organ::regular_singular_detail::derive_system(
      mount.foundation.mounted_operator);
  if (!system.derived) { return 2; }
  const auto zero = holonics::organ::regular_singular_detail::form_chart(mount.foundation, 0);
  const auto one = holonics::organ::regular_singular_detail::form_chart(mount.foundation, 1);
  const auto infinity = holonics::organ::regular_singular_detail::form_chart(
      mount.foundation, 2);
  if (!zero.exact || !one.exact || !infinity.exact || zero.obstruction_scalar != 0 ||
      one.obstruction_scalar != 1 || infinity.nilpotent_rank != 1) { return 3; }
  for (std::uint16_t slot = 0; slot < mount.foundation.term_count; ++slot) {
    if (!holonics::organ::regular_singular_detail::form_term(
        mount.foundation, slot).exact) { return 4; }
  }
  holonics::organ::chamber_connection_receipt connection{};
  holonics::organ::regular_singular_detail::form_connection(mount.foundation, connection);
  return connection.exact ? 0 : 5;
}
