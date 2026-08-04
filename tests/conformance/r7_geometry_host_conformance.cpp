#include <type_traits>

#include <holonics/receiver/resident_geometry.hpp>

#include "../model/r7_cases.hpp"
#include "../model/r7_oracle.hpp"

static_assert(!std::is_copy_constructible_v<holonics::receiver::resident_geometry>);
static_assert(!std::is_move_constructible_v<holonics::receiver::resident_geometry>);

int main() {
  const auto mount = holonics::tests::r7_case();
  if (holonics::receiver::validate_geometry_program(mount.receiver) !=
      holonics::receiver::geometry_obstruction::none) {
    return 1;
  }
  const auto oracle = holonics::tests::r7_oracle(mount);
  if (!oracle.receiver.all_deeds_returned ||
      !oracle.receiver.swing.projectively_equal ||
      oracle.receiver.sameness.occurrence_equal ||
      oracle.receiver.projection.created_source_incidence.value() != 0 ||
      oracle.receiver.connection.open_path_residual_is_holonomy ||
      !oracle.receiver.hypergeometric.recurrence_exact ||
      oracle.receiver.carrier.literal_physical_identity ||
      oracle.receiver.information.general_relativistic_fidelity) {
    return 2;
  }
  return 0;
}
