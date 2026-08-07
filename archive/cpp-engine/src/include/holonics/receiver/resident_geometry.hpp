#pragma once

#include <type_traits>

#include <holonics/receiver/geometry_law.hpp>

namespace holonics::receiver {

class resident_geometry final {
 public:
  resident_geometry() = delete;
  resident_geometry(const resident_geometry&) = delete;
  resident_geometry& operator=(const resident_geometry&) = delete;
  resident_geometry(resident_geometry&&) = delete;
  resident_geometry& operator=(resident_geometry&&) = delete;

  HOLONICS_CALLABLE explicit resident_geometry(const geometry_program& program) noexcept
      : program_(program) {
    observation_.program_identity = program.identity;
    observation_.obstruction = validate_geometry_program(program);
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr const geometry_program& program() const noexcept {
    return program_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const geometry_observation& observation()
      const noexcept { return observation_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr geometry_observation& observation() noexcept {
    return observation_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted() const noexcept {
    return observation_.obstruction == geometry_obstruction::none;
  }

 private:
  geometry_program program_{};
  geometry_observation observation_{};
};

static_assert(std::is_trivially_destructible_v<resident_geometry>);

}  // namespace holonics::receiver
