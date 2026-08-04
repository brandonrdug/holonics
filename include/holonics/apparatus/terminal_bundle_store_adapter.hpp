#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/event/dependent_theorem_setup.hpp>

namespace holonics::apparatus {

inline constexpr std::size_t first_return_artifact_capacity = 8192;

enum class terminal_store_status : std::uint8_t {
  returned,
  invalid_aperture,
  open_refused,
  read_refused,
  size_refused,
  integrity_refused
};

struct dependent_setup_store_receipt final {
  terminal_store_status state{terminal_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word read_calls{};
  exact::word developmental_source_bytes{};
  exact::word retrieval_handles{};
  bool integrity_exact{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == terminal_store_status::returned;
  }
};

struct first_return_artifact_testimony final {
  char deed[first_return_artifact_capacity]{};
  std::uint64_t deed_fold{};
  std::uint64_t produced_artifact_fold{};
  std::uint32_t deed_bytes{};
  std::uint32_t produced_artifact_bytes{};
  exact::word observer_artifact_reads{};
  exact::word engine_source_reads{};
  bool exact{};
};

[[nodiscard]] dependent_setup_store_receipt read_dependent_theorem_setup(
    const char* path, event::dependent_theorem_setup& setup) noexcept;

[[nodiscard]] terminal_store_status collect_first_return_artifacts(
    const char* deed_path, const char* produced_artifact_path,
    first_return_artifact_testimony& testimony) noexcept;

}  // namespace holonics::apparatus
