#pragma once

#include <concepts>

#include <holonics/exact/word.hpp>

namespace holonics::event {

struct obstruction_marker final {};

template<class Obstruction>
concept obstruction = requires(const Obstruction& value) {
  typename Obstruction::holonics_obstruction;
  { value.code() } -> std::same_as<exact::word>;
} && std::same_as<typename Obstruction::holonics_obstruction, obstruction_marker>;

class open_obstruction final {
 public:
  using holonics_obstruction = obstruction_marker;

  explicit constexpr open_obstruction(exact::word code) noexcept : code_(code) {}

  [[nodiscard]] constexpr exact::word code() const noexcept { return code_; }

 private:
  exact::word code_;
};

static_assert(obstruction<open_obstruction>);

}  // namespace holonics::event
