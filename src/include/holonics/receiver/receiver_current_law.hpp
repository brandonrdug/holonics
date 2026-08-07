#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/integer_arithmetic.hpp>
#include <holonics/structure/local_population.hpp>

namespace holonics::receiver {

inline constexpr std::size_t path_population_limbs = 8;
using path_population = exact::unsigned_integer<path_population_limbs>;

/// One directed passage between two receiver sites.
struct receiver_passage final {
  std::uint32_t antecedent{};
  std::uint32_t consequent{};
};

/// What one site received at one arrival wave.
///
/// **Equal-arrival predecessor incidence is retained factorized: the exact path
/// population is carried as a wide integer and the paths themselves are never
/// enumerated.** A population of `10^30` paths costs one addition, not `10^30`
/// visits, and it never collapses into a machine word.
struct arrival final {
  path_population population{};
  std::uint32_t wave{};
  std::uint32_t predecessors{};
  bool reached{};
};

enum class radiation_state : std::uint8_t {
  returned,
  horizon_reached,
  capacity_refused,
  population_refused
};

struct radiation_receipt final {
  radiation_state state{radiation_state::capacity_refused};
  std::uint32_t waves{};
  std::uint32_t reached_sites{};
  std::uint32_t visited_passages{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool returned() const noexcept {
    return state == radiation_state::returned ||
        state == radiation_state::horizon_reached;
  }
};

/// The information-calculus engine: sites, passages, and radiation to a declared
/// horizon inside a declared aperture. Work follows the reached front, never the
/// retained population.
template<std::size_t SiteCapacity, std::size_t PassageCapacity>
class receiver_current_law final {
  static_assert(SiteCapacity > 0 && PassageCapacity > 0);

 public:
  HOLONICS_CALLABLE constexpr receiver_current_law() noexcept : passages_{}, arrivals_{} {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t sites() const noexcept {
    return sites_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t passages() const noexcept {
    return passages_used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const arrival& at(
      std::uint32_t site) const noexcept {
    return arrivals_[site];
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t found_site() noexcept {
    if (sites_ >= SiteCapacity) {
      return structure::no_ordinal;
    }
    const std::uint32_t minted = sites_;
    sites_ = sites_ + 1U;
    return minted;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool found_passage(
      std::uint32_t antecedent,
      std::uint32_t consequent) noexcept {
    if (passages_used_ >= PassageCapacity || antecedent >= sites_ ||
        consequent >= sites_ || antecedent == consequent) {
      return false;
    }
    passages_[passages_used_] = receiver_passage{antecedent, consequent};
    passages_used_ = passages_used_ + 1U;
    return true;
  }

  /// Radiate from one origin to a declared horizon. Each wave adds the exact
  /// predecessor populations of the sites it reaches; nothing enumerates a path.
  [[nodiscard]] HOLONICS_CALLABLE constexpr radiation_receipt radiate_to_horizon(
      std::uint32_t origin,
      std::uint32_t horizon) noexcept {
    radiation_receipt receipt{};
    if (origin >= sites_) {
      return receipt;
    }
    for (std::uint32_t site = 0; site < sites_; ++site) {
      arrivals_[site] = arrival{};
    }
    arrivals_[origin].population = path_population::from_word(1);
    arrivals_[origin].reached = true;
    arrivals_[origin].wave = 0;
    receipt.reached_sites = 1;
    for (std::uint32_t wave = 0; wave < horizon; ++wave) {
      bool advanced = false;
      for (std::uint32_t slot = 0; slot < passages_used_; ++slot) {
        const receiver_passage crossing = passages_[slot];
        if (!arrivals_[crossing.antecedent].reached ||
            arrivals_[crossing.antecedent].wave != wave) {
          continue;
        }
        receipt.visited_passages = receipt.visited_passages + 1U;
        arrival& target = arrivals_[crossing.consequent];
        const auto joined =
            exact::add(target.population, arrivals_[crossing.antecedent].population);
        if (!joined.accepted()) {
          receipt.state = radiation_state::population_refused;
          return receipt;
        }
        if (!target.reached) {
          target.reached = true;
          target.wave = wave + 1U;
          receipt.reached_sites = receipt.reached_sites + 1U;
        }
        if (target.wave == wave + 1U) {
          target.population = joined.value;
          target.predecessors = target.predecessors + 1U;
          advanced = true;
        }
      }
      receipt.waves = wave + 1U;
      if (!advanced) {
        receipt.state = radiation_state::returned;
        return receipt;
      }
    }
    receipt.state = radiation_state::horizon_reached;
    return receipt;
  }

 private:
  receiver_passage passages_[PassageCapacity]{};
  arrival arrivals_[SiteCapacity]{};
  std::uint32_t sites_{};
  std::uint32_t passages_used_{};
};

}  // namespace holonics::receiver
