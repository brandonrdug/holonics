#pragma once

#include <cstdint>
#include <type_traits>

#include <holonics/structure/complex_schema.hpp>
#include <holonics/structure/occurrence.hpp>

namespace holonics::structure {

class resident_cell final {
 public:
  using occurrence_identity = identity<occurrence_identity_owner>;
  using lineage_identity = identity<lineage_identity_owner>;
  using region_identity = identity<region_identity_owner>;

  resident_cell() = delete;
  HOLONICS_CALLABLE constexpr resident_cell(
      occurrence_identity occurrence,
      lineage_identity lineage,
      region_identity region,
      std::uint8_t dimension,
      exact::word multiplicity) noexcept
      : occurrence_(occurrence),
        lineage_(lineage),
        region_(region),
        multiplicity_(multiplicity),
        dimension_(dimension) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr occurrence_identity occurrence() const noexcept {
    return occurrence_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t dimension() const noexcept {
    return dimension_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool active() const noexcept { return active_; }
  HOLONICS_CALLABLE constexpr void depart() noexcept { active_ = false; }
  HOLONICS_CALLABLE constexpr void set_outgoing(
      std::uint16_t begin,
      std::uint16_t count) noexcept {
    outgoing_begin_ = begin;
    outgoing_count_ = count;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t outgoing_begin() const noexcept {
    return outgoing_begin_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t outgoing_count() const noexcept {
    return outgoing_count_;
  }
  HOLONICS_CALLABLE constexpr void attach_incidence() noexcept { ++incident_count_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t incident_count() const noexcept {
    return incident_count_;
  }

 private:
  occurrence_identity occurrence_;
  lineage_identity lineage_;
  region_identity region_;
  exact::word multiplicity_{};
  std::uint16_t outgoing_begin_{};
  std::uint16_t outgoing_count_{};
  std::uint16_t incident_count_{};
  std::uint8_t dimension_{};
  bool active_{true};
};

class resident_incidence final {
 public:
  resident_incidence() = delete;
  HOLONICS_CALLABLE constexpr resident_incidence(
      std::uint16_t higher_slot,
      std::uint16_t lower_slot,
      identity<event_identity_owner> event,
      identity<port_identity_owner> port,
      identity<lineage_identity_owner> lineage,
      std::int8_t orientation,
      exact::word multiplicity) noexcept
      : event_(event),
        port_(port),
        lineage_(lineage),
        multiplicity_(multiplicity),
        higher_slot_(higher_slot),
        lower_slot_(lower_slot),
        orientation_(orientation) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t higher_slot() const noexcept {
    return higher_slot_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t lower_slot() const noexcept {
    return lower_slot_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::int8_t orientation() const noexcept {
    return orientation_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word multiplicity() const noexcept {
    return multiplicity_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool active() const noexcept { return active_; }
  HOLONICS_CALLABLE constexpr void depart() noexcept { active_ = false; }

 private:
  identity<event_identity_owner> event_;
  identity<port_identity_owner> port_;
  identity<lineage_identity_owner> lineage_;
  exact::word multiplicity_{};
  std::uint16_t higher_slot_{};
  std::uint16_t lower_slot_{};
  std::int8_t orientation_{};
  bool active_{true};
};

class persistent_path_node final {
 public:
  persistent_path_node() = delete;
  HOLONICS_CALLABLE constexpr persistent_path_node(
      identity<occurrence_identity_owner> occurrence,
      std::uint16_t parent) noexcept
      : occurrence_(occurrence), parent_(parent) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<occurrence_identity_owner> occurrence()
      const noexcept {
    return occurrence_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t parent() const noexcept {
    return parent_;
  }

 private:
  identity<occurrence_identity_owner> occurrence_;
  std::uint16_t parent_{};
};

static_assert(std::is_trivially_destructible_v<resident_cell>);
static_assert(std::is_trivially_destructible_v<resident_incidence>);
static_assert(std::is_trivially_destructible_v<persistent_path_node>);

}  // namespace holonics::structure
