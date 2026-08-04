#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/marked_population.hpp>

namespace holonics::structure {

class resident_marked_population final {
 public:
  resident_marked_population() = delete;
  resident_marked_population(const resident_marked_population&) = delete;
  resident_marked_population& operator=(const resident_marked_population&) = delete;
  resident_marked_population(resident_marked_population&&) = delete;
  resident_marked_population& operator=(resident_marked_population&&) = delete;

  HOLONICS_CALLABLE explicit resident_marked_population(
      std::uint64_t owner_seed,
      std::size_t source_count,
      std::size_t occurrence_count,
      std::size_t relation_count) noexcept
      : occurrence_mint_(owner_seed), source_mint_(owner_seed + 1'000'000U),
        cut_mint_(owner_seed + 2'000'000U), lineage_mint_(owner_seed + 3'000'000U),
        event_mint_(owner_seed + 4'000'000U), port_mint_(owner_seed + 5'000'000U),
        occurrences_(occurrence_mint_.reserve(occurrence_count)),
        sources_(source_mint_.reserve(source_count)),
        cuts_(cut_mint_.reserve(occurrence_count + source_count)),
        lineages_(lineage_mint_.reserve(occurrence_count + relation_count)),
        events_(event_mint_.reserve(relation_count)), ports_(port_mint_.reserve(relation_count)) {
    admitted_ = source_count <= marked_source_capacity &&
        occurrence_count <= marked_occurrence_capacity && relation_count <= marked_relation_capacity &&
        source_arena_.reserve(source_count) && occurrence_arena_.reserve(occurrence_count) &&
        relation_arena_.reserve(relation_count);
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted() const noexcept { return admitted_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr auto source_id(std::size_t slot) const noexcept {
    return sources_.at(slot);
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr auto occurrence_id(std::size_t slot) const noexcept {
    return occurrences_.at(slot);
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr auto cut_id(std::size_t slot) const noexcept {
    return cuts_.at(slot);
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr auto lineage_id(std::size_t slot) const noexcept {
    return lineages_.at(slot);
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr auto event_id(std::size_t slot) const noexcept {
    return events_.at(slot);
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr auto port_id(std::size_t slot) const noexcept {
    return ports_.at(slot);
  }

  template<class... Arguments>
  HOLONICS_CALLABLE marked_source& construct_source(std::size_t slot, Arguments... arguments) noexcept {
    return source_arena_.construct(slot, arguments...);
  }
  template<class... Arguments>
  HOLONICS_CALLABLE marked_occurrence& construct_occurrence(
      std::size_t slot, Arguments... arguments) noexcept {
    return occurrence_arena_.construct(slot, arguments...);
  }
  template<class... Arguments>
  HOLONICS_CALLABLE marked_relation& construct_relation(
      std::size_t slot, Arguments... arguments) noexcept {
    return relation_arena_.construct(slot, arguments...);
  }

  [[nodiscard]] HOLONICS_CALLABLE const marked_source& source(std::size_t slot) const noexcept {
    return source_arena_.at(slot);
  }
  [[nodiscard]] HOLONICS_CALLABLE const marked_occurrence& occurrence(std::size_t slot) const noexcept {
    return occurrence_arena_.at(slot);
  }
  [[nodiscard]] HOLONICS_CALLABLE const marked_relation& relation(std::size_t slot) const noexcept {
    return relation_arena_.at(slot);
  }

 private:
  identity_mint<occurrence_identity_owner> occurrence_mint_;
  identity_mint<source_identity_owner> source_mint_;
  identity_mint<event_cut_identity_owner> cut_mint_;
  identity_mint<lineage_identity_owner> lineage_mint_;
  identity_mint<event_identity_owner> event_mint_;
  identity_mint<port_identity_owner> port_mint_;
  identity_reservation<occurrence_identity_owner> occurrences_{};
  identity_reservation<source_identity_owner> sources_{};
  identity_reservation<event_cut_identity_owner> cuts_{};
  identity_reservation<lineage_identity_owner> lineages_{};
  identity_reservation<event_identity_owner> events_{};
  identity_reservation<port_identity_owner> ports_{};
  parallel_arena<marked_source, marked_source_capacity> source_arena_{};
  parallel_arena<marked_occurrence, marked_occurrence_capacity> occurrence_arena_{};
  parallel_arena<marked_relation, marked_relation_capacity> relation_arena_{};
  bool admitted_{};
};

}  // namespace holonics::structure
