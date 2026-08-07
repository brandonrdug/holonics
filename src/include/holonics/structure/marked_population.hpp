#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/identity_mint.hpp>
#include <holonics/structure/occurrence.hpp>
#include <holonics/structure/parallel_arena.hpp>

namespace holonics::structure {

inline constexpr std::size_t marked_source_capacity = 4;
inline constexpr std::size_t marked_occurrence_capacity = 16'384;
inline constexpr std::size_t marked_relation_capacity = 16'384;
inline constexpr std::uint16_t no_marked_slot = 65'535U;

class marked_source final {
 public:
  marked_source() = delete;
  HOLONICS_CALLABLE constexpr marked_source(
      identity<source_identity_owner> source,
      std::uint16_t occurrence_begin,
      std::uint16_t occurrence_count,
      std::uint16_t relation_begin,
      std::uint16_t cut_begin) noexcept
      : source_(source), occurrence_begin_(occurrence_begin),
        occurrence_count_(occurrence_count), relation_begin_(relation_begin), cut_begin_(cut_begin) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<source_identity_owner> source() const noexcept {
    return source_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t occurrence_begin() const noexcept {
    return occurrence_begin_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t occurrence_count() const noexcept {
    return occurrence_count_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t relation_begin() const noexcept {
    return relation_begin_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t cut_begin() const noexcept {
    return cut_begin_;
  }
  friend HOLONICS_CALLABLE constexpr bool operator==(
      const marked_source& left, const marked_source& right) noexcept {
    return left.source_ == right.source_ && left.occurrence_begin_ == right.occurrence_begin_ &&
        left.occurrence_count_ == right.occurrence_count_ &&
        left.relation_begin_ == right.relation_begin_ && left.cut_begin_ == right.cut_begin_;
  }

 private:
  identity<source_identity_owner> source_;
  std::uint16_t occurrence_begin_{};
  std::uint16_t occurrence_count_{};
  std::uint16_t relation_begin_{};
  std::uint16_t cut_begin_{};
};

class marked_occurrence final {
 public:
  marked_occurrence() = delete;
  HOLONICS_CALLABLE constexpr marked_occurrence(
      identity<occurrence_identity_owner> occurrence,
      identity<source_identity_owner> source,
      identity<event_cut_identity_owner> begin_cut,
      identity<event_cut_identity_owner> end_cut,
      identity<lineage_identity_owner> lineage,
      exact::word payload,
      std::uint16_t source_slot,
      std::uint16_t local_coordinate,
      std::uint16_t incoming,
      std::uint16_t outgoing) noexcept
      : occurrence_(occurrence), source_(source), begin_cut_(begin_cut), end_cut_(end_cut),
        lineage_(lineage), payload_(payload), source_slot_(source_slot),
        local_coordinate_(local_coordinate), incoming_(incoming), outgoing_(outgoing) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<occurrence_identity_owner> occurrence() const noexcept {
    return occurrence_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<source_identity_owner> source() const noexcept {
    return source_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word payload() const noexcept { return payload_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t source_slot() const noexcept {
    return source_slot_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t local_coordinate() const noexcept {
    return local_coordinate_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t incoming() const noexcept { return incoming_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t outgoing() const noexcept { return outgoing_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<event_cut_identity_owner> begin_cut() const noexcept {
    return begin_cut_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<event_cut_identity_owner> end_cut() const noexcept {
    return end_cut_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<lineage_identity_owner> lineage() const noexcept {
    return lineage_;
  }
  friend HOLONICS_CALLABLE constexpr bool operator==(
      const marked_occurrence& left, const marked_occurrence& right) noexcept {
    return left.occurrence_ == right.occurrence_ && left.source_ == right.source_ &&
        left.begin_cut_ == right.begin_cut_ && left.end_cut_ == right.end_cut_ &&
        left.lineage_ == right.lineage_ && left.payload_ == right.payload_ &&
        left.source_slot_ == right.source_slot_ &&
        left.local_coordinate_ == right.local_coordinate_ &&
        left.incoming_ == right.incoming_ && left.outgoing_ == right.outgoing_;
  }

 private:
  identity<occurrence_identity_owner> occurrence_;
  identity<source_identity_owner> source_;
  identity<event_cut_identity_owner> begin_cut_;
  identity<event_cut_identity_owner> end_cut_;
  identity<lineage_identity_owner> lineage_;
  exact::word payload_{};
  std::uint16_t source_slot_{};
  std::uint16_t local_coordinate_{};
  std::uint16_t incoming_{};
  std::uint16_t outgoing_{};
};

class marked_relation final {
 public:
  marked_relation() = delete;
  HOLONICS_CALLABLE constexpr marked_relation(
      identity<event_identity_owner> event,
      identity<port_identity_owner> port,
      identity<lineage_identity_owner> lineage,
      std::uint16_t from,
      std::uint16_t to,
      exact::word local_label) noexcept
      : event_(event), port_(port), lineage_(lineage), local_label_(local_label),
        from_(from), to_(to) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t from() const noexcept { return from_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t to() const noexcept { return to_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word local_label() const noexcept {
    return local_label_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<event_identity_owner> event() const noexcept {
    return event_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<port_identity_owner> port() const noexcept {
    return port_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<lineage_identity_owner> lineage() const noexcept {
    return lineage_;
  }
  friend HOLONICS_CALLABLE constexpr bool operator==(
      const marked_relation& left, const marked_relation& right) noexcept {
    return left.event_ == right.event_ && left.port_ == right.port_ &&
        left.lineage_ == right.lineage_ && left.local_label_ == right.local_label_ &&
        left.from_ == right.from_ && left.to_ == right.to_;
  }
 private:
  identity<event_identity_owner> event_;
  identity<port_identity_owner> port_;
  identity<lineage_identity_owner> lineage_;
  exact::word local_label_{};
  std::uint16_t from_{};
  std::uint16_t to_{};
};

}  // namespace holonics::structure
