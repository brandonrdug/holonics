#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/body/continuation.hpp>
#include <holonics/body/rest_record.hpp>
#include <holonics/structure/identity_mint.hpp>

namespace holonics::body {

struct body_head_identity_owner final {};

enum class body_change_status : std::uint8_t {
  committed,
  stale_predecessor,
  invalid_continuation,
  invalid_region,
  capacity_refused
};

struct body_change_receipt final {
  body_change_status state{body_change_status::invalid_continuation};
  exact::word predecessor{};
  exact::word successor{};
  exact::word continuation_before{};
  exact::word continuation_after{};
  std::uint16_t region{};
  std::uint64_t morphology_before{};
  std::uint64_t morphology_after{};
};

class continuing_body final {
 public:
  continuing_body() = delete;
  continuing_body(const continuing_body&) = delete;
  continuing_body& operator=(const continuing_body&) = delete;
  HOLONICS_CALLABLE continuing_body(continuing_body&& other) noexcept
      : head_mint_(static_cast<structure::identity_mint<body_head_identity_owner>&&>(other.head_mint_)),
        head_(other.head_), continuation_(static_cast<linear_continuation&&>(other.continuation_)),
        next_continuation_(other.next_continuation_), lineage_(other.lineage_) {
    for (std::size_t slot = 0; slot < live_region_capacity; ++slot) { regions_[slot] = other.regions_[slot]; }
  }
  continuing_body& operator=(continuing_body&&) = delete;

  HOLONICS_CALLABLE continuing_body(
      std::uint64_t owner_seed,
      const rest_region* regions) noexcept
      : head_mint_(owner_seed), head_(head_mint_.mint()),
        continuation_(exact::word{owner_seed + 1'000'000U}),
        next_continuation_(owner_seed + 1'000'001U), lineage_(owner_seed + 2'000'000U) {
    for (std::size_t slot = 0; slot < live_region_capacity; ++slot) { regions_[slot] = regions[slot]; }
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word head() const noexcept {
    return head_.serial();
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool can_open() const noexcept {
    return continuation_.valid();
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word continuation_serial() const noexcept {
    return continuation_.serial();
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word lineage() const noexcept {
    return exact::word{lineage_};
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const rest_region& region(std::size_t slot) const noexcept {
    return regions_[slot];
  }
  [[nodiscard]] HOLONICS_CALLABLE linear_continuation take_continuation() noexcept {
    return static_cast<linear_continuation&&>(continuation_);
  }
  HOLONICS_CALLABLE void recover(linear_continuation&& capability) noexcept {
    if (!continuation_.valid() && capability.valid()) {
      continuation_ = static_cast<linear_continuation&&>(capability);
    }
  }

  [[nodiscard]] HOLONICS_CALLABLE body_change_receipt commit(
      exact::word predecessor,
      std::uint16_t region_slot,
      std::uint64_t morphology_delta,
      std::uint64_t successor_current,
      linear_continuation&& capability) noexcept {
    body_change_receipt receipt{};
    receipt.predecessor = head_.serial();
    receipt.successor = head_.serial();
    receipt.continuation_before = capability.serial();
    receipt.continuation_after = capability.serial();
    receipt.region = region_slot;
    if (predecessor != head_.serial()) { receipt.state = body_change_status::stale_predecessor; }
    else if (!capability.valid() || continuation_.valid()) { receipt.state = body_change_status::invalid_continuation; }
    else if (region_slot >= live_region_capacity) { receipt.state = body_change_status::invalid_region; }
    else if (~std::uint64_t{0} - regions_[region_slot].morphology < morphology_delta) {
      receipt.state = body_change_status::capacity_refused;
    } else {
      receipt.morphology_before = regions_[region_slot].morphology;
      regions_[region_slot].morphology += morphology_delta;
      regions_[region_slot].current = successor_current;
      receipt.morphology_after = regions_[region_slot].morphology;
      capability.consume();
      head_ = head_mint_.mint();
      continuation_ = linear_continuation{exact::word{next_continuation_++}};
      ++lineage_;
      receipt.state = body_change_status::committed;
      receipt.successor = head_.serial();
      receipt.continuation_after = continuation_.serial();
      return receipt;
    }
    receipt.morphology_before = region_slot < live_region_capacity ? regions_[region_slot].morphology : 0;
    receipt.morphology_after = receipt.morphology_before;
    recover(static_cast<linear_continuation&&>(capability));
    return receipt;
  }

  [[nodiscard]] HOLONICS_CALLABLE rest_receipt rest(rest_record& record) noexcept {
    rest_receipt receipt{};
    if (!continuation_.valid()) { return receipt; }
    record.head = head_.serial().value();
    record.next_head = head_mint_.next_serial().value();
    record.continuation = continuation_.serial().value();
    record.next_continuation = next_continuation_;
    record.lineage = lineage_;
    for (std::size_t slot = 0; slot < live_region_capacity; ++slot) { record.regions[slot] = regions_[slot]; }
    record.integrity = rest_integrity(record);
    continuation_.consume();
    receipt.returned = true;
    receipt.integrity_exact = true;
    receipt.head = exact::word{record.head};
    receipt.continuation = exact::word{record.continuation};
    receipt.integrity = exact::word{record.integrity};
    return receipt;
  }

  [[nodiscard]] HOLONICS_CALLABLE static continuing_body remount(
      const rest_record& record,
      rest_receipt& receipt) noexcept {
    const bool integrity_valid = record.integrity == rest_integrity(record);
    continuing_body result{record, integrity_valid};
    receipt.returned = integrity_valid;
    receipt.integrity_exact = integrity_valid;
    receipt.source_replay_count = 0;
    receipt.head = exact::word{record.head};
    receipt.continuation = exact::word{record.continuation};
    receipt.integrity = exact::word{record.integrity};
    return result;
  }

 private:
  HOLONICS_CALLABLE continuing_body(const rest_record& record, bool integrity_valid) noexcept
      : head_mint_(record.next_head), head_(structure::identity_mint<body_head_identity_owner>{record.head}.mint()),
        continuation_(exact::word{record.continuation}), next_continuation_(record.next_continuation),
        lineage_(record.lineage) {
    for (std::size_t slot = 0; slot < live_region_capacity; ++slot) {
      regions_[slot] = integrity_valid ? record.regions[slot] : rest_region{};
    }
    if (!integrity_valid) { continuation_.consume(); }
  }

  structure::identity_mint<body_head_identity_owner> head_mint_;
  structure::identity<body_head_identity_owner> head_;
  linear_continuation continuation_;
  std::uint64_t next_continuation_{};
  std::uint64_t lineage_{};
  rest_region regions_[live_region_capacity]{};
};

}  // namespace holonics::body
