#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/body/continuing_body.hpp>
#include <holonics/structure/occurrence.hpp>

namespace holonics::event {
struct deed_request final {
  std::uint64_t owner_seed{};
  std::uint16_t region{};
  std::uint64_t payload{};
};

struct deed_return final {
  std::uint64_t predecessor{};
  std::uint64_t event{};
  std::uint64_t port{};
  std::uint64_t lineage{};
  std::uint64_t payload{};
};

using deed_outbound_port = structure::port<deed_request, structure::port_direction::outbound>;
using deed_return_port = structure::port<deed_return, structure::port_direction::inbound>;

enum class lifecycle_status : std::uint8_t {
  exact,
  continuation_unavailable,
  stale_return,
  foreign_return,
  wrong_return_port,
  already_resumed,
  malformed_return
};

struct outbound_occurrence final {
  std::uint64_t predecessor{};
  std::uint64_t event{};
  std::uint64_t occurrence{};
  std::uint64_t outbound_port{};
  std::uint64_t expected_return_port{};
  std::uint64_t lineage{};
  std::uint64_t payload{};
  std::uint16_t region{};
};

struct complete_delta_receipt final {
  std::uint64_t predecessor{};
  std::uint64_t input_event{};
  std::uint64_t return_event{};
  std::uint64_t read_support{};
  std::uint64_t change_support{};
  std::int64_t incidence_delta{};
  std::uint64_t successor_current{};
  std::uint64_t returned_consequence{};
  std::uint64_t stress{};
  std::uint64_t obstruction{};
  std::uint64_t logical_resource{};
  std::uint64_t lineage{};
  std::uint16_t region{};
};

struct body_observation final {
  std::uint64_t head{};
  std::uint64_t continuation{};
  std::uint64_t lineage{};
  body::rest_region regions[body::live_region_capacity]{};
};

struct lifecycle_adversarial_receipt final {
  lifecycle_status second_open{lifecycle_status::malformed_return};
  lifecycle_status foreign_return{lifecycle_status::malformed_return};
  lifecycle_status stale_return{lifecycle_status::malformed_return};
  lifecycle_status correct_return{lifecycle_status::malformed_return};
  lifecycle_status double_return{lifecycle_status::malformed_return};
  // The capacity-refusal case was removed on 2026-08-07 with the counter that
  // was its only trigger. A refusal case with no reachable cause is not
  // evidence, and the obligation it carried — a typed refusal leaves the body
  // untouched and returns the capability — is established by the five cases
  // above and by the interruption cases below.
  bool interruption_predecessors[3]{};
  bool interruption_successor{};
};

struct lifecycle_output final {
  outbound_occurrence outbound{};
  lifecycle_status resume_state{lifecycle_status::malformed_return};
  complete_delta_receipt delta{};
  body::body_change_receipt commit{};
  body_observation predecessor{};
  body_observation successor{};
  body::rest_receipt rest{};
  body::rest_receipt remount{};
  body_observation remounted{};
  lifecycle_adversarial_receipt adversarial{};
  std::uint16_t exterior_returns{};
  std::uint16_t source_replays{};
};

}  // namespace holonics::event
