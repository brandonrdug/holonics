#pragma once

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include <holonics/body/continuing_body.hpp>
#include <holonics/receiver/condensation_response_law.hpp>

namespace holonics::event {

class resident_condensation final {
 public:
  resident_condensation() = delete;
  resident_condensation(const resident_condensation&) = delete;
  resident_condensation& operator=(const resident_condensation&) = delete;
  resident_condensation(resident_condensation&&) = delete;
  resident_condensation& operator=(resident_condensation&&) = delete;

  HOLONICS_CALLABLE explicit resident_condensation(
      const receiver::condensation_program& program,
      const body::rest_region* body_regions) noexcept
      : program_(program), body_(program.predecessor.value(), body_regions),
        admitted_tally_(program.admitted_tally), current_(program.current), lineage_(program.lineage),
        logical_resource_(program.logical_resource), group_count_(program.initial_group_count) {
    observation_.program_identity = program.identity;
    observation_.obstruction = receiver::validate_condensation_program(program);
    if (observation_.obstruction == receiver::condensation_obstruction::none &&
        !receiver::make_group_sums(program_.source_values, program_.source_count,
            program_.initial_groups, group_count_, group_sums_)) {
      observation_.obstruction = receiver::condensation_obstruction::arithmetic_refused;
    }
    observation_.predecessor = snapshot();
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr const receiver::condensation_program& program()
      const noexcept { return program_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const receiver::condensation_observation& observation()
      const noexcept { return observation_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted() const noexcept {
    return observation_.obstruction == receiver::condensation_obstruction::none;
  }

  HOLONICS_CALLABLE void apply_history(std::size_t history_slot) noexcept {
    if (!admitted() || history_slot >= receiver::condensation_history_capacity) { return; }
    const auto& input = program_.history[history_slot];
    const auto& family = active_family();
    auto& step = observation_.history[history_slot];
    step.input_occurrence = input.occurrence;
    step.input_port = input.port;
    step.common_predecessor = body_.head();
    step.direct_input_language = family.admitted_input_support;
    step.condensed_input_language = family.admitted_input_support;
    step.response.family = family.identity;
    step.response.version = family.version;
    step.response.query = exact::word{input.query};
    step.response.retained_source_support = family.admitted_input_support;
    step.response.factor_count = group_count_;
    if (input.required_family_version != family.version) {
      refuse_step(step, receiver::condensation_obstruction::family_mismatch);
      return;
    }
    if (!receiver::direct_response(program_.source_values, program_.source_count,
            family, input, step.response.direct) ||
        !receiver::boundary_response(group_sums_, active_groups(), program_.source_count,
            group_count_, family, input, step.response.factorized)) {
      refuse_step(step, receiver::condensation_obstruction::arithmetic_refused);
      return;
    }
    step.response.exact = step.response.direct == step.response.factorized;
    if (!step.response.exact) {
      refuse_step(step, receiver::condensation_obstruction::unfactorable_query);
      return;
    }
    auto predicted = snapshot();
    if (!receiver::apply_snapshot_delta(predicted, input,
            exact::word{body_.head().value() + 1U}, step.response.factorized)) {
      refuse_step(step, receiver::condensation_obstruction::arithmetic_refused);
      return;
    }
    auto capability = body_.take_continuation();
    const auto commit = body_.commit(body_.head(), static_cast<std::uint16_t>(history_slot %
        body::live_region_capacity), input.delta.value(), step.response.factorized.value(),
        static_cast<body::linear_continuation&&>(capability));
    if (commit.state != body::body_change_status::committed ||
        commit.successor != predicted.head) {
      refuse_step(step, receiver::condensation_obstruction::continuation_refused);
      return;
    }
    commit_input(input, step.response.factorized);
    step.direct_successor = predicted;
    step.condensed_successor = snapshot();
    grade_step(step);
    ++observation_.history_count;
  }

  HOLONICS_CALLABLE void refine_family() noexcept {
    if (!admitted() || refined_) { return; }
    exact::word rebuilt[receiver::condensation_group_capacity]{};
    std::uint64_t next_lineage = 0;
    std::uint64_t next_resource = 0;
    if (!receiver::make_group_sums(program_.source_values, program_.source_count,
            program_.refined_groups, program_.refined_group_count, rebuilt) ||
        !receiver::geometry_add(lineage_.value(), program_.refinement_lineage.value(),
            next_lineage) ||
        !receiver::geometry_add(logical_resource_.value(), 1U, next_resource)) {
      observation_.obstruction = receiver::condensation_obstruction::arithmetic_refused;
      return;
    }
    auto& result = observation_.refinement;
    result.occurrence = program_.refinement_occurrence;
    result.predecessor = body_.head();
    result.old_family = program_.initial_family.identity;
    result.old_version = program_.initial_family.version;
    result.new_family = program_.refined_family.identity;
    result.new_version = program_.refined_family.version;
    result.reconstruction_capability = program_.reconstruction_capability;
    result.lineage = program_.refinement_lineage;
    result.old_group_count = group_count_;
    result.new_group_count = program_.refined_group_count;
    auto capability = body_.take_continuation();
    const auto commit = body_.commit(body_.head(), 0, 0, current_.value(),
        static_cast<body::linear_continuation&&>(capability));
    if (commit.state != body::body_change_status::committed) {
      observation_.obstruction = receiver::condensation_obstruction::continuation_refused;
      return;
    }
    refined_ = true;
    group_count_ = program_.refined_group_count;
    for (std::size_t group = 0; group < group_count_; ++group) { group_sums_[group] = rebuilt[group]; }
    lineage_ = exact::word{next_lineage};
    logical_resource_ = exact::word{next_resource};
    result.successor = commit.successor;
    result.family_grew = true;
    result.source_reopened = true;
    result.exact_reconstruction = true;
    result.retained_fiber = true;
  }

  HOLONICS_CALLABLE void finish() noexcept {
    observation_.successor = snapshot();
    observation_.factorized_boundary = true;
    observation_.stateful_bisimulation =
        observation_.history_count == receiver::condensation_history_capacity;
    for (std::size_t slot = 0; slot < observation_.history_count; ++slot) {
      observation_.factorized_boundary &= observation_.history[slot].response.exact;
      observation_.stateful_bisimulation &=
          observation_.history[slot].complete_successor_equal;
    }
    observation_.source_fiber_retained =
        observation_.refinement.retained_fiber && program_.reconstruction_capability.value() != 0;
    observation_.non_resumable = true;
  }

 private:
  [[nodiscard]] HOLONICS_CALLABLE const receiver::future_receiver_family& active_family()
      const noexcept { return refined_ ? program_.refined_family : program_.initial_family; }
  [[nodiscard]] HOLONICS_CALLABLE const std::uint16_t* active_groups() const noexcept {
    return refined_ ? program_.refined_groups : program_.initial_groups;
  }
  [[nodiscard]] HOLONICS_CALLABLE receiver::condensed_snapshot snapshot() const noexcept {
    return receiver::make_condensed_snapshot(program_, program_.source_values, body_.head(),
        admitted_tally_, current_, lineage_, logical_resource_, observation_.obstruction);
  }
  HOLONICS_CALLABLE void commit_input(const receiver::condensation_input& input,
      exact::word response) noexcept {
    const std::size_t group = active_groups()[input.source_cell];
    program_.source_values[input.source_cell] = exact::word{
        program_.source_values[input.source_cell].value() + input.delta.value()};
    group_sums_[group] = exact::word{group_sums_[group].value() + input.delta.value()};
    admitted_tally_ = exact::word{admitted_tally_.value() + input.delta.value()};
    current_ = response;
    lineage_ = exact::word{lineage_.value() + input.lineage.value()};
    logical_resource_ = exact::word{logical_resource_.value() + 1U};
  }
  HOLONICS_CALLABLE static void refuse_step(receiver::boundary_bisimulation_step& step,
      receiver::condensation_obstruction obstruction) noexcept {
    step.direct_obstruction = obstruction;
    step.condensed_obstruction = obstruction;
    step.obstruction_equal = true;
  }
  HOLONICS_CALLABLE static void grade_step(
      receiver::boundary_bisimulation_step& step) noexcept {
    step.next_language_equal = step.direct_input_language == step.condensed_input_language;
    step.testimony_equal = step.response.direct == step.response.factorized;
    step.obstruction_equal = step.direct_obstruction == step.condensed_obstruction;
    step.incidence_equal = step.direct_successor.incidence == step.condensed_successor.incidence;
    step.current_equal = step.direct_successor.current == step.condensed_successor.current;
    step.admitted_tally_equal = step.direct_successor.admitted_tally == step.condensed_successor.admitted_tally;
    step.alternatives_equal = step.direct_successor.alternatives == step.condensed_successor.alternatives;
    step.lineage_equal = step.direct_successor.lineage == step.condensed_successor.lineage;
    step.logical_resource_equal = step.direct_successor.logical_resource ==
        step.condensed_successor.logical_resource;
    step.complete_successor_equal = receiver::equal_condensed_snapshot(
        step.direct_successor, step.condensed_successor);
  }

  receiver::condensation_program program_{};
  body::continuing_body body_;
  receiver::condensation_observation observation_{};
  exact::word admitted_tally_{};
  exact::word current_{};
  exact::word lineage_{};
  exact::word logical_resource_{};
  exact::word group_sums_[receiver::condensation_group_capacity]{};
  std::uint16_t group_count_{};
  bool refined_{};
};

static_assert(std::is_trivially_destructible_v<resident_condensation>);

}  // namespace holonics::event
