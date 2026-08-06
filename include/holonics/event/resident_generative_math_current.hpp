#pragma once

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include <holonics/event/generative_math_return.hpp>
#include <holonics/organ/generative_math_law.hpp>
#include <holonics/receiver/generative_math_question.hpp>

namespace holonics::event {

class resident_generative_math_current final {
 public:
  resident_generative_math_current() = delete;
  resident_generative_math_current(const resident_generative_math_current&) = delete;
  resident_generative_math_current& operator=(const resident_generative_math_current&) = delete;
  resident_generative_math_current(resident_generative_math_current&&) = delete;
  resident_generative_math_current& operator=(resident_generative_math_current&&) = delete;

  HOLONICS_CALLABLE resident_generative_math_current(
      const organ::generative_math_foundation& foundation,
      std::uint64_t body_seed,
      const body::rest_region* regions,
      bool source_detached) noexcept
      : foundation_(foundation), body_(body_seed, regions), source_detached_(source_detached),
        obstruction_(organ::valid_generative_foundation(foundation)
            ? organ::generative_obstruction::none
            : organ::generative_obstruction::invalid_foundation) {}

  [[nodiscard]] HOLONICS_CALLABLE organ::generative_obstruction obstruction() const noexcept {
    return obstruction_;
  }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }

  [[nodiscard]] HOLONICS_CALLABLE generative_math_return generate(
      const receiver::generative_math_question& question) noexcept {
    generative_math_return result{};
    result.source_detached = source_detached_;
    if (obstruction_ != organ::generative_obstruction::none) { return result; }
    const organ::generative_math_goal goal{question.identity, question.receiver,
        question.premise_declaration, question.target_type, question.metavariable,
        question.maximum_dependencies,
        question.orientation == receiver::equivalence_orientation::reverse};
    auto& receipt = result.generation;
    receipt.expansion = organ::expand_generative_fibers(foundation_, goal);
    if (receipt.expansion.obstruction != organ::generative_obstruction::receiver_underdetermined) {
      receipt.obstruction = receipt.expansion.obstruction;
      return result;
    }
    organ::proof_fiber selected{};
    std::uint16_t retained = 0;
    if (!organ::restrict_generative_fibers(receipt.expansion, selected, retained)) {
      receipt.obstruction = organ::generative_obstruction::no_consequence;
      return result;
    }
    std::uint64_t statement = 0;
    std::uint64_t proof = 0;
    std::uint64_t passage = 0;
    if (!organ::exact_add(question.identity.value(), 10'000, statement) ||
        !organ::exact_add(question.identity.value(), 20'000, proof) ||
        !organ::exact_add(question.identity.value(), 30'000, passage)) {
      receipt.obstruction = organ::generative_obstruction::arithmetic_refused;
      return result;
    }
    receipt.passage = {exact::word{passage}, exact::word{statement}, exact::word{proof},
        question.target_type, question.premise_declaration, selected.rule, selected.lineage,
        selected.formation, true, true};
    receipt.exclusion.generated_statement = receipt.passage.statement;
    receipt.exclusion.generated_proof = receipt.passage.proof;
    receipt.exclusion.distinct_from_inherited = generated_identity_is_new(receipt.passage);
    receipt.exclusion.absent_before_generation = receipt.exclusion.distinct_from_inherited;

    const exact::word predecessor = body_.head();
    auto continuation = body_.take_continuation();
    const auto commit = body_.commit(predecessor, 0, 3, passage,
        static_cast<body::linear_continuation&&>(continuation));
    if (commit.state != body::body_change_status::committed) {
      receipt.obstruction = organ::generative_obstruction::continuation_refused;
      return result;
    }
    receipt.information = {question.identity, question.receiver, predecessor, commit.successor,
        commit.continuation_before, selected.lineage, exact::word{3},
        receipt.expansion.open_count, retained,
        organ::generative_obstruction::receiver_underdetermined, true, true, true};
    const codec::generated_math_surface surface{receipt.passage.identity,
        receipt.passage.statement, receipt.passage.proof, receipt.passage.premise_declaration,
        1, 1};
    if (!codec::render_formal_math_face(surface, result.formal) ||
        !codec::render_conversational_math_face(surface, result.conversational)) {
      receipt.obstruction = organ::generative_obstruction::render_refused;
      return result;
    }
    receipt.obstruction = organ::generative_obstruction::none;
    receipt.exact_local_expansion = true;
    receipt.exact_receiver_restriction = true;
    receipt.proof_current_lineaged = true;
    result.final_head = body_.head();
    result.final_region = body_.region(0);
    result.same_closed_passage = result.formal.passage == result.conversational.passage &&
        result.formal.passage == receipt.passage.identity;
    result.continuation_valid = body_.can_open();
    return result;
  }

 private:
  [[nodiscard]] HOLONICS_CALLABLE bool generated_identity_is_new(
      const organ::generated_math_passage& passage) const noexcept {
    const exact::word inherited[7]{foundation_.ecology, foundation_.premise_declaration,
        foundation_.premise_type, foundation_.premise_proof, foundation_.provenance,
        foundation_.rules[0].identity, foundation_.rules[1].identity};
    for (const auto identity : inherited) {
      if (passage.identity == identity || passage.statement == identity || passage.proof == identity) {
        return false;
      }
    }
    return true;
  }

  organ::generative_math_foundation foundation_{};
  body::continuing_body body_;
  bool source_detached_{};
  organ::generative_obstruction obstruction_{organ::generative_obstruction::invalid_foundation};
};

static_assert(std::is_trivially_destructible_v<resident_generative_math_current>);

}  // namespace holonics::event
