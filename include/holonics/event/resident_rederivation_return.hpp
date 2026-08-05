#pragma once

#include <holonics/event/rederivation_surface_law.hpp>
#include <holonics/event/resident_rederivation.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline bool resident_rederivation::form_foil(
    rederivation_observation &observation) noexcept {
  if (!admitted_ || pending_live_ || stage_ != passage_stage::none ||
      !observation.inquiry.theory_formed ||
      !codec::render_rederivation_foil(
          observation.inquiry.theory.passage,
          observation.inquiry.matching.duplicate_q_vandermonde,
          observation.inquiry.cover_card.words,
          observation.inquiry.cover_card.maximum_width,
          observation.foil.formal))
    return false;
  auto continuation = body_.take_continuation();
  observation.foil.formation_commit = body_.commit(
      body_.head(), 0, 2, observation.inquiry.theory.passage.value(),
      static_cast<body::linear_continuation &&>(continuation));
  if (observation.foil.formation_commit.state !=
      body::body_change_status::committed)
    return false;
  const checker_outbound_occurrence outbound{body_.head(),
                                             exact::word{163'000},
                                             exact::word{163'001},
                                             exact::word{163'002},
                                             exact::word{163'003},
                                             exact::word{163'004},
                                             observation.inquiry.theory.passage,
                                             observation.foil.formal.identity};
  ::new (static_cast<void *>(pending_storage_))
      checker_pending_deed{body_.take_continuation(), outbound};
  pending_live_ = true;
  stage_ = passage_stage::foil_pending;
  observation.foil.outbound = outbound;
  observation.foil.checker_stage = checker_stage_status::exact;
  observation.foil.pending_before_process = true;
  return true;
}

HOLONICS_CALLABLE inline bool resident_rederivation::resume_foil(
    const checker_raw_return &raw,
    rederivation_observation &observation) noexcept {
  observation.foil.raw = raw;
  auto *pending = live_pending();
  if (pending == nullptr || !pending->resumable() ||
      stage_ != passage_stage::foil_pending)
    return false;
  const auto expected = pending->outbound();
  auto &typed = observation.foil.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  if (raw.predecessor != expected.predecessor || raw.event != expected.event ||
      raw.port != expected.expected_return_port ||
      raw.lineage.value() != expected.lineage.value() + 1U ||
      raw.passage != expected.passage || raw.source != expected.source) {
    typed.state = checker_return_status::passage_mismatch;
    return false;
  }
  constexpr char declaration[] =
      "Soma.Holonics.R30.rejected_duplicate_and_short_cover_foil";
  constexpr char source[] = "theorem rejected_duplicate_and_short_cover_foil";
  cm_checker_detail::normalize(raw, observation.foil.formal, declaration,
                               source, typed);
  const bool rejected = typed.state == checker_return_status::rejected ||
                        typed.state == checker_return_status::remaining_goals;
  auto &morphology = observation.foil.returned_morphology;
  morphology.mathematical_before = mathematical_morphology_;
  morphology.codec_before = codec_morphology_;
  mathematical_morphology_ += 1;
  codec_morphology_ += 2;
  rederivation_morphology_ += 1;
  morphology.commit =
      body_.commit(expected.predecessor, 0, 4, expected.passage.value(),
                   pending->take_continuation());
  pending_live_ = false;
  morphology.mathematical_after = mathematical_morphology_;
  morphology.codec_after = codec_morphology_;
  morphology.returned_difference_applied =
      morphology.commit.state == body::body_change_status::committed;
  observation.foil.pending_after_return = false;
  observation.foil.passage_preserved = typed.passage == expected.passage;
  observation.foil.expected_rejection = rejected;
  stage_ = rejected && morphology.returned_difference_applied
               ? passage_stage::foil_returned
               : passage_stage::none;
  return stage_ == passage_stage::foil_returned;
}

HOLONICS_CALLABLE inline bool resident_rederivation::form_valid(
    rederivation_observation &observation,
    const organ::rederivation_workspace &workspace) noexcept {
  if (!admitted_ || pending_live_ || stage_ != passage_stage::foil_returned)
    return false;
  rederivation_surface_detail::form(observation.inquiry, workspace,
                                    observation.passage.surface);
  if (!codec::render_rederivation(observation.passage.surface,
                                  observation.passage.formal) ||
      !codec::render_rederivation_dossier(
          observation.passage.surface, observation.foil.expected_rejection,
          observation.foil.raw.exit_status, observation.passage.conversational))
    return false;
  auto continuation = body_.take_continuation();
  observation.passage.formation_commit = body_.commit(
      body_.head(), 0, 55, observation.inquiry.theory.passage.value(),
      static_cast<body::linear_continuation &&>(continuation));
  if (observation.passage.formation_commit.state !=
      body::body_change_status::committed)
    return false;
  const checker_outbound_occurrence outbound{
      body_.head(),
      exact::word{163'010},
      exact::word{163'011},
      exact::word{163'012},
      exact::word{163'013},
      exact::word{163'014},
      observation.inquiry.theory.passage,
      observation.passage.formal.identity};
  ::new (static_cast<void *>(pending_storage_))
      checker_pending_deed{body_.take_continuation(), outbound};
  pending_live_ = true;
  stage_ = passage_stage::valid_pending;
  observation.passage.outbound = outbound;
  observation.passage.checker_stage = checker_stage_status::exact;
  observation.passage.pending_before_process = true;
  return true;
}

HOLONICS_CALLABLE inline bool resident_rederivation::resume_valid(
    const checker_raw_return &raw,
    rederivation_observation &observation) noexcept {
  observation.passage.raw = raw;
  auto *pending = live_pending();
  if (pending == nullptr || !pending->resumable() ||
      stage_ != passage_stage::valid_pending)
    return false;
  const auto expected = pending->outbound();
  auto &typed = observation.passage.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  if (raw.predecessor != expected.predecessor || raw.event != expected.event ||
      raw.port != expected.expected_return_port ||
      raw.lineage.value() != expected.lineage.value() + 1U ||
      raw.passage != expected.passage || raw.source != expected.source) {
    typed.state = checker_return_status::passage_mismatch;
    return false;
  }
  constexpr char declaration[] =
      "Soma.Holonics.R30.generated_plural_rederivation_ecology";
  constexpr char source[] = "theorem generated_plural_rederivation_ecology";
  cm_checker_detail::normalize(raw, observation.passage.formal, declaration,
                               source, typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  if (!codec::complete_rederivation_dossier(accepted, raw.exit_status,
                                            observation.passage.conversational))
    return false;
  auto &morphology = observation.passage.returned_morphology;
  morphology.mathematical_before = mathematical_morphology_;
  morphology.codec_before = codec_morphology_;
  mathematical_morphology_ += accepted ? 37U : 1U;
  codec_morphology_ += accepted ? 12U : 2U;
  rederivation_morphology_ += accepted ? 55U : 1U;
  const std::uint64_t delta = accepted ? 60U : 4U;
  morphology.commit =
      body_.commit(expected.predecessor, 0, delta, expected.passage.value(),
                   pending->take_continuation());
  pending_live_ = false;
  morphology.mathematical_after = mathematical_morphology_;
  morphology.codec_after = codec_morphology_;
  morphology.returned_difference_applied =
      morphology.commit.state == body::body_change_status::committed;
  observation.passage.pending_after_return = false;
  observation.passage.passage_preserved = typed.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    const exact::word ids[4]{exact::word{197'300}, exact::word{197'301},
                             exact::word{197'302}, exact::word{197'303}};
    organ::acquired_rederivation_fiber *fields[4]{
        &matching_rederivation_, &lattice_rederivation_,
        &potential_rederivation_, &cover_rederivation_};
    for (std::uint8_t i = 0; i < 4; ++i) {
      *fields[i] = {ids[i],
                    expected.passage,
                    raw.event,
                    observation.inquiry.theory.lineage,
                    exact::word{delta},
                    true};
      observation.passage.acquired[i] = *fields[i];
    }
    stage_ = passage_stage::returned;
  }
  return accepted && morphology.returned_difference_applied;
}

} // namespace holonics::event
