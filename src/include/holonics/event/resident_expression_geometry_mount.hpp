#pragma once

#include <holonics/event/resident_expression_geometry.hpp>

namespace holonics::event {
HOLONICS_CALLABLE inline resident_expression_geometry::resident_expression_geometry(
    const organ::expression_geometry_foundation& foundation,
    const intrinsic_hypergeometry_rest_record& record,
    intrinsic_hypergeometry_remount_receipt& receipt) noexcept
    : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
      first_(record.first), second_(record.second), geometry_(record.geometry),
      phase_crystal_(record.phase_crystal), characteristic_(record.characteristic),
      regular_singular_(record.regular_singular), code_reconstruction_(record.code_reconstruction),
      moment_reconstruction_(record.moment_reconstruction), cm_incidence_(record.cm_incidence),
      toric_cycle_(record.toric_cycle), algebraic_variation_(record.algebraic_variation),
      causal_linear_(record.causal_linear), intrinsic_hypergeometry_(record.intrinsic_hypergeometry),
      source_detached_(true) {
  const bool exact = record.integrity == intrinsic_hypergeometry_rest_integrity(record);
  receipt.theory = intrinsic_hypergeometry_.identity;
  receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && intrinsic_hypergeometry_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved &&
      organ::expression_geometry_detail::valid_foundation(foundation_);
}

HOLONICS_CALLABLE inline resident_expression_geometry::resident_expression_geometry(
    const expression_geometry_rest_record& record,
    expression_geometry_remount_receipt& receipt) noexcept
    : body_(body::continuing_body::remount(record.body, receipt.body)), first_(record.first),
      second_(record.second), geometry_(record.geometry), phase_crystal_(record.phase_crystal),
      characteristic_(record.characteristic), regular_singular_(record.regular_singular),
      code_reconstruction_(record.code_reconstruction),
      moment_reconstruction_(record.moment_reconstruction), cm_incidence_(record.cm_incidence),
      toric_cycle_(record.toric_cycle), algebraic_variation_(record.algebraic_variation),
      causal_linear_(record.causal_linear), intrinsic_hypergeometry_(record.intrinsic_hypergeometry),
      expression_geometry_(record.expression_geometry),
      stage_(passage_stage::returned), source_detached_(true) {
  const bool exact = record.integrity == expression_geometry_rest_integrity(record);
  receipt.theory = expression_geometry_.identity;
  receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && expression_geometry_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved;
}

}  // namespace holonics::event
