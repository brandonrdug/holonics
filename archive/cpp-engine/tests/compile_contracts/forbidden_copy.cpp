#include <concepts>

#include <holonics/apparatus/resident_world_contract.hpp>
#include <holonics/body/ownership.hpp>
#include <holonics/codec/environment_contract.hpp>
#include <holonics/event/deed.hpp>

static_assert(
    std::copy_constructible<holonics::body::continuation_capability>,
    "continuation capability must not be copy constructible");
static_assert(
    std::copy_constructible<holonics::body::body_contract>,
    "body contract must not be copy constructible");
static_assert(
    std::copy_constructible<holonics::body::live_morphology_contract>,
    "live morphology must not be copy constructible");
static_assert(
    std::copy_constructible<holonics::event::pending_contract>,
    "pending deed must not be copy constructible");
static_assert(
    std::copy_constructible<holonics::event::delta_contract>,
    "delta must not be copy constructible");
static_assert(
    std::copy_constructible<holonics::apparatus::resident_world_contract>,
    "resident world must not be copy constructible");
static_assert(
    std::copy_constructible<holonics::codec::environment_contract>,
    "codec environment must not be copy constructible");
static_assert(
    std::copy_constructible<holonics::body::rest_ownership>,
    "rest ownership must not be copy constructible");
static_assert(
    std::is_copy_assignable_v<holonics::body::continuation_capability>,
    "continuation capability must not be copy assignable");
static_assert(
    std::is_copy_assignable_v<holonics::body::body_contract>,
    "body contract must not be copy assignable");
static_assert(
    std::is_copy_assignable_v<holonics::body::live_morphology_contract>,
    "live morphology must not be copy assignable");
static_assert(
    std::is_copy_assignable_v<holonics::event::pending_contract>,
    "pending deed must not be copy assignable");
static_assert(
    std::is_copy_assignable_v<holonics::event::delta_contract>,
    "delta must not be copy assignable");
static_assert(
    std::is_copy_assignable_v<holonics::apparatus::resident_world_contract>,
    "resident world must not be copy assignable");
static_assert(
    std::is_copy_assignable_v<holonics::codec::environment_contract>,
    "codec environment must not be copy assignable");
static_assert(
    std::is_copy_assignable_v<holonics::body::rest_ownership>,
    "rest ownership must not be copy assignable");
