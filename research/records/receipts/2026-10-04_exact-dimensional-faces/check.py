"""Exact bounded consistency receipt; not part of HNN execution."""
from dataclasses import dataclass
from fractions import Fraction as F
import resource
import time

from dimensions import L, M, ONE, Q, T, Dim, Quantity as V, require_dimension, require_equal

started_ns = time.monotonic_ns()


def expect_refusal(label, operation):
    try:
        operation()
    except (TypeError, ValueError, ZeroDivisionError):
        print(f"reject {label}")
    else:
        raise AssertionError(f"expected refusal: {label}")


def expect_exact(actual, expected, label):
    if actual != expected:
        raise AssertionError(f"{label}: expected {expected}, got {actual}")


# Runtime exactness: annotations do not stop Fraction(float) from appearing.
expect_refusal("float coefficient", lambda: V.of(0.1))
expect_refusal("float dimension exponent", lambda: Dim((0.1, 0, 0, 0)))
expect_refusal("float power", lambda: V.of(2) ** 0.5)

# Tube section. The actual two derivative columns share one producing epsilon.
a, b, c, s = (V.of(1, L) for _ in range(4))
u, v, eps = V.of(F(1, 2)), V.of(0), V.of(F(1, 4))
xu = a * (V.of(1) + V.of(2) * eps * u)
xv = b * (V.of(1) + eps * u)
xs = c / s
area = xu * xv
require_dimension(xs, ONE, "longitudinal derivative")
require_dimension(xu, L, "first section derivative")
require_dimension(xv, L, "second section derivative")
require_dimension(area, L * 2, "section area")
expect_refusal("adding length to dimensionless section coordinate", lambda: a + u)


@dataclass(frozen=True)
class BoundaryReceipt:
    quantity_role: str
    dimension: Dim
    proper_basis: tuple[str, ...]
    orientation: tuple[str, str, str]
    normalization: str
    domain: str
    source_clock: str
    receiver_clock: str
    phase_branch: str
    phase_carry: int
    producing_family: object

    def require_admitted(self, role, dimension, basis, orientation, normalization, domain,
                         source_clock, receiver_clock, family,
                         phase_branch="lifted-phase-log", phase_carry=0):
        wanted = (role, dimension, basis, orientation, normalization, domain,
                  source_clock, receiver_clock, phase_branch, phase_carry)
        actual = (self.quantity_role, self.dimension, self.proper_basis, self.orientation,
                  self.normalization, self.domain, self.source_clock,
                  self.receiver_clock, self.phase_branch, self.phase_carry)
        if actual != wanted or self.producing_family is not family:
            raise ValueError("boundary receipt does not match the declared producing operands")


family_eps0 = object()
frame = ("t", "d1", "d2")
receipt = BoundaryReceipt(
    "oriented_section_area", L * 2, frame, ("du", "dv", "+t"),
    "d1 cross d2 = +t; area coefficient retained", "u²+v²<=1; 2|epsilon|<1",
    "spine-clock", "receiver-clock", "lifted-phase-log", 0, family_eps0)
receipt.require_admitted("oriented_section_area", L * 2, frame, ("du", "dv", "+t"),
    "d1 cross d2 = +t; area coefficient retained", "u²+v²<=1; 2|epsilon|<1",
    "spine-clock", "receiver-clock", family_eps0)
expect_refusal("same units, wrong quantity role",
               lambda: receipt.require_admitted("energy", L * 2, frame, ("du", "dv", "+t"),
                   "d1 cross d2 = +t; area coefficient retained",
                   "u²+v²<=1; 2|epsilon|<1", "spine-clock", "receiver-clock", family_eps0))
expect_refusal("same units, substituted source clock",
               lambda: receipt.require_admitted("oriented_section_area", L * 2, frame,
                   ("du", "dv", "+t"), "d1 cross d2 = +t; area coefficient retained",
                   "u²+v²<=1; 2|epsilon|<1", "other-spine-clock",
                   "receiver-clock", family_eps0))
expect_refusal("same units, substituted phase branch",
               lambda: receipt.require_admitted("oriented_section_area", L * 2, frame,
                   ("du", "dv", "+t"), "d1 cross d2 = +t; area coefficient retained",
                   "u²+v²<=1; 2|epsilon|<1", "spine-clock", "receiver-clock",
                   family_eps0, phase_branch="other-phase-log"))
expect_refusal("same units, substituted phase carry",
               lambda: receipt.require_admitted("oriented_section_area", L * 2, frame,
                   ("du", "dv", "+t"), "d1 cross d2 = +t; area coefficient retained",
                   "u²+v²<=1; 2|epsilon|<1", "spine-clock", "receiver-clock",
                   family_eps0, phase_carry=1))

storage_work_role = BoundaryReceipt(
    "stored_energy", M + L * 2 - T * 2, ("u", "w"), ("u,w", "+"),
    "E_* native quadratic form", "finite declared receiver chart", "mechanical-clock",
    "mechanical-clock", "principal+2pi*n", 0, object())
expect_refusal("same M L^2 T^-2 units do not identify torque with stored energy",
               lambda: storage_work_role.require_admitted("constitutive_torque",
                   M + L * 2 - T * 2, ("u", "w"), ("u,w", "+"),
                   "E_* native quadratic form", "finite declared receiver chart",
                   "mechanical-clock", "mechanical-clock", storage_work_role.producing_family,
                   phase_branch="principal+2pi*n"))

# Clock conversion is a typed relation between addressed clocks. Under a declared
# differentiable t_source(tau_receiver), every source-rate term and chart rate
# receives the same exact alpha = dt_source/dtau_receiver.
@dataclass(frozen=True)
class ClockRate:
    source: str
    receiver: str
    alpha: F


def convert_source_rate(clock_rate, value):
    if not isinstance(clock_rate, ClockRate):
        raise TypeError("addressed ClockRate required")
    return value * V.of(clock_rate.alpha)


clock_rate = ClockRate("spine-clock", "receiver-clock", F(2, 3))
rho_s = V.of(2, Q - L * 3)
j_s = V.of(5, Q - L * 2 - T)
w_s = V.of(1, L - T)
sigma_s = V.of(7, Q - L * 3 - T)
rho_w_s = rho_s * w_s
relative_j_receiver = convert_source_rate(clock_rate, j_s - rho_w_s)
sigma_receiver = convert_source_rate(clock_rate, sigma_s)
w_receiver = convert_source_rate(clock_rate, w_s)
require_dimension(relative_j_receiver, Q - L * 2 - T, "reclocked relative current")
require_dimension(sigma_receiver, Q - L * 3 - T, "reclocked source rate")
require_dimension(w_receiver, L - T, "reclocked chart velocity")
expect_exact(relative_j_receiver.value, F(2), "alpha*(j-rho*w)")
expect_exact(sigma_receiver.value, F(14, 3), "alpha*sigma")
expect_exact(w_receiver.value, F(2, 3), "alpha*w")

@dataclass(frozen=True)
class PhaseIncrement:
    receiver_clock: str
    branch: str
    carry: int
    omega: V
    h: V

    def read(self, declared_clock):
        if self.receiver_clock != declared_clock:
            raise ValueError("phase increment uses a different receiver clock")
        result = self.omega * self.h
        require_dimension(result, ONE, "omega*h phase increment")
        return result


phase_step = PhaseIncrement("receiver-clock", "principal+2pi*n", 1,
                            V.of(F(2, 3), T * -1), V.of(3, T))
expect_exact(phase_step.read("receiver-clock").value, F(2), "omega*h")
expect_exact(phase_step.branch, "principal+2pi*n", "phase branch retained")
expect_exact(phase_step.carry, 1, "phase carry retained")
expect_refusal("phase increment on another receiver clock",
               lambda: phase_step.read("other-receiver-clock"))

# Full moving chart dimensional faces. Conventional M,L,T,Q exponents are a
# receiver shadow only; typed source/receiver clock identity remains above.
J = V.of(1, L * 2)
rho = V.of(1, Q - L * 3)
j = V.of(1, Q - L * 2 - T)
w_phys = V.of(1, L - T)
rho_hat = J * rho
relative_current = j - rho * w_phys
flux_s = J * V.of(1, Q - L * 2 - T)
flux_u = J * V.of(1, Q - L * 3 - T)
flux_v = J * V.of(1, Q - L * 3 - T)
require_dimension(rho_hat, Q - L, "J rho on reference section")
require_dimension(flux_s, Q - T, "longitudinal pulled-back flux")
require_dimension(flux_u, Q - L - T, "transverse u pulled-back flux")
require_dimension(flux_v, Q - L - T, "transverse v pulled-back flux")
require_dimension(relative_current, Q - L * 2 - T, "physical relative current")
continuity_dt = rho_hat / V.of(1, T)
continuity_ds = flux_s / V.of(1, L)
continuity_du, continuity_dv = flux_u, flux_v
for label, term in (("time derivative", continuity_dt), ("s divergence", continuity_ds),
                    ("u divergence", continuity_du), ("v divergence", continuity_dv)):
    require_dimension(term, Q - L - T, f"continuity {label}")

# Metric entries pair differential-column units: (X_s,X_u,X_v)=(1,L,L).
differential_column_units = (ONE, L, L)
gss = V.of(1, differential_column_units[0] + differential_column_units[0])
gsu = V.of(1, differential_column_units[0] + differential_column_units[1])
guu = V.of(1, differential_column_units[1] + differential_column_units[1])
require_dimension(gss, ONE, "gss")
require_dimension(gsu, L, "gsu")
require_dimension(guu, L * 2, "guu")

# Port normalization maps, kept as equations in one declared torsional realization.
E_star = V.of(5, M + L * 2 - T * 2)
T_star = V.of(3, T)
unum, wnum, hnum = V.of(F(2, 3)), V.of(F(1, 3)), V.of(F(1, 5))
Cnum, Knum, Dnum, Gnum = V.of(2), V.of(3), V.of(4), V.of(5)
anum, bnum, aoutnum, boutnum = (V.of(F(k, 7)) for k in (1, 2, 3, 4))
u_phys = unum
w_phys_port = wnum / T_star
h_phys = T_star * hnum
C_phys = E_star * (T_star ** 2) * Cnum
K_phys = E_star * Knum
D_phys = E_star * T_star * Dnum
Gc_phys = Gnum / (E_star * T_star)
a_phys, b_phys, aout_phys, bout_phys = (E_star * x for x in (anum, bnum, aoutnum, boutnum))
for label, quantity, dimension in (
    ("u", u_phys, ONE), ("w", w_phys_port, T * -1), ("h", h_phys, T),
    ("C", C_phys, M + L * 2), ("K", K_phys, M + L * 2 - T * 2),
    ("D", D_phys, M + L * 2 - T), ("Gc", Gc_phys, T - M - L * 2),
    ("a", a_phys, M + L * 2 - T * 2), ("b", b_phys, M + L * 2 - T * 2),
    ("aout", aout_phys, M + L * 2 - T * 2), ("bout", bout_phys, M + L * 2 - T * 2)):
    require_dimension(quantity, dimension, f"port map {label}")

# Physical storage energy must equal E_* times the native energy. Use a nonzero
# rate so the deliberate C_phys ×2 mutation cannot hide in a zero kinetic term.
Estar_dim = M + L * 2 - T * 2
native_energy = (Cnum * (wnum ** 2) + Knum * (unum ** 2)) / V.of(2)
physical_energy = (C_phys * (w_phys_port ** 2) + K_phys * (u_phys ** 2)) / V.of(2)
require_equal(physical_energy, E_star * native_energy, "physical/native storage energy")
expect_refusal("factor-two C_phys breaks storage-energy normalization",
               lambda: require_equal((V.of(2) * C_phys * (w_phys_port ** 2) +
                                       K_phys * (u_phys ** 2)) / V.of(2),
                                      E_star * native_energy, "mutated storage energy"))

# The port solve's terms and work face are dimensionally closed.
C = V.of(1, M + L * 2)
K = V.of(1, M + L * 2 - T * 2)
D = V.of(1, M + L * 2 - T)
Gc = V.of(1, T - M - L * 2)
h = V.of(1, T)
omega = V.of(1, T * -1)
torque = V.of(1, M + L * 2 - T * 2)
u_angle = V.of(1)
mass_solve = V.of(2) * C + V.of(2) * h / Gc + h * D + (h ** 2) * K / V.of(2)
rhs = h * torque + V.of(2) * C * omega - h * K * u_angle
storage = (C * (omega ** 2) + K * (u_angle ** 2)) / V.of(2)
port_work = h * Gc * (torque ** 2) / V.of(4)
require_dimension(mass_solve, M + L * 2, "torsional solve denominator")
require_dimension(rhs, M + L * 2 - T, "torsional solve numerator")
require_dimension(rhs / mass_solve, T * -1, "torsional output angular rate")
require_dimension(storage, Estar_dim, "storage energy")
require_dimension(port_work, Estar_dim, "port work")

# Exact oriented/family witness at a=b=1,u=1/2,v=0. The section profile is
# from the same family at both columns. A different admissible family is refused.
def exact_area(epsilon):
    return (1 + epsilon * F(1, 2)) * (1 + 2 * epsilon * F(1, 2))

area_source = exact_area(F(0))
area_same_family = exact_area(F(0))
area_other_family = exact_area(F(1, 4))
assert area_source == area_same_family == F(1)
assert area_other_family == F(45, 32)
assert abs(F(1, 4)) < F(1, 2)
assert F(1) + F(1, 4) * F(1, 2) > 0
assert F(1) + 2 * F(1, 4) * F(1, 2) > 0
expect_refusal("same units, another family's exact area",
               lambda: require_equal(V.of(area_other_family, L * 2),
                                     V.of(area_source, L * 2), "producing-family area"))
expect_refusal("section formula mixed with another producing family",
               lambda: receipt.require_admitted("oriented_section_area", L * 2, frame,
                   ("du", "dv", "+t"), "d1 cross d2 = +t; area coefficient retained",
                   "u²+v²<=1; 2|epsilon|<1", "spine-clock", "receiver-clock", object()))
expect_refusal("swapped section-column orientation",
               lambda: require_equal(V.of(-area_source, L * 2),
                                     V.of(area_source, L * 2), "oriented area sign"))

# Finite exact affine-work witness, in normalized coordinates. Source/target
# scales are retained and T_ij carries target_i/source_j units. The additive
# source term c remains in the affine map and contributes both cross and self work.
Tnum = ((F(1), F(2)), (F(3), F(4)))
cnum = (F(1, 2), F(-1, 3))
xnum = (F(2), F(-1, 2))
Gnum_mat = ((F(4), F(1)), (F(1), F(3)))
source_scales = (V.of(1), V.of(1) / T_star)
target_scales = (V.of(2), V.of(1) / (V.of(2) * T_star))
Tphys = tuple(tuple(target_scales[i] / source_scales[j] * V.of(Tnum[i][j])
                    for j in range(2)) for i in range(2))
cphys = tuple(target_scales[i] * V.of(cnum[i]) for i in range(2))
xphys = tuple(source_scales[i] * V.of(xnum[i]) for i in range(2))
for i in range(2):
    for j in range(2):
        require_dimension(Tphys[i][j], target_scales[i].dim - source_scales[j].dim,
                          f"T[{i},{j}] target/source chart units")

def mat_vec(mat, vec):
    return tuple(sum((mat[i][j] * vec[j] for j in range(2)), V.of(0, mat[i][0].dim + vec[0].dim))
                 for i in range(2))

def qform(mat, vec):
    return sum((vec[i] * mat[i][j] * vec[j] for i in range(2) for j in range(2)),
               V.of(0, vec[0].dim + mat[0][0].dim + vec[0].dim)) / V.of(2)

Gphys = tuple(tuple(E_star * V.of(Gnum_mat[i][j]) /
                    (target_scales[i] * target_scales[j]) for j in range(2))
              for i in range(2))
for i, j, wanted in ((0, 0, Estar_dim), (0, 1, Estar_dim + T),
                     (1, 1, Estar_dim + T * 2)):
    require_dimension(Gphys[i][j], wanted, f"G[{i},{j}] coordinate metric")
y_num_linear = tuple(sum((V.of(Tnum[i][j]) * V.of(xnum[j]) for j in range(2)), V.of(0))
                        for i in range(2))
y_num = tuple(y_num_linear[i] + V.of(cnum[i]) for i in range(2))
y_phys = tuple(sum((Tphys[i][j] * xphys[j] for j in range(2)), cphys[i])
               for i in range(2))
physical_affine_energy = qform(Gphys, y_phys)
native_affine_energy = E_star * qform(tuple(tuple(V.of(x) for x in row) for row in Gnum_mat),
                                     y_num)
require_equal(physical_affine_energy, native_affine_energy, "affine chart energy")
linear_energy = qform(tuple(tuple(V.of(x) for x in row) for row in Gnum_mat),
                      y_num_linear)
cross_work = sum((y_num_linear[i] * V.of(Gnum_mat[i][j]) * V.of(cnum[j])
                  for i in range(2) for j in range(2)), V.of(0))
offset_energy = qform(tuple(tuple(V.of(x) for x in row) for row in Gnum_mat),
                      tuple(V.of(x) for x in cnum))
require_equal(qform(tuple(tuple(V.of(x) for x in row) for row in Gnum_mat),
                    y_num),
              linear_energy + cross_work + offset_energy, "affine work with source term")

print("pass dimensions: candidate pulled-back balance terms, mixed metric, declared torsional port")
print("pass clock identities: alpha*(j-rho*w), alpha*sigma, alpha*w on addressed clocks")
print("pass exact witnesses: source area=1; alternate epsilon area=45/32")
print("pass affine work: rational source/target scales, map, and additive term retained")
print("pass storage normalization: nonzero-rate physical energy equals E_* native energy")
print(f"receipt monotonic_ns start={started_ns} stop={time.monotonic_ns()} maxrss={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss} unit=KiB")
