"""Tiny exact dimensional algebra for the tube and torsional-port chart."""
from dataclasses import dataclass
from fractions import Fraction


def exact_rational(value: int | Fraction) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise TypeError(f"exact integer/Fraction required, got {type(value).__name__}")
    return Fraction(value)


@dataclass(frozen=True)
class Dim:
    # Exponents of mass, length, time and transported content.
    e: tuple[Fraction, Fraction, Fraction, Fraction] = (Fraction(0),) * 4

    def __post_init__(self) -> None:
        if len(self.e) != 4:
            raise ValueError("dimension must carry exactly four conventional exponents")
        object.__setattr__(self, "e", tuple(exact_rational(x) for x in self.e))

    def __add__(self, other: "Dim") -> "Dim":
        return Dim(tuple(a + b for a, b in zip(self.e, other.e)))

    def __sub__(self, other: "Dim") -> "Dim":
        return Dim(tuple(a - b for a, b in zip(self.e, other.e)))

    def __mul__(self, exponent: int | Fraction) -> "Dim":
        q = exact_rational(exponent)
        return Dim(tuple(a * q for a in self.e))


M = Dim((Fraction(1), Fraction(0), Fraction(0), Fraction(0)))
L = Dim((Fraction(0), Fraction(1), Fraction(0), Fraction(0)))
T = Dim((Fraction(0), Fraction(0), Fraction(1), Fraction(0)))
Q = Dim((Fraction(0), Fraction(0), Fraction(0), Fraction(1)))
ONE = Dim()


@dataclass(frozen=True)
class Quantity:
    value: Fraction
    dim: Dim

    def __post_init__(self) -> None:
        object.__setattr__(self, "value", exact_rational(self.value))
        if not isinstance(self.dim, Dim):
            raise TypeError("Quantity dimension must be a Dim")

    @staticmethod
    def of(value: int | Fraction, dim: Dim = ONE) -> "Quantity":
        return Quantity(exact_rational(value), dim)

    def __add__(self, other: "Quantity") -> "Quantity":
        if self.dim != other.dim:
            raise ValueError(f"cannot add dimensions {self.dim.e} and {other.dim.e}")
        return Quantity(self.value + other.value, self.dim)

    def __sub__(self, other: "Quantity") -> "Quantity":
        return self + Quantity(-other.value, other.dim)

    def __mul__(self, other: "Quantity") -> "Quantity":
        return Quantity(self.value * other.value, self.dim + other.dim)

    def __truediv__(self, other: "Quantity") -> "Quantity":
        if other.value == 0:
            raise ZeroDivisionError
        return Quantity(self.value / other.value, self.dim - other.dim)

    def __pow__(self, exponent: int | Fraction) -> "Quantity":
        q = exact_rational(exponent)
        if self.value < 0 and q.denominator != 1:
            raise ValueError("nonintegral power of negative exact value")
        if q.denominator != 1:
            raise ValueError("checker supports rational dimensions, integer value powers only")
        return Quantity(self.value ** q.numerator, self.dim * q)


def require_equal(actual: Quantity, expected: Quantity, label: str) -> None:
    if actual != expected:
        raise ValueError(f"{label}: expected {expected}, got {actual}")


def require_dimension(actual: Quantity, expected: Dim, label: str) -> None:
    if actual.dim != expected:
        raise ValueError(f"{label}: expected dimension {expected.e}, got {actual.dim.e}")
