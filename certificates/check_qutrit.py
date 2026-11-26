"""Exact polynomial checks for the qutrit Haar-parent protocols. Python 3, standard library."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb


def add(*polys):
    return [sum((p[i] for p in polys if i < len(p)), F(0))
            for i in range(max(map(len, polys)))]


def scale(p, a):
    return [a * v for v in p]


def multiply(p, q):
    return [sum((p[j] * q[i-j] for j in range(len(p)) if 0 <= i-j < len(q)), F(0))
            for i in range(len(p) + len(q) - 1)]


@lru_cache(None)
def moment(r, n):
    """Power-basis coefficients of E[z**r * ell**n] as a polynomial in s."""
    result = [F(0)] * (n + 1)
    for b in range(n // 2 + 1):
        angular = F(comb(n, 2*b) * comb(2*b, b), 2**n * 4**b)
        for a in range(n - 2*b + 1):
            integral = sum(F((-1)**j * comb(b, j), r + a + 2*j + 1)
                           for j in range(b + 1))
            term = angular * comb(n-2*b, a) * (-1)**a * integral
            for j in range(b + 1):
                result[a + 2*j] += term * (-1)**j * comb(b, j)
    return result


def switch_polynomial(h, lam, last_power):
    """Compute gamma and the polynomial s*c(s)."""
    keep = add([1], scale(h, -1))
    gamma = sum(a * F(6, 8) * (F(3, (m+2)*(m+3)) - F(7, (m+3)*(m+4)))
                for m, a in enumerate(h))
    k = 2*lam - lam**2
    result = [F(0)]
    for m, weight in enumerate(keep):
        if not weight:
            continue
        part = add(multiply([(1-lam)**2, 0, -lam**2], moment(1, m+2)),
                   [0] + scale(moment(2, m+1), 1-lam),
                   [0, 0] + scale(moment(1, m+1), lam))
        part = scale(part, F(3, m+5))
        for j in range(last_power + 1):
            difference = add(moment(1, m+j+2), scale(moment(1, m+j+3), -1))
            part = add(part, [0, 0] + scale(difference, 3*k / (m+j+6)))
        result = add(result, scale(part, weight))
    return gamma, result


def trim(p):
    while len(p) > 1 and not p[-1]:
        p.pop()
    return p


def bernstein(p):
    n = len(p) - 1
    return [sum(p[j] * F(comb(i, j), comb(n, j)) for j in range(i+1))
            for i in range(n+1)]


def check_two_fifths():
    h = multiply([(-1)**i * comb(7, i) for i in range(8)], [1, 7, 28])
    gamma, cs = switch_polynomial(h, F(2, 3), 1)
    assert gamma == F(419, 11440) < F(1, 20)
    b = bernstein(trim(add(cs, [0, -F(1, 20), 0, gamma])))
    floors = [int(v * 100000 // 1) for v in b]
    assert floors == [917, 670, 470, 316, 204, 131, 91, 79, 88, 109, 134, 152, 152, 118, 30]
    kappa = F(339259, 1107025920)
    assert min(b) == b[-1] == kappa > 0
    visibility = F(2, 5) + 3*kappa
    assert visibility == F(29588543, 73801728)
    assert F(5, 12) - visibility == F(1162177, 73801728)
    print("gamma =", gamma, "and kappa =", kappa, "(attained at s=1)")
    print("visibility =", visibility, "and projective gap =", F(5, 12) - visibility)
    return trim(cs)


def check_elementary_protocol():
    gamma, cs = switch_polynomial([0], F(4, 5), 2)
    c = F(523, 11200)
    factor = [1680, -12072, 26379, 10251, -555, -555]
    expected = add([0, c], scale(multiply([1, -1], factor), F(1, 448000)))
    assert gamma == 0 and trim(cs) == trim(expected)
    assert 12072**2 < 4*1680*26379 and 10251 > 2*555
    print("Without the qubit input: visibility =", F(1, 4) + 3*c)


if __name__ == "__main__":
    check_two_fifths()
    check_elementary_protocol()

