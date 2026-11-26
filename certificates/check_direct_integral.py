"""Independent integration of the pair-switch response at 17 rational points.

Polynomials use monomials T^a z^b U^c, where
U = sqrt((1-s^2)(1-z^2)) cos(phi). No Bernstein or moment recurrence
is used to integrate the response. Python 3 standard library only.
"""
from fractions import Fraction as F
from functools import cache
from math import comb
from pathlib import Path
import re

from check_qutrit import check_two_fifths

ONE = {(0, 0, 0): F(1)}
T = {(1, 0, 0): F(1)}
Z = {(0, 1, 0): F(1)}
U = {(0, 0, 1): F(1)}


def add(*polys):
    result = {}
    for poly in polys:
        for key, value in poly.items():
            result[key] = result.get(key, 0) + value
    return {k: v for k, v in result.items() if v}


def scale(poly, factor):
    return {k: v * factor for k, v in poly.items() if factor}


def mul(p, q):
    result = {}
    for (a, b, c), v in p.items():
        for (i, j, k), w in q.items():
            key = (a+i, b+j, c+k)
            result[key] = result.get(key, 0) + v*w
    return {k: v for k, v in result.items() if v}


def power(poly, n):
    result = ONE
    for _ in range(n):
        result = mul(result, poly)
    return result


@cache
def haar_monomial(a, b, c, s):
    if c % 2:
        return 0
    h = c // 2
    z_integral = sum(F((-1)**j * comb(h, j), b + 2*j + 1) for j in range(h + 1))
    return F(2, a+2) * F(comb(2*h, h), 4**h) * (1-s*s)**h * z_integral


def direct_switch(s):
    l = F(2, 3)
    k = 2*l-l*l
    low = scale(mul(T, add(ONE, scale(Z, -s), U)), F(1, 2))
    high = add(low, scale(mul(T, Z), s))
    # H is the lower binomial tail on nine independent Bernoulli trials.
    no = add(ONE, scale(low, -1))
    gate = add(ONE, *(scale(mul(power(low, i), power(no, 9-i)), -comb(9, i))
                      for i in range(3)))
    # Evaluate tr(P_high B_low) before doing the angular or radial averages.
    anticommutator = add(high, low, scale(T, -s*s))
    first = add(high, scale(anticommutator, -l), scale(low, l*l*(1-s*s)))
    second = scale(mul(mul(low, add(ONE, low)), add(T, scale(low, -1))), k*s*s)
    integrand = mul(mul(mul(T, Z), low), mul(gate, add(first, second)))
    return F(3, 2)*sum(v*haar_monomial(*key, s) for key, v in integrand.items())


def kernel_coefficients():
    text = (Path(__file__).resolve().parents[1] /
            "ManuscriptProofs/QutritCertificate.lean").read_text(encoding="utf-8")
    block = text.split("noncomputable def switchMoment", 1)[1].split("noncomputable def kappa", 1)[0]
    expression = block.split(":=", 1)[1].strip()
    numerator, denominator = expression[1:].split(") /")
    terms = re.findall(r"([+-]?)\s*(\d+)(?:\s*\*\s*s(?:\s*\^\s*(\d+))?)?", numerator)
    coefficients = [F(0)]*15
    for i, (sign, coefficient, exponent) in enumerate(terms):
        j = int(exponent) if exponent else int(i != 0)
        coefficients[j] = F((-1 if sign == "-" else 1)*int(coefficient), int(denominator))
    return coefficients


def main():
    polynomial = check_two_fifths()
    assert polynomial == kernel_coefficients(), "Lean power basis differs from the moment sums"
    for j in range(17):
        s = F(j, 16)
        predicted = sum(v*s**i for i, v in enumerate(polynomial))
        assert direct_switch(s) == predicted, f"direct integration failed at {s}"
    print("All 17 exact direct Haar integrals agree with the degree-14 polynomial.")
    print("The power-basis coefficients match the Lean definition exactly.")


if __name__ == "__main__":
    main()
