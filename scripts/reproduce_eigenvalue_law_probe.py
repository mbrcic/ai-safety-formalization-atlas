#!/usr/bin/env python3
"""Numerical stress evidence for the O70-EIGEN-LAW frontier (candidate Prop 8.11).

This is V7 evidence for `AISafetyAtlas.SingularLearning.EigenvalueLawStatement`.
It is **not** a proof and not an inhabitant: it is a falsification attempt. Every
kernel-checked anchor in `EigenvalueLaw.lean` other than `eigenvalueLaw_ratio`
instantiates `T = 0` and `rho = 0`, which never exercises the weight exponent
under `T`, the factor prod (1 + T s_i)^(-rho), or the Vandermonde factor. This
script exercises all three.

The frontier says: for every wide shape k <= d there is a single positive Z,
quantified BEFORE rho and T, with

    int_{R^{k x d}} e^{-|X|_F^2} det(1 + T X X^T)^{-rho} dX
      = Z * J(k, T, (d - k - 1)/2, rho)

    J(k, T, alpha, rho) = int_{(0,inf)^k} e^{-sum s_i} (prod s_i^alpha)
                            * |Vandermonde(s)| * prod (1 + T s_i)^{-rho} ds .

Because Z is unpinned, no single (T, rho) can falsify a wrong constant. What can
falsify a wrong *shape* is the ratio: Z cancels between two parameter choices,
so LHS(T1,rho1) * J(T2,rho2) - LHS(T2,rho2) * J(T1,rho1) must vanish. That is
exactly `eigenvalueLaw_ratio`, and it is what this script tests numerically.

Two regimes:

  k = 1  reduces analytically. XX^T is the scalar |X|^2, so the left side is a
         radial integral, and substituting u = r^2 turns it into the same
         one-dimensional integral the right side already is. The check is
         therefore exact rather than statistical, and it pins Z = pi^(d/2) /
         Gamma(d/2). It tests the weight exponent (d - k - 1)/2 -- formed in R,
         so negative at d = 1 -- and the (1 + T s)^{-rho} factor. The Vandermonde
         is trivially 1 at k = 1, so this regime cannot test it.

  k = 2  is the smallest shape with a nontrivial Vandermonde |s_1 - s_2|. The
         left side is a 4- or 6-dimensional integral with no radial reduction, so
         it is estimated by Monte-Carlo against the Gaussian factor; the right
         side is a two-dimensional quadrature. Tolerances are loose accordingly,
         and a Vandermonde-free variant is run alongside to confirm the test has
         the power to reject it.

Stdlib only, deterministic seed. Run:  python3 scripts/reproduce_eigenvalue_law_probe.py
Exit 0 iff every check passes.
"""

from __future__ import annotations

import math
import random
import sys

FAILURES: list[str] = []


def check(name: str, got: float, want: float, tol: float) -> None:
    ok = abs(got - want) <= tol * max(1.0, abs(want))
    print(f"[{'ok ' if ok else 'FAIL'}] {name}: got {got:.10g}, want {want:.10g}")
    if not ok:
        FAILURES.append(name)


def check_true(name: str, ok: bool, detail: str = "") -> None:
    print(f"[{'ok ' if ok else 'FAIL'}] {name}{(' -- ' + detail) if detail else ''}")
    if not ok:
        FAILURES.append(name)


# --------------------------------------------------------------------------
# Quadrature. The orthant integrands carry s^alpha with alpha >= -1/2, singular
# at 0 for d = 1 and d = 2. The substitution s = t^2 removes it: s^alpha ds
# becomes 2 t^(2 alpha + 1) dt, and 2 alpha + 1 = d - k >= 0 on every shape we
# probe. Simpson on the t variable is then integrating a smooth function.
# --------------------------------------------------------------------------

def simpson(f, a: float, b: float, n: int = 20000) -> float:
    if n % 2:
        n += 1
    h = (b - a) / n
    total = f(a) + f(b)
    for i in range(1, n):
        total += (4 if i % 2 else 2) * f(a + i * h)
    return total * h / 3


def orthant_1d(alpha: float, T: float, rho: float, t_max: float = 9.0) -> float:
    """int_0^inf e^{-s} s^alpha (1 + T s)^{-rho} ds, via s = t^2."""
    def g(t: float) -> float:
        s = t * t
        return 2.0 * t ** (2.0 * alpha + 1.0) * math.exp(-s) * (1.0 + T * s) ** (-rho)
    return simpson(g, 0.0, t_max)


def orthant_2d(alpha: float, T: float, rho: float, vandermonde: bool = True,
               t_max: float = 7.0, n: int = 420) -> float:
    """J at k = 2, via s_i = t_i^2 on both coordinates."""
    def row(t1: float) -> float:
        s1 = t1 * t1
        f1 = 2.0 * t1 ** (2.0 * alpha + 1.0) * math.exp(-s1) * (1.0 + T * s1) ** (-rho)

        def g(t2: float) -> float:
            s2 = t2 * t2
            f2 = 2.0 * t2 ** (2.0 * alpha + 1.0) * math.exp(-s2) * (1.0 + T * s2) ** (-rho)
            return f1 * f2 * (abs(s1 - s2) if vandermonde else 1.0)
        return simpson(g, 0.0, t_max, n)
    return simpson(row, 0.0, t_max, n)


# --------------------------------------------------------------------------
# k = 1: exact reduction.
#
#   LHS(d, T, rho) = S_{d-1} int_0^inf r^{d-1} e^{-r^2} (1 + T r^2)^{-rho} dr
#                  = (S_{d-1}/2) int_0^inf u^{(d-2)/2} e^{-u} (1 + T u)^{-rho} du
#
# and the right-hand orthant integral at k = 1 is that same integral with
# alpha = (d - 1 - 1)/2 = (d - 2)/2 and Vandermonde 1. So Z = S_{d-1}/2, with
# S_{d-1} = 2 pi^(d/2) / Gamma(d/2) the surface measure of the unit sphere.
# --------------------------------------------------------------------------

def lhs_k1(d: int, T: float, rho: float) -> float:
    alpha = (d - 2) / 2.0
    sphere = 2.0 * math.pi ** (d / 2.0) / math.gamma(d / 2.0)
    return (sphere / 2.0) * orthant_1d(alpha, T, rho)


def probe_k1() -> None:
    print("\n-- k = 1: exact reduction; tests the weight exponent and (1+Ts)^-rho --")
    for d in (1, 2, 3, 5):
        alpha = ((d - 1 - 1) / 2.0)
        z_expected = math.pi ** (d / 2.0) / math.gamma(d / 2.0)
        ratios = []
        for T, rho in ((0.0, 0.0), (0.5, 0.75), (2.0, 1.5), (7.0, 0.25), (0.3, 3.0)):
            j = orthant_1d(alpha, T, rho)
            ratios.append(lhs_k1(d, T, rho) / j)
        spread = max(ratios) - min(ratios)
        check_true(
            f"k=1 d={d}: Z is constant across five (T, rho)",
            spread / abs(ratios[0]) < 1e-9,
            f"relative spread {spread / abs(ratios[0]):.3g}",
        )
        check(f"k=1 d={d}: Z = pi^(d/2)/Gamma(d/2)", ratios[0], z_expected, 1e-9)

    # The exponent is the point: N-subtraction would give alpha = 0 at d = 1.
    d = 1
    alpha_real = (d - 1 - 1) / 2.0
    check(f"k=1 d=1: the exponent is -1/2, not 0", alpha_real, -0.5, 0.0)
    j_real = orthant_1d(alpha_real, 0.0, 0.0)
    j_trunc = orthant_1d(0.0, 0.0, 0.0)
    check(f"k=1 d=1: J(0) with the real exponent is Gamma(1/2)", j_real,
          math.gamma(0.5), 1e-6)
    check_true(
        "k=1 d=1: the N-truncated exponent gives a different J(0)",
        abs(j_real - j_trunc) > 0.5,
        f"Gamma(1/2)={j_real:.6f} vs truncated {j_trunc:.6f}",
    )


# --------------------------------------------------------------------------
# k = 2: Monte-Carlo. e^{-|X|_F^2} is sqrt(pi)^(kd) times the density of a
# Gaussian with variance 1/2 per entry, so
#
#   LHS = pi^(kd/2) * E[ det(1 + T X X^T)^{-rho} ],   X_ij ~ N(0, 1/2).
# --------------------------------------------------------------------------

def det2(m: list[list[float]]) -> float:
    return m[0][0] * m[1][1] - m[0][1] * m[1][0]


def lhs_k2_mc(d: int, T: float, rho: float, draws: int, rng: random.Random) -> float:
    sigma = math.sqrt(0.5)
    acc = 0.0
    for _ in range(draws):
        X = [[rng.gauss(0.0, sigma) for _ in range(d)] for _ in range(2)]
        g11 = sum(X[0][j] * X[0][j] for j in range(d))
        g12 = sum(X[0][j] * X[1][j] for j in range(d))
        g22 = sum(X[1][j] * X[1][j] for j in range(d))
        acc += det2([[1.0 + T * g11, T * g12], [T * g12, 1.0 + T * g22]]) ** (-rho)
    return math.pi ** (2 * d / 2.0) * acc / draws


def probe_k2() -> None:
    print("\n-- k = 2: Monte-Carlo; the smallest shape with a real Vandermonde --")
    draws = 400_000
    params = ((0.0, 0.0), (0.5, 1.0), (2.0, 0.5))
    for d in (2, 3):
        alpha = (d - 2 - 1) / 2.0
        rng = random.Random(20260904 + d)
        ratios, ratios_novdm = [], []
        for T, rho in params:
            lhs = lhs_k2_mc(d, T, rho, draws, rng)
            ratios.append(lhs / orthant_2d(alpha, T, rho, vandermonde=True))
            ratios_novdm.append(lhs / orthant_2d(alpha, T, rho, vandermonde=False))
        spread = (max(ratios) - min(ratios)) / abs(ratios[0])
        check_true(
            f"k=2 d={d}: Z is constant across three (T, rho), with the Vandermonde",
            spread < 0.02, f"relative spread {spread:.4g}")
        spread_nv = (max(ratios_novdm) - min(ratios_novdm)) / abs(ratios_novdm[0])
        check_true(
            f"k=2 d={d}: dropping the Vandermonde breaks constancy -- the test has power",
            spread_nv > 3 * max(spread, 1e-3),
            f"spread without it {spread_nv:.4g} vs {spread:.4g} with it")


def main() -> int:
    print((__doc__ or "").split("\n\n")[0])
    print("\nThis is a falsification attempt, not a proof, and not an inhabitant of")
    print("EigenvalueLawStatement. Passing does not make the frontier true.")
    probe_k1()
    probe_k2()
    print("\nScope limits: k in {1, 2} and d <= 5 only; the k = 2 arm is statistical,")
    print("so it rejects gross shape errors and not small ones. Nothing here touches")
    print("k > 2, and nothing here bears on O70-EXACT-LOCAL.")
    if FAILURES:
        print(f"\nFAIL: {len(FAILURES)} check(s) failed: {', '.join(FAILURES)}")
        return 1
    print("\nPASS: every check above succeeded.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
