#!/usr/bin/env python3
"""Independent re-derivation of the atlas's arithmetic claims about MAIS-O70.

This is V7 stress evidence for CONJ-026 and it lives in `scripts/` so that it is
part of the repository a reader clones. Lean docstrings in
`AISafetyAtlas/Conjectures/MAIS/O70.lean` cite it by this path.

Nothing here is taken from the candidate's own scripts, which are not public
(see 01-statement-and-fidelity.md section 7).  Everything is recomputed from
the *printed* formulas: Theorem 1.1/1.2 and Corollary 1.3 of the candidate,
and Theorem `thm:aw` of `agendas/A6/MAIS-A6.tex`.

Run:  python3 scripts/reproduce_o70_table.py
Exit 0 iff every check passes.
"""

from fractions import Fraction as F
from itertools import product
import sys

failures = []


def check(name, got, want):
    if got != want:
        failures.append(f"{name}: got {got!r}, want {want!r}")


# --- Theorem 1.2: the residual table, five branches -------------------------
def residual_pair_branches(p, n, h):
    """(lambda_0, m_0) from the five-branch case list of Theorem 1.2."""
    if p == 0 or n == 0 or h == 0:
        return F(0), 1
    if p <= n + h and n <= p + h and h <= p + n:          # balanced
        lam = F(2 * h * (p + n) - (p - n) ** 2 - h ** 2, 8)
        if (p + n + h) % 2 == 0:
            return lam, 1
        return lam + F(1, 8), 2
    if n + h < p:
        return F(h * n, 2), 1
    if p + h < n:
        return F(h * p, 2), 1
    if p + n < h:
        return F(p * n, 2), 1
    raise AssertionError(f"branches are not exhaustive at {(p, n, h)}")


# --- Corollary 1.3: the unified discrete-minimisation form ------------------
def residual_pair_minform(p, n, h):
    """(lambda_0, m_0) from min_t [ hn + t(p-h-n) + t^2 ] / 2."""
    ts = range(0, min(h, n) + 1)
    cs = [h * n + t * (p - h - n) + t * t for t in ts]
    best = min(cs)
    return F(best, 2), cs.count(best)


# --- Theorem 1.1 ------------------------------------------------------------
def local_pair(M, N, H, r, a, b):
    q = M * a + b * N - a * b
    p, n, h = M - b, N - a, H - a - b + r
    lam0, m0 = residual_pair_branches(p, n, h)
    return F(q, 2) + lam0, m0, q, (p, n, h)


def feasible(M, N, H, r, a, b):
    """Arithmetic rank feasibility only.

    Deliberately does NOT require 0 < M, N, H: checks [7] and [8] rely on
    that, [8] precisely to exhibit the degenerate strata an unguarded
    predicate would admit (review 16, H1).  If the Lean feasibility layer
    takes the positivity guard, this function is its arithmetic core, not
    its mirror.
    """
    return (r <= min(a, b) and a <= min(H, N) and b <= min(H, M)
            and a + b - r <= H)


# --- Theorem thm:aw (MAIS-A6.tex lines 184-205), transcribed ----------------
def aoyagi_watanabe(M, N, H, r):
    if M + r <= N + H and N + r <= M + H and H + r <= M + N:
        base = 2 * (H + r) * (M + N) - (M - N) ** 2 - (H + r) ** 2
        if (M + N + H + r) % 2 == 0:
            return F(base, 8), 1
        return F(base + 1, 8), 2
    if N + H < M + r:
        return F(H * N - H * r + M * r, 2), 1
    if M + H < N + r:
        return F(H * M - H * r + N * r, 2), 1
    if M + N < H + r:
        return F(M * N, 2), 1
    raise AssertionError(f"AW cases not exhaustive at {(M, N, H, r)}")


# ===========================================================================
# CHECK 1.  Theorem 1.2 (branches) == Corollary 1.3 (min form), 0<=p,n,h<=40.
# ===========================================================================
RANGE = 41
for p, n, h in product(range(RANGE), repeat=3):
    check(f"branches-vs-minform({p},{n},{h})",
          residual_pair_branches(p, n, h), residual_pair_minform(p, n, h))
print(f"[1] branch table == min form on {RANGE**3} triples "
      f"0 <= p,n,h <= {RANGE-1}")

# ===========================================================================
# CHECK 2.  Transpose symmetry: (p,n,h) and (n,p,h) give the same pair.
# ===========================================================================
for p, n, h in product(range(RANGE), repeat=3):
    check(f"transpose({p},{n},{h})",
          residual_pair_branches(p, n, h), residual_pair_branches(n, p, h))
print("[2] transpose symmetry (p<->n) holds on the same range")

# ===========================================================================
# CHECK 3.  min over feasible strata == the published Aoyagi-Watanabe pair,
#           with m the LARGEST multiplicity among threshold-minimisers.
#           (A6 thm:aw: "lambda is the minimum of lambda(w) over w in W_0,
#            and m is the largest m(w) among the minimizers".)
# ===========================================================================
tuples = 0
for M, N, H in product(range(1, 7), repeat=3):
    for r in range(0, min(M, N, H) + 1):
        strata = [(a, b) for a in range(H + 1) for b in range(H + 1)
                  if feasible(M, N, H, r, a, b)]
        if not strata:
            continue
        pairs = [local_pair(M, N, H, r, a, b)[:2] for (a, b) in strata]
        lam_min = min(l for (l, _) in pairs)
        m_max = max(m for (l, m) in pairs if l == lam_min)
        check(f"global({M},{N},{H},{r})", (lam_min, m_max),
              aoyagi_watanabe(M, N, H, r))
        tuples += 1
print(f"[3] min over strata == Aoyagi-Watanabe on {tuples} tuples, M,N,H <= 6")

# ===========================================================================
# CHECK 4.  Section 12's table for N = M = H = 2, transcribed from the paper.
# ===========================================================================
SEC12 = [
    # r, (a,b), q, (p,n,h), lam0, m0, (lam,m), is_minimiser
    (0, (0, 0), 0, (2, 2, 2), F(3, 2), 1, (F(3, 2), 1), True),
    (0, (0, 1), 2, (1, 2, 1), F(1, 2), 1, (F(3, 2), 1), True),
    (0, (1, 0), 2, (2, 1, 1), F(1, 2), 1, (F(3, 2), 1), True),
    (0, (1, 1), 3, (1, 1, 0), F(0),    1, (F(3, 2), 1), True),
    (0, (0, 2), 4, (0, 2, 0), F(0),    1, (F(2),    1), False),
    (0, (2, 0), 4, (2, 0, 0), F(0),    1, (F(2),    1), False),
    (1, (1, 1), 3, (1, 1, 1), F(1, 2), 2, (F(2),    2), True),
    (1, (1, 2), 4, (0, 1, 0), F(0),    1, (F(2),    1), True),
    (1, (2, 1), 4, (1, 0, 0), F(0),    1, (F(2),    1), True),
    (2, (2, 2), 4, (0, 0, 0), F(0),    1, (F(2),    1), True),
]
M = N = H = 2
for r, (a, b), q_want, pnh_want, lam0_want, m0_want, pair_want, _ in SEC12:
    assert feasible(M, N, H, r, a, b), (r, a, b)
    lam, m, q, pnh = local_pair(M, N, H, r, a, b)
    check(f"sec12 q r={r} (a,b)=({a},{b})", q, q_want)
    check(f"sec12 (p,n,h) r={r} (a,b)=({a},{b})", pnh, pnh_want)
    check(f"sec12 lam0 r={r} (a,b)=({a},{b})",
          residual_pair_branches(*pnh), (lam0_want, m0_want))
    check(f"sec12 pair r={r} (a,b)=({a},{b})", (lam, m), pair_want)

# every feasible stratum of the 2x2x2 case is listed, and no others
for r in range(0, 3):
    listed = {(a, b) for (rr, (a, b), *_) in SEC12 if rr == r}
    actual = {(a, b) for a in range(3) for b in range(3)
              if feasible(M, N, H, r, a, b)}
    check(f"sec12 strata complete r={r}", listed, actual)
print(f"[4] Section 12 table for N=M=H=2 reproduced, all {len(SEC12)} rows "
      "and the feasible-stratum lists")

# ===========================================================================
# CHECK 5.  The problem page's anchor (MAIS-A6.tex, prob:calibration):
#           N=M=H=2, r=0, at (I_2, 0) the local coefficient is 2,
#           while "the table" (Aoyagi-Watanabe) gives 3/2.
#           (I_2, 0) has rank A = 2, rank B = 0.
# ===========================================================================
lam_anchor, m_anchor, _, _ = local_pair(2, 2, 2, 0, a=2, b=0)
check("anchor local", (lam_anchor, m_anchor), (F(2), 1))
check("anchor global", aoyagi_watanabe(2, 2, 2, 0), (F(3, 2), 1))
print("[5] anchor: local pair at (I_2,0) is (2,1); global is (3/2,1) -- "
      "print's example reproduced")

# ===========================================================================
# CHECK 6.  The support gap in MAIS-A6.tex rem:conventions.
#           Claim (01-statement-and-fidelity.md section 5): there is a truth
#           for which some stratum attains the AW *threshold* but not the AW
#           *multiplicity*, so "W contains a neighborhood of a factorization
#           attaining the Aoyagi-Watanabe minimum" does not pin (lambda, m).
# ===========================================================================
witnesses = []
for M, N, H in product(range(1, 7), repeat=3):
    for r in range(0, min(M, N, H) + 1):
        lam_gl, m_gl = aoyagi_watanabe(M, N, H, r)
        if m_gl == 1:
            continue                       # nothing to lose
        for a in range(H + 1):
            for b in range(H + 1):
                if not feasible(M, N, H, r, a, b):
                    continue
                lam, m, _, _ = local_pair(M, N, H, r, a, b)
                if lam == lam_gl and m < m_gl:
                    witnesses.append((M, N, H, r, a, b, lam, m, m_gl))
if not witnesses:
    failures.append("support gap: no witness found, the section 5 claim is wrong")
else:
    small = min(witnesses, key=lambda w: (w[0] + w[1] + w[2] + w[3]))
    print(f"[6] support gap in rem:conventions: {len(witnesses)} witnesses with "
          f"M,N,H <= 6; smallest is")
    print(f"    (M,N,H,r)=({small[0]},{small[1]},{small[2]},{small[3]}) "
          f"stratum (a,b)=({small[4]},{small[5]}): "
          f"local ({small[6]},{small[7]}) vs global multiplicity {small[8]}")
    # the one quoted in the review
    check("support gap quoted witness present",
          (2, 2, 2, 1, 1, 2) in [w[:6] for w in witnesses], True)

# --- [7] the V6 source bounds, the m<=2 bound, and the arithmetic minimum ---
# Evidence for review 14 (G2, G3).  All three are statements plan 11 needs:
#   V6      0 < lambda <= dim(W)/2 = H*(N+M)/2, and m <= 2 (not m <= H*(N+M))
#   G2      awLambda == min over feasible strata of the local lambda
# The last is the bridge that makes P3's "minimum" a minimum rather than an
# equality with a number; it extends check [3] from M,N,H <= 6 to <= 8.
LIM7 = 8
n_strata = n_tuples = 0
bad_pos = bad_up = bad_m = bad_min = 0
for M in range(1, LIM7 + 1):
    for N in range(1, LIM7 + 1):
        for H in range(1, LIM7 + 1):
            dim_W = F(H * (N + M))
            for r in range(0, min(M, N, H) + 1):
                lams = []
                for a in range(0, min(H, N) + 1):
                    for b in range(0, min(H, M) + 1):
                        if not feasible(M, N, H, r, a, b):
                            continue
                        n_strata += 1
                        lam, m, _, _ = local_pair(M, N, H, r, a, b)
                        if not lam > 0:
                            bad_pos += 1
                        if not lam <= dim_W / 2:
                            bad_up += 1
                        if m > 2:
                            bad_m += 1
                        lams.append(lam)
                if lams:
                    n_tuples += 1
                    if min(lams) != aoyagi_watanabe(M, N, H, r)[0]:
                        bad_min += 1
check("[7a] 0 < lambda on every feasible stratum", bad_pos, 0)
check("[7b] lambda <= H*(N+M)/2 on every feasible stratum", bad_up, 0)
check("[7c] m <= 2 on every feasible stratum", bad_m, 0)
check("[7d] awLambda == min over feasible strata", bad_min, 0)
print(f"[7] V6 bounds and the arithmetic minimum hold on {n_strata} feasible "
      f"strata")
print(f"    over {n_tuples} (M,N,H,r) tuples with 1 <= M,N,H <= {LIM7}")


# --- [8] the unguarded P3 stratum predicate admits degenerate dimensions -----
# Evidence for review 16.  `IsO70FiberMinimumTable` carries 0 < M, N, H;
# `IsO70AWValueStratumTable` does not.  Every feasible stratum with a zero
# ambient dimension satisfies lambda == awLambda, so an unguarded predicate
# forces all of them into `o70Minimizers` -- contradicting the plan's own scope
# row, which grades dimensions as positive.
LIM8 = 5
deg_equal = deg_unequal = 0
for M in range(0, LIM8 + 1):
    for N in range(0, LIM8 + 1):
        for H in range(0, LIM8 + 1):
            if M > 0 and N > 0 and H > 0:
                continue
            for r in range(0, min(M, N, H) + 1):
                for a in range(0, min(H, N) + 1):
                    for b in range(0, min(H, M) + 1):
                        if not feasible(M, N, H, r, a, b):
                            continue
                        lam, _, _, _ = local_pair(M, N, H, r, a, b)
                        if lam == aoyagi_watanabe(M, N, H, r)[0]:
                            deg_equal += 1
                        else:
                            deg_unequal += 1
check("[8] every degenerate-dimension feasible stratum attains awLambda",
      deg_unequal, 0)
print(f"[8] {deg_equal} feasible strata with a zero ambient dimension all satisfy")
print(f"    lambda == awLambda, so an unguarded stratum predicate admits them all")


# ===========================================================================
print()
if failures:
    print(f"FAIL: {len(failures)} check(s) failed")
    for f_ in failures[:20]:
        print("  -", f_)
    sys.exit(1)
print("PASS: every check above succeeded.")
