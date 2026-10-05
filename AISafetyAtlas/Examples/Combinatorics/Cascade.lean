module

public import AISafetyAtlas.Combinatorics.Cascade

/-!
# Worked example: the cascade, evaluated

Small cases where the answer is known by hand, and then the corpus numbers the
benchmark analysis reports, so that the Lean definition and
`benchmark-facet-atlas/analysis/kk_envelope.py` are checked against each other
at the values the analysis actually reports. This is pointwise agreement in the
kernel, at those counts; the two are not proved equal as functions, and a
divergence away from the reported values would not be caught here.

Three edges on three cards admit one triangle and touch three vertices; five
edges admit two triangles and need four vertices. Both are checked below, and
both are cases where the multicomplex bound is wrong for simplicial complexes —
Macaulay's shift permits four triangles on three edges.

These are compiling documentation examples, not public theorems.
-/

namespace AISafetyAtlas.Examples.Combinatorics.Cascade

open AISafetyAtlas.Combinatorics

/-! ## Small cases, by hand -/

/-- Three edges admit exactly one triangle. -/
example : cascadeUpper 2 3 = 1 := by decide

/-- And touch exactly three vertices. -/
example : cascadeShadow 2 3 = 3 := by decide

/-- Five edges admit two triangles — `K₄` minus an edge. -/
example : cascadeUpper 2 5 = 2 := by decide

/-- And need four vertices. -/
example : cascadeShadow 2 5 = 4 := by decide

/-! ## The greedy digit -/

/-- `C(3,2) = 3` fits inside `5` and `C(4,2) = 6` does not. -/
example : cascadeTop 2 5 = 3 :=
  AISafetyAtlas.Combinatorics.cascadeTop_eq (r := 1) (by decide) (by decide)

/-- The digit fits. -/
example : (cascadeTop 2 5).choose 2 ≤ 5 :=
  AISafetyAtlas.Combinatorics.cascadeTop_choose_le 1 5

/-- The next one does not. -/
example : 5 < (cascadeTop 2 5 + 1).choose 2 :=
  AISafetyAtlas.Combinatorics.lt_succ_cascadeTop_choose 1 5

/-- Fitting inside is the same as being at or below the digit. -/
example {k : ℕ} : k.choose 2 ≤ 5 ↔ k ≤ cascadeTop 2 5 :=
  AISafetyAtlas.Combinatorics.choose_le_iff_le_cascadeTop 1 5 k

/-- Nothing past `a + r` can be a digit. -/
example {k : ℕ} (h : k.choose 2 ≤ 5) : k ≤ 5 + 2 :=
  AISafetyAtlas.Combinatorics.le_bound_of_choose_le (r := 1) h

/-- The growth fact the bound rests on. -/
example (j : ℕ) : j + 1 ≤ (j + 2).choose 2 :=
  AISafetyAtlas.Combinatorics.succ_le_choose_add 1 j

/-- The digit is monotone. -/
example : cascadeTop 2 3 ≤ cascadeTop 2 5 :=
  AISafetyAtlas.Combinatorics.cascadeTop_mono 1 (by decide)

/-- The remainder falls under the next binomial down. -/
example : 5 - (cascadeTop 2 5).choose 2 ≤ (cascadeTop 2 5).choose 1 :=
  AISafetyAtlas.Combinatorics.sub_cascadeTop_choose_le 1 5

/-- And the digit cannot exceed a `K` whose binomial already contains the count. -/
example : cascadeTop 2 5 ≤ 4 :=
  AISafetyAtlas.Combinatorics.cascadeTop_le_of_le_choose (K := 4) (by decide) (by decide)

/-! ## The shifts, on their own terms -/

/-- Nothing below nothing. -/
example : cascadeShadow 3 0 = 0 :=
  AISafetyAtlas.Combinatorics.cascadeShadow_zero_right 3

/-- Nothing above nothing. -/
example : cascadeUpper 3 0 = 0 :=
  AISafetyAtlas.Combinatorics.cascadeUpper_zero_right 3

/-- A complete level permits the complete level above it. -/
example : cascadeUpper 2 (Nat.choose 4 2) = Nat.choose 4 3 :=
  AISafetyAtlas.Combinatorics.cascadeUpper_choose 1 4 (by decide)

/-- And touches the complete level below it. -/
example : cascadeShadow 2 (Nat.choose 4 2) = Nat.choose 4 1 :=
  AISafetyAtlas.Combinatorics.cascadeShadow_choose 1 4 (by decide)

/-- **The cap.** Five pairs sit inside four cards, so at most `C(4,3) = 4`
triples are available. -/
example : cascadeUpper 2 5 ≤ Nat.choose 4 3 :=
  AISafetyAtlas.Combinatorics.cascadeUpper_le_choose 2 4 5 (by decide)

/-- **The cap is monotone.** -/
example : cascadeUpper 2 3 ≤ cascadeUpper 2 5 :=
  AISafetyAtlas.Combinatorics.cascadeUpper_mono 2 (by decide)

/-! ### A grid, not a handful

Every pair below was produced by running
`benchmark-facet-atlas/analysis/kk_envelope.py`'s own cap and shadow
functions and printing the answer, so each line is the kernel
checking the Lean definition against the Python one at that point. The grid
sweeps the levels the analysis uses and, at each, the boundary cases a
greedy digit can get wrong: zero, one, an exact binomial coefficient and the
values either side of it. It is still pointwise agreement rather than a proof
that the two functions are equal.
-/

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 0 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 0 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 1 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 1 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 2 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 2 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 3 = 3 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 3 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 4 = 6 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 4 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 5 = 10 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 5 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 7 = 21 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 7 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 8 = 28 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 8 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 17 = 136 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 17 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 100 = 4950 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 100 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 257 = 32896 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 257 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 1 611 = 186355 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 1 611 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 0 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 0 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 1 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 1 = 2 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 2 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 2 = 3 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 3 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 3 = 3 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 5 = 2 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 5 = 4 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 9 = 7 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 9 = 5 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 10 = 10 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 10 = 5 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 11 = 10 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 11 = 6 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 17 = 21 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 17 = 7 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 28 = 56 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 28 = 8 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 29 = 56 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 29 = 9 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 100 = 400 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 100 = 15 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 257 = 1777 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 257 = 24 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 2 611 = 6665 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 2 611 = 36 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 0 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 0 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 1 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 1 = 3 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 2 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 2 = 5 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 3 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 3 = 6 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 5 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 5 = 8 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 17 = 9 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 17 = 15 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 19 = 12 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 19 = 15 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 20 = 15 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 20 = 15 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 21 = 15 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 21 = 17 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 84 = 126 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 84 = 36 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 85 = 126 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 85 = 38 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 100 = 146 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 100 = 43 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 257 = 579 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 257 = 76 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 3 611 = 1955 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 3 611 = 131 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 0 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 0 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 1 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 1 = 4 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 2 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 2 = 7 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 3 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 3 = 9 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 4 = 0 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 4 = 10 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 5 = 1 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 5 = 10 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 17 = 6 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 17 = 25 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 34 = 18 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 34 = 35 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 35 = 21 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 35 = 35 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 36 = 21 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 36 = 38 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 100 = 81 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 100 = 76 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 210 = 252 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 210 = 120 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 211 = 252 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 211 = 123 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 257 = 298 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 257 = 147 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeUpper 4 611 = 980 := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
example : cascadeShadow 4 611 = 265 := by decide

/-! ## The corpus numbers

Every cascade value the four reported configurations of
`benchmark-facet-atlas/analysis/kk_envelope.py` print -- the cap, the cap
propagated from order one, and the floor, at orders two through four, on the
unanimous and union merges over the root and leaf cuts. Thirty-two values, each
checked in the kernel.

These are not `decide` evaluations of the operator. `cascadeTop` is a
`Nat.findGreatest`, which the kernel evaluates by scanning, so deciding
`cascadeShadow 4 883916` overflows the stack. Each proof instead supplies the
greedy digit at every level and discharges the two binomial inequalities that
pin it, through `cascadeUpper_step` and `cascadeShadow_step`. The digits come
from the analysis, so if the Python and the Lean disagreed at any level the
inequality would fail and this file would not compile.

That is still agreement at the values reported rather than a proof that the two
implementations are the same function. What it buys is that no number the paper
prints is unchecked.

Regenerate with the analysis itself, which emits exactly this block:

```text
for a in m100_unanimous m100_union; do for c in roots leaves; do
  python3 analysis/kk_envelope.py --bkg <v6>.jsonc --assign $a.json \
      --cut $c --kmax 4 --emit-lean emit_${a}_${c}.lean
done; done
```
-/

set_option maxRecDepth 4000000 in
example : cascadeUpper 1 89 = 3916 := by
  rw [cascadeUpper_step (k := 89) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 1 135 = 9045 := by
  rw [cascadeUpper_step (k := 135) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 1 141 = 9870 := by
  rw [cascadeUpper_step (k := 141) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 1 223 = 24753 := by
  rw [cascadeUpper_step (k := 223) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 2 1587 = 28801 := by
  rw [cascadeUpper_step (k := 56) (by decide) (by decide),
      cascadeUpper_step (k := 47) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 2 2170 = 46060 := by
  rw [cascadeUpper_step (k := 66) (by decide) (by decide),
      cascadeUpper_step (k := 25) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 2 3449 = 92916 := by
  rw [cascadeUpper_step (k := 83) (by decide) (by decide),
      cascadeUpper_step (k := 46) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 2 3916 = 113564 := by
  rw [cascadeUpper_step (k := 89) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 2 6504 = 242417 := by
  rw [cascadeUpper_step (k := 114) (by decide) (by decide),
      cascadeUpper_step (k := 63) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 2 9045 = 400995 := by
  rw [cascadeUpper_step (k := 135) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 2 9870 = 457310 := by
  rw [cascadeUpper_step (k := 141) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 2 24753 = 1823471 := by
  rw [cascadeUpper_step (k := 223) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 3 15284 = 163627 := by
  rw [cascadeUpper_step (k := 46) (by decide) (by decide),
      cascadeUpper_step (k := 14) (by decide) (by decide),
      cascadeUpper_step (k := 13) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 3 16721 = 183370 := by
  rw [cascadeUpper_step (k := 47) (by decide) (by decide),
      cascadeUpper_step (k := 32) (by decide) (by decide),
      cascadeUpper_step (k := 10) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 3 46220 = 725080 := by
  rw [cascadeUpper_step (k := 66) (by decide) (by decide),
      cascadeUpper_step (k := 30) (by decide) (by decide),
      cascadeUpper_step (k := 25) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 3 90703 = 1794693 := by
  rw [cascadeUpper_step (k := 82) (by decide) (by decide),
      cascadeUpper_step (k := 65) (by decide) (by decide),
      cascadeUpper_step (k := 63) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 3 113564 = 2441626 := by
  rw [cascadeUpper_step (k := 89) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 3 400995 = 13232835 := by
  rw [cascadeUpper_step (k := 135) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 3 457310 = 15777195 := by
  rw [cascadeUpper_step (k := 141) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeUpper 3 1823471 = 100290905 := by
  rw [cascadeUpper_step (k := 223) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 2 1587 = 57 := by
  rw [cascadeShadow_step (k := 56) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 47) (by decide) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 2 2170 = 67 := by
  rw [cascadeShadow_step (k := 66) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 25) (by decide) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 2 3449 = 84 := by
  rw [cascadeShadow_step (k := 83) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 46) (by decide) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 2 6504 = 115 := by
  rw [cascadeShadow_step (k := 114) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 63) (by decide) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 3 15284 = 1050 := by
  rw [cascadeShadow_step (k := 46) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 14) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 13) (by decide) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 3 16721 = 1114 := by
  rw [cascadeShadow_step (k := 47) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 32) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 10) (by decide) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 3 46220 = 2176 := by
  rw [cascadeShadow_step (k := 66) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 30) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 25) (by decide) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 3 90703 = 3387 := by
  rw [cascadeShadow_step (k := 82) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 65) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 63) (by decide) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 4 91911 = 9997 := by
  rw [cascadeShadow_step (k := 40) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 15) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 12) (by decide) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 4 99918 = 10598 := by
  rw [cascadeShadow_step (k := 40) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 38) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 14) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 1) (by decide) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 4 419036 = 30674 := by
  rw [cascadeShadow_step (k := 57) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 53) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 35) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 5) (by decide) (by decide) (by decide)]
  decide
set_option maxRecDepth 4000000 in
example : cascadeShadow 4 883916 = 53616 := by
  rw [cascadeShadow_step (k := 69) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 49) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 45) (by decide) (by decide) (by decide),
      cascadeShadow_step (k := 1) (by decide) (by decide) (by decide)]
  decide

/-! ## The two shifts are adjoint

The shadow bound and the cap are two readings of one theorem, and
`AISafetyAtlas.Combinatorics.cascadeShadow_le_iff_le_cascadeUpper` is what makes
them the same reading. Everything below order two is excluded, because a level of
singletons sits above the one empty set whatever its size.
-/

/-- **The shadow, against a binomial.** Five pairs sit inside `C(4,2) = 6`, so
they touch at most `C(4,1) = 4` cards. -/
example : cascadeShadow 2 5 ≤ Nat.choose 4 1 :=
  AISafetyAtlas.Combinatorics.cascadeShadow_le_choose 1 4 5 (by decide)

/-- **The greedy digit is at least the level.** -/
example : 1 + 1 ≤ cascadeTop (1 + 1) 5 :=
  AISafetyAtlas.Combinatorics.le_cascadeTop_of_pos (by decide)

/-- **The cap, strictly.** Three pairs sit strictly inside `C(4,2) = 6`, so they
permit strictly fewer than `C(4,3) = 4` triples. -/
example : cascadeUpper 2 3 < Nat.choose 4 3 :=
  AISafetyAtlas.Combinatorics.cascadeUpper_lt_choose 2 4 3 (by decide) (by decide)

/-- **The shadow is monotone.** -/
example : cascadeShadow 2 3 ≤ cascadeShadow 2 5 :=
  AISafetyAtlas.Combinatorics.cascadeShadow_mono 2 (by decide)

/-- **At level one the greedy digit is the number.** -/
example : cascadeTop 1 7 = 7 :=
  AISafetyAtlas.Combinatorics.cascadeTop_one 7

/-- **And the cap is a single binomial coefficient.** Seven cards permit
`C(7,2) = 21` pairs. -/
example : cascadeUpper 1 7 = Nat.choose 7 2 :=
  AISafetyAtlas.Combinatorics.cascadeUpper_one 7

/-- **Counit.** Capping five pairs and taking the shadow back does not overshoot
the five. -/
example : cascadeShadow (2 + 1) (cascadeUpper 2 5) ≤ 5 :=
  AISafetyAtlas.Combinatorics.cascadeShadow_cascadeUpper_le 2 5

/-- **Unit.** Four pairs, shadowed to their cards and capped again, are not
lost. -/
example : 4 ≤ cascadeUpper (0 + 1) (cascadeShadow (0 + 2) 4) :=
  AISafetyAtlas.Combinatorics.le_cascadeUpper_cascadeShadow 0 4

/-- **The adjunction itself**, at the orders the corpus is measured on: four
pairs fit above four cards exactly when four cards permit four pairs. -/
example : cascadeShadow (0 + 2) 4 ≤ 4 ↔ 4 ≤ cascadeUpper (0 + 1) 4 :=
  AISafetyAtlas.Combinatorics.cascadeShadow_le_iff_le_cascadeUpper 0 4 4

/-- **As a `GaloisConnection`.** -/
example : GaloisConnection (cascadeShadow (0 + 2)) (cascadeUpper (0 + 1)) :=
  AISafetyAtlas.Combinatorics.galoisConnection_cascadeShadow_cascadeUpper 0

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- **The corpus cap, read through the adjunction.** The unanimous merge reports
28801 triples permitted by 1587 pairs; that ceiling is the shadow bound in the
other direction, and this is the step that was missing when the script's cap
column was first written. -/
example : 28801 ≤ cascadeUpper (1 + 1) 1587 :=
  (AISafetyAtlas.Combinatorics.cascadeShadow_le_iff_le_cascadeUpper 1 1587 28801).1
    (by decide)

end AISafetyAtlas.Examples.Combinatorics.Cascade
