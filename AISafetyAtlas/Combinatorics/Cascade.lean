/-
The `cascadeTop` layer below — the greedy step of the cascade representation and
its characterisation — is adapted from `anthropics/fermats-last-theorem`
(https://github.com/anthropics/fermats-last-theorem) at commit
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`, licensed Apache-2.0 with no upstream
`NOTICE`. Two files are involved:

* `Definitions/Def_Nat_MacaulayPow.lean`, SHA-256
  `54f12d5895ae2e3fde1a41b8ce7e0e37fa02ea2cf679e9841e6ff05a492dabb2`
* `P2M/Sol/S_Nat_macaulayPow_lt_macaulayPow_of_lt.lean`, SHA-256
  `bd2134a0f07974b6638fb2435e9a8073f642f251167a819950abfc9244dfa25e`

Atlas changes. Upstream indexes the greedy step by `d` and searches on
`choose (d + 1)`; here it is indexed by the set size `r` and searches on
`choose r`, so every upstream statement appears with `r` in place of `d + 1`.
Upstream defines one shift operator, `Nat.macaulayPow`, which raises **both**
indices of each cascade term and is the bound for multicomplexes; this file
defines the two Kruskal-Katona shifts, which move only the lower index, and they
are strictly smaller — for three edges upstream's operator permits four triangles
where two is the truth. `cascadeShadow` carries a zero guard upstream does not
need, because the downward shift of a spent term contributes `Nat.choose 0 0 = 1`
rather than `0`. Namespace `P2MW.S_Nat_macaulayPow_lt_macaulayPow_of_lt.MacMono`
-> `AISafetyAtlas.Combinatorics`; `set_option autoImplicit false` is the atlas
default and is dropped; per-declaration `public` and `@[expose]` are added,
because a section-scoped declaration is invisible to `scripts/check_public_api.py`
and `scripts/check_print_axioms.py`. Lean v4.33.1 -> v4.33.0, which costs
nothing. The arithmetic of the greedy step is the upstream authors'.
Repository-level notice: `AISafetyAtlas/Upstream/LICENSE-NOTICE`.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.GaloisConnection.Defs

/-!
# The cascade representation of a natural number

Every natural number has exactly one representation

```text
m = C(a_r, r) + C(a_{r-1}, r-1) + ... + C(a_s, s),   a_r > a_{r-1} > ... > a_s ≥ s ≥ 1
```

a positional number system whose digits are binomial coefficients rather than
powers. It is read off greedily: take the largest `a_r` whose `C(a_r, r)` still
fits, subtract, drop to `r - 1`, repeat. `cascadeTop` is that greedy choice and
`cascadeTop_eq` is what makes it well defined.

The representation is not interesting on its own. What is interesting is that
several different theorems are the *same shift applied to it*:

| move each term `C(a, j)` to | and you have | about |
|---|---|---|
| `C(a, j - 1)` | Kruskal-Katona, shadow direction | simplicial complexes |
| `C(a, j + 1)` | Kruskal-Katona, upper direction | simplicial complexes |
| `C(a + 1, j + 1)` | Macaulay | Hilbert functions of graded algebras |

This file carries the representation and the first two shifts, `cascadeShadow`
and `cascadeUpper`. The third is upstream's `Nat.macaulayPow`, named in the
attribution above; it is a *weaker* bound here, since a simplicial complex is a
multicomplex but not conversely, and the gap is not small — three edges admit one
triangle and Macaulay's shift permits four.

The two shifts are not independent. They are a Galois connection,
`cascadeShadow_le_iff_le_cascadeUpper`, so the shadow bound and the cap are one
theorem read two ways rather than two results. It relates size `r + 1` to size
`r + 2` for every `r`, so the single pair it does not cover is size zero against
size one: a level of singletons sits above the one empty set whatever its size,
and nothing caps it from below.

**What this file does not do.** It carries the arithmetic and no theorem about
set families. `AISafetyAtlas.Combinatorics.CascadeFamily` supplies the counting
that connects the two — the colex rank, which is the *combinatorial number
system* — and with it proves Kruskal-Katona in this form, which Mathlib's own
file records as an open task.

Source and scope: the cascade representation is classical, from Macaulay 1927 and
Kruskal 1963 / Katona 1968. The greedy-step arithmetic is adapted rather than
rebuilt; see the attribution above. Nothing here is coverage of a printed result
in the registry's sense.
-/

namespace AISafetyAtlas.Combinatorics

/--
**The greedy digit.** The largest `k` whose `C(k, r)` still fits inside `a`.

`a + r` is a bound rather than a guess: `le_bound_of_choose_le` shows no `k` past
it can qualify, which is what lets `Nat.findGreatest` be used at all.
-/
@[expose] public def cascadeTop (r a : ℕ) : ℕ :=
  Nat.findGreatest (fun k => k.choose r ≤ a) (a + r)

/-- A binomial coefficient grows at least as fast as its own top index. -/
public theorem succ_le_choose_add (r j : ℕ) : j + 1 ≤ (j + (r + 1)).choose (r + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (j + 1 + (r + 1)).choose (r + 1)
        = (j + (r + 1)).choose r + (j + (r + 1)).choose (r + 1) := by
      rw [show j + 1 + (r + 1) = (j + (r + 1)) + 1 by omega, Nat.choose_succ_succ]
    have h2 : 1 ≤ (j + (r + 1)).choose r := Nat.choose_pos (by omega)
    omega

/-- Nothing past `a + r` can be a cascade digit at level `r`. -/
public theorem le_bound_of_choose_le {r a k : ℕ} (h : k.choose (r + 1) ≤ a) :
    k ≤ a + (r + 1) := by
  by_cases hk : k ≤ r
  · omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + (r + 1) := ⟨k - (r + 1), by omega⟩
    have := succ_le_choose_add r j
    omega

/--
**The greedy digit, characterised.** A binomial `C(k, r)` fits inside `a` exactly
when `k` is at or below the greedy choice.

This is the whole cascade API: uniqueness, monotonicity and evaluation all come
out of it.
-/
public theorem choose_le_iff_le_cascadeTop (r a k : ℕ) :
    k.choose (r + 1) ≤ a ↔ k ≤ cascadeTop (r + 1) a := by
  constructor
  · intro h
    exact Nat.le_findGreatest (le_bound_of_choose_le h) h
  · intro h
    have hspec : (cascadeTop (r + 1) a).choose (r + 1) ≤ a :=
      Nat.findGreatest_spec (P := fun k => k.choose (r + 1) ≤ a) (m := 0) (Nat.zero_le _) (by simp)
    exact (Nat.choose_le_choose (r + 1) h).trans hspec

/-- The greedy digit fits. -/
public theorem cascadeTop_choose_le (r a : ℕ) : (cascadeTop (r + 1) a).choose (r + 1) ≤ a :=
  (choose_le_iff_le_cascadeTop r a _).2 le_rfl

/-- And the next one does not. -/
public theorem lt_succ_cascadeTop_choose (r a : ℕ) : a < (cascadeTop (r + 1) a + 1).choose (r + 1) := by
  by_contra h
  have := (choose_le_iff_le_cascadeTop r a (cascadeTop (r + 1) a + 1)).1 (not_lt.1 h)
  omega

/--
**The digit is unique.** Anything squeezed between consecutive binomials is the
greedy choice, so the cascade representation is forced rather than merely
available.
-/
public theorem cascadeTop_eq {r a k : ℕ} (h₁ : k.choose (r + 1) ≤ a)
    (h₂ : a < (k + 1).choose (r + 1)) : cascadeTop (r + 1) a = k := by
  have hk : k ≤ cascadeTop (r + 1) a := (choose_le_iff_le_cascadeTop r a k).1 h₁
  rcases hk.lt_or_eq with hlt | heq
  · exact absurd ((choose_le_iff_le_cascadeTop r a (k + 1)).2 (by omega)) (not_le.2 h₂)
  · exact heq.symm

/-- The digit is monotone in the number being represented. -/
public theorem cascadeTop_mono (r : ℕ) {a b : ℕ} (h : a ≤ b) :
    cascadeTop (r + 1) a ≤ cascadeTop (r + 1) b :=
  (choose_le_iff_le_cascadeTop r b _).1 ((cascadeTop_choose_le r a).trans h)

/--
**The Kruskal-Katona shadow shift.** Move every cascade term down one level.

If a family of `a` distinct `r`-sets is downward closed, this is the least number
of `(r-1)`-sets it can touch. The zero guard is needed: a spent term would
otherwise contribute `Nat.choose 0 0 = 1`.
-/
@[expose] public def cascadeShadow : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r + 1, a =>
      if a = 0 then 0
      else (cascadeTop (r + 1) a).choose r +
        cascadeShadow r (a - (cascadeTop (r + 1) a).choose (r + 1))

/--
**The Kruskal-Katona upper shift.** Move every cascade term up one level.

If a simplicial complex has `a` faces of size `r`, this is the most faces of size
`r + 1` it can have. It needs no zero guard, because a spent term contributes
`Nat.choose r (r + 2) = 0`.
-/
@[expose] public def cascadeUpper : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r + 1, a =>
      (cascadeTop (r + 1) a).choose (r + 2) +
        cascadeUpper r (a - (cascadeTop (r + 1) a).choose (r + 1))

/-- Nothing of size `r` means nothing of size `r - 1` below it. -/
@[simp] public theorem cascadeShadow_zero_right (r : ℕ) : cascadeShadow r 0 = 0 := by
  cases r with
  | zero => rfl
  | succ r => rw [cascadeShadow, if_pos rfl]

/-- And nothing of size `r + 1` above it. -/
@[simp] public theorem cascadeUpper_zero_right (r : ℕ) : cascadeUpper r 0 = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have ht : cascadeTop (r + 1) 0 = r := cascadeTop_eq (by simp) (by simp)
    rw [cascadeUpper, ht, Nat.choose_eq_zero_of_lt (by omega : r < r + 2), Nat.zero_add,
      Nat.zero_sub, ih]

/--
**Evaluation at a single binomial.** A complete level `C(K, r + 1)` of faces
permits exactly `C(K, r + 2)` above it — the complete `(r + 2)`-skeleton on `K`
cards, which is the extremal case Kruskal-Katona identifies.
-/
public theorem cascadeUpper_choose (r K : ℕ) (hK : r + 1 ≤ K) :
    cascadeUpper (r + 1) (K.choose (r + 1)) = K.choose (r + 2) := by
  have ht : cascadeTop (r + 1) (K.choose (r + 1)) = K := by
    refine cascadeTop_eq le_rfl ?_
    rw [Nat.choose_succ_succ']
    have : 0 < K.choose r := Nat.choose_pos (by omega)
    omega
  rw [cascadeUpper, ht, Nat.sub_self, cascadeUpper_zero_right, Nat.add_zero]

/--
**Evaluation of the shadow at a single binomial.** All `C(K, r + 1)` sets of size
`r + 1` inside `K` cards touch exactly the `C(K, r)` sets of size `r`.
-/
public theorem cascadeShadow_choose (r K : ℕ) (hK : r + 1 ≤ K) :
    cascadeShadow (r + 1) (K.choose (r + 1)) = K.choose r := by
  have hpos : 0 < K.choose (r + 1) := Nat.choose_pos hK
  have ht : cascadeTop (r + 1) (K.choose (r + 1)) = K := by
    refine cascadeTop_eq le_rfl ?_
    rw [Nat.choose_succ_succ']
    have : 0 < K.choose r := Nat.choose_pos (by omega)
    omega
  rw [cascadeShadow, if_neg (by omega), ht, Nat.sub_self, cascadeShadow_zero_right,
    Nat.add_zero]

/-- The remainder after the greedy step is under the next binomial down. -/
public theorem sub_cascadeTop_choose_le (r a : ℕ) :
    a - (cascadeTop (r + 1) a).choose (r + 1) ≤ (cascadeTop (r + 1) a).choose r := by
  have h := lt_succ_cascadeTop_choose r a
  rw [Nat.choose_succ_succ'] at h
  omega

/-- The greedy digit does not exceed a `K` whose binomial already contains `a`. -/
public theorem cascadeTop_le_of_le_choose {r K m : ℕ} (hm : 0 < m) (h : m ≤ K.choose (r + 1)) :
    cascadeTop (r + 1) m ≤ K := by
  by_contra hlt
  have hKr : r + 1 ≤ K := by
    by_contra hK
    rw [Nat.choose_eq_zero_of_lt (by omega)] at h
    omega
  have h1 : (K + 1).choose (r + 1) ≤ m :=
    (choose_le_iff_le_cascadeTop r m (K + 1)).2 (by omega)
  have h2 : (K + 1).choose (r + 1) = K.choose r + K.choose (r + 1) := Nat.choose_succ_succ' _ _
  have h3 : 0 < K.choose r := Nat.choose_pos (by omega)
  omega

/--
**The cap, evaluated.** A level of size at most `C(K, r)` permits at most
`C(K, r + 1)` above it.

This is the statement a consumer wants: it turns a measured count at one order
into a ceiling at the next, with the extremal case being the complete skeleton on
`K` cards.
-/
public theorem cascadeUpper_le_choose :
    ∀ (r K m : ℕ), m ≤ K.choose r → cascadeUpper r m ≤ K.choose (r + 1) := by
  intro r
  induction r with
  | zero => intro K m _; simp [cascadeUpper]
  | succ r ih =>
    intro K m hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp
    have htK : cascadeTop (r + 1) m ≤ K := cascadeTop_le_of_le_choose hpos hm
    have hrem : m - (cascadeTop (r + 1) m).choose (r + 1) ≤ (cascadeTop (r + 1) m).choose r :=
      sub_cascadeTop_choose_le r m
    have hih := ih (cascadeTop (r + 1) m) _ hrem
    rw [cascadeUpper]
    show _ ≤ K.choose (r + 2)
    rcases htK.lt_or_eq with hlt | heq
    · have hpascal : (cascadeTop (r + 1) m + 1).choose (r + 2)
          = (cascadeTop (r + 1) m).choose (r + 1) + (cascadeTop (r + 1) m).choose (r + 2) :=
        Nat.choose_succ_succ' _ _
      have hle : (cascadeTop (r + 1) m + 1).choose (r + 2) ≤ K.choose (r + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega
    · have hzero : m - (cascadeTop (r + 1) m).choose (r + 1) = 0 := by
        rw [heq]; omega
      rw [hzero, cascadeUpper_zero_right, Nat.add_zero, heq]

/--
**The cap is monotone.** More faces at one order never permit fewer at the next.

Weak and not strict: `cascadeUpper 1` is `fun a => a.choose 2`, which is `0` at
both `0` and `1`. Upstream's `Nat.macaulayPow` *is* strictly monotone, and the
difference is exactly the `+1` on the top index that makes it the multicomplex
bound rather than this one.
-/
public theorem cascadeUpper_mono : ∀ (r : ℕ) {a b : ℕ}, a ≤ b →
    cascadeUpper r a ≤ cascadeUpper r b := by
  intro r
  induction r with
  | zero => intro a b _; simp [cascadeUpper]
  | succ r ih =>
    intro a b hab
    have hmono : cascadeTop (r + 1) a ≤ cascadeTop (r + 1) b := cascadeTop_mono r hab
    rw [cascadeUpper, cascadeUpper]
    rcases hmono.lt_or_eq with hlt | heq
    · have hbound : cascadeUpper r (a - (cascadeTop (r + 1) a).choose (r + 1))
          ≤ (cascadeTop (r + 1) a).choose (r + 1) :=
        cascadeUpper_le_choose r _ _ (sub_cascadeTop_choose_le r a)
      have hpascal : (cascadeTop (r + 1) a + 1).choose (r + 2)
          = (cascadeTop (r + 1) a).choose (r + 1) + (cascadeTop (r + 1) a).choose (r + 2) :=
        Nat.choose_succ_succ' _ _
      have hle : (cascadeTop (r + 1) a + 1).choose (r + 2) ≤ (cascadeTop (r + 1) b).choose (r + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega
    · have hrem : a - (cascadeTop (r + 1) a).choose (r + 1)
          ≤ b - (cascadeTop (r + 1) b).choose (r + 1) := by
        rw [← heq]; omega
      have := ih hrem
      rw [heq] at this ⊢
      omega

/--
**One greedy step, with the digit supplied.** If `k` is the cascade digit of `a`
at level `r + 1`, the cap peels off `C(k, r + 2)` and recurses.

`cascadeUpper` is defined through `Nat.findGreatest`, which the kernel evaluates
by scanning, so deciding a value of it costs time linear in that value and
overflows the stack well before the counts a real corpus reports. Supplying the
digit and checking the two binomial inequalities instead costs four cheap
comparisons per level, whatever the size. This is what lets the numbers an
analysis actually prints be checked in the kernel rather than only sampled.
-/
public theorem cascadeUpper_step {r a k : ℕ} (h₁ : k.choose (r + 1) ≤ a)
    (h₂ : a < (k + 1).choose (r + 1)) :
    cascadeUpper (r + 1) a = k.choose (r + 2) + cascadeUpper r (a - k.choose (r + 1)) := by
  rw [cascadeUpper, cascadeTop_eq h₁ h₂]

/-- The same step for the shadow. The zero guard has to be discharged too. -/
public theorem cascadeShadow_step {r a k : ℕ} (ha : a ≠ 0) (h₁ : k.choose (r + 1) ≤ a)
    (h₂ : a < (k + 1).choose (r + 1)) :
    cascadeShadow (r + 1) a = k.choose r + cascadeShadow r (a - k.choose (r + 1)) := by
  rw [cascadeShadow, if_neg ha, cascadeTop_eq h₁ h₂]

/--
**The shadow, evaluated against a binomial.** A level of size at most `C(K, r+1)`
touches at most `C(K, r)` below it.

This is the downward mirror of `cascadeUpper_le_choose`, and it is what makes
`cascadeShadow` monotone.
-/
public theorem cascadeShadow_le_choose :
    ∀ (r K m : ℕ), m ≤ K.choose (r + 1) → cascadeShadow (r + 1) m ≤ K.choose r := by
  intro r
  induction r with
  | zero =>
    intro K m hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp
    rw [cascadeShadow, if_neg (by omega)]
    simp [cascadeShadow]
  | succ r ih =>
    intro K m hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp
    have htK : cascadeTop (r + 1 + 1) m ≤ K := cascadeTop_le_of_le_choose hpos hm
    have hrem : m - (cascadeTop (r + 1 + 1) m).choose (r + 1 + 1)
        ≤ (cascadeTop (r + 1 + 1) m).choose (r + 1) := sub_cascadeTop_choose_le (r + 1) m
    have hih : cascadeShadow (r + 1) (m - (cascadeTop (r + 1 + 1) m).choose (r + 1 + 1))
        ≤ (cascadeTop (r + 1 + 1) m).choose r := ih _ _ hrem
    rw [cascadeShadow, if_neg (by omega)]
    rcases htK.lt_or_eq with hlt | heq
    · have hpascal : (cascadeTop (r + 1 + 1) m + 1).choose (r + 1)
          = (cascadeTop (r + 1 + 1) m).choose r + (cascadeTop (r + 1 + 1) m).choose (r + 1) :=
        Nat.choose_succ_succ' _ _
      have hle : (cascadeTop (r + 1 + 1) m + 1).choose (r + 1) ≤ K.choose (r + 1) :=
        Nat.choose_le_choose _ (by omega)
      omega
    · have htop : (cascadeTop (r + 1 + 1) m).choose (r + 1 + 1) ≤ m :=
        cascadeTop_choose_le (r + 1) m
      have hzero : m - (cascadeTop (r + 1 + 1) m).choose (r + 1 + 1) = 0 := by
        rw [heq] at htop ⊢; omega
      rw [hzero, cascadeShadow_zero_right, Nat.add_zero, heq]

/-- Below its own level the greedy digit is the level minus one, so a level that
is not full leaves the top index strictly short. -/
public theorem le_cascadeTop_of_pos {r m : ℕ} (hm : 0 < m) : r + 1 ≤ cascadeTop (r + 1) m :=
  (choose_le_iff_le_cascadeTop r m (r + 1)).1 (by rw [Nat.choose_self]; omega)

/--
**The cap, evaluated strictly.** A level strictly inside `C(K, r)` permits
strictly fewer than `C(K, r + 1)` above it.

The strict form is what the Galois connection needs: without it the greedy digit
of `cascadeUpper r a` cannot be pinned to the greedy digit of `a`.
-/
public theorem cascadeUpper_lt_choose :
    ∀ (r K m : ℕ), r + 1 ≤ K → m < K.choose r → cascadeUpper r m < K.choose (r + 1) := by
  intro r
  induction r with
  | zero =>
    intro K m hK hm
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    have : cascadeUpper 0 0 = 0 := rfl
    rw [this, Nat.choose_one_right]
    omega
  | succ r ih =>
    intro K m hK hm
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [cascadeUpper_zero_right]
      exact Nat.choose_pos (by omega)
    have hrt : r + 1 ≤ cascadeTop (r + 1) m := le_cascadeTop_of_pos hpos
    have htop : (cascadeTop (r + 1) m).choose (r + 1) ≤ m := cascadeTop_choose_le r m
    have htK : cascadeTop (r + 1) m ≤ K := by
      by_contra hcon
      have : (K + 1).choose (r + 1) ≤ (cascadeTop (r + 1) m).choose (r + 1) :=
        Nat.choose_le_choose _ (by omega)
      omega
    have hrem : m - (cascadeTop (r + 1) m).choose (r + 1) ≤ (cascadeTop (r + 1) m).choose r :=
      sub_cascadeTop_choose_le r m
    rw [cascadeUpper]
    show _ < (K + 1).choose (r + 2)
    have hpascalK : (K + 1).choose (r + 2) = K.choose (r + 1) + K.choose (r + 2) :=
      Nat.choose_succ_succ' _ _
    rcases htK.lt_or_eq with hlt | heq
    · have hbound : cascadeUpper r (m - (cascadeTop (r + 1) m).choose (r + 1))
          ≤ (cascadeTop (r + 1) m).choose (r + 1) :=
        cascadeUpper_le_choose r _ _ hrem
      have hpascal : (cascadeTop (r + 1) m + 1).choose (r + 2)
          = (cascadeTop (r + 1) m).choose (r + 1) + (cascadeTop (r + 1) m).choose (r + 2) :=
        Nat.choose_succ_succ' _ _
      have hle : (cascadeTop (r + 1) m + 1).choose (r + 2) ≤ K.choose (r + 2) :=
        Nat.choose_le_choose _ (by omega)
      have hposK : 0 < K.choose (r + 1) := Nat.choose_pos (by omega)
      omega
    · have hpascalt : (K + 1).choose (r + 1) = K.choose r + K.choose (r + 1) :=
        Nat.choose_succ_succ' _ _
      have hremlt : m - (cascadeTop (r + 1) m).choose (r + 1) < (cascadeTop (r + 1) m).choose r := by
        rw [heq] at htop ⊢; omega
      have hstrict : cascadeUpper r (m - (cascadeTop (r + 1) m).choose (r + 1))
          < (cascadeTop (r + 1) m).choose (r + 1) :=
        ih _ _ (by omega) hremlt
      rw [heq] at hstrict ⊢
      omega

/--
**The shadow is monotone.** More faces at one order never touch fewer below.
-/
public theorem cascadeShadow_mono : ∀ (r : ℕ) {a b : ℕ}, a ≤ b →
    cascadeShadow r a ≤ cascadeShadow r b := by
  intro r
  induction r with
  | zero => intro a b _; simp [cascadeShadow]
  | succ r ih =>
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · simp
    have hbpos : 0 < b := by omega
    have hmono : cascadeTop (r + 1) a ≤ cascadeTop (r + 1) b := cascadeTop_mono r hab
    have hrema : a - (cascadeTop (r + 1) a).choose (r + 1) ≤ (cascadeTop (r + 1) a).choose r :=
      sub_cascadeTop_choose_le r a
    rw [cascadeShadow, cascadeShadow, if_neg (by omega), if_neg (by omega)]
    rcases hmono.lt_or_eq with hlt | heq
    · have hkey : (cascadeTop (r + 1) a).choose r
          + cascadeShadow r (a - (cascadeTop (r + 1) a).choose (r + 1))
          ≤ (cascadeTop (r + 1) a + 1).choose r := by
        rcases Nat.eq_zero_or_pos r with rfl | hrpos
        · simp [cascadeShadow]
        · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
          have hin : cascadeShadow (r' + 1) (a - (cascadeTop (r' + 1 + 1) a).choose (r' + 1 + 1))
              ≤ (cascadeTop (r' + 1 + 1) a).choose r' :=
            cascadeShadow_le_choose r' (cascadeTop (r' + 1 + 1) a) _ hrema
          have hp : (cascadeTop (r' + 1 + 1) a + 1).choose (r' + 1)
              = (cascadeTop (r' + 1 + 1) a).choose r' + (cascadeTop (r' + 1 + 1) a).choose (r' + 1) :=
            Nat.choose_succ_succ' _ _
          omega
      have hle : (cascadeTop (r + 1) a + 1).choose r ≤ (cascadeTop (r + 1) b).choose r :=
        Nat.choose_le_choose _ (by omega)
      have hnn : 0 ≤ cascadeShadow r (b - (cascadeTop (r + 1) b).choose (r + 1)) := Nat.zero_le _
      omega
    · have hrem : a - (cascadeTop (r + 1) a).choose (r + 1)
          ≤ b - (cascadeTop (r + 1) b).choose (r + 1) := by
        rw [← heq]; omega
      have := ih hrem
      rw [heq] at this ⊢
      omega

/-- At level one the greedy digit is the number itself. -/
public theorem cascadeTop_one (a : ℕ) : cascadeTop 1 a = a :=
  cascadeTop_eq (by simp) (by simp)

/-- At level one the cap is a single binomial coefficient. -/
public theorem cascadeUpper_one (a : ℕ) : cascadeUpper 1 a = a.choose 2 := by
  rw [cascadeUpper, cascadeTop_one]
  simp

/--
**Counit.** Shifting a level up and then back down never overshoots.
-/
public theorem cascadeShadow_cascadeUpper_le :
    ∀ (r a : ℕ), cascadeShadow (r + 1) (cascadeUpper r a) ≤ a := by
  intro r
  induction r with
  | zero => intro a; simp [cascadeUpper, cascadeShadow]
  | succ r ih =>
    intro a
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · simp
    have hrt : r + 1 ≤ cascadeTop (r + 1) a := le_cascadeTop_of_pos hpos
    have htop : (cascadeTop (r + 1) a).choose (r + 1) ≤ a := cascadeTop_choose_le r a
    have hlt : a < (cascadeTop (r + 1) a + 1).choose (r + 1) := lt_succ_cascadeTop_choose r a
    have hpascal : (cascadeTop (r + 1) a + 1).choose (r + 1)
        = (cascadeTop (r + 1) a).choose r + (cascadeTop (r + 1) a).choose (r + 1) :=
      Nat.choose_succ_succ' _ _
    have hremlt : a - (cascadeTop (r + 1) a).choose (r + 1) < (cascadeTop (r + 1) a).choose r := by
      omega
    have hVlt : cascadeUpper r (a - (cascadeTop (r + 1) a).choose (r + 1))
        < (cascadeTop (r + 1) a).choose (r + 1) :=
      cascadeUpper_lt_choose r _ _ (by omega) hremlt
    have hunf : cascadeUpper (r + 1) a
        = (cascadeTop (r + 1) a).choose (r + 2)
          + cascadeUpper r (a - (cascadeTop (r + 1) a).choose (r + 1)) := by
      rw [cascadeUpper]
    rcases Nat.eq_zero_or_pos (cascadeUpper (r + 1) a) with hU | hU
    · rw [hU, cascadeShadow_zero_right]; omega
    have hpascal2 : (cascadeTop (r + 1) a + 1).choose (r + 2)
        = (cascadeTop (r + 1) a).choose (r + 1) + (cascadeTop (r + 1) a).choose (r + 2) :=
      Nat.choose_succ_succ' _ _
    have hbr : (cascadeTop (r + 1) a).choose (r + 1 + 1) = (cascadeTop (r + 1) a).choose (r + 2) :=
      rfl
    have htopU : cascadeTop (r + 1 + 1) (cascadeUpper (r + 1) a) = cascadeTop (r + 1) a := by
      refine cascadeTop_eq ?_ ?_
      · rw [hunf]; omega
      · rw [hunf]
        have hbr2 : (cascadeTop (r + 1) a + 1).choose (r + 1 + 1)
            = (cascadeTop (r + 1) a + 1).choose (r + 2) := rfl
        omega
    rw [cascadeShadow, if_neg (by omega), htopU]
    have hsub : cascadeUpper (r + 1) a - (cascadeTop (r + 1) a).choose (r + 1 + 1)
        = cascadeUpper r (a - (cascadeTop (r + 1) a).choose (r + 1)) := by
      rw [hunf]; omega
    rw [hsub]
    have := ih (a - (cascadeTop (r + 1) a).choose (r + 1))
    omega

/--
**Unit.** Shifting a level down and then back up never loses anything.

Stated from order two upward. At order one it is false and not by accident: a
single level of singletons has the one empty set below it whatever its size, so
no bound on the level can be read back off its shadow.
-/
public theorem le_cascadeUpper_cascadeShadow :
    ∀ (r b : ℕ), b ≤ cascadeUpper (r + 1) (cascadeShadow (r + 2) b) := by
  intro r
  induction r with
  | zero =>
    intro b
    rcases Nat.eq_zero_or_pos b with rfl | hpos
    · simp
    have hrt : 2 ≤ cascadeTop 2 b := le_cascadeTop_of_pos hpos
    have htop : (cascadeTop 2 b).choose 2 ≤ b := cascadeTop_choose_le 1 b
    have hlt : b < (cascadeTop 2 b + 1).choose 2 := lt_succ_cascadeTop_choose 1 b
    have hpascal : (cascadeTop 2 b + 1).choose 2 = (cascadeTop 2 b).choose 1 + (cascadeTop 2 b).choose 2 :=
      Nat.choose_succ_succ' _ _
    have hone : (cascadeTop 2 b).choose 1 = cascadeTop 2 b := Nat.choose_one_right _
    have hunf : cascadeShadow 2 b
        = (cascadeTop 2 b).choose 1 + cascadeShadow 1 (b - (cascadeTop 2 b).choose 2) := by
      rw [cascadeShadow, if_neg (by omega)]
    rcases Nat.eq_zero_or_pos (b - (cascadeTop 2 b).choose 2) with hrem | hrem
    · have : cascadeShadow 2 b = cascadeTop 2 b := by rw [hunf, hrem]; simp [cascadeShadow, hone]
      rw [this, cascadeUpper_one]
      omega
    · have hs1 : cascadeShadow 1 (b - (cascadeTop 2 b).choose 2) = 1 := by
        rw [cascadeShadow, if_neg (by omega)]
        simp [cascadeShadow]
      have : cascadeShadow 2 b = cascadeTop 2 b + 1 := by rw [hunf, hs1, hone]
      rw [this, cascadeUpper_one]
      have : (cascadeTop 2 b + 1).choose 2 = (cascadeTop 2 b).choose 1 + (cascadeTop 2 b).choose 2 :=
        Nat.choose_succ_succ' _ _
      omega
  | succ r ih =>
    intro b
    rcases Nat.eq_zero_or_pos b with rfl | hpos
    · simp
    have hrt : r + 2 + 1 ≤ cascadeTop (r + 2 + 1) b := le_cascadeTop_of_pos hpos
    have hbrA : (cascadeTop (r + 2 + 1) b).choose (r + 1 + 1)
        = (cascadeTop (r + 2 + 1) b).choose (r + 2) := rfl
    have hbrB : (cascadeTop (r + 2 + 1) b).choose (r + 1 + 2)
        = (cascadeTop (r + 2 + 1) b).choose (r + 2 + 1) := rfl
    have hbrC : (cascadeTop (r + 2 + 1) b + 1).choose (r + 1 + 1)
        = (cascadeTop (r + 2 + 1) b + 1).choose (r + 2) := rfl
    have htop : (cascadeTop (r + 2 + 1) b).choose (r + 2 + 1) ≤ b := cascadeTop_choose_le (r + 2) b
    have hlt : b < (cascadeTop (r + 2 + 1) b + 1).choose (r + 2 + 1) :=
      lt_succ_cascadeTop_choose (r + 2) b
    have hpascal : (cascadeTop (r + 2 + 1) b + 1).choose (r + 2 + 1)
        = (cascadeTop (r + 2 + 1) b).choose (r + 2) + (cascadeTop (r + 2 + 1) b).choose (r + 2 + 1) :=
      Nat.choose_succ_succ' _ _
    have hpascal2 : (cascadeTop (r + 2 + 1) b + 1).choose (r + 1 + 1)
        = (cascadeTop (r + 2 + 1) b).choose (r + 1) + (cascadeTop (r + 2 + 1) b).choose (r + 1 + 1) :=
      Nat.choose_succ_succ' _ _
    have hremlt : b - (cascadeTop (r + 2 + 1) b).choose (r + 2 + 1)
        < (cascadeTop (r + 2 + 1) b).choose (r + 2) := by omega
    have hsig : cascadeShadow (r + 2) (b - (cascadeTop (r + 2 + 1) b).choose (r + 2 + 1))
        ≤ (cascadeTop (r + 2 + 1) b).choose (r + 1) :=
      cascadeShadow_le_choose (r + 1) _ _ (by omega)
    have hunf : cascadeShadow (r + 2 + 1) b
        = (cascadeTop (r + 2 + 1) b).choose (r + 2)
          + cascadeShadow (r + 2) (b - (cascadeTop (r + 2 + 1) b).choose (r + 2 + 1)) := by
      rw [cascadeShadow, if_neg (by omega)]
    rcases lt_or_eq_of_le hsig with hcase | hcase
    · have htopS : cascadeTop (r + 1 + 1) (cascadeShadow (r + 2 + 1) b)
          = cascadeTop (r + 2 + 1) b := by
        refine cascadeTop_eq ?_ ?_ <;> omega
      have hsub : cascadeShadow (r + 2 + 1) b - (cascadeTop (r + 2 + 1) b).choose (r + 1 + 1)
          = cascadeShadow (r + 2) (b - (cascadeTop (r + 2 + 1) b).choose (r + 2 + 1)) := by
        omega
      have hunfU : cascadeUpper (r + 1 + 1) (cascadeShadow (r + 2 + 1) b)
          = (cascadeTop (r + 2 + 1) b).choose (r + 1 + 2)
            + cascadeUpper (r + 1)
                (cascadeShadow (r + 2) (b - (cascadeTop (r + 2 + 1) b).choose (r + 2 + 1))) := by
        rw [cascadeUpper, htopS, hsub]
      have hihb := ih (b - (cascadeTop (r + 2 + 1) b).choose (r + 2 + 1))
      rw [hunfU]
      omega
    · have hSeq : cascadeShadow (r + 2 + 1) b
          = (cascadeTop (r + 2 + 1) b + 1).choose (r + 1 + 1) := by omega
      rw [hSeq, cascadeUpper_choose (r + 1) _ (by omega)]
      have hp2 : (cascadeTop (r + 2 + 1) b + 1).choose (r + 1 + 2)
          = (cascadeTop (r + 2 + 1) b).choose (r + 1 + 1)
            + (cascadeTop (r + 2 + 1) b).choose (r + 1 + 2) := Nat.choose_succ_succ' _ _
      omega

/--
**The Galois connection.** The Kruskal-Katona shadow bound and the Kruskal-Katona
cap are adjoint: a level of size `b` can sit above a level of size `a` exactly
when the shadow bound permits it, and exactly when the cap permits it.

This is what licenses reading the theorem in the capping direction. The shadow
direction says a measured count at order `r + 2` forces at least
`cascadeShadow (r + 2)` of them at order `r + 1`; this says the two readings
carry the same content, with no slack lost either way.

From order two upward; see `le_cascadeUpper_cascadeShadow` for why order one is
genuinely excluded.
-/
public theorem cascadeShadow_le_iff_le_cascadeUpper (r a b : ℕ) :
    cascadeShadow (r + 2) b ≤ a ↔ b ≤ cascadeUpper (r + 1) a := by
  constructor
  · intro h
    exact le_trans (le_cascadeUpper_cascadeShadow r b) (cascadeUpper_mono (r + 1) h)
  · intro h
    exact le_trans (cascadeShadow_mono (r + 2) h) (cascadeShadow_cascadeUpper_le (r + 1) a)

/-- The same statement as a `GaloisConnection`. -/
public theorem galoisConnection_cascadeShadow_cascadeUpper (r : ℕ) :
    GaloisConnection (cascadeShadow (r + 2)) (cascadeUpper (r + 1)) :=
  fun b a => cascadeShadow_le_iff_le_cascadeUpper r a b

end AISafetyAtlas.Combinatorics
