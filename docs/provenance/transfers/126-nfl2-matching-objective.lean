import AISafetyAtlas.Learning.Sharp

/-!
Schumacher, Vose & Whitley (2001), NFL2, p. 3. "For any two algorithms `A` and
`B`, and for any function `f`, there exists a function `g` such that
`V(A, f) = V(B, g)`." `𝒳` and `𝒴` are finite (§2.1); an algorithm is a search
operator `g : 𝒯 → 𝒳` run from the empty trace, `T_{m+1} = T_m ‖ (g(T_m), f(g(T_m)))`,
whose range contains only non-repeating traces (traces have size at most `|𝒳|`);
`V_m(A, f) = (T_m(A, f))^y`, with the free length `m` universally quantified
(footnote 1). The cited declaration is `AISafetyAtlas.Learning.exists_observed_eq`:
adaptive no-revisit rules `X → Y` over any `Y` (finite `X`), at any length `m`.

The map sends a Lean instance `(X, Y, m, r₁, r₂, f)` to print's alphabet
`range f` (finite), the objective `f` corestricted to it, the same `m`, and the
two search operators `phi rᵢ`: on a trace of length `k < m` apply `rᵢ` at step
`k` to the trace's values (included into `Y`); on a longer trace return a point
the trace has not visited (the continuation to a complete search). (H): both
operators are non-repeating, from the injectivity of `ruleVisit rᵢ` and the
fresh continuation; `m ≤ |X|` from injectivity. (C): the printed performance
vector of `phi rᵢ` is the observed history of `rᵢ` (`replay_observed`), so
print's matching objective `g'` into `range f` gives the Lean `g = val ∘ g'`
(`observed_eq_iff`, read along the inclusion). `print_of_lean` is omitted: it
needs every cost history to be realized by some objective, a separate
induction.

Checked: `lake env lean docs/provenance/transfers/126-nfl2-matching-objective.lean`
-/

namespace Transfer126

open AISafetyAtlas.Learning Function

universe uX uY

/-- Print's performance vector `V_m(A, f)`. -/
def perf {X : Type uX} {Y : Type uY} (g : List (X × Y) → X) (f : X → Y) (m : ℕ) : List Y :=
  (traceRun g f m).map Prod.snd

/-- Print's algorithm: every trace it generates from `T₀` (size `≤ |𝒳|`) is non-repeating. -/
def NonRepeating {X : Type uX} {Y : Type uY} [Fintype X] (g : List (X × Y) → X) : Prop :=
  ∀ (f : X → Y) (n : ℕ), n ≤ Fintype.card X → ((traceRun g f n).map Prod.fst).Nodup

def PrintStatement : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [Fintype X] [Fintype Y] (A B : List (X × Y) → X),
    NonRepeating A → NonRepeating B → ∀ (f : X → Y) (m : ℕ), m ≤ Fintype.card X →
      ∃ g : X → Y, perf A f m = perf B g m

def LeanStatement : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [Fintype X] (m : ℕ) (r₁ r₂ : AdaptiveRule X Y m),
    (∀ c, Injective (ruleVisit r₁ c)) → (∀ c, Injective (ruleVisit r₂ c)) →
      ∀ f : X → Y, ∃ g : X → Y, observed r₂ g = observed r₁ f

variable {X : Type uX} {Y : Type uY} {m : ℕ}

/-- A rule over `Y` read on histories in a sub-alphabet `S ⊆ Y`. -/
def lift {S : Set Y} (r : AdaptiveRule X Y m) : AdaptiveRule X S m :=
  fun k c => r k (Subtype.val ∘ c)

open Classical in
/-- The search operator of a rule: the rule on short traces, a fresh point after. -/
noncomputable def phi {S : Set Y} (r : AdaptiveRule X Y m) (x₀ : X) : List (X × S) → X :=
  fun T => if h : T.length < m then r ⟨T.length, h⟩ (fun i => (T[i.val]'i.isLt).2.val)
    else if hx : ∃ x, x ∉ T.map Prod.fst then hx.choose else x₀

theorem replay_snd {S : Type uY} (g : List (X × S) → X) :
    ∀ (k : ℕ) (c : Fin k → S), (replay g k c).map Prod.snd = List.ofFn c
  | 0, _ => rfl
  | k + 1, c => by
    rw [replay, List.map_append, replay_snd g k, List.ofFn_succ' c]
    simp [List.concat_eq_append]
    rfl

theorem traceRun_fst {S : Type uY} (g : List (X × S) → X) (f : X → S) :
    ∀ n, (traceRun g f n).map Prod.fst = List.ofFn (fun j : Fin n => g (traceRun g f j))
  | 0 => rfl
  | n + 1 => by
    rw [traceRun, List.map_append, traceRun_fst g f n, List.ofFn_succ']
    simp [List.concat_eq_append]

theorem searchRule_phi {S : Set Y} (r : AdaptiveRule X Y m) (x₀ : X) :
    searchRule m (phi (S := S) r x₀) = lift r := by
  funext k c
  obtain ⟨k, hk⟩ := k
  change phi r x₀ (replay (phi r x₀) k c) = r ⟨k, hk⟩ (Subtype.val ∘ c)
  have hT := replay_snd (phi (S := S) r x₀) k c
  have hlen : (replay (phi r x₀) k c).length = k := by
    simpa using congrArg List.length hT
  generalize replay (phi r x₀) k c = T at hT hlen
  subst hlen
  rw [phi, dif_pos hk]
  congr 1
  funext i
  have := List.getElem_of_eq hT (i := i.val) (by simp)
  simp only [List.getElem_map, List.getElem_ofFn] at this
  simp [this]

theorem perf_phi {S : Set Y} (r : AdaptiveRule X Y m) (x₀ : X) (f : X → S) :
    perf (phi r x₀) f m = List.ofFn (observed (lift r) f) := by
  rw [perf, ← replay_observed, replay_snd, searchRule_phi]

theorem observed_lift {S : Set Y} (r : AdaptiveRule X Y m) (f : X → S) :
    observed r (Subtype.val ∘ f) = Subtype.val ∘ observed (lift r) f := by
  rw [observed_eq_iff]
  intro k
  exact congrArg Subtype.val ((observed_eq_iff (lift r) f _).mp rfl k)

/-- (H) for one operator: `phi r` is non-repeating. -/
theorem H [Fintype X] {S : Set Y} (r : AdaptiveRule X Y m)
    (h : ∀ c, Injective (ruleVisit r c)) (x₀ : X) : NonRepeating (phi (S := S) r x₀) := by
  classical
  intro f n hn
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
    rw [traceRun, List.map_append, List.nodup_append]
    refine ⟨ih (by omega), by simp, ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    rintro x hx _ rfl hxe
    subst hxe
    have hlen : (traceRun (phi (S := S) r x₀) f n).length = n := by
      simpa using congrArg List.length (traceRun_fst (phi (S := S) r x₀) f n)
    by_cases hnm : n < m
    · rw [traceRun_fst, List.mem_ofFn] at hx
      obtain ⟨j, hj⟩ := hx
      have hv := fun k : Fin m => ruleVisit_searchRule (phi (S := S) r x₀) f k
      rw [searchRule_phi] at hv
      have e : ruleVisit r (Subtype.val ∘ observed (lift (S := S) r) f) ⟨j, by omega⟩ =
          ruleVisit r (Subtype.val ∘ observed (lift (S := S) r) f) ⟨n, hnm⟩ :=
        (hv ⟨j, by omega⟩).trans (hj.trans (hv ⟨n, hnm⟩).symm)
      have := h _ e
      exact absurd (congrArg Fin.val this) (by simp; omega)
    · have hfresh : ∃ x, x ∉ (traceRun (phi (S := S) r x₀) f n).map Prod.fst := by
        by_contra hall
        push Not at hall
        have := (Finset.card_le_card (s := Finset.univ) (fun x _ => List.mem_toFinset.mpr (hall x))).trans
          (List.toFinset_card_le _)
        simp [hlen] at this
        omega
      have hval : phi (S := S) r x₀ (traceRun (phi r x₀) f n) = hfresh.choose := by
        rw [phi, dif_neg (by omega), dif_pos hfresh]
      exact hfresh.choose_spec (hval ▸ hx)

/-- (C): print's matching objective at the image gives the Lean one. -/
theorem C {S : Set Y} (r₁ r₂ : AdaptiveRule X Y m) (x₀ : X) (f : X → S)
    (hP : ∃ g' : X → S, perf (phi r₁ x₀) f m = perf (phi r₂ x₀) g' m) :
    ∃ g : X → Y, observed r₂ g = observed r₁ (Subtype.val ∘ f) := by
  obtain ⟨g', hg'⟩ := hP
  rw [perf_phi, perf_phi] at hg'
  refine ⟨Subtype.val ∘ g', ?_⟩
  rw [observed_lift, observed_lift, List.ofFn_injective hg']

theorem lean_of_print : PrintStatement.{uX, uY} → LeanStatement.{uX, uY} := by
  intro hP X Y _ m r₁ r₂ h₁ h₂ f
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨f, funext fun i => i.elim0⟩
  have hcard : m ≤ Fintype.card X := by
    simpa using Fintype.card_le_of_injective _ (h₁ (observed r₁ f))
  let x₀ : X := r₁ ⟨0, hm⟩ Fin.elim0
  classical
  let _ : Fintype (Set.range f) := Fintype.ofSurjective _ Set.rangeFactorization_surjective
  exact C r₁ r₂ x₀ (Set.rangeFactorization f)
    (hP X (Set.range f) (phi r₁ x₀) (phi r₂ x₀) (H r₁ h₁ x₀) (H r₂ h₂ x₀) _ m hcard)

end Transfer126
