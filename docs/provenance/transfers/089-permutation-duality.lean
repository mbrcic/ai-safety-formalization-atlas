import AISafetyAtlas.Learning.Sharp
import Mathlib.Data.Set.Finite.Range

/-!
Schumacher, Vose and Whitley (2001), Corollary ("Duality"), PDF p. 3.
`V(σA, f) = V(A, σf)`: for finite `X` and `Y`, a deterministic non-repeating
blackbox search algorithm `A` with search operator `g`, a permutation `σ` of
`X` and `f : X → Y`, the performance vector of the permuted algorithm
(search operator `σ⁻¹ ∘ g ∘ σ_x`) on `f` equals that of `A` on
`σf = f ∘ σ⁻¹`. Lengths `m ≤ |X|`; traces start from the empty trace.
"Non-repeating" is read in its strong form: on every non-repeating trace
shorter than `|X|` the operator returns a point not yet in the trace (this
implies the reachable-trace reading). The cited theorem is
`AISafetyAtlas.Learning.observed_permRule`.

The map, for a rule `r` of depth `m`, a permutation `π` and an objective `f`:
let `c` be what `r` observes on `f ∘ π` and `d` what `permRule π r` observes on
`f`, with query points `x₀ k = ruleVisit r c k` and `x₁ k = ruleVisit r d k`.
The printed domain is `Fin (m + 1) × Bool`, a copy of each depth below `m`
for each of the two runs plus a spare depth. The printed objective at
`(k, b)` is `some (f (π (if b then x₀ k else x₁ k)))` below depth `m` and
`none` at depth `m`; the cost alphabet is its finite range. The printed
permutation swaps the two copies. At a trace of length `k < m` the printed
operator decodes the costs, applies `r k` and picks `(k, false)` when the
result is `x₀ k` and `(k, true)` otherwise; it falls back to a fresh point
whenever its choice is already in the trace. Unfolding `traceRun`,
`permSearch` and `ruleVisit` by depth shows that the printed performance
vectors are `some ∘ d` (permuted algorithm on the objective) and `some ∘ c`
(algorithm on the permuted objective), so print's conclusion gives `d = c`.

The forward direction is omitted: it needs the bridge from `observed` of
`searchRule` to the cost list of `traceRun`, which the library states only
as `replay_observed`.

Checked: `lake env lean docs/provenance/transfers/089-permutation-duality.lean`
-/

namespace Transfer089

open AISafetyAtlas.Learning Classical

universe uX uY a b

/-- Print's non-repeating operator (strong reading). -/
def NonRepeating {X : Type a} {Y : Type b} [Finite X] (g : List (X × Y) → X) : Prop :=
  ∀ T : List (X × Y), (T.map Prod.fst).Nodup → T.length < Nat.card X →
    g T ∉ T.map Prod.fst

def PrintStatement : Prop :=
  ∀ (X : Type a) (Y : Type b) [Finite X] [Finite Y] (g : List (X × Y) → X),
    NonRepeating g → ∀ (σ : Equiv.Perm X) (f : X → Y) (m : ℕ), m ≤ Nat.card X →
      (traceRun (permSearch σ g) f m).map Prod.snd =
        (traceRun g (fun x ↦ f (σ.symm x)) m).map Prod.snd

def LeanStatement : Prop :=
  ∀ {X : Type uX} {Y : Type uY} {m : ℕ} (π : Equiv.Perm X) (r : AdaptiveRule X Y m)
    (f : X → Y), observed (permRule π r) f = observed r (f ∘ (π : X → X))

section

variable {X : Type uX} {Y : Type uY} {m : ℕ} (π : Equiv.Perm X) (r : AdaptiveRule X Y m)
  (f : X → Y)

abbrev Pt (m : ℕ) : Type := Fin (m + 1) × Bool

noncomputable def x0 (k : Fin m) : X := ruleVisit r (observed r (f ∘ π)) k
noncomputable def x1 (k : Fin m) : X := ruleVisit r (observed (permRule π r) f) k

noncomputable def cost0 (q : Pt m) : Option Y :=
  if h : (q.1 : ℕ) < m then
    some (f (π (if q.2 then x0 π r f ⟨q.1, h⟩ else x1 π r f ⟨q.1, h⟩)))
  else none

abbrev Cost : Type uY := Set.range (cost0 π r f)

instance : Finite (Cost π r f) := Finite.Set.finite_range _

noncomputable def fPrint (q : Pt m) : Cost π r f := ⟨cost0 π r f q, q, rfl⟩

def swap : Equiv.Perm (Pt m) :=
  ⟨fun q ↦ (q.1, !q.2), fun q ↦ (q.1, !q.2), fun q ↦ by simp, fun q ↦ by simp⟩

noncomputable def pref (T : List (Pt m × Cost π r f)) : Pt m :=
  if hk : T.length < m then
    (⟨T.length, by omega⟩, !decide (r ⟨T.length, hk⟩
      (fun i ↦ ((T[i.val]'i.isLt).2.1).getD (f (x0 π r f ⟨0, by omega⟩))) =
        x0 π r f ⟨T.length, hk⟩))
  else (0, false)

noncomputable def gPrint (T : List (Pt m × Cost π r f)) : Pt m :=
  if pref π r f T ∉ T.map Prod.fst then pref π r f T
  else if h : ∃ q, q ∉ T.map Prod.fst then h.choose else pref π r f T

/-- The map: domain, cost alphabet, operator, permutation, objective and length. -/
noncomputable def phi :
    (List (Pt m × Cost π r f) → Pt m) × Equiv.Perm (Pt m) × (Pt m → Cost π r f) × ℕ :=
  (gPrint π r f, swap, fPrint π r f, m)

theorem exists_fresh (l : List (Pt m)) (hl : l.length < Nat.card (Pt m)) : ∃ q, q ∉ l := by
  classical
  by_contra h
  push Not at h
  have h1 : (Finset.univ : Finset (Pt m)) ⊆ l.toFinset := fun q _ ↦ List.mem_toFinset.mpr (h q)
  have h2 := (Finset.card_le_card h1).trans (List.toFinset_card_le l)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
  omega

theorem gPrint_eq (T : List (Pt m × Cost π r f)) (k : ℕ) (hlen : T.length = k) (hk : k < m)
    (e : Fin m → Y)
    (hcost : ∀ i (hi : i < k), ((T[i]'(by omega)).2.1 : Option Y) = some (e ⟨i, by omega⟩))
    (hdepth : ∀ q ∈ T.map Prod.fst, (q.1 : ℕ) < k) :
    gPrint π r f T =
      (⟨k, by omega⟩, !decide (ruleVisit r e ⟨k, hk⟩ = x0 π r f ⟨k, hk⟩)) := by
  subst hlen
  have hp : pref π r f T = (⟨T.length, by omega⟩,
      !decide (ruleVisit r e ⟨T.length, hk⟩ = x0 π r f ⟨T.length, hk⟩)) := by
    have hfun : (fun i : Fin T.length ↦
        ((T[i.val]'i.isLt).2.1).getD (f (x0 π r f ⟨0, by omega⟩))) =
        fun i : Fin T.length ↦ e (i.castLE hk.le) := by
      funext i
      rw [hcost i i.isLt]
      rfl
    simp only [pref, dif_pos hk, hfun]
    rfl
  have hnot : pref π r f T ∉ T.map Prod.fst := by
    intro hmem
    have := hdepth _ hmem
    rw [hp] at this
    exact lt_irrefl _ this
  unfold gPrint
  rw [if_pos hnot, hp]

theorem nonRepeating : NonRepeating (gPrint π r f) := by
  intro T _ hT
  by_cases hp : pref π r f T ∉ T.map Prod.fst
  · simpa only [gPrint, if_pos hp] using hp
  · have hfresh := exists_fresh (T.map Prod.fst) (by simpa using hT)
    simp only [gPrint, if_neg hp, dif_pos hfresh]
    exact hfresh.choose_spec

theorem sim (G : List (Pt m × Cost π r f) → Pt m) (F : Pt m → Cost π r f)
    (P : Fin m → Pt m)
    (hstep : ∀ T : List (Pt m × Cost π r f), (hk : T.length < m) →
      (∀ i (hi : i < T.length), T[i] = (P ⟨i, by omega⟩, F (P ⟨i, by omega⟩))) →
        G T = P ⟨T.length, hk⟩) :
    ∀ k (hk : k ≤ m), traceRun G F k =
      List.ofFn (fun i : Fin k ↦ (P (i.castLE hk), F (P (i.castLE hk)))) := by
  intro k
  induction k with
  | zero => intro _; simp [traceRun]
  | succ k ih =>
    intro hk
    have hT := ih (Nat.le_of_succ_le hk)
    have hG : G (traceRun G F k) = P ⟨k, hk⟩ := by
      have h := hstep (traceRun G F k) (by rw [hT, List.length_ofFn]; omega) (by
        intro i hi
        simp only [hT, List.getElem_ofFn]
        rfl)
      simpa only [hT, List.length_ofFn] using h
    show traceRun G F k ++ [(G (traceRun G F k), F (G (traceRun G F k)))] = _
    rw [hG, hT, List.ofFn_succ', List.concat_eq_append]
    rfl

theorem costL (i : Fin m) :
    (fPrint π r f (i.castSucc, decide (x1 π r f i = x0 π r f i))).1 =
      some (observed (permRule π r) f i) := by
  have hd : f (π (x1 π r f i)) = observed (permRule π r) f i :=
    observed_consistent (permRule π r) f i
  have hlt : ((i.castSucc : Fin (m + 1)) : ℕ) < m := by simp
  have key : cost0 π r f (i.castSucc, decide (x1 π r f i = x0 π r f i)) =
      some (f (π (if decide (x1 π r f i = x0 π r f i) then x0 π r f i else x1 π r f i))) :=
    dif_pos hlt
  change cost0 π r f _ = _
  rw [key]
  split_ifs with h1
  · rw [← of_decide_eq_true h1, hd]
  · rw [hd]

theorem costR (i : Fin m) :
    (fPrint π r f (swap.symm (i.castSucc, false))).1 = some (observed r (f ∘ π) i) := by
  have hc : f (π (x0 π r f i)) = observed r (f ∘ π) i := observed_consistent r (f ∘ π) i
  have hlt : ((i.castSucc : Fin (m + 1)) : ℕ) < m := by simp
  have key : cost0 π r f (i.castSucc, true) = some (f (π (x0 π r f i))) := dif_pos hlt
  change cost0 π r f (i.castSucc, true) = _
  rw [key, hc]

/-- (H): the Lean statement has no hypotheses; the printed ones hold at the map. -/
theorem H : NonRepeating (phi π r f).1 ∧ (phi π r f).2.2.2 ≤ Nat.card (Pt m) := by
  refine ⟨nonRepeating π r f, ?_⟩
  change m ≤ Nat.card (Pt m)
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

/-- (C): print's conclusion at the map gives the Lean conclusion. -/
theorem C (h : (traceRun (permSearch (phi π r f).2.1 (phi π r f).1) (phi π r f).2.2.1
      (phi π r f).2.2.2).map Prod.snd =
    (traceRun (phi π r f).1 (fun x ↦ (phi π r f).2.2.1 ((phi π r f).2.1.symm x))
      (phi π r f).2.2.2).map Prod.snd) :
    observed (permRule π r) f = observed r (f ∘ (π : X → X)) := by
  let s : Equiv.Perm (Pt m) := swap
  -- the permuted algorithm on the objective observes `some ∘ d`
  have hL := sim π r f (permSearch s (gPrint π r f)) (fPrint π r f)
    (fun i ↦ (i.castSucc, decide (x1 π r f i = x0 π r f i))) (fun T hk hT ↦ by
      have hlen : (traceMapX s T).length = T.length := by simp [traceMapX]
      have hg := gPrint_eq π r f (traceMapX s T) T.length hlen hk (observed (permRule π r) f)
        (fun i hi ↦ by
          simp only [traceMapX, List.getElem_map, Prod.map_snd, id]
          rw [hT i hi]
          exact costL π r f ⟨i, by omega⟩)
        (fun q hq ↦ by
          rw [traceMapX, List.map_map, List.mem_map] at hq
          obtain ⟨u, hu, rfl⟩ := hq
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
          rw [hT i hi]
          simpa [s, swap] using hi)
      change s.symm (gPrint π r f (traceMapX s T)) = _
      rw [hg]
      simp only [s, swap, Equiv.coe_fn_symm_mk, Bool.not_not]
      rfl)
    m le_rfl
  -- the algorithm on the permuted objective observes `some ∘ c`
  have hR := sim π r f (gPrint π r f) (fun x ↦ fPrint π r f (s.symm x))
    (fun i ↦ (i.castSucc, false)) (fun T hk hT ↦ by
      have hg := gPrint_eq π r f T T.length rfl hk (observed r (f ∘ π))
        (fun i hi ↦ by
          rw [hT i hi]
          exact costR π r f ⟨i, by omega⟩)
        (fun q hq ↦ by
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
          rw [hT i hi]
          simpa using hi)
      have hdec : decide (ruleVisit r (observed r (f ∘ π)) ⟨T.length, hk⟩ =
          x0 π r f ⟨T.length, hk⟩) = true := decide_eq_true rfl
      rw [hg, hdec]
      rfl)
    m le_rfl
  change (traceRun (permSearch s (gPrint π r f)) (fPrint π r f) m).map Prod.snd =
    (traceRun (gPrint π r f) (fun x ↦ fPrint π r f (s.symm x)) m).map Prod.snd at h
  rw [hL, hR, List.map_ofFn, List.map_ofFn] at h
  funext i
  have hi := congrArg Subtype.val (congrFun (List.ofFn_injective h) i)
  simp only [Function.comp] at hi
  rw [costL, costR] at hi
  exact Option.some_injective _ hi

end

theorem lean_of_print : PrintStatement.{0, uY} → LeanStatement.{uX, uY} := by
  intro hp X Y m π r f
  exact C π r f (hp (Pt m) (Cost π r f) (phi π r f).1 (H π r f).1 (phi π r f).2.1
    (phi π r f).2.2.1 (phi π r f).2.2.2 (H π r f).2)

end Transfer089
