module

public import AISafetyAtlas.Causal.BayesianNetwork
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Pearl's Properties 1 and 2 at discrete variables with countably many values

`AISafetyAtlas.Causal.BayesianNetwork`'s `Discrete` section states Pearl's
Definition 1.3.1 and equation (1.37) with each variable `c` ranging over an
arbitrary type `V c`. Pearl's standing setting is *"a finite number of discrete
variables"* (§1.1.2, PDF p. 24): the number of **variables** is finite, the number
of **values** is not bounded. Properties 1 and 2 (equations (1.38) and (1.39),
PDF p. 46) compare **marginals** of two members of the family, and the `Fin`-valued
marginal layer of `AISafetyAtlas.Causal.Model` cannot state them for a variable with
infinitely many values. This module is that layer.

## Choices

* **Values are real.** A marginal is a sum over the assignments that agree on the
  kept variables, which at infinitely many values is a series. Over an arbitrary
  ordered field such a series need not converge even when the joint does (over `ℚ`
  a marginal of a rational network can be irrational), so the statements are at
  print's own `ℝ`.
* **The marginal is an unconditional sum** (`tsum`) over the subtype of complete
  assignments agreeing with `w` on `s`. Every theorem below that reads one also
  proves the sum converges (`hasSum_marginal`), so no statement rests on `tsum`'s
  junk value.
* **Property 1 is multiplied out**, as in the finite layer
  (`Model.marginal_insert_parents`): `P(v_i, pa_i) = P(pa_i) · P_{pa_i}(v_i)`,
  which is print's quotient wherever `P(pa_i) > 0` and stays true where print's is
  undefined.
* **Property 2's binder names only the variable**, as in the finite layer
  (`Model.marginal_singleton_do_parents`): `c ∉ S`; an `S` meeting `PA_c` is
  print's instance at `S \ PA_c`.
-/

namespace AISafetyAtlas.Causal.Discrete

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {V : C → Type*} [∀ c, DecidableEq (V c)]

/-- The **marginal** on the variables `s`, at the values `w` takes there, of the
member of `P` at the intervention `do(targets = target)`: the sum of that member
over the complete assignments agreeing with `w` on `s`. -/
@[expose] public noncomputable def marginal (P : InterventionalFamily C V ℝ)
    (targets : Finset C) (target : (c : C) → V c) (s : Finset C) (w : (c : C) → V c) : ℝ :=
  ∑' v : {v : (c : C) → V c // ∀ d ∈ s, v d = w d}, P targets target v.1

private theorem ConditionalTables.family_nonneg {G : C → Finset C}
    (q : ConditionalTables C V ℝ G)
    (T : Finset C) (target v : (c : C) → V c) : 0 ≤ q.family T target v := by
  unfold ConditionalTables.family
  refine Finset.prod_nonneg fun d _ ↦ ?_
  split_ifs
  · exact zero_le_one
  · exact le_refl 0
  · exact q.nonneg _ _ _

private theorem ConditionalTables.family_eq_zero_of_mem {G : C → Finset C}
    (q : ConditionalTables C V ℝ G)
    {T : Finset C} {target v : (c : C) → V c} {d : C} (hd : d ∈ T) (hv : v d ≠ target d) :
    q.family T target v = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ d) (by rw [if_pos hd, if_neg (Ne.symm hv)])

/-- Pulling the factor of a free variable `c` out of a truncated product, at an
assignment where `c` already takes its forced value. -/
private theorem ConditionalTables.family_eq_table_mul {G : C → Finset C}
    (q : ConditionalTables C V ℝ G)
    {T : Finset C} {c : C} (hc : c ∉ T) (target v : (c : C) → V c) (hv : v c = target c) :
    q.family T target v = q.table c (v c) v * q.family (insert c T) target v := by
  simp only [ConditionalTables.family]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c),
    if_neg hc, if_pos (Finset.mem_insert_self c T), if_pos hv.symm, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun d hd ↦ ?_
  rw [Finset.mem_erase] at hd
  simp only [Finset.mem_insert, hd.1, false_or]

/-- Updating a sink `e` (a free variable no free variable reads) multiplies the
truncated product forcing `e` by `e`'s own table. -/
private theorem ConditionalTables.family_update {G : C → Finset C}
    (q : ConditionalTables C V ℝ G)
    {T : Finset C} {e : C} (heT : e ∉ T) (hsink : ∀ d ∉ T, e ∉ G d) (w x : (c : C) → V c)
    (hx : x e = w e) (a : V e) :
    q.family T w (Function.update x e a) = q.table e a x * q.family (insert e T) w x := by
  simp only [ConditionalTables.family]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e),
    if_neg heT, if_pos (Finset.mem_insert_self e T), if_pos hx.symm, one_mul,
    Function.update_self]
  congr 1
  · refine q.reads_parents e a _ x fun p hp ↦ Function.update_of_ne ?_ a x
    rintro rfl
    exact hsink p heT hp
  · refine Finset.prod_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_erase] at hd
    simp only [Finset.mem_insert, hd.1, false_or, Function.update_of_ne hd.1]
    by_cases hdT : d ∈ T
    · rw [if_pos hdT, if_pos hdT]
    · rw [if_neg hdT, if_neg hdT]
      refine q.reads_parents d (x d) _ x fun p hp ↦ Function.update_of_ne ?_ a x
      rintro rfl
      exact hsink d hdT hp

/-- Summing out one sink. -/
private theorem hasSum_indicator_of_insert {G : C → Finset C}
    (q : ConditionalTables C V ℝ G) {T s : Finset C} {e : C} (heT : e ∉ T) (hes : e ∉ s)
    (hsink : ∀ d ∉ T, e ∉ G d) (w : (c : C) → V c) {r : ℝ}
    (h : HasSum ({v : (c : C) → V c | ∀ d ∈ s, v d = w d}.indicator
      (q.family (insert e T) w)) r) :
    HasSum ({v : (c : C) → V c | ∀ d ∈ s, v d = w d}.indicator (q.family T w)) r := by
  set S := {v : (c : C) → V c | ∀ d ∈ s, v d = w d} with hS
  set h' := S.indicator (q.family (insert e T) w) with hh'
  have hmemS : ∀ x (a : V e), Function.update x e a ∈ S ↔ x ∈ S := by
    intro x a
    simp only [hS, Set.mem_ofPred_eq]
    refine forall₂_congr fun d hd ↦ ?_
    rw [Function.update_of_ne (fun h : d = e ↦ hes (h ▸ hd))]
  have hnn : ∀ x, 0 ≤ h' x := by
    intro x
    rw [hh', Set.indicator_apply]
    split_ifs
    exacts [q.family_nonneg _ w x, le_rfl]
  let X := {x : (c : C) → V c | x e = w e}
  let E : X × V e ≃ ((c : C) → V c) :=
    { toFun := fun p ↦ Function.update p.1.1 e p.2
      invFun := fun u ↦ (⟨Function.update u e (w e), Function.update_self _ _ _⟩, u e)
      left_inv := by
        rintro ⟨⟨x, hx⟩, a⟩
        refine Prod.ext (Subtype.ext ?_) (Function.update_self _ _ _)
        change Function.update (Function.update x e a) e (w e) = x
        rw [Function.update_idem, ← show x e = w e from hx, Function.update_eq_self]
      right_inv := fun u ↦ by
        change Function.update (Function.update u e (w e)) e (u e) = u
        rw [Function.update_idem, Function.update_eq_self] }
  have hpt : ∀ p : X × V e,
      S.indicator (q.family T w) (E p) = q.table e p.2 p.1.1 * h' p.1.1 := by
    rintro ⟨⟨x, hx⟩, a⟩
    change S.indicator (q.family T w) (Function.update x e a) = q.table e a x * h' x
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem ((hmemS x a).mpr hxS), hh', Set.indicator_of_mem hxS,
        q.family_update heT hsink w x hx a]
    · rw [Set.indicator_of_notMem (fun h ↦ hxS ((hmemS x a).mp h)), hh',
        Set.indicator_of_notMem hxS, mul_zero]
  have hsupp : Function.support h' ⊆ X := by
    intro x hx
    by_contra hxe
    refine hx ?_
    rw [hh']
    exact Set.indicator_apply_eq_zero.mpr fun _ ↦
      q.family_eq_zero_of_mem (Finset.mem_insert_self e T) hxe
  have hX : HasSum (fun x : X ↦ h' x.1) r :=
    (hasSum_subtype_iff_of_support_subset (s := X) hsupp).mpr h
  let H : X × V e → ℝ := fun p ↦ q.table e p.2 p.1.1 * h' p.1.1
  have hfib : ∀ x : X, HasSum (fun a ↦ H (x, a)) (h' x.1) := by
    intro x
    simpa [H] using (q.hasSum_one e x.1).mul_right (h' x.1)
  have hHnn : 0 ≤ H := fun p ↦ mul_nonneg (q.nonneg _ _ _) (hnn _)
  have hHs : Summable H := by
    refine (summable_prod_of_nonneg hHnn).mpr ⟨fun x ↦ (hfib x).summable, ?_⟩
    have : (fun x : X ↦ ∑' a, H (x, a)) = fun x : X ↦ h' x.1 :=
      funext fun x ↦ (hfib x).tsum_eq
    rw [this]
    exact hX.summable
  have hHr : HasSum H r := by
    rw [hX.unique (hHs.hasSum.prod_fiberwise hfib)]
    exact hHs.hasSum
  rw [← E.hasSum_iff]
  have hfun : (S.indicator (q.family T w)) ∘ E = H := funext hpt
  rw [hfun]
  exact hHr

/-- Summing out a set of free variables none of which is read by a free variable
outside it. -/
private theorem hasSum_indicator_of_union {G : C → Finset C}
    (hG : ∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c)
    (q : ConditionalTables C V ℝ G) (s : Finset C) (w : (c : C) → V c) (r : ℝ) :
    ∀ (K T : Finset C), (∀ e ∈ K, e ∉ s) → (∀ e ∈ K, e ∉ T) →
      (∀ e ∈ K, ∀ d, d ∉ T → d ∉ K → e ∉ G d) →
      HasSum ({v : (c : C) → V c | ∀ d ∈ s, v d = w d}.indicator (q.family (T ∪ K) w)) r →
      HasSum ({v : (c : C) → V c | ∀ d ∈ s, v d = w d}.indicator (q.family T w)) r := by
  obtain ⟨rank, hrank⟩ := hG
  intro K
  induction K using Finset.strongInduction with
  | H K ih =>
    intro T hKs hKT hsink h
    rcases K.eq_empty_or_nonempty with rfl | hne
    · rwa [Finset.union_empty] at h
    obtain ⟨e, heK, hemax⟩ := K.exists_max_image rank hne
    refine hasSum_indicator_of_insert q (hKT e heK) (hKs e heK) ?_ w ?_
    · intro d hdT hed
      by_cases hdK : d ∈ K
      · have h1 := hrank d e hed
        have h2 := hemax d hdK
        omega
      · exact hsink e heK d hdT hdK hed
    · refine ih (K.erase e) (Finset.erase_ssubset heK) (insert e T) ?_ ?_ ?_ ?_
      · intro e' he'
        exact hKs e' (Finset.mem_of_mem_erase he')
      · intro e' he' hmem
        rw [Finset.mem_erase] at he'
        rcases Finset.mem_insert.mp hmem with h1 | h1
        · exact he'.1 h1
        · exact hKT e' he'.2 h1
      · intro e' he' d hd hd'
        rw [Finset.mem_insert, not_or] at hd
        rw [Finset.mem_erase, not_and] at hd'
        exact hsink e' (Finset.mem_of_mem_erase he') d hd.2 (fun hdK ↦ hd' hd.1 hdK)
      · have hTK : insert e T ∪ K.erase e = T ∪ K := by
          ext d
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
          by_cases hd : d = e
          · subst hd
            simp [heK]
          · simp [hd]
        rwa [hTK]

/-- **Each member of the family is a probability distribution**: the truncated
product of an acyclic mechanism family sums to one over all complete assignments,
however many values each variable has. -/
public theorem ConditionalTables.hasSum_family {G : C → Finset C}
    (hG : ∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c)
    (q : ConditionalTables C V ℝ G) (targets : Finset C) (target : (c : C) → V c) :
    HasSum (q.family targets target) 1 := by
  have hind : ∀ f : ((c : C) → V c) → ℝ,
      {v : (c : C) → V c | ∀ d ∈ (∅ : Finset C), v d = target d}.indicator f = f :=
    fun f ↦ funext fun v ↦ Set.indicator_of_mem
      (show v ∈ {v : (c : C) → V c | ∀ d ∈ (∅ : Finset C), v d = target d} from
        fun d hd ↦ absurd hd (Finset.notMem_empty d)) f
  have h := hasSum_indicator_of_union hG q ∅ target 1 targetsᶜ targets
    (fun e _ ↦ Finset.notMem_empty e) (fun e he ↦ Finset.mem_compl.mp he)
    (fun e he d hd hd' ↦ absurd (Finset.mem_compl.mpr hd) hd')
  rw [hind, hind, Finset.union_compl] at h
  refine h ?_
  have hu : q.family Finset.univ target = fun v ↦ if v = target then 1 else 0 :=
    funext fun v ↦ q.family_univ target v
  rw [hu]
  exact hasSum_ite_eq target 1

/-- Every marginal of a truncated product converges. -/
public theorem ConditionalTables.hasSum_marginal {G : C → Finset C}
    (hG : ∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c)
    (q : ConditionalTables C V ℝ G) (targets : Finset C) (target : (c : C) → V c)
    (s : Finset C) (w : (c : C) → V c) :
    HasSum (fun v : {v : (c : C) → V c // ∀ d ∈ s, v d = w d} => q.family targets target v.1)
      (marginal q.family targets target s w) := by
  exact ((q.hasSum_family hG targets target).summable.subtype
    (fun v ↦ ∀ d ∈ s, v d = w d)).hasSum

/-- **Setting a variable's parents leaves it its own mechanism**, whatever else is
set: under `do(PA_c = pa_c, S = s)` with `c ∉ S`, the marginal of `c` is its table
at `pa_c`. -/
public theorem ConditionalTables.marginal_singleton_do_parents {G : C → Finset C}
    (hG : ∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c)
    (q : ConditionalTables C V ℝ G) {c : C} {extra : Finset C} (hc : c ∉ extra)
    (target : (c : C) → V c) :
    marginal q.family (G c ∪ extra) target {c} target = q.table c (target c) target := by
  obtain ⟨rank, hrank⟩ := id hG
  have hcT : c ∉ G c ∪ extra := by
    rw [Finset.mem_union, not_or]
    exact ⟨fun h ↦ lt_irrefl _ (hrank c c h), hc⟩
  have hpt : ∀ v, {v : (c : C) → V c | ∀ d ∈ ({c} : Finset C), v d = target d}.indicator
      (q.family (G c ∪ extra) target) v =
        q.table c (target c) target * q.family (insert c (G c ∪ extra)) target v := by
    intro v
    by_cases hvc : v c = target c
    · have hmem : v ∈ {v : (c : C) → V c | ∀ d ∈ ({c} : Finset C), v d = target d} := by
        intro d hd
        rw [Finset.mem_singleton] at hd
        rw [hd]
        exact hvc
      rw [Set.indicator_of_mem hmem, q.family_eq_table_mul hcT target v hvc]
      by_cases hpa : ∀ p ∈ G c, v p = target p
      · congr 1
        rw [q.reads_parents c (v c) v target hpa, hvc]
      · push Not at hpa
        obtain ⟨p, hp, hvp⟩ := hpa
        rw [q.family_eq_zero_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hp)) hvp,
          mul_zero, mul_zero]
    · have hmem : v ∉ {v : (c : C) → V c | ∀ d ∈ ({c} : Finset C), v d = target d} :=
        fun h ↦ hvc (h c (Finset.mem_singleton_self c))
      rw [Set.indicator_of_notMem hmem, q.family_eq_zero_of_mem (Finset.mem_insert_self c _) hvc,
        mul_zero]
  have hsum : HasSum ({v : (c : C) → V c | ∀ d ∈ ({c} : Finset C), v d = target d}.indicator
      (q.family (G c ∪ extra) target)) (q.table c (target c) target) := by
    rw [funext hpt]
    simpa using (q.hasSum_family hG (insert c (G c ∪ extra)) target).mul_left
      (q.table c (target c) target)
  exact (tsum_subtype _ _).trans hsum.tsum_eq

/-- **The observational conditional of a variable given its parents is its
mechanism**, multiplied out: `P(v_c, pa_c) = P(pa_c) · q_c(v_c ∣ pa_c)`. -/
public theorem ConditionalTables.marginal_insert_parents {G : C → Finset C}
    (hG : ∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c)
    (q : ConditionalTables C V ℝ G) (c : C) (w : (c : C) → V c) :
    marginal q.family ∅ w (insert c (G c)) w =
      marginal q.family ∅ w (G c) w * q.table c (w c) w := by
  obtain ⟨rank, hrank⟩ := id hG
  set D := Finset.univ.filter (fun d ↦ rank c < rank d) with hD
  have hmemD : ∀ d, d ∈ D ↔ rank c < rank d := fun d ↦ by simp [hD]
  have hcD : c ∉ D := by rw [hmemD]; exact lt_irrefl _
  have hm : ∀ (s : Finset C) (r' : ℝ),
      HasSum ({v : (c : C) → V c | ∀ d ∈ s, v d = w d}.indicator (q.family ∅ w)) r' →
        marginal q.family ∅ w s w = r' :=
    fun s r' h ↦ (tsum_subtype _ _).trans h.tsum_eq
  set r := marginal q.family (insert c D) w (G c) w
  have hr : HasSum ({v : (c : C) → V c | ∀ d ∈ G c, v d = w d}.indicator
      (q.family (insert c D) w)) r :=
    hasSum_subtype_iff_indicator.mp (q.hasSum_marginal hG (insert c D) w (G c) w)
  have hR : HasSum ({v : (c : C) → V c | ∀ d ∈ G c, v d = w d}.indicator
      (q.family ∅ w)) r := by
    refine hasSum_indicator_of_union hG q (G c) w r (insert c D) ∅ ?_ ?_ ?_ ?_
    · intro e he hec
      have := hrank c e hec
      rcases Finset.mem_insert.mp he with rfl | he
      · omega
      · have := (hmemD e).mp he
        omega
    · intro e _
      exact Finset.notMem_empty e
    · intro e he d _ hd hed
      have h1 := hrank d e hed
      rw [Finset.mem_insert, not_or, hmemD] at hd
      rcases Finset.mem_insert.mp he with rfl | he
      · omega
      · have := (hmemD e).mp he
        omega
    · rwa [Finset.empty_union]
  have hpt : ∀ v, {v : (c : C) → V c | ∀ d ∈ insert c (G c), v d = w d}.indicator
      (q.family D w) v = q.table c (w c) w *
        {v : (c : C) → V c | ∀ d ∈ G c, v d = w d}.indicator (q.family (insert c D) w) v := by
    intro v
    by_cases hpa : ∀ p ∈ G c, v p = w p
    · rw [Set.indicator_of_mem
        (show v ∈ {v : (c : C) → V c | ∀ d ∈ G c, v d = w d} from hpa)]
      by_cases hvc : v c = w c
      · have hmem : v ∈ {v : (c : C) → V c | ∀ d ∈ insert c (G c), v d = w d} := by
          intro d hd
          rcases Finset.mem_insert.mp hd with rfl | hd
          · exact hvc
          · exact hpa d hd
        rw [Set.indicator_of_mem hmem, q.family_eq_table_mul hcD w v hvc]
        congr 1
        rw [q.reads_parents c (v c) v w hpa, hvc]
      · rw [Set.indicator_of_notMem
            (show v ∉ {v : (c : C) → V c | ∀ d ∈ insert c (G c), v d = w d} from
              fun h ↦ hvc (h c (Finset.mem_insert_self c _))),
          q.family_eq_zero_of_mem (Finset.mem_insert_self c D) hvc, mul_zero]
    · rw [Set.indicator_of_notMem
          (show v ∉ {v : (c : C) → V c | ∀ d ∈ insert c (G c), v d = w d} from
            fun h ↦ hpa fun p hp ↦ h p (Finset.mem_insert_of_mem hp)),
        Set.indicator_of_notMem
          (show v ∉ {v : (c : C) → V c | ∀ d ∈ G c, v d = w d} from hpa), mul_zero]
  have hL : HasSum ({v : (c : C) → V c | ∀ d ∈ insert c (G c), v d = w d}.indicator
      (q.family ∅ w)) (q.table c (w c) w * r) := by
    refine hasSum_indicator_of_union hG q (insert c (G c)) w _ D ∅ ?_ ?_ ?_ ?_
    · intro e he hec
      have := (hmemD e).mp he
      rcases Finset.mem_insert.mp hec with rfl | hec
      · omega
      · have := hrank c e hec
        omega
    · intro e _
      exact Finset.notMem_empty e
    · intro e he d _ hd hed
      have := hrank d e hed
      rw [hmemD] at hd he
      omega
    · rw [Finset.empty_union, funext hpt]
      exact hr.mul_left _
  rw [hm _ _ hL, hm _ _ hR, mul_comm]

/-- **Each member of a causal Bayesian network is a probability distribution**,
at discrete variables. -/
public theorem IsCausalBayesNetwork.hasSum_one {G : C → Finset C}
    {P : InterventionalFamily C V ℝ} (h : IsCausalBayesNetwork G P)
    (targets : Finset C) (target : (c : C) → V c) :
    HasSum (P targets target) 1 := by
  obtain ⟨q, rfl⟩ := eq_family_of_isCausalBayesNetwork h
  exact q.hasSum_family h.1 targets target

/--
**Pearl, Property 2 (equation (1.39)), at discrete variables.** *"For all `i` and
for every subset `S` of variables disjoint of `{V_i, PA_i}`, we have
`P_{pa_i, s}(v_i) = P_{pa_i}(v_i)`."* For every family compatible with `G` in
Definition 1.3.1's sense, with values in arbitrary types.
-/
public theorem IsCausalBayesNetwork.marginal_do_parents_union {G : C → Finset C}
    {P : InterventionalFamily C V ℝ} (h : IsCausalBayesNetwork G P) {c : C}
    {S : Finset C} (hc : c ∉ S) (target : (c : C) → V c) :
    marginal P (G c ∪ S) target {c} target = marginal P (G c) target {c} target := by
  obtain ⟨q, rfl⟩ := eq_family_of_isCausalBayesNetwork h
  have h₀ := q.marginal_singleton_do_parents h.1 (extra := ∅) (Finset.notMem_empty c) target
  rw [Finset.union_empty] at h₀
  rw [q.marginal_singleton_do_parents h.1 hc target, h₀]

/--
**Pearl, Property 1 (equation (1.38)), at discrete variables**, multiplied out.
*"For all `i`, `P(v_i ∣ pa_i) = P_{pa_i}(v_i)`"*, as
`P(v_i, pa_i) = P(pa_i) · P_{pa_i}(v_i)`, for every family compatible with `G` in
Definition 1.3.1's sense, with values in arbitrary types.
-/
public theorem IsCausalBayesNetwork.marginal_insert_parents {G : C → Finset C}
    {P : InterventionalFamily C V ℝ} (h : IsCausalBayesNetwork G P) (c : C)
    (w : (c : C) → V c) :
    marginal P ∅ w (insert c (G c)) w =
      marginal P ∅ w (G c) w * marginal P (G c) w {c} w := by
  obtain ⟨q, rfl⟩ := eq_family_of_isCausalBayesNetwork h
  have h₀ := q.marginal_singleton_do_parents h.1 (extra := ∅) (Finset.notMem_empty c) w
  rw [Finset.union_empty] at h₀
  rw [q.marginal_insert_parents h.1 c w, h₀]

end AISafetyAtlas.Causal.Discrete
