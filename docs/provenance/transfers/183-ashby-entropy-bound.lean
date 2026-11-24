import AISafetyAtlas.Control.RequisiteVariety

/-!
Ashby (1956, second impression 1957), *An Introduction to Cybernetics*, §11/8,
book p. 208, with the accepted repair (S03-R05). For three variables `D`, `R`,
`E`, each an information source with finitely many values (Shannon's entropy
of a finite set of probabilities, §9/11), if `H_R(E) ≥ H_R(D)` then
`H(D) + H_D(R) ≤ H(R) + H_R(E)` and `H(E) ≥ H(D) + H_D(R) − H(R)`. The cited
theorems are `AISafetyAtlas.Control.entropy_ge_of_condEntropy_ge` and
`AISafetyAtlas.Control.entropy_add_condEntropy_le_of_condEntropy_ge`; they
take any measure that is zero or a probability, finite-range variables, a
slack `K`, and (intermediate line) an arbitrary `E`.

Print's instance is a joint table, rendered as a finite probability space
carrying `D`, `R`, `E` (`print_on` pushes any probability space with
finite-range variables onto the finite range of the triple, E27). Reading (no
ruling settles it): the value types are countable types with measurable
singletons; on a finite sample space each variable takes finitely many of
their values, so this is the finite table, not a widening.

The map, at a probability measure `μ` and slack `K`, with
`a = max (-K) 0` and `b = max K 0` (`b - a = K`):
* final line (`phiFinal`, `H_final`, `C_final`): on `Ω × W` under `μ ⊗ ν`,
  with `W` a pair of finite noise alphabets of entropies `a` and `b`
  (`exists_measureEntropy_eq`), the variables `(D, N₁)`, `R`, `(E, N₂)`.
  Independence adds `a` to `H(D)` and `H(D, R)`, and `b` to `H(E)` and
  `H(E, R)`, so print's premise is the Lean premise and print's final line
  gives the Lean bound.
* intermediate line (`phiInter`, `H_inter`, `C_inter`; arbitrary `E`, read
  only through `H[E | R]`): the same, with `E` replaced by an independent
  noise variable of entropy `H[E | R] + b`. This map does not translate `E`
  itself, only that scalar; at a finite-range measurable `E` the final-line
  map applies instead.
At the zero measure every entropy vanishes, the premise forces `K ≥ 0`, and
both Lean bounds hold without print; that case is not a print instance.

The two cited theorems have different instance sets, so each has its own map.
`lean_of_print` takes print at two universe instantiations (the intermediate
line's noise alphabet is in `Type`). The forward direction is omitted: a
finite table is a Lean instance at `K = 0` after `Fin`-coding, routine but
long.

Checked: `lake env lean docs/provenance/transfers/183-ashby-entropy-bound.lean`
-/

namespace Transfer183

open MeasureTheory ProbabilityTheory Real AISafetyAtlas.Control

universe uO u1 u2 u3 uΩ uD uR uE

def PrintStatement : Prop :=
  ∀ (Ω : Type uO) (D : Type u1) (R : Type u2) (E : Type u3) [MeasurableSpace Ω] [Finite Ω]
    [MeasurableSpace D] [MeasurableSingletonClass D] [Countable D]
    [MeasurableSpace R] [MeasurableSingletonClass R] [Countable R]
    [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Dv : Ω → D) (Rv : Ω → R) (Ev : Ω → E),
    Measurable Dv → Measurable Rv → Measurable Ev → H[Dv | Rv ; μ] ≤ H[Ev | Rv ; μ] →
      H[Dv ; μ] + H[Rv | Dv ; μ] ≤ H[Rv ; μ] + H[Ev | Rv ; μ] ∧
        H[Dv ; μ] + H[Rv | Dv ; μ] - H[Rv ; μ] ≤ H[Ev ; μ]

def LeanStatement : Prop :=
  ∀ (Ω : Type uΩ) (D : Type uD) (R : Type uR) (E : Type uE) [MeasurableSpace Ω]
    [MeasurableSpace D] [MeasurableSingletonClass D] [Countable D]
    [MeasurableSpace R] [MeasurableSingletonClass R] [Countable R] [MeasurableSpace E]
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (Dv : Ω → D) (Rv : Ω → R) (Ev : Ω → E),
    Measurable Dv → Measurable Rv → ∀ [FiniteRange Dv] [FiniteRange Rv] (K : ℝ),
    H[Dv | Rv ; μ] - K ≤ H[Ev | Rv ; μ] →
      H[Dv ; μ] + H[Rv | Dv ; μ] - K ≤ H[Rv ; μ] + H[Ev | Rv ; μ] ∧
      (∀ [MeasurableSingletonClass E] [Countable E], Measurable Ev → FiniteRange Ev →
        H[Dv ; μ] + H[Rv | Dv ; μ] - K - H[Rv ; μ] ≤ H[Ev ; μ])

theorem ident_range {P : Type*} [MeasurableSpace P] {T : Type*} [MeasurableSpace T] {Ψ : P → T}
    (hΨ : Measurable Ψ) (m : Measure P) {S : Type*} [MeasurableSpace S] (f : Set.range Ψ → S)
    (hf : Measurable f) :
    IdentDistrib f (f ∘ Set.rangeFactorization Ψ) (m.map (Set.rangeFactorization Ψ)) m :=
  ⟨hf.aemeasurable, (hf.comp hΨ.subtype_mk).aemeasurable, Measure.map_map hf hΨ.subtype_mk⟩

/-- Print on any probability space with finite-range variables, through the push to the
finite range of the triple (E27). -/
theorem print_on (hp : PrintStatement.{max u1 u2 u3, u1, u2, u3}) {P : Type uΩ}
    [MeasurableSpace P] {D : Type u1} {R : Type u2} {E : Type u3}
    [MeasurableSpace D] [MeasurableSingletonClass D] [Countable D]
    [MeasurableSpace R] [MeasurableSingletonClass R] [Countable R]
    [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
    (m : Measure P) [IsProbabilityMeasure m] {X : P → D} {Y : P → R} {Z : P → E}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] (h : H[X | Y ; m] ≤ H[Z | Y ; m]) :
    H[X ; m] + H[Y | X ; m] ≤ H[Y ; m] + H[Z | Y ; m] ∧
      H[X ; m] + H[Y | X ; m] - H[Y ; m] ≤ H[Z ; m] := by
  let Ψ : P → D × R × E := fun p ↦ (X p, Y p, Z p)
  have hΨ : Measurable Ψ := hX.prodMk (hY.prodMk hZ)
  have hrf : Measurable (Set.rangeFactorization Ψ) := hΨ.subtype_mk
  have hfin : (Set.range Ψ).Finite :=
    ((FiniteRange.finite (X := X)).prod ((FiniteRange.finite (X := Y)).prod
      (FiniteRange.finite (X := Z)))).subset (by
        rintro _ ⟨p, rfl⟩; exact ⟨⟨p, rfl⟩, ⟨p, rfl⟩, ⟨p, rfl⟩⟩)
  have : Finite (Set.range Ψ) := hfin.to_subtype
  let μ' := m.map (Set.rangeFactorization Ψ)
  have : IsProbabilityMeasure μ' := Measure.isProbabilityMeasure_map hrf.aemeasurable
  let X' : Set.range Ψ → D := fun x ↦ x.1.1
  let Y' : Set.range Ψ → R := fun x ↦ x.1.2.1
  let Z' : Set.range Ψ → E := fun x ↦ x.1.2.2
  have hX' : Measurable X' := measurable_fst.comp measurable_subtype_coe
  have hY' : Measurable Y' := (measurable_fst.comp measurable_snd).comp measurable_subtype_coe
  have hZ' : Measurable Z' := (measurable_snd.comp measurable_snd).comp measurable_subtype_coe
  have : FiniteRange X' := ⟨Set.finite_range _⟩
  have : FiniteRange Y' := ⟨Set.finite_range _⟩
  have : FiniteRange Z' := ⟨Set.finite_range _⟩
  have eX : H[X' ; μ'] = H[X ; m] := (ident_range hΨ m X' hX').entropy_congr
  have eY : H[Y' ; μ'] = H[Y ; m] := (ident_range hΨ m Y' hY').entropy_congr
  have eZ : H[Z' ; μ'] = H[Z ; m] := (ident_range hΨ m Z' hZ').entropy_congr
  have cXY : H[X' | Y' ; μ'] = H[X | Y ; m] :=
    IdentDistrib.condEntropy_eq hX' hY' hX hY (ident_range hΨ m _ (hX'.prodMk hY'))
  have cYX : H[Y' | X' ; μ'] = H[Y | X ; m] :=
    IdentDistrib.condEntropy_eq hY' hX' hY hX (ident_range hΨ m _ (hY'.prodMk hX'))
  have cZY : H[Z' | Y' ; μ'] = H[Z | Y ; m] :=
    IdentDistrib.condEntropy_eq hZ' hY' hZ hY (ident_range hΨ m _ (hZ'.prodMk hY'))
  have := hp (Set.range Ψ) D R E μ' X' Y' Z' hX' hY' hZ' (by rw [cXY, cZY]; exact h)
  rwa [eX, eY, eZ, cYX, cZY] at this

/-- Noise alphabet size for a prescribed entropy. -/
noncomputable def size (h : ℝ) : ℕ := ⌈exp h⌉₊

theorem le_log_size (h : ℝ) : h ≤ log (size h + 1) := by
  have h1 : exp h ≤ (size h : ℝ) + 1 := by unfold size; linarith [Nat.le_ceil (exp h)]
  calc h = log (exp h) := (log_exp h).symm
    _ ≤ _ := log_le_log (exp_pos h) h1

/-- A law on a finite alphabet with entropy `h ≥ 0`. -/
noncomputable def noise (h : ℝ) (h0 : 0 ≤ h) : Measure (Fin (size h + 1)) :=
  (exists_measureEntropy_eq (size h) h0 (le_log_size h)).choose

instance (h : ℝ) (h0 : 0 ≤ h) : IsProbabilityMeasure (noise h h0) :=
  (exists_measureEntropy_eq (size h) h0 (le_log_size h)).choose_spec.1

theorem noise_entropy (h : ℝ) (h0 : 0 ≤ h) : Hm[noise h h0] = h :=
  (exists_measureEntropy_eq (size h) h0 (le_log_size h)).choose_spec.2

section product

variable {Ω : Type uΩ} [MeasurableSpace Ω] {W : Type*} [MeasurableSpace W]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure W) [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] in
theorem ent_fst {S : Type*} [MeasurableSpace S] {X : Ω → S} (hX : Measurable X) :
    H[X ∘ Prod.fst ; μ.prod ν] = H[X ; μ] := by
  rw [entropy_def, entropy_def, ← Measure.map_map hX measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul]

theorem ent_snd {S : Type*} [MeasurableSpace S] {N : W → S} (hN : Measurable N) :
    H[N ∘ Prod.snd ; μ.prod ν] = H[N ; ν] := by
  rw [entropy_def, entropy_def, ← Measure.map_map hN measurable_snd, Measure.map_snd_prod,
    measure_univ, one_smul]

theorem ent_pair {S T : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] {X : Ω → S} {N : W → T}
    (hX : Measurable X) (hN : Measurable N) [FiniteRange X] [FiniteRange N] :
    H[fun p : Ω × W ↦ (X p.1, N p.2) ; μ.prod ν] = H[X ; μ] + H[N ; ν] := by
  have hi : IndepFun (X ∘ Prod.fst) (N ∘ Prod.snd) (μ.prod ν) := indepFun_fst_snd.comp hX hN
  have h := hi.entropy_pair_eq_add (hX.comp measurable_fst) (hN.comp measurable_snd)
  rw [ent_fst μ ν hX, ent_snd μ ν hN] at h
  exact h

/-- Appending independent noise to the first coordinate of a pair. -/
theorem ent_pair3 {S T U : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U] {X : Ω → S} {Y : Ω → U}
    {N : W → T} (hX : Measurable X) (hY : Measurable Y) (hN : Measurable N)
    [FiniteRange X] [FiniteRange Y] [FiniteRange N] :
    H[fun p : Ω × W ↦ ((X p.1, N p.2), Y p.1) ; μ.prod ν] = H[⟨X, Y⟩ ; μ] + H[N ; ν] := by
  let g : (S × U) × T → (S × T) × U := fun q ↦ ((q.1.1, q.2), q.1.2)
  have hg : Function.Injective g := fun q q' h ↦ by
    simp only [g, Prod.mk.injEq] at h; ext <;> simp [h]
  rw [← ent_pair μ ν (hX.prodMk hY) hN]
  exact entropy_comp_of_injective _ ((hX.prodMk hY).comp measurable_fst |>.prodMk
    (hN.comp measurable_snd)) g hg

end product

theorem fr_pair {P S T : Type*} (f : P → S) (g : P → T) [FiniteRange f] [FiniteRange g] :
    FiniteRange (fun p ↦ (f p, g p)) := inferInstance

theorem fr_fin {W : Type*} {n : ℕ} (f : W → Fin n) : FiniteRange f := inferInstance

theorem max_sub (K : ℝ) : max K 0 - max (-K) 0 = K := by
  rcases le_total K 0 with h | h <;> simp [h]

/-- The noise of the map: entropy `max (-K) 0` for `D`, `max K 0` for `E`. -/
noncomputable abbrev noiseD (K : ℝ) := noise (max (-K) 0) (le_max_right _ _)
noncomputable abbrev noiseE (K : ℝ) := noise (max K 0) (le_max_right _ _)

section map

variable {Ω : Type uΩ} [MeasurableSpace Ω] {D : Type uD} {R : Type uR} {E : Type uE}
  [MeasurableSpace D] [MeasurableSingletonClass D] [Countable D]
  [MeasurableSpace R] [MeasurableSingletonClass R] [Countable R] [MeasurableSpace E]
  {a b : ℕ}

/-- The variables of the map on `Ω × (Fin a × Fin b)`: `(D, N₁)`, `R`, and `(E, N₂)` (final
line) or `N₂` (intermediate line). -/
def XD (Dv : Ω → D) : Ω × (Fin a × Fin b) → D × Fin a := fun p ↦ (Dv p.1, p.2.1)
def YR (Rv : Ω → R) : Ω × (Fin a × Fin b) → R := fun p ↦ Rv p.1
def ZE (Ev : Ω → E) : Ω × (Fin a × Fin b) → E × Fin b := fun p ↦ (Ev p.1, p.2.2)
def ZN : Ω × (Fin a × Fin b) → Fin b := fun p ↦ p.2.2

instance (Dv : Ω → D) [FiniteRange Dv] : FiniteRange (XD (a := a) (b := b) Dv) :=
  fr_pair (Dv ∘ Prod.fst) (fun p : Ω × (Fin a × Fin b) ↦ p.2.1)
instance (Rv : Ω → R) [FiniteRange Rv] : FiniteRange (YR (a := a) (b := b) Rv) :=
  inferInstanceAs (FiniteRange (Rv ∘ Prod.fst))
instance (Ev : Ω → E) [FiniteRange Ev] : FiniteRange (ZE (a := a) (b := b) Ev) :=
  fr_pair (Ev ∘ Prod.fst) (fun p : Ω × (Fin a × Fin b) ↦ p.2.2)

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν₁ : Measure (Fin a)) (ν₂ : Measure (Fin b))
  [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] {Dv : Ω → D} {Rv : Ω → R} {Ev : Ω → E}

theorem vals_D (hD : Measurable Dv) (hR : Measurable Rv) [FiniteRange Dv] [FiniteRange Rv] :
    H[XD Dv ; μ.prod (ν₁.prod ν₂)] = H[Dv ; μ] + Hm[ν₁] ∧
      H[⟨XD Dv, YR Rv⟩ ; μ.prod (ν₁.prod ν₂)] = H[⟨Dv, Rv⟩ ; μ] + Hm[ν₁] ∧
      H[YR (a := a) (b := b) Rv ; μ.prod (ν₁.prod ν₂)] = H[Rv ; μ] := by
  have : FiniteRange (Prod.fst : Fin a × Fin b → Fin a) := fr_fin _
  have mf : Measurable (Prod.fst : Fin a × Fin b → Fin a) := measurable_fst
  have n : H[(Prod.fst : Fin a × Fin b → Fin a) ; ν₁.prod ν₂] = Hm[ν₁] := by
    rw [entropy_def, Measure.map_fst_prod, measure_univ, one_smul]
  exact ⟨(ent_pair μ (ν₁.prod ν₂) hD mf).trans (congrArg _ n),
    (ent_pair3 μ (ν₁.prod ν₂) hD hR mf).trans (congrArg _ n), ent_fst μ (ν₁.prod ν₂) hR⟩

theorem vals_E [MeasurableSingletonClass E] [Countable E] (hE : Measurable Ev)
    (hR : Measurable Rv) [FiniteRange Ev] [FiniteRange Rv] :
    H[ZE Ev ; μ.prod (ν₁.prod ν₂)] = H[Ev ; μ] + Hm[ν₂] ∧
      H[⟨ZE Ev, YR Rv⟩ ; μ.prod (ν₁.prod ν₂)] = H[⟨Ev, Rv⟩ ; μ] + Hm[ν₂] := by
  have : FiniteRange (Prod.snd : Fin a × Fin b → Fin b) := fr_fin _
  have ms : Measurable (Prod.snd : Fin a × Fin b → Fin b) := measurable_snd
  have n : H[(Prod.snd : Fin a × Fin b → Fin b) ; ν₁.prod ν₂] = Hm[ν₂] := by
    rw [entropy_def, Measure.map_snd_prod, measure_univ, one_smul]
  exact ⟨(ent_pair μ (ν₁.prod ν₂) hE ms).trans (congrArg _ n),
    (ent_pair3 μ (ν₁.prod ν₂) hE hR ms).trans (congrArg _ n)⟩

theorem vals_N (hR : Measurable Rv) [FiniteRange Rv] :
    H[⟨YR Rv, ZN⟩ ; μ.prod (ν₁.prod ν₂)] = H[Rv ; μ] + Hm[ν₂] := by
  have : FiniteRange (Prod.snd : Fin a × Fin b → Fin b) := fr_fin _
  have ms : Measurable (Prod.snd : Fin a × Fin b → Fin b) := measurable_snd
  have n : H[(Prod.snd : Fin a × Fin b → Fin b) ; ν₁.prod ν₂] = Hm[ν₂] := by
    rw [entropy_def, Measure.map_snd_prod, measure_univ, one_smul]
  exact (ent_pair μ (ν₁.prod ν₂) hR ms).trans (congrArg _ n)

omit [MeasurableSingletonClass D] [Countable D] [MeasurableSingletonClass R] [Countable R] in
theorem meas (hD : Measurable Dv) (hR : Measurable Rv) :
    Measurable (XD (a := a) (b := b) Dv) ∧ Measurable (YR (a := a) (b := b) Rv) :=
  ⟨(hD.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd), hR.comp measurable_fst⟩

/-- Print's terms at the map, in joint entropies. -/
theorem print_terms {S T U : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    [Countable S] [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U] {P : Type*}
    [MeasurableSpace P] (m : Measure P) [IsProbabilityMeasure m] {X : P → S} {Y : P → T}
    {Z : P → U} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X]
    [FiniteRange Y] [FiniteRange Z] :
    H[X | Y ; m] = H[⟨X, Y⟩ ; m] - H[Y ; m] ∧ H[Y | X ; m] = H[⟨X, Y⟩ ; m] - H[X ; m] ∧
      H[Z | Y ; m] = H[⟨Z, Y⟩ ; m] - H[Y ; m] :=
  ⟨chain_rule'' m hX hY, (chain_rule'' m hY hX).trans (by rw [entropy_comm hY hX]),
    chain_rule'' m hZ hY⟩

/-- The map for the final line: noise of entropies `max (-K) 0` and `max K 0`. -/
noncomputable abbrev phiFinal (K : ℝ) := (noiseD K).prod (noiseE K)

/-- The intermediate line's `E` side: noise of entropy `H[E | R] + max K 0`. -/
noncomputable abbrev noiseI (Ev : Ω → E) (Rv : Ω → R) (K : ℝ) :=
  noise (H[Ev | Rv ; μ] + max K 0) (add_nonneg (condEntropy_nonneg _ _ _) (le_max_right _ _))

/-- The map for the intermediate line. -/
noncomputable abbrev phiInter (Ev : Ω → E) (Rv : Ω → R) (K : ℝ) :=
  (noiseD K).prod (noiseI μ Ev Rv K)

theorem H_final [MeasurableSingletonClass E] [Countable E] (hD : Measurable Dv)
    (hR : Measurable Rv) (hE : Measurable Ev) [FiniteRange Dv] [FiniteRange Rv] [FiniteRange Ev]
    (K : ℝ) (hkey : H[Dv | Rv ; μ] - K ≤ H[Ev | Rv ; μ]) :
    H[XD Dv | YR Rv ; μ.prod (phiFinal K)] ≤ H[ZE Ev | YR Rv ; μ.prod (phiFinal K)] := by
  obtain ⟨hX, hY⟩ := meas (a := size (max (-K) 0) + 1) (b := size (max K 0) + 1) hD hR
  have hZ : Measurable (ZE (a := size (max (-K) 0) + 1) (b := size (max K 0) + 1) Ev) :=
    (hE.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  obtain ⟨-, vXY, vY⟩ := vals_D μ (noiseD K) (noiseE K) hD hR
  obtain ⟨-, vZY⟩ := vals_E μ (noiseD K) (noiseE K) hE hR
  obtain ⟨c1, -, c3⟩ := print_terms (μ.prod (phiFinal K)) hX hY hZ
  rw [c1, c3]
  rw [vXY, vY, vZY, noise_entropy, noise_entropy, chain_rule'' μ hD hR] at *
  rw [chain_rule'' μ hE hR] at hkey
  linarith [max_sub K]

theorem C_final [MeasurableSingletonClass E] [Countable E] (hD : Measurable Dv)
    (hR : Measurable Rv) (hE : Measurable Ev) [FiniteRange Dv] [FiniteRange Rv] [FiniteRange Ev]
    (K : ℝ) (hc : H[XD Dv ; μ.prod (phiFinal K)] + H[YR Rv | XD Dv ; μ.prod (phiFinal K)] -
      H[YR Rv ; μ.prod (phiFinal K)] ≤ H[ZE Ev ; μ.prod (phiFinal K)]) :
    H[Dv ; μ] + H[Rv | Dv ; μ] - K - H[Rv ; μ] ≤ H[Ev ; μ] := by
  obtain ⟨hX, hY⟩ := meas (a := size (max (-K) 0) + 1) (b := size (max K 0) + 1) hD hR
  obtain ⟨vX, vXY, vY⟩ := vals_D μ (noiseD K) (noiseE K) hD hR
  obtain ⟨vZ, -⟩ := vals_E μ (noiseD K) (noiseE K) hE hR
  obtain ⟨-, c2, -⟩ := print_terms (μ.prod (phiFinal K)) hX hY hY
  rw [c2, vX, vXY, vY, vZ, noise_entropy, noise_entropy] at hc
  rw [chain_rule'' μ hR hD, entropy_comm hR hD]
  linarith [max_sub K]

theorem H_inter (hD : Measurable Dv) (hR : Measurable Rv) [FiniteRange Dv] [FiniteRange Rv]
    (K : ℝ) (hkey : H[Dv | Rv ; μ] - K ≤ H[Ev | Rv ; μ]) :
    H[XD Dv | YR Rv ; μ.prod (phiInter μ Ev Rv K)] ≤
      H[ZN | YR Rv ; μ.prod (phiInter μ Ev Rv K)] := by
  obtain ⟨hX, hY⟩ := meas (a := size (max (-K) 0) + 1)
    (b := size (H[Ev | Rv ; μ] + max K 0) + 1) hD hR
  have hZ : Measurable (ZN (Ω := Ω) (a := size (max (-K) 0) + 1)
    (b := size (H[Ev | Rv ; μ] + max K 0) + 1)) := measurable_snd.comp measurable_snd
  obtain ⟨-, vXY, vY⟩ := vals_D μ (noiseD K) (noiseI μ Ev Rv K) hD hR
  have vYZ := vals_N μ (noiseD K) (noiseI μ Ev Rv K) hR
  obtain ⟨c1, -, c3⟩ := print_terms (μ.prod (phiInter μ Ev Rv K)) hX hY hZ
  rw [c1, c3, entropy_comm hZ hY]
  rw [vXY, vY, vYZ, noise_entropy, noise_entropy]
  rw [chain_rule'' μ hD hR] at hkey
  linarith [max_sub K]

theorem C_inter (hD : Measurable Dv) (hR : Measurable Rv) [FiniteRange Dv] [FiniteRange Rv]
    (K : ℝ) (hc : H[XD Dv ; μ.prod (phiInter μ Ev Rv K)] +
      H[YR Rv | XD Dv ; μ.prod (phiInter μ Ev Rv K)] ≤ H[YR Rv ; μ.prod (phiInter μ Ev Rv K)] +
      H[ZN | YR Rv ; μ.prod (phiInter μ Ev Rv K)]) :
    H[Dv ; μ] + H[Rv | Dv ; μ] - K ≤ H[Rv ; μ] + H[Ev | Rv ; μ] := by
  obtain ⟨hX, hY⟩ := meas (a := size (max (-K) 0) + 1)
    (b := size (H[Ev | Rv ; μ] + max K 0) + 1) hD hR
  have hZ : Measurable (ZN (Ω := Ω) (a := size (max (-K) 0) + 1)
    (b := size (H[Ev | Rv ; μ] + max K 0) + 1)) := measurable_snd.comp measurable_snd
  obtain ⟨vX, vXY, vY⟩ := vals_D μ (noiseD K) (noiseI μ Ev Rv K) hD hR
  have vYZ := vals_N μ (noiseD K) (noiseI μ Ev Rv K) hR
  obtain ⟨-, c2, c3⟩ := print_terms (μ.prod (phiInter μ Ev Rv K)) hX hY hZ
  rw [c2, c3, entropy_comm hZ hY] at hc
  rw [vX, vXY, vY, vYZ, noise_entropy, noise_entropy] at hc
  rw [chain_rule'' μ hR hD, entropy_comm hR hD]
  linarith [max_sub K]

end map

theorem lean_of_print (hp : PrintStatement.{max uD uR uE, uD, uR, uE})
    (hp' : PrintStatement.{max uD uR, uD, uR, 0}) : LeanStatement.{uΩ, uD, uR, uE} := by
  intro Ω D R E _ _ _ _ _ _ _ _ μ _ Dv Rv Ev hD hR _ _ K hkey
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | _
  · simp only [condEntropy_zero_measure, entropy_zero_measure] at hkey ⊢
    exact ⟨by linarith, fun _ _ ↦ by linarith⟩
  refine ⟨?_, fun hE hEf ↦ ?_⟩
  · -- the intermediate line, through print's intermediate line at `phiInter`
    let a := size (max (-K) 0) + 1
    let b := size (H[Ev | Rv ; μ] + max K 0) + 1
    obtain ⟨hX, hY⟩ := meas (a := a) (b := b) hD hR
    have hZ : Measurable (ZN (Ω := Ω) (a := a) (b := b)) := measurable_snd.comp measurable_snd
    exact C_inter μ hD hR K (print_on hp' _ hX hY hZ (H_inter μ hD hR K hkey)).1
  · -- the final line, through print's final line at `phiFinal`
    have := hEf
    let a := size (max (-K) 0) + 1
    let b := size (max K 0) + 1
    obtain ⟨hX, hY⟩ := meas (a := a) (b := b) hD hR
    have hZ : Measurable (ZE (a := a) (b := b) Ev) :=
      (hE.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
    exact C_final μ hD hR hE K (print_on hp _ hX hY hZ (H_final μ hD hR hE K hkey)).2

end Transfer183
