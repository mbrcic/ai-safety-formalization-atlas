module

public import AISafetyAtlas.Explainability

/-!
# Two collinear features, and no ranking that survives them

`attribution_impossibility_weak` says that under the Rashomon property, a
ranking that is faithful in both directions and antisymmetric cannot relate two
features of the same group either way. Nothing had run it, so the Rashomon
hypothesis had never been met and a reader could not tell whether the
impossibility bites anywhere.

It bites at two features. `attr` gives the first all the weight on one model and
the second all the weight on the other, which is exactly what Rashomon asks for:
within a group, models exist ranking two features oppositely.

**The conclusion is stated as a non-existence rather than applied at a ranking,
and that is deliberate.** The three hypotheses are jointly unsatisfiable here —
faithfulness in both directions forces the ranking to relate the pair both ways,
which antisymmetry forbids — so any ranking supplied to the theorem would be one
that does not exist. `no_faithful_antisymmetric_ranking` is the honest reading:
at this attribution, no such ranking is available at all. That is the
impossibility, rather than a consequence drawn inside it.
-/

namespace AISafetyAtlas.Examples.Explainability

open AISafetyAtlas.Explainability

/-- Two features in one collinearity group. An `abbrev` so that
`twoFeatures.P` reduces and `Fin twoFeatures.P` accepts numerals. -/
public abbrev twoFeatures : FeatureIndex where
  P := 2
  L := 1
  hP := by norm_num
  groupOf := fun _ => 0

/-- Each model puts all the attribution on one of the two features: the first on
the model `true`, the second on the model `false`. -/
public abbrev attr : Fin twoFeatures.P → Bool → ℝ :=
  fun j f => if f then (if j.val = 0 then 1 else 0) else (if j.val = 0 then 0 else 1)

/-- **The Rashomon property holds**: within the group, two models rank the two
features oppositely. This is the hypothesis nothing had met. -/
public theorem rashomon_twoFeatures : RashomonProperty twoFeatures Bool attr := by
  intro l j k hj hk hjk
  have hne : j.val ≠ k.val := fun hc => hjk (Fin.ext hc)
  have hjlt : j.val < 2 := j.isLt
  have hklt : k.val < 2 := k.isLt
  have hj2 : j.val = 0 ∨ j.val = 1 := by omega
  have hk2 : k.val = 0 ∨ k.val = 1 := by omega
  refine ⟨decide (j.val = 0), decide (k.val = 0), ?_, ?_⟩ <;>
    rcases hj2 with h1 | h1 <;> rcases hk2 with h2 | h2 <;>
      simp [attr, h1, h2] at hne ⊢

/--
**So no faithful, antisymmetric ranking of the two features exists.**

The weak impossibility says such a ranking must leave the pair unrelated; the
Rashomon witness then forces it to relate them. Both cannot hold, and the
conclusion is that the ranking does not exist — which is what the theorem is
for.

Written with its full name: the vendored `Upstream.Attribution` carries an
`attribution_impossibility_weak` too, so a bare use of that leaf is evidence for
both declarations and therefore for neither.
-/
public theorem no_faithful_antisymmetric_ranking :
    ¬ ∃ ranking : Fin twoFeatures.P → Fin twoFeatures.P → Prop,
        (∀ f : Bool, attr 0 f > attr 1 f → ranking 0 1) ∧
        (∀ f : Bool, attr 1 f > attr 0 f → ranking 1 0) ∧
        ¬ (ranking 0 1 ∧ ranking 1 0) := by
  rintro ⟨ranking, hjk, hkj, hanti⟩
  have hconc := AISafetyAtlas.Explainability.attribution_impossibility_weak
    twoFeatures Bool attr
    rashomon_twoFeatures 0 0 1
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    (by decide)
    ranking hjk hkj hanti
  exact hconc (Or.inl (hjk true (by norm_num [attr])))

end AISafetyAtlas.Examples.Explainability
