module

public import AISafetyAtlas.Sovereignty.Auditability
public import AISafetyAtlas.Compositional.Hyperproperties

/-!
# Cognitive sovereignty as the proposal states it, and what belief change proves

`CogSov` transcribes the boxed predicate of the proposal's §7.4: there is one
defender `D` in the admissible class such that the runs of the implementation
composed with it lie in the relational specification, **and** every observation
of every authorized request in every environment lies inside the authorized
trace language and the required-service language.

Every component is a parameter, and that is deliberate: the definition carries
no content by itself and is not supposed to. What it fixes is the *shape* of
the claim -- that the same `D` must provide the service and satisfy the
authorship condition, and that the authorship condition is a property of a set
of runs and not of one run, which is why `H` has type `Set (Set Run)`. Nothing
here says the relational specification is satisfiable, nor that a constitution
is legitimate; print is explicit that the second is a separate assumption.

That shape already has a name **in this repository**, and **since 2026-09-13
`H` carries it**: `AISafetyAtlas.Compositional.Hyperproperties.Hyperproperty` is
`Set (Set Trace)`, so `H` is that type at `Run` and `runs I D ∈ H` is its
satisfaction test. That module cites Clarkson and Schneider, *Hyperproperties*,
J. Computer Security 18(6):1157-1210, 2010, and carries their Theorem 2; page
1161 of that paper is where the type and the membership test are defined. The
transport is a change of signature and nothing else: `Hyperproperty` is an
abbreviation, so every statement below reads exactly as it did, and what changes
is that the two clusters now name one object.

**What the transport buys, and what it costs.** The paper's page-1167 class of
*subset-closed* hyperproperties is in the tree as
`AISafetyAtlas.Compositional.Hyperproperties.SubsetClosed`, with their Theorem 1
-- every hypersafety hyperproperty is subset-closed -- as
`subsetClosed_of_isHyperSafetyOp`. `cogSov_mono_of_subsetClosed` is what it is
for: **if the relational specification is subset-closed then deleting runs
cannot destroy cognitive sovereignty**, with the same defender.

**Whether `H` ought to be required to carry that closure is still not decided
here**, and `Examples.Sovereignty.CogSov.shrinking_can_destroy_cogSov` is why the
question is real rather than free: at a specification that is *not* subset-closed
-- accept exactly the total run set, and nothing less -- removing runs destroys
cognitive sovereignty outright. Recorded in
`SOURCES-2026-09-09-sovereignty.md`.

## `C4`

Print: *positive learning influence is compatible with cognitive sovereignty*,
so magnitude of belief change is not an authorship test. Two statements carry
that here and neither is about `CogSov`'s satisfiability:

* `cogSov_of_witness` -- a defender meeting both clauses gives `CogSov`, which
  is the only direction print uses;
* `magnitude_does_not_decide_authorship` -- two protected transitions with the
  *same* endorsed belief change, one residual-free and one not. Since the
  observable magnitude is identical, no function of it separates the
  authorized case from the unauthorized one.

The second is the content. `C3`'s `residualFree_iff_factors` is what the first
of the two satisfies, and print's own remark that residual-freeness "permits
large, legitimate changes in beliefs when `e` changes" is the reason the
separation is possible at all.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

/--
**The proposed operational cognitive-sovereignty predicate**, §7.4.

`𝒟` is the admissible defender class, `runs` the set of runs of the
implementation composed with a defender, `H` the relational specification,
`obs` the observations of an authorized request in an environment, `Γ` the
authorized trace language and `L` the required service at a request.
-/
@[expose] public def CogSov {Impl Defender Req Env Run Obs : Type*}
    (𝒟 : Set Defender) (runs : Impl → Defender → Set Run)
    (H : AISafetyAtlas.Compositional.Hyperproperties.Hyperproperty Run)
    (obs : Impl → Defender → Req → Env → Set Obs) (Γ : Set Obs)
    (L : Req → Set Obs) (I : Impl) : Prop :=
  ∃ D ∈ 𝒟, runs I D ∈ H ∧ ∀ r τ, obs I D r τ ⊆ Γ ∩ L r

/-- **One defender that does both jobs establishes it.** This is the only
direction print uses, and it is the definition read forward. -/
public theorem cogSov_of_witness {Impl Defender Req Env Run Obs : Type*}
    {𝒟 : Set Defender} {runs : Impl → Defender → Set Run}
    {H : AISafetyAtlas.Compositional.Hyperproperties.Hyperproperty Run}
    {obs : Impl → Defender → Req → Env → Set Obs} {Γ : Set Obs}
    {L : Req → Set Obs} {I : Impl} {D : Defender} (hD : D ∈ 𝒟)
    (hH : runs I D ∈ H) (hobs : ∀ r τ, obs I D r τ ⊆ Γ ∩ L r) :
    CogSov 𝒟 runs H obs Γ L I :=
  ⟨D, hD, hH, hobs⟩

/-- **And it fails when no admissible defender does.** -/
public theorem not_cogSov {Impl Defender Req Env Run Obs : Type*}
    {𝒟 : Set Defender} {runs : Impl → Defender → Set Run}
    {H : AISafetyAtlas.Compositional.Hyperproperties.Hyperproperty Run}
    {obs : Impl → Defender → Req → Env → Set Obs} {Γ : Set Obs}
    {L : Req → Set Obs} {I : Impl}
    (h : ∀ D ∈ 𝒟, runs I D ∉ H ∨ ∃ r τ, ¬ obs I D r τ ⊆ Γ ∩ L r) :
    ¬ CogSov 𝒟 runs H obs Γ L I := by
  rintro ⟨D, hD, hH, hobs⟩
  rcases h D hD with hbad | ⟨r, τ, hbad⟩
  · exact hbad hH
  · exact hbad (hobs r τ)


/--
**What subset-closure buys, if the specification has it.** When `H` is
subset-closed, deleting runs from the composed system cannot destroy cognitive
sovereignty: the defender that worked before still works.

This is the point of the transport. `H`'s type is
`AISafetyAtlas.Compositional.Hyperproperties.Hyperproperty`, and
`SubsetClosed` is Clarkson and Schneider's class at their page 1167 -- the one
for which refinement transfers. Their Theorem 1, in this tree as
`subsetClosed_of_isHyperSafetyOp`, says every hypersafety specification is in it.
-/
public theorem cogSov_mono_of_subsetClosed {Impl Defender Req Env Run Obs : Type*}
    {𝒟 : Set Defender} {runs runs' : Impl → Defender → Set Run}
    {H : AISafetyAtlas.Compositional.Hyperproperties.Hyperproperty Run}
    {obs : Impl → Defender → Req → Env → Set Obs} {Γ : Set Obs}
    {L : Req → Set Obs} {I : Impl}
    (hsc : AISafetyAtlas.Compositional.Hyperproperties.SubsetClosed H)
    (hsub : ∀ D, runs' I D ⊆ runs I D)
    (h : CogSov 𝒟 runs H obs Γ L I) :
    CogSov 𝒟 runs' H obs Γ L I := by
  obtain ⟨D, hD, hH, hobs⟩ := h
  exact ⟨D, hD, hsc _ hH _ (hsub D), hobs⟩

/--
**`C4`: the size of an authorized belief change decides nothing.**

Two protected transitions that produce exactly the same belief at every
endorsed evidence and every request, one of which depends on nothing else and
one of which does. The endorsed influence is therefore identical -- and can be
maximal, when `g` is onto `S` -- while only the first satisfies `C3`'s
endorsement condition. The two transitions agree at the realised unendorsed
input `u₀`, not at every input: agreeing everywhere would make the second
residual-free too.

So no function of the magnitude of belief change separates the authorized case
from the unauthorized one, which is print's conclusion. Print's other
hypotheses, authenticated requests and intact alternatives, are the two clauses
of `CogSov` and are not what the separation turns on.
-/
public theorem magnitude_does_not_decide_authorship {E J S : Type*}
    (u₀ u₁ : Bool) (hu : u₀ ≠ u₁) (g : E → J → S) (s₁ : S)
    (hs : ∃ e j, g e j ≠ s₁) :
    ∃ F F' : E → J → Bool → S,
      (∀ e j u, F e j u = g e j) ∧ (∀ e j, F' e j u₀ = g e j) ∧
        (∀ e j u u', F e j u = F e j u') ∧
          ¬ ∀ e j u u', F' e j u = F' e j u' := by
  classical
  refine ⟨fun e j _ => g e j, fun e j u => if u = u₀ then g e j else s₁,
    fun _ _ _ => rfl, fun e j => by simp, fun _ _ _ _ => rfl, ?_⟩
  obtain ⟨e, j, hne⟩ := hs
  intro hconst
  have hval := hconst e j u₀ u₁
  simp only [if_neg (Ne.symm hu)] at hval
  exact hne hval

end AISafetyAtlas.Sovereignty
