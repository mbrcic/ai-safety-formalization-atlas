module

public import AISafetyAtlas.Preference
public import AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.Properties
public import Mathlib.Computability.Primrec.List

/-!
# Simplicity does not break the planner/reward tie

## Statement intent

- **Objects.** Behaviours and rewards as bit strings
  (`Kolmogorov.BitString = List Bool`), and plain Kolmogorov complexity
  `Kolmogorov.plainK` relative to an optimal conditional decompressor `U`.
- **Assumptions.** `U` is optimal conditional (`isOptimalConditional`), the same
  hypothesis the vendored Chaitin development uses. The reward is fixed first;
  the constant is then uniform in the behaviour.
- **Quantifier order.** Constants are chosen before behaviours: there *exists*
  a constant such that for *every* behaviour the bound holds. Constants never
  depend on the behaviour, which is what makes the statements bite.
- **Conclusion.** Both bounds, **for one canonical encoding only**. *Lower*
  (`explanation_at_least_behaviour`): the behaviour is computably recoverable
  from `encodeExplanation r b`, so *that string* is not more than a constant
  simpler than the behaviour. It quantifies over the manufactured strings
  `encodeExplanation r b`, **not** over arbitrary planner/reward pairs compatible
  with `b`. *Upper*
  (`degenerate_explanation_cheap`): the degenerate explanation is at most a
  constant more complex than the behaviour. Together
  (`explanation_complexity_eq_behaviour`) the degenerate explanation sits within
  additive constants of the behaviour's own complexity. It does **not** follow
  that it is within a constant of the minimum over all compatible explanations:
  there is no planner type, no compatibility predicate and no minimum over
  explanations in this module, so that stronger reading is unproved here.
- **Difference from the source.** Armstrong and Mindermann, §5.1, argue that
  "the complexity of `π̇` is close to a lower bound on any pair compatible with
  it" via the evaluation map `(p, R) ↦ p(R)`, and that "degenerate decompositions
  are themselves close to this bound"; Proposition 7 combines these. Here the
  evaluation map is realised concretely as `decodeBehaviour` on a
  self-delimiting encoding, and the source's framework of `c`-reasonable
  languages and "comparable complexity" is replaced by plain additive constants
  over `Kolmogorov.plainK`. Crucially the source applies evaluation
  `(p, R) ↦ p(R)` to *every* compatible pair, whereas `decodeBehaviour` inverts
  one fixed encoding, so the lower bound here is strictly narrower than the
  source's. Only the degenerate pair `(p_π̇, 0)` is treated. The quantified-over-
  all-compatible-pairs statement lives in
  `AISafetyAtlas.Preference.ReasonableLanguage.policy_le_of_compatible`, over an
  abstract complexity measure rather than `plainK`.

## Explicit non-claims

- **Not** a claim that no prior can distinguish the pairs — only that a prior
  built from plain Kolmogorov complexity cannot, up to an additive constant.
- **Not** a treatment of the source's anti-rational pair `(-p_g, -R_π̇)` or of
  its regret analysis.
- **Not** a lower bound over arbitrary explanations. It is a bi-Lipschitz fact
  about one canonical pairing encoding.
- **Not** the formal core of the source's Proposition 7, which quantifies over
  all compatible pairs; see `Reasonable.lean` for that.
- **Not** a statement about resource-bounded or computable-in-practice priors;
  the source's Appendix A discusses those separately.

Survey row: **BY-011**. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Preference

open Kolmogorov

/--
A self-delimiting encoding of the degenerate explanation of behaviour `b` under
a fixed reward `r`: the length of `b` in unary, a `false` marker, then `b`, then
`r`. The degenerate planner is the one that ignores its reward and returns `b`,
so `b` together with `r` is exactly the data of that explanation.
-/
@[expose] public def encodeExplanation (r b : BitString) : BitString :=
  (b.map fun _ => true) ++ (false :: (b ++ r))

/-- The encoding is computable in the behaviour, for each fixed reward. -/
public theorem computable_encodeExplanation (r : BitString) :
    Computable (encodeExplanation r) := by
  unfold encodeExplanation
  refine Primrec.to_comp ?_
  refine Primrec₂.comp Primrec.list_append
    (Primrec.list_map Primrec.id (Primrec₂.const true)) ?_
  exact Primrec₂.comp Primrec.list_cons (Primrec.const false)
    (Primrec₂.comp Primrec.list_append Primrec.id (Primrec.const r))

/--
The encoding genuinely carries the behaviour: distinct behaviours receive
distinct encodings. Without this the complexity bound below would be vacuous,
since a constant encoding trivially satisfies it.
-/
public theorem encodeExplanation_injective (r : BitString) :
    Function.Injective (encodeExplanation r) := by
  intro b₁ b₂ h
  have hlen : b₁.length = b₂.length := by
    have := congrArg List.length h
    simp only [encodeExplanation, List.length_append, List.length_map,
      List.length_cons] at this
    omega
  have hpre : (b₁.map fun _ => true) = (b₂.map fun _ => true) := by
    simp [List.map_const', hlen]
  unfold encodeExplanation at h
  rw [hpre] at h
  have h2 : (false :: (b₁ ++ r)) = (false :: (b₂ ++ r)) := List.append_cancel_left h
  have h3 : b₁ ++ r = b₂ ++ r := by simpa using h2
  exact List.append_cancel_right h3

/--
Recover the behaviour from its encoded degenerate explanation: read the unary
length prefix, drop it and the marker, then take that many bits. This is the
encoded form of the source's evaluation map `(p, R) ↦ p(R)`.
-/
@[expose] public def decodeBehaviour (x : BitString) : BitString :=
  ((x.dropWhile id).tail).take ((x.takeWhile id).length)

private theorem takeWhile_encode (r b : BitString) :
    (encodeExplanation r b).takeWhile id = b.map fun _ => true := by
  unfold encodeExplanation
  induction b with
  | nil => simp
  | cons a t ih => simp

private theorem dropWhile_encode (r b : BitString) :
    (encodeExplanation r b).dropWhile id = false :: (b ++ r) := by
  unfold encodeExplanation
  induction b with
  | nil => simp
  | cons a t ih => simp

/-- The decoder inverts the encoding. -/
public theorem decodeBehaviour_encodeExplanation (r b : BitString) :
    decodeBehaviour (encodeExplanation r b) = b := by
  unfold decodeBehaviour
  rw [takeWhile_encode, dropWhile_encode]
  simp

/-- The decoder is computable. -/
public theorem computable_decodeBehaviour : Computable decodeBehaviour := by
  unfold decodeBehaviour
  refine Primrec.to_comp ?_
  exact Primrec₂.comp Primrec.list_take
    (Primrec.list_length.comp (Primrec.list_takeWhile Primrec.id))
    (Primrec.list_tail.comp (Primrec.list_dropWhile Primrec.id))

/--
**Lower bound for the canonical encoding.**

Since the behaviour is computably recoverable from `encodeExplanation r b`, that
string's complexity is at least the behaviour's, up to a constant.

This is the source's §5.1 lower bound *specialised to one encoding*. The source
argues it for every compatible pair via the evaluation map `(p, R) ↦ p(R)`; here
`decodeBehaviour` inverts one fixed pairing, so nothing is claimed about
arbitrary explanations.
-/
public theorem explanation_at_least_behaviour
    (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ r b : BitString,
      plainK U b ≤ plainK U (encodeExplanation r b) + (c : ENat) := by
  obtain ⟨c, hc⟩ := plainKMapLe U hU decodeBehaviour computable_decodeBehaviour
  refine ⟨c, fun r b => ?_⟩
  have := hc (encodeExplanation r b)
  rwa [decodeBehaviour_encodeExplanation] at this

/--
**Simplicity does not break the tie (BY-011).**

For any fixed reward, the degenerate explanation of a behaviour has plain
Kolmogorov complexity at most that of the behaviour plus a constant independent
of the behaviour. This theorem makes no comparison with an intended
planner/reward decomposition; such a comparison would require a separate lower
bound on the intended pair, corresponding to the source's unproved Conjecture 9.

Proved by applying the vendored invariance lemma `Kolmogorov.plainKMapLe` to the
computable encoding `encodeExplanation r`.
-/
public theorem degenerate_explanation_cheap
    (U : Map) (hU : isOptimalConditional U) (r : BitString) :
    ∃ c : ℕ, ∀ b : BitString,
      plainK U (encodeExplanation r b) ≤ plainK U b + (c : ENat) :=
  plainKMapLe U hU (encodeExplanation r) (computable_encodeExplanation r)

/--
**Both bounds together, for the canonical encoding.**

`encodeExplanation r b` has plain Kolmogorov complexity equal to that of `b`, up
to additive constants in both directions.

This does **not** establish that it is within a constant of the cheapest
compatible explanation, since no minimum over explanations is formalized here.
The corresponding quantified statement is
`ReasonableLanguage.proposition_seven`, over an abstract measure.
-/
public theorem explanation_complexity_eq_behaviour
    (U : Map) (hU : isOptimalConditional U) (r : BitString) :
    ∃ c₁ c₂ : ℕ, ∀ b : BitString,
      plainK U b ≤ plainK U (encodeExplanation r b) + (c₁ : ENat) ∧
      plainK U (encodeExplanation r b) ≤ plainK U b + (c₂ : ENat) := by
  obtain ⟨c₁, h₁⟩ := explanation_at_least_behaviour U hU
  obtain ⟨c₂, h₂⟩ := degenerate_explanation_cheap U hU r
  exact ⟨c₁, c₂, fun b => ⟨h₁ r b, h₂ b⟩⟩

end AISafetyAtlas.Preference
