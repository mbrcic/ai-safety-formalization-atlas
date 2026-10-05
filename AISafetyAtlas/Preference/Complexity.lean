module

public import AISafetyAtlas.Preference
public import AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.Properties
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.PartrecCode

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
- **Conclusion.** Two layers. The first is both bounds **for one canonical
  encoding only**, and is described next; the second, added 2026-09-20, is the
  source's lower bound **at the source's own quantifier** — see *The lower bound
  at print's quantifier* below, where `behaviour_le_of_evaluatesTo` bounds the
  behaviour by every string that evaluates to it, through a real evaluation map.
  *Lower*
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
  are themselves close to this bound"; Proposition 7 combines these. The
  source's framework of `c`-reasonable languages and "comparable complexity" is
  replaced throughout by plain additive constants over `Kolmogorov.plainK`, and
  no `ReasonableLanguage` is instantiated at `plainK` — doing that needs
  policies as strings and is a separate piece of work.

  **Until 2026-09-20 the lower bound here was narrower than the source's**, and
  the gap was the quantifier: the source applies evaluation to *every*
  compatible pair, while `decodeBehaviour` inverts one fixed encoding. That is
  closed. `evalPair` is the source's map, `EvaluatesTo` its compatibility
  relation, and `behaviour_le_of_evaluatesTo` the bound over every compatible
  pair with one constant. The older pair of bounds is kept and is not
  superseded: `encodeExplanation` is a different, non-program pairing, and
  `explanation_complexity_eq_behaviour` is a true two-sided fact about it. The
  abstract statement over an arbitrary complexity measure remains
  `AISafetyAtlas.Preference.ReasonableLanguage.policy_le_of_compatible`.

## Explicit non-claims

- **Not** a claim that no prior can distinguish the pairs — only that a prior
  built from plain Kolmogorov complexity cannot, up to an additive constant.
- **Not** a treatment of the source's anti-rational pair `(-p_g, -R_π̇)` or of
  its regret analysis.
- **Not**, in `explanation_at_least_behaviour`, a lower bound over arbitrary
  explanations: that one is a bi-Lipschitz fact about one canonical pairing
  encoding. `behaviour_le_of_evaluatesTo` **is** over arbitrary compatible
  pairs, and the two are separate statements about separate objects.
- **Not** the whole of the source's Proposition 7. The lower bound half is here
  at the source's quantifier; the upper half is here only for `readerPair`, and
  the three named degenerate pairs of §5.1.2 live in `Reasonable.lean` over an
  abstract measure.
- **Not** an upper bound on the source's own degenerate pair `(p_π̇, R)` as a
  function of the behaviour. `degeneratePair` builds its planner *from* the
  behaviour, so such a bound needs the primitive recursiveness of the
  constant-program map, which the pinned Mathlib does not state. `readerPair`
  carries the upper bound instead and is compatible with the same behaviour.
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

/-! ## The lower bound at print's quantifier

Everything above is about **one** pairing, `encodeExplanation`, and says so. The
source's §5.1 argues the lower bound *"on any pair compatible with"* the
behaviour, and its reason is that **evaluation is a simple map**: a planner
applied to a reward is a fixed computable operation, so the behaviour is never
more than a constant simpler than the pair that produces it.

This section renders that. A pair is a bit string carrying a **program** and a
**reward**; `evalPair` runs the one on the other; `EvaluatesTo` is the source's
compatibility relation, and `behaviour_le_of_evaluatesTo` is the bound over
*every* string that evaluates to the behaviour, with one constant.

Two facts about a planner make this possible that the framework above does not
have. A planner applied to a reward may **diverge**, so the evaluation map is
partial and `Kolmogorov.plainKMapLe` — which takes a total computable map — does
not apply; `plainK_le_of_partrec` is its partial form. And the program slot is
read off the string as a **run length**, so every program index is the index of
some string: without that the source's degenerate pair would not be expressible
and the bound would quantify over an antecedent nobody could inhabit.
-/

/--
**Invariance under a partial computable map.**

`Kolmogorov.plainKMapLe` is this for a total map. Evaluation of a planner is
partial — the planner may not halt on the reward — so the total form does not
reach the statement this module needs.

Generic mathematics in the sense of `docs/agent/policy/lean-routing.md`, kept
here because its only consumer is below and because the vendored
`AISafetyAtlas.Upstream.KolmogorovMathlib` tree is a pinned revision that must
not be edited. It is the natural next lemma there, and is offered upstream with
the rest of that development rather than added to the pin.
-/
public theorem plainK_le_of_partrec (U : Map) (hU : isOptimalConditional U)
    (f : BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ x y : BitString, y ∈ f x → plainK U y ≤ plainK U x + (c : ENat) := by
  let D : Map := fun pair ↦ (U (pair.1, [])).bind f
  have hD : isDecompressor D := Partrec.bind
    (Partrec.comp hU.1 (Computable.pair Computable.fst (Computable.const [])))
    (hf.comp Computable.snd)
  obtain ⟨c, hc⟩ := hU.2 D hD
  refine ⟨c, fun x y hy => ?_⟩
  refine le_trans (hc y []) ?_
  gcongr
  refine sInf_le_sInf ?_
  rintro n ⟨p, hp, rfl⟩
  exact ⟨p, Part.mem_bind_iff.2 ⟨x, hp, hy⟩, rfl⟩

open Nat.Partrec (Code)

/--
**A planner/reward pair as a bit string.** The program index in unary, a `false`
marker, then the reward. The unary index is wasteful and nothing below depends
on it: every bound here is an additive invariance constant.

Reading the index as a **run length** is what makes the encoding surjective onto
programs — every index is the index of some pair — where reading it through
`Encodable.encode` on bit strings would not be.
-/
@[expose] public def pairString (n : ℕ) (r : BitString) : BitString :=
  List.replicate n true ++ false :: r

/-- The planner a pair names. -/
@[expose] public def pairProgram (x : BitString) : Code :=
  Denumerable.ofNat Code ((x.takeWhile id).length)

/-- The reward a pair names. -/
@[expose] public def pairReward (x : BitString) : BitString :=
  (x.dropWhile id).tail

private theorem takeWhile_pairString (n : ℕ) (r : BitString) :
    (pairString n r).takeWhile id = List.replicate n true := by
  unfold pairString
  induction n with
  | zero => simp
  | succ k ih => simp [List.replicate_succ]

private theorem dropWhile_pairString (n : ℕ) (r : BitString) :
    (pairString n r).dropWhile id = false :: r := by
  unfold pairString
  induction n with
  | zero => simp
  | succ k ih => simp [List.replicate_succ]

/-- The pairing is read back: the program slot is the index it was built from. -/
public theorem pairProgram_pairString (n : ℕ) (r : BitString) :
    pairProgram (pairString n r) = Denumerable.ofNat Code n := by
  rw [pairProgram, takeWhile_pairString, List.length_replicate]

/-- …and the reward slot is the reward it was built from. -/
public theorem pairReward_pairString (n : ℕ) (r : BitString) :
    pairReward (pairString n r) = r := by
  rw [pairReward, dropWhile_pairString, List.tail_cons]

public theorem computable_pairProgram : Computable pairProgram :=
  (Computable.ofNat Code).comp
    (Primrec.to_comp (Primrec.list_length.comp (Primrec.list_takeWhile Primrec.id)))

public theorem computable_pairReward : Computable pairReward :=
  Primrec.to_comp (Primrec.list_tail.comp (Primrec.list_dropWhile Primrec.id))

/--
**The source's evaluation map, at bit strings.** Run the pair's planner on the
pair's reward and read the result back as a behaviour. The source writes it
`(p, R) ↦ p(R)`.

It is a **partial** function: nothing makes a planner halt on a reward.
-/
@[expose] public noncomputable def evalPair (x : BitString) : Part BitString :=
  (Code.eval (pairProgram x) (Encodable.encode (pairReward x))).bind
    fun n => (Encodable.decode (α := BitString) n : Part BitString)

/-- Evaluation is partial computable, which is the whole of the source's *"because
evaluation is a simple map"*. -/
public theorem partrec_evalPair : Partrec evalPair :=
  Partrec.bind
    (Code.eval_part.comp computable_pairProgram
      (Computable.encode.comp computable_pairReward))
    (Computable.ofOption (Computable.decode.comp Computable.snd))

/--
**Compatibility, in the source's sense.** The pair evaluates to the behaviour.

`AISafetyAtlas.Preference.ReasonableLanguage.Compatible` is the same relation
over an abstract language, where evaluation is the structure field `op3`. This
one is concrete: the planner is a program and evaluation runs it.
-/
@[expose] public def EvaluatesTo (x b : BitString) : Prop := b ∈ evalPair x

/--
**The source's §5.1 lower bound, at the source's quantifier.**

*"The complexity of `π̇` is close to a lower bound on any pair compatible with
it."* One constant, chosen before the pair and before the behaviour, bounds the
behaviour's complexity by that of **every** string that evaluates to it.

This is what `explanation_at_least_behaviour` does not say. That theorem
quantifies over the manufactured strings `encodeExplanation r b` and inverts one
fixed pairing; this one quantifies over compatible pairs through the evaluation
map, as the source does. Both are true and the older one is not superseded — it
is the same bound for a different, non-program pairing.
-/
public theorem behaviour_le_of_evaluatesTo (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x b : BitString, EvaluatesTo x b →
      plainK U b ≤ plainK U x + (c : ENat) := by
  obtain ⟨c, hc⟩ := plainK_le_of_partrec U hU evalPair partrec_evalPair
  exact ⟨c, fun x b hxb => hc x b hxb⟩

/--
**The source's degenerate pair.** The planner ignores its reward and returns the
behaviour; the reward is whatever you like. This is `(p_π̇, R)` in the source's
notation, and the source's `(p_π̇, 0)` is the case `r = []`.
-/
@[expose] public def degeneratePair (r b : BitString) : BitString :=
  pairString (Encodable.encode (Code.const (Encodable.encode b))) r

/--
**The antecedent is inhabited, and by the source's own object.** The degenerate
pair evaluates to the behaviour, so `behaviour_le_of_evaluatesTo` is not a bound
over an empty class.
-/
public theorem evaluatesTo_degeneratePair (r b : BitString) :
    EvaluatesTo (degeneratePair r b) b := by
  unfold EvaluatesTo evalPair degeneratePair
  rw [pairProgram_pairString, pairReward_pairString, Denumerable.ofNat_encode,
    Code.eval_const]
  simp [Encodable.encodek]

/--
**The reading pair**: the planner is the identity program and the reward carries
the behaviour. Unlike the degenerate pair its planner does not depend on the
behaviour, which is what makes it computable in the behaviour and so cheap.
-/
@[expose] public def readerPair (b : BitString) : BitString :=
  pairString (Encodable.encode Code.id) b

/-- It too is compatible with the behaviour. -/
public theorem evaluatesTo_readerPair (b : BitString) :
    EvaluatesTo (readerPair b) b := by
  unfold EvaluatesTo evalPair readerPair
  rw [pairProgram_pairString, pairReward_pairString, Denumerable.ofNat_encode,
    Code.eval_id]
  simp [Encodable.encodek]

public theorem computable_readerPair : Computable readerPair := by
  unfold readerPair pairString
  refine Primrec.to_comp ?_
  exact Primrec₂.comp Primrec.list_append (Primrec.const _)
    (Primrec₂.comp Primrec.list_cons (Primrec.const false) Primrec.id)

/--
**The shape of the source's second §5.1 claim, at a fourth pair.** The source
writes *"degenerate decompositions are themselves close to this bound"* about
its own three pairs. The reading pair is none of them. What it shows is that the
argument closes: it is at most a constant more complex than the behaviour, and
by `behaviour_le_of_evaluatesTo` no compatible pair is more than a constant
simpler — so it sits within additive constants of the whole compatible class,
not merely of one manufactured string. The source's own three pairs are in
`AISafetyAtlas.Preference.Reasonable`, over an abstract measure.

The degenerate pair itself carries no such upper bound here, and the reason is
not that it is false: its planner is built from the behaviour, so bounding it
needs the primitive recursiveness of the constant-program map, which the pinned
Mathlib does not state.
-/
public theorem readerPair_complexity_eq_behaviour (U : Map)
    (hU : isOptimalConditional U) :
    ∃ c₁ c₂ : ℕ, ∀ b : BitString,
      plainK U b ≤ plainK U (readerPair b) + (c₁ : ENat) ∧
      plainK U (readerPair b) ≤ plainK U b + (c₂ : ENat) := by
  obtain ⟨c₁, h₁⟩ := behaviour_le_of_evaluatesTo U hU
  obtain ⟨c₂, h₂⟩ := plainKMapLe U hU readerPair computable_readerPair
  exact ⟨c₁, c₂, fun b => ⟨h₁ _ b (evaluatesTo_readerPair b), h₂ b⟩⟩

end AISafetyAtlas.Preference
