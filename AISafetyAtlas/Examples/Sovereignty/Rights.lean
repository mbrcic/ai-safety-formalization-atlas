module

public import AISafetyAtlas.Sovereignty.Rights
public import AISafetyAtlas.Sovereignty.Mandate

/-!
# Peleg's two-shirt society, and the two game forms he tests against it

Print's Example 2.3, journal page 69: `N = {1, 2}`, each member wears a white or
a blue shirt, `A` is the four pairs, `ρ = {ρ₁}` is the right to freely choose
one's own shirt, `α(∅) = ∅` and `α(1) = α(2) = α(N) = ρ₁`.

Print then tests two game forms against it.

* **Example 3.6.** Both members choose simultaneously, `g(x¹, x²) = (x¹, x²)`.
  Print: this *is* a representation. `represents_shirtGame`.
* **Example 3.7.** Member 2 chooses after observing member 1, so `Σ² = Σ¹ → Σ¹`
  and `g(x, f) = (x, f(x))`. Print: this is *not* a representation, because by
  choosing `f(x) = x` member 2 alone forces `{(w, w), (b, b)}`, which is not in
  `E(2)`. `not_represents_sequentialGame`.

**One thing print leaves to the reader.** Example 2.3 lists
`γ(1, ρ₁) = {{(w, w), (w, b)}, {(b, w), (b, b)}}` -- the two *minimal* attainable
sets, and no supersets -- while writing `γ(N, ρ₁) = 2^A \ {∅}` in full in the
same sentence. So the listing at members 1 and 2 names generators of an
upward-closed family, and the example says so itself by giving the third
coalition's family entire. `shirtAccess` is that reading. Taken as the whole
family instead, the constitution fails print's own condition (3.3) and by
Theorem 3.5 is not representable at all, contradicting Example 3.6:
`not_monotoneAlternatives_listedShirt` and `not_represents_of_induced_eq_listed`
are those two facts.

The third witness, `represented_not_monotoneAlternatives`, is about Theorem 3.5
rather than about this society: it is a constitution `shirtGame` represents
whose access correspondence fails (3.3) **off the diagonal**, where a
representation cannot see it.

## Print's other two societies, and what each settles

* **Example 2.7**, journal page 70: workers sharing an office, where the single
  right is the *obligation* not to smoke in front of a non-smoker.
  `smokeConstitution`. It turns out to answer a question print raises one
  section later and leaves open — Definition 3.1's *"an EF that is derived from
  a constitution by (3.1) might not be superadditive"* — since
  `not_superadditive_officeConstitution` is exactly that, and
  `not_represents_officeConstitution` follows.
* **Example 2.10**, journal page 71: Gibbard's marriage society, three members
  and three social states, with two rights. `gibbardConstitution`. Print's
  **Example 3.8**, page 74, computes its effectivity function by (3.1) and ends
  *"as the reader may easily verify, `E(·)` is superadditive and monotonic
  w.r.t. the alternatives"*. `gibbardInduced_superadditive` and
  `gibbardConstitution_upwardClosed` are those two verifications, and the eight
  computed values, from `gibbardInduced_empty` to `gibbardInduced_univ`, are print's
  table.

**A second looseness of print, and it is the same one.** Examples 2.7 and 2.10
both write `γ(S, ∅) = A` and `γ(∅, θ) = A` where page 69's standing assumption
writes `{A}` — the singleton-for-set shorthand again, three examples running.
`Standing` asks for the family, and both `smokeConstitution_standing` and
`gibbardConstitution_standing` prove it in that form.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-! ## The society -/

/-- A shirt: `false` is white, `true` is blue. -/
public abbrev Shirt : Type := Bool

/-- A social state: what each of the two members wears. -/
public abbrev Outfit : Type := Shirt × Shirt

/-- What member `i` is wearing in a given social state. -/
@[expose] public def worn (i : Bool) (x : Outfit) : Shirt :=
  cond i x.2 x.1

/--
**The sets a coalition can pin down by fixing its own members' shirts**, closed
upwards. Print's `γ(S, ρ₁)`, with the supersets print's Example 2.3 leaves
implicit and its Example 2.10 writes out.
-/
@[expose] public def shirtAccess (C : Set Bool) : Set (Set Outfit) :=
  {B | ∃ f : Bool → Shirt, {x : Outfit | ∀ i ∈ C, worn i x = f i} ⊆ B}

/-- The empty coalition pins nothing down, so its family is the whole state
space alone -- print's standing assumption, here computed. -/
public theorem shirtAccess_empty : shirtAccess (∅ : Set Bool) = {Set.univ} := by
  ext B
  simp only [shirtAccess, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_f, hf⟩
    exact Set.univ_subset_iff.mp (by simpa using hf)
  · rintro rfl
    exact ⟨fun _ => false, Set.subset_univ _⟩

/-- The whole state space is attainable by every coalition. -/
public theorem univ_mem_shirtAccess (C : Set Bool) : Set.univ ∈ shirtAccess C :=
  ⟨fun _ => false, Set.subset_univ _⟩

/-- A larger coalition pins down at least as much. -/
public theorem shirtAccess_mono {C D : Set Bool} (h : C ⊆ D) :
    shirtAccess C ⊆ shirtAccess D := by
  rintro B ⟨f, hf⟩
  exact ⟨f, fun x hx => hf fun i hi => hx i (h hi)⟩

/--
**Print's Example 2.3 as a constitution.** One right, held by every non-empty
coalition and by no other; with it, a coalition attains what it can pin down,
and without it only the whole state space.
-/
@[expose] public def shirtConstitution : Constitution Bool Outfit Unit where
  assign := fun C => {_r | C.Nonempty}
  access := fun C θ =>
    {B | () ∈ θ ∧ B ∈ shirtAccess C ∨ () ∉ θ ∧ B = Set.univ}

/-- The rights a coalition holds: all of them when it is non-empty, none
otherwise. Print's `α(∅) = ∅`, `α(1) = α(2) = α(N) = ρ₁`. -/
public theorem mem_shirtConstitution_assign {C : Set Bool} :
    () ∈ shirtConstitution.assign C ↔ C.Nonempty := Iff.rfl

/-- **The induced effectivity function is exactly what a coalition can pin
down**, at every coalition -- including the empty one, where the standing
assumption and the computation agree. -/
public theorem shirtConstitution_induced (C : Set Bool) :
    shirtConstitution.induced C = shirtAccess C := by
  by_cases hC : C.Nonempty
  · ext B
    simp only [Constitution.induced, shirtConstitution, Set.mem_ofPred_eq]
    exact ⟨fun h => h.elim (fun h => h.2) (fun h => absurd hC h.1), fun h => Or.inl ⟨hC, h⟩⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hC
    subst hC
    ext B
    simp only [Constitution.induced, shirtConstitution, Set.mem_ofPred_eq,
      shirtAccess_empty, Set.mem_singleton_iff]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, rfl⟩)
      · exact absurd h (by simp)
      · rfl
    · rintro rfl
      exact Or.inr ⟨by simp, rfl⟩

/-- Print's standing assumptions hold of it. -/
public theorem shirtConstitution_standing : shirtConstitution.Standing where
  assign_empty := by
    ext r
    simp [shirtConstitution]
  access_empty_coalition θ := by
    ext B
    simp only [shirtConstitution, Set.mem_ofPred_eq, shirtAccess_empty,
      Set.mem_singleton_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
    · rintro rfl
      by_cases h : () ∈ θ
      · exact Or.inl ⟨h, rfl⟩
      · exact Or.inr ⟨h, rfl⟩
  access_empty_rights C := by
    ext B
    simp only [shirtConstitution, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h (by simp)
      · exact h
    · rintro rfl
      exact Or.inr ⟨by simp, rfl⟩

/-! ## Print's three monotonicity conditions, on this constitution -/

/-- **(3.2).** A larger coalition holds at least the rights of a smaller one. -/
public theorem shirtConstitution_monotoneAssign : shirtConstitution.MonotoneAssign := by
  rintro S T hST r ⟨x, hx⟩
  exact ⟨x, hST hx⟩

/-- **(3.4).** More rights attain more -- print says this generally fails, and
on a constitution with one right it does not. -/
public theorem shirtConstitution_monotoneRights : shirtConstitution.MonotoneRights := by
  rintro S θ θ' hθ B (⟨h, hB⟩ | ⟨h, rfl⟩)
  · exact Or.inl ⟨hθ h, hB⟩
  · by_cases h' : () ∈ θ'
    · exact Or.inl ⟨h', univ_mem_shirtAccess S⟩
    · exact Or.inr ⟨h', rfl⟩

/-- **(3.5).** A larger coalition attains more at fixed rights. -/
public theorem shirtConstitution_monotoneCoalitions :
    shirtConstitution.MonotoneCoalitions := by
  rintro S S' θ hSS' B (⟨h, hB⟩ | ⟨h, rfl⟩)
  · exact Or.inl ⟨h, shirtAccess_mono hSS' hB⟩
  · exact Or.inr ⟨h, rfl⟩

/-- **The induced effectivity function is coalition-monotone**, by print's own
composition of (3.2), (3.4) and (3.5). -/
public theorem shirtConstitution_induced_mono {S T : Set Bool} (hST : S ⊆ T) :
    shirtConstitution.induced S ⊆ shirtConstitution.induced T :=
  shirtConstitution.induced_mono shirtConstitution_monotoneAssign
    shirtConstitution_monotoneRights shirtConstitution_monotoneCoalitions hST

/-- **Print's condition (i) on an effectivity function**, computed rather than
stipulated. -/
public theorem shirtConstitution_induced_empty :
    shirtConstitution.induced (∅ : Set Bool) = {Set.univ} :=
  shirtConstitution.induced_empty shirtConstitution_standing

/-! ## Example 3.6: the simultaneous game form

Stated once for a whole family, because Example 3.7's negative witness needs a
second member of it and nothing else changes.
-/

/-- Each member picks a shirt, and a relabelling `φ` records what that choice
puts on their back. Print's Example 3.6 is `φ = id`. -/
@[expose] public def shirtGameOf (φ : Bool → Shirt → Shirt) : GameForm Bool Outfit where
  strategy := fun _ => Shirt
  outcome := fun s => (φ false (s false), φ true (s true))

/-- What a member is wearing under such a game form is the relabelling of their
own choice, and nobody else's. -/
public theorem worn_outcome (φ : Bool → Shirt → Shirt) (i : Bool)
    (s : ∀ j, (shirtGameOf φ).strategy j) :
    worn i ((shirtGameOf φ).outcome s) = φ i (s i) := by
  cases i <;> rfl

/-- A social state is determined by what each of the two members is wearing. -/
public theorem outfit_ext {x y : Outfit} (h₀ : worn false x = worn false y)
    (h₁ : worn true x = worn true y) : x = y := by
  simp only [worn, cond_false, cond_true] at h₀ h₁
  exact Prod.ext h₀ h₁

/-- **What each such game form's α-effectivity function is.** A coalition can
force exactly what it can pin down, provided each member's relabelling is onto:
the members of `C` fix their own coordinates and nothing else is fixed. -/
public theorem effectivity_shirtGameOf {φ : Bool → Shirt → Shirt}
    (hφ : ∀ i, Function.Surjective (φ i)) (C : Set Bool) :
    effectivity (shirtGameOf φ) C = shirtAccess C := by
  classical
  ext B
  constructor
  · rintro ⟨sC, hsC⟩
    refine ⟨fun i => if h : i ∈ C then φ i (sC ⟨i, h⟩) else false, fun x hx => ?_⟩
    choose t ht using fun i : Bool => hφ i (worn i x)
    set s : ∀ j, (shirtGameOf φ).strategy j :=
      fun i => if h : i ∈ C then sC ⟨i, h⟩ else t i with hsdef
    have key : (shirtGameOf φ).outcome s ∈ B := hsC s (fun i => by simp [hsdef, i.2])
    have hval : ∀ i : Bool, φ i (s i) = worn i x := by
      intro i
      by_cases h : i ∈ C
      · simpa [hsdef, h] using (hx i h).symm
      · simpa [hsdef, h] using ht i
    have hout : (shirtGameOf φ).outcome s = x :=
      outfit_ext (by rw [worn_outcome]; exact hval false)
        (by rw [worn_outcome]; exact hval true)
    exact hout ▸ key
  · rintro ⟨f, hf⟩
    choose t ht using fun i : Bool => hφ i (f i)
    refine ⟨fun i => t i, fun s hs' => hf (fun i hi => ?_)⟩
    rw [worn_outcome, hs' ⟨i, hi⟩]
    exact ht i

/-- **Print's Example 3.6.** Both members choose simultaneously and the outcome
is the pair of choices. -/
@[expose] public def shirtGame : GameForm Bool Outfit := shirtGameOf fun _ => id

/-- The same game with both members' choices read in the opposite sense -- a
second, different game form with the same distribution of power. -/
@[expose] public def shirtGameFlipped : GameForm Bool Outfit := shirtGameOf fun _ => not

/-- **Print's Example 3.6, as a theorem: the simultaneous game form is a
representation of the two-shirt constitution.** -/
public theorem represents_shirtGame : Represents shirtGame shirtConstitution := fun C => by
  rw [shirtGame, effectivity_shirtGameOf (fun _ => Function.surjective_id) C,
    shirtConstitution_induced]

/-- And so is the relabelled one, which is a genuinely different game form. -/
public theorem represents_shirtGameFlipped :
    Represents shirtGameFlipped shirtConstitution := fun C => by
  rw [shirtGameFlipped,
    effectivity_shirtGameOf (fun _ b => ⟨!b, by simp⟩) C, shirtConstitution_induced]

/-- **Two game forms representing one constitution retain every mandate across
the move between them** -- the constitution-side retention lemma at a pair that
is not the trivial one. -/
public theorem retainsFamily_shirtGames (C : Set Bool) (𝒜 : Set (Set Outfit)) :
    RetainsFamily shirtGame shirtGameFlipped C C 𝒜 :=
  retainsFamily_of_represents represents_shirtGame represents_shirtGameFlipped C 𝒜

/-! ## What representation forces -/

/-- **The outcome function is onto**, derived from the representation rather
than assumed -- print assumes surjectivity from Definition 3.3 onward. -/
public theorem surjective_shirtGame_outcome : Function.Surjective shirtGame.outcome :=
  represents_shirtGame.surjective_outcome shirtConstitution_standing

/-- **Theorem 3.5's condition (ii) on this constitution**, obtained from the
representation. -/
public theorem superadditive_shirtConstitution : Superadditive shirtConstitution.induced :=
  represents_shirtGame.superadditive

/-- **Condition (3.3) on the diagonal**, likewise. -/
public theorem upwardClosed_shirtConstitution : UpwardClosed shirtConstitution.induced :=
  represents_shirtGame.upwardClosed

/-! ## Example 3.7: the sequential game form -/

/-- Member 1 chooses a shirt; member 2 chooses a shirt **as a function of what
member 1 chose**. -/
@[expose] public def seqStrategy : Bool → Type
  | false => Shirt
  | true => Shirt → Shirt

/-- Member 2's strategy in the coalition `{2}`: copy member 1. Print's `f(x) = x`. -/
@[expose] public def copyOne : ∀ i : ({true} : Set Bool), seqStrategy i.1
  | ⟨true, _⟩ => id
  | ⟨false, h⟩ => absurd h (by simp)

/-- **Print's Example 3.7.** Member 2 observes member 1's choice before making
their own. -/
@[expose] public def sequentialGame : GameForm Bool Outfit where
  strategy := seqStrategy
  outcome := fun s => (s false, (s true) (s false))

/-- **Member 2 alone forces the two matching outfits**, which is exactly what
the sequential procedure adds. -/
public theorem forces_matching :
    Forces sequentialGame {true} {x : Outfit | x.1 = x.2} := by
  refine ⟨copyOne, fun s hs => ?_⟩
  have h := hs ⟨true, rfl⟩
  simp only [copyOne] at h
  show (s false, (s true) (s false)).1 = (s false, (s true) (s false)).2
  rw [h]
  rfl

/-- But the two matching outfits are not attainable by member 2 under the
constitution: neither of member 2's own choices pins them down. -/
public theorem matching_not_mem_shirtAccess :
    {x : Outfit | x.1 = x.2} ∉ shirtAccess {true} := by
  rintro ⟨f, hf⟩
  have h : (!f true, f true) ∈ {x : Outfit | ∀ i ∈ ({true} : Set Bool), worn i x = f i} := by
    intro i hi
    simp only [Set.mem_singleton_iff] at hi
    subst hi
    rfl
  have := hf h
  simp only [Set.mem_ofPred_eq] at this
  exact (Bool.not_ne_self _) this

/-- **Print's Example 3.7, as a theorem: the sequential game form is not a
representation.** -/
public theorem not_represents_sequentialGame :
    ¬ Represents sequentialGame shirtConstitution := by
  intro h
  refine matching_not_mem_shirtAccess ?_
  rw [← shirtConstitution_induced, ← h {true}]
  exact forces_matching

/-! ## How Example 2.3's listing has to be read

Print lists `γ(1, ρ₁)` and `γ(2, ρ₁)` as two sets each -- the *minimal* outfits
a member can pin down -- and in the same sentence writes `γ(N, ρ₁) = 2^A \ {∅}`
in full. One coalition's family is given entire and the other two by their least
elements, which is the evidence, inside the example itself, that the listing at
1 and 2 names generators. Remark 2.2 on the same page supplies the reading, and
Example 2.10 two pages later writes the closure out with its `B⁺` notation.

This is notational looseness, not a misstatement: the theorems below say what
goes wrong if the listing is taken as the whole family, and nothing here claims
print meant it that way.
-/

/-- The sets print *lists* at a coalition: what its members can pin down, with
no supersets. -/
@[expose] public def listedAccess (C : Set Bool) : Set (Set Outfit) :=
  {B | ∃ f : Bool → Shirt, B = {x : Outfit | ∀ i ∈ C, worn i x = f i}}

/-- A constitution whose family at member 1 is print's listed `γ(1, ρ₁)`, and
whose other values model nothing -- the object exists only to carry the two
theorems below. -/
@[expose] public def listedShirt : Constitution Bool Outfit Unit where
  assign := fun C => {_r | C.Nonempty}
  access := fun C _θ => listedAccess C

/-- **Taken as the whole family, the listing fails print's own condition
(3.3).** Member 1 pins down the white-shirted outfits, and the whole state space
is a superset of them that the listing does not contain. -/
public theorem not_monotoneAlternatives_listedShirt :
    ¬ listedShirt.MonotoneAlternatives := by
  intro h
  obtain ⟨f, hf⟩ :=
    h {false} Set.univ {x : Outfit | ∀ i ∈ ({false} : Set Bool), worn i x = false}
      Set.univ ⟨fun _ => false, rfl⟩ (Set.subset_univ _)
  have hmem : ((!f false, f true) : Outfit) ∈ (Set.univ : Set Outfit) := Set.mem_univ _
  rw [hf] at hmem
  exact Bool.not_ne_self _ (hmem false rfl)

/--
**And then no game form whatever represents it** -- not only the two print
tests. Stated for every constitution whose induced family at member 1 is the
listing, since that single value is all the argument uses: a game form's
α-effectivity function is closed upwards and the listing is not.

This is why Example 2.3's listing cannot be the whole family: print's Example
3.6 exhibits a representation of that constitution.
-/
public theorem not_represents_of_induced_eq_listed {R : Type} (G : GameForm Bool Outfit)
    (κ : Constitution Bool Outfit R)
    (hκ : κ.induced {false} = listedAccess {false}) : ¬ Represents G κ := by
  intro h
  obtain ⟨f, hf⟩ := hκ ▸
    h.upwardClosed {false} {x : Outfit | ∀ i ∈ ({false} : Set Bool), worn i x = false}
      Set.univ (hκ ▸ ⟨fun _ => false, rfl⟩) (Set.subset_univ _)
  have hmem : ((!f false, f true) : Outfit) ∈ (Set.univ : Set Outfit) := Set.mem_univ _
  rw [hf] at hmem
  exact Bool.not_ne_self _ (hmem false rfl)

/-- The same at `listedShirt` itself. -/
public theorem not_represents_listedShirt (G : GameForm Bool Outfit) :
    ¬ Represents G listedShirt :=
  not_represents_of_induced_eq_listed G listedShirt rfl

/-! ## Where a representation cannot see condition (3.3)

Theorem 3.5's condition (i) asks (3.3) of `γ` at **every** set of rights, while
a representation constrains only `γ(S, α(S))`. The gap is real: this
constitution is represented by `shirtGame` and fails (3.3).
-/

open Classical in
/-- A constitution that agrees with `shirtConstitution` wherever `α` sends a
coalition, and is wrong everywhere else. Two rights, so that a set of rights can
be neither empty nor everything. -/
@[expose] public noncomputable def offDiagonal : Constitution Bool Outfit Bool where
  assign := fun C => {_r | C.Nonempty}
  access := fun C θ =>
    if C = ∅ ∨ θ = ∅ then {Set.univ}
    else if θ = Set.univ then shirtAccess C
    else {(∅ : Set Outfit)}

/-- On the diagonal it is the two-shirt constitution. -/
public theorem offDiagonal_induced (C : Set Bool) :
    offDiagonal.induced C = shirtAccess C := by
  by_cases hC : C.Nonempty
  · have hne : C ≠ ∅ := Set.nonempty_iff_ne_empty.mp hC
    have hassign : offDiagonal.assign C = (Set.univ : Set Bool) := by
      ext r
      simp [offDiagonal, hC]
    rw [Constitution.induced, hassign]
    show (if C = ∅ ∨ (Set.univ : Set Bool) = ∅ then _
      else if (Set.univ : Set Bool) = Set.univ then _ else _) = _
    rw [if_neg (by
      rintro (h | h)
      · exact hne h
      · exact (Set.univ_nonempty (α := Bool)).ne_empty h), if_pos rfl]
  · rw [Set.not_nonempty_iff_eq_empty] at hC
    subst hC
    rw [Constitution.induced]
    show (if (∅ : Set Bool) = ∅ ∨ _ then _ else _) = _
    rw [if_pos (Or.inl rfl), shirtAccess_empty]

/-- **A represented constitution that fails condition (3.3).** `shirtGame`
represents it, and the failure sits at a set of rights no coalition is ever
assigned, where the representation says nothing. -/
public theorem represented_not_monotoneAlternatives :
    Represents shirtGame offDiagonal ∧ ¬ offDiagonal.MonotoneAlternatives := by
  refine ⟨fun C => by
    rw [shirtGame, effectivity_shirtGameOf (fun _ => Function.surjective_id) C,
      offDiagonal_induced], ?_⟩
  intro h
  have hne : (Set.univ : Set Bool) ≠ ∅ := (Set.univ_nonempty (α := Bool)).ne_empty
  have hhalf : ({false} : Set Bool) ≠ ∅ := by
    intro hc
    exact absurd (hc ▸ rfl : false ∈ (∅ : Set Bool)) (by simp)
  have hhalf' : ({false} : Set Bool) ≠ Set.univ := by
    intro hc
    have htrue : true ∈ ({false} : Set Bool) := hc ▸ Set.mem_univ true
    simp at htrue
  have hcond : ¬((Set.univ : Set Bool) = ∅ ∨ ({false} : Set Bool) = ∅) := by
    rintro (hc | hc)
    · exact hne hc
    · exact hhalf hc
  have haccess : offDiagonal.access Set.univ {false} = {(∅ : Set Outfit)} := by
    show (if (Set.univ : Set Bool) = ∅ ∨ ({false} : Set Bool) = ∅ then _
      else if ({false} : Set Bool) = Set.univ then _ else _) = _
    rw [if_neg hcond, if_neg hhalf']
  have hmem : (∅ : Set Outfit) ∈ offDiagonal.access Set.univ {false} := by
    rw [haccess]
    rfl
  have hup := h Set.univ {false} ∅ Set.univ hmem (Set.empty_subset _)
  rw [haccess, Set.mem_singleton_iff] at hup
  exact Set.empty_ne_univ hup.symm

/-- **Print's EF condition (ii) on this game form.** The grand coalition is
effective for exactly the non-empty sets, which follows from the surjectivity
the representation itself forced. -/
public theorem effectivity_shirtGame_univ :
    effectivity shirtGame (Set.univ : Set Bool) = {B : Set Outfit | B.Nonempty} :=
  effectivity_univ_eq_nonempty surjective_shirtGame_outcome

/-! ## The stand-in, instantiated -/

/-- **Equality of effectivity functions is representation against a constitution
read off a game form**, on the pair this file already has. -/
public theorem effectivityEq_shirtGames : EffectivityEq shirtGame shirtGameFlipped :=
  (effectivityEq_iff_represents_ofGameForm Unit).mpr
    (fun C => (represents_shirtGame C).trans (represents_shirtGameFlipped C).symm)

/-- Every game form represents its own α-effectivity function. -/
public theorem represents_ofGameForm_shirtGame :
    Represents shirtGame (Constitution.ofGameForm shirtGame Unit) :=
  represents_ofGameForm shirtGame Unit

/-- Transitivity, through the relabelled game and back. -/
public theorem effectivityEq_shirtGame_self : EffectivityEq shirtGame shirtGame :=
  EffectivityEq.trans effectivityEq_shirtGames
    (EffectivityEq.symm effectivityEq_shirtGames)

/-! ## Print's Example 2.7: the office, and a right that is an obligation

Journal page 70. `N = {1, …, n}` workers share an office; `L : N → {σ, v}` says
who smokes, `N₂ = {i | L i = v}` are the non-smokers, and `A = {smoky, clear}`.
The single right is the **obligation** *"Refrain from smoking, at the office, in
the presence of at least one non-smoker"*, with `α(∅) = ∅` and `α(S) = ρ` for
every non-empty `S`, and

> `γ(S, ρ) = 2^A \ {∅}` when `S ∩ N₂ = ∅` and `S ≠ ∅`,
> `γ(S, ρ) = {{clear}, A}` when `S ∩ N₂ ≠ ∅`,

with `γ(S, ∅) = γ(∅, ρ) = A`.

**`{{clear}, A}` is `{clear}` closed upwards**, because `A` has two elements, so
both families here are the upward closures print's Remark 2.2 says to read. The
final clause is print's standing assumption written `= A` where page 69 writes
`= {A}` — the same singleton-for-set shorthand Example 2.3 uses, and harmless
because `Standing` asks for the family.

**Print's `N` is finite and this is not**, which costs nothing: the condition
that decides `γ` is *"some member of the coalition is a non-smoker"*, and that is
a property of the coalition rather than a count.

### What this society is a witness for

Print introduces Example 2.7 to illustrate Remarks 2.5 and 2.6 — symmetry, and
rights that are obligations — and claims nothing about representability. It
turns out to settle a question print raises abstractly one section later.
Definition 3.1's discussion says *"an EF that is derived from a constitution by
(3.1) might not be superadditive"*, and offers no example.
`not_superadditive_officeConstitution` is one: a smoker alone may attain
`{smoky}`, a non-smoker alone may attain `{clear}`, and together they would have
to attain `∅`, which the obligation forbids. By `Represents.superadditive` no
game form represents this society at all — `not_represents_officeConstitution`.
-/

/-- The state of the air at the office: `false` is smoky, `true` is clear. -/
public abbrev Air : Type := Bool

/-- Print's *clear*. -/
@[expose] public def clearAir : Air := true

/-- Print's *smoky*. -/
@[expose] public def smokyAir : Air := false

/-- Print's `S ∩ N₂ ≠ ∅`: the coalition contains a non-smoker. -/
@[expose] public def HasNonSmoker {N : Type u} (nonSmoker : N → Prop) (C : Set N) : Prop :=
  ∃ i ∈ C, nonSmoker i

/--
**Print's `γ(S, ρ)`**, in its three printed cases: the whole state space alone at
the empty coalition, every non-empty set for a coalition of smokers, and the
sets containing *clear* for a coalition that includes a non-smoker.
-/
@[expose] public def smokeAccess {N : Type u} (nonSmoker : N → Prop) (C : Set N) :
    Set (Set Air) :=
  {B | (¬ C.Nonempty ∧ B = Set.univ)
      ∨ (C.Nonempty ∧ HasNonSmoker nonSmoker C ∧ clearAir ∈ B)
      ∨ (C.Nonempty ∧ ¬ HasNonSmoker nonSmoker C ∧ B.Nonempty)}

/-- **Print's Example 2.7 as a constitution.** -/
@[expose] public def smokeConstitution {N : Type u} (nonSmoker : N → Prop) :
    Constitution N Air Unit where
  assign := fun C => {_r | C.Nonempty}
  access := fun C θ =>
    {B | () ∈ θ ∧ B ∈ smokeAccess nonSmoker C ∨ () ∉ θ ∧ B = Set.univ}

/-- Print's standing assumptions hold of it. -/
public theorem smokeConstitution_standing {N : Type u} (nonSmoker : N → Prop) :
    (smokeConstitution nonSmoker).Standing where
  assign_empty := by
    ext r
    simp [smokeConstitution]
  access_empty_coalition := by
    intro θ
    ext B
    simp only [smokeConstitution, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, rfl⟩)
      · rcases h with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · rfl
        · exact absurd h (by simp)
        · exact absurd h (by simp)
      · rfl
    · rintro rfl
      by_cases h : () ∈ θ
      · exact Or.inl ⟨h, Or.inl ⟨by simp, rfl⟩⟩
      · exact Or.inr ⟨h, rfl⟩
  access_empty_rights := by
    intro C
    ext B
    simp only [smokeConstitution, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h ↦ h.elim (fun h ↦ absurd h.1 (by simp)) (fun h ↦ h.2),
      fun h ↦ Or.inr ⟨by simp, h⟩⟩

/-- **The induced effectivity function is print's `γ(S, ρ)`** at every
coalition, the empty one included. -/
public theorem smokeConstitution_induced {N : Type u} (nonSmoker : N → Prop)
    (C : Set N) :
    (smokeConstitution nonSmoker).induced C = smokeAccess nonSmoker C := by
  by_cases hC : C.Nonempty
  · ext B
    simp only [Constitution.induced, smokeConstitution, Set.mem_ofPred_eq]
    refine ⟨fun h ↦ h.elim (fun h ↦ h.2) (fun h ↦ absurd hC h.1), fun h ↦ Or.inl ⟨hC, h⟩⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hC
    subst hC
    ext B
    simp only [Constitution.induced, smokeConstitution, smokeAccess, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, rfl⟩)
      · exact absurd h (by simp)
      · exact Or.inl ⟨by simp, rfl⟩
    · rintro (⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inr ⟨by simp, rfl⟩
      · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- **(3.3) holds here.** Each of print's three families is closed upwards: the
whole space is the top, *"contains clear"* is upward closed, and so is
*"non-empty"*. -/
public theorem smokeConstitution_monotoneAlternatives {N : Type u} (nonSmoker : N → Prop) :
    (smokeConstitution nonSmoker).MonotoneAlternatives := by
  rintro C θ B B' (⟨hθ, hB⟩ | ⟨hθ, rfl⟩) hBB'
  · refine Or.inl ⟨hθ, ?_⟩
    rcases hB with ⟨hC, rfl⟩ | ⟨hC, hns, hcl⟩ | ⟨hC, hns, hne⟩
    · exact Or.inl ⟨hC, Set.univ_subset_iff.mp hBB'⟩
    · exact Or.inr (Or.inl ⟨hC, hns, hBB' hcl⟩)
    · exact Or.inr (Or.inr ⟨hC, hns, hne.mono hBB'⟩)
  · exact Or.inr ⟨hθ, Set.univ_subset_iff.mp hBB'⟩

/-- **A coalition of smokers may have a smoky office.** -/
public theorem smoky_mem_smokeAccess {N : Type u} {nonSmoker : N → Prop} {C : Set N}
    (hC : C.Nonempty) (h : ¬ HasNonSmoker nonSmoker C) :
    ({smokyAir} : Set Air) ∈ smokeAccess nonSmoker C :=
  Or.inr (Or.inr ⟨hC, h, ⟨smokyAir, rfl⟩⟩)

/-- **A coalition with one non-smoker in it may not.** This is the obligation
doing its work, and it is the only place the two branches of print's `γ` differ
on a single set. -/
public theorem smoky_notMem_smokeAccess {N : Type u} {nonSmoker : N → Prop} {C : Set N}
    (h : HasNonSmoker nonSmoker C) :
    ({smokyAir} : Set Air) ∉ smokeAccess nonSmoker C := by
  rintro (⟨hC, hB⟩ | ⟨-, -, hcl⟩ | ⟨-, hns, -⟩)
  · exact hC ⟨h.choose, h.choose_spec.1⟩
  · exact absurd hcl (by decide)
  · exact hns h

/-- Clear air is attainable by any non-empty coalition, whoever is in it. -/
public theorem clear_mem_smokeAccess {N : Type u} {nonSmoker : N → Prop} {C : Set N}
    (hC : C.Nonempty) : ({clearAir} : Set Air) ∈ smokeAccess nonSmoker C := by
  by_cases h : HasNonSmoker nonSmoker C
  · exact Or.inr (Or.inl ⟨hC, h, rfl⟩)
  · exact Or.inr (Or.inr ⟨hC, h, ⟨clearAir, rfl⟩⟩)

/-! ### The office of two, and what it settles -/

/-- Two workers sharing the office: `false` smokes, `true` does not. -/
@[expose] public def officeNonSmoker (i : Bool) : Prop := i = true

/-- **Print's Definition 3.1 remark, inhabited.** *"An EF that is derived from a
constitution by (3.1) might not be superadditive"* — print says this and gives no
example. Here is one, and it is print's own Example 2.7.

The smoker alone may have the office smoky; the non-smoker alone may have it
clear; superadditivity would make the two of them together effective for the
intersection, which is empty, and the obligation says the office is clear
whenever they are both in the room. -/
public theorem not_superadditive_officeConstitution :
    ¬ Superadditive (smokeConstitution officeNonSmoker).induced := by
  intro hsup
  have hsmoker : ({smokyAir} : Set Air) ∈
      (smokeConstitution officeNonSmoker).induced {false} := by
    rw [smokeConstitution_induced]
    refine smoky_mem_smokeAccess ⟨false, rfl⟩ ?_
    rintro ⟨i, hi, hns⟩
    rw [Set.mem_singleton_iff] at hi
    exact absurd (hi ▸ hns) (by simp [officeNonSmoker])
  have hnonsmoker : ({clearAir} : Set Air) ∈
      (smokeConstitution officeNonSmoker).induced {true} := by
    rw [smokeConstitution_induced]
    exact clear_mem_smokeAccess ⟨true, rfl⟩
  have hdisj : Disjoint ({false} : Set Bool) {true} := by simp
  have hbad := hsup {false} {true} {smokyAir} {clearAir} hdisj hsmoker hnonsmoker
  rw [smokeConstitution_induced] at hbad
  have hinter : ({smokyAir} : Set Air) ∩ {clearAir} = ∅ := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, h⟩
    exact absurd h (by decide)
  rw [hinter] at hbad
  rcases hbad with ⟨hC, -⟩ | ⟨-, -, hcl⟩ | ⟨-, -, hne⟩
  · exact hC ⟨true, Or.inr rfl⟩
  · exact absurd hcl (by simp)
  · exact absurd hne (by simp)

/-- **So no game form represents print's Example 2.7**, by
`Represents.superadditive`. Print never claims one does; the example is offered
to illustrate obligations and symmetry, and this records what it also shows. -/
public theorem not_represents_officeConstitution (G : GameForm Bool Air) :
    ¬ Represents G (smokeConstitution officeNonSmoker) :=
  fun h ↦ not_superadditive_officeConstitution h.superadditive

/-! ## Print's Example 2.10: Gibbard's society, and Example 3.8's computation

Journal pages 71 and 74. `N = {A, E, J}` — Angelina, Edwin, and the judge — and
three social states `{0, e, j}`: she stays single, she marries Edwin, she marries
the judge. Two rights, `ρ₁` to remain single and `ρ₂` to marry, assigned

> `α(∅) = ∅`, `α(A) = α(E) = α(J) = ρ₁`, `α({A, E}) = α({A, J}) = ρ`,
> `α({E, J}) = ρ₁`, `α(N) = ρ`,

and print computes `γ` from *"the usual interpretation"* with `B⁺` for the
supersets of `B`. `up` is that notation.

**Two closed forms replace print's table of eighteen values.** The right to
remain single is a **veto**: Angelina can refuse any marriage, Edwin can refuse
to marry her, the judge likewise, and what a coalition holding `ρ₁` is effective
for is the upward closure of the states nobody in it vetoes — `unvetoed`. The
right to marry is a **pair**: it forces a wedding only for a coalition holding
both Angelina and the intended partner. Every one of print's values is an
instance, and `mem_gibbardConstitution_induced` is the closed form the eight
checks run on, coalition by coalition.

**The `= A` shorthand again.** Print writes `γ(∅, θ) = {0, e, j}` and
`γ(S, ∅) = {0, e, j}` where page 69's standing assumption writes `{A}`, exactly
as Examples 2.3 and 2.7 do. `Standing` asks for the family, and
`gibbardConstitution_standing` proves it.

**Example 3.8 is (3.1) at this society**, journal page 74, and print ends it with
*"as the reader may easily verify, `E(·)` is superadditive and monotonic w.r.t.
the alternatives. Hence, by Theorem 3.5, `E` is representable."* Those two
verifications are `gibbardInduced_superadditive` and
`gibbardConstitution_upwardClosed`. The conclusion drawn from them is **not**
recorded: it uses the sufficiency half of Theorem 3.5, which this cluster does
not have.
-/

/-- Print's three members. -/
public abbrev Person : Type := Fin 3

/-- Angelina. -/
@[expose] public def angelina : Person := 0

/-- Edwin. -/
@[expose] public def edwin : Person := 1

/-- The judge. -/
@[expose] public def judge : Person := 2

/-- Print's three social states `0`, `e`, `j`. -/
public abbrev Status : Type := Fin 3

/-- Print's `0`: Angelina remains single. -/
@[expose] public def single : Status := 0

/-- Print's `e`: she marries Edwin. -/
@[expose] public def weddedEdwin : Status := 1

/-- Print's `j`: she marries the judge. -/
@[expose] public def weddedJudge : Status := 2

/-- Print's two rights. `false` is `ρ₁`, the right to remain single; `true` is
`ρ₂`, the right to marry. -/
public abbrev MarriageRight : Type := Bool

/-- `ρ₁`. -/
@[expose] public def remainSingle : MarriageRight := false

/-- `ρ₂`. -/
@[expose] public def mayMarry : MarriageRight := true

/-- **Print's `B⁺`**: the sets containing `B`. -/
@[expose] public def up (S : Set Status) : Set (Set Status) := {B | S ⊆ B}

/-- **Print's `α`.** Every non-empty coalition holds the right to remain single;
the right to marry needs Angelina and a partner. -/
@[expose] public def gibbardAssign (C : Set Person) : Set MarriageRight :=
  {r | (r = remainSingle ∧ C.Nonempty) ∨
       (r = mayMarry ∧ angelina ∈ C ∧ (edwin ∈ C ∨ judge ∈ C))}

/-- **The states no member of the coalition can refuse.** Angelina can refuse
either marriage, Edwin can refuse to marry her, the judge likewise, and nobody
can stop her staying single. -/
@[expose] public def unvetoed (C : Set Person) : Set Status :=
  {x | x = single
     ∨ (x = weddedEdwin ∧ angelina ∉ C ∧ edwin ∉ C)
     ∨ (x = weddedJudge ∧ angelina ∉ C ∧ judge ∉ C)}

/-- **Print's `γ`.** The whole state space always; the unvetoed states when the
coalition holds `ρ₁`; and a wedding when it holds `ρ₂` together with both
parties to it. -/
@[expose] public def gibbardAccess (C : Set Person) (θ : Set MarriageRight) :
    Set (Set Status) :=
  {B | B = Set.univ
     ∨ (remainSingle ∈ θ ∧ unvetoed C ⊆ B)
     ∨ (mayMarry ∈ θ ∧ angelina ∈ C ∧ edwin ∈ C ∧ weddedEdwin ∈ B)
     ∨ (mayMarry ∈ θ ∧ angelina ∈ C ∧ judge ∈ C ∧ weddedJudge ∈ B)}

/-- **Print's Example 2.10 as a constitution.** -/
@[expose] public def gibbardConstitution : Constitution Person Status MarriageRight where
  assign := gibbardAssign
  access := gibbardAccess

/-- The empty coalition vetoes nothing, so every state survives. -/
public theorem unvetoed_empty : unvetoed (∅ : Set Person) = Set.univ := by
  ext x
  simp only [unvetoed, Set.mem_ofPred_eq, Set.mem_univ, iff_true, Set.notMem_empty,
    not_false_eq_true, and_true]
  fin_cases x <;> simp [single, weddedEdwin, weddedJudge]

/-- Print's standing assumptions hold of it. -/
public theorem gibbardConstitution_standing : gibbardConstitution.Standing where
  assign_empty := by
    ext r
    simp [gibbardConstitution, gibbardAssign]
  access_empty_coalition := by
    intro θ
    ext B
    simp only [gibbardConstitution, gibbardAccess, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      unvetoed_empty, Set.notMem_empty]
    constructor
    · rintro (rfl | ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩)
      · rfl
      · exact (Set.univ_subset_iff.mp h).symm ▸ rfl
      · exact absurd h (by simp)
      · exact absurd h (by simp)
    · rintro rfl
      exact Or.inl rfl
  access_empty_rights := by
    intro C
    ext B
    simp only [gibbardConstitution, gibbardAccess, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      Set.notMem_empty, false_and, or_false]

/-- **(3.3) holds**, which is the first of print's two verifications in Example
3.8: every one of `γ`'s four disjuncts is closed upwards. -/
public theorem gibbardConstitution_monotoneAlternatives :
    gibbardConstitution.MonotoneAlternatives := by
  rintro C θ B B' (rfl | ⟨hθ, h⟩ | ⟨hθ, ha, he, hw⟩ | ⟨hθ, ha, hj, hw⟩) hBB'
  · exact Or.inl (Set.univ_subset_iff.mp hBB')
  · exact Or.inr (Or.inl ⟨hθ, h.trans hBB'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hθ, ha, he, hBB' hw⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hθ, ha, hj, hBB' hw⟩))

/-- And on the induced effectivity function, which is where Example 3.8 states
it. -/
public theorem gibbardConstitution_upwardClosed :
    UpwardClosed gibbardConstitution.induced :=
  fun C B B' hB hBB' ↦
    gibbardConstitution_monotoneAlternatives C (gibbardConstitution.assign C) B B' hB hBB'

/-! ### (3.1) at this society — print's Example 3.8 -/

/-- **A larger coalition vetoes more**, so the unvetoed states shrink. -/
public theorem unvetoed_antitone {C D : Set Person} (h : C ⊆ D) :
    unvetoed D ⊆ unvetoed C := by
  rintro x (hx | ⟨hx, ha, he⟩ | ⟨hx, ha, hj⟩)
  · exact Or.inl hx
  · exact Or.inr (Or.inl ⟨hx, fun hc ↦ ha (h hc), fun hc ↦ he (h hc)⟩)
  · exact Or.inr (Or.inr ⟨hx, fun hc ↦ ha (h hc), fun hc ↦ hj (h hc)⟩)

/-- Angelina in the room vetoes both weddings, so only staying single survives. -/
public theorem unvetoed_of_mem_angelina {C : Set Person} (h : angelina ∈ C) :
    unvetoed C = {single} := by
  ext x
  simp only [unvetoed, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun hx ↦ hx.elim id (fun hx ↦ hx.elim (fun hx ↦ absurd h hx.2.1)
    (fun hx ↦ absurd h hx.2.1)), Or.inl⟩

/-- Every non-empty coalition holds the right to remain single. -/
public theorem remainSingle_mem_gibbardAssign {C : Set Person} (h : C.Nonempty) :
    remainSingle ∈ gibbardAssign C := Or.inl ⟨rfl, h⟩

/-- And the right to marry needs Angelina together with one of the two men. -/
public theorem mayMarry_mem_gibbardAssign_iff {C : Set Person} :
    mayMarry ∈ gibbardAssign C ↔ angelina ∈ C ∧ (edwin ∈ C ∨ judge ∈ C) := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, ha, hm⟩)
    · exact absurd h (by decide)
    · exact ⟨ha, hm⟩
  · rintro ⟨ha, hm⟩
    exact Or.inr ⟨rfl, ha, hm⟩

/-- **(3.1) at this society, in closed form.** A non-empty coalition is effective
for a set when the set contains every state nobody in it vetoes, or when the
coalition holds both parties to one of the two weddings and the set contains
that wedding. -/
public theorem mem_gibbardConstitution_induced {C : Set Person} (hC : C.Nonempty)
    (B : Set Status) :
    B ∈ gibbardConstitution.induced C ↔
      unvetoed C ⊆ B
        ∨ (angelina ∈ C ∧ edwin ∈ C ∧ weddedEdwin ∈ B)
        ∨ (angelina ∈ C ∧ judge ∈ C ∧ weddedJudge ∈ B) := by
  simp only [Constitution.induced, gibbardConstitution, gibbardAccess, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | ⟨-, h⟩ | ⟨-, ha, he, hw⟩ | ⟨-, ha, hj, hw⟩)
    · exact Or.inl (Set.subset_univ _)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨ha, he, hw⟩)
    · exact Or.inr (Or.inr ⟨ha, hj, hw⟩)
  · rintro (h | ⟨ha, he, hw⟩ | ⟨ha, hj, hw⟩)
    · exact Or.inr (Or.inl ⟨remainSingle_mem_gibbardAssign hC, h⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨mayMarry_mem_gibbardAssign_iff.mpr ⟨ha, Or.inl he⟩, ha, he, hw⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨mayMarry_mem_gibbardAssign_iff.mpr ⟨ha, Or.inr hj⟩, ha, hj, hw⟩))

/-- **`E(∅) = {A}`**, print's first value, which is the standing assumption. -/
public theorem gibbardInduced_empty :
    gibbardConstitution.induced (∅ : Set Person) = {Set.univ} :=
  gibbardConstitution.induced_empty gibbardConstitution_standing

/-- **`E(A) = {0}⁺`.** Angelina alone can refuse both suitors and nothing else. -/
public theorem gibbardInduced_angelina :
    gibbardConstitution.induced {angelina} = up {single} := by
  have hA : angelina ∈ ({angelina} : Set Person) := rfl
  ext B
  rw [mem_gibbardConstitution_induced (C := {angelina}) ⟨angelina, hA⟩,
    unvetoed_of_mem_angelina hA]
  refine ⟨fun h ↦ h.elim id (fun h ↦ h.elim (fun h ↦ absurd h.2.1 ?_)
    (fun h ↦ absurd h.2.1 ?_)), Or.inl⟩
  · exact fun hc ↦ absurd (hc : edwin = angelina) (by decide)
  · exact fun hc ↦ absurd (hc : judge = angelina) (by decide)

/-- **`E(E) = {0, j}⁺`.** Edwin can refuse to marry her, and can do nothing
about the judge. -/
public theorem gibbardInduced_edwin :
    gibbardConstitution.induced {edwin} = up {single, weddedJudge} := by
  have hE : edwin ∈ ({edwin} : Set Person) := rfl
  have hunv : unvetoed ({edwin} : Set Person) = {single, weddedJudge} := by
    ext x
    simp only [unvetoed, Set.mem_ofPred_eq]
    constructor
    · rintro (hx | ⟨-, -, he⟩ | ⟨hx, -, -⟩)
      · exact Or.inl hx
      · exact absurd hE he
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr (Or.inr ⟨hx, fun hc ↦ absurd (hc : angelina = edwin) (by decide),
          fun hc ↦ absurd (hc : judge = edwin) (by decide)⟩)
  ext B
  rw [mem_gibbardConstitution_induced (C := {edwin}) ⟨edwin, hE⟩, hunv]
  refine ⟨fun h ↦ h.elim id (fun h ↦ h.elim (fun h ↦ absurd h.1 ?_)
    (fun h ↦ absurd h.1 ?_)), Or.inl⟩
  · exact fun hc ↦ absurd (hc : angelina = edwin) (by decide)
  · exact fun hc ↦ absurd (hc : angelina = edwin) (by decide)

/-- **`E(J) = {0, e}⁺`**, the judge's mirror of Edwin's. -/
public theorem gibbardInduced_judge :
    gibbardConstitution.induced {judge} = up {single, weddedEdwin} := by
  have hJ : judge ∈ ({judge} : Set Person) := rfl
  have hunv : unvetoed ({judge} : Set Person) = {single, weddedEdwin} := by
    ext x
    simp only [unvetoed, Set.mem_ofPred_eq]
    constructor
    · rintro (hx | ⟨hx, -, -⟩ | ⟨-, -, hj⟩)
      · exact Or.inl hx
      · exact Or.inr hx
      · exact absurd hJ hj
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr (Or.inl ⟨hx, fun hc ↦ absurd (hc : angelina = judge) (by decide),
          fun hc ↦ absurd (hc : edwin = judge) (by decide)⟩)
  ext B
  rw [mem_gibbardConstitution_induced (C := {judge}) ⟨judge, hJ⟩, hunv]
  refine ⟨fun h ↦ h.elim id (fun h ↦ h.elim (fun h ↦ absurd h.1 ?_)
    (fun h ↦ absurd h.1 ?_)), Or.inl⟩
  · exact fun hc ↦ absurd (hc : angelina = judge) (by decide)
  · exact fun hc ↦ absurd (hc : angelina = judge) (by decide)

/-- **`E({E, J}) = {0}⁺`.** The two men together can refuse her, and that is all
they can do: neither wedding is theirs to force. -/
public theorem gibbardInduced_edwin_judge :
    gibbardConstitution.induced {edwin, judge} = up {single} := by
  have hE : edwin ∈ ({edwin, judge} : Set Person) := Or.inl rfl
  have hJ : judge ∈ ({edwin, judge} : Set Person) := Or.inr rfl
  have hA : angelina ∉ ({edwin, judge} : Set Person) := by
    rintro (hc | hc)
    · exact absurd (hc : angelina = edwin) (by decide)
    · exact absurd (hc : angelina = judge) (by decide)
  have hunv : unvetoed ({edwin, judge} : Set Person) = {single} := by
    ext x
    simp only [unvetoed, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ h.elim id (fun h ↦ h.elim (fun h ↦ absurd hE h.2.2)
      (fun h ↦ absurd hJ h.2.2)), Or.inl⟩
  ext B
  rw [mem_gibbardConstitution_induced (C := {edwin, judge}) ⟨edwin, hE⟩, hunv]
  exact ⟨fun h ↦ h.elim id (fun h ↦ h.elim (fun h ↦ absurd h.1 hA)
    (fun h ↦ absurd h.1 hA)), Or.inl⟩

/-- `B⁺` at a single state is membership. -/
public theorem mem_up_singleton {x : Status} {B : Set Status} :
    B ∈ up {x} ↔ x ∈ B :=
  ⟨fun h ↦ h rfl, fun h _ hy ↦ hy ▸ h⟩

/-- **`E({A, E}) = {0}⁺ ∪ {e}⁺`.** Angelina and Edwin together can hold the
wedding, or she can stay single. -/
public theorem gibbardInduced_angelina_edwin :
    gibbardConstitution.induced {angelina, edwin} = up {single} ∪ up {weddedEdwin} := by
  have hA : angelina ∈ ({angelina, edwin} : Set Person) := Or.inl rfl
  have hE : edwin ∈ ({angelina, edwin} : Set Person) := Or.inr rfl
  have hJ : judge ∉ ({angelina, edwin} : Set Person) := by
    rintro (hc | hc)
    · exact absurd (hc : judge = angelina) (by decide)
    · exact absurd (hc : judge = edwin) (by decide)
  ext B
  rw [mem_gibbardConstitution_induced (C := {angelina, edwin}) ⟨angelina, hA⟩,
    unvetoed_of_mem_angelina hA]
  simp only [Set.mem_union, mem_up_singleton]
  constructor
  · rintro (h | ⟨-, -, hw⟩ | ⟨-, hj, -⟩)
    · exact Or.inl (h rfl)
    · exact Or.inr hw
    · exact absurd hj hJ
  · rintro (h | h)
    · exact Or.inl fun _ hy ↦ hy ▸ h
    · exact Or.inr (Or.inl ⟨hA, hE, h⟩)

/-- **`E({A, J}) = {0}⁺ ∪ {j}⁺`**, the same with the judge. -/
public theorem gibbardInduced_angelina_judge :
    gibbardConstitution.induced {angelina, judge} = up {single} ∪ up {weddedJudge} := by
  have hA : angelina ∈ ({angelina, judge} : Set Person) := Or.inl rfl
  have hJ : judge ∈ ({angelina, judge} : Set Person) := Or.inr rfl
  have hE : edwin ∉ ({angelina, judge} : Set Person) := by
    rintro (hc | hc)
    · exact absurd (hc : edwin = angelina) (by decide)
    · exact absurd (hc : edwin = judge) (by decide)
  ext B
  rw [mem_gibbardConstitution_induced (C := {angelina, judge}) ⟨angelina, hA⟩,
    unvetoed_of_mem_angelina hA]
  simp only [Set.mem_union, mem_up_singleton]
  constructor
  · rintro (h | ⟨-, he, -⟩ | ⟨-, -, hw⟩)
    · exact Or.inl (h rfl)
    · exact absurd he hE
    · exact Or.inr hw
  · rintro (h | h)
    · exact Or.inl fun _ hy ↦ hy ▸ h
    · exact Or.inr (Or.inr ⟨hA, hJ, h⟩)

/-- **`E(N) = {0}⁺ ∪ {e}⁺ ∪ {j}⁺`**, print's last value: between the three of
them any outcome can be settled. -/
public theorem gibbardInduced_univ :
    gibbardConstitution.induced Set.univ =
      up {single} ∪ up {weddedEdwin} ∪ up {weddedJudge} := by
  ext B
  rw [mem_gibbardConstitution_induced (C := Set.univ) ⟨angelina, trivial⟩,
    unvetoed_of_mem_angelina (Set.mem_univ angelina)]
  simp only [Set.mem_union, mem_up_singleton]
  constructor
  · rintro (h | ⟨-, -, hw⟩ | ⟨-, -, hw⟩)
    · exact Or.inl (Or.inl (h rfl))
    · exact Or.inl (Or.inr hw)
    · exact Or.inr hw
  · rintro ((h | h) | h)
    · exact Or.inl fun _ hy ↦ hy ▸ h
    · exact Or.inr (Or.inl ⟨trivial, trivial, h⟩)
    · exact Or.inr (Or.inr ⟨trivial, trivial, h⟩)

/-- **Superadditivity**, the second of print's two verifications in Example 3.8
and the one it leaves to the reader.

Three of the nine coalition pairs are vacuous, because a wedding needs Angelina
and two disjoint coalitions cannot both contain her. The pair that does the work
is a veto against a wedding: if one coalition forces a wedding, the other
contains neither party to it, so that wedding is among the states it does not
veto and lies in its set too. -/
public theorem gibbardInduced_superadditive :
    Superadditive gibbardConstitution.induced := by
  intro C₁ C₂ B₁ B₂ hd h₁ h₂
  have hdl := Set.disjoint_left.mp hd
  have hdr := Set.disjoint_right.mp hd
  rcases Set.eq_empty_or_nonempty C₁ with rfl | hC₁
  · rw [gibbardInduced_empty, Set.mem_singleton_iff] at h₁
    subst h₁
    simpa using h₂
  rcases Set.eq_empty_or_nonempty C₂ with rfl | hC₂
  · rw [gibbardInduced_empty, Set.mem_singleton_iff] at h₂
    subst h₂
    simpa using h₁
  obtain ⟨w₁, hw₁⟩ := hC₁
  rw [mem_gibbardConstitution_induced ⟨w₁, hw₁⟩] at h₁
  obtain ⟨w₂, hw₂⟩ := hC₂
  rw [mem_gibbardConstitution_induced ⟨w₂, hw₂⟩] at h₂
  rw [mem_gibbardConstitution_induced ⟨w₁, Or.inl hw₁⟩]
  rcases h₁ with hu₁ | ⟨ha₁, he₁, hb₁⟩ | ⟨ha₁, hj₁, hb₁⟩
  · rcases h₂ with hu₂ | ⟨ha₂, he₂, hb₂⟩ | ⟨ha₂, hj₂, hb₂⟩
    · exact Or.inl fun x hx ↦
        ⟨hu₁ (unvetoed_antitone Set.subset_union_left hx),
         hu₂ (unvetoed_antitone Set.subset_union_right hx)⟩
    · exact Or.inr (Or.inl ⟨Or.inr ha₂, Or.inr he₂,
        hu₁ (Or.inr (Or.inl ⟨rfl, hdr ha₂, hdr he₂⟩)), hb₂⟩)
    · exact Or.inr (Or.inr ⟨Or.inr ha₂, Or.inr hj₂,
        hu₁ (Or.inr (Or.inr ⟨rfl, hdr ha₂, hdr hj₂⟩)), hb₂⟩)
  · rcases h₂ with hu₂ | ⟨ha₂, -, -⟩ | ⟨ha₂, -, -⟩
    · exact Or.inr (Or.inl ⟨Or.inl ha₁, Or.inl he₁, hb₁,
        hu₂ (Or.inr (Or.inl ⟨rfl, hdl ha₁, hdl he₁⟩))⟩)
    · exact absurd ha₂ (hdl ha₁)
    · exact absurd ha₂ (hdl ha₁)
  · rcases h₂ with hu₂ | ⟨ha₂, -, -⟩ | ⟨ha₂, -, -⟩
    · exact Or.inr (Or.inr ⟨Or.inl ha₁, Or.inl hj₁, hb₁,
        hu₂ (Or.inr (Or.inr ⟨rfl, hdl ha₁, hdl hj₁⟩))⟩)
    · exact absurd ha₂ (hdl ha₁)
    · exact absurd ha₂ (hdl ha₁)

end AISafetyAtlas.Examples.Sovereignty
