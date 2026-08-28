module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# A canonical self-delimiting code, and sparse monomial syntax

A self-delimiting code over a three-symbol alphabet, the composition lemmas that
build compound encoders from atomic ones, and the sparse polynomial syntax those
encoders spell out. Source coding, not a domain notion: no atlas definition is
imported and `σ` is an arbitrary variable type.

The consumer that motivated it is MAIS-A2 `prob:effective`, which requires the
**construction time** of its polynomial list to be polynomial in `S`, *"using
sparse monomial encoding"*. A machine cannot be asked to output a `MvPolynomial`;
it outputs a list of symbols. So the clause needs a fixed syntax, and this module
supplies one; `AISafetyAtlas.Causal.EffectiveGenericity` instantiates it. Where a
design choice below was made for that consumer, it is named as such.

**Why the encoding is fixed here rather than quantified with the machine.**
A solution predicate of the shape *"there exist a machine **and an encoding**
such that …"* is satisfiable by advice: choose an encoding that already carries
the answer, and the machine only has to copy its input. Print asks for a
construction, not for a lookup, so the code below is a definition and every
statement about construction time uses it.

**Why binary and not unary.** The size clause bounds coefficient bit lengths by a
polynomial in `S`, so a solution's coefficients are `poly(S)` bits long. A unary
code would make their transcript exponentially long in `S`, and no machine could
write it within `poly(S)` steps — a unary code would make `prob:effective`
unsatisfiable for reasons having nothing to do with the mathematics. `encodeNat`
is therefore base two, least significant digit first.

**The code is prefix-free**, which is what `IsPrefixCode` records: reading one
codeword off the front of a stream determines both the value and the remainder.
That is the property that makes concatenation unambiguous, and it composes —
`IsPrefixCode.pair` and `IsPrefixCode.list` build the compound encoders from the
atomic ones. Without it, *"the machine outputs the encoding of the list"* would
be satisfiable by a machine that outputs the encoding of a different list which
happens to collide.
-/

namespace AISafetyAtlas.InformationTheory

/-! ## The alphabet -/

/-- The output alphabet: two digits and a separator.

Three symbols rather than two because the separator is what makes the code
self-delimiting without a length-prefix escape convention. A two-symbol alphabet
would work as well and is not more faithful — print fixes no alphabet, only that
the syntax is a sparse monomial one. -/
public inductive CodeSym
  | zero
  | one
  | sep
  deriving DecidableEq, Inhabited

/-- The alphabet is finite, as a Turing-machine tape alphabet must be. -/
public instance : Fintype CodeSym :=
  ⟨{CodeSym.zero, CodeSym.one, CodeSym.sep}, by intro x; cases x <;> decide⟩

/-- Digits, as distinct from the separator. -/
@[expose] public def CodeSym.isDigit : CodeSym → Bool
  | .sep => false
  | _ => true

/-- A bit as a digit symbol. -/
@[expose] public def CodeSym.ofBool : Bool → CodeSym
  | false => .zero
  | true => .one

public theorem CodeSym.ofBool_injective : Function.Injective CodeSym.ofBool := by
  intro a b h
  cases a <;> cases b <;> simp_all [CodeSym.ofBool]

public theorem CodeSym.isDigit_ofBool (b : Bool) : (CodeSym.ofBool b).isDigit := by
  cases b <;> rfl

/-! ## Prefix codes -/

/-- `f` is a **prefix code**: one codeword read off the front of a stream
determines both the value it encodes and everything after it.

This is the property that makes a concatenation of codewords unambiguous, and it
is what the O24 construction clause needs: without it, *"the machine outputs
`encode (Q input)`"* could be met by a machine emitting the encoding of some
other list whose code happens to agree. -/
@[expose] public def IsPrefixCode {α : Type*} (f : α → List CodeSym) : Prop :=
  ∀ a b (x y : List CodeSym), f a ++ x = f b ++ y → a = b ∧ x = y

public theorem IsPrefixCode.injective {α : Type*} {f : α → List CodeSym}
    (h : IsPrefixCode f) : Function.Injective f := by
  intro a b hab
  exact (h a b [] [] (by simp [hab])).1

/-! ## Bit strings

Every code below is a bit string followed by the separator, so the prefix-free
property is proved **once** here. A new codeword then costs an injectivity proof
about bit strings rather than a second `takeWhile` argument, which is what makes
naming a structured variable — `IsPrefixCode.ofBoolList` — cheap enough to do
with a definition instead of an existential. -/

/-- A bit string, terminated by the separator. -/
@[expose] public def encodeBoolList (l : List Bool) : List CodeSym :=
  l.map CodeSym.ofBool ++ [CodeSym.sep]

/-- Splitting a digit string at its terminating separator. -/
public theorem takeWhile_digits_append {l : List CodeSym}
    (h : ∀ a ∈ l, a.isDigit) (r : List CodeSym) :
    (l ++ CodeSym.sep :: r).takeWhile CodeSym.isDigit = l ∧
      (l ++ CodeSym.sep :: r).dropWhile CodeSym.isDigit = CodeSym.sep :: r := by
  induction l with
  | nil => simp [CodeSym.isDigit]
  | cons a t ih =>
      have hat : a.isDigit := h a (List.mem_cons_self ..)
      have htail : ∀ b ∈ t, b.isDigit := fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
      obtain ⟨h1, h2⟩ := ih htail
      refine ⟨?_, ?_⟩
      · simpa [List.takeWhile_cons, hat] using congrArg (a :: ·) h1
      · simpa [List.dropWhile_cons, hat] using h2

/-- Reading a terminated bit string off the front of a stream recovers both the
bits and the remainder. -/
public theorem encodeBoolList_takeWhile (l : List Bool) (r : List CodeSym) :
    (encodeBoolList l ++ r).takeWhile CodeSym.isDigit = l.map CodeSym.ofBool ∧
      (encodeBoolList l ++ r).dropWhile CodeSym.isDigit = CodeSym.sep :: r := by
  have hdig : ∀ s ∈ l.map CodeSym.ofBool, s.isDigit := by
    intro s hs
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hs
    exact CodeSym.isDigit_ofBool t
  have := takeWhile_digits_append (l := l.map CodeSym.ofBool) hdig r
  simpa [encodeBoolList, List.append_assoc] using this

public theorem isPrefixCode_encodeBoolList : IsPrefixCode encodeBoolList := by
  intro a b x y hxy
  obtain ⟨ha1, ha2⟩ := encodeBoolList_takeWhile a x
  obtain ⟨hb1, hb2⟩ := encodeBoolList_takeWhile b y
  have hbits : a.map CodeSym.ofBool = b.map CodeSym.ofBool := by
    rw [← ha1, ← hb1, hxy]
  refine ⟨List.map_injective_iff.mpr CodeSym.ofBool_injective hbits, ?_⟩
  have : CodeSym.sep :: x = CodeSym.sep :: y := by rw [← ha2, ← hb2, hxy]
  exact List.cons_injective this

/-- **Any injective bit-string presentation is a prefix code.** This is the
combinator every structured name below is built with: writing a code for a new
kind of variable means saying which bit string names it and proving that reading
determines it, with no second prefix argument. -/
public theorem IsPrefixCode.ofBoolList {α : Type*} {g : α → List Bool}
    (hg : Function.Injective g) : IsPrefixCode fun a ↦ encodeBoolList (g a) := by
  intro a b x y h
  obtain ⟨hbits, hxy⟩ := isPrefixCode_encodeBoolList _ _ _ _ h
  exact ⟨hg hbits, hxy⟩

/-! ## Natural numbers -/

/-- A natural number in base two, least significant digit first, terminated by
the separator. `0` encodes as the empty digit string, since `Nat.bits 0 = []`. -/
@[expose] public def encodeNat (n : ℕ) : List CodeSym :=
  encodeBoolList (Nat.bits n)

/-- `Nat.bits` is injective, through `Nat.digits`' left inverse. -/
public theorem bits_injective : Function.Injective Nat.bits := by
  intro m n h
  have hd : Nat.digits 2 m = Nat.digits 2 n := by
    rw [Nat.digits_two_eq_bits, Nat.digits_two_eq_bits, h]
  calc m = Nat.ofDigits 2 (Nat.digits 2 m) := (Nat.ofDigits_digits 2 m).symm
    _ = Nat.ofDigits 2 (Nat.digits 2 n) := by rw [hd]
    _ = n := Nat.ofDigits_digits 2 n

public theorem isPrefixCode_encodeNat : IsPrefixCode encodeNat :=
  IsPrefixCode.ofBoolList bits_injective

/-! ## Composition -/

/-- Two prefix codes read in sequence form a prefix code on pairs. -/
public theorem IsPrefixCode.pair {α β : Type*} {f : α → List CodeSym} {g : β → List CodeSym}
    (hf : IsPrefixCode f) (hg : IsPrefixCode g) :
    IsPrefixCode fun p : α × β ↦ f p.1 ++ g p.2 := by
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ x y h
  simp only [List.append_assoc] at h
  obtain ⟨h1, h2⟩ := hf _ _ _ _ h
  obtain ⟨h3, h4⟩ := hg _ _ _ _ h2
  exact ⟨by rw [h1, h3], h4⟩

/-- A list, encoded as its length followed by its elements. -/
@[expose] public def encodeList {α : Type*} (f : α → List CodeSym) (l : List α) :
    List CodeSym :=
  encodeNat l.length ++ l.flatMap f

/-- The length prefix makes a list of codewords a codeword. -/
public theorem IsPrefixCode.list {α : Type*} {f : α → List CodeSym} (hf : IsPrefixCode f) :
    IsPrefixCode (encodeList f) := by
  have key : ∀ (l m : List α), l.length = m.length →
      ∀ x y : List CodeSym, l.flatMap f ++ x = m.flatMap f ++ y → l = m ∧ x = y := by
    intro l
    induction l with
    | nil =>
        intro m hm x y h
        cases m with
        | nil => simpa using h
        | cons _ _ => simp at hm
    | cons a t ih =>
        intro m hm x y h
        cases m with
        | nil => simp at hm
        | cons b s =>
            simp only [List.flatMap_cons, List.append_assoc] at h
            obtain ⟨hab, hrest⟩ := hf _ _ _ _ h
            obtain ⟨hts, hxy⟩ := ih s (by simpa using hm) x y hrest
            exact ⟨by rw [hab, hts], hxy⟩
  intro a b x y h
  simp only [encodeList, List.append_assoc] at h
  obtain ⟨hlen, hrest⟩ := isPrefixCode_encodeNat _ _ _ _ h
  exact key a b hlen x y hrest

/-! ## Integers and rationals -/

/-- An integer as a sign symbol followed by its absolute value. -/
@[expose] public def encodeInt (i : ℤ) : List CodeSym :=
  (if i < 0 then CodeSym.one else CodeSym.zero) :: encodeNat i.natAbs

public theorem isPrefixCode_encodeInt : IsPrefixCode encodeInt := by
  intro a b x y h
  simp only [encodeInt, List.cons_append] at h
  obtain ⟨hsign, hrest⟩ := List.cons_eq_cons.mp h
  obtain ⟨habs, hxy⟩ := isPrefixCode_encodeNat _ _ _ _ hrest
  refine ⟨?_, hxy⟩
  rcases lt_or_ge a 0 with ha | ha <;> rcases lt_or_ge b 0 with hb | hb
  · omega
  · simp [ha, hb.not_gt] at hsign
  · simp [ha.not_gt, hb] at hsign
  · omega

/-- A rational as its numerator and its denominator. -/
@[expose] public def encodeRat (q : ℚ) : List CodeSym :=
  encodeInt q.num ++ encodeNat q.den

public theorem isPrefixCode_encodeRat : IsPrefixCode encodeRat := by
  intro a b x y h
  simp only [encodeRat, List.append_assoc] at h
  obtain ⟨hnum, hrest⟩ := isPrefixCode_encodeInt _ _ _ _ h
  obtain ⟨hden, hxy⟩ := isPrefixCode_encodeNat _ _ _ _ hrest
  exact ⟨Rat.ext hnum hden, hxy⟩

/-! ## Sparse monomial syntax

This is print's *"sparse monomial encoding"*: a polynomial is the list of the
monomials it actually carries, each a coefficient together with the list of
`(variable, exponent)` pairs whose exponent is nonzero. A dense encoding would
instead write `(deg+1)^S` coefficients, which is what "sparse" excludes and what
would make the size bounds unmeetable.

**Variables are named, not numbered.** A monomial carries the variables
themselves, in whatever type the polynomials are written over, rather than
indices into an `S`-element enumeration. The alternative — syntax over `Fin S`
plus a bijection `σ ≃ Fin S` — reintroduces exactly the advice this module
exists to exclude, since an unrestricted bijection carries `log₂(S!)` bits of
per-instance choice about *which* coordinate each monomial is about, and a
machine emitting fixed syntax could then "construct" a certificate it never
computed. The bijection is an encoding, and the rule for encodings is the one
above: definitions, not existentials. So the name code is a parameter here, and
every instantiation supplies a definition for it. -/

/-- One monomial over the variables `σ`: a coefficient and the variables it
uses. -/
public abbrev SparseMonomial (σ : Type*) := ℚ × List (σ × ℕ)

/-- One polynomial: its list of monomials. -/
public abbrev SparsePoly (σ : Type*) := List (SparseMonomial σ)

/-- A `(variable, exponent)` pair, under a name code for the variables. -/
@[expose] public def encodeVarPow {σ : Type*} (f : σ → List CodeSym) (p : σ × ℕ) :
    List CodeSym :=
  f p.1 ++ encodeNat p.2

public theorem isPrefixCode_encodeVarPow {σ : Type*} {f : σ → List CodeSym}
    (hf : IsPrefixCode f) : IsPrefixCode (encodeVarPow f) :=
  hf.pair isPrefixCode_encodeNat

/-- One monomial. -/
@[expose] public def encodeMonomial {σ : Type*} (f : σ → List CodeSym)
    (m : SparseMonomial σ) : List CodeSym :=
  encodeRat m.1 ++ encodeList (encodeVarPow f) m.2

public theorem isPrefixCode_encodeMonomial {σ : Type*} {f : σ → List CodeSym}
    (hf : IsPrefixCode f) : IsPrefixCode (encodeMonomial f) :=
  isPrefixCode_encodeRat.pair (isPrefixCode_encodeVarPow hf).list

/-- One polynomial, in sparse monomial form. -/
@[expose] public def encodeSparsePoly {σ : Type*} (f : σ → List CodeSym)
    (p : SparsePoly σ) : List CodeSym :=
  encodeList (encodeMonomial f) p

public theorem isPrefixCode_encodeSparsePoly {σ : Type*} {f : σ → List CodeSym}
    (hf : IsPrefixCode f) : IsPrefixCode (encodeSparsePoly f) :=
  (isPrefixCode_encodeMonomial hf).list

/-- The whole output: `Q^G_1, …, Q^G_r`, each in sparse monomial form. -/
@[expose] public def encodeSparseList {σ : Type*} (f : σ → List CodeSym)
    (l : List (SparsePoly σ)) : List CodeSym :=
  encodeList (encodeSparsePoly f) l

public theorem isPrefixCode_encodeSparseList {σ : Type*} {f : σ → List CodeSym}
    (hf : IsPrefixCode f) : IsPrefixCode (encodeSparseList f) :=
  (isPrefixCode_encodeSparsePoly hf).list

/-- The output code is injective, which is what makes *"the machine outputs the
encoding of the list"* a statement about the list. -/
public theorem encodeSparseList_injective {σ : Type*} {f : σ → List CodeSym}
    (hf : IsPrefixCode f) : Function.Injective (encodeSparseList f) :=
  (isPrefixCode_encodeSparseList hf).injective

/-! ## Reading syntax back as a polynomial

The machine writes syntax; `prob:effective` asks it to construct **polynomials**.
These read one back. No numbering is involved: the syntax already names its
variables, so decoding is a definition on the nose rather than a definition
relative to a supplied bijection.

Note the direction. A statement could instead fix a serialization of each
polynomial and ask the machine to reproduce it — but the sparse form of a
polynomial is a *set* of monomials, so serializing it would fix an arbitrary
order and demand the machine reproduce that order too. That is an accidental
demand print does not make. Asking instead that the machine's output *decode to*
the right list keeps the polynomials pinned and leaves the byte order free. The
order of the list `Q₁, …, Q_r` is not free: print numbers those. -/

/-- The exponent vector a list of `(variable, exponent)` pairs names. Repeats add,
which is the reading that makes `decode` total without a well-formedness side
condition. -/
@[expose] public noncomputable def sparseExponents {σ : Type*} (l : List (σ × ℕ)) :
    σ →₀ ℕ :=
  (l.map fun p ↦ Finsupp.single p.1 p.2).sum

/-- The polynomial one monomial names. -/
@[expose] public noncomputable def ofSparseMonomial {σ : Type*} (m : SparseMonomial σ) :
    MvPolynomial σ ℚ :=
  MvPolynomial.monomial (sparseExponents m.2) m.1

/-- The polynomial a sparse form names. -/
@[expose] public noncomputable def ofSparsePoly {σ : Type*} (p : SparsePoly σ) :
    MvPolynomial σ ℚ :=
  (p.map ofSparseMonomial).sum

/-- The empty syntax names the zero polynomial. -/
@[simp] public theorem ofSparsePoly_nil {σ : Type*} :
    ofSparsePoly ([] : SparsePoly σ) = 0 := rfl

end AISafetyAtlas.InformationTheory
