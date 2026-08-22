module

public import AISafetyAtlas.Causal.SparseEncoding

/-!
# Worked model of the sparse monomial code

`AISafetyAtlas.Causal.SparseEncoding` supplies the syntax MAIS-O24's
construction-time clause is stated in. This module runs it, because the two
properties that clause leans on are easy to assert and easy to get wrong.

* The code is **prefix-free**, so a concatenation of codewords parses back. The
  checks below are the smallest cases where that could fail: `0` encodes as the
  empty digit string, so its codeword is the separator alone, and two of those in
  a row must still be two codewords rather than one.
* The code is **injective**, which is what makes *"the machine outputs the
  encoding of the list"* a statement about the list rather than about a string
  that happens to collide with it.

The decoder is exercised too, on the one polynomial whose syntax is forced: the
empty monomial list is the zero polynomial.
-/

namespace AISafetyAtlas.Examples.Causal.SparseEncoding

open AISafetyAtlas.Causal

/-! ## Codewords -/

/-- `0` has no binary digits, so its codeword is the separator alone. This is the
edge case a length-prefixed code would have to special-case and a self-delimiting
one does not. -/
public theorem encodeNat_zero : encodeNat 0 = [CodeSym.sep] := by
  simp [encodeNat, encodeBoolList]

/-- `1` is a single digit. -/
public theorem encodeNat_one : encodeNat 1 = [CodeSym.one, CodeSym.sep] := by
  simp [encodeNat, encodeBoolList, CodeSym.ofBool]

/-- `2` is `0` then `1`, least significant digit first. -/
public theorem encodeNat_two :
    encodeNat 2 = [CodeSym.zero, CodeSym.one, CodeSym.sep] := rfl

/-! ## Prefix-freeness at its sharpest case -/

/-- Two zeros in a row parse as two codewords, not one. `encodeNat 0` is a single
separator, so `[sep, sep]` is the shortest string where a code that merely
terminated its words could go wrong. -/
public theorem encodeNat_zero_zero :
    encodeNat 0 ++ encodeNat 0 = [CodeSym.sep, CodeSym.sep] := by
  simp [encodeNat, encodeBoolList]

/-- And the prefix property recovers both. -/
public theorem prefix_splits_zero_zero {a b : ℕ} {x y : List CodeSym}
    (h : encodeNat a ++ x = encodeNat b ++ y) : a = b ∧ x = y :=
  isPrefixCode_encodeNat a b x y h

/-- Distinct naturals have distinct codewords. -/
public theorem encodeNat_injective : Function.Injective encodeNat :=
  isPrefixCode_encodeNat.injective

/-! ## Rationals -/

/-- A rational's codeword is its numerator's followed by its denominator's, so
sign, magnitude and denominator are all recoverable. -/
public theorem encodeRat_one :
    encodeRat 1 = CodeSym.zero :: encodeNat 1 ++ encodeNat 1 := by
  simp [encodeRat, encodeInt]

/-- Negative rationals carry the sign symbol. -/
public theorem encodeRat_neg_one :
    encodeRat (-1) = CodeSym.one :: encodeNat 1 ++ encodeNat 1 := by
  norm_num [encodeRat, encodeInt]

/-! ## The output code -/

/-- The whole output code is injective **as soon as the name code is**, which is
the property the construction clause needs: a machine that writes this string
wrote the syntax of this list. The hypothesis is where the name code earns its
keep — with an arbitrary naming this would be a statement about a string. -/
public theorem output_injective {σ : Type} {f : σ → List CodeSym}
    (hf : IsPrefixCode f) : Function.Injective (encodeSparseList f) :=
  encodeSparseList_injective hf

/-- The empty list of polynomials encodes as the codeword for length `0`. -/
public theorem encodeSparseList_nil {σ : Type} (f : σ → List CodeSym) :
    encodeSparseList f ([] : List (SparsePoly σ)) = encodeNat 0 := by
  simp [encodeSparseList, encodeList]

/-! ## Decoding -/

/-- Empty syntax is the zero polynomial. This is the one value of the decoder
that is forced, and it is what makes an empty certificate the degenerate case
rather than an ill-formed one. -/
public theorem ofSparsePoly_nil_eq_zero {σ : Type} :
    ofSparsePoly ([] : SparsePoly σ) = 0 :=
  ofSparsePoly_nil

/-- A single monomial with no variables is its coefficient. -/
public theorem ofSparsePoly_const {σ : Type} (c : ℚ) :
    ofSparsePoly [(c, [])] = (MvPolynomial.C c : MvPolynomial σ ℚ) := by
  simp [ofSparsePoly, ofSparseMonomial, sparseExponents]

/-- **The decoder reads the names off the syntax.** A monomial naming the
variable `x` with exponent `1` decodes to `X x`, whatever `x` is — the syntax
determines the polynomial with no bijection interposed. -/
public theorem ofSparsePoly_single {σ : Type} (x : σ) :
    ofSparsePoly [((1 : ℚ), [(x, 1)])] = (MvPolynomial.X x : MvPolynomial σ ℚ) := by
  simp [ofSparsePoly, ofSparseMonomial, sparseExponents, MvPolynomial.X]

end AISafetyAtlas.Examples.Causal.SparseEncoding
