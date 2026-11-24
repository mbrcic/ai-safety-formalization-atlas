import AISafetyAtlas.Wireheading.SelfMod

/-!
Orseau and Ring (2011), §3, p. 6, survival agent. Its utility is one when
the current program is the initial program and zero otherwise. Its horizon is
the reinforcement-learning agent's window, which is one when `k - t ≤ m`
and zero otherwise. The cited declarations are `SelfMod.survivalUtility`
and `SelfMod.survivalAgent`.

The map sends the initial code to one admissible one-symbol program and every
other code to a second admissible program. It maps history entries and leaves
time and window length as given. At empty history the current code is the
initial code.

Checked: `lake env lean docs/provenance/transfers/044-survival-agent.lean`
-/

namespace Transfer044

open AISafetyAtlas.Wireheading.AgentEquations AISafetyAtlas.Wireheading.SelfMod

def Program {Symbol : Type*} (valid : List Symbol → Prop) (bound : ℕ) :=
  {p : List Symbol // valid p ∧ p.length < bound}

instance {Symbol : Type*} [DecidableEq Symbol] {valid : List Symbol → Prop} {bound : ℕ} :
    DecidableEq (Program valid bound) :=
  inferInstanceAs (DecidableEq {p : List Symbol // valid p ∧ p.length < bound})

def PrintStatement {Symbol Act Obs : Type*} [DecidableEq Symbol]
    {valid : List Symbol → Prop} {bound : ℕ} (c0 : Program valid bound)
    (h : History (CompAct Act (Program valid bound)) Obs) (m t k : ℕ) (u w : ℝ) : Prop :=
  let ct := (h.getLast?.map (fun p ↦ p.1.2)).getD c0
  u = (if ct = c0 then 1 else 0) ∧ w = (if k - t ≤ m then 1 else 0)

def LeanStatement {Code Act Obs : Type*} [DecidableEq Code] (c0 : Code)
    (h : History (CompAct Act Code) Obs) (m t k : ℕ) (u w : ℝ) : Prop :=
  u = survivalUtility c0 h ∧ u = (survivalAgent c0 m).utility h ∧
    w = (survivalAgent c0 m : Agent (CompAct Act Code) Obs).horizon t k

abbrev PrintCode := Program (fun p : List Bool ↦ p.length = 1) 2

def word (b : Bool) : PrintCode := ⟨[b], by simp⟩

def encode {Code : Type*} [DecidableEq Code] (c0 c : Code) : PrintCode :=
  if c = c0 then word false else word true

def mapHistory {Code Code' Act Obs : Type*} (f : Code → Code')
    (h : History (CompAct Act Code) Obs) : History (CompAct Act Code') Obs :=
  h.map fun p ↦ ((p.1.1, f p.1.2), p.2)

def phi {Code Act Obs : Type*} [DecidableEq Code] (c0 : Code)
    (h : History (CompAct Act Code) Obs) : History (CompAct Act PrintCode) Obs :=
  mapHistory (encode c0) h

theorem encode_eq_initial {Code : Type*} [DecidableEq Code] (c0 c : Code) :
    encode c0 c = word false ↔ c = c0 := by
  by_cases h : c = c0
  · simp [encode, h]
  · have hw : word true ≠ word false := by
      intro heq
      have := congrArg Subtype.val heq
      simp [word] at this
    simp [encode, h, hw]

private theorem compare {Code Symbol Act Obs : Type*} [DecidableEq Code] [DecidableEq Symbol]
    {valid : List Symbol → Prop} {bound : ℕ}
    (c0 : Code) (d0 : Program valid bound) (f : Code → Program valid bound)
    (hf : ∀ c, f c = d0 ↔ c = c0)
    (h : History (CompAct Act Code) Obs) (m t k : ℕ) (u w : ℝ) :
    LeanStatement c0 h m t k u w ↔ PrintStatement d0 (mapHistory f h) m t k u w := by
  have htime : k - t ≤ m ↔ k ≤ t + m := by omega
  cases hh : h.getLast? <;>
    simp [LeanStatement, PrintStatement, mapHistory, List.getLast?_map, hh, survivalUtility,
      survivalAgent, htime, hf]

theorem defining_condition {Code Act Obs : Type*} [DecidableEq Code] (c0 : Code)
    (h : History (CompAct Act Code) Obs) (m t k : ℕ) (u w : ℝ) :
    LeanStatement c0 h m t k u w ↔ PrintStatement (word false) (phi c0 h) m t k u w :=
  compare c0 (word false) (encode c0) (encode_eq_initial c0) h m t k u w

theorem lean_of_print {Code Act Obs : Type*} [DecidableEq Code] (c0 : Code)
    (h : History (CompAct Act Code) Obs) (m t k : ℕ) (u w : ℝ) :
    PrintStatement (word false) (phi c0 h) m t k u w → LeanStatement c0 h m t k u w :=
  (defining_condition c0 h m t k u w).mpr

theorem print_of_lean {Symbol Act Obs : Type*} [DecidableEq Symbol]
    {valid : List Symbol → Prop} {bound : ℕ} (c0 : Program valid bound)
    (h : History (CompAct Act (Program valid bound)) Obs) (m t k : ℕ) (u w : ℝ) :
    LeanStatement c0 h m t k u w → PrintStatement c0 h m t k u w := by
  have hmap : mapHistory id h = h := by
    induction h with
    | nil => rfl
    | cons p ps ih =>
      change p :: mapHistory id ps = p :: ps
      rw [ih]
  intro hLean
  have hPrint := (compare c0 c0 id (fun _ ↦ Iff.rfl) h m t k u w).mp hLean
  simpa only [hmap] using hPrint

end Transfer044
