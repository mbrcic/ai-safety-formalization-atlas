module

public import AISafetyAtlas.Compositional.Knowability

/-!
# A worked network where the view decodes the state

`AISafetyAtlas.Compositional.Networks.knowable_runFor` asserts that a decoder
exists. A positive knowability statement is exactly the kind that can be true
because the setting is degenerate — the proof below even has a branch for the
case where nothing inhabits it — so this module exhibits a network where it is
not.

The network is two nodes, one port each, pointing at each other. The algorithm
xors in the message it receives, so states really do move. Two configurations:
one constant, one that labels the nodes apart.

`allTrue_same_state` is the point. Its conclusion is a fact about `runFor`, and
its proof never mentions `runFor_eq_of_view_eq` — it obtains the decoder from
`knowable_runFor` and applies it twice. That is the import edge from
`Compositional` to `Knowledge` doing the work *in this proof*.

Not doing work that could not be done otherwise: the network is two symmetric
nodes under a constant configuration, so a routine induction reaches the same
conclusion without the kernel. `rfl` does not close it — `n` is a variable, so
`runFor` does not reduce — so the example is not vacuous, but it demonstrates
the mechanism rather than a necessity.
-/

namespace AISafetyAtlas.Examples.Compositional

open AISafetyAtlas.Compositional.Networks

/-- Two nodes, one port each, each pointing at the other. -/
@[expose] public def pair : Network (Fin 2) 1 where
  port v _ := v + 1

/-- Every node emits its state and xors in what it receives. -/
@[expose] public def parity : Algorithm Bool Bool 1 where
  send s _ := s
  update s m := xor s (m 0)

/-- The configuration that labels the two nodes alike. -/
@[expose] public def allTrue : Config (Fin 2) Bool := fun _ => true

/-- The configuration that labels them apart. -/
@[expose] public def apart : Config (Fin 2) Bool := fun v => v = 0

/-- Under `allTrue` every view is the constant `true`, at every depth. -/
public theorem allTrue_view (n : ℕ) (u : Fin 2) :
    view pair allTrue n u = fun _ => true := rfl

/--
**The decoder does the work.** Both nodes are in the same state after any number
of rounds, and this is derived from `knowable_runFor` — the decoder is applied to
each node's view, and the two views are equal.
-/
public theorem allTrue_same_state (n : ℕ) :
    runFor pair parity allTrue n 0 = runFor pair parity allTrue n 1 := by
  obtain ⟨decoder, hdec⟩ := knowable_runFor pair parity allTrue n
  rw [hdec 0, hdec 1, allTrue_view, allTrue_view]

/-- Under `apart` the views already differ at depth zero, so the observation is
not constant and the decoder is not free to be. -/
public theorem apart_view_ne : view pair apart 0 0 ≠ view pair apart 0 1 := by
  intro h
  have := congrFun h ⟨[], Nat.le_refl 0⟩
  simp [view, pathTo, apart] at this

end AISafetyAtlas.Examples.Compositional
