module

public import AISafetyAtlas.Compositional.Networks

/-!
# The automorphism action, at the cheapest network

`step_semiconj` had no worked instance: nothing in the tree built a
`Network`, an `Algorithm`, or an `Automorphism` of one. The cheapest
instance — no ports at all — makes `port_equivariant` vacuous and `send`/
`update` trivial, while still exercising the actual statement:
`Function.Semiconj` at a real (if degenerate) permutation action.
-/

namespace AISafetyAtlas.Examples.Compositional.Networks

open AISafetyAtlas.Compositional.Networks

/-- One node, no ports: the empty network. -/
public def trivialNetwork : Network Unit 0 where
  port := fun _ i => i.elim0

/-- The identity automorphism of the trivial network. `port_equivariant` is
vacuous, since there are no ports to preserve. -/
public def trivialAutomorphism : Automorphism trivialNetwork where
  toEquiv := Equiv.refl Unit
  port_equivariant := fun _ i => i.elim0

/-- The algorithm that sends and updates nothing, there being no ports. -/
public def trivialAlgorithm : Algorithm Unit Unit 0 where
  send := fun _ i => i.elim0
  update := fun s _ => s

/-- **The round action commutes with the automorphism action**, at the
trivial network. -/
public theorem trivialNetwork_step_semiconj :
    Function.Semiconj (fun c : Config Unit Unit => c ∘ trivialAutomorphism.toEquiv)
      (step trivialNetwork trivialAlgorithm) (step trivialNetwork trivialAlgorithm) :=
  step_semiconj trivialAutomorphism trivialAlgorithm

end AISafetyAtlas.Examples.Compositional.Networks
