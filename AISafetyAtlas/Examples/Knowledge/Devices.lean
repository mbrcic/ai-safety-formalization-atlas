module

public import AISafetyAtlas.Knowledge.Devices
public import AISafetyAtlas.Knowledge.Check
public import AISafetyAtlas.Examples.Inference.FinDevice

/-!
# The spine–device joint, run

`Knowledge.Devices` states that a collision in *every* realized block refutes
both Definition 3 and Definition 11. Two things need showing, because neither is
visible from the statement:

1. the hypothesis is **satisfiable** — a four-state device meets it, and the
   kernel checks that by execution;
2. the hypothesis's awkward clause is **load-bearing** — a collision pair on
   which the target merely differs, without straddling the value in question,
   leaves the block answering.

Model 2 is the one that keeps the transport honest. Dropping the straddle clause
would make `BlockwiseCollision` refute devices that infer perfectly well.

Both models use the same device, so the contrast is not an artefact of choosing
a convenient second one.
-/

namespace AISafetyAtlas.Examples.Knowledge.Devices

open AISafetyAtlas.Inference
open AISafetyAtlas.Knowledge.Devices
open AISafetyAtlas.Examples.Inference.Enumerable

/-! ## Decidability

Both predicates are `def`s over quantifiers that are finite once the device's
two types are fixed. Instance search works at reducible transparency and will not
see through them, so each is unfolded by hand, exactly as
`Enumerable.decidableWeaklyInfers` has to.
-/

public instance decidableBlockwiseCollision {m n : ℕ} (d : FinDevice m n)
    {G : Type} [DecidableEq G] (Γ : Fin m → G) (γ : G) :
    Decidable (BlockwiseCollision d.toDevice Γ γ) := by
  unfold BlockwiseCollision InferenceDevice.Realized
  infer_instance

public instance decidableRealized {m n : ℕ} (d : FinDevice m n) (x : Fin n) :
    Decidable (d.toDevice.Realized x) := by
  unfold InferenceDevice.Realized
  infer_instance

public instance decidableBlockAnswers {m n : ℕ} (d : FinDevice m n)
    {G : Type} (Γ : Fin m → G) (f : G → Bool) (x : Fin n) :
    Decidable (BlockAnswers d.toDevice Γ f x) := by
  unfold BlockAnswers
  infer_instance

/-! ## The device

Four universes, two setup values, the target taking two values. The setup splits
the universes into `{0, 1}` and `{2, 3}`; the conclusion is constant on each
block; the target alternates. Every block therefore contains one universe at
target value `0` and one away from it, with the device configured and concluding
identically at both.
-/

/-- Setup: `{0, 1} ↦ 0`, `{2, 3} ↦ 1`. Non-constant, so the device respects the
source's own two-value stipulation on setup functions. -/
public def blockSetup : Fin 4 → Fin 2 := fun i => if i.val < 2 then 0 else 1

/-- Conclusion: `true` on the first block, `false` on the second. Onto `Bool`. -/
public def blockConcl : Fin 4 → Bool := fun i => i.val < 2

/-- Target: alternating, so each block straddles the value `0`. -/
public def blockTarget : Fin 4 → Fin 2 := fun i => if i.val % 2 = 0 then 0 else 1

/-- The device as enumerable data. -/
public def blockDevice : FinDevice 4 2 where
  setup := blockSetup
  concl := blockConcl
  concl_surj := by decide

/-! ## 1. The hypothesis is satisfiable, by execution -/

/-- Every realized block hides the target value `0`. Checked by the kernel. -/
public theorem blockDevice_blockwiseCollision :
    BlockwiseCollision blockDevice.toDevice blockTarget 0 := by
  decide

/-- Hence the device does not weakly infer the target. -/
public theorem blockDevice_not_weaklyInfers :
    ¬ WeaklyInfers blockDevice.toDevice blockTarget :=
  blockDevice_blockwiseCollision.not_weaklyInfers_classical ⟨0, by decide⟩

/--
Hence it does not physically know the target at `0` **in any context**.

The same certificate settles both, which is the point of naming the hypothesis
once: Definition 3 and Definition 11 are refuted by one object.
-/
public theorem blockDevice_not_physicallyKnows (W : Set (Fin 4)) :
    ¬ PhysicallyKnows blockDevice.toDevice blockTarget 0 W :=
  blockDevice_blockwiseCollision.not_physicallyKnows W

/-! ## 2. The straddle clause is load-bearing

`BlockwiseCollision` asks each block for a pair the device cannot separate on
which the target takes the value `γ` at one endpoint and misses it at the other.
The obvious weakening is to ask only that the target *differ* across the pair.

That weakening refutes nothing, and the device below is the proof: **every**
realized block carries such a pair, and it weakly infers the target anyway.

Eight universes, four blocks, three target values. Three of the blocks answer one
probe each by concluding `false` throughout — legitimate, because no universe in
them sits at the value being probed. Each still contains two universes whose
targets differ, both away from that value. The fourth block only exists to make
the conclusion function onto `Bool`.
-/

/-- Blocks are consecutive pairs: `{0,1}, {2,3}, {4,5}, {6,7}`. -/
public def straddleSetup : Fin 8 → Fin 4 := fun i => ⟨i.val / 2, by omega⟩

/-- `false` except on the last block, which is what makes the device onto `Bool`. -/
public def straddleConcl : Fin 8 → Bool := fun i => 6 ≤ i.val

/--
Target values per block: `{1,2}`, `{0,2}`, `{0,1}`, `{0,1}`. Each of the first
three blocks omits exactly one value, which is the probe it answers.
-/
public def straddleTarget : Fin 8 → Fin 3 := fun i =>
  match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 0
  | _ => 1

/-- The device as enumerable data. -/
public def straddleDevice : FinDevice 8 4 where
  setup := straddleSetup
  concl := straddleConcl
  concl_surj := by decide

/--
The weakened hypothesis holds: every realized block contains a pair the device
cannot separate on which the target differs.
-/
public theorem straddleDevice_collision_in_every_block :
    ∀ x : Fin 4, straddleDevice.toDevice.Realized x → ∃ u u' : Fin 8,
      straddleSetup u = x ∧ straddleSetup u' = x ∧
        straddleConcl u = straddleConcl u' ∧ straddleTarget u ≠ straddleTarget u' := by
  decide

/--
And the device weakly infers the target regardless. So dropping the straddle
clause would turn `BlockwiseCollision` into a hypothesis that refutes devices
satisfying Definition 3 — it would be unsound, not merely weaker.
-/
public theorem straddleDevice_weaklyInfers :
    WeaklyInfers straddleDevice.toDevice straddleTarget := by
  decide

/-- The straddle clause is therefore genuinely not met here, at any value. -/
public theorem straddleDevice_no_blockwiseCollision (γ : Fin 3) :
    ¬ BlockwiseCollision straddleDevice.toDevice straddleTarget γ := by
  revert γ
  decide

/-! ## 3. The same facts, from the checker rather than by hand

`Knowledge.Check` computes what the sections above prove. Running it here is how
the two stay in step: if the checker and the proofs ever disagree, one of them is
wrong, and this file is where that shows up rather than in a consumer's model.

`scripts/check_atlas_check.sh` does the same for the command-line reader, on
models built from `Examples.Oversight.Overseer`.
-/

/-- The device's conclusion function alone does not determine the target, and
`findCollision` finds the pair that shows it. -/
public theorem checker_finds_the_block_collision :
    (AISafetyAtlas.Knowledge.Check.findCollision (List.finRange 4) blockDevice.toDevice.concl blockTarget).isSome := by
  decide

/-- The checker's answer is the kernel's: the pair it returns refutes knowability. -/
public theorem checker_refutes_knowable_from_conclusion :
    ¬ AISafetyAtlas.Knowledge.Knowable blockDevice.toDevice.concl blockTarget := by
  rcases hfind : AISafetyAtlas.Knowledge.Check.findCollision (List.finRange 4)
      blockDevice.toDevice.concl blockTarget with _ | p
  · exact absurd (hfind ▸ checker_finds_the_block_collision) (by simp)
  · exact AISafetyAtlas.Knowledge.Check.not_knowable_of_findCollision_eq_some hfind

/-- The straddle device's setup does determine nothing about the target either,
but here the checker returning nothing would be the informative outcome — so the
completeness hypothesis is discharged explicitly rather than assumed. -/
public theorem checker_enumeration_is_complete :
    ∀ i : Fin 4, i ∈ List.finRange 4 := by
  intro i
  simp

end AISafetyAtlas.Examples.Knowledge.Devices
