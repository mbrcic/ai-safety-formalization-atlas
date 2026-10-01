module

public import AISafetyAtlas.Sovereignty.CogSov

/-!
# The predicate is inhabited, refutable, and blind to how much beliefs move

`cogSov_holds` and `not_cogSov_of_service_failure` are the two checks a
definition with this many parameters owes: it is satisfiable, and it is not
satisfied by everything. The first exhibits a defender meeting both clauses;
the second is a system whose only admissible defender emits an observation
outside the required service, so no choice of defender rescues it.

`magnitude_separation` instantiates `C4` at the smallest interesting data: the
endorsed evidence is a bit, the belief is that bit, and two protected
transitions agree everywhere on the endorsed interface while only one of them
ignores the unendorsed channel.
-/

namespace AISafetyAtlas.Examples.Sovereignty.CogSov

open AISafetyAtlas.Sovereignty

/-! ## The predicate is satisfiable -/

/-- **A defender meeting both clauses.** The run set is the one the relational
specification asks for and every observation is authorized and serviceable. -/
public theorem cogSov_holds :
    CogSov (Set.univ : Set Unit) (fun (_ : Unit) (_ : Unit) => (Set.univ : Set Unit))
      {(Set.univ : Set Unit)} (fun _ _ (_ : Unit) (_ : Unit) => (Set.univ : Set Unit))
      Set.univ (fun _ => Set.univ) () :=
  cogSov_of_witness (D := ()) (Set.mem_univ _) rfl fun _ _ => by simp

/-! ## And it is not satisfied by everything -/

/-- **A system no defender rescues.** The required service excludes the
observation the system emits, so the second clause fails at every admissible
defender. -/
public theorem not_cogSov_of_service_failure :
    ¬ CogSov (Set.univ : Set Unit) (fun (_ : Unit) (_ : Unit) => (Set.univ : Set Unit))
      {(Set.univ : Set Unit)} (fun _ _ (_ : Unit) (_ : Unit) => (Set.univ : Set Bool))
      Set.univ (fun _ => ({true} : Set Bool)) () := by
  refine not_cogSov fun D _ => Or.inr ⟨(), (), fun hsub => ?_⟩
  have : (false : Bool) ∈ ({true} : Set Bool) := (hsub (Set.mem_univ false)).2
  simp at this


/-! ## Why subset-closure is a real question -/

/-- A relational specification that accepts the total run set **and nothing
less**. This is the smallest hyperproperty that is not subset-closed. -/
@[expose] public def topOnly : AISafetyAtlas.Compositional.Hyperproperties.Hyperproperty Bool :=
  {(Set.univ : Set Bool)}

/-- And it is not subset-closed, which is what the next theorem turns on. -/
public theorem topOnly_not_subsetClosed :
    ¬ AISafetyAtlas.Compositional.Hyperproperties.SubsetClosed topOnly := by
  intro h
  have := h Set.univ rfl ∅ (Set.empty_subset _)
  have hne : (∅ : Set Bool) ≠ Set.univ := by
    intro hc
    exact absurd (hc ▸ Set.mem_univ true) (by simp)
  exact hne this

/--
**Deleting runs can destroy cognitive sovereignty**, at a specification that is
not subset-closed. The same implementation, the same defender class, the same
observations — only the composed run set shrinks, from everything to nothing,
and the predicate flips.

So `cogSov_mono_of_subsetClosed`'s hypothesis is load-bearing, and the open
question the module docstring records — whether `H` should be *required* to be
subset-closed — has a cost on the other side.
-/
public theorem shrinking_can_destroy_cogSov :
    CogSov (Set.univ : Set Unit) (fun (_ : Unit) (_ : Unit) => (Set.univ : Set Bool))
        topOnly (fun _ _ (_ : Unit) (_ : Unit) => (Set.univ : Set Unit))
        Set.univ (fun _ => Set.univ) ()
      ∧ ¬ CogSov (Set.univ : Set Unit) (fun (_ : Unit) (_ : Unit) => (∅ : Set Bool))
        topOnly (fun _ _ (_ : Unit) (_ : Unit) => (Set.univ : Set Unit))
        Set.univ (fun _ => Set.univ) () := by
  refine ⟨cogSov_of_witness (D := ()) (Set.mem_univ _) rfl fun _ _ => by simp, ?_⟩
  rintro ⟨D, -, hH, -⟩
  have hc : (∅ : Set Bool) = Set.univ := hH
  exact absurd (hc ▸ Set.mem_univ true) (by simp)

/-! ## `C4` at one bit -/

/-- **Two transitions, the same belief change, different authorship.** The
belief is the endorsed bit in both, so the magnitude of the change is
identical and maximal; only the first ignores the unendorsed channel. -/
public theorem magnitude_separation :
    ∃ F F' : Bool → Unit → Bool → Bool,
      (∀ e j u, F e j u = e) ∧ (∀ e j, F' e j true = e) ∧
        (∀ e j u u', F e j u = F e j u') ∧
          ¬ ∀ e j u u', F' e j u = F' e j u' :=
  magnitude_does_not_decide_authorship true false (by decide) (fun e _ => e) false
    ⟨true, (), by decide⟩

/-! ## And what subset-closure buys on the other side

`shrinking_can_destroy_cogSov` shows the hypothesis is load-bearing by removing
it. This is the same experiment with the hypothesis in place. -/

/-- A relational specification that accepts **every** run set. The largest
hyperproperty, and subset-closed for the reason every top element is. -/
@[expose] public def anyRuns :
    AISafetyAtlas.Compositional.Hyperproperties.Hyperproperty Bool :=
  Set.univ

/-- It is subset-closed. -/
public theorem anyRuns_subsetClosed :
    AISafetyAtlas.Compositional.Hyperproperties.SubsetClosed anyRuns :=
  fun _ _ _ _ => Set.mem_univ _

/--
**Deleting runs cannot destroy cognitive sovereignty when the specification is
subset-closed.**

Set this against `shrinking_can_destroy_cogSov`. The implementation, the
defender class, the observations, the required service and the shrinkage are
the same in both -- the run set goes from everything to nothing either way. The
only difference is which hyperproperty the runs are graded against, and the
predicate flips there and survives here.

So `cogSov_mono_of_subsetClosed` is not a technical convenience: subset-closure
is exactly what makes refinement safe, and Clarkson and Schneider's Theorem 1
(`subsetClosed_of_isHyperSafetyOp`) is what supplies it for hypersafety.
-/
public theorem shrinking_preserves_cogSov :
    CogSov (Set.univ : Set Unit) (fun (_ : Unit) (_ : Unit) => (∅ : Set Bool))
      anyRuns (fun _ _ (_ : Unit) (_ : Unit) => (Set.univ : Set Unit))
      Set.univ (fun _ => Set.univ) () :=
  cogSov_mono_of_subsetClosed anyRuns_subsetClosed (fun _ => Set.empty_subset _)
    (cogSov_of_witness (𝒟 := (Set.univ : Set Unit))
      (runs := fun (_ : Unit) (_ : Unit) => (Set.univ : Set Bool))
      (D := ()) (Set.mem_univ _) (Set.mem_univ _) fun _ _ => by simp)

end AISafetyAtlas.Examples.Sovereignty.CogSov
