module

public import AISafetyAtlas.Sovereignty.ConformityCheck
public import AISafetyAtlas.Knowledge.IncidentCount
public import AISafetyAtlas.Compositional.AgentNetwork
public import AISafetyAtlas.Fairness.Tradeoff
public import AISafetyAtlas.Sovereignty.Refusal
public import AISafetyAtlas.Sovereignty.AmendmentLog

/-!
# The practitioner layers, run

Each module here states a conditional obstruction, and a conditional obstruction
nothing satisfies is decoration. These are the instances.

* `rivalReqs` is a two-item checklist a system passes item by item and no single
  operating policy serves, decided by the executable searches rather than by
  hand.
* `bandReport` is an incident regime whose filings cannot distinguish one
  incident from two, so its published count is a property of the schema.
* `pairFleet` is two identical agents facing each other, where the symmetry that
  makes one evaluation cover both is the symmetry that stops either becoming the
  coordinator.
-/

namespace AISafetyAtlas.Examples.Practitioner

open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Knowledge
open AISafetyAtlas.Compositional

/-! ## Conformity: the checklist and the deployment disagree -/

/-- Two policies, one environment move, two outcomes: policy `0` yields outcome
`0` and policy `1` yields outcome `1`. -/
@[expose] public def twoPolicies : Fin 2 → Fin 1 → Fin 2 := fun a _ => a

/-- Two requirements that contradict each other. -/
@[expose] public def rivalReqs : List (Fin 2 → Bool) :=
  [fun x => x == 0, fun x => x == 1]

/-- **The checklist passes**, decided rather than argued. -/
public theorem rivalReqs_passesEach :
    Conformity.passesEachB twoPolicies rivalReqs = true := by decide

/-- **And no single policy serves the catalogue.** -/
public theorem rivalReqs_not_operable :
    Conformity.operableB twoPolicies rivalReqs = false := by decide

/-- So the checklist result really is `Demandwise`... -/
public theorem rivalReqs_demandwise :
    Demandwise (Conformity.tableGame twoPolicies) Conformity.operator
      (Conformity.reqSets rivalReqs) :=
  Conformity.demandwise_of_passesEachB rivalReqs_passesEach

/-- ...and the operability result really refutes `DemandwiseUniform`. Both
verdicts are certified, which is what makes the disagreement evidence. -/
public theorem rivalReqs_not_demandwiseUniform :
    ¬ DemandwiseUniform (Conformity.tableGame twoPolicies) Conformity.operator
      (Conformity.reqSets rivalReqs) :=
  Conformity.not_demandwiseUniform_of_operableB_eq_false rivalReqs_not_operable

/-! ## Incident counting: the schema decides the number -/

/-- Two deployments. The regime files a severity band; one deployment had a
single incident and the other had two. -/
@[expose] public def bandReport : IncidentCount.Reporting Bool Nat where
  report _ := 0
  count b := if b then 2 else 1

/-- The filings are identical. -/
public theorem bandReport_same : bandReport.report true = bandReport.report false := rfl

/-- The counts are not. -/
public theorem bandReport_differs : bandReport.count true ≠ bandReport.count false := by decide

/-- **So no counting rule over filings recovers the number.** -/
public theorem bandReport_count_not_determined :
    ¬ Knowable bandReport.report bandReport.count :=
  IncidentCount.count_not_determined_of_collision bandReport bandReport_same bandReport_differs

/-- **And every rule scores the two deployments alike while their counts
differ**, which is the statement that the published number is not a measurement
of incidents. -/
public theorem bandReport_not_a_measurement :
    ∀ rule : Nat → Nat,
      rule (bandReport.report true) = rule (bandReport.report false) ∧
        bandReport.count true ≠ bandReport.count false :=
  IncidentCount.count_is_not_a_measurement bandReport bandReport_same bandReport_differs

/-- A regime that files the count has no obstruction, so the positive half is not
a hypothesis nothing meets. -/
@[expose] public def honestReport : IncidentCount.Reporting Bool Nat where
  report b := if b then 2 else 1
  count b := if b then 2 else 1

/-- **And then a counting rule exists.** -/
public theorem honestReport_schema_fixes_it :
    ∃ rule : Nat → Nat, ∀ ω, honestReport.count ω = rule (honestReport.report ω) :=
  IncidentCount.schema_fixes_the_count honestReport
    (IncidentCount.knowable_of_report_carries_count honestReport
      (fun ω ω' h => by
        cases ω <;> cases ω' <;> simp_all [honestReport]))

/-! ## A fleet of two identical agents -/

/-- Two agents, one port each, pointed at each other. -/
@[expose] public def pairTopology : Networks.Network Bool 1 where
  port v _ := !v

/-- A program that does nothing, which is enough: the obstruction is about the
symmetry and not about the computation. -/
@[expose] public def inertProgram : Networks.Algorithm Unit Unit 1 where
  send _ _ := ()
  update s _ := s

/-- The fleet. -/
@[expose] public def pairFleet : AgentNetwork.Fleet Bool Unit Unit 1 where
  topology := pairTopology
  program := inertProgram
  initial := fun _ => ()

/-- **One evaluation covers the other agent**, since their views agree at every
depth in a fleet whose instances are interchangeable. -/
public theorem pairFleet_evaluation_transfers (n : Nat) (u v : Bool)
    (hview : Networks.SameView pairFleet.topology pairFleet.initial n u v) :
    Networks.runFor pairFleet.topology pairFleet.program pairFleet.initial n u
      = Networks.runFor pairFleet.topology pairFleet.program pairFleet.initial n v :=
  AgentNetwork.evaluating_one_covers_its_peers pairFleet n u v hview

/-- The swap: each agent is the other's only neighbour, and it moves both. -/
@[expose] public def swap : Networks.Automorphism pairTopology where
  toEquiv := Equiv.refl Bool |>.trans ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩
  port_equivariant := by intro v i; cases v <;> rfl

/-- It fixes no agent. -/
public theorem swap_moves_everything : ∀ v, swap.toEquiv v ≠ v := by decide

/-- **Both halves at one fleet: the evaluation transfers, and no agent becomes
the coordinator.** The same symmetry does both, which is the point. -/
public theorem pairFleet_symmetry_is_shared (n : Nat) (u v : Bool)
    (hview : Networks.SameView pairFleet.topology pairFleet.initial n u v) :
    Networks.runFor pairFleet.topology pairFleet.program pairFleet.initial n u
        = Networks.runFor pairFleet.topology pairFleet.program pairFleet.initial n v ∧
      ¬ Symmetry.HasUniqueLeader (fun _ : Unit => True)
        (Networks.runFor pairFleet.topology pairFleet.program pairFleet.initial n) :=
  AgentNetwork.symmetry_is_the_shared_cause pairFleet swap swap_moves_everything
    (fun _ => True) (fun _ => rfl) n u v hview

/-! ## Fairness: a population where all three conditions are unavailable -/

/-- Two feature vectors. Group `0` is concentrated on the low-risk one and
group `1` on the high-risk one, so the base rates differ while the risk at each
feature vector is the same for everybody. -/
public noncomputable def splitPopulation : Fairness.Instance (Fin 2) where
  p := fun σ => if σ = 0 then 1 / 4 else 3 / 4
  n := fun t σ => if (t = 0) = (σ = 0) then 4 else 0
  p_nonneg := by
    intro σ
    by_cases h : σ = 0
    · simp [h]
    · simp [h]; norm_num
  p_le_one := by
    intro σ
    by_cases h : σ = 0
    · simp [h]; norm_num
    · simp [h]; norm_num
  n_nonneg := by
    intro t σ
    by_cases h : (t = 0) = (σ = 0) <;> simp [h]

/-- **No risk assignment on this population is calibrated and balanced for both
classes.** Not "none that anyone has built": the quantifier is over all of them,
and the two escape hatches are shut by the population itself. -/
public theorem splitPopulation_no_fair_assignment
    (hμ : ∀ t, 0 < splitPopulation.μ t)
    (hμN : ∀ t, splitPopulation.μ t < splitPopulation.N t)
    (hperfect : ¬ Fairness.PerfectPrediction splitPopulation)
    (hbase : ¬ Fairness.EqualBaseRates splitPopulation) :
    ∀ R : Fairness.RiskAssignment (Fin 2) (Fin 1),
      ¬ (Fairness.Calibrated splitPopulation R ∧
          Fairness.BalancedNegative splitPopulation R ∧
          Fairness.BalancedPositive splitPopulation R) :=
  Fairness.cannot_have_all_three splitPopulation hμ hμN hperfect hbase

/-- And the other direction at the same population: any assignment that did meet
all three would force one of the two population facts. -/
public theorem splitPopulation_escape_is_the_population
    (hμ : ∀ t, 0 < splitPopulation.μ t)
    (hμN : ∀ t, splitPopulation.μ t < splitPopulation.N t)
    (R : Fairness.RiskAssignment (Fin 2) (Fin 1))
    (h : Fairness.Calibrated splitPopulation R ∧
        Fairness.BalancedNegative splitPopulation R ∧
        Fairness.BalancedPositive splitPopulation R) :
    Fairness.PerfectPrediction splitPopulation ∨
      Fairness.EqualBaseRates splitPopulation :=
  Fairness.population_escape_of_all_three splitPopulation hμ hμN R h

/-! ## A safety suite with a do-nothing pass

Three outcomes: refuse, answer helpfully, answer harmfully.
-/

/-- A service that always refuses. -/
@[expose] public def refuser : GameForm.{0, 0, 0} Bool (Fin 3) where
  strategy _ := Unit
  outcome _ := 0

/-- Everyone has a strategy. -/
public instance refuser_nonempty (i : Bool) : Nonempty (refuser.strategy i) := ⟨()⟩

/-- It is inert at the refusal. -/
public theorem refuser_inert : Inert refuser (0 : Fin 3) := fun _ => rfl

/-- The audit: safety says "not harmful", the deployment is for helpful answers. -/
@[expose] public def assistantAudit : Refusal.Audit (Fin 3) where
  mustHold := {{0, 1}}
  mustServe := {{1}}

/-- **The refusing service passes the whole safety suite and serves nothing.**
The defect is in the audit and no system had to be examined to see it. -/
public theorem assistantAudit_admits_refusal :
    RetainsFamily refuser refuser Set.univ Set.univ assistantAudit.mustHold ∧
      ¬ Demandwise refuser Set.univ assistantAudit.mustServe := by
  refine Refusal.safety_suite_admits_a_refusal assistantAudit refuser_inert
    (fun P hP => ?_) (R := {1}) rfl (by decide) Set.univ Set.univ
  obtain rfl : P = {0, 1} := hP
  exact Set.mem_insert _ _

/-- And the executable check agrees, on the same suite written as bit vectors. -/
public theorem assistantAudit_admitsRefusal_decides :
    Refusal.admitsRefusal [fun x : Fin 3 => x != 2] [fun x : Fin 3 => x == 1] = true := by
  decide

/-- A suite with no such outcome, so the check is not vacuously positive. -/
public theorem tightSuite_has_no_refusal_hole :
    Refusal.admitsRefusal
      [fun x : Fin 3 => x != 2, fun x : Fin 3 => x != 0] [fun x : Fin 3 => x == 1] = false := by
  decide

/-- **The checker's witness, extracted.** A `true` verdict names the outcome that
passes every safety property and misses a request, which is what makes it a
finding rather than a number. -/
public theorem assistantAudit_refusal_witness :
    ∃ x : Fin 3, (∀ P ∈ [fun x : Fin 3 => x != 2], P x = true) ∧
      ∃ R ∈ [fun x : Fin 3 => x == 1], R x = false :=
  Refusal.exists_refusal_hole_of_admitsRefusal assistantAudit_admitsRefusal_decides

/-- **And a `false` verdict really is the absence of one**, so the check is exact
in both directions rather than one-sided like the rest of the family. -/
public theorem tightSuite_no_outcome_is_a_hole :
    ∀ x : Fin 3, ¬ ((∀ P ∈ [fun x : Fin 3 => x != 2, fun x : Fin 3 => x != 0], P x = true) ∧
      ∃ R ∈ [fun x : Fin 3 => x == 1], R x = false) :=
  Refusal.not_exists_refusal_hole_of_admitsRefusal_eq_false tightSuite_has_no_refusal_hole

/-! ## A change log under a rule that permits everything -/

/-- **Every state is authorised under the permissive rule**, which is the fact the
absence below is read off. -/
public theorem permissive_reaches_everything (κ : Fin 3) :
    AuthorizedFrom (fun _ _ => True) (0 : Fin 3) κ :=
  AmendmentLog.log_shows_only_rule_compliance (0 : Fin 3) κ

/-- **No state is excluded**, so a complete log constrains nothing. -/
public theorem permissive_log_excludes_nothing :
    ¬ ∃ κ : Fin 3, ¬ AuthorizedFrom (fun _ _ => True) (0 : Fin 3) κ :=
  AmendmentLog.unbroken_chain_is_not_a_constraint (0 : Fin 3)

/-- **And a chain under a strict rule survives weakening**, which is the sense in
which the rule and not the record carries the assurance: the same log is
authorised under every weaker rule, including the one that permits everything. -/
public theorem strict_chain_is_permissive_chain (κ₀ κ : Fin 3)
    (h : AuthorizedFrom (fun a b => b = a + 1) κ₀ κ) :
    AuthorizedFrom (fun _ _ => True) κ₀ κ :=
  AmendmentLog.the_rule_carries_the_assurance (fun _ _ _ => trivial) κ₀ κ h

end AISafetyAtlas.Examples.Practitioner
