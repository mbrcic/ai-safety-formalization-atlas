# Reactive Robot Verification Model

This document records the scope and provenance of
`AISafetyAtlas.Verification.Robot.action_safety_unverifiable`. The declaration
formalizes the **computability core** of Theorem 1 and Corollary 1 in Jan van
Leeuwen and Jiří Wiedermann, [*Impossibility Results for the Online Verification
of Ethical and Legal Behaviour of Robots*](https://web.archive.org/web/20220222045551/http://www.cs.uu.nl/groups/AD/UU-PCS-2021-02.pdf)
(Utrecht UU-PCS-2021-02, 2021). It does not claim to formalize the paper's
complete robotics language or a physical robot.

Local working copy of the PDF used for statement extraction (maintainer
workspace): `../2021 robot ethics limits.pdf`.

## Extracted paper statements (verbatim)

Source: §3.2, pages 15–17 of UU-PCS-2021-02. Hyphenation at line breaks is
normalized; wording is otherwise as in the paper.

### Definition 2 (structured programs)

A robot program ρ is said to be **structured** if the following two conditions
are satisfied:

- every command block β in the hyper-command of its plan-part consists of an
  optional preparatory (computational) section, followed by an action section
  β<sub>a</sub> that specifies the (instructions for the) action(s) to be
  performed by the robot, whenever the command block is scheduled for execution
  by the supervisory control of the hyper-command, and
- its act-part faithfully implements the execution of every "action
  specification" β<sub>a</sub> that it receives in its queue at runtime from the
  plan-part of ρ, i.e. without altering the semantics or properties of the
  specified actions.

### Definition 3 (non-trivial robot property)

A robot property *P* is called **non-trivial** if there are a robot *A*, a
structured program ρ, an alternative β<sub>a</sub>′ to every action segment
β<sub>a</sub> in ρ, and a corresponding modification of its act-part act<sub>ρ</sub>
into act<sub>ρ′</sub> such that

- when ρ is implemented on *A*, then the actions of *A* always satisfy *P*,
- when ρ would be modified, during its operation and at the beginning of a next
  iteration of its operational cycle, by replacing every action segment
  β<sub>a</sub> by the corresponding action segment β<sub>a</sub>′ and its
  act<sub>ρ</sub> by act<sub>ρ′</sub> (inheriting the settings of act<sub>ρ</sub>
  at the time of replacement), then
  - it remains a valid program and it continues to execute on *A* without
    interruption, but
  - its actions no longer all satisfy *P* in all situations, where the situations
    in which *P* is not satisfied occur with non-zero probability.

### Theorem 1

> Let *P* be any non-trivial robot property. There does not exist an algorithmic
> procedure that will enable an observer to tell, given an arbitrary robot with
> potentially unbounded memory, whether the actions of the robot always satisfy
> *P*.

### Corollary 1

> Let *P* be a non-trivial robot property. There does not exist an algorithmic
> procedure that will enable an observer to tell, given any robot (with
> potentially unbounded memory) that is programmed by a structured program,
> whether the actions of the robot always satisfy *P*.

Corollary 1 is immediate from the proof of Theorem 1 once one notes that every
constructed τ<sub>x</sub> is structured (paper, p. 17).

## What the paper proof actually does

The paper's argument (Theorem 1 proof, Fig. 1) is a classical reduction from the
**diagonal** halting set *K* = { *x* | φ<sub>*x*</sub>(*x*)↓ }. Outline:

1. **Assume** a total algorithmic observer that, for every robot program, decides
   whether its actions always satisfy *P*.
2. **Unpack non-triviality (Def. 3):** there exist a structured base program ρ
   whose actions always satisfy *P*, and a runtime switch of action segments /
   act-part to (ρ′, β<sub>a</sub>′) after which *P* fails with non-zero
   probability in some situations.
3. **Build τ<sub>x</sub>** (Fig. 1): Sense–Plan–Act program that
   - runs like ρ while a flag *b* is true;
   - in each operational cycle, advances a paced simulation of *M*<sub>*x*</sub>
     by a fixed number of steps (paper uses *c* := 100) so every cycle finishes
     in finite time;
   - if the simulation ever reports termination, sets *b* := false and thereafter
     runs the alternative (non-*P*) actions.
4. **Argue validity in their model:** τ<sub>x</sub> remains a valid robot program
   under hyper-command format, composition, re-initialization, and **potentially
   unbounded memory** for the TM configuration `des`.
5. **Reduction:** actions of τ<sub>x</sub> always satisfy *P* **iff** the program
   never switches **iff** *M*<sub>*x*</sub> does not halt on *x*.
6. **Contradiction:** a total observer would decide the complement of *K*, which
   is non-recursive.

**Logical polarity note.** The narrative in steps 5–6 is the intended one (always
*P* ⇔ non-halting). The printed line "iff *x* ∈ *K* with
*K* = {*x* | φ<sub>*x*</sub>(*x*)↓}" is inconsistent with that narrative and with
standard notation for *K*; the following sentence also refers to both *K* and
its complement being non-recursive. The atlas formalization follows the
narrative polarity (always acceptable ⇔ non-halting), not that inconsistent
membership line.

**Why the paper proof is longer than the Lean proof — not for show.**

| Paper work | Lean analogue |
|---|---|
| SPA language, hyper-commands, structured programs (Defs 1–2) | Abstract `Program`, predicate `structured` |
| Non-triviality as *existence of a switchable pair* (ρ, ρ′) (Def. 3) | *Assumed* as `SwitchingConstruction` (certificate) |
| Explicit construction of τ<sub>x</sub> (Fig. 1), pacing, memory | `compile : Code → Program` + `satisfies_iff_nonhalting` |
| Validity / composition arguments under the robotics model | `compiled_structured`, `computable_compile` |
| Diagonal *K* = {*x* \| φ<sub>*x*</sub>(*x*)↓} | Fixed-input `(eval source sourceInput).Dom` (equally undecidable) |
| Final reduction + "observer is total algorithm" | `Verifier` + composition + `halting_problem` |

So the bulk of the paper is **building and justifying the switching
construction inside a robotics programming model**. Once that construction
exists, the remainder is a short, standard reduction from an undecidable
halting set — exactly what Lean checks. The Lean development deliberately
**assumes** an effective `SwitchingConstruction` instead of mechanizing Def. 3
and Fig. 1, because the interesting modeling debt is "does this program class
admit such a τ?", not the last arithmetic of the reduction.

That is also why the registry relationship is **`RELATED`**, not `EXACT` /
`EQUIVALENT`: Lean proves the conditional core
"if a switching construction exists, then no total sound-and-complete verifier
exists," not the paper's full "every non-trivial *P* (Def. 3) yields such a
construction in the SPA model."

## Atlas representation

| Paper concept | Atlas representation |
|---|---|
| Robot program | An abstract, encodable type `Program` |
| Complete environmental circumstances, observations, and scheduling choices | An abstract type `Scenario` |
| Repeated operational cycles | Natural-number index `cycle` |
| Executed action | `behavior program scenario cycle : Action` |
| Every action has property *P* | `AlwaysSatisfies behavior acceptable program` |
| Structured robot programs | A predicate `structured : Program → Prop` |
| Hypothetical online observer or verifier | A total computable Boolean `Verifier` correct on structured programs |
| Program τ<sub>x</sub> (Fig. 1) | `SwitchingConstruction.compile` |
| Non-triviality (Def. 3) supplying (ρ, ρ′) | **Assumed**, not derived — folded into the existence of `SwitchingConstruction` |

`Behavior` is a total reactive trace, `Scenario → ℕ → Action`. A scenario may
carry the complete environment and observation history, so the interface does
not assume that the next action is independent of prior interaction. This is a
semantic interface: it deliberately does not prescribe sensors, actuators,
controllers, geometry, probability spaces, or a particular implementation
language.

The essential assumption is explicit. `SwitchingConstruction` certifies that
the chosen program class can computably embed an arbitrary source computation,
continue producing actions while that computation is simulated, and change
from an always-acceptable trace to a violating trace if the computation
halts. This is where the paper's potentially unbounded memory and
program-composition power enter the theorem.

The paper reduces from a diagonal halting problem. The Lean statement uses
Mathlib's equally undecidable fixed-input halting predicate and the atlas's
canonical `AISafetyAtlas.Computability.halting_problem` facade. This changes
the presentation of the source problem, not the reduction principle.

## Machine-checked conclusion

Given a `SwitchingConstruction`, there is no total computable Boolean verifier
that is both sound and complete for `AlwaysSatisfies` on every program selected
by `structured`. The example in `AISafetyAtlas.Examples.Robot` constructs a
certificate using Mathlib's finite-step evaluator: each cycle performs a longer
bounded approximation, returns an acceptable action while no result has been
found, and returns an unacceptable action after a result appears.

The example proves that the interface is non-vacuous. It is not evidence that
the minimal example is a faithful physical or ethical robot model.

### Correspondence table (paper claim → Lean)

| Paper | Lean |
|---|---|
| Theorem 1 / Corollary 1 conclusion: no total algorithmic observer for always-*P* | `¬ Nonempty (Verifier …)` under a `SwitchingConstruction` |
| "non-trivial *P*" (Def. 3) | Not a first-class predicate; existence of switch pair is packaged as `SwitchingConstruction` |
| "structured program" (Def. 2) | Abstract `structured : Program → Prop` (no hyper-command syntax) |
| "potentially unbounded memory" | Implicit in programs that can host the construction (Mathlib `Code` in the example) |
| Diagonal *K* | Fixed-input non-halting via `eval` |
| Corollary 1 restriction to structured programs | `Verifier.correct` only required on `structured` |

## What is not concluded

The theorem does not by itself establish any of the following:

- impossibility for finite-state, bounded-memory, bounded-horizon, or otherwise
  restricted program classes (the paper itself drops unbounded memory after
  Corollary 1 and develops separate interaction results);
- impossibility of sound but incomplete proof systems, semi-decision
  procedures, testing, runtime monitoring, or conservative certification;
- impossibility for proof-carrying systems or model classes deliberately chosen
  to make the property decidable;
- that a proposed `acceptable` predicate correctly captures ethics, law,
  alignment, safety, or human values; or
- a limitation of any named deployed robot or AI system.

Those require separate definitions, instantiations, and human review. In
particular, replacing `acceptable` with an "aligned" predicate does not create
a new theorem: the current theorem is already generic over every action
predicate. A new alignment result belongs in the public API only if its system
model or conclusion adds material structure.

## Existing formalization precedents

The exact objects used by van Leeuwen and Wiedermann were not found as a
maintained formal library that could be reused directly. There are, however,
strong precedents for the modeling choices:

- [RoboChart in Isabelle/UTP](https://isabelle-utp.york.ac.uk/paradigms/robotics)
  provides substantially richer state-machine and robotic-controller semantics.
- [ROSCoq](https://www.cs.cornell.edu/~aa755/ROSCoq/ROSCOQ.pdf) gives executable
  Rocq models for message-driven ROS software, including state-and-message
  handlers that produce new state and outgoing messages.
- [Interaction Trees](https://github.com/DeepSpec/InteractionTrees) provide a
  Rocq representation of recursive and reactive computations with visible
  events.
- Lean and Mathlib supply the partial-recursive codes, finite-step evaluator,
  computability definitions, and halting theorem used by this proof, but no
  maintained Lean robotics semantics library was identified for these exact
  paper objects.

These developments justify the use of traces, state evolution, and reactive
semantics as standard formal techniques. Importing or porting one would add a
large dependency without strengthening the present computability result.
Should a later theorem require physical dynamics, timed communication, or a
specific controller language, that requirement should be evaluated then and
the smallest suitable framework reused.

## Evidence classification

The registry classifies the Lean declaration as `RELATED`, not `EXACT` or
`EQUIVALENT`. The halting reduction and its crucial effective-construction
assumption are machine checked. Correspondence with the paper's full
Sense–Plan–Act and structured-program model, and every ethical, legal, or
AI-safety interpretation, remain `HUMAN_REVIEW`.
