module

import AISafetyAtlas.Knowledge.Temporal
import Mathlib.Data.Nat.Basic

/-!
# The contemporaneity gap, exhibited

`AISafetyAtlas.Knowledge.Temporal` separates *knowing the state as of time `s`
from evidence at time `t`* from *knowing the current state at `t`*. Separating
two definitions proves nothing on its own: if the two always stood or fell
together the distinction would be bookkeeping.

This module shows they come apart, in one model, with cumulative evidence
throughout — the shape a distributed snapshot has (`LAND-CL-001`), and the reason
"a system cannot know its own state" is the wrong headline.

## The model

Time is `ℕ`. A history is a pair: the target value at time 0 and at time 1. The
observer sees nothing at time 0, and from time 1 on sees **the time-0 value
only** — the past has arrived, the present has not.

| | time 0 | time ≥ 1 |
|---|---|---|
| target | `ω.1` | `ω.2` |
| evidence | `()` | `ω.1` |

Everything below is decidable on four histories, and deliberately so: the point
is the *shape*, not the difficulty.
-/

namespace AISafetyAtlas.Examples.Knowledge.Temporal

open AISafetyAtlas.Knowledge AISafetyAtlas.Knowledge.Temporal

/-- A history: the target value at time 0 and the target value at time 1. -/
private abbrev Hist := Bool × Bool

/-- Evidence type: nothing at time 0, the time-0 value afterwards. -/
private abbrev Ev : ℕ → Type
  | 0 => Unit
  | _ + 1 => Bool

/-- The observer sees nothing at time 0, and the *past* value afterwards. -/
private def observe : (t : ℕ) → Hist → Ev t
  | 0, _ => ()
  | _ + 1, ω => ω.1

/-- The target is the value current at that time. -/
private def target : ℕ → Hist → Bool
  | 0, ω => ω.1
  | _ + 1, ω => ω.2

/-! ## Evidence is cumulative

Nothing is forgotten, so `knowableFrom_mono` applies and knowledge established at
one time survives to every later one. -/

example : EvidenceMonotone observe := by
  rintro (_ | t) (_ | t') hle
  · exact ⟨fun _ => (), fun _ => rfl⟩
  · exact ⟨fun _ => (), fun _ => rfl⟩
  · exact absurd hle (by omega)
  · exact ⟨id, fun _ => rfl⟩

/-! ## The past becomes knowable -/

/-- At time 1 the time-0 target is known exactly: the decoder is the identity. -/
example : KnowableFrom observe target 1 0 :=
  ⟨id, fun _ => rfl⟩

/-! ## The present does not -/

/-- The *current* target at time 1 is not knowable at time 1. The histories
`(false, false)` and `(false, true)` agree on every piece of evidence available
at time 1 and disagree on the target there. -/
example : ¬ KnowableAt observe target 1 :=
  not_knowableAt_of_collisionAt
    ⟨(false, false), (false, true), rfl, by decide⟩

/-- Nor is the time-0 target knowable at time 0: the observer sees nothing yet. -/
example : ¬ KnowableAt observe target 0 :=
  not_knowableAt_of_collisionAt
    ⟨(false, false), (true, false), rfl, by decide⟩

/-! ## Both halves together

`DelayedKnowable observe target 0 1` is exactly "the time-0 target is not
knowable when current, and is knowable from time-1 evidence". Inhabiting it is
the non-implication: contemporaneous failure does **not** entail permanent
failure, so an impossibility result has to say *when*. -/

example : DelayedKnowable observe target 0 1 :=
  ⟨by omega,
   not_knowableAt_of_collisionAt
     ⟨(false, false), (true, false), rfl, by decide⟩,
   ⟨id, fun _ => rfl⟩⟩

/-! ## What this does not show

There is no dynamics here, only an indexed family, so the model says nothing
about *why* the present is unreadable. It exhibits that the two definitions come
apart, which is what licenses stating the obstruction contemporaneously rather
than absolutely. Whether a given system has causal innovation at a given time is
a modelling question this file does not touch. -/

end AISafetyAtlas.Examples.Knowledge.Temporal
