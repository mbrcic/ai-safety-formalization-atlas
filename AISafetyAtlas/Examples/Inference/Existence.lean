module

public import AISafetyAtlas.Inference
public import AISafetyAtlas.Examples.Inference.Device
public import AISafetyAtlas.Examples.Inference.Halting

/-!
# Worked models: when an inferring device exists

The existence theorem is only interesting beside the refutation it repairs, so
both are exercised here against the same target shape.

`fin3_has_inferring_device` applies the theorem at three values — the least its
hypothesis allows — and gets a device. `two_values_is_too_few` drops to two and
gets the 2008 countermodel. The hypothesis `|Γ(U)| ≥ 3` is therefore load-bearing
in the strongest available sense: one value fewer and the conclusion is provably
false, not merely unproved.
-/

namespace AISafetyAtlas.Examples.Inference.Existence

open AISafetyAtlas.Inference
open AISafetyAtlas.Examples.Inference.Device
open AISafetyAtlas.Examples.Inference.Halting

/-- The theorem applies to the identity on `Fin 3` and yields a device. -/
theorem fin3_has_inferring_device :
    ∃ C : InferenceDevice.{0, 0} (Fin 3), WeaklyInfers C (id : Fin 3 → Fin 3) :=
  exists_weaklyInfers_of_three_values (id : Fin 3 → Fin 3)
    (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
    (by decide : (1 : Fin 3) ≠ 2)

/-- The source's own construction works, not merely some device: `X` the
identity, `Y` true at exactly one point. -/
theorem fin3_identityDevice_infers :
    WeaklyInfers (identityDevice (0 : Fin 3) ⟨1, by decide⟩) (id : Fin 3 → Fin 3) :=
  identityDevice_weaklyInfers (id : Fin 3 → Fin 3)
    (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
    (by decide : (1 : Fin 3) ≠ 2)

/-- **The boundary.** One value fewer and the claim is false: `Γ = id` on `Bool`
attains two values and *no* device infers it. This is 2008 Corollary 1(ii) as
printed, refuted, and it is why the 2018 hypothesis is not decoration. -/
theorem two_values_is_too_few :
    ¬ ∃ C : InferenceDevice.{0, 0} Bool, WeaklyInfers C (id : Bool → Bool) :=
  no_device_weaklyInfers_id_on_bool

/-- Citing the source's own Proposition 7(2) witness by name. -/
theorem idDeviceOnBool_is_device_pair :
    idDeviceOnBool.setup = id ∧ idDeviceOnBool.concl = id :=
  id_is_device_pair_on_bool

/-- Definition 5 and Definition 4 at a device's own pair agree, applied at two
distinct devices of the same universe. -/
theorem haltingDevice_stronglyInfers_iff_stronglyInfersPair :
    StronglyInfers haltingDevice stuckDevice ↔
      StronglyInfersPair haltingDevice stuckDevice.setup stuckDevice.concl :=
  stronglyInfers_iff_stronglyInfersPair haltingDevice stuckDevice

/-- **Proposition 7(2): some pair of functions no device strongly infers.**
The witness is `S = T = id`, and the point of it is that this is a *function*
pair rather than a device pair -- a device pair would force the second component
to be a conclusion, which at `Fin 3` it is not. Named at `Fin 3`, the smallest
universe where the distinction bites. -/
public theorem exists_unpaired_at_three :
    ∃ S T : Fin 3 → Fin 3, ∀ C : InferenceDevice.{0, 0} (Fin 3), ¬ StronglyInfersPair C S T :=
  exists_pair_not_stronglyInfers

end AISafetyAtlas.Examples.Inference.Existence
