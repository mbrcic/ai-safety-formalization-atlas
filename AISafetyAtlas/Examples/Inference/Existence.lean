module

public import AISafetyAtlas.Inference
public import AISafetyAtlas.Examples.Inference.Device

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

end AISafetyAtlas.Examples.Inference.Existence
