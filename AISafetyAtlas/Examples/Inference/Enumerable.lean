module

public import AISafetyAtlas.Inference

/-!
# Devices as data, so a search can quantify over them

Every countermodel in this development names one device. That is enough to refute
a universal claim, but it cannot answer *"is there any device at all with this
property?"* — `InferenceDevice` carries its setup type as a field, so a statement
quantifying over devices ranges over a proper class of types and nothing can
enumerate it.

`FinDevice m n` fixes both types: `U = Fin m`, `Setup = Fin n`. It is a `Fintype`,
so a statement quantifying over **all** devices of that shape is decidable and
`decide` settles it in the kernel.

This is the object a property-based search wants. `plausible` is the wrong tool
here even though it is available: on a goal it fails to refute it closes with
`sorry`, so it can never be committed, whereas `decide` on a small shape is
exhaustive *and* kernel-checked. Sampling only becomes necessary when the shape is
too large to exhaust.
-/

namespace AISafetyAtlas.Examples.Inference.Enumerable

open AISafetyAtlas.Inference

/-- A device with both of its types fixed, so that devices are enumerable. -/
public structure FinDevice (m n : ℕ) where
  /-- How the device is set up in each of the `m` universes. -/
  setup : Fin m → Fin n
  /-- What it concludes there. -/
  concl : Fin m → Bool
  /-- Definition 1's surjectivity. -/
  concl_surj : Function.Surjective concl

public instance instFintypeFinDevice (m n : ℕ) : Fintype (FinDevice m n) :=
  Fintype.ofEquiv {p : (Fin m → Fin n) × (Fin m → Bool) // Function.Surjective p.2}
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun d => ⟨(d.setup, d.concl), d.concl_surj⟩
      left_inv := fun p => by cases p; rfl
      right_inv := fun d => by cases d; rfl }

/-- The `InferenceDevice` it denotes. -/
public abbrev FinDevice.toDevice {m n : ℕ} (d : FinDevice m n) :
    InferenceDevice (Fin m) where
  Setup := Fin n
  setup := d.setup
  concl := d.concl
  concl_surjective := d.concl_surj

/-- `WeaklyInfers` is decidable on an enumerable device: every quantifier in
Definition 3 ranges over a finite type once both of the device's types are fixed.

The instance has to unfold the definitions by hand. `WeaklyInfers` and `Realized`
are `def`s, and instance search works at reducible transparency, so it will not see
the decidable `∀`/`∃` structure underneath on its own. -/
public instance decidableWeaklyInfers {m n : ℕ} (d : FinDevice m n)
    {G : Type} [Fintype G] [DecidableEq G] (Γ : Fin m → G) :
    Decidable (WeaklyInfers d.toDevice Γ) := by
  unfold WeaklyInfers InferenceDevice.Realized IsProbe
  infer_instance

/-! ## Corollary 1(ii), refuted exhaustively

`Examples.Inference.Device.no_device_weaklyInfers_id_on_bool` refutes the printed
Corollary 1(ii) with **one** device. The claim it contradicts is existential —
*"there is a device that infers `Γ`"* — so a single countermodel is not the whole
refutation; what is needed is that **no** device works.

Over a two-state universe with two setup values, `decide` checks every device. -/

public theorem no_finDevice_weaklyInfers_id :
    ∀ d : FinDevice 2 2, ¬ WeaklyInfers d.toDevice (fun w : Fin 2 => w) := by decide

end AISafetyAtlas.Examples.Inference.Enumerable
