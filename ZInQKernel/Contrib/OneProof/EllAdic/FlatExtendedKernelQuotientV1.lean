import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient

set_option autoImplicit false

open scoped TensorProduct

namespace RC53.EllAdic

/-- For a surjective ring homomorphism, flatness of its target uses the same
base action as the quotient by its kernel. -/
theorem flat_surjective_iff_flat_kernelQuotient {R T : Type*}
    [CommRing R] [CommRing T] (f : R →+* T) (hf : Function.Surjective f) :
    f.Flat ↔ Module.Flat R (R ⧸ RingHom.ker f) := by
  let q : R →+* (R ⧸ RingHom.ker f) := Ideal.Quotient.mk (RingHom.ker f)
  let e : (R ⧸ RingHom.ker f) ≃+* T := RingHom.quotientKerEquivOfSurjective hf
  have hq : q.Flat ↔ Module.Flat R (R ⧸ RingHom.ker f) :=
    RingHom.flat_algebraMap_iff (R := R) (S := R ⧸ RingHom.ker f)
  have h₁ : e.toRingHom.comp q = f := by
    ext x
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hf x
  have h₂ : e.symm.toRingHom.comp f = q := RingHom.quotientKerEquivOfSurjective_symm_comp hf
  have he : e.toRingHom.Flat := RingHom.Flat.of_bijective e.bijective
  have he' : e.symm.toRingHom.Flat := RingHom.Flat.of_bijective e.symm.bijective
  constructor
  · intro h
    exact hq.1 (h₂ ▸ h.comp he')
  · intro h
    exact h₁ ▸ (hq.2 h).comp he

/-- Base change of a flat surjection, expressed as the actual quotient
by the extension of the original kernel ideal. -/
theorem flat_extended_kernelQuotient_of_surjective {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] (a : R →+* S) (f : R →+* T)
    (hf : Function.Surjective f) (hflat : f.Flat) :
    Module.Flat S (S ⧸ Ideal.map a (RingHom.ker f)) := by
  let : Algebra R S := a.toAlgebra
  let : Module.Flat R (R ⧸ RingHom.ker f) :=
    (flat_surjective_iff_flat_kernelQuotient f hf).1 hflat
  have ht : Module.Flat S (S ⊗[R] (R ⧸ RingHom.ker f)) :=
    Module.Flat.baseChange R S (R ⧸ RingHom.ker f)
  let e : (S ⧸ Ideal.map a (RingHom.ker f)) ≃ₗ[S] (S ⊗[R] (R ⧸ RingHom.ker f)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (RingHom.ker f)).toLinearEquiv
  exact (Module.Flat.equiv_iff e).2 ht

end RC53.EllAdic
