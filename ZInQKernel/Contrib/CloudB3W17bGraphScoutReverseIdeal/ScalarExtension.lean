import ZInQKernel.Contrib.CloudB3W17bGraphScoutReverseIdeal.RangeLocalization
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
The algebraic image-under-scalar-extension step for the reverse ideal bridge.
It identifies extension of an actual image ideal with the image of the extended
unit-valued linear map, independently of flatness or any graph assumption.
-/

open TensorProduct
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal

/-- Scalar extension of the actual linear map into the unit ring module. -/
def scalarExtendedMapToRing
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (q : M →ₗ[R] R) :
    S ⊗[R] M →ₗ[S] S :=
  (AlgebraTensorModule.rid R S S).toLinearMap.comp (LinearMap.baseChange S q)

lemma scalarExtendedMapToRing_tmul
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (q : M →ₗ[R] R) (s : S) (m : M) :
    scalarExtendedMapToRing (S := S) q (s ⊗ₜ[R] m) = s * algebraMap R S (q m) := by
  simp only [scalarExtendedMapToRing, LinearMap.comp_apply, LinearMap.baseChange_tmul]
  change (AlgebraTensorModule.rid R S S) (s ⊗ₜ[R] q m) = s * algebraMap R S (q m)
  rw [AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm]

/-- An actual image ideal extends to the image of the scalar-extended map.
This is the ring/module part of the analytification stalk-image comparison. -/
theorem linearRangeIdeal_scalar_extension
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (q : M →ₗ[R] R) :
    (linearRangeIdeal q).map (algebraMap R S) =
      linearRangeIdeal (scalarExtendedMapToRing (S := S) q) := by
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr ?_
    rintro r ⟨m, rfl⟩
    exact ⟨1 ⊗ₜ[R] m, by rw [scalarExtendedMapToRing_tmul, one_mul]⟩
  · rintro r ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul s m =>
      rw [scalarExtendedMapToRing_tmul]
      exact ((linearRangeIdeal q).map (algebraMap R S)).mul_mem_left s
        (Ideal.mem_map_of_mem (algebraMap R S) ⟨m, rfl⟩)
    | add x y hx hy =>
      rw [map_add]
      exact ((linearRangeIdeal q).map (algebraMap R S)).add_mem hx hy

end ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal
