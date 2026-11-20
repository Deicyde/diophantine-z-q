import ZInQKernel.Contrib.OneProof.TateRangeComplement

/-! # The regular trace pairing and semisimplicity under scalar extension

For a finite-dimensional algebra in characteristic zero, an inner inverse for
each element makes the trace pairing of the left regular representation
nondegenerate. Its Gram determinant stays nonzero over every extension field.
The nilpotent Jacobson radical pairs to zero and therefore vanishes.
-/

noncomputable section
open scoped TensorProduct

namespace ZInQ.Contrib.TateFiniteApproximation

variable (F : Type*) [Field F] (R : Type*) [Ring R] [Algebra F R]

/-- Trace of left multiplication by xy, also for noncommutative algebras. -/
def regularTracePairing : LinearMap.BilinForm F R :=
  LinearMap.compr₂ (Algebra.lmul F R).toLinearMap ((LinearMap.trace F R).comp (Algebra.lmul F R).toLinearMap)

private theorem pairing_separating_of_innerInverse [FiniteDimensional F R] [CharZero F]
    (hinv : ∀ x : R, ∃ y, x * y * x = x) : (regularTracePairing F R).SeparatingLeft := by
  intro x hx
  obtain ⟨y, h⟩ := hinv x
  have he : IsIdempotentElem (x*y) := by change x*y*(x*y) = x*y; rw [← mul_assoc, h]
  have hp : IsIdempotentElem (Algebra.lmul F R (x*y)) := he.map (Algebra.lmul F R)
  have hz := (LinearMap.IsIdempotentElem.trace_eq_zero_iff hp).mp (hx y)
  have hxy : x*y = 0 := by simpa using LinearMap.congr_fun hz 1
  rwa [hxy, zero_mul, eq_comm] at h

private theorem semisimple_of_pairing_separating [FiniteDimensional F R]
    (h : (regularTracePairing F R).SeparatingLeft) : IsSemisimpleRing R := by
  have : IsArtinianRing R := IsArtinianRing.of_finite F R
  apply IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr
  apply le_antisymm _ bot_le
  intro x hx
  apply h x
  intro y
  obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := R)
  have hxy := Ideal.pow_mem_pow ((Ring.jacobson R).mul_mem_right y hx) n
  rw [hn] at hxy
  have hnxy : IsNilpotent (x*y) := ⟨n, hxy⟩
  exact isNilpotent_iff_eq_zero.mp
    (LinearMap.isNilpotent_trace_of_isNilpotent (hnxy.map (Algebra.lmul F R)))

/-- A finite-dimensional characteristic-zero algebra in which each element
has an inner inverse remains semisimple after every extension of the field. -/
theorem semisimple_baseChange_of_innerInverse [FiniteDimensional F R] [CharZero F]
    (E : Type*) [Field E] [Algebra F E] (h : ∀ x : R, ∃ y, x*y*x = x) :
    IsSemisimpleRing (E ⊗[F] R) := by
  classical
  let b := Module.finBasis F R
  have hsep := pairing_separating_of_innerInverse F R h
  have hdet := Matrix.separatingLeft_iff_det_ne_zero.mp
    ((LinearMap.BilinForm.separatingLeft_toMatrix_iff b).mpr hsep)
  apply semisimple_of_pairing_separating E (E ⊗[F] R)
  apply (LinearMap.BilinForm.separatingLeft_toMatrix_iff (b.baseChange E)).mp
  apply Matrix.separatingLeft_iff_det_ne_zero.mpr
  have hm : (regularTracePairing E (E ⊗[F] R)).toMatrix (b.baseChange E) =
      ((regularTracePairing F R).toMatrix b).map (algebraMap F E) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Matrix.map_apply, Module.Basis.baseChange_apply]
    change LinearMap.trace E _ (Algebra.lmul E _ (((1 : E) ⊗ₜ[F] b i)*((1 : E) ⊗ₜ[F] b j))) =
      algebraMap F E (LinearMap.trace F _ (Algebra.lmul F _ (b i*b j)))
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.baseChange_lmul,
      LinearMap.trace_baseChange]
  rw [hm]
  change ((algebraMap F E).mapMatrix ((regularTracePairing F R).toMatrix b)).det ≠ 0
  rw [← RingHom.map_det]
  exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr hdet

/-- Scalar extension preserves finite-dimensional semisimple algebras in
characteristic zero, without a commutativity assumption on the algebra. -/
theorem semisimple_baseChange [FiniteDimensional F R] [CharZero F] [IsSemisimpleRing R]
    (E : Type*) [Field E] [Algebra F E] : IsSemisimpleRing (E ⊗[F] R) :=
  semisimple_baseChange_of_innerInverse F R E exists_innerInverse_of_semisimple

end ZInQ.Contrib.TateFiniteApproximation
