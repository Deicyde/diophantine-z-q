import ZInQKernel.Contrib.OneProof.TateRationalHom
import ZInQKernel.Contrib.OneProof.TateImageSaturation
import ZInQKernel.Contrib.OneProof.FaltingsFromIsogenyBound

/-! # Integral Tate comparison from the rational graph construction -/

noncomputable section

open PkgI3.AbVar
open scoped CategoryTheory.MonObj TensorProduct nonZeroDivisors

namespace ZInQ.Contrib.TateFiniteApproximation

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

private def integralTensorInclusion {H : Type*} [AddCommGroup H] :
    (ℤ_[ℓ] ⊗[ℤ] H) →ₗ[ℤ] ℚ_[ℓ] ⊗[ℤ] H :=
  TensorProduct.map ((Algebra.linearMap ℤ_[ℓ] ℚ_[ℓ]).restrictScalars ℤ) LinearMap.id

private theorem integralTensorInclusion_smul {H : Type*} [AddCommGroup H]
    (a : ℤ_[ℓ]) (x : ℤ_[ℓ] ⊗[ℤ] H) :
    integralTensorInclusion ℓ (a • x) =
      (algebraMap ℤ_[ℓ] ℚ_[ℓ] a) • integralTensorInclusion ℓ x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul a' h =>
    change (algebraMap ℤ_[ℓ] ℚ_[ℓ] (a * a')) ⊗ₜ[ℤ] h =
      ((algebraMap ℤ_[ℓ] ℚ_[ℓ] a) * (algebraMap ℤ_[ℓ] ℚ_[ℓ] a')) ⊗ₜ[ℤ] h
    rw [map_mul]

private theorem exists_primePow_mul_eq_integral {H : Type*} [AddCommGroup H]
    (x : ℚ_[ℓ] ⊗[ℤ] H) :
    ∃ (n : ℕ) (y : ℤ_[ℓ] ⊗[ℤ] H), (ℓ : ℚ_[ℓ]) ^ n • x = integralTensorInclusion ℓ y := by
  let N := ℤ_[ℓ] ⊗[ℤ] H
  let e : (ℚ_[ℓ] ⊗[ℤ_[ℓ]] N) ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℤ] H :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ] H
  have he (y : N) : e (1 ⊗ₜ[ℤ_[ℓ]] y) = integralTensorInclusion ℓ y := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => rw [TensorProduct.tmul_add, map_add, hy, hz, map_add]
    | tmul a y =>
      change (a • (1 : ℚ_[ℓ])) ⊗ₜ[ℤ] y = (algebraMap ℤ_[ℓ] ℚ_[ℓ] a) ⊗ₜ[ℤ] y
      rw [Algebra.smul_def, mul_one]
  obtain ⟨⟨y, d⟩, hd⟩ := IsLocalizedModule.surj (ℤ_[ℓ])⁰
      (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] N 1) (e.symm x)
  have hd' : (algebraMap ℤ_[ℓ] ℚ_[ℓ] d.1) • e.symm x = 1 ⊗ₜ[ℤ_[ℓ]] y := by
    change (d.1 : ℤ_[ℓ]) • e.symm x = 1 ⊗ₜ[ℤ_[ℓ]] y at hd
    simpa only [IsScalarTower.algebraMap_smul] using hd
  have h : (algebraMap ℤ_[ℓ] ℚ_[ℓ] d.1) • x = integralTensorInclusion ℓ y := by
    simpa only [map_smul, LinearEquiv.apply_symm_apply, he] using congrArg e hd'
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.coe_ne_zero d) PadicInt.irreducible_p
  refine ⟨n, (↑u⁻¹ : ℤ_[ℓ]) • y, ?_⟩
  rw [integralTensorInclusion_smul, ← h, smul_smul, ← map_mul, hu, ← mul_assoc, Units.inv_mul,
    one_mul, map_pow, map_natCast]

private theorem tateHomQl_smul {K : Type} [Field K] (A B : PkgI3.AbVar K)
    (a : ℚ_[ℓ]) (x : ℚ_[ℓ] ⊗[ℤ] Hom A B) :
    tateHomQl ℓ A B (a • x) = a • tateHomQl ℓ A B x := by
  induction x using TensorProduct.inductionOn with
  | tmul b f => rw [TensorProduct.smul_tmul', tateHomQl_tmul, tateHomQl_tmul, smul_smul, smul_eq_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

private theorem tateHomQl_integralTensorInclusion {K : Type} [Field K] (A B : PkgI3.AbVar K)
    (x : ℤ_[ℓ] ⊗[ℤ] Hom A B) :
    tateHomQl ℓ A B (integralTensorInclusion ℓ x) = (tateHomZl ℓ A B x).baseChange ℚ_[ℓ] := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.baseChange_add]
  | tmul a f =>
    change (algebraMap ℤ_[ℓ] ℚ_[ℓ] a) • (homT (ℓ := ℓ) f).baseChange ℚ_[ℓ] =
      (a • homT (ℓ := ℓ) f).baseChange ℚ_[ℓ]
    rw [LinearMap.baseChange_smul, IsScalarTower.algebraMap_smul]

omit hℓ in
private theorem tate_nsmul_injective {M : Type*} [AddCommGroup M] (n : ℕ) :
    Function.Injective (fun x : PkgI3.Tate.T ℓ M => ℓ ^ n • x) := by
  intro x y h
  apply Subtype.ext
  funext j
  have hj := congrArg (fun v : PkgI3.Tate.T ℓ M => v.1 (j + n)) h
  change ℓ ^ n • x.1 (j + n) = ℓ ^ n • y.1 (j + n) at hj
  rwa [PkgI3.Tate.pow_smul_shift x.2 n j, PkgI3.Tate.pow_smul_shift y.2 n j] at hj

private theorem tate_to_rational_injective {M : Type*} [AddCommGroup M] :
    Function.Injective
      (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ M) 1) := by
  intro x y hxy
  obtain ⟨d, h⟩ := IsLocalizedModule.exists_of_eq (S := (ℤ_[ℓ])⁰)
    (f := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ M) 1) hxy
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.coe_ne_zero d) PadicInt.irreducible_p
  change (d.1 : ℤ_[ℓ]) • x = d.1 • y at h
  rw [hu, mul_smul, mul_smul] at h
  apply tate_nsmul_injective ℓ n
  simp only [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], Nat.cast_pow]
  exact (u.isUnit.smul_left_cancel.mp h)

private theorem tate_baseChange_injective {K : Type} [Field K] (A B : PkgI3.AbVar K) :
    Function.Injective (LinearMap.baseChange ℚ_[ℓ] : (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) → _) := by
  intro f g h
  apply LinearMap.ext
  intro x
  apply tate_to_rational_injective ℓ (M := Additive (B.Pt (AlgebraicClosure K)))
  exact LinearMap.congr_fun h ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x)

/-- Clear denominators and use saturation to recover the integral map. -/
theorem tateHomZl_mem_range_of_rational {K : Type} [Field K] [CharZero K] (A B : PkgI3.AbVar K)
    (f : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ)
    (hf : f.baseChange ℚ_[ℓ] ∈ Set.range (tateHomQl ℓ A B)) :
    f ∈ Set.range (tateHomZl ℓ A B) := by
  obtain ⟨x, hx⟩ := hf
  obtain ⟨n, y, hy⟩ := exists_primePow_mul_eq_integral ℓ x
  apply ZInQ.Contrib.TateImageSaturation.tateHomZl_saturated ℓ n f
  refine ⟨y, tate_baseChange_injective ℓ A B ?_⟩
  rw [← tateHomQl_integralTensorInclusion ℓ A B, ← hy, tateHomQl_smul, hx]
  rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], LinearMap.baseChange_smul,
    Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul ℚ_[ℓ], Nat.cast_pow]

end ZInQ.Contrib.TateFiniteApproximation
