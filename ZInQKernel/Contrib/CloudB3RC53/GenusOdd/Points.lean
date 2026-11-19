import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Glue
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.IndexAlgebra

/-!
# GenusOdd: Heegner sums, native lattices and heights (PROVED)

* `chiSign_coe`, `chiSign_mul`: a quadratic `χ` takes the values `chiSign χ t ∈ {±1}`,
  multiplicatively.
* `heegnerSum_mem_eigenLattice`: the unaveraged sum `P_χ` lies in the native lattice (tex L2415).
* `heightK_eq_canonicalHeight`: for quadratic `χ`, CST's `ĥ_K(P_χ)` (the hermitian extension of the
  Néron–Tate pairing over `H_c`, divided by `[H_c : K]`) is `ĥ_{H_c}(P_χ) / [H_c : K]` for the
  honest point `P_χ = heegnerSum χ y`.
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Complex

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

section RingClass

variable {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]

theorem chi_val {χ : Pic (conductorOrder K c) →* ℂˣ} (hχ : ∀ t, χ t * χ t = 1) (t) :
    ((χ t : ℂˣ) : ℂ) = 1 ∨ ((χ t : ℂˣ) : ℂ) = -1 := by
  have h : ((χ t : ℂˣ) : ℂ) * ((χ t : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, hχ t, Units.val_one]
  have : (((χ t : ℂˣ) : ℂ) - 1) * (((χ t : ℂˣ) : ℂ) + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linear_combination h1
  · right; linear_combination h1

theorem chiSign_coe {χ : Pic (conductorOrder K c) →* ℂˣ} (hχ : ∀ t, χ t * χ t = 1) (t) :
    ((chiSign χ t : ℤ) : ℂ) = ((χ t : ℂˣ) : ℂ) := by
  unfold chiSign
  rcases chi_val hχ t with h | h
  · rw [if_pos h, h]; simp
  · rw [if_neg (by rw [h]; norm_num), h]; simp

theorem chiSign_mul {χ : Pic (conductorOrder K c) →* ℂˣ} (hχ : ∀ t, χ t * χ t = 1) (a b) :
    chiSign χ (a * b) = chiSign χ a * chiSign χ b := by
  have h := chiSign_coe hχ (a * b)
  rw [map_mul, Units.val_mul, ← chiSign_coe hχ a, ← chiSign_coe hχ b] at h
  exact_mod_cast h

theorem chiSign_sq {χ : Pic (conductorOrder K c) →* ℂˣ} (t) :
    chiSign χ t * chiSign χ t = 1 := by
  unfold chiSign; split_ifs <;> norm_num

theorem chiSign_inv {χ : Pic (conductorOrder K c) →* ℂˣ} (hχ : ∀ t, χ t * χ t = 1) (t) :
    chiSign χ t⁻¹ = chiSign χ t := by
  have h := chiSign_mul hχ t t⁻¹
  rw [mul_inv_cancel] at h
  have h1 : chiSign χ (1 : Pic (conductorOrder K c)) = 1 := by
    unfold chiSign; simp
  rw [h1] at h
  have := chiSign_sq (χ := χ) t
  calc chiSign χ t⁻¹ = chiSign χ t * chiSign χ t * chiSign χ t⁻¹ := by rw [this, one_mul]
    _ = chiSign χ t * (chiSign χ t * chiSign χ t⁻¹) := by ring
    _ = chiSign χ t := by rw [← h, mul_one]

variable (E : WeierstrassCurve ℚ)

section Dec

variable [DecidableEq (ringClassField (conductorOrder K c))]

theorem galPt_mul (σ τ : ringClassField (conductorOrder K c) ≃ₐ[K]
    ringClassField (conductorOrder K c)) (x) :
    galPt E (σ * τ) x = galPt E σ (galPt E τ x) := by
  simp only [galPt]
  rw [WeierstrassCurve.Affine.Point.map_map]
  rfl

/-- **The unaveraged Heegner sum lies in its native lattice** (PROVED): `σ P_χ = χ(σ) P_χ`. -/
theorem heegnerSum_mem_eigenLattice {χ : Pic (conductorOrder K c) →* ℂˣ}
    (hχ : ∀ t, χ t * χ t = 1) (y) : heegnerSum E χ y ∈ eigenLattice E χ := by
  intro σ
  set art := ringClassArtinEquiv (conductorOrder K c)
  simp only [heegnerSum, map_sum, map_zsmul]
  simp_rw [← galPt_mul]
  rw [Finset.smul_sum]
  refine (Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun τ => ?_)
  simp only [Equiv.coe_mulLeft, smul_smul, map_mul, chiSign_mul hχ]
  congr 1
  have := chiSign_sq (χ := χ) (art.symm σ)
  calc chiSign χ (art.symm τ) = (chiSign χ (art.symm σ) * chiSign χ (art.symm σ)) *
      chiSign χ (art.symm τ) := by rw [this, one_mul]
    _ = _ := by ring

end Dec

/-- **CST's `ĥ_K(P_χ)` for a quadratic `χ`** (PROVED): the hermitian extension collapses to the
Néron–Tate height over `H_c` of the honest point `P_χ`, divided by `[H_c : K]`. -/
theorem heightK_eq_canonicalHeight [E.IsElliptic] {χ : Pic (conductorOrder K c) →* ℂˣ}
    (hχ : ∀ t, χ t * χ t = 1) (y) :
    letI := Classical.decEq (ringClassField (conductorOrder K c))
    heightK E K c χ y = ((((Module.finrank K (ringClassField (conductorOrder K c)) : ℝ)⁻¹ *
      (heegnerSum E χ y).canonicalHeight : ℝ)) : ℂ) := by
  let _ := Classical.decEq (ringClassField (conductorOrder K c))
  set art := ringClassArtinEquiv (conductorOrder K c)
  unfold heightK ntPairing
  simp_rw [← chiSign_coe hχ, map_intCast]
  rw [← WeierstrassCurve.Affine.neronTatePairing_self]
  simp only [heegnerSum, map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
    zsmul_eq_mul]
  push_cast
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  simp only [galPt]
  conv_rhs => rw [mul_left_comm, ← mul_assoc]
  congr 1

end RingClass

end ZInQ.Contrib.CloudB3RC53.GenusOdd
