import WeightTwoProfileInversion03

/-!
# Actual finite division-form prototypes at every slash representative

Right special-linear multiplication preserves primitive residue rows and
commutes with inverse-unit scaling. The concrete weight-two inverse matrix
therefore recovers the transported signed axis deltas. The finite prototype
forms have these actual constants at every integral slash representative,
with the same uniform offset. No final cusp interpolation is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable

open Complex Filter Matrix ModularForm
open UpperHalfPlane hiding I
open scoped Topology Real ModularForm MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants

open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinNormalization PrimitiveEisensteinUnitSeries

/-- The actual residue reduction of an integral special-linear matrix. -/
def residueSL (N : ℕ) (γ : SL(2, ℤ)) : SL(2, ZMod N) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ

/-- Right multiplication of actual primitive residue rows. -/
def rightPrimitive (N : ℕ) (γ : SL(2, ℤ)) (p : PrimitiveRow N) : PrimitiveRow N := by
  let A := residueSL N γ
  refine ⟨p.1 ᵥ* A.1, ?_⟩
  obtain ⟨x, y, hxy⟩ := p.2
  refine ⟨A 1 1 * x - A 0 1 * y, -A 1 0 * x + A 0 0 * y, ?_⟩
  have hd := A.det_coe
  rw [Matrix.det_fin_two] at hd
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  linear_combination (x * p.1 0 + y * p.1 1) * hd + hxy

/-- Unit scaling commutes with right multiplication, including the nonunit-guard identity branch. -/
theorem unitPermutation_rightPrimitive (N d : ℕ) (γ : SL(2, ℤ)) (p : PrimitiveRow N) :
    unitPermutation N d (rightPrimitive N γ p) = rightPrimitive N γ (unitPermutation N d p) := by
  classical
  by_cases hd : d.Coprime N
  · simp only [unitPermutation, dite_eq_left hd]
    apply Subtype.ext
    funext i
    simp only [primitiveUnitEquiv, Equiv.coe_fn_mk, rightPrimitive, scaleResidue,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  · simp only [unitPermutation, dite_eq_right hd, Equiv.refl_apply]

/-- Actual x constants respect precisely the congruence class of each integral label. -/
theorem xConstant_congr (N : ℕ) [NeZero N] (a b r s : ℤ)
    (h0 : (a : ZMod N) = (r : ZMod N)) (h1 : (b : ZMod N) = (s : ZMod N)) :
    xConstant N a b = xConstant N r s := by
  have hd0 : (N : ℤ) ∣ a - r :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a - r) N).mp (by simp only [Int.cast_sub, h0, sub_self])
  have hd1 : (N : ℤ) ∣ b - s :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (b - s) N).mp (by simp only [Int.cast_sub, h1, sub_self])
  obtain ⟨m, hm⟩ := hd0
  obtain ⟨n, hn⟩ := hd1
  have ha : r + (N : ℤ) * m = a := by linarith
  have hb : s + (N : ℤ) * n = b := by linarith
  have he : TorsionWeierstrassData.xValue N a b = TorsionWeierstrassData.xValue N r s := by
    funext τ
    have h := WeierstrassDistributionNat.xValue_shift (NeZero.pos N) r s m n τ
    simpa only [ha, hb] using h
  have ht := xValue_tendsto N (NeZero.pos N) a b
  rw [he] at ht
  exact tendsto_nhds_unique ht (xValue_tendsto N (NeZero.pos N) r s)

lemma rightPrimitive_label_cast (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (p : PrimitiveRow N) (i : Fin 2) :
    ((((![((p.1 0).val : ℤ), ((p.1 1).val : ℤ)] ᵥ* γ.1) i : ℤ) : ZMod N)) =
      (rightPrimitive N γ p).1 i := by
  simp [rightPrimitive, residueSL, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Matrix.SpecialLinearGroup.map_apply_coe, Matrix.map_apply,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The unchanged division form has the constant of the actual transported primitive row. -/
theorem division_slash_primitive_coeff_zero (N : ℕ) [NeZero N]
    (γ : SL(2, ℤ)) (p : PrimitiveRow N) :
    (qExpansion (N : ℝ)
      ((EisensteinWeightTwo.divisionEisensteinMF N (NeZero.pos N)
        ![((p.1 0).val : ℤ), ((p.1 1).val : ℤ)] : ℍ → ℂ) ∣[(2 : ℤ)] γ)).coeff 0 =
      xConstant N (((rightPrimitive N γ p).1 0).val : ℤ)
        (((rightPrimitive N γ p).1 1).val : ℤ) := by
  rw [divisionEisensteinMF_slash_coeff_zero N (NeZero.pos N)]
  apply xConstant_congr N
  · simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using rightPrimitive_label_cast N γ p 0
  · simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using rightPrimitive_label_cast N γ p 1

variable (N : ℕ) [NeZero N] [Fintype (PrimitiveRow N)] [DecidableEq (PrimitiveRow N)]

/-- Actual transported constants in the same fixed finite coordinate system. -/
def transportedActualProfile (γ : SL(2, ℤ)) : PrimitiveRow N → ℂ :=
  fun p => actualProfileVector N (rightPrimitive N γ p)

/-- The signed axis delta vector after actual special-linear transport. -/
def transportedAxis (γ : SL(2, ℤ)) : PrimitiveRow N → ℂ :=
  fun p => axisProfile N (rightPrimitive N γ p).1

/-- The very same concrete matrix realizes the actual profile at every slash representative. -/
theorem profileMatrix_transported (hN : 3 ≤ N) (γ : SL(2, ℤ)) :
    (profileMatrix N).mulVec (transportedAxis N γ) =
      fun p => transportedActualProfile N γ p + profileFinitePart N := by
  rw [profileMatrix, WeightTwoFiniteConvolution.convolutionMatrix_mulVec]
  funext p
  have h := primitive_xConstant_add_tail N hN (rightPrimitive N γ p)
  unfold transportedAxis transportedActualProfile actualProfileVector
  calc
    _ = axisProfile N (rightPrimitive N γ p).1 +
        ∑' n : ℕ, unitCoefficient N 2 (n + 2) *
          axisProfile N (unitPermutation N (n + 2) (rightPrimitive N γ p)).1 := by
      congr 1
      apply tsum_congr
      intro n
      rw [← unitPermutation_rightPrimitive N (n + 2) γ p]
      by_cases hd : (n + 2).Coprime N
      · simp only [unitCoefficient, ite_eq_left hd]
      · simp only [unitCoefficient, ite_eq_right hd, zero_mul]
    _ = _ := h.symm

/-- Ordinary inverse recovery of every actual transported weight-two profile. -/
theorem profileMatrix_recover_transported (hN : 3 ≤ N) (γ : SL(2, ℤ)) :
    ((profileMatrix N)⁻¹).mulVec
      (fun p => transportedActualProfile N γ p + profileFinitePart N) = transportedAxis N γ := by
  rw [← profileMatrix_transported N hN γ]
  exact WeightTwoFiniteConvolution.convolutionMatrix_recover (unitPermutation N)
    (fun d => d.Coprime N) (transportedAxis N γ)

/-- Slash transport is a linear map between genuine same-level weight-two modular forms. -/
def principalSlashMap (γ : SL(2, ℤ)) :
    ModularForm (principalLevel N) 2 →ₗ[ℂ] ModularForm (principalLevel N) 2 where
  toFun f := principalMFSlash N 2 f γ
  map_add' f g := by
    apply DFunLike.coe_injective
    simp only [principalMFSlash_coe, FunLike.coe_add, SlashAction.add_slash]
  map_smul' a f := by
    apply DFunLike.coe_injective
    simp only [principalMFSlash_coe, FunLike.coe_smul, ModularForm.SL_smul_slash, RingHom.id_apply]

/-- The actual slash constant as a linear functional, with period N and weight two. -/
def slashCoefficientMap (γ : SL(2, ℤ)) : ModularForm (principalLevel N) 2 →ₗ[ℂ] ℂ :=
  (coefficientZeroMap N (NeZero.pos N)).comp (principalSlashMap N γ)

lemma slashCoefficientMap_apply (γ : SL(2, ℤ)) (f : ModularForm (principalLevel N) 2) :
    slashCoefficientMap N γ f =
      (qExpansion (N : ℝ) ((f : ℍ → ℂ) ∣[(2 : ℤ)] γ)).coeff 0 := rfl

lemma slashCoefficientMap_division (γ : SL(2, ℤ)) (p : PrimitiveRow N) :
    slashCoefficientMap N γ
      (EisensteinWeightTwo.divisionEisensteinMF N (NeZero.pos N)
        ![((p.1 0).val : ℤ), ((p.1 1).val : ℤ)]) =
      xConstant N (((rightPrimitive N γ p).1 0).val : ℤ)
        (((rightPrimitive N γ p).1 1).val : ℤ) :=
  division_slash_primitive_coeff_zero N γ p

lemma profileForm_slash_coeff_zero_sum (γ : SL(2, ℤ)) (p : PrimitiveRow N) :
    (qExpansion (N : ℝ)
      ((profileForm N (NeZero.pos N) p : ℍ → ℂ) ∣[(2 : ℤ)] γ)).coeff 0 =
      ∑ q : PrimitiveRow N, ((profileMatrix N)⁻¹ p q / (N : ℂ) ^ 2) *
        xConstant N (((rightPrimitive N γ q).1 0).val : ℤ)
          (((rightPrimitive N γ q).1 1).val : ℤ) := by
  rw [← slashCoefficientMap_apply]
  unfold profileForm
  rw [map_sum]
  simp only [map_smul, slashCoefficientMap_division N γ, smul_eq_mul]

/-- Every actual prototype has the proved signed delta profile, with the same offset at all cusps. -/
theorem profileForm_slash_coeff_zero (hN : 3 ≤ N) (γ : SL(2, ℤ)) (p : PrimitiveRow N) :
    (qExpansion (N : ℝ)
      ((profileForm N (NeZero.pos N) p : ℍ → ℂ) ∣[(2 : ℤ)] γ)).coeff 0 =
      axisProfile N (rightPrimitive N γ p).1 - uniformProfileOffset N := by
  have hr := congrFun (profileMatrix_recover_transported N hN γ) p
  have h : axisProfile N (rightPrimitive N γ p).1 =
      ∑ q : PrimitiveRow N, (profileMatrix N)⁻¹ p q *
        (transportedActualProfile N γ q + profileFinitePart N) := by
    exact hr.symm.trans (Matrix.mulVec_apply_eq_sum _ _ _)
  have he : (∑ q : PrimitiveRow N, (profileMatrix N)⁻¹ p q *
      (transportedActualProfile N γ q + profileFinitePart N)) =
      (∑ q : PrimitiveRow N, ((profileMatrix N)⁻¹ p q / (N : ℂ) ^ 2) *
        xConstant N (((rightPrimitive N γ q).1 0).val : ℤ)
          (((rightPrimitive N γ q).1 1).val : ℤ)) +
        profileFinitePart N * (∑ q : PrimitiveRow N, (profileMatrix N)⁻¹ p q) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    unfold transportedActualProfile actualProfileVector
    ring
  rw [he, profileMatrix_inverse_row_sum N p, ← profileForm_slash_coeff_zero_sum N γ p] at h
  unfold uniformProfileOffset
  rw [div_eq_mul_inv]
  linear_combination -h

#print axioms rightPrimitive
#print axioms unitPermutation_rightPrimitive
#print axioms division_slash_primitive_coeff_zero
#print axioms profileMatrix_transported
#print axioms profileMatrix_recover_transported
#print axioms profileForm_slash_coeff_zero

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants
