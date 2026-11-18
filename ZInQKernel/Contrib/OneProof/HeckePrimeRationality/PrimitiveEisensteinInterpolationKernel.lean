import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinFiniteStabilizer

/-!
# The actual complete finite constant-term interpolation kernel

The entire SL₂(ℤ/Nℤ) sum is reindexed, not replaced by a guessed orbit.
The two actual axis fibres are enumerated by their proved equivalences.
Translation invariance and central parity of the actual quotient constants
make each of the N positive and N negative contributions equal to bσ.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Complex Filter Set UpperHalfPlane Matrix Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinInterpolation
open ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinConstants

lemma sum_positive_fibre (N : ℕ) [NeZero N] (F : SL(2, ZMod N) → ℂ) :
    (∑ A : SL(2, ZMod N), if positiveRow N ᵥ* A = positiveRow N then F A else 0) =
      ∑ t : ZMod N, F (unipotent N t) := by
  have hs : (∑ A : SL(2, ZMod N), if positiveRow N ᵥ* A = positiveRow N then F A else 0) =
      ∑ A : {A : SL(2, ZMod N) // positiveRow N ᵥ* A = positiveRow N}, F A.1 := by
    calc (∑ A : SL(2, ZMod N), if positiveRow N ᵥ* A = positiveRow N then F A else 0) =
        ∑ A ∈ {A : SL(2, ZMod N) | positiveRow N ᵥ* A = positiveRow N}.toFinset, F A := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext A; simp
          · intro A _; rfl
      _ = _ := Finset.sum_toFinset_eq_subtype (fun A : SL(2, ZMod N) => positiveRow N ᵥ* A = positiveRow N) F
  rw [hs,← (positiveFibreEquiv N).sum_comp (fun A => F A.1)]
  rfl

lemma sum_negative_fibre (N : ℕ) [NeZero N] (F : SL(2, ZMod N) → ℂ) :
    (∑ A : SL(2, ZMod N), if positiveRow N ᵥ* A = negativeRow N then F A else 0) =
      ∑ t : ZMod N, F (-unipotent N t) := by
  have hs : (∑ A : SL(2, ZMod N), if positiveRow N ᵥ* A = negativeRow N then F A else 0) =
      ∑ A : {A : SL(2, ZMod N) // positiveRow N ᵥ* A = negativeRow N}, F A.1 := by
    calc (∑ A : SL(2, ZMod N), if positiveRow N ᵥ* A = negativeRow N then F A else 0) =
        ∑ A ∈ {A : SL(2, ZMod N) | positiveRow N ᵥ* A = negativeRow N}.toFinset, F A := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext A; simp
          · intro A _; rfl
      _ = _ := Finset.sum_toFinset_eq_subtype (fun A : SL(2, ZMod N) => positiveRow N ᵥ* A = negativeRow N) F
  rw [hs,← (negativeFibreEquiv N).sum_comp (fun A => F A.1)]
  rfl

lemma weight_sign_square (k : ℕ) : (-1 : ℂ)^k * (-1 : ℂ)^k = 1 := by
  rw [← mul_pow]
  simp

/-- The exact 2N interpolation factor is proved from the full finite group,
with the coefficient function taken from the actual modular form. -/
theorem actual_constant_kernel (N : ℕ) [NeZero N] (_hN : 3 ≤ N)
    (k : ℕ) (f : ModularForm (principalReal N) (k : ℤ)) (σ : SL(2, ZMod N)) :
    (∑ A : SL(2, ZMod N), finiteConstants N (k : ℤ) f A *
      constantProfile N k (positiveRow N ᵥ* (A⁻¹*σ : SL(2, ZMod N)))) =
      (2*(N : ℂ)) * finiteConstants N (k : ℤ) f σ := by
  let e : SL(2, ZMod N) ≃ SL(2, ZMod N) := (Equiv.inv _).trans (Equiv.mulLeft σ)
  have he (A : SL(2, ZMod N)) : e A = σ*A⁻¹ := rfl
  have hk (A : SL(2, ZMod N)) : (e A)⁻¹*σ = A := by
    rw [he,_root_.mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one]
  rw [← e.sum_comp (fun A : SL(2, ZMod N) => finiteConstants N (k : ℤ) f A *
    constantProfile N k (positiveRow N ᵥ* (A⁻¹*σ : SL(2, ZMod N))))]
  simp_rw [hk]
  simp only [he,constantProfile,mul_add,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero]
  rw [sum_positive_fibre,sum_negative_fibre]
  have hp (t : ZMod N) : finiteConstants N (k : ℤ) f (σ*(unipotent N t)⁻¹) = finiteConstants N (k : ℤ) f σ := by
    rw [unipotent_inv,finiteConstants_unipotent]
  have hn (t : ZMod N) : finiteConstants N (k : ℤ) f (σ*(-unipotent N t)⁻¹) * (-1 : ℂ)^k =
      finiteConstants N (k : ℤ) f σ := by
    rw [inv_neg,unipotent_inv,mul_neg,finiteConstants_neg,finiteConstants_unipotent]
    calc (-1 : ℂ)^k * finiteConstants N (k : ℤ) f σ * (-1 : ℂ)^k =
        ((-1 : ℂ)^k * (-1 : ℂ)^k) * finiteConstants N (k : ℤ) f σ := by ring
      _ = _ := by rw [weight_sign_square,one_mul]
  simp only [hp,hn,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,ZMod.card]
  ring

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinInterpolation
