import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinRepeatedPrimeTrace

/-!
# Actual principal-group moves across a coprime-prime fibre

For p coprime to N, strong approximation realizes any special-linear motion
of nonzero rows modulo p while fixing every row modulo N. The resulting
integral principal-group matrix identifies actual upper residue classes.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups Matrix

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure

/-- A nonzero field row can be moved to the first coordinate row by an explicit determinant-one matrix. -/
theorem exists_SL2_row_to_one {K : Type*} [Field K] (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ A : SL(2, K), ![a,b] ᵥ* A.1 = ![1,0] := by
  rcases hab with ha | hb
  · have hd : ( !![a⁻¹,-b;0,a] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      simp [Matrix.det_fin_two, inv_mul_cancel₀ ha]
    refine ⟨⟨!![a⁻¹,-b;0,a], hd⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_inv_cancel₀ ha]
    ring
  · have hd : (!![0,-b;b⁻¹,a] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      simp [Matrix.det_fin_two, mul_inv_cancel₀ hb]
    refine ⟨⟨!![0,-b;b⁻¹,a], hd⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_inv_cancel₀ hb]
    ring

/-- Every two nonzero field rows lie in the same actual special-linear orbit. -/
theorem exists_SL2_nonzero_row_move {K : Type*} [Field K] (a b c d : K)
    (hab : a ≠ 0 ∨ b ≠ 0) (hcd : c ≠ 0 ∨ d ≠ 0) :
    ∃ A : SL(2, K), ![a,b] ᵥ* A.1 = ![c,d] := by
  obtain ⟨U, hU⟩ := exists_SL2_row_to_one a b hab
  obtain ⟨V, hV⟩ := exists_SL2_row_to_one c d hcd
  refine ⟨U * V⁻¹, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.vecMul_vecMul, hU, ← hV,
    Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

/-- Equality modulo two coprime positive moduli implies equality modulo their product. -/
theorem intCast_eq_product_of_eq (p N : ℕ) (hcop : Nat.Coprime p N) (u v : ℤ)
    (hp : (u : ZMod p) = v) (hN : (u : ZMod N) = v) :
    (u : ZMod (p * N)) = v := by
  let e := ZMod.chineseRemainder hcop
  apply e.injective
  have heu : e (u : ZMod (p * N)) = ((u : ZMod p),(u : ZMod N)) := by
    rw [show e = ZMod.chineseRemainder hcop from rfl, map_intCast]
    rfl
  have hev : e (v : ZMod (p * N)) = ((v : ZMod p),(v : ZMod N)) := by
    rw [show e = ZMod.chineseRemainder hcop from rfl, map_intCast]
    rfl
  rw [heu, hev, hp, hN]

/-- All nonzero p-residue points in an N-fibre are linked by actual Gamma(N) matrices. -/
theorem exists_Gamma_coprime_fiber_move (p N : ℕ) [Fact p.Prime] (hcop : Nat.Coprime p N)
    (a b c d : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (hcd : (c : ZMod p) ≠ 0 ∨ (d : ZMod p) ≠ 0)
    (hc : (a : ZMod N) = c) (hd : (b : ZMod N) = d) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma N ∧
      (((![a,b] ᵥ* γ.1) 0 : ℤ) : ZMod (p * N)) = (c : ZMod (p * N)) ∧
      (((![a,b] ᵥ* γ.1) 1 : ℤ) : ZMod (p * N)) = (d : ZMod (p * N)) := by
  obtain ⟨A, hA⟩ := exists_SL2_nonzero_row_move (a : ZMod p) (b : ZMod p) c d hab hcd
  obtain ⟨γ, hγ, hmap⟩ := exists_mem_Gamma_map_intCast_zmod_eq hcop A
  have hrow (i : Fin 2) : (((![a,b] ᵥ* γ.1) i : ℤ) : ZMod p) = (![c,d] i : ZMod p) := by
    have h := RingHom.map_vecMul (Int.castRingHom (ZMod p)) γ.1 ![a,b] i
    have he : γ.1.map (Int.castRingHom (ZMod p)) = A.1 := by
      exact congrArg Subtype.val hmap
    rw [he] at h
    have hv : ((Int.castRingHom (ZMod p)) ∘ (![a,b] : Fin 2 → ℤ)) =
        (![(a : ZMod p),(b : ZMod p)] : Fin 2 → ZMod p) := by
      ext j; fin_cases j <;> rfl
    rw [hv, hA] at h
    fin_cases i <;> simpa using h
  have hNrow (i : Fin 2) : (((![a,b] ᵥ* γ.1) i : ℤ) : ZMod N) = (![a,b] i : ZMod N) :=
    EisensteinWeightTwo.label_intCast_Gamma N ![a,b] γ hγ i
  refine ⟨γ, hγ, ?_, ?_⟩
  · apply intCast_eq_product_of_eq p N hcop
    · exact hrow 0
    · exact (hNrow 0).trans hc
  · apply intCast_eq_product_of_eq p N hcop
    · exact hrow 1
    · exact (hNrow 1).trans hd

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure
