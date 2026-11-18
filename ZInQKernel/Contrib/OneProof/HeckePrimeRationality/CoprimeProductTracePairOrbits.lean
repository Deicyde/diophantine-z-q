import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceActualProducts
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinCoprimeFiberMoves

/-!
# Actual determinant-pair orbits for a coprime prime

Equal nonzero determinant pairs over a field are related by a determinant-one
matrix. Coprime strong approximation lifts this motion to the actual integral
principal group while retaining all lower residue coordinates.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups Matrix

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

/-- Two independent row pairs with the same determinant have an actual SL₂ motion. -/
theorem exists_SL2_determinant_pair_move {K : Type*} [Field K]
    (T U V W : Pair K) (d : K) (hd : d ≠ 0) (hTU : det T U = d) (hVW : det V W = d) :
    ∃ γ : SL(2, K), ![T.1,T.2] ᵥ* γ.1 = ![V.1,V.2] ∧
      ![U.1,U.2] ᵥ* γ.1 = ![W.1,W.2] := by
  have hA : (!![T.1,T.2;d⁻¹ * U.1,d⁻¹ * U.2] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [Matrix.det_fin_two]
    have ht := congrArg (fun z : K => d⁻¹ * z) hTU
    rw [inv_mul_cancel₀ hd] at ht
    dsimp [det] at ht
    linear_combination ht
  have hB : (!![V.1,V.2;d⁻¹ * W.1,d⁻¹ * W.2] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [Matrix.det_fin_two]
    have ht := congrArg (fun z : K => d⁻¹ * z) hVW
    rw [inv_mul_cancel₀ hd] at ht
    dsimp [det] at ht
    linear_combination ht
  let A : SL(2, K) := ⟨!![T.1,T.2;d⁻¹ * U.1,d⁻¹ * U.2], hA⟩
  let B : SL(2, K) := ⟨!![V.1,V.2;d⁻¹ * W.1,d⁻¹ * W.2], hB⟩
  let γ := A⁻¹ * B
  have he : A * γ = B := by dsimp [γ]; rw [mul_inv_cancel_left]
  have hrow0 : ![T.1,T.2] ᵥ* γ.1 = ![V.1,V.2] := by
    ext i
    have h := congrArg (fun G : SL(2, K) => G 0 i) he
    fin_cases i <;> simpa [A, B, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h
  have hrow1 : (d⁻¹ • (![U.1,U.2] : Fin 2 → K)) ᵥ* γ.1 = d⁻¹ • ![W.1,W.2] := by
    ext i
    have h := congrArg (fun G : SL(2, K) => G 1 i) he
    fin_cases i <;> simpa [A, B, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h
  rw [Matrix.smul_vecMul] at hrow1
  have hh := congrArg (fun v : Fin 2 → K => d • v) hrow1
  simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at hh
  exact ⟨γ, hrow0, hh⟩

/-- Actual simultaneous principal-group motion of independent integer row pairs
with the same nonzero prime determinant and the same lower residue rows. -/
theorem exists_Gamma_determinant_pair_move (p N : ℕ) [Fact p.Prime]
    (hcop : Nat.Coprime p N) (a b c d r s t u : ℤ)
    (hdet : (a : ZMod p) * d - (b : ZMod p) * c = (r : ZMod p) * u - (s : ZMod p) * t)
    (hne : (a : ZMod p) * d - (b : ZMod p) * c ≠ 0)
    (ha : (a : ZMod N) = r) (hb : (b : ZMod N) = s)
    (hc : (c : ZMod N) = t) (hd : (d : ZMod N) = u) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma N ∧
      (((![a,b] ᵥ* γ.1) 0 : ℤ) : ZMod (p * N)) = r ∧
      (((![a,b] ᵥ* γ.1) 1 : ℤ) : ZMod (p * N)) = s ∧
      (((![c,d] ᵥ* γ.1) 0 : ℤ) : ZMod (p * N)) = t ∧
      (((![c,d] ᵥ* γ.1) 1 : ℤ) : ZMod (p * N)) = u := by
  obtain ⟨G, hG0, hG1⟩ := exists_SL2_determinant_pair_move
    ((a : ZMod p),(b : ZMod p)) ((c : ZMod p),(d : ZMod p))
    ((r : ZMod p),(s : ZMod p)) ((t : ZMod p),(u : ZMod p))
    ((a : ZMod p) * d - (b : ZMod p) * c) hne rfl hdet.symm
  obtain ⟨γ, hγ, hmap⟩ := exists_mem_Gamma_map_intCast_zmod_eq hcop G
  have hrow (v w x y : ℤ) (hG : ![(v : ZMod p),(w : ZMod p)] ᵥ* G.1 = ![(x : ZMod p),(y : ZMod p)])
      (i : Fin 2) : (((![v,w] ᵥ* γ.1) i : ℤ) : ZMod p) = (![x,y] i : ZMod p) := by
    have h := RingHom.map_vecMul (Int.castRingHom (ZMod p)) γ.1 ![v,w] i
    have hmat : γ.1.map (Int.castRingHom (ZMod p)) = G.1 := congrArg Subtype.val hmap
    rw [hmat] at h
    have hv : ((Int.castRingHom (ZMod p)) ∘ (![v,w] : Fin 2 → ℤ)) =
        (![(v : ZMod p),(w : ZMod p)] : Fin 2 → ZMod p) := by
      ext j; fin_cases j <;> rfl
    rw [hv, hG] at h
    fin_cases i <;> simpa using h
  have hNrow (v w : ℤ) (i : Fin 2) : (((![v,w] ᵥ* γ.1) i : ℤ) : ZMod N) = (![v,w] i : ZMod N) :=
    EisensteinWeightTwo.label_intCast_Gamma N ![v,w] γ hγ i
  refine ⟨γ, hγ, ?_, ?_, ?_, ?_⟩
  · exact DivisionEisensteinLowerClosure.intCast_eq_product_of_eq p N hcop _ _
      (hrow a b r s hG0 0) ((hNrow a b 0).trans ha)
  · exact DivisionEisensteinLowerClosure.intCast_eq_product_of_eq p N hcop _ _
      (hrow a b r s hG0 1) ((hNrow a b 1).trans hb)
  · exact DivisionEisensteinLowerClosure.intCast_eq_product_of_eq p N hcop _ _
      (hrow c d t u hG1 0) ((hNrow c d 0).trans hc)
  · exact DivisionEisensteinLowerClosure.intCast_eq_product_of_eq p N hcop _ _
      (hrow c d t u hG1 1) ((hNrow c d 1).trans hd)

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
