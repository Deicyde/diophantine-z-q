import ZInQKernel.Contrib.OneProof.RC.CMField2.Frobenius
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_KroneckerTransport
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_transcendental_jqModC
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_dedekindPsi_prime

/-! The formal Laurent-series proof of Kronecker's polynomial congruence.
On-the-spot glue (c). -/

noncomputable section
open Polynomial ModularCurve

namespace ZInQ.Manuscript.RC.CMField2

private def swap {R : Type*} [CommRing R] : R[X][X] →+* R[X][X] :=
  eval₂RingHom (aeval (R := R) (X : R[X][X])).toRingHom (C X)

private theorem swap_reduce (p : ℕ) :
    (swap (R := ZMod p)).comp (reduceModBivar p) =
      (reduceModBivar p).comp swapBivar := by
  ext <;> simp [swap, swapBivar, swapInner, reduceModBivar]

private theorem jqMod_eq_jqModC (p : ℕ) : jqMod p = jqModC (ZMod p) := by
  rw [jqMod, jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one, jqModC]

/-- In characteristic p the reduced polynomial vanishes at Y = Xᵖ. -/
theorem modularPolynomial_reduced_root (p : ℕ) [Fact p.Prime]
    (D : ModularPolynomialData p) :
    (reduceModBivar p D.Φ).eval ((X : (ZMod p)[X]) ^ p) = 0 := by
  let q := laurentMap (Int.castRingHom ℚ)
  have hz : D.Φ.eval₂ evalAtJInt (jqIntN p) = 0 := by
    apply laurentMap_injective (f := Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
    change q (D.Φ.eval₂ evalAtJInt (jqIntN p)) = q 0
    rw [hom_eval₂, laurentMap_comp_evalAtJInt, laurentMap_jqIntN, map_zero]
    exact D.eval_eq_zero
  have ht : jqNMod p p = jqMod p ^ p := by
    rw [jqNMod, jqMod_eq_jqModC, qExpand_jqModC_eq_pow_unconditional]
  have he : Function.Injective (evalAtJMod p) := by
    rw [show evalAtJMod p = (aeval (R := ZMod p) (jqMod p)).toRingHom from rfl,
      jqMod_eq_jqModC]
    exact transcendental_iff_injective.mp (transcendental_jqModC (ZMod p))
  apply he
  rw [map_zero, ← eval₂_at_apply, map_pow, evalAtJMod_X,
    ← ht, reduceModBivar, coe_mapRingHom, eval₂_map, evalAtJMod_comp_map,
    ← laurentMap_jqIntN_mod, ← hom_eval₂, hz, map_zero]

/-- Kronecker's congruence for the monic normalized prime-level modular polynomial. -/
theorem kroneckerCongruence_of_prime (p : ℕ) [Fact p.Prime]
    (D : ModularPolynomialData p) : KroneckerCongruence p D := by
  let R := (ZMod p)[X]
  let P := reduceModBivar p D.Φ
  let L : R[X] := X - C (X ^ p)
  let T : R[X] := X ^ p - C X
  have hp : p.Prime := Fact.out
  have hroot : P.IsRoot (X ^ p) := modularPolynomial_reduced_root p D
  have hl : L ∣ P := dvd_iff_isRoot.mpr hroot
  have hs : swap P = P := by
    change (swap.comp (reduceModBivar p)) D.Φ = _
    rw [swap_reduce, RingHom.comp_apply, swapBivar_eq_of_evalSymm
      (ModularPolynomialData.evalSymm_of_prime p D)]
  have ht : T ∣ P := by
    have hmap := map_dvd swap hl
    rw [hs] at hmap
    have he : swap L = -T := by
      change swap (X - C (X ^ p)) = -(X ^ p - C X)
      simp [swap, neg_sub, eval₂_pow]
    rw [he] at hmap
    obtain ⟨q, hq⟩ := hmap
    exact ⟨-q, by rw [hq]; ring⟩
  obtain ⟨Q, hQ⟩ := ht
  have hT : T.eval (X ^ p) ≠ 0 := by
    simp only [T, eval_sub, eval_pow, eval_X, eval_C, sub_ne_zero, ← pow_mul]
    intro he
    have hd := congrArg (fun P : R => P.natDegree) he
    rw [natDegree_X_pow, natDegree_X] at hd
    nlinarith [hp.two_le]
  have hq : L ∣ Q := by
    apply dvd_iff_isRoot.mpr
    exact (mul_eq_zero.mp (show T.eval (X ^ p) * Q.eval (X ^ p) = 0 by
      rw [← eval_mul, ← hQ]; exact hroot)).resolve_left hT
  obtain ⟨Q', hQ'⟩ := hq
  have hdiv : L * T ∣ P := ⟨Q', by rw [hQ, hQ']; ring⟩
  have hmon : (L * T).Monic :=
    (monic_X_sub_C _).mul (monic_X_pow_sub_C _ hp.ne_zero)
  have hP : P.Monic := D.monic.map _
  have hdeg : P.natDegree ≤ (L * T).natDegree := by
    have hPd : P.natDegree = p + 1 := by
      simp only [P, reduceModBivar, coe_mapRingHom, D.monic.natDegree_map,
        D.natDegree_eq, dedekindPsi_prime hp]
    have hLm : L.Monic := monic_X_sub_C _
    have hTm : T.Monic := monic_X_pow_sub_C _ hp.ne_zero
    rw [hPd, natDegree_mul hLm.ne_zero hTm.ne_zero]
    change p + 1 ≤ (X - C (X ^ p) : R[X]).natDegree + (X ^ p - C X : R[X]).natDegree
    rw [natDegree_X_sub_C, natDegree_X_pow_sub_C]
    omega
  have he : P = L * T := by
    simpa only [hP.leadingCoeff, C_1, one_mul] using
      eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hmon hdiv hdeg
  change P = _
  rw [he]
  simp only [L, T, ← C_pow]
  ring

/-- An integral diagonal root reduces to a Frobenius fixed value in any residue
field of characteristic p. -/
theorem pow_eq_of_modularPolynomial_diagonal_root (p : ℕ) [Fact p.Prime]
    (D : ModularPolynomialData p) {k : Type*} [Field k] [CharP k p] (x : k)
    (hx : (D.Φ.map (eval₂RingHom (Int.castRingHom k) x)).eval x = 0) : x ^ p = x := by
  let f := ZMod.castHom (dvd_refl p) k
  let g := eval₂RingHom f x
  have hg : g.comp (mapRingHom (Int.castRingHom (ZMod p))) =
      eval₂RingHom (Int.castRingHom k) x := by
    apply Polynomial.ringHom_ext' (Subsingleton.elim _ _)
    simp [g]
  have h := congrArg (fun P : (ZMod p)[X][X] => P.eval₂ g x)
    (kroneckerCongruence_of_prime p D)
  change (reduceModBivar p D.Φ).eval₂ g x =
    (((C X : (ZMod p)[X][X]) ^ p - X) * (C X - X ^ p)).eval₂ g x at h
  rw [reduceModBivar, coe_mapRingHom, eval₂_map, hg, ← eval_map, hx] at h
  apply pow_eq_of_kronecker_diagonal p
  simpa [eval₂_mul, eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, g] using h.symm


end ZInQ.Manuscript.RC.CMField2
