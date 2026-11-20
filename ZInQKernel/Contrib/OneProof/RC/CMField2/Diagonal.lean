import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare

/-! The diagonal modular polynomial gives an integral equation at a cyclic self-isogeny.
On-the-spot calculation (c). -/

noncomputable section

open Polynomial ModularCurve

namespace ZInQ.Manuscript.RC.CMField2

/-- Evaluation commutes with substituting the same variable into both slots of Φ. -/
theorem eval_diagonal {F : Type*} [CommRing F] (P : ℤ[X][X]) (z : F) :
    (P.eval₂ (RingHom.id ℤ[X]) X).eval₂ (Int.castRingHom F) z =
      (P.map (eval₂RingHom (Int.castRingHom F) z)).eval z := by
  rw [eval_map]
  simpa only [RingHom.comp_id, coe_eval₂RingHom, eval₂_X] using
    hom_eval₂ P (RingHom.id ℤ[X]) (eval₂RingHom (Int.castRingHom F) z) X

/-- A complex period lattice with a cyclic self-isogeny of nonsquare degree has integral j. -/
theorem isIntegral_jLattice_of_cyclicSelf (N : ℕ) [NeZero N] (hN : ¬ IsSquare N)
    (L L' : PeriodPair) (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice)
    (hidx : L.sublatticeIndex L' = N) (hcyc : IsAddCyclic (L.sublatticeQuotient L'))
    (hj : L'.jLattice = L.jLattice) : IsIntegral ℤ L.jLattice := by
  obtain ⟨P⟩ := nonempty_modularPolynomialData N
  let D : ℤ[X] := P.Φ.eval₂ (RingHom.id _) X
  have hD : IsUnit D.leadingCoeff := ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare N hN P
  have hz := ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic N P L L' hsub hidx hcyc
  rw [hj, ← eval_diagonal] at hz
  let u := hD.unit
  have hu : (↑u : ℤ) = D.leadingCoeff := hD.unit_spec
  refine ⟨C (↑u⁻¹ : ℤ) * D, monic_C_mul_of_mul_leadingCoeff_eq_one ?_, ?_⟩
  · rw [← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · change eval₂ (Int.castRingHom ℂ) L.jLattice (C (↑u⁻¹ : ℤ) * D) = 0
    rw [eval₂_mul, show D.eval₂ (Int.castRingHom ℂ) L.jLattice = 0 from hz, mul_zero]

/-- The norm polynomial of n + ω has a value of nonsquare degree. The hypothesis
is the negativity of the discriminant, in the form trace² < 4 * norm. -/
theorem exists_nonsquare_quadratic_value (t u : ℤ) (h : t ^ 2 < 4 * u) :
    ∃ n m : ℤ, 1 ≤ m ∧ m ^ 2 < n ^ 2 + t * n + u ∧
      n ^ 2 + t * n + u < (m + 1) ^ 2 := by
  let q := t / 2
  have hpar : t = 2 * q ∨ t = 2 * q + 1 := by dsimp [q]; omega
  cases hpar with
  | inl ht =>
    have hu : 0 < u - q ^ 2 := by rw [ht] at h; nlinarith
    let m := u - q ^ 2
    have hm : 1 ≤ m := by dsimp [m]; omega
    have he : (m - q) ^ 2 + t * (m - q) + u = m ^ 2 + m := by
      rw [ht]; dsimp [m]; ring
    refine ⟨m - q, m, hm, ?_, ?_⟩
    · rw [he]; omega
    · rw [he]; nlinarith
  | inr ht =>
    have hu : 0 ≤ u - q ^ 2 - q := by
      by_contra! hn
      have hn' : u - q ^ 2 - q ≤ -1 := by omega
      rw [ht] at h
      nlinarith
    let m := u - q ^ 2 - q + 1
    have hm : 1 ≤ m := by dsimp [m]; omega
    have he : (m - q) ^ 2 + t * (m - q) + u = m ^ 2 + m + (m - 1) := by
      rw [ht]; dsimp [m]; ring
    refine ⟨m - q, m, ?_, ?_, ?_⟩
    · exact hm
    · rw [he]; omega
    · rw [he]; nlinarith

/-- Diagonal root multiplicities of the specialized modular polynomial are
preserved by embeddings of the field containing the specialization. -/
theorem rootMultiplicity_specialization_eq_of_embeddings {F : Type*} [Field F]
    (P : ℤ[X][X]) (e f : F →+* ℂ) (x : F) :
    rootMultiplicity (e x) (P.map (eval₂RingHom (Int.castRingHom ℂ) (e x))) =
      rootMultiplicity (f x) (P.map (eval₂RingHom (Int.castRingHom ℂ) (f x))) := by
  let q := P.map (eval₂RingHom (Int.castRingHom F) x)
  have he (g : F →+* ℂ) :
      q.map g = P.map (eval₂RingHom (Int.castRingHom ℂ) (g x)) := by
    rw [show q = _ from rfl, map_map]
    congr 1
    apply Polynomial.ringHom_ext'
    · rw [RingHom.comp_assoc, eval₂RingHom_comp_C, eval₂RingHom_comp_C]
      exact Subsingleton.elim _ _
    · simp
  rw [← he e, ← he f, ← eq_rootMultiplicity_map e.injective, ← eq_rootMultiplicity_map f.injective]


end ZInQ.Manuscript.RC.CMField2
