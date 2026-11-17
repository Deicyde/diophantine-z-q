import ZInQKernel.Contrib.OneProof.GrossZagierSplit.QuadSplit
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# gzcd-s1: the discriminant bridge for `K = ℚ(√D)`

Task gzcd-s1 (2026-11-17). Report: `docs/research/gzcd-s1.md`; scratch and log: `scratch/gzcd-s1/`.

For a quadratic number field `K` and a negative fundamental discriminant `D`:
* `discr_eq_of_sq`: if `δ ∈ K` has `δ² = D`, then the absolute discriminant of `K` (Mathlib's
  `NumberField.discr K`) is `D` (from eps-splitting's `𝓞_K = ℤ[θ]`, `θ = (D + δ)/2`);
* `exists_sq_eq_discr`: conversely every quadratic field contains a square root of its discriminant.

So "`K` is the imaginary quadratic field of discriminant `D`" (Gross–Zagier's wording) and
"`[K : ℚ] = 2` and `K` contains `√D`" (eps-splitting's binder) are equivalent.

No `sorry`, no `axiom`.
-/

open Polynomial NumberField Module

namespace ZInQ.GZDiscr

variable {K : Type*} [Field K]

/-- **Discriminant of a basis `{1, w}`** of a quadratic extension with `w² = A w + B`:
`disc(1, w) = A² + 4B`. -/
theorem discr_basis_two [Algebra ℚ K] (c : Basis (Fin 2) ℚ K) (h0 : c 0 = 1) (A B : ℚ)
    (hw : c 1 * c 1 = A • c 1 + B • (1 : K)) :
    Algebra.discr ℚ c = A ^ 2 + 4 * B := by
  haveI : Module.Finite ℚ K := Module.Finite.of_basis c
  have hfin : finrank ℚ K = 2 := by rw [finrank_eq_card_basis c]; simp
  have htr1 : Algebra.trace ℚ K 1 = 2 := by
    rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap, hfin]; norm_num
  have htrw : Algebra.trace ℚ K (c 1) = A := by
    classical
    rw [Algebra.trace_eq_matrix_trace c, Matrix.trace, Fin.sum_univ_two]
    simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, h0, mul_one, hw, c.repr_self,
      map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply]
    have h1 : (1 : K) = c 0 := h0.symm
    rw [h1, c.repr_self, c.repr_self]
    simp
  have htrww : Algebra.trace ℚ K (c 1 * c 1) = A * A + 2 * B := by
    rw [hw, map_add, map_smul, map_smul, htrw, htr1, smul_eq_mul, smul_eq_mul]; ring
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, h0, mul_one, one_mul, htr1,
    htrw, htrww]
  ring

section Sq

variable [NumberField K] {D : ℤ} {δ : K}

open EpsSplit

/-- `{1, θ}` is a `ℤ`-basis of `𝓞_K`. -/
noncomputable def thetaBasis (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) : Basis (Fin 2) ℤ (𝓞 K) :=
  Basis.mk (v := ![1, thetaO hD hδ])
    (by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have hK' : ((s : K) + (t : K) * thetaK D δ) = 0 := by
        have := congrArg (fun y : 𝓞 K => (y : K)) hst
        simpa [zsmul_eq_mul, coe_thetaO] using this
      by_cases ht : t = 0
      · subst ht
        simp only [Int.cast_zero, zero_mul, add_zero, Int.cast_eq_zero] at hK'
        exact ⟨hK', rfl⟩
      · exfalso
        apply thetaK_ne hneg hδ (-s / t)
        have ht' : (t : K) ≠ 0 := by exact_mod_cast ht
        push_cast
        field_simp
        linear_combination hK')
    (by
      rintro x -
      obtain ⟨a, b, hab⟩ := exists_int_repr hD hneg hK hδ (RingOfIntegers.isIntegral_coe x)
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨![a, b], ?_⟩
      rw [Fin.sum_univ_two]
      ext
      simp [zsmul_eq_mul, coe_thetaO, hab])

theorem thetaBasis_apply (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) (i : Fin 2) :
    thetaBasis hD hneg hK hδ i = ![1, thetaO hD hδ] i := by
  simp [thetaBasis]

/-- **`disc(K) = D`** for `K = ℚ(√D)`, `D < 0` a fundamental discriminant. -/
theorem discr_eq_of_sq (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) : discr K = D := by
  rw [← discr_eq_discr K (thetaBasis hD hneg hK hδ)]
  apply Int.cast_injective (α := ℚ)
  rw [← eq_intCast (algebraMap ℤ ℚ), ← Algebra.discr_localizationLocalization ℤ ℤ⁰ K]
  have h4 := four_mul_cD hD.1
  have hval : Algebra.discr ℚ ((thetaBasis hD hneg hK hδ).localizationLocalization ℚ ℤ⁰ K) =
      (D : ℚ) ^ 2 + 4 * (-(cD D : ℚ)) := by
    apply discr_basis_two
    · simp [Basis.localizationLocalization_apply, thetaBasis_apply]
    · simp only [Basis.localizationLocalization_apply, thetaBasis_apply, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      show (thetaO hD hδ : K) * (thetaO hD hδ : K) = _
      rw [coe_thetaO, Rat.smul_def, Rat.smul_def, mul_one]
      have h4K : (4 : K) * (cD D : K) = (D : K) ^ 2 - D := by exact_mod_cast congrArg (Int.cast (R := K)) h4
      simp only [thetaK]
      push_cast
      linear_combination (1 / 4 : K) * hδ + (1 / 4 : K) * h4K
  rw [hval]
  have h4Q : (4 : ℚ) * (cD D : ℚ) = (D : ℚ) ^ 2 - D := by exact_mod_cast h4
  linear_combination -h4Q

end Sq

section Exists

variable [NumberField K]

/-- **Every quadratic field contains a square root of its discriminant.** -/
theorem exists_sq_eq_discr (hK : finrank ℚ K = 2) : ∃ δ : K, δ ^ 2 = (discr K : K) := by
  -- an element outside `ℚ`
  obtain ⟨w, hw⟩ : ∃ w : K, w ∉ Set.range (algebraMap ℚ K) := by
    by_contra h
    push_neg at h
    have : finrank ℚ K = 1 := by
      have hbot : (⊥ : Subalgebra ℚ K) = ⊤ := by
        rw [eq_top_iff]; intro x _; exact h x
      rw [← Subalgebra.finrank_top', ← hbot, Subalgebra.finrank_bot]
    omega
  have hli : LinearIndependent ℚ ![(1 : K), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hw ⟨-s / t, ?_⟩
      rw [Rat.smul_def, Rat.smul_def, mul_one] at hst
      have ht' : (t : K) ≠ 0 := by exact_mod_cast ht
      rw [eq_ratCast]
      push_cast
      field_simp
      linear_combination hst
  let c := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  have hc0 : c 0 = 1 := by simp [c]
  have hc1 : c 1 = w := by simp [c]
  set A := c.repr (w * w) 1
  set B := c.repr (w * w) 0
  have hww : c 1 * c 1 = A • c 1 + B • (1 : K) := by
    have := c.sum_repr (w * w)
    rw [Fin.sum_univ_two, hc0, hc1] at this
    rw [hc1, ← this, add_comm]
  have hdc := discr_basis_two c hc0 A B hww
  -- compare with an integral basis
  let b' := (integralBasis K).reindex ((integralBasis K).indexEquiv c)
  have hb' : (⇑b' : Fin 2 → K) = Matrix.vecMul (⇑c) ((c.toMatrix b').map (algebraMap ℚ K)) := by
    funext j
    rw [← c.sum_toMatrix_smul_self b' j]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Algebra.smul_def]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdisc : (discr K : ℚ) = (c.toMatrix b').det ^ 2 * (A ^ 2 + 4 * B) := by
    rw [coe_discr, ← hdc, ← Algebra.discr_of_matrix_vecMul, ← hb']
    simp only [b', Basis.coe_reindex, Algebra.discr_reindex]
  refine ⟨((c.toMatrix b').det : K) * (2 * w - (A : K)), ?_⟩
  have : ((discr K : ℤ) : K) = (((discr K : ℚ)) : K) := (Rat.cast_intCast _).symm
  rw [this, hdisc]
  have hww' : w * w = (A : K) * w + (B : K) := by
    rw [← hc1, hww, Rat.smul_def, Rat.smul_def, mul_one]
  push_cast
  linear_combination (4 * ((c.toMatrix b').det : K) ^ 2) * hww'

end Exists

end ZInQ.GZDiscr
