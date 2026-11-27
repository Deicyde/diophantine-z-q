import ZInQKernel.HDecomp.Analytic.Hom
import ZInQKernel.HDecomp.Faltings.HodgeData

/-! # cmheight62-p1, step 3/4: the covolume of `a(ℤ + τℤ) ⊂ ℂ¹` is `|a|² Im τ`

From `BPAnalytic.covolume_periodLattice` (`g = 1`, `Ω = (τ)`) and the change of variables
`ZInQ.DefFaltings.covolume_comap_mul_det` for `z ↦ a⁻¹ z`. -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open MeasureTheory BPAnalytic ZInQ.DefFaltings

/-- Covolume does not see the instance proofs. -/
theorem covolume_congr {Λ₁ Λ₂ : Submodule ℤ (Fin 1 → ℂ)} (h : Λ₁ = Λ₂)
    [DiscreteTopology Λ₁] [IsZLattice ℝ Λ₁] [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₂] :
    ZLattice.covolume Λ₁ = ZLattice.covolume Λ₂ := by
  subst h; rfl

/-- The `1 × 1` period matrix `(τ)`. -/
def tauMat (τ : ℂ) : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => τ

theorem tauMat_det_im (τ : ℂ) : ((tauMat τ).map Complex.im).det = τ.im := by
  simp [tauMat, Matrix.det_unique]

theorem mem_periodLattice_tauMat {τ : ℂ} (hτ : ((tauMat τ).map Complex.im).det ≠ 0)
    (z : Fin 1 → ℂ) :
    z ∈ periodLattice (tauMat τ) hτ ↔ ∃ m n : ℤ, z 0 = m + n * τ := by
  unfold periodLattice
  rw [coe_periodBasis, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c (Sum.inr 0), c (Sum.inl 0), ?_⟩
    rw [← hc]
    simp [Fintype.sum_sum_type, periodVec, tauMat]
    ring
  · rintro ⟨m, n, h⟩
    refine ⟨Sum.elim (fun _ => n) (fun _ => m), ?_⟩
    funext i
    fin_cases i
    simp [Fintype.sum_sum_type, periodVec, tauMat, h]
    ring

/-- **`covol(a(ℤ + τℤ)) = |a|² Im τ`.** -/
theorem covolume_eq_of_mem_iff {τ : ℂ} (hτ : 0 < τ.im) {a : ℂ} (ha : a ≠ 0)
    (Λ : Submodule ℤ (Fin 1 → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = a * (m + n * τ)) :
    ZLattice.covolume Λ = ‖a‖ ^ 2 * τ.im := by
  have hd : ((tauMat τ).map Complex.im).det ≠ 0 := by rw [tauMat_det_im]; exact hτ.ne'
  set Λτ := periodLattice (tauMat τ) hd
  let T : (Fin 1 → ℂ) ≃ₗ[ℂ] (Fin 1 → ℂ) := LinearEquiv.smulOfNeZero ℂ (Fin 1 → ℂ) a⁻¹ (inv_ne_zero ha)
  have hcomap : Λ = ZLattice.comap ℝ Λτ (realify T).toLinearMap := by
    ext z
    change z ∈ Λ ↔ (realify T) z ∈ Λτ
    rw [hΛ, mem_periodLattice_tauMat]
    change _ ↔ ∃ m n : ℤ, (a⁻¹ • z) 0 = m + n * τ
    simp only [Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨m, n, h⟩; exact ⟨m, n, by rw [h]; field_simp⟩
    · rintro ⟨m, n, h⟩; exact ⟨m, n, by rw [← h]; field_simp⟩
  have h := covolume_comap_mul_det Λτ volume (realify T)
  have hdet : LinearMap.det ((realify T).toLinearMap : (Fin 1 → ℂ) →ₗ[ℝ] (Fin 1 → ℂ)) =
      Complex.normSq (LinearMap.det (T : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) :=
    det_restrictScalars_complex (T : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))
  have hdetT : LinearMap.det (T : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) = a⁻¹ := by
    have hT : (T : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) =
        a⁻¹ • (LinearMap.id : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) := by
      ext; simp [T]
    rw [hT, LinearMap.det_smul, LinearMap.det_id]
    simp
  have hcov : ZLattice.covolume Λτ = τ.im := by
    rw [covolume_periodLattice, tauMat_det_im, abs_of_pos hτ]
  rw [hdet, hdetT, abs_of_nonneg (Complex.normSq_nonneg _), hcov] at h
  rw [covolume_congr hcomap]
  have hn : Complex.normSq a⁻¹ ≠ 0 := by simpa using ha
  rw [Complex.normSq_inv, Complex.normSq_eq_norm_sq] at h hn
  field_simp at h ⊢
  linarith

end ZInQ.Contrib.CMHeight62
