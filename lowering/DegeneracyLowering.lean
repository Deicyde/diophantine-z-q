import lowering.RationalTraceOrbit
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Basic

/-!
# Nonzero degeneracy lowering inside the original rational translate orbit

The adjoint is the actual trace of the main-involution translate. Its finite
positive rational coset slashes preserve the orbit. The center compatibility of
the actual Petersson trace identity is handled explicitly by extending forms
only when their actual weight makes the central slash trivial.
-/

noncomputable section
set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open HeckeRing.GLn
open scoped MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.ReverseHecke

/-- The central negative identity belongs to every center-adjoined integral subgroup. -/
theorem neg_one_mem_withCenter (Γ : Subgroup SL(2, ℤ)) :
    (-1 : SL(2, ℤ)) ∈ Γ.withCenter :=
  Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mpr ⟨1, Γ.one_mem, Or.inr rfl⟩

/-- A nonzero actual form fixed by the negative identity forces its central weight scalar to one. -/
theorem central_scalar_eq_one (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (g : CuspForm (Γ.map (mapGL ℝ)) k) (hg : g ≠ 0) :
    (-1 : ℂ) ^ k = 1 := by
  have hs := g.slash_action_eq' (-1 : GL (Fin 2) ℝ)
    (Subgroup.mem_map.mpr ⟨-1, hneg, mapGL_neg_one⟩)
  rw [_root_.ModularForm.slash_neg_one] at hs
  obtain ⟨τ, hτ⟩ : ∃ τ : ℍ, g τ ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (DFunLike.ext _ _ fun τ ↦ h τ)
  have hp := congrFun hs τ
  simp only [Pi.smul_apply, smul_eq_mul] at hp
  exact mul_right_cancel₀ hτ (hp.trans (one_mul (g τ)).symm)

/-- A trivial central weight scalar gives actual slash invariance under the center-adjoined group. -/
theorem invariant_withCenter (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (hk : (-1 : ℂ) ^ k = 1) (g : CuspForm (Γ.map (mapGL ℝ)) k) :
    ∀ δ ∈ Γ.withCenter.map (mapGL ℝ), ⇑g ∣[k] δ = ⇑g := by
  rintro δ ⟨γ, hγ, rfl⟩
  obtain ⟨γ', hγ', hcase⟩ := Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mp hγ
  rcases hcase with rfl | rfl
  · exact g.slash_action_eq' _ (Subgroup.mem_map_of_mem _ hγ')
  · rw [← mul_neg_one γ', map_mul, mapGL_neg_one, SlashAction.slash_mul,
      _root_.ModularForm.slash_neg_one, hk, one_smul]
    exact g.slash_action_eq' _ (Subgroup.mem_map_of_mem _ hγ')

/-- Extend an actual cusp form to the center-adjoined group, preserving every value and every cusp. -/
def centerLift (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (hk : (-1 : ℂ) ^ k = 1) (g : CuspForm (Γ.map (mapGL ℝ)) k) :
    CuspForm (Γ.withCenter.map (mapGL ℝ)) k :=
  CuspForm.ofSlashInvariant
    (fun c hc ↦ Subgroup.IsArithmetic.isCusp_of_isCusp c hc) g (invariant_withCenter Γ k hk g)

/-- Center extension does not change the actual function. -/
theorem centerLift_coe (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (hk : (-1 : ℂ) ^ k = 1) (g : CuspForm (Γ.map (mapGL ℝ)) k) :
    ⇑(centerLift Γ k hk g) = ⇑g := by
  rw [centerLift, CuspForm.coe_ofSlashInvariant]

/-- The actual unnormalized coset Petersson pairing is unchanged by center extension. -/
theorem petersson_centerLift (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (hk : (-1 : ℂ) ^ k = 1) (g h : CuspForm (Γ.map (mapGL ℝ)) k) :
    CuspForm.peterssonInnerCosets (centerLift Γ k hk g) (centerLift Γ k hk h) =
      CuspForm.peterssonInnerCosets g h := by
  have hid : Γ.withCenter.withCenter = Γ.withCenter := by
    simp [Subgroup.withCenter_def]
  have hg : CuspForm.restrict (Subgroup.map_mono Γ.le_withCenter) (centerLift Γ k hk g) = g := by
    apply DFunLike.coe_injective
    rw [CuspForm.coe_restrict, centerLift_coe]
  have hh : CuspForm.restrict (Subgroup.map_mono Γ.le_withCenter) (centerLift Γ k hk h) = h := by
    apply DFunLike.coe_injective
    rw [CuspForm.coe_restrict, centerLift_coe]
  have hp := CuspForm.peterssonInnerCosets_restrict_restrict
    (Subgroup.map_mono Γ.le_withCenter) (centerLift Γ k hk g) (centerLift Γ k hk h)
  rw [hg, hh, hid, Subgroup.relIndex_self, Nat.cast_one, one_mul] at hp
  exact hp.symm

/-- A conjugated integral subgroup inclusion remains valid after adjoining the common center. -/
theorem conjugate_inclusion_withCenter (Γ Γ' : Subgroup SL(2, ℤ)) (α : GL (Fin 2) ℝ)
    (hle : Γ'.map (mapGL ℝ) ≤ ConjAct.toConjAct α⁻¹ • Γ.map (mapGL ℝ)) :
    Γ'.withCenter.map (mapGL ℝ) ≤ ConjAct.toConjAct α⁻¹ • Γ.withCenter.map (mapGL ℝ) := by
  have hinc : ConjAct.toConjAct α⁻¹ • Γ.map (mapGL ℝ) ≤
      ConjAct.toConjAct α⁻¹ • Γ.withCenter.map (mapGL ℝ) := by
    change (Γ.map (mapGL ℝ)).map (MulAut.conj α⁻¹).toMonoidHom ≤
      (Γ.withCenter.map (mapGL ℝ)).map (MulAut.conj α⁻¹).toMonoidHom
    exact Subgroup.map_mono (Subgroup.map_mono Γ.le_withCenter)
  rintro δ ⟨γ, hγ, rfl⟩
  obtain ⟨γ', hγ', hcase⟩ := Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mp hγ
  have hb := hinc (hle (Subgroup.mem_map_of_mem (mapGL ℝ) hγ'))
  rcases hcase with rfl | rfl
  · exact hb
  · rw [← mul_neg_one γ', map_mul, mapGL_neg_one]
    exact Subgroup.mul_mem _ hb (Subgroup.mem_conjAct_smul_of_mem_center
      (Subgroup.mem_center_iff.mpr fun x ↦ by rw [mul_neg_one, neg_one_mul]) α⁻¹
      (Subgroup.mem_map.mpr ⟨-1, neg_one_mem_withCenter Γ, mapGL_neg_one⟩))

/-- The genuine adjoint trace is nonzero when the actual translated restriction pairs nontrivially. -/
theorem exists_nonzero_adjoint_trace_in_orbit
    (Γ Γ' : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [Γ'.FiniteIndex]
    (α : GL (Fin 2) ℚ) (hint : HasIntEntries 2 α)
    (hpos : 0 < (α : Matrix (Fin 2) (Fin 2) ℚ).det)
    (hle : Γ'.map (mapGL ℝ) ≤ ConjAct.toConjAct
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) α)⁻¹ • Γ.map (mapGL ℝ))
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ ↔ (-1 : SL(2, ℤ)) ∈ Γ')
    (k : ℤ) (f : ℍ → ℂ) (F : CuspForm (Γ'.map (mapGL ℝ)) k)
    (hF : ⇑F ∈ functionOrbit k f) (g : CuspForm (Γ.map (mapGL ℝ)) k)
    (hpair : CuspForm.peterssonInnerCosets
      (CuspForm.restrict hle (CuspForm.translate g (GeneralLinearGroup.map (algebraMap ℚ ℝ) α))) F ≠ 0) :
    ∃ G : CuspForm (Γ.map (mapGL ℝ)) k, G ≠ 0 ∧ ⇑G ∈ functionOrbit k f := by
  let : (ConjAct.toConjAct (GeneralLinearGroup.map (algebraMap ℚ ℝ) α)⁻¹ •
      Γ.map (mapGL ℝ)).IsFiniteRelIndex (Γ'.map (mapGL ℝ)) :=
    finiteRelIndex_conj_integral_rational Γ' Γ α hint
  let : (ConjAct.toConjAct (GeneralLinearGroup.map (algebraMap ℚ ℝ) (TauCeti.adjugateGL α))⁻¹ •
      Γ'.map (mapGL ℝ)).IsFiniteRelIndex (Γ.map (mapGL ℝ)) :=
    finiteRelIndex_conj_integral_rational Γ Γ' (TauCeti.adjugateGL α)
      (hasIntEntries_adjugate_rational hint)
  let : (ConjAct.toConjAct (TauCeti.adjugateGL
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) α))⁻¹ •
      Γ'.map (mapGL ℝ)).IsFiniteRelIndex (Γ.map (mapGL ℝ)) := by
    rw [← map_adjugate_rational]
    infer_instance
  let G := CuspForm.trace (Γ.map (mapGL ℝ))
    (CuspForm.translate F (TauCeti.adjugateGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) α)))
  have hadj := CuspForm.peterssonInnerCosets_trace_translate
    (_root_.ModularForm.det_map_ratCast_pos hpos) hneg g F
  rw [cusp_trace_eq_restrict_of_le _ _ hle k] at hadj
  refine ⟨G, ?_, ?_⟩
  · intro hG
    apply hpair
    change CuspForm.peterssonInnerCosets _ F = CuspForm.peterssonInnerCosets g G at hadj
    simpa only [hG, CuspForm.peterssonInnerCosets_zero_right] using hadj
  · apply cusp_trace_mem_functionOrbit Γ _ k f
    rw [CuspForm.coe_translate, ← map_adjugate_rational]
    exact slash_mem_functionOrbit k f hF (TauCeti.adjugateGL α)
      (positive_adjugate_rational hpos)

/-- The actual rational dilation is integral. -/
theorem scaleGLRat_hasIntEntries (d : ℕ) [NeZero d] : HasIntEntries 2 (TauCeti.scaleGLRat d) := by
  apply (hasIntEntries_iff 2).mpr
  refine ⟨!![(d : ℤ), 0; 0, 1], ?_⟩
  rw [TauCeti.scaleGLRat, TauCeti.diagGL_coe, Matrix.diagonal_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The actual rational dilation has positive determinant. -/
theorem scaleGLRat_det_pos (d : ℕ) [NeZero d] :
    0 < (TauCeti.scaleGLRat d : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [TauCeti.scaleGLRat, TauCeti.diagGL_coe, Matrix.diagonal_fin_two, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mk0,
    Units.val_one, mul_one, mul_zero, sub_zero]
  exact_mod_cast NeZero.pos d

/-- A nonzero degeneracy pairing yields a nonzero lower actual cusp in the original orbit.
The center condition is explicit here; the full actual-level endpoint discharges it separately. -/
theorem exists_lower_cusp_of_pairing_same_center (L M d : ℕ) [NeZero L]
    (hdvd : d * M ∣ L)
    (hneg : (-1 : SL(2, ℤ)) ∈ Gamma1 M ↔ (-1 : SL(2, ℤ)) ∈ Gamma1 L)
    (k : ℤ) (f : ℍ → ℂ) (F : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (hF : ⇑F ∈ functionOrbit k f) (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hpair : haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
      CuspForm.peterssonInnerCosets
        (TauCeti.CuspForm.levelRaise d (TauCeti.Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) g) F ≠ 0) :
    ∃ G : CuspForm ((Gamma1 M).map (mapGL ℝ)) k, G ≠ 0 ∧ ⇑G ∈ functionOrbit k f := by
  let : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
  let : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
  have hle := TauCeti.Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd
  have hV : TauCeti.CuspForm.levelRaise d hle g =
      (d : ℂ) ^ (1 - k) • CuspForm.restrict hle (CuspForm.translate g (TauCeti.scaleGL d)) := by
    apply DFunLike.coe_injective
    rw [TauCeti.CuspForm.coe_levelRaise, FunLike.coe_smul,
      CuspForm.coe_restrict, CuspForm.coe_translate]
  have hraw : CuspForm.peterssonInnerCosets
      (CuspForm.restrict hle (CuspForm.translate g (TauCeti.scaleGL d))) F ≠ 0 := by
    intro hz
    apply hpair
    rw [hV, CuspForm.peterssonInnerCosets_smul_left, hz, mul_zero]
  have hle' : (Gamma1 L).map (mapGL ℝ) ≤ ConjAct.toConjAct
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (TauCeti.scaleGLRat d))⁻¹ •
        (Gamma1 M).map (mapGL ℝ) := by
    simpa only [TauCeti.map_ratCast_scaleGLRat] using hle
  have heq : CuspForm.restrict hle'
      (CuspForm.translate g (GeneralLinearGroup.map (algebraMap ℚ ℝ) (TauCeti.scaleGLRat d))) =
      CuspForm.restrict hle (CuspForm.translate g (TauCeti.scaleGL d)) := by
    apply DFunLike.coe_injective
    rw [CuspForm.coe_restrict, CuspForm.coe_restrict, CuspForm.coe_translate,
      CuspForm.coe_translate, TauCeti.map_ratCast_scaleGLRat]
  have hraw' : CuspForm.peterssonInnerCosets (CuspForm.restrict hle'
      (CuspForm.translate g (GeneralLinearGroup.map (algebraMap ℚ ℝ) (TauCeti.scaleGLRat d)))) F ≠ 0 := by
    rw [heq]
    exact hraw
  exact exists_nonzero_adjoint_trace_in_orbit (Gamma1 M) (Gamma1 L) (TauCeti.scaleGLRat d)
    (scaleGLRat_hasIntEntries d) (scaleGLRat_det_pos d) hle' hneg k f F hF g hraw'

end ZInQ.Contrib.HeckePrimeRationality.ReverseHecke
