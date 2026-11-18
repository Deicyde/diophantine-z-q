import hecke.GoodEigenformOrbit
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Petersson.Trace
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Trace
import ZInQKernel.Contrib.TauCeti.NumberTheory.HeckeRing.GLn.Basic

/-!
# Actual trace operators preserve a rational translate orbit

Every coset in an actual trace to an integral level has a determinant-one
integral representative. The resulting finite sum therefore preserves the
original positive-rational translate orbit. Integral rational matrices and their
adjugates also supply the genuine finite relative indices for the traces.
-/

noncomputable section
set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open HeckeRing.GLn Subgroup.Commensurable
open scoped MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.ReverseHecke

/-- The actual cusp trace to any integral finite-index level preserves the function orbit. -/
theorem cusp_trace_mem_functionOrbit (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsFiniteRelIndex (Γ.map (mapGL ℝ))]
    (k : ℤ) (f : ℍ → ℂ) (g : CuspForm 𝒢 k) (hg : ⇑g ∈ functionOrbit k f) :
    ⇑(CuspForm.trace (Γ.map (mapGL ℝ)) g) ∈ functionOrbit k f := by
  classical
  let : Fintype (Γ.map (mapGL ℝ) ⧸ 𝒢.subgroupOf (Γ.map (mapGL ℝ))) := Fintype.ofFinite _
  rw [CuspForm.coe_trace]
  apply Submodule.sum_mem
  intro q _
  rw [← Quotient.out_eq q, SlashInvariantForm.quotientFunc_mk]
  obtain ⟨γ, hγ, hmap⟩ := q.out.property
  have hpos : 0 < (mapGL ℚ γ⁻¹ : Matrix (Fin 2) (Fin 2) ℚ).det := by
    exact _root_.ModularForm.map_mapGL_le_glpos Γ (Subgroup.mem_map_of_mem _ (Γ.inv_mem hγ))
  have hs := slash_mem_functionOrbit k f hg (mapGL ℚ γ⁻¹) hpos
  simpa only [map_mapGL, map_inv, hmap] using hs

/-- A positive rational translate, followed by the actual cusp trace, stays in the orbit. -/
theorem cusp_trace_translate_mem_functionOrbit
    (Γ Γ' : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [Γ'.FiniteIndex]
    (α : GL (Fin 2) ℚ) (hα : 0 < (α : Matrix (Fin 2) (Fin 2) ℚ).det)
    [(ConjAct.toConjAct (GeneralLinearGroup.map (algebraMap ℚ ℝ) α)⁻¹ •
      Γ'.map (mapGL ℝ)).IsFiniteRelIndex (Γ.map (mapGL ℝ))]
    (k : ℤ) (f : ℍ → ℂ) (g : CuspForm (Γ'.map (mapGL ℝ)) k)
    (hg : ⇑g ∈ functionOrbit k f) :
    ⇑(CuspForm.trace (Γ.map (mapGL ℝ))
      (CuspForm.translate g (GeneralLinearGroup.map (algebraMap ℚ ℝ) α))) ∈ functionOrbit k f := by
  apply cusp_trace_mem_functionOrbit Γ _ k f
  rw [CuspForm.coe_translate]
  exact slash_mem_functionOrbit k f hg α hα

/-- In size two the adjugate has the same determinant, in the actual rational matrix group. -/
theorem det_adjugate_rational (α : GL (Fin 2) ℚ) :
    (TauCeti.adjugateGL α : Matrix (Fin 2) (Fin 2) ℚ).det =
      (α : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [TauCeti.adjugateGL_val, Matrix.adjugate_fin_two, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Positive rational matrices have positive rational adjugates. -/
theorem positive_adjugate_rational {α : GL (Fin 2) ℚ}
    (hα : 0 < (α : Matrix (Fin 2) (Fin 2) ℚ).det) :
    0 < (TauCeti.adjugateGL α : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rwa [det_adjugate_rational]

/-- The actual adjugate commutes with the rational-to-real matrix map. -/
theorem map_adjugate_rational (α : GL (Fin 2) ℚ) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (TauCeti.adjugateGL α) =
      TauCeti.adjugateGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) α) := by
  apply Units.ext
  rw [GeneralLinearGroup.val_map_apply, TauCeti.adjugateGL_val,
    TauCeti.adjugateGL_val, GeneralLinearGroup.val_map_apply,
    Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Integral rational matrices have integral rational adjugates. -/
theorem hasIntEntries_adjugate_rational {α : GL (Fin 2) ℚ} (hα : HasIntEntries 2 α) :
    HasIntEntries 2 (TauCeti.adjugateGL α) := by
  obtain ⟨A, hA⟩ := (hasIntEntries_iff 2).mp hα
  apply (hasIntEntries_iff 2).mpr
  refine ⟨A.adjugate, ?_⟩
  rw [TauCeti.adjugateGL_val, hA, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Integral rational conjugates of actual finite-index integral levels have finite relative index. -/
theorem finiteRelIndex_conj_integral_rational
    (Γ Γ' : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [Γ'.FiniteIndex]
    (α : GL (Fin 2) ℚ) (hα : HasIntEntries 2 α) :
    (ConjAct.toConjAct (GeneralLinearGroup.map (algebraMap ℚ ℝ) α)⁻¹ •
      Γ'.map (mapGL ℝ)).IsFiniteRelIndex (Γ.map (mapGL ℝ)) := by
  have hc : α ∈ commensurator (Γ'.map (mapGL ℚ)) := by
    rw [Subgroup.Commensurable.eq (commensurable_map_SLnZ 2 Γ')]
    exact mem_commensurator_of_hasIntEntries 2 hα
  have hi := (commensurator (Γ'.map (mapGL ℚ))).inv_mem hc
  rw [commensurator_mem_iff] at hi
  have hh := hi.trans ((commensurable_map_SLnZ 2 Γ').trans
    (commensurable_map_SLnZ 2 Γ).symm)
  have hr : (ConjAct.toConjAct α⁻¹ • Γ'.map (mapGL ℚ)).IsFiniteRelIndex
      (Γ.map (mapGL ℚ)) := hh.1
  have hmap : (ConjAct.toConjAct α⁻¹ • Γ'.map (mapGL ℚ)).map
      (GeneralLinearGroup.map (algebraMap ℚ ℝ)) =
      ConjAct.toConjAct (GeneralLinearGroup.map (algebraMap ℚ ℝ) α)⁻¹ •
        (Γ'.map (mapGL ℚ)).map (GeneralLinearGroup.map (algebraMap ℚ ℝ)) := by
    have he :
        (GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)).comp
          (MulAut.conj α⁻¹).toMonoidHom =
        (MulAut.conj (GeneralLinearGroup.map (algebraMap ℚ ℝ) α)⁻¹).toMonoidHom.comp
          (GeneralLinearGroup.map (algebraMap ℚ ℝ)) := by
      ext x
      simp
    change ((Γ'.map (mapGL ℚ)).map (MulAut.conj α⁻¹).toMonoidHom).map
        (GeneralLinearGroup.map (algebraMap ℚ ℝ)) =
      ((Γ'.map (mapGL ℚ)).map (GeneralLinearGroup.map (algebraMap ℚ ℝ))).map
        (MulAut.conj (GeneralLinearGroup.map (algebraMap ℚ ℝ) α)⁻¹).toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map, he]
    simp only [Subgroup.map_map, MonoidHom.comp_assoc]
  simpa only [hmap, Subgroup.map_mapGL] using hr.map
    (GeneralLinearGroup.map (algebraMap ℚ ℝ))

/-- When the trace's source group contains its target, the actual trace is just restriction. -/
theorem cusp_trace_eq_restrict_of_le (𝒢 ℋ : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsFiniteRelIndex ℋ] (hle : ℋ ≤ 𝒢) (k : ℤ) (g : CuspForm 𝒢 k) :
    CuspForm.trace ℋ g = CuspForm.restrict hle g := by
  classical
  let : Fintype (ℋ ⧸ 𝒢.subgroupOf ℋ) := Fintype.ofFinite _
  have htop : 𝒢.subgroupOf ℋ = ⊤ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_top, iff_true]
    exact hle x.property
  have hcard : Fintype.card (ℋ ⧸ 𝒢.subgroupOf ℋ) = 1 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, htop]
    exact Subgroup.index_top
  have hq : ∀ q : ℋ ⧸ 𝒢.subgroupOf ℋ, SlashInvariantForm.quotientFunc g q = ⇑g := by
    intro q
    induction q using Quotient.inductionOn with
    | h r =>
      rw [SlashInvariantForm.quotientFunc_mk]
      exact SlashInvariantFormClass.slash_action_eq g _ (hle (ℋ.inv_mem r.property))
  apply DFunLike.coe_injective
  rw [CuspForm.coe_trace, CuspForm.coe_restrict]
  simp only [hq, Finset.sum_const, Finset.card_univ, hcard, one_nsmul]

end ZInQ.Contrib.HeckePrimeRationality.ReverseHecke
