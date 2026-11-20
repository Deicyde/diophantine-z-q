import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.NumberField

/-! The cuspidal part of the characteristic-zero inventory (tex 9754–9764).
The old/new theorem is used at the intrinsic level of the block. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open HeckeRing.GL2 TauCeti
open scoped MatrixGroups

/-- The label of a cuspidal column in the character `χ` at level `N`.
The source is a genuine normalized newform at its own level. -/
structure CuspOldColumn (N : ℕ) [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ) where
  level : ℕ
  degree : ℕ
  divides : degree * level ∣ N
  newform : @Newform level (NeZero.of_dvd (dvd_of_mul_left_dvd divides)) 2
  character : let _ : NeZero level := NeZero.of_dvd (dvd_of_mul_left_dvd divides)
    newform.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd divides)) = χ

namespace CuspOldColumn

variable {N : ℕ} [NeZero N] {χ : (ZMod N)ˣ →* ℂˣ}

def form (a : CuspOldColumn N χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2 := by
  letI : NeZero a.level := NeZero.of_dvd (dvd_of_mul_left_dvd a.divides)
  letI : NeZero a.degree := NeZero.of_dvd (dvd_of_mul_right_dvd a.divides)
  exact CuspForm.levelRaise a.degree (Gamma1_map_le_conjAct_scaleGL_of_dvd a.divides)
    a.newform.toCuspForm

def coeff (a : CuspOldColumn N χ) (n : ℕ) : ℂ :=
  letI : NeZero a.level := NeZero.of_dvd (dvd_of_mul_left_dvd a.divides)
  if a.degree ∣ n then (qExpansion 1 a.newform.toCuspForm).coeff (n / a.degree) else 0

theorem coeff_form (a : CuspOldColumn N χ) (n : ℕ) :
    (qExpansion 1 a.form).coeff n = a.coeff n := by
  let : NeZero a.level := NeZero.of_dvd (dvd_of_mul_left_dvd a.divides)
  let : NeZero a.degree := NeZero.of_dvd (dvd_of_mul_right_dvd a.divides)
  exact CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
    (one_mem_strictPeriods_Gamma1_map _) _ _ n

def field (a : CuspOldColumn N χ) : IntermediateField ℚ ℂ :=
  let : NeZero a.level := NeZero.of_dvd (dvd_of_mul_left_dvd a.divides)
  CoefficientField a.newform

theorem numberField (a : CuspOldColumn N χ) : NumberField a.field :=
  let : NeZero a.level := NeZero.of_dvd (dvd_of_mul_left_dvd a.divides)
  numberField_CoefficientField a.newform le_rfl

theorem coeff_mem_field (a : CuspOldColumn N χ) {n : ℕ} (hn : 0 < n) :
    a.coeff n ∈ a.field := by
  let : NeZero a.level := NeZero.of_dvd (dvd_of_mul_left_dvd a.divides)
  unfold coeff
  split
  · rename_i hd
    exact coeff_mem_CoefficientField a.newform ⟨n / a.degree,
      Nat.div_pos (Nat.le_of_dvd hn hd) (Nat.pos_of_ne_zero
        (NeZero.of_dvd (dvd_of_mul_right_dvd a.divides)).out)⟩
  · exact zero_mem _

theorem char_mem_field (a : CuspOldColumn N χ) (u : (ZMod a.level)ˣ) :
    let _ : NeZero a.level := NeZero.of_dvd (dvd_of_mul_left_dvd a.divides)
    (a.newform.χ u : ℂ) ∈ a.field :=
  let _ : NeZero a.level := NeZero.of_dvd (dvd_of_mul_left_dvd a.divides)
  char_mem_CoefficientField a.newform u

end CuspOldColumn

/-- Cuspidal old/new spanning with the character restriction at the block's
own level. Project away the other diamond characters using their independence. -/
theorem cusp_mem_span_intrinsic {N : ℕ} [NeZero N] {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2} (hf : f ∈ cuspFormCharSpace 2 χ) :
    f ∈ Submodule.span ℂ (Set.range (CuspOldColumn.form (N := N) (χ := χ))) := by
  classical
  let S := Submodule.span ℂ (Set.range (CuspOldColumn.form (N := N) (χ := χ)))
  let R := ⨆ (ξ : (ZMod N)ˣ →* ℂˣ) (_ : ξ ≠ χ), cuspFormCharSpace 2 ξ
  have hS : S ≤ cuspFormCharSpace 2 χ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    let : NeZero a.level := NeZero.of_dvd (dvd_of_mul_left_dvd a.divides)
    let : NeZero a.degree := NeZero.of_dvd (dvd_of_mul_right_dvd a.divides)
    have ha : a.form ∈ cuspFormCharSpace 2
        (a.newform.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd a.divides))) :=
      CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd a.divides _ a.newform.mem_charSpace
    exact (congrArg (cuspFormCharSpace 2) a.character) ▸ ha
  have htop : S ⊔ R = ⊤ := by
    apply top_unique
    rw [← Newform.span_levelRaise_eq_top N 2]
    apply Submodule.span_le.mpr
    rintro _ ⟨M, d, _, _, h, g, rfl⟩
    by_cases he : g.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd h)) = χ
    · exact Submodule.mem_sup_left (Submodule.subset_span
        ⟨⟨M, d, h, g, he⟩, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem _
        (Submodule.mem_iSup_of_mem he
          (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd h _ g.mem_charSpace)))
  obtain ⟨s, hs, r, hr, hsr⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top (x := f))
  have hrχ : r ∈ cuspFormCharSpace 2 χ := by
    have hh := (cuspFormCharSpace 2 χ).sub_mem hf (hS hs)
    rwa [← hsr, add_sub_cancel_left] at hh
  have hr0 := (Submodule.disjoint_def.mp (iSupIndep_def.mp
    (iSupIndep_cuspFormCharSpace 2) χ)) r hrχ hr
  simpa [← hsr, hr0, S] using hs

/-- Extract finitely many genuine cuspidal columns, with the old degree and
character still part of each label. State the expansion in the same coefficient
convention as a dilation column in `BlocksPerU.Inventory`. -/
theorem finite_cuspidal_columns {N : ℕ} [NeZero N] {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2} (hf : f ∈ cuspFormCharSpace 2 χ) :
    ∃ (s : Finset (CuspOldColumn N χ)) (w : CuspOldColumn N χ → ℂ), ∀ n,
      (qExpansion 1 f).coeff n = ∑ a ∈ s, w a * a.coeff n := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (cusp_mem_span_intrinsic hf)
  refine ⟨c.support, c, fun n => ?_⟩
  let e := CuspForm.qExpansionCoeffₗ one_pos (one_mem_strictPeriods_Gamma1_map N) 2 n
  rw [← CuspForm.qExpansionCoeffₗ_apply one_pos (one_mem_strictPeriods_Gamma1_map N)]
  change e f = _
  rw [← hc, Finsupp.sum, map_sum]
  simp only [map_smul, smul_eq_mul, e, CuspForm.qExpansionCoeffₗ_apply, CuspOldColumn.coeff_form]

end ZInQ.Manuscript.RC.EvenJoin
