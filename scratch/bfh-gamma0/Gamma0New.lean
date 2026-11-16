import ZInQKernel.Contrib.OneProof.BFHKronecker
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.AtkinLehner.Sign
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma0
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 HeckeRing.GLn
open scoped MatrixGroups ModularForm HeckeCosetModule

namespace ZInQ.BFHPrinted.Gamma0Test

open TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

def IsGamma0New (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : Prop :=
  ∀ (M d : ℕ) (h : d * M ∣ N), M ≠ N →
    ∀ g : CuspForm ((Gamma0 M).map (mapGL ℝ)) k,
      haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
      CuspForm.peterssonInnerCosets
        (TauCeti.CuspForm.levelRaise d (TauCeti.Gamma0_map_le_conjAct_scaleGL_of_dvd h) g) F = 0

theorem restrict_levelRaise_gamma0 {M d : ℕ} [NeZero d] (h : d * M ∣ N)
    (g : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    CuspForm.restrict (Gamma1_map_le_Gamma0_map N)
        (TauCeti.CuspForm.levelRaise d (TauCeti.Gamma0_map_le_conjAct_scaleGL_of_dvd h) g) =
      TauCeti.CuspForm.levelRaise d (TauCeti.Gamma1_map_le_conjAct_scaleGL_of_dvd h)
        (CuspForm.restrict (Gamma1_map_le_Gamma0_map M) g) :=
  CuspForm.ext fun τ ↦ by simp [CuspForm.coe_restrict]

theorem relIndex_gamma1_gamma0_ne_zero :
    ((Gamma1 N).withCenter.relIndex (Gamma0 N).withCenter : ℂ) ≠ 0 := by
  have : (Gamma1 N).withCenter.FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1 N).le_withCenter
  have h1 : (Gamma1 N).withCenter.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  intro h0
  apply h1
  rw [← Subgroup.relIndex_top_right]
  exact Subgroup.relIndex_eq_zero_of_le_right le_top (by exact_mod_cast h0)

theorem isGamma0New_toCuspFormGamma0 (f : Newform N k) (hχ : f.χ = 1) :
    IsGamma0New (f.toCuspFormGamma0 hχ) := by
  intro M d h hM g
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
  have hnew := (TauCeti.mem_cuspFormsNew_iff.mp f.isNew) M d h hM
    (CuspForm.restrict (Gamma1_map_le_Gamma0_map M) g)
  have key := CuspForm.peterssonInnerCosets_restrict_restrict (Γ := Gamma0 N) (Γ' := Gamma1 N)
    (Gamma1_map_le_Gamma0_map N)
    (TauCeti.CuspForm.levelRaise d (TauCeti.Gamma0_map_le_conjAct_scaleGL_of_dvd h) g)
    (f.toCuspFormGamma0 hχ)
  rw [restrict_levelRaise_gamma0 h, Newform.restrict_toCuspFormGamma0, hnew] at key
  exact (mul_eq_zero.mp key.symm).resolve_left relIndex_gamma1_gamma0_ne_zero

/-! Hecke operators on S_k(Γ₀(N)) -/

variable (N k) in
noncomputable def heckeGamma0 :
    𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ →ₗ[ℤ]
      Module.End ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  Finsupp.linearCombination ℤ fun D ↦ heckeSlashGamma0CuspFormEnd k D

theorem heckeGamma0_single
    (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))) (c : ℤ) :
    heckeGamma0 N k (HeckeCosetModule.single ℤ D c) = c • heckeSlashGamma0CuspFormEnd k D :=
  (Finsupp.linearCombination_apply (R := ℤ)
    (v := fun D ↦ heckeSlashGamma0CuspFormEnd k D) _).trans
    (HeckeCosetModule.sum_single_index ℤ (zero_smul _ _))

theorem coe_heckeGamma0 (T : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ)
    (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ⇑(heckeGamma0 N k T F) =
      ⇑((heckeRingHomCuspCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) T
        ⟨CuspForm.restrict (Gamma1_map_le_Gamma0_map N) F,
          TauCeti.restrict_mem_cuspFormCharSpace_one F⟩ :
          cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  induction T using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd S T hS hT =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, FunLike.coe_add, hS, hT]
    rfl
  | hsingle D c =>
    rw [heckeRingHomCuspCharSpace_apply, twistedHeckeSlashCuspFormCharLinearMap_single,
      heckeGamma0_single]
    simp [CuspForm.coe_restrict]

end ZInQ.BFHPrinted.Gamma0Test
