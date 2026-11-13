/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 4d91513e4d30, module
-- TauCeti.NumberTheory.ModularForms.Newforms.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Basic

/-! # Old subspaces from a family of levels (backport)

`cuspFormsOldOf N k P`: the span of the level-raises from the levels `M` with `P M`. In Tau Ceti's
main, `cuspFormsOld` is defined as its case `P M := M ≠ N`; the vendored commit-5a01f5fe
`cuspFormsOld` is unchanged here.
-/

public noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

open _root_.CuspForm

variable {k : ℤ}

/-! ### Old subspaces from a family of levels -/

/-- The span of the level-raises `V_d : S_k(Γ₁(M)) → S_k(Γ₁(N))` over the pairs `(M, d)` with
`d * M ∣ N` and `P M`, for a condition `P` on the source level `M`. The old subspace
`cuspFormsOld` is the case `P M := M ≠ N`; taking `P M := q * M ∣ N` gives the old subspace at a
prime `q`. -/
def cuspFormsOldOf (N : ℕ) [NeZero N] (k : ℤ) (P : ℕ → Prop) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨆ (M : ℕ) (d : ℕ) (h : d * M ∣ N ∧ P M),
    have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h.1)
    LinearMap.range (CuspForm.levelRaiseₗ (k := k) d (Gamma1_map_le_conjAct_scaleGL_of_dvd h.1))

variable {M d N : ℕ} {P : ℕ → Prop}

/-- **Introduction rule for `cuspFormsOldOf`**: every level-raise from a level `M` with `P M`
lies in `cuspFormsOldOf N k P`. -/
theorem levelRaise_mem_cuspFormsOldOf [NeZero N] (h : d * M ∣ N) (hP : P M)
    (k : ℤ) (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
    CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f ∈ cuspFormsOldOf N k P :=
  let _ := NeZero.of_dvd (dvd_of_mul_right_dvd h)
  Submodule.mem_iSup_of_mem M (Submodule.mem_iSup_of_mem d
    (Submodule.mem_iSup_of_mem ⟨h, hP⟩ ⟨f, CuspForm.levelRaiseₗ_apply d _ f⟩))

/-- **Elimination rule for `cuspFormsOldOf`**: a subspace containing every level-raise from a
level `M` with `P M` contains `cuspFormsOldOf N k P`. -/
theorem cuspFormsOldOf_le [NeZero N] {V : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (hV : ∀ (M d : ℕ) (h : d * M ∣ N), P M →
      ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
        haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
        CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f ∈ V) :
    cuspFormsOldOf N k P ≤ V := by
  refine iSup_le fun M ↦ iSup_le fun d ↦ iSup_le fun h ↦ ?_
  have := NeZero.of_dvd (dvd_of_mul_right_dvd h.1)
  rintro _ ⟨f, rfl⟩
  rw [CuspForm.levelRaiseₗ_apply]
  exact hV M d h.1 h.2 f

/-- The restriction to level `N` of a cusp form of a level `M ∣ N` with `P M` lies in
`cuspFormsOldOf N k P`: it is the level-raise `V₁`. -/
theorem restrict_mem_cuspFormsOldOf [NeZero N] (h : M ∣ N) (hP : P M) (k : ℤ)
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    _root_.CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd h) f ∈
      cuspFormsOldOf N k P := by
  have h1 : 1 * M ∣ N := by rwa [one_mul]
  have := levelRaise_mem_cuspFormsOldOf h1 hP k f
  -- At `d = 1`, level-raising is exactly restriction along the subgroup inclusion.
  rwa [_root_.CuspForm.levelRaise_one] at this

/-- **Orthogonality to `cuspFormsOldOf` is tested on the level-raises.** A cusp form of level
`N` is Petersson-orthogonal to `cuspFormsOldOf N k P` exactly when it is orthogonal to `V_d g`
for every cusp form `g` of a level `M` with `P M`. -/
theorem mem_peterssonOrthogonal_cuspFormsOldOf_iff [NeZero N]
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} :
    f ∈ CuspForm.peterssonOrthogonal (cuspFormsOldOf N k P) ↔
      ∀ (M d : ℕ) (h : d * M ∣ N), P M →
        ∀ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
          haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
          peterssonInnerCosets
            (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g) f = 0 := by
  refine ⟨fun hf M d h hP g ↦ CuspForm.mem_peterssonOrthogonal_iff.mp hf _
    (levelRaise_mem_cuspFormsOldOf h hP k g), fun h ↦ ?_⟩
  rw [CuspForm.mem_peterssonOrthogonal_iff_le_ker]
  refine cuspFormsOldOf_le fun M d hdvd hP g ↦ ?_
  rw [LinearMap.mem_ker, CuspForm.peterssonInnerCosetsₛₗ_apply_apply,
    ← peterssonInnerCosets_conj_symm, h M d hdvd hP g, map_zero]

end TauCeti
