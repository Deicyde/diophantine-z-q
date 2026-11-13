/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 4d91513e4d30, module
-- TauCeti.NumberTheory.ModularForms.Fricke.OldSpace), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Fricke.OldSpace`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Fricke.OldSpace
public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ModularForms.Newforms.Basic

/-! # The Fricke operator preserves `cuspFormsOldOf` (backport) -/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {M d e N : ℕ} {k : ℤ}

/-! ### Stability of the old subspace -/

/-- **The Fricke operator preserves `cuspFormsOldOf`**: `W_N` maps `cuspFormsOldOf N k P` into
itself. A level-raise `V_d f` from a level `M` with `P M`, with `d * M ∣ N`, goes to a multiple of
`V_e (W_M f)` for the complementary `e = N / (d * M)` (`frickeOperatorCusp_levelRaise`), again a
level-raise from `M`. -/
theorem frickeOperatorCusp_mem_cuspFormsOldOf [NeZero N] {P : ℕ → Prop}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsOldOf N k P) :
    frickeOperatorCusp k f ∈ cuspFormsOldOf N k P := by
  refine (cuspFormsOldOf_le (V := (cuspFormsOldOf N k P).comap (frickeOperatorCusp k))
    fun M d hdM hP g ↦ ?_) hf
  obtain ⟨e, he⟩ := hdM
  have hN : d * e * M = N := by rw [he]; ring
  have heM : e * M ∣ N := ⟨d, by rw [← hN]; ring⟩
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd ⟨e, he⟩)
  have : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd ⟨e, he⟩)
  have : NeZero e := NeZero.of_dvd (dvd_of_mul_right_dvd heM)
  rw [Submodule.mem_comap, frickeOperatorCusp_levelRaise hN _
    (Gamma1_map_le_conjAct_scaleGL_of_dvd heM)]
  exact Submodule.smul_mem _ _ (levelRaise_mem_cuspFormsOldOf heM hP k _)

end TauCeti
