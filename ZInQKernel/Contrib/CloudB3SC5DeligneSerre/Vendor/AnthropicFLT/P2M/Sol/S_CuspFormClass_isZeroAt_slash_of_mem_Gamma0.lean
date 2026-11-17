/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspFormClass_isZeroAt_slash_of_mem_Gamma0 (git blob d3bc55283ddc4f52997f55365a74483e2289c878, sha256 f57be553f1315fcdafd6ccb4c523c4f8ec35957746c542c1f4c8cb3800964cf5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspFormClass_isZeroAt_slash_ratCast

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspFormClass_isZeroAt_slash_of_mem_Gamma0

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem mapGL_rat_eq (σ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ σ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) := by
  ext i j
  simp [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL]

theorem Gamma_le_GammaH' (M : ℕ) (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := CongruenceSubgroup.Gamma_mem.mp hA
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

scoped instance GammaH_finiteIndex' (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH' M H)

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (σ : CongruenceSubgroup.Gamma0 M)
    {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [CuspFormClass F (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {c : OnePoint ℝ} (hc : IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) k := by
  have := CuspFormClass.isZeroAt_slash_ratCast f (Matrix.SpecialLinearGroup.mapGL ℚ (σ : SL(2, ℤ))) hc
  rwa [mapGL_rat_eq] at this
