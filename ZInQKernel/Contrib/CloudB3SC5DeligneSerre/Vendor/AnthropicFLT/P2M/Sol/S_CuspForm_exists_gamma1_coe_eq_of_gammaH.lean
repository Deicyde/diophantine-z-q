/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_exists_gamma1_coe_eq_of_gammaH (git blob 22a1e79db86f74dd4c9165423b8c8d9a5a6cae80, sha256 1a9d79623840c01ebb22b7f7d3d5c72aa52a9e1a6cbcbdcdaa5dfa4186e529eb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import Mathlib.NumberTheory.ModularForms.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_exists_gamma1_coe_eq_of_gammaH

set_option autoImplicit false

open scoped MatrixGroups

private theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact hA.2.2
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA.2.1, Units.val_one]
  rw [this]; exact one_mem H

private theorem Gamma_le_GammaH' (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma M ≤ CohCarrier.GammaH M H := by
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

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) k, (⇑g : UpperHalfPlane → ℂ) = ⇑f := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma_le_GammaH' M H)
  have hle : ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (Gamma1_le_GammaH M H)
  refine ⟨{ toFun := ⇑f
            slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
            holo' := CuspFormClass.holo f
            zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps f
              ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
                ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)) }, rfl⟩
