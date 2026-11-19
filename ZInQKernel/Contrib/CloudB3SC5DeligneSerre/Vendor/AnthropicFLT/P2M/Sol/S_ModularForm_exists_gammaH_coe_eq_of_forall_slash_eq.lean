/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq (git blob 17fa53e9ccfc1565caad78c581bb857a49803456, sha256 7d85225ec6a77fcd3ddb1f5ac812030f0c928a89214745955bf1d109f31451ee).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace MatrixGroups
end MatrixGroups
namespace ModularForm
end ModularForm
namespace P2MW.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq.ModularForm
end P2MW.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq.ModularForm

namespace P2MW.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq

set_option autoImplicit false

open scoped _root_.MatrixGroups _root_.ModularForm _root_.P2MW.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq.ModularForm

private theorem Gamma_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := CongruenceSubgroup.Gamma_mem.mp hA
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

namespace ModularForm export _root_.ModularForm (holo' SL_slash ext bdd_at_cusps') end ModularForm
open scoped _root_.ModularForm in

private theorem ModularForm.exists_coe_eq_of_forall_slash_eq_of_finiteIndex
    (Γ Γ' : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [Γ'.FiniteIndex] (k : ℤ)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hg : ∀ γ ∈ Γ', (⇑g : UpperHalfPlane → ℂ) ∣[k] γ = ⇑g) :
    ∃ f : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k, (⇑f : UpperHalfPlane → ℂ) = ⇑g := by
  have hinv : ∀ γ ∈ ((Γ' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      (⇑g : UpperHalfPlane → ℂ) ∣[k] γ = ⇑g := by
    intro γ hγ
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hγ
    have h := hg A hA
    rw [ModularForm.SL_slash] at h
    exact h
  refine ⟨{ toFun := ⇑g
            slash_action_eq' := hinv
            holo' := g.holo'
            bdd_at_cusps' := fun {c} hc => ModularFormClass.bdd_at_cusps g
              ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
                ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)) }, rfl⟩

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hg : ∀ γ ∈ CohCarrier.GammaH M H, (⇑g : UpperHalfPlane → ℂ) ∣[k] γ = ⇑g) :
    ∃ f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑f : UpperHalfPlane → ℂ) = ⇑g := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma_le_GammaH M H)
  exact ModularForm.exists_coe_eq_of_forall_slash_eq_of_finiteIndex _ _ k g hg
