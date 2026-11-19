/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularFormClass_heckeU_heckeU_comm (git blob fa2fb4bd5872982445d65f7dc31ed7835e99947c, sha256 66e58dabec550c240d2e88fd691edd8d0f28c981d3b4c33c05ed80a648099ae1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_mdifferentiable_heckeU
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_isBoundedAtImInfty_heckeU
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_periodic_heckeU_comp_ofComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_coeffHeckeU_comm
import Batteries.Tactic.Alias

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace W2WsF
end W2WsF

namespace P2MW.S_ModularFormClass_heckeU_heckeU_comm

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

open ModularForm ModularFormClass

namespace W2WsF

private theorem _root_.W2WsF.eq_of_forall_qCoeff_eq {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1) (hghol : MDiff g)
    (hgbdd : IsBoundedAtImInfty g) (h : ∀ n : ℕ, qCoeff f n = qCoeff g n) : f = g :=
  UpperHalfPlane.eq_of_forall_qCoeff_eq hfper hfhol hfbdd hgper hghol hgbdd h

alias eq_of_forall_qCoeff_eq := _root_.W2WsF.eq_of_forall_qCoeff_eq

theorem qCoeff_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (c : ℂ) (n : ℕ) : qCoeff (c • f) n = c * qCoeff f n := by
  simp only [qCoeff]
  rw [UpperHalfPlane.qExpansion_smul (analyticAt_cuspFunction_zero one_pos hper hhol hbdd)]
  simp

theorem periodic_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • f) ∘ ofComplex) 1 := fun z ↦ by
  simpa using congrArg (c * ·) (hper z)

section Class

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem mf_periodic [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) :
    Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f hΓ

theorem mf_bdd [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) :
    IsBoundedAtImInfty ⇑f :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  bdd_at_infty f

end Class

theorem heckeU_heckeU_comm_bare {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (k : ℤ) (p q : ℕ) :
    heckeU k p (heckeU k q f) = heckeU k q (heckeU k p f) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  refine eq_of_forall_qCoeff_eq
    (periodic_heckeU_comp_ofComplex (periodic_heckeU_comp_ofComplex hper k q) k p)
    (mdifferentiable_heckeU (mdifferentiable_heckeU hhol k q) k p)
    (isBoundedAtImInfty_heckeU (isBoundedAtImInfty_heckeU hbdd k q) k p)
    (periodic_heckeU_comp_ofComplex (periodic_heckeU_comp_ofComplex hper k p) k q)
    (mdifferentiable_heckeU (mdifferentiable_heckeU hhol k p) k q)
    (isBoundedAtImInfty_heckeU (isBoundedAtImInfty_heckeU hbdd k p) k q) fun n ↦ ?_
  rw [UpperHalfPlane.qCoeff_heckeU (periodic_heckeU_comp_ofComplex hper k q)
      (mdifferentiable_heckeU hhol k q) (isBoundedAtImInfty_heckeU hbdd k q) k hp,
    UpperHalfPlane.qCoeff_heckeU (periodic_heckeU_comp_ofComplex hper k p)
      (mdifferentiable_heckeU hhol k p) (isBoundedAtImInfty_heckeU hbdd k p) k hq]
  have hq' : qCoeff (heckeU k q f) = coeffHeckeU q (qCoeff f) :=
    funext fun m ↦ UpperHalfPlane.qCoeff_heckeU hper hhol hbdd k hq m
  have hp' : qCoeff (heckeU k p f) = coeffHeckeU p (qCoeff f) :=
    funext fun m ↦ UpperHalfPlane.qCoeff_heckeU hper hhol hbdd k hp m
  rw [hq', hp', coeffHeckeU_comm]

end W2WsF

theorem solution {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (p q : ℕ) : ModularForm.heckeU k p (ModularForm.heckeU k q ⇑f) = ModularForm.heckeU k q (ModularForm.heckeU k p ⇑f) :=
  W2WsF.heckeU_heckeU_comm_bare (W2WsF.mf_periodic f hΓ) (ModularFormClass.holo f)
    (W2WsF.mf_bdd f hΓ) k p q

end
