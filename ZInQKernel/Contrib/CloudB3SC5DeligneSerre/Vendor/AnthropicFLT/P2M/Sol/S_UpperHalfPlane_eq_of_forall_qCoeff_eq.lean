/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_UpperHalfPlane_eq_of_forall_qCoeff_eq (git blob 10c048f9b1534d3805e2a1d7841931f897a434f3, sha256 b6415656583044c0b3d629d962390332c7825bb6d42994d2dea4b4d8c0ca6ebf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_UpperHalfPlane_eq_of_forall_qCoeff_eq

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

open ModularForm ModularFormClass

namespace W2WsF

theorem hasSum_qCoeff {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos hper hhol hbdd τ

end W2WsF

theorem solution {f g : UpperHalfPlane → ℂ} (hfper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hfhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hfbdd : UpperHalfPlane.IsBoundedAtImInfty f) (hgper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1) (hghol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g) (hgbdd : UpperHalfPlane.IsBoundedAtImInfty g) (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by
  funext τ
  have hf := W2WsF.hasSum_qCoeff hfper hfhol hfbdd τ
  have hg := W2WsF.hasSum_qCoeff hgper hghol hgbdd τ
  simp only [h] at hf
  exact hf.unique hg

end
