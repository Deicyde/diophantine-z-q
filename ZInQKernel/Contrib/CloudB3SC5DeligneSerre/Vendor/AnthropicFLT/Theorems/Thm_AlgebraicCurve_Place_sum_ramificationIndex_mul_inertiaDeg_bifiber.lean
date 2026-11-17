/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber (git blob 10587eb1b13be31fc09689d050ee92318ace2312, sha256 ae17ea7d363b65df715752a25957649b722645d31c1f1a395c4e342b8bf50d69).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import Mathlib.FieldTheory.Galois.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber {K F F₁ F₂ E : Type*} (M : Type*) [Field K] [Field F] [Field F₁] [Field F₂] [Field E] [Field M] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E] [Algebra K M] [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F M] [Algebra F₁ E] [Algebra F₂ E] [Algebra F₁ M] [Algebra F₂ M] [Algebra E M] [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F M] [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower K F₁ M] [IsScalarTower K F₂ M] [IsScalarTower K E M] [IsScalarTower F F₁ M] [IsScalarTower F F₂ M] [IsScalarTower F E M] [IsScalarTower F₁ E M] [IsScalarTower F₂ E M] [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E] [FiniteDimensional F₁ E] [FiniteDimensional F₂ E] [FiniteDimensional F M] [IsGalois F M] (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤) (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂) (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂) (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v) (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) : ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F = (w₁.ramificationIndex F * w₁.inertiaDeg F) * (w₂.ramificationIndex F * w₂.inertiaDeg F) := by
  revert K F F₁ F₂ E M hgen hLD v w₁ w₂ hw₁ hw₂ T hT
  exact @_root_.P2MW.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.solution
