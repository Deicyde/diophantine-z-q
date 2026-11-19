/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WLight_exists_mdifferentiable_div_of_monicRel (git blob 726caa51bd12d3d6ce3c27852b84382acbfcdd73, sha256 e7535b0e695a483d6716a93b6dff34b207e5230263a12f225d2f8b6fec181dcc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WLight_exists_mdifferentiable_div_of_monicRel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.exists_mdifferentiable_div_of_monicRel {a b : ℍ → ℂ} {c : ℕ → ℍ → ℂ} {d : ℕ}
    (hahol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a) (hbhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b)
    (hb0 : b ≠ 0) (hc : ∀ k < d, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c k))
    (hrel : a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k = 0) :
    ∃ F : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ F * b = a := by
  revert a b c d hahol hbhol hb0 hc hrel
  exact @_root_.P2MW.S_WLight_exists_mdifferentiable_div_of_monicRel.solution
