/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WLight_exists_analyticOnNhd_div_of_monicRel (git blob fa0e05170c60d3e1310bf401b1578ddc85d5e1d4, sha256 caa5785aed12afffca40d43647ee2a16da9b57ae102a093a9e8137afe2731846).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WLight_exists_analyticOnNhd_div_of_monicRel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.exists_analyticOnNhd_div_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {U : Set 𝕜} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ}
    (hF : AnalyticOnNhd 𝕜 F U) (hG : AnalyticOnNhd 𝕜 G U) (hG0 : ∃ z ∈ U, G z ≠ 0)
    (hc : ∀ k < n, AnalyticOnNhd 𝕜 (c k) U)
    (hrel : Set.EqOn (F ^ n + ∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) 0 U) :
    ∃ H : 𝕜 → 𝕜, AnalyticOnNhd 𝕜 H U ∧ Set.EqOn F (G * H) U := by
  revert 𝕜 U hU hUc F G c n hF hG hG0 hc hrel
  exact @_root_.P2MW.S_WLight_exists_analyticOnNhd_div_of_monicRel.solution
