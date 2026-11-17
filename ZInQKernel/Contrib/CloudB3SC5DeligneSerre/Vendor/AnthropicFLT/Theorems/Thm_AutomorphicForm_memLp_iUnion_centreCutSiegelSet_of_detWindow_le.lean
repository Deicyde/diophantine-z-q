/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le (git blob a56e9ba769f660beb9fd3bf91c7fc500f8fc1585, sha256 6a021c59f4bc2d0b17bd4dc9bf05a93c588044d6a35e1c1d67a29d324f595113).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel
  MeasureTheory

theorem AutomorphicForm.memLp_iUnion_centreCutSiegelSet_of_detWindow_le
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ dp : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hdp : 0 < dp) (hdp₂ : dp < d₂) (hd₁ : d₁ ≤ dp)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφm : letI := glBorel (Fin 2) (𝓞 F) F; AEStronglyMeasurable φ (adelicGLHaar (Fin 2) (𝓞 F) F))
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hω : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g)
    (hcontr : d₁ ≤ 0 → ∀ (w : InfinitePlace F) (a : (w.Completion)ˣ), ‖(a : w.Completion)‖ < 1 →
      ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1)
    (hL2 : letI := glBorel (Fin 2) (𝓞 F) F;
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u dp d₂))) :
    letI := glBorel (Fin 2) (𝓞 F) F;
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  revert F c u d₁ d₂ dp T hdp hdp₂ hd₁ φ hφm ω hω hcontr hL2
  exact @_root_.P2MW.S_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le.solution
