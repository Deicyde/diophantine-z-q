/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds (git blob 0b20fe0e56f77aca9b6ee68aeb50fcb10a3faac3, sha256 e0f1f146a556ced546034bb545bd5295107b24b0f9dc0ab44598215d1a25e9e1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped Topology

theorem solution (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    ∃ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c ∧ 0 < d₁ ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∈ 𝓝 g := by
  classical
  refine ⟨1 / 2, 1, 1 / 2, 2, {g}, by norm_num, by norm_num, ?_⟩
  have h1 : (1 : AdelicGL2 (𝓞 F) F) ∈ interior (centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2) :=
    one_mem_interior_centreCutSiegelSet (by norm_num) one_ne_zero (by norm_num) (by norm_num)
  have hW : (⋃ x ∈ ({g} : Finset (AdelicGL2 (𝓞 F) F)), (· * x) '' centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2) =
      (· * g) '' centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2 := by
    ext h
    simp only [Finset.mem_singleton, Set.mem_iUnion, exists_prop, exists_eq_left]
  rw [hW]
  have hn : centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2 ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F) := mem_interior_iff_mem_nhds.mp h1
  have him := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds hn
  rw [Homeomorph.coe_mulRight] at him
  simpa only [one_mul] using him
