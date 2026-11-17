/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact (git blob 7a75644ca1f487733909a80d154ba9b39d0990dc, sha256 0a86866c7b58119070f4ebe196a12433422ea75c4780effa9a81c8a14a3bbdec).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) U f)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h) (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, h (u * x) = h x ∧ h (x * u) = h x)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    rightConv F (rightConv F φ f) h = rightConv F (rightConv F φ h) f := by
  revert F U hU O hO hUO τ hirr f hf h hh hht hhU φ hφ
  exact @_root_.P2MW.S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact.solution
