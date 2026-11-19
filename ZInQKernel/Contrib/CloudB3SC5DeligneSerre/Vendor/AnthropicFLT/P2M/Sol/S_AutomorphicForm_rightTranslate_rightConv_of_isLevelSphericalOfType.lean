/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_rightTranslate_rightConv_of_isLevelSphericalOfType (git blob e251fedd05a6b2c3f97d5662cf90e762193b3252, sha256 47086e3313c44272083cdbd382c771bf1cc830ea01e7219439aa63ac0e541490).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_rightTranslate_rightConv_of_isLevelSphericalOfType

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem solution
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F tys U f)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F (rowIsometryInclAt₀ F w k) (rightConv F φ f) =
      rightConv F (rightTranslate F (rowIsometryInclAt₀ F w k) φ) f := by
  obtain ⟨fa, -, -, hconj, hfac⟩ := hf
  have hinv : (fun y => f (rowIsometryInclAt₀ F w k * y * (rowIsometryInclAt₀ F w k)⁻¹)) = f := by
    funext y
    rw [hfac (rowIsometryInclAt₀ F w k * y * (rowIsometryInclAt₀ F w k)⁻¹), hfac y]
    simp only [_root_.map_mul, _root_.map_inv, glArch_rowIsometryInclAt₀, glFin_rowIsometryInclAt₀, hconj,
      one_mul, inv_one, mul_one]
  rw [AutomorphicForm.CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj, hinv]
