/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne (git blob 9afa5dd10a30db556be684cd7e8aa0d1c4b0f852, sha256 e0932a5263fe513fea0e12123dfb6f640aff65af2e1d0d6ce10647052d4bab39).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace CommAway17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

section Commuting

variable {w : InfinitePlace F} (hw : w.IsReal) {k : AdelicGL2 (𝓞 F) F}
  (hk : ∀ m : GL (Fin 2) ℝ, archRealGLAt hw m * k = k * archRealGLAt hw m)

include hk

theorem archRealLiftAt_mul_comm (e : Fin 2 → Fin 2 → ℝ) : archRealLiftAt hw e * k = k * archRealLiftAt hw e := by
  unfold archRealLiftAt
  split_ifs
  · exact hk _
  · rw [one_mul, mul_one]

theorem archFlowAt_mul_comm (d : ArchDir) (t : ℝ) : archFlowAt hw d t * k = k * archFlowAt hw d t :=
  hk _

theorem isArchSmoothAt_rightTranslate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    IsArchSmoothAt hw (rightTranslate F k φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archRealLiftAt hw e * k)) _
  have hfun : (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e * k)) =
      fun e => φ (g * k * archRealLiftAt hw e) := by
    funext e
    rw [mul_assoc, archRealLiftAt_mul_comm hw hk e, ← mul_assoc]
  rw [hfun]
  exact hφ (g * k)

theorem archDerivAt_rightTranslate (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw d (rightTranslate F k φ) = rightTranslate F k (archDerivAt hw d φ) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAt hw d t * k)) 0 = deriv (fun t : ℝ => φ (g * k * archFlowAt hw d t)) 0
  congr 1
  funext t
  rw [mul_assoc, archFlowAt_mul_comm hw hk d t, ← mul_assoc]

theorem archCasimirAt_rightTranslate (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAt hw (rightTranslate F k φ) = rightTranslate F k (archCasimirAt hw φ) := by
  rw [archCasimirAt, archCasimirAt, archDerivAt_rightTranslate hw hk .H φ,
    archDerivAt_rightTranslate hw hk .H (archDerivAt hw .H φ), archDerivAt_rightTranslate hw hk .Fm φ,
    archDerivAt_rightTranslate hw hk .E (archDerivAt hw .Fm φ)]
  rfl

omit hk in
theorem continuous_rightTranslate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (k' : AdelicGL2 (𝓞 F) F) :
    Continuous (rightTranslate F k' φ) :=
  hφ.comp (continuous_id.mul continuous_const)

theorem package (x : AdelicGL2 (𝓞 F) F → ℂ) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    IsArchSmoothAt hw (rightTranslate F k x) ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate F k x))) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightTranslate F k x)))) ∧
    archCasimirAt hw (rightTranslate F k x) = rightTranslate F k (archCasimirAt hw x) := by
  refine ⟨isArchSmoothAt_rightTranslate hw hk hxs, fun d => ?_, fun d d' => ?_, archCasimirAt_rightTranslate hw hk x⟩
  · rw [archDerivAt_rightTranslate hw hk]
    exact continuous_rightTranslate (hD1 d) k
  · rw [archDerivAt_rightTranslate hw hk, archDerivAt_rightTranslate hw hk]
    exact continuous_rightTranslate (hD2 d d') k

end Commuting

theorem archRealGLAt_mul_rowIsometryInclAt₀_comm {w w' : InfinitePlace F} (hw : w.IsReal) (hne : w' ≠ w)
    (k : rowIsometrySubgroup₀ w'.Completion) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m * rowIsometryInclAt₀ F w' k = rowIsometryInclAt₀ F w' k * archRealGLAt hw m := by
  rw [rowIsometryInclAt₀_apply]
  show adelicArchGLInclAt F w _ * adelicArchGLInclAt F w' _ = adelicArchGLInclAt F w' _ * adelicArchGLInclAt F w _
  exact (commute_adelicArchGLInclAt_of_ne F (Ne.symm hne) _ _).eq

end CommAway17

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    ∀ (w' : InfinitePlace K) (hw' : w' ≠ w) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAt hw x) := by
  intro w' hw' k
  exact CommAway17.package hw (CommAway17.archRealGLAt_mul_rowIsometryInclAt₀_comm hw hw' k) x hxs hD1 hD2
