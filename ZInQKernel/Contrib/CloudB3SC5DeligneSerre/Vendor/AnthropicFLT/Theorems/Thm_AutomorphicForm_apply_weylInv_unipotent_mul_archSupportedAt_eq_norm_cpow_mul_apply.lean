/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply (git blob 6b22325b3faefdd8234f12c5f9953afd6e8a4329, sha256 c30dfb1f4b924f8b321a3a805b7c937b3ed4a225264204221ab0c15a9f762aca).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal
open scoped Classical in

theorem AutomorphicForm.apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (w : InfinitePlace F) (k : AdelicGL2 (𝓞 F) F)
      (_hkf : glFin (𝓞 F) F k = 1)
      (_hka : ∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k) = 1)
      (x : AdeleRing (𝓞 F) F),
    let kw : Matrix (Fin 2) (Fin 2) w.Completion := (archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion)
    ∀ (_hx : kw 0 0 + x.1 w * kw 1 0 ≠ 0),
    let x' : AdeleRing (𝓞 F) F := (Function.update x.1 w ((kw 0 1 + x.1 w * kw 1 1) / (kw 0 0 + x.1 w * kw 1 0)), x.2)
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k)
      = (((‖kw.det‖ ^ w.mult : ℝ)) : ℂ) ^ (s + 1 / 2)
        * (((‖kw 0 0 + x.1 w * kw 1 0‖ ^ w.mult : ℝ)) : ℂ) ^ (-(2 * s + 1))
        * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x') := by
  revert F
  exact @_root_.P2MW.S_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply.solution
