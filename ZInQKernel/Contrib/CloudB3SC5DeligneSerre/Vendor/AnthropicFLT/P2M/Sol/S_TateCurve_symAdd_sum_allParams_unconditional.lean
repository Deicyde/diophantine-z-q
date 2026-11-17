/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_symAdd_sum_allParams_unconditional (git blob 2df68096a13d6cdc2b5d09950680e6ae3d97c341, sha256 108f3c2d68471bc5ab96bfc411dc97ef5f3c6c3f83020254e45a181bf9a9ec0c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_XMultIdentities
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_KeystoneVocab
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_ks17_D2_exports
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_symAdd_sum_regional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_diffHyp_unconditional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace TateCurve
end TateCurve
namespace P2MW.S_TateCurve_symAdd_sum_allParams_unconditional.TateCurve
end P2MW.S_TateCurve_symAdd_sum_allParams_unconditional.TateCurve

namespace P2MW.S_TateCurve_symAdd_sum_allParams_unconditional

open scoped NNReal
open _root_.TateCurve
open _root_.P2MW.S_TateCurve_symAdd_sum_allParams_unconditional.TateCurve

universe u_1 u_2
namespace TateCurve
export _root_.TateCurve (symSumNum AddParams pointX pointY DiffHyp ExpansionRegion ks17_D2_exports symAdd_sum_regional diffHyp_unconditional)
open _root_.TateCurve

theorem diffHyp_of_region_closed : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] {q τ : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))),
      DiffHyp q :=
  TateCurve.ks17_D2_exports.{u_1}.1

theorem exists_sqrt_of_isAlgClosed : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] [IsAlgClosed K] (q : K),
      ∃ τ : K, τ ^ 2 = q :=
  TateCurve.ks17_D2_exports.{u_1}.2.1

theorem symAdd_sum_of_region_closed : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] {q u v τ : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v),
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = symSumNum q (pointX q u) (pointX q v) :=
  TateCurve.ks17_D2_exports.{u_1}.2.2

end TateCurve

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    ∀ u v : K, TateCurve.AddParams q u v →
      (TateCurve.pointX q (u * v) + TateCurve.pointX q (u * v⁻¹)) * (TateCurve.pointX q u - TateCurve.pointX q v) ^ 2 =
        TateCurve.symSumNum q (TateCurve.pointX q u) (TateCurve.pointX q v) := by
  intro u v hp
  obtain ⟨τ, hτ⟩ := TateCurve.exists_sqrt_of_isAlgClosed (K := K) q
  exact TateCurve.symAdd_sum_of_region_closed hq0 hq hτ (TateCurve.symAdd_sum_regional hq0 hq)
    (fun u' v' hreg => TateCurve.diffHyp_unconditional hq0 hq u' v' hreg.params) hp
