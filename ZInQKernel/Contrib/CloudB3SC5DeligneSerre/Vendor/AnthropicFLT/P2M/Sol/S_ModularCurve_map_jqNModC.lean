/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_map_jqNModC (git blob d19917ee42e4a11aea3d9c5191dc01e10d3f345c, sha256 139e48e2d5ac7542123d89cd166ea56695063628594c0a7d308ec76bd7c220c8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_map_jqNModC.ModularCurve
end P2MW.S_ModularCurve_map_jqNModC.ModularCurve

namespace P2MW.S_ModularCurve_map_jqNModC

open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_map_jqNModC.ModularCurve

set_option autoImplicit false

namespace ModularCurve export _root_.ModularCurve (coeffMap coeffMap_coeff jqModC jqNModC map_jqModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd) end ModularCurve
open scoped _root_.ModularCurve in

theorem ModularCurve.solution_aux_coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (N : ℕ) [NeZero N] : coeffMap φ (jqNModC R N) = jqNModC S N := by
  have hj : coeffMap φ (jqModC R) = jqModC S := map_jqModC φ
  rw [jqNModC, jqNModC, ModularCurve.solution_aux_coeffMap_qExpand, hj]
