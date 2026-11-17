/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_coeffEmb_jqN (git blob 3093eac4ff73fdb8473ba0523b214a154b9fe070, sha256 ee5f96a766b606a5874634b8bcbbf1aca49439484ab660d60f1a38cf2673f945).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.RingTheory.Algebraic.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_coeffEmb_jqN

noncomputable section
open HahnSeries

namespace ModularCurve export _root_.ModularCurve (jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jqN coeffMap coeffEmb) namespace CharLRows end ModularCurve.CharLRows
open scoped _root_.ModularCurve in
theorem ModularCurve.CharLRows.coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ L)

open scoped _root_.ModularCurve in

theorem ModularCurve.CharLRows.map_qExpand_aux {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : (qExpand R N x).map f = qExpand S N (x.map f) := by
  ext k
  rw [HahnSeries.map_coeff]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, HahnSeries.map_coeff]
  · rw [qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

open scoped _root_.ModularCurve in
theorem ModularCurve.CharLRows.coeffEmb_jqN (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    coeffEmb L (jqN N) = jqNModC L N := by
  rw [jqN, jqNModC, ← CharLRows.coeffEmb_jq L]
  exact CharLRows.map_qExpand_aux (algebraMap ℚ L) N jq

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeffEmb_jqN.ModularCurve in
theorem solution (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    coeffEmb L (jqN N) = jqNModC L N :=
  CharLRows.coeffEmb_jqN L N
