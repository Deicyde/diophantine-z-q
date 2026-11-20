/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_coeffEmb_jq
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.RingTheory.Algebraic.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
namespace P2MW.S_ModularCurve_coeffEmb_jq

noncomputable section
open HahnSeries

namespace ModularCurve p2m_export "ModularCurve" "jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jqN coeffMap coeffEmb" namespace CharLRows end ModularCurve.CharLRows
p2m_open_scoped "ModularCurve" in
theorem ModularCurve.CharLRows.coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ L)

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.CharLRows.map_qExpand_aux {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : (qExpand R N x).map f = qExpand S N (x.map f) := by
  ext k
  rw [HahnSeries.map_coeff]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, HahnSeries.map_coeff]
  · rw [qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

p2m_open_scoped "ModularCurve" in
theorem ModularCurve.CharLRows.coeffEmb_jqN (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    coeffEmb L (jqN N) = jqNModC L N := by
  rw [jqN, jqNModC, ← CharLRows.coeffEmb_jq L]
  exact CharLRows.map_qExpand_aux (algebraMap ℚ L) N jq

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeffEmb_jq.ModularCurve in
theorem solution (L : Type*) [Field L] [Algebra ℚ L] :
    coeffEmb L jq = jqModC L :=
  CharLRows.coeffEmb_jq L
