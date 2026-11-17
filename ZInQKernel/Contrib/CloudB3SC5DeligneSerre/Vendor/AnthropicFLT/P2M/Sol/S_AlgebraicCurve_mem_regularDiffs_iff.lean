/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_mem_regularDiffs_iff (git blob 1380c8cb5c7692e483b4a01e4571cd0aeaf0b739, sha256 37647cc8ca9caf5d7754317f5ea7687697479912f0c4b2c59a84d9c18363b013).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ordDiff_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_mem_regularDiffs_iff

noncomputable section
open KaehlerDifferential

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place.diffCoeff Place.ordDiff_def IsRegularDiff regularDiffs mem_regularDiffs_of_isRegularDiff Place Place.diffCoeff_smul_D_of_ord_ne_zero Place.diffCoeff_smul_D_eq Place.ordDiff_zero Place.ordDiff_smul)
namespace FF2Tail
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
  [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
theorem diffCoeff_add (v : Place K F) {t : F} (ht : v.ord t ≠ 0) (ω₁ ω₂ : Ω[F⁄K]) :
    Place.diffCoeff t (ω₁ + ω₂) = Place.diffCoeff t ω₁ + Place.diffCoeff t ω₂ := by
  have h1 := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht ω₁
  have h2 := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht ω₂
  conv_lhs => rw [← h1, ← h2, ← add_smul]
  exact Place.diffCoeff_smul_D_eq x v ht _

include x in
theorem min_ordDiff_le_ordDiff_add (v : Place K F) {ω₁ ω₂ : Ω[F⁄K]} (h₁₂ : ω₁ + ω₂ ≠ 0) :
    min (v.ordDiff ω₁) (v.ordDiff ω₂) ≤ v.ordDiff (ω₁ + ω₂) := by
  rcases eq_or_ne ω₁ 0 with rfl | h₁
  · rw [zero_add]; exact min_le_right _ _
  rcases eq_or_ne ω₂ 0 with rfl | h₂
  · rw [add_zero]; exact min_le_left _ _
  have hu : v.ord v.uniformizer_alt ≠ 0 := by
    rw [v.ord_uniformizer_alt v.exists_ord_eq_one]; exact one_ne_zero

  have hcoe : ∀ ω : Ω[F⁄K], ω ≠ 0 → Place.diffCoeff v.uniformizer_alt ω ≠ 0 := by
    intro ω hω h0
    have := Place.diffCoeff_smul_D_of_ord_ne_zero x v hu ω
    rw [h0, zero_smul] at this
    exact hω this.symm
  simp only [Place.ordDiff_def]
  rw [diffCoeff_add x v hu]
  exact v.min_ord_le_ord_add (hcoe _ h₁) (hcoe _ h₂) (by rw [← diffCoeff_add x v hu]; exact hcoe _ h₁₂)

include x in
theorem isRegularDiff_zero : IsRegularDiff K F (0 : Ω[F⁄K]) := fun v => by
  rw [Place.ordDiff_zero x v]

include x in
theorem isRegularDiff_add {ω₁ ω₂ : Ω[F⁄K]} (h₁ : IsRegularDiff K F ω₁) (h₂ : IsRegularDiff K F ω₂) :
    IsRegularDiff K F (ω₁ + ω₂) := by
  intro v
  rcases eq_or_ne (ω₁ + ω₂) 0 with h12 | h12
  · rw [h12, Place.ordDiff_zero x v]
  · exact le_trans (le_min (h₁ v) (h₂ v)) (min_ordDiff_le_ordDiff_add x v h12)

include x in
theorem isRegularDiff_smul (c : K) {ω : Ω[F⁄K]} (h : IsRegularDiff K F ω) :
    IsRegularDiff K F (c • ω) := by
  intro v
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul]; exact isRegularDiff_zero x v
  rcases eq_or_ne ω 0 with rfl | hω
  · rw [smul_zero]; exact isRegularDiff_zero x v
  rw [← algebraMap_smul F c ω, Place.ordDiff_smul x v ((map_ne_zero _).mpr hc) hω, v.ord_algebraMap,
    zero_add]
  exact h v

include x in

theorem mem_regularDiffs_iff (ω : Ω[F⁄K]) : ω ∈ regularDiffs K F ↔ IsRegularDiff K F ω := by
  refine ⟨fun h => ?_, mem_regularDiffs_of_isRegularDiff⟩
  induction h using Submodule.span_induction with
  | mem ω hω => exact hω
  | zero => exact isRegularDiff_zero x
  | add ω₁ ω₂ _ _ h₁ h₂ => exact isRegularDiff_add x h₁ h₂
  | smul c ω _ h => exact isRegularDiff_smul x c h

end AlgebraicCurve.FF2Tail

end

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (ω : Ω[F⁄K]) :
    ω ∈ AlgebraicCurve.regularDiffs K F ↔ AlgebraicCurve.IsRegularDiff K F ω :=
  AlgebraicCurve.FF2Tail.mem_regularDiffs_iff x ω
