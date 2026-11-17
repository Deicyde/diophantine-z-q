/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero (git blob 655500042235036f7bfc3e2a2a3fd0f4cf9b2831, sha256 bba4a2f2574dd74288816ec319f50fef8b315786a2ba1133d1621f128e9c5575).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_KaehlerDifferential_span_D_eq_top_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Mathlib.FieldTheory.Perfect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero

noncomputable section
open KaehlerDifferential

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place.diffCoeff Place.diffCoeff_smul_D Place.ordDiff_def Place isAlgebraic_adjoin_of_transcendental)
namespace FF2R3
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
  [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]

include x in

private theorem isSeparable_adjoin (v : Place K F) {t : F} (ht : v.ord t ≠ 0) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
    AlgebraicCurve.isAlgebraic_adjoin_of_transcendental x (v.transcendental_of_ord_ne_zero ht)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  infer_instance

include x in
theorem D_ne_zero_of_ord_ne_zero (v : Place K F) {t : F} (ht : v.ord t ≠ 0) : D K F t ≠ 0 :=
  haveI := isSeparable_adjoin x v ht
  KaehlerDifferential.D_ne_zero_of_transcendental K t (v.transcendental_of_ord_ne_zero ht)

include x in
theorem exists_eq_smul_D_of_ord_ne_zero (v : Place K F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    ∃ g : F, ω = g • D K F t := by
  haveI := isSeparable_adjoin x v ht
  have hspan := KaehlerDifferential.span_D_eq_top_of_transcendental K t (v.transcendental_of_ord_ne_zero ht)
  have hω : ω ∈ Submodule.span F {D K F t} := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hω
  exact ⟨g, hg.symm⟩

include x in
theorem diffCoeff_smul_D_of_ord_ne_zero (v : Place K F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    Place.diffCoeff t ω • D K F t = ω :=
  Place.diffCoeff_smul_D (exists_eq_smul_D_of_ord_ne_zero x v ht ω)

include x in
theorem diffCoeff_smul_of_ord_ne_zero (v : Place K F) {t : F} (ht : v.ord t ≠ 0) (g : F) :
    Place.diffCoeff t (g • D K F t) = g :=
  smul_left_injective F (D_ne_zero_of_ord_ne_zero x v ht)
    (Place.diffCoeff_smul_D ⟨g, rfl⟩)

include x in
theorem ordDiff_smul_D_uniformizer (v : Place K F) (g : F) :
    v.ordDiff (g • D K F v.uniformizer_alt) = v.ord g := by
  have h1 : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  rw [Place.ordDiff_def, diffCoeff_smul_of_ord_ne_zero x v (by rw [h1]; exact one_ne_zero)]

include x in
theorem ordDiff_zero (v : Place K F) : v.ordDiff 0 = 0 := by
  simpa using ordDiff_smul_D_uniformizer x v 0

include x in
theorem ordDiff_D_uniformizer (v : Place K F) : v.ordDiff (D K F v.uniformizer_alt) = 0 := by
  simpa using ordDiff_smul_D_uniformizer x v 1

end AlgebraicCurve.FF2R3

end

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) :
    KaehlerDifferential.D K F t ≠ 0 :=
  AlgebraicCurve.FF2R3.D_ne_zero_of_ord_ne_zero x v ht
