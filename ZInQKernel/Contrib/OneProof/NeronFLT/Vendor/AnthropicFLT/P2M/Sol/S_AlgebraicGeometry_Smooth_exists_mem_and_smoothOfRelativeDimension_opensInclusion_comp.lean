/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace RingHom p2m_export "RingHom" "Smooth IsStandardSmoothOfRelativeDimension locally_of toMorphismProperty_respectsIso_iff isStandardSmoothOfRelativeDimension_respectsIso locally_respectsIso Locally toMorphismProperty IsStandardSmooth toAlgebra" namespace IsStandardSmooth p2m_export "RingHom.IsStandardSmooth" "toAlgebra smooth" end RingHom.IsStandardSmooth
p2m_open_scoped "RingHom RingHom.IsStandardSmooth" in

theorem RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_gc3
    {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S} (h : φ.IsStandardSmooth) :
    ∃ n : ℕ, φ.IsStandardSmoothOfRelativeDimension n := by
  letI := φ.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h.out
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ SmoothOfRelativeDimension d (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨d, hd⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_gc3 hstd
  refine ⟨V, d, hx, ?_⟩

  have hres : SmoothOfRelativeDimension d (f.resLE U V e) := by
    haveI : IsAffine V := hV
    haveI : IsAffine U := hU
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension d)]
    have := (RingHom.toMorphismProperty_respectsIso_iff.mp
      (RingHom.locally_respectsIso (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d))))
    refine ((MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d))) (arrowResLEAppIso f U V e)).mpr ?_)
    exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d)) _ hd
  rw [← Scheme.Hom.resLE_comp_ι f e]
  have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
  simpa using this
