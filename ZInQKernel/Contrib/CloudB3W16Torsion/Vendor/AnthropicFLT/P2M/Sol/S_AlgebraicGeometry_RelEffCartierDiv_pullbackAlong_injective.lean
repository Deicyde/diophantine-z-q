/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_injective. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_injective_of_flat_of_surjective
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_injective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open AlgebraicGeometry in
theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) [Flat φ] [Surjective φ] :
    Function.Injective fun D : RelEffCartierDiv f r g' => D.pullbackAlong φ hφ := by
  intro D E h
  have hI := congrArg RelEffCartierDiv.I h
  change D.I.comap (mapOnProdOver f φ hφ) = E.I.comap (mapOnProdOver f φ hφ) at hI

  haveI : Flat (mapOnProdOver f φ hφ) :=
    MorphismProperty.of_isPullback (isPullback_mapOnProdOver f φ hφ).flip inferInstance
  haveI : Surjective (mapOnProdOver f φ hφ) :=
    MorphismProperty.of_isPullback (isPullback_mapOnProdOver f φ hφ).flip inferInstance
  exact RelEffCartierDiv.ext
    (Scheme.IdealSheafData.comap_injective_of_flat_of_surjective (mapOnProdOver f φ hφ) hI)
