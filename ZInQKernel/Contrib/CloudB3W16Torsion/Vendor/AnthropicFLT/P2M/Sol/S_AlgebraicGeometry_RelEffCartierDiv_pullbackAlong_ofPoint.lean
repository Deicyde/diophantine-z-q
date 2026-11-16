/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.

namespace AlgebraicGeometry
export AlgebraicGeometry (Scheme.Hom.ker_comp_of_isIso Scheme.Hom Scheme Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsSeparated Scheme.IdealSheafData graphOver graphOver_snd RelEffCartierDiv.ofPoint RelEffCartierDiv RelEffCartierDiv.ext mapOnProdOver isPullback_mapOnProdOver)
namespace RelEffCartierDiv
export AlgebraicGeometry.RelEffCartierDiv (ofPoint ext pullbackAlong)
namespace OfPointNaturality
open AlgebraicGeometry.RelEffCartierDiv
open AlgebraicGeometry
open AlgebraicGeometry
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.
open AlgebraicGeometry.RelEffCartierDiv
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}

theorem isPullback_graphOver_comp [IsSeparated f] (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    IsPullback (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ])) φ
      (mapOnProdOver f φ hφ) (graphOver f a ha) := by
  have s : IsPullback (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) ≫ pullback.snd f g)
      φ φ (graphOver f a ha ≫ pullback.snd f g') := by
    rw [graphOver_snd, graphOver_snd]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine IsPullback.of_right s ?_ (isPullback_mapOnProdOver f φ hφ).flip
  apply pullback.hom_ext <;> simp

end AlgebraicGeometry.RelEffCartierDiv.OfPointNaturality

theorem solution {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (a : T' ⟶ 𝒞) (ha : a ≫ f = g') (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (RelEffCartierDiv.ofPoint f a ha).pullbackAlong φ hφ =
      RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) := by
  refine RelEffCartierDiv.ext ?_
  change (graphOver f a ha).ker.comap (mapOnProdOver f φ hφ) = (graphOver f (φ ≫ a) _).ker
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (AlgebraicGeometry.RelEffCartierDiv.OfPointNaturality.isPullback_graphOver_comp
      f a ha φ hφ).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
