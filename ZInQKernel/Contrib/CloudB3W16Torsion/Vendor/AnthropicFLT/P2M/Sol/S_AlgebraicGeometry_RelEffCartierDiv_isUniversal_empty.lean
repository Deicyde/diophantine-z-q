/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_isUniversal_empty. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isUniversal_empty

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
-- Deferred synthetic P2M scope: root namespace remains open.

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme Scheme.IdealSheafData.comap_top Scheme.IdealSheafData RelEffCartierDiv.empty RelEffCartierDiv.empty_I RelEffCartierDiv)
namespace RelEffCartierDiv
export _root_.AlgebraicGeometry.RelEffCartierDiv (empty empty_I I_eq_top_of_degree_zero ext I IsUniversal)
open AlgebraicGeometry.RelEffCartierDiv
open AlgebraicGeometry

theorem isUniversal_empty_aux {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) :
    (RelEffCartierDiv.empty f (𝟙 S)).IsUniversal := by
  intro T g D
  refine ⟨⟨g, Category.comp_id g⟩, ?_, ?_⟩
  · change (RelEffCartierDiv.empty f (𝟙 S)).I.comap _ = D.I
    rw [RelEffCartierDiv.empty_I, Scheme.IdealSheafData.comap_top, D.I_eq_top_of_degree_zero]
  · rintro ⟨ψ, hψ⟩ -
    exact Subtype.ext ((Category.comp_id ψ).symm.trans hψ)

end AlgebraicGeometry.RelEffCartierDiv

theorem solution {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) :
    (RelEffCartierDiv.empty f (𝟙 S)).IsUniversal :=
  AlgebraicGeometry.RelEffCartierDiv.isUniversal_empty_aux f
