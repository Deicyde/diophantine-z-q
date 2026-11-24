/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal

set_option autoImplicit false
-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry CategoryTheory TopologicalSpace AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry.Scheme"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "affine_isReduced_iff Spec IsIntegral Scheme Scheme.IdealSheafData.vanishingIdeal IsReduced.of_openCover IsReduced Scheme.IdealSheafData isIntegral_of_irreducibleSpace_of_isReduced"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "IdealSheafData.coe_support_vanishingIdeal Γ IdealSheafData.vanishingIdeal IdealSheafData.vanishingIdeal_ideal affineOpens IdealSheafData"
namespace IntegralSubscheme
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"
universe u
section IntegralSubscheme

variable {V : Scheme.{u}}

theorem isReduced_vanishingIdeal (Z : Closeds V) :
    IsReduced (IdealSheafData.vanishingIdeal Z).subscheme := by

  have hchart : ∀ U : V.affineOpens,
      IsReduced ((IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X U) := by
    intro U

    show IsReduced (Spec (CommRingCat.of
      (Γ(V, U.1) ⧸ (IdealSheafData.vanishingIdeal Z).ideal U)))
    rw [affine_isReduced_iff]

    have hrad : ((IdealSheafData.vanishingIdeal Z).ideal U).IsRadical := by
      rw [IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    constructor
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨n, hn⟩ := hx
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrad ⟨n, hn⟩)
  haveI := hchart
  exact AlgebraicGeometry.IsReduced.of_openCover
    (X := (IdealSheafData.vanishingIdeal Z).subscheme)
    (IdealSheafData.vanishingIdeal Z).subschemeCover.openCover

theorem support_vanishingIdeal (Z : Closeds V) :
    (IdealSheafData.vanishingIdeal Z).support = Z := by
  exact SetLike.coe_injective (IdealSheafData.coe_support_vanishingIdeal Z)

theorem irreducible_vanishingIdeal (Z : Closeds V)
    (hZ : IsIrreducible (Z : Set V)) :
    IrreducibleSpace (IdealSheafData.vanishingIdeal Z).subscheme := by

  exact Subtype.irreducibleSpace hZ

theorem isIntegral_vanishingIdeal (Z : Closeds V)
    (hZ : IsIrreducible (Z : Set V)) :
    IsIntegral (IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI := isReduced_vanishingIdeal Z
  haveI := irreducible_vanishingIdeal Z hZ
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end IntegralSubscheme
end AlgebraicGeometry.Scheme.IntegralSubscheme

universe u
open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry TopologicalSpace in
theorem solution {V : Scheme.{u}} (Z : Closeds V) (hZ : IsIrreducible (Z : Set V)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  AlgebraicGeometry.Scheme.IntegralSubscheme.isIntegral_vanishingIdeal Z hZ
