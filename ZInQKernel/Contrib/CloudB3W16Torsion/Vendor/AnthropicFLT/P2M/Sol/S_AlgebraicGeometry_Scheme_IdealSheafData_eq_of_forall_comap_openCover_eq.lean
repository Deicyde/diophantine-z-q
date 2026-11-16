/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Cover.Open
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.

namespace AlgebraicGeometry
export AlgebraicGeometry (Scheme Scheme.IdealSheafData)
namespace Scheme
export AlgebraicGeometry.Scheme (OpenCover affineOpens isBasis_affineOpens Opens IdealSheafData Cover)
namespace IdealSheafData
export AlgebraicGeometry.Scheme.IdealSheafData (ideal ext_of_iSup_eq_top comap ideal_comap_of_isOpenImmersion)
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.Scheme
open AlgebraicGeometry

theorem eq_of_forall_comap_openCover_eq_aux
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J := by
  refine ext_of_iSup_eq_top
    (fun p : Σ i, (𝒰.X i).affineOpens => ⟨𝒰.f p.1 ''ᵁ (p.2 : (𝒰.X p.1).Opens),
      p.2.2.image_of_isOpenImmersion _⟩) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨y, hy⟩ := 𝒰.covers x
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
      (𝒰.X (𝒰.idx x)).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨𝒰.idx x, ⟨W, hW⟩⟩, ⟨y, hyW, hy⟩⟩
  · rintro ⟨i, W⟩
    have hW := congrArg (fun K : (𝒰.X i).IdealSheafData => K.ideal W) (h i)
    simp only [ideal_comap_of_isOpenImmersion] at hW
    exact Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso (W : (𝒰.X i).Opens)).inv).2 hW

end AlgebraicGeometry.Scheme.IdealSheafData

theorem solution
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J :=
  AlgebraicGeometry.Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq_aux 𝒰 h
