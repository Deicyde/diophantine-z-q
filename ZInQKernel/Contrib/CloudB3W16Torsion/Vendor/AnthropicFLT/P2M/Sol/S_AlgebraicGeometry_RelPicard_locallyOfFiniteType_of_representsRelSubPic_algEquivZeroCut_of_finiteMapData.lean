/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_locallyOfFiniteType_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_AffineLimit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_locallyOfFiniteType_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_locallyOfFiniteType_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open GoodReductionJacobian
open AlgebraicGeometry.AffineLimit
open P2MW.S_AlgebraicGeometry_RelPicard_locallyOfFiniteType_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData.AlgebraicGeometry.AffineLimit
open Opposite

namespace AlgebraicGeometry
export AlgebraicGeometry (SmoothOfRelativeDimension IsProper GeometricallyIntegral LocallyOfFiniteType Spec Spec.map Scheme geometrically SmoothProperCurve.FiniteMapData)
namespace AffineLimit
export AlgebraicGeometry.AffineLimit (specOver specOverOfSubalgebra IsLFPSurj HomIsLFP locallyOfFiniteType_of_forall_exists_fg_factor)
open AlgebraicGeometry.AffineLimit
open AlgebraicGeometry

theorem exists_fg_factor_of_representableBy {R : Type u} [CommRing R] {X : Scheme.{u}} (ξ : X ⟶ Spec (CommRingCat.of R))
    (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1)) (e : G.RepresentableBy (Over.mk ξ)) (hG : IsLFPSurj G)
    (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X)
    (hφ : φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of ↥A₀) ⟶ X),
      φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀)) ∧
      Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ := by
  let g : specOver R A ⟶ Over.mk ξ := Over.homMk φ hφ
  obtain ⟨A₀, hA₀, x₀, hx₀⟩ := hG A (e.homEquiv g)
  let g₀ : specOver R ↥A₀ ⟶ Over.mk ξ := e.homEquiv.symm x₀
  refine ⟨A₀, hA₀, g₀.left, Over.w g₀, ?_⟩
  have hg : specOverOfSubalgebra R A₀ ≫ g₀ = g :=
    e.homEquiv.injective (by rw [e.homEquiv_comp, Equiv.apply_symm_apply, hx₀])
  exact congrArg (fun k => k.left) hg

end AlgebraicGeometry.AffineLimit

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) :
    LocallyOfFiniteType D.toBase :=
  locallyOfFiniteType_of_forall_exists_fg_factor D.toBase fun A _ _ φ hφ =>
    exists_fg_factor_of_representableBy D.toBase _ h.representableBy
      (isLFPSurj_relSubPicPresheaf_algEquivZeroCut R c ε h𝔉) A φ hφ
