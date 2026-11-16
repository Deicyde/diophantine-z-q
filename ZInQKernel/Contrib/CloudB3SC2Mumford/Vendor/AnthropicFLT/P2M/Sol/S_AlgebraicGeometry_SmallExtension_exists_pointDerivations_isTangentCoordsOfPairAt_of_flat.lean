/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_Algebra_PointDerivations
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_isTangentCoordsOfPairAt_of_flat

set_option autoImplicit false

-- [port] was: p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover GoodReductionJacobian NeronModelInfra"
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TensorProduct
open _root_.IsLocalRing
open _root_.AlgebraicGeometry.SmallExtension
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.GoodReductionJacobian
open _root_.NeronModelInfra

universe u

theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u : Spec (CommRingCat.of C) ⟶ Y) (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (v : Spec (CommRingCat.of C) ⟶ Y) (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1) :
    letI := algebraOfHom xk Ue
    ∃ δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))),
      IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue
        (fun a => (δ : Γ(Ak, Ue) →ₗ[ResidueField T'] (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))) a) := by
  obtain ⟨c, hc⟩ := exists_isTangentCoordsOfPairAt I hI hsmall V ι hι hιI C qY u hu xk Lk ak hak Ue hUe e₁ he₁ v hv huv
  obtain ⟨w₀, hw₀, w₁, hpair, hw₁, hcw⟩ := hc
  have h1 : (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) := by
    rw [hw₁]
    exact (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) w₀ hw₀).2.1
  have h2 : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
      ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ (Lk.one (𝟙 _)).1 := by
    rw [hw₁]
    exact (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) w₀ hw₀).2.2
  obtain ⟨D, hD⟩ := (mem_pointDerivations_tangentCoords_and_injective_and_surjective V C xk (Lk.one (𝟙 _)).1
    (Lk.one (𝟙 _)).2 Ue hUe e₁ he₁).1 w₁ h1 h2
  refine ⟨D, w₀, hw₀, w₁, hpair, hw₁, ?_⟩
  rw [← hcw]
  exact funext fun a => (hD a).trans (congrFun hcw a).symm
