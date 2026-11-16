/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_Algebra_PointDerivations
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover

universe u
theorem AlgebraicGeometry.SmallExtension.mem_pointDerivations_tangentCoords_and_injective_and_surjective
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C]
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (pt : Spec (CommRingCat.of (ResidueField T')) ⟶ Ak) (hpt : pt ≫ xk = 𝟙 _)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = pt) :
    letI := algebraOfHom xk Ue
    (∀ w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
        (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt →
        ∃ D : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
                ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
                (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))),
          ∀ a, D.1 a = tangentCoords T' V C (chartRingHom V C Ue w₁) a) ∧
    (∀ w₁ w₁' : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
        (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt →
        (w₁' ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁' ≫ Ue.ι = reductionBase T' C ≫ pt →
        tangentCoords T' V C (chartRingHom V C Ue w₁) = tangentCoords T' V C (chartRingHom V C Ue w₁') → w₁ = w₁') ∧
    (∀ D : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
                ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
                (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))),
        ∃ w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
          (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) ∧
          SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
              ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt ∧
          ∀ a, D.1 a = tangentCoords T' V C (chartRingHom V C Ue w₁) a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective.solution
