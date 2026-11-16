/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T')
  (C : Type u) [CommRing C] [Algebra T' C]

def chartRingHom {Ak : Scheme.{u}} (Ue : Ak.Opens)
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) :
    Γ(Ak, Ue) →+* thickening T' V C :=
  (Ue.topIso.inv ≫ w₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (thickening T' V C))).hom).hom

def IsTangentCoordsOfPairAt {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))) : Prop :=
  ∃ (w₀ : Spec (CommRingCat.of (thickening T' V C)) ⟶ Ak)
    (hw₀ : w₀ ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})),
    IsTangentOfPair I V ι C u v (w₀ ≫ ak) ∧
    w₁ ≫ Ue.ι = (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
                  (thickening_isPullback V C) w₀ hw₀).1 ∧
    c = tangentCoords T' V C (chartRingHom V C Ue w₁)

end AlgebraicGeometry.SmallExtension

end
