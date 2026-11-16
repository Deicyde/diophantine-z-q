/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentOfPair_comp_of_isTangentOfPair_of_flat
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SmallExtension_isTangentOfPair_comp_of_isTangentOfPair_of_flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u
theorem AlgebraicGeometry.SmallExtension.isTangentOfPair_comp_of_isTangentOfPair_of_flat
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] (C' : Type u) [CommRing C'] [Algebra T' C'] [Module.Flat T' C']
    (h : C →ₐ[T'] C')
    {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y) (w : Spec (CommRingCat.of (thickening T' V C)) ⟶ Y)
    (huvw : IsTangentOfPair I V ι C u v w) :
    IsTangentOfPair I V ι C'
      (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ u)
      (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ v)
      (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map
              (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h)
              (AlgHom.id (ResidueField T') (TrivSqZeroExt (ResidueField T') V)) :
            thickening T' V C →ₐ[ResidueField T'] thickening T' V C').toRingHom) ≫ w) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_isTangentOfPair_comp_of_isTangentOfPair_of_flat.solution
