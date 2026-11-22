/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_pointSubBasepoint. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_ajFamily_fibre_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_pointSubBasepoint

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open GoodReductionJacobian

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a] [LocallyOfFiniteType a]
    (P ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    IsAlgEquivZero a ((Scheme.Modules.pullback (toProdSpec a)).obj (pointSubBasepointModule (a := a) P ε)) :=
  by
  refine ⟨A, a, inferInstance, inferInstance, ajFamily (a := a) ε, isInvertible_ajFamily (a := a) ε, ε, P, ?_, ?_⟩
  · obtain ⟨i⟩ := nonempty_ajFamily_fibre_iso (a := a) ε ε
    obtain ⟨p⟩ := Scheme.IdealSheafData.IsCartierFLT.nonempty_invModule_tensor_module_iso
      (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint a ε.1 ε.2))
    exact ⟨i ≪≫ p⟩
  · obtain ⟨i⟩ := nonempty_ajFamily_fibre_iso (a := a) ε P
    exact ⟨i ≪≫ (fstPullbackToProdSpecPullbackIso a _).symm⟩
