/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_pointSubBasepoint
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint

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
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))
    {L : A.Modules}
    (e : (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ pointsSubBasepointModule (a := a) ε Ps) :
    IsAlgEquivZero a L :=
  by
  have key : ∀ Qs : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a),
      IsAlgEquivZero a ((Scheme.Modules.pullback (toProdSpec a)).obj (pointsSubBasepointModule (a := a) ε Qs)) := by
    intro Qs
    induction Qs with
    | nil =>
      exact IsAlgEquivZero.of_iso (Scheme.Modules.pullbackTensorUnitObjIso _).symm (IsAlgEquivZero.tensorUnit a)
    | cons P Ps ih =>
      exact IsAlgEquivZero.of_iso (Scheme.Modules.pullbackTensorObjIsoFLT _ _ _).symm
        ((isAlgEquivZero_pointSubBasepoint P ε).tensor ih)
  exact IsAlgEquivZero.of_fst_pullback_iso e (key Ps)
