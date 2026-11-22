import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Stalk
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalkCartesian
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.RingTheory.Kaehler.PushoutBaseChange
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
Only upstream lines [(115, 145)] are retained.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory

open _root_.CategoryTheory
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom
#cloudR2LocalInstances
#cloudR2Vendor isIso_relativeDifferentialsMap_of_isPullback in
/-- **Stacks Project, Tag 01V0.** For a cartesian square of schemes with left edge `f' : X' ⟶ S'`,
right edge `f : X ⟶ S` and top edge `g' : X' ⟶ X`, the canonical map
`g'^* Ω_{X/S} ⟶ Ω_{X'/S'}` of Tag 01UV is an isomorphism. -/

theorem isIso_relativeDifferentialsMap_of_isPullback {X' X S' S : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (h : IsPullback g' f' f g) :
    IsIso (relativeDifferentialsMap g' f f' g h.w) := by
  refine isIso_relativeDifferentialsMap_of_stalk g' f f' g h.w fun x => ?_
  intro R A B C
  let : Algebra R A := (f.stalkMap (g'.base x)).hom.toAlgebra
  let : Algebra A C := (g'.stalkMap x).hom.toAlgebra
  let : Algebra B C := (f'.stalkMap x).hom.toAlgebra
  let : Algebra R B :=
    (eqToHom (congrArg (fun z => S.presheaf.stalk z)
        (congrArg (fun k : X' ⟶ S => k.base x) h.w)) ≫ g.stalkMap (f'.base x)).hom.toAlgebra
  obtain ⟨φ, hleft, hright, M, hloc⟩ :=
    BaseChangeStalk.cartesian_stalk_isLocalization g' f' f g h x
  let T : Type u := TensorProduct R A B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra T C := φ.toAlgebra
  let : IsScalarTower A T C :=
    IsScalarTower.of_algebraMap_eq fun a => (DFunLike.congr_fun hleft a).symm
  let : IsScalarTower B T C :=
    IsScalarTower.of_algebraMap_eq fun b => (DFunLike.congr_fun hright b).symm
  let : Algebra.IsPushout R B A T :=
    (inferInstance : Algebra.IsPushout R A B (TensorProduct R A B)).symm
  let M' : Submonoid T := M
  let : IsLocalization M' C := hloc
  let : Algebra.FormallyEtale T C := Algebra.FormallyEtale.of_isLocalization M'
  exact ⟨KaehlerDifferential.tensorKaehlerEquivOfFormallyEtalePushout R A B T C,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtalePushout_tmul_D R A B T C⟩
end AlgebraicGeometry.Scheme.Hom

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
