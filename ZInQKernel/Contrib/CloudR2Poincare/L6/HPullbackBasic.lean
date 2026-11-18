import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Isomorphism
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Invertible
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Sections

/-!
# Actual native unit-cohomology pullback and scalar action

H-72 L6 native implementation. Uses the unchanged W07 native Scheme.Modules.H
pullback/coefficient maps (Jacobian-Challenge c4254cce, existing W07 LICENSE /
NOTICE and port change notices). New L6 wrappers; no supplier or pin is changed.
These maps are the actual W07 maps, not a rank-selected comparison.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L6

/-- Actual pullback on the cohomology of the native structure sheaf. -/
def nativeUnitHPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ) :
    (Scheme.Modules.unit Y).H q →+ (Scheme.Modules.unit X).H q :=
  (Scheme.Modules.H.map (Scheme.Modules.pullbackObjUnitIso f).hom q).comp
    (Scheme.Modules.H.pullback f (Scheme.Modules.unit Y) q).toAddMonoidHom

/-- The full defining map, with the actual native unit coefficient iso. -/
theorem nativeUnitHPullback_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ)
    (z : (Scheme.Modules.unit Y).H q) :
    nativeUnitHPullback f q z =
      Scheme.Modules.H.map (Scheme.Modules.pullbackObjUnitIso f).hom q
        (Scheme.Modules.H.pullback f (Scheme.Modules.unit Y) q z) := rfl

/-- Semilinearity for the ACTUAL map on global functions, for every scheme morphism. -/
theorem nativeUnitHPullback_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ)
    (a : Γ(Y, ⊤)) (z : (Scheme.Modules.unit Y).H q) :
    nativeUnitHPullback f q (a • z) = f.appTop a • nativeUnitHPullback f q z := by
  change Scheme.Modules.H.map (Scheme.Modules.pullbackObjUnitIso f).hom q
      (Scheme.Modules.H.pullback f (Scheme.Modules.unit Y) q (a • z)) =
    f.appTop a • Scheme.Modules.H.map (Scheme.Modules.pullbackObjUnitIso f).hom q
      (Scheme.Modules.H.pullback f (Scheme.Modules.unit Y) q z)
  exact (congrArg
    (fun w => Scheme.Modules.H.map (Scheme.Modules.pullbackObjUnitIso f).hom q w)
    ((Scheme.Modules.H.pullback f (Scheme.Modules.unit Y) q).map_smul' a z)).trans
      (Scheme.Modules.H.map_smul _ q (f.appTop a) _)

/-- The same actual map is linear over the original field for an Over morphism. -/
def nativeUnitHPullbackLinearMap {k : Type u} [Field k]
    (X Y : Over (Spec (.of k))) (f : X ⟶ Y) (q : ℕ) :
    letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    (Scheme.Modules.unit Y.left).H q →ₗ[k] (Scheme.Modules.unit X.left).H q := by
  letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  refine { nativeUnitHPullback f.left q with map_smul' := ?_ }
  intro c z
  change nativeUnitHPullback f.left q
      (Scheme.globalSectionsRingHom k (X := Y.left) c • z) =
    Scheme.globalSectionsRingHom k (X := X.left) c • nativeUnitHPullback f.left q z
  rw [nativeUnitHPullback_smul]
  have hw : Y.hom.appTop ≫ f.left.appTop = X.hom.appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg (fun g : X.left ⟶ Spec (.of k) => g.appTop) (Over.w f)
  have hc : f.left.appTop (Scheme.globalSectionsRingHom k (X := Y.left) c) =
      Scheme.globalSectionsRingHom k (X := X.left) c := by
    change f.left.appTop (((Scheme.ΓSpecIso (.of k)).inv ≫ Y.hom.appTop) c) =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) c)
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ Y.hom.appTop) ≫ f.left.appTop) c =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) c)
    rw [Category.assoc, hw]
  rw [hc]

/-- The field-linear wrapper does not replace or alter the actual additive map. -/
theorem nativeUnitHPullbackLinearMap_apply {k : Type u} [Field k]
    (X Y : Over (Spec (.of k))) (f : X ⟶ Y) (q : ℕ) :
    letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    ∀ z : (Scheme.Modules.unit Y.left).H q,
      nativeUnitHPullbackLinearMap X Y f q z = nativeUnitHPullback f.left q z := by
  intros
  rfl

end ZInQ.Contrib.CloudR2Poincare.L6
