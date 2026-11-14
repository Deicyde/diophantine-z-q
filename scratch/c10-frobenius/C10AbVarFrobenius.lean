import C10Frobenius
import ZInQKernel.HDecomp.Objects
import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeUniversalHomeomorphism

set_option autoImplicit false

/-!
# Native abelian-variety Frobenius packaging

Use the original fork's PkgI3.AbVar and ObjBridge constructors. The target
is the canonical Frobenius twist, with its transported original group law;
no endomorphism over an arbitrary characteristic-p field is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius

namespace C10Frobenius.NativeAbVar

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The actual canonical group twist retains all original abelian-variety properties. -/
instance twistIsAbelianVariety (A : PkgI3.AbVar k) :
    PkgI2.IsAbelianVariety
      (groupTwist (Spec (.of k)) p (isInCharacteristic_spec k p) (ObjBridge.toGrp A)) := by
  constructor
  · change IsProper
      ((Over.pullback (absoluteFrobenius (Spec (.of k)) p
        (isInCharacteristic_spec k p))).obj A.X).hom
    dsimp
    infer_instance
  · change Smooth
      ((Over.pullback (absoluteFrobenius (Spec (.of k)) p
        (isInCharacteristic_spec k p))).obj A.X).hom
    dsimp
    infer_instance
  · change GeometricallyIntegral
      ((Over.pullback (absoluteFrobenius (Spec (.of k)) p
        (isInCharacteristic_spec k p))).obj A.X).hom
    dsimp
    infer_instance

/-- The canonical Frobenius twist as the original native abelian-variety object. -/
def twist (A : PkgI3.AbVar k) : PkgI3.AbVar k :=
  ObjBridge.ofGrp
    (groupTwist (Spec (.of k)) p (isInCharacteristic_spec k p) (ObjBridge.toGrp A))

/-- The native object retains exactly the original transported group object. -/
@[simp] theorem toGrp_twist (A : PkgI3.AbVar k) :
    ObjBridge.toGrp (twist p A) =
      groupTwist (Spec (.of k)) p (isInCharacteristic_spec k p) (ObjBridge.toGrp A) :=
  ObjBridge.toGrp_ofGrp _

/-- The relative Frobenius as the original native `AbVar.Hom`, not a substitute map. -/
def hom (A : PkgI3.AbVar k) : PkgI3.AbVar.Hom A (twist p A) :=
  ObjBridge.homOfGrp
    (relativeHom (Spec (.of k)) p (isInCharacteristic_spec k p) (ObjBridge.toGrp A))

/-- The native Hom's underlying map is exactly upstream relative Frobenius. -/
@[simp] theorem hom_hom (A : PkgI3.AbVar k) :
    PkgI3.AbVar.Hom.hom (hom p A) =
      relativeFrobenius (Spec (.of k)) p (isInCharacteristic_spec k p) A.X := by
  exact relativeHom_hom (Spec (.of k)) p (isInCharacteristic_spec k p) (ObjBridge.toGrp A)

/-- This same native relative Frobenius satisfies the original finite-surjective predicate. -/
theorem hom_isIsogeny (A : PkgI3.AbVar k) :
    PkgI3.AbVar.IsIsogenyMor (PkgI3.AbVar.Hom.hom (hom p A)) := by
  unfold PkgI3.AbVar.IsIsogenyMor
  rw [hom_hom]
  refine ⟨?_, ?_⟩
  · let : IsProper A.X.hom := A.proper
    let : LocallyOfFiniteType A.X.hom := inferInstance
    exact relativeFrobenius_isFinite (Spec (.of k)) p (isInCharacteristic_spec k p) A.X
  · exact ((universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp
      (relativeFrobenius_universalHomeomorphism (Spec (.of k)) p
        (isInCharacteristic_spec k p) A.X)).2.2

end C10Frobenius.NativeAbVar
