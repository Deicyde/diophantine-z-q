/-
H5 Lane5 GM12, universe-u native power/pullback maps. SOURCE ONLY, UNCOMPILED.

NO-LINE ANALYSIS (the original target is unchanged):
PkgI2.HasGoodReduction A O requires ONLY an actual abelian-scheme GROUP over
O with an actual generic-fibre GROUP isomorphism to the same original A/K.
It contains no line bundle. L0 and M are existential witnesses constructed
from the original inputs; a line, closed-section presentation and psi/cocycle
are INTERMEDIATE effective-descent data, never final NOS premises. The final
consumer must descend the actual Source power M^n with beta^n to the Source
power L0' of the SAME original L0, using actual monoidal pullback/power maps.

This first GM12 component constructs the native half of those maps. It uses
only the actual W07 left-recursive powers and the actual native monoidal
pullback tensorator/unit. It does NOT identify them with the Source power,
port a FLT Type0 closure, assume a comparison Fact, or claim original NOS.
The remaining Source/native tensor/power comparison is a separate typed edge.

Original mathematical code. W07/Jacobian-Challenge primitive notices and
Apache-2.0 copyrights remain in their unchanged imported sources.
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorPower
import Mathlib.CategoryTheory.Monoidal.Functor

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace H5OriginalDVR.Lane5.GM12.NativePower

variable {X : Scheme.{u}}

/-- Actual map on the native W07 tensor powers. No Source power is aliased. -/
def map {M N : X.Modules} (f : M ⟶ N) :
    (n : ℕ) → M.tensorPow n ⟶ N.tensorPow n
  | 0 => 𝟙 _
  | n + 1 => f ⊗ₘ map f n

@[simp]
theorem map_zero {M N : X.Modules} (f : M ⟶ N) : map f 0 = 𝟙 _ := rfl

@[simp]
theorem map_succ {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    map f (n + 1) = f ⊗ₘ map f n := rfl

@[simp]
theorem map_id (M : X.Modules) (n : ℕ) : map (𝟙 M) n = 𝟙 (M.tensorPow n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (𝟙 M) ⊗ₘ map (𝟙 M) n = 𝟙 (M ⊗ M.tensorPow n)
      rw [ih]
      exact MonoidalCategory.id_tensorHom_id M (M.tensorPow n)

@[simp]
theorem map_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    map (f ≫ g) n = map f n ≫ map g n := by
  induction n with
  | zero =>
      change 𝟙 (𝟙_ X.Modules) = 𝟙 (𝟙_ X.Modules) ≫ 𝟙 (𝟙_ X.Modules)
      exact (Category.id_comp (𝟙 (𝟙_ X.Modules))).symm
  | succ n ih =>
      change (f ≫ g) ⊗ₘ map (f ≫ g) n =
        (f ⊗ₘ map f n) ≫ (g ⊗ₘ map g n)
      rw [ih]
      exact (MonoidalCategory.tensorHom_comp_tensorHom f (map f n) g (map g n)).symm

/-- Powers are a genuine functor, with the literal native W07 objects. -/
def functor (n : ℕ) : X.Modules ⥤ X.Modules where
  obj M := M.tensorPow n
  map f := map f n
  map_id M := map_id M n
  map_comp f g := map_comp f g n

/-- Power of an actual module isomorphism, including its actual inverse. -/
def mapIso {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    M.tensorPow n ≅ N.tensorPow n := (functor n).mapIso e

@[simp]
theorem mapIso_hom {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    (mapIso e n).hom = map e.hom n := rfl

@[simp]
theorem mapIso_inv {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    (mapIso e n).inv = map e.inv n := rfl

/-- Pullback commutes with powers by the actual monoidal unit/tensor maps.
The zero case is the inverse of the monoidal unit isomorphism; the successor
case is the inverse tensorator followed by the previous comparison. -/
def pullbackIso {Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (n : ℕ) → (Scheme.Modules.pullback f).obj (M.tensorPow n) ≅
      ((Scheme.Modules.pullback f).obj M).tensorPow n
  | 0 => (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm
  | n + 1 =>
      Scheme.Modules.pullbackTensorObjIso f M (M.tensorPow n) ≪≫
        (Iso.refl ((Scheme.Modules.pullback f).obj M) ⊗ᵢ pullbackIso f M n)

/-- Literal comparison map at exponent zero, not an arbitrary chosen iso. -/
theorem pullbackIso_zero {Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    pullbackIso f M 0 = (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm := rfl

/-- Literal comparison map at a successor, retaining the actual tensorator. -/
theorem pullbackIso_succ {Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ) :
    pullbackIso f M (n + 1) =
      Scheme.Modules.pullbackTensorObjIso f M (M.tensorPow n) ≪≫
        (Iso.refl ((Scheme.Modules.pullback f).obj M) ⊗ᵢ pullbackIso f M n) := rfl

/-- An actual generic beta between pullbacks yields its native power beta.
The same maps i and q, same M and L0 and same beta are preserved. This is an
intermediate object/map construction, not a new final good-model assumption. -/
def betaPow {U A : Scheme.{u}} (i : U ⟶ X) (q : U ⟶ A)
    (M : X.Modules) (L0 : A.Modules)
    (beta : (Scheme.Modules.pullback i).obj M ≅
      (Scheme.Modules.pullback q).obj L0) (n : ℕ) :
    (Scheme.Modules.pullback i).obj (M.tensorPow n) ≅
      (Scheme.Modules.pullback q).obj (L0.tensorPow n) :=
  pullbackIso i M n ≪≫ mapIso beta n ≪≫ (pullbackIso q L0 n).symm

/-- The map is the prescribed monoidal construction of the original beta. -/
theorem betaPow_hom {U A : Scheme.{u}} (i : U ⟶ X) (q : U ⟶ A)
    (M : X.Modules) (L0 : A.Modules)
    (beta : (Scheme.Modules.pullback i).obj M ≅
      (Scheme.Modules.pullback q).obj L0) (n : ℕ) :
    (betaPow i q M L0 beta n).hom =
      (pullbackIso i M n).hom ≫ map beta.hom n ≫ (pullbackIso q L0 n).inv := rfl

/-- Native invertibility of powers is an actual W07 theorem, not a Fact. -/
theorem invertible (M : X.Modules) [M.IsInvertible] (n : ℕ) :
    (M.tensorPow n).IsInvertible := inferInstance

end H5OriginalDVR.Lane5.GM12.NativePower
