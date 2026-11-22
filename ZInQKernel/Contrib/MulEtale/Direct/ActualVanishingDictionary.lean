/-
Multiplication-etale construction: ActualVanishingDictionary.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import Mathlib.RingTheory.Derivation.Basic

noncomputable section

namespace H101DirectFieldRoute.ActualTransport

/-- Exact integer/relative derivation dictionary. In the geometric caller,
all algebra/module structures below are induced by actual stalk/residue maps. -/
def annihilatingZEquiv
    (R A κ : Type*) [CommRing R] [CommRing A] [CommRing κ]
    [Algebra R A] [Algebra A κ] [Algebra R κ] [IsScalarTower R A κ] :
    {d : Derivation ℤ A κ // ∀ r : R, d (algebraMap R A r) = 0} ≃
      Derivation R A κ where
  toFun D :=
    { toLinearMap :=
        { toFun := D.val
          map_add' := D.val.map_add
          map_smul' := by
            intro r a
            have hz : D.val (algebraMap R A r) = 0 := D.property r
            calc D.val (r • a)
                = D.val (algebraMap R A r * a) := by rw [Algebra.smul_def]
              _ = algebraMap R A r • D.val a + a • D.val (algebraMap R A r) :=
                D.val.leibniz _ _
              _ = r • D.val a := by
                rw [hz, smul_zero, add_zero, IsScalarTower.algebraMap_smul] }
      map_one_eq_zero' := D.val.map_one_eq_zero
      leibniz' := D.val.leibniz }
  invFun D := ⟨D.restrictScalars ℤ, D.map_algebraMap⟩
  left_inv _ := Subtype.ext (Derivation.ext fun _ => rfl)
  right_inv _ := Derivation.ext fun _ => rfl

@[simp]
theorem annihilatingZEquiv_apply
    (R A κ : Type*) [CommRing R] [CommRing A] [CommRing κ]
    [Algebra R A] [Algebra A κ] [Algebra R κ] [IsScalarTower R A κ]
    (D : {d : Derivation ℤ A κ // ∀ r : R, d (algebraMap R A r) = 0}) (a : A) :
    annihilatingZEquiv R A κ D a = D.val a := rfl

end H101DirectFieldRoute.ActualTransport
