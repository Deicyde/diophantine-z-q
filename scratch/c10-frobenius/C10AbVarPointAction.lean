import C10AbVarFiniteField
import C10FieldPoints

set_option autoImplicit false

/-!
# Frobenius on the original native finite-field points

Identify the exact q-power native endomorphism's point map with the existing
native arithmetic-Galois action. No reduction map or global GQ comparison
is constructed, and no point or Tate model is replaced.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius
open scoped CategoryTheory.MonObj

namespace C10Frobenius.NativePointAction

variable {k : Type} [Field k] [Fintype k] (K : Type) [Field K] [Algebra k K]
  (p f : ℕ) [Fact p.Prime] [CharP k p] [CharP K p] [PerfectRing K p]
  (hcard : Fintype.card k = p ^ f)

/-- The original native point map is the exact arithmetic-Frobenius action on coordinates. -/
theorem ptMap_apply (A : PkgI3.AbVar k) (x : A.Pt K) :
    PkgI3.AbVar.ptMap (L := K) (NativeFiniteField.endomorphism p f hcard A) x =
      A.galAct (arithmeticFrobenius k K p f hcard) x := by
  apply Over.OverMorphism.ext
  exact FieldPoints.endomorphism_onFieldPoints K p f hcard (ObjBridge.toGrp A) x

/-- Equality in the original native point-homomorphism API, not just a coordinate slogan. -/
theorem ptMap_eq_galAct (A : PkgI3.AbVar k) :
    PkgI3.AbVar.ptMap (L := K) (NativeFiniteField.endomorphism p f hcard A) =
      A.galAct (arithmeticFrobenius k K p f hcard) :=
  MonoidHom.ext (ptMap_apply K p f hcard A)

/-- The existing q-power automorphism on the actual algebraic closure, in the native Galois type. -/
def arithmeticGal : Field.absoluteGaloisGroup k := by
  let : CharP (AlgebraicClosure k) p :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  exact arithmeticFrobenius k (AlgebraicClosure k) p f hcard

/-- The native finite-field Galois element is arithmetic, acting by q-th powers. -/
theorem arithmeticGal_apply (x : AlgebraicClosure k) :
    (AlgEquiv.toAlgHom (arithmeticGal p f hcard)) x = x ^ Fintype.card k := by
  let : CharP (AlgebraicClosure k) p :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  exact arithmeticFrobenius_apply k (AlgebraicClosure k) p f hcard x

/-- On the actual algebraic-closure points, the native End map equals native Galois action. -/
theorem ptMap_eq_galAct_arithmeticGal (A : PkgI3.AbVar k) :
    PkgI3.AbVar.ptMap (L := AlgebraicClosure k)
        (NativeFiniteField.endomorphism p f hcard A) =
      A.galAct (arithmeticGal p f hcard) := by
  let : CharP (AlgebraicClosure k) p :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  exact ptMap_eq_galAct (AlgebraicClosure k) p f hcard A

/-- The original native Tate map is the existing Galois map of arithmetic Frobenius. -/
theorem homT_eq_galT (A : PkgI3.AbVar k) (ℓ : ℕ) [Fact ℓ.Prime] :
    PkgI3.AbVar.homT (ℓ := ℓ) (NativeFiniteField.endomorphism p f hcard A) =
      A.galT (ℓ := ℓ) (arithmeticGal p f hcard) := by
  unfold PkgI3.AbVar.homT PkgI3.AbVar.galT
  rw [ptMap_eq_galAct_arithmeticGal]

/-- Rationalizing the original native Tate map gives the original Galois representation action. -/
theorem homT_baseChange_eq_galRep (A : PkgI3.AbVar k) (ℓ : ℕ) [Fact ℓ.Prime] :
    (PkgI3.AbVar.homT (ℓ := ℓ) (NativeFiniteField.endomorphism p f hcard A)).baseChange ℚ_[ℓ] =
      A.galRep ℓ (arithmeticGal p f hcard) := by
  change (PkgI3.AbVar.homT (ℓ := ℓ)
    (NativeFiniteField.endomorphism p f hcard A)).baseChange ℚ_[ℓ] =
      (A.galT (ℓ := ℓ) (arithmeticGal p f hcard)).baseChange ℚ_[ℓ]
  rw [homT_eq_galT]

end C10Frobenius.NativePointAction
