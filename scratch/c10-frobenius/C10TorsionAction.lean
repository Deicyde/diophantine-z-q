import C10FieldPoints

set_option autoImplicit false

/-!
# Frobenius on same-field finite-order points

Restrict the existing point-group automorphism to the actual n-torsion sets.
This is not a reduction map, a Tate-module transport, or a C10 comparison.
No commutativity hypothesis is needed for a statement about these sets.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace C10Frobenius.TorsionAction

universe u

variable {k : Type u} [Field k] [Fintype k] (K : Type u) [Field K] [Algebra k K]
  (p f : ℕ) [Fact p.Prime] [CharP k p] [CharP K p] [PerfectRing K p]
  (hcard : Fintype.card k = p ^ f)

/-- The same-field Frobenius action preserves and reflects every n-torsion predicate. -/
theorem endomorphism_pow_eq_one_iff (A : Grp (Over (Spec (.of k)))) (n : ℕ)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X) :
    (x ≫ (FiniteField.endomorphism p f hcard A).hom.hom) ^ n = 1 ↔ x ^ n = 1 := by
  rw [FieldPoints.endomorphism_eq_arithmeticPointEquiv]
  simpa only [map_pow] using
    (FieldPoints.arithmeticPointEquiv K p f hcard A).map_eq_one_iff (x := x ^ n)

/-- Same-field Frobenius is bijective on every actual n-torsion set. -/
theorem endomorphism_bijOn_nTorsion (A : Grp (Over (Spec (.of k)))) (n : ℕ) :
    Set.BijOn (fun x :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X =>
        x ≫ (FiniteField.endomorphism p f hcard A).hom.hom)
      {x | x ^ n = 1} {x | x ^ n = 1} := by
  simpa only [FieldPoints.endomorphism_eq_arithmeticPointEquiv,
    MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] using
    (FieldPoints.arithmeticPointEquiv K p f hcard A).toEquiv.bijOn
      (s := {x | x ^ n = 1}) (t := {x | x ^ n = 1})
      (fun x => by
        change (FieldPoints.arithmeticPointEquiv K p f hcard A x) ^ n = 1 ↔ x ^ n = 1
        simpa only [FieldPoints.endomorphism_eq_arithmeticPointEquiv] using
          endomorphism_pow_eq_one_iff K p f hcard A n x)

/-- Restrict the existing same-field action with the upstream set-bijection constructor. -/
def torsionPointEquiv (A : Grp (Over (Spec (.of k)))) (n : ℕ) :
    {x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X // x ^ n = 1} ≃
      {x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X // x ^ n = 1} :=
  Set.BijOn.equiv (fun x => x ≫ (FiniteField.endomorphism p f hcard A).hom.hom)
    (endomorphism_bijOn_nTorsion K p f hcard A n)

/-- The restricted equivalence still acts by the exact scheme Frobenius map. -/
@[simp] theorem torsionPointEquiv_apply (A : Grp (Over (Spec (.of k)))) (n : ℕ)
    (x : {x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X // x ^ n = 1}) :
    (torsionPointEquiv K p f hcard A n x).val =
      x.val ≫ (FiniteField.endomorphism p f hcard A).hom.hom := rfl

end C10Frobenius.TorsionAction
