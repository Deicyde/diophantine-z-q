import ZInQKernel.Contrib.OneProof.SZThm33.ToricSchemeTorsionDensity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.LocalSections

/-! Universal units and the affine reductions of the prime-power torsion
subschemes of a split torus. -/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace SZRaynaud

abbrev ToricRing (R : Type*) [CommRing R] (r : ℕ) :=
  AddMonoidAlgebra R (Fin r → ℤ)

/-- The Laurent monomial corresponding to an exponent lattice vector,
viewed as a unit. -/
def toricMonomialUnit {R : Type*} [CommRing R] {M : Type*} [AddGroup M] (a : M) :
    (AddMonoidAlgebra R M)ˣ :=
  (AddMonoidAlgebra.of R M).toHomUnits (Multiplicative.ofAdd a)

/-- The universal tuple of invertible torus coordinates. -/
def toricUniversal {R : Type*} [CommRing R] (r : ℕ) (i : Fin r) : (ToricRing R r)ˣ :=
  toricMonomialUnit (Pi.single i 1)

private def toricCharacter {R : Type*} [CommRing R] {r : ℕ} (t : Fin r → Rˣ) :
    Multiplicative (Fin r → ℤ) →* Rˣ where
  toFun a := ∏ i, t i ^ a.toAdd i
  map_one' := by simp
  map_mul' a b := by
    change (∏ i, t i ^ (a.toAdd i + b.toAdd i)) = _
    simp only [zpow_add, Finset.prod_mul_distrib]

/-- Evaluating the universal tuple at any specified tuple of units. -/
def toricEvaluate {R : Type*} [CommRing R] {r : ℕ} (t : Fin r → Rˣ) :
    ToricRing R r →ₐ[R] R :=
  AddMonoidAlgebra.lift R R _ ((Units.coeHom R).comp (toricCharacter t))

theorem toricEvaluate_universal {R : Type*} [CommRing R] {r : ℕ}
    (t : Fin r → Rˣ) (i : Fin r) :
    Units.map (toricEvaluate t).toRingHom.toMonoidHom (toricUniversal r i) = t i := by
  classical
  apply Units.ext
  change toricEvaluate t (AddMonoidAlgebra.single (Pi.single i 1) 1) = _
  rw [toricEvaluate, AddMonoidAlgebra.lift_single, one_smul]
  let z : Fin r → ℤ := Pi.single i 1
  change ((∏ j, t j ^ z j : Rˣ) : R) = _
  apply congrArg (fun a : Rˣ => (a : R))
  rw [Finset.prod_eq_single i]
  · simp [z]
  · intro j _ hj
    simp [z, Pi.single_eq_of_ne hj]
  · simp

/-- The universal tuple becomes (m)-torsion after reducing the exponent
lattice modulo (m). -/
theorem toricUniversal_torsion {R : Type*} [CommRing R] (r m : ℕ) (i : Fin r) :
    (Units.map (AddMonoidAlgebra.mapDomainRingHom R (modToricExponent r m)).toMonoidHom
      (toricUniversal r i)) ^ m = 1 := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_one]
  change ((AddMonoidAlgebra.mapDomainRingHom R (modToricExponent r m))
    (AddMonoidAlgebra.single (Pi.single i 1) 1)) ^ m = 1
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
  let z := modToricExponent r m (Pi.single i 1)
  have hz : m • z = 0 := by
    funext j
    change m • (z j) = 0
    simp [nsmul_eq_mul]
  change (AddMonoidAlgebra.of R _ (Multiplicative.ofAdd z)) ^ m = 1
  rw [← map_pow]
  change AddMonoidAlgebra.of R _ (Multiplicative.ofAdd (m • z)) = 1
  rw [hz]
  exact map_one (AddMonoidAlgebra.of R (Fin r → ZMod m))

set_option backward.isDefEq.respectTransparency false in
/-- Field tests suffice for equality of morphisms from a split torus when
the compositions with étale multiplication agree on each torsion
subscheme. The argument works over a nonreduced base. -/
theorem affineToric_hom_ext_of_fieldTests_and_unramified
    {R : Type} [CommRing R] {r ℓ : ℕ} (hℓ : 1 < ℓ)
    {Y S : Scheme} (p : Y ⟶ S) [IsSeparated p]
    (f g : affineToricScheme R r ⟶ Y) (he : f ≫ p = g ≫ p)
    (w : ℕ → (Y ⟶ Y))
    (hL : ∀ n, LocallyOfFiniteType (w n)) (hU : ∀ n, FormallyUnramified (w n))
    (hComp : ∀ n, affineToricTorsionι R r (ℓ ^ n) ≫ f ≫ w n =
      affineToricTorsionι R r (ℓ ^ n) ≫ g ≫ w n)
    (hField : ∀ (n : ℕ) (L : Type) [Field L]
      (a : Spec (.of L) ⟶ Spec (.of (AddMonoidAlgebra R (Fin r → ZMod (ℓ ^ n))))),
      a ≫ affineToricTorsionι R r (ℓ ^ n) ≫ f =
        a ≫ affineToricTorsionι R r (ℓ ^ n) ≫ g) : f = g := by
  apply affineToric_hom_ext_torsion hℓ p f g he
  intro n
  let D := AddMonoidAlgebra R (Fin r → ZMod (ℓ ^ n))
  let d := affineToricTorsionι R r (ℓ ^ n)
  let a := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical D)))
  haveI : Surjective a :=
    ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical (R := D) le_rfl).2⟩
  haveI : IsReduced (D ⧸ nilradical D) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  haveI : LocallyOfFiniteType (w n) := hL n
  haveI : FormallyUnramified (w n) := hU n
  apply hom_eq_of_surjective_precomp_of_formallyUnramified (w n) (d ≫ f) (d ≫ g)
    (by simpa only [Category.assoc] using hComp n) a
  let T := Over.mk (a ≫ d ≫ f ≫ p)
  let Y' := Over.mk p
  have eq : a ≫ d ≫ g ≫ p = T.hom := by change _ = a ≫ d ≫ f ≫ p; rw [he]
  let f' : T ⟶ Y' := Over.homMk (a ≫ d ≫ f) (by
    change (a ≫ d ≫ f) ≫ p = a ≫ d ≫ f ≫ p
    simp only [Category.assoc])
  let g' : T ⟶ Y' := Over.homMk (a ≫ d ≫ g) (by
    change (a ≫ d ≫ g) ≫ p = T.hom
    simpa only [Category.assoc] using eq)
  haveI : IsReduced T.left := inferInstanceAs (IsReduced (Spec (.of (D ⧸ nilradical D))))
  haveI : IsSeparated Y'.hom := ‹IsSeparated p›
  have hh := Scheme.over_hom_eq_of_field_tests f' g' (fun L _ b v => by
    apply Over.OverMorphism.ext
    change v.left ≫ a ≫ d ≫ f = v.left ≫ a ≫ d ≫ g
    simpa only [Category.assoc] using hField n L (v.left ≫ a))
  have hc := congrArg Over.Hom.left hh
  change a ≫ d ≫ f = a ≫ d ≫ g at hc
  simpa only [Category.assoc] using hc

#print axioms toricEvaluate_universal
#print axioms toricUniversal_torsion
#print axioms affineToric_hom_ext_of_fieldTests_and_unramified

end SZRaynaud
