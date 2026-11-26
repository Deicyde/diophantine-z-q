import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Data.Complex.Basic

import Mathlib.Data.Nat.Totient
/-! # The generic comparison required by the integral model -/

open CategoryTheory AlgebraicGeometry

namespace WeierstrassCurve.ModelLevels

private noncomputable def complexSource : Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))

/-- Complex points of a scheme over the rationals. -/
abbrev RationalCurveComplexPoints (X : Over (Spec (CommRingCat.of ℚ))) :=
  complexSource ⟶ X

/-- The readings to be compared on the generic fibres. Hecke readings use
multisets to retain the multiplicities of the kernels producing a point. -/
structure GenericReadings (X : Over (Spec (CommRingCat.of ℚ))) (PairClasses TargetPoints : Type*) where
  j : RationalCurveComplexPoints X → ℂ
  pairClass : RationalCurveComplexPoints X → PairClasses
  atkinLehner : ℕ → RationalCurveComplexPoints X → RationalCurveComplexPoints X
  hecke : ℕ → RationalCurveComplexPoints X → Multiset (RationalCurveComplexPoints X)
  param : RationalCurveComplexPoints X → TargetPoints

/-- Open generic-fibre obligation for tex 8470–8479 and 8481–8492.
The intended `levelGeneric` is the rational base change of
`Spec ((S_N^H)_0)` and the intended `branchOpen` is the finite-`j`
chart `X0Model3.finiteChart N` of `X0Branch.model N`.
An isomorphism over the rationals must intertwine the (j)-reading, the
elliptic-curve and cyclic-subgroup reading, the exact-divisor Atkin–Lehner
operators, the good Hecke operators and the fixed parametrization.
The route through complex points and the function field `ℚ(j,j_N)`
has an UNVERIFIED print locator. -/
def GenericFibreComparison (ell N : ℕ) (_h5 : 5 ≤ ell)
    (_hTame : ¬ ell ∣ N * N.totient)
    (levelGeneric branchOpen : Over (Spec (CommRingCat.of ℚ))) {PairClasses TargetPoints : Type*}
    (level : GenericReadings levelGeneric PairClasses TargetPoints)
    (branch : GenericReadings branchOpen PairClasses TargetPoints) : Prop :=
  ∃ e : levelGeneric ≅ branchOpen,
    ∀ x : RationalCurveComplexPoints levelGeneric,
      branch.j (x ≫ e.hom) = level.j x ∧
      branch.pairClass (x ≫ e.hom) = level.pairClass x ∧
      (∀ Q : ℕ, Q ∣ N → Nat.Coprime Q (N / Q) →
        branch.atkinLehner Q (x ≫ e.hom) = level.atkinLehner Q x ≫ e.hom) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ell →
        branch.hecke p (x ≫ e.hom) = (level.hecke p x).map (fun y => y ≫ e.hom)) ∧
      branch.param (x ≫ e.hom) = level.param x

#print axioms GenericFibreComparison

end WeierstrassCurve.ModelLevels
