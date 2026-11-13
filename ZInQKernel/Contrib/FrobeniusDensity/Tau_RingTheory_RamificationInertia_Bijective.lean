/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported for the T18 contribution from TauCetiProject/TauCeti@1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/RingTheory/RamificationInertia/Bijective.lean. Changes: imports relocated to the owned flat contribution directory;
proof and definition bodies initially unchanged. Project pins are not changed.
See docs/research/t18-frobenius-density.md for attribution and license text.
-/
module

public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
import ZInQKernel.Contrib.FrobeniusDensity.Tau_Algebra_Algebra_Tower

/-!
# Residue degree and ramification index over isomorphic base rings

Let `R → S → T` be a tower of algebras in which `algebraMap R S` is bijective. Then an ideal of
`T` has the same residue degree over `R` as over `S`, and, under the flatness needed for
multiplicativity of ramification indices in towers, the same ramification index. This lets
statements about two presentations of the same base ring, such as `ℤ` and the ring of integers
of `ℚ`, be transported into each other.

## Main results

* `Ideal.inertiaDeg_eq_of_bijective`: `r.inertiaDeg S = r.inertiaDeg R`.
* `Ideal.ramificationIdx_eq_of_bijective`: `r.ramificationIdx S = r.ramificationIdx R`.
-/

public section

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T]

/-- An ideal has the same residue degree over `S` as over `R` when `algebraMap R S` is
bijective. -/
theorem inertiaDeg_eq_of_bijective (h : Function.Bijective (algebraMap R S)) (r : Ideal T) :
    r.inertiaDeg S = r.inertiaDeg R := by
  let e := RingEquiv.ofBijective (algebraMap R S) h
  let : Algebra S R := e.symm.toRingHom.toAlgebra
  have : IsScalarTower S R T := .of_algebraMap_rightInverse e.apply_symm_apply
  exact Nat.dvd_antisymm (inertiaDeg_above_dvd (r.under S) r) (inertiaDeg_above_dvd (r.under R) r)

/-- An ideal has the same ramification index over `S` as over `R` when `algebraMap R S` is
bijective and `T` is flat over `S`. -/
theorem ramificationIdx_eq_of_bijective [Module.Flat S T]
    (h : Function.Bijective (algebraMap R S)) (r : Ideal T) :
    r.ramificationIdx S = r.ramificationIdx R := by
  have : Module.Flat R S :=
    .of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap R S) h).symm
  have : Module.Flat R T := .trans R S T
  let e := RingEquiv.ofBijective (algebraMap R S) h
  let : Algebra S R := e.symm.toRingHom.toAlgebra
  have : IsScalarTower S R T := .of_algebraMap_rightInverse e.apply_symm_apply
  exact Nat.dvd_antisymm (ramificationIdx_above_dvd (r.under S) r)
    (ramificationIdx_above_dvd (r.under R) r)

end Ideal
