import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# The inertia ring is unramified over the base, and so is every intermediate ring below it

Let `S` be Galois over `R` with finite group `G`, `P` a prime of `S` over `p`, and `T` an inertia
ring of `P` (`S` is Galois over `T` with group the inertia group `I` of `P`).

* `ramificationIdx_under_inertiaRing_eq_one`: the prime of `T` below `P` has ramification index
  `1` over `R`. The order of the inertia group equals the ramification index (separable residue
  fields); over `T`, the inertia group of `P` inside `I` is all of `I`, so
  `e(P | P ∩ T) = |I| = e(P | p)`; ramification indices multiply in `R ⊆ T ⊆ S`.
* `ramificationIdx_under_eq_one_of_le_inertiaRing`: the same for any intermediate ring `T'` with
  `T` flat over `T'`.
* `isUnramifiedAt_under_inertiaRing`: with essentially finite type and separable residue fields,
  the prime of `T` below `P` is unramified over `R`.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open Ideal MulAction

variable {R T S : Type*} [CommRing R] [CommRing T] [CommRing S] [IsDomain R] [IsDomain T]
  [IsDomain S] [Algebra R T] [Algebra T S] [Algebra R S] [IsScalarTower R T S]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  [Module.Finite R S] [Module.Flat R S] [Module.Finite T S] [Module.Flat T S]
  [FaithfulSMul T S]

theorem ramificationIdx_under_inertiaRing_eq_one (p : Ideal R) (P : Ideal S) [p.IsPrime]
    [P.IsPrime] [P.LiesOver p] [IsGaloisGroup (P.inertia G) T S]
    [Algebra.HasSeparableResidueFieldsAt R S p]
    [Algebra.HasSeparableResidueFieldsAt T S (P.under T)] :
    (P.under T).ramificationIdx R = 1 := by
  set H : Subgroup G := P.inertia G with hH
  have h1 : Nat.card (P.inertia G) = ramificationIdxIn p S :=
    card_inertia_eq_ramificationIdxIn (G := G) p P
  have h2 : Nat.card (P.inertia H) = ramificationIdxIn (P.under T) S :=
    card_inertia_eq_ramificationIdxIn (G := H) (P.under T) P
  have htop : P.inertia H = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro h x
    exact h.2 x
  rw [htop, Subgroup.card_top] at h2
  have h3 : ramificationIdxIn (P.under T) S = ramificationIdxIn p S := by
    rw [← h2, ← h1]
  rw [ramificationIdxIn_eq_ramificationIdx (P.under T) P H,
    ramificationIdxIn_eq_ramificationIdx p P G] at h3
  have htower := ramificationIdx_tower (R := R) (P.under T) P
  have hne : P.ramificationIdx T ≠ 0 := by
    rw [← ramificationIdxIn_eq_ramificationIdx (P.under T) P H]
    exact ramificationIdxIn_ne_zero H
  rw [← h3] at htower
  exact (mul_eq_right₀ hne).1 htower.symm

/-- Every intermediate ring below the inertia ring is unramified over the base. -/
theorem ramificationIdx_under_eq_one_of_le_inertiaRing {T' : Type*} [CommRing T'] [Algebra R T']
    [Algebra T' T] [IsScalarTower R T' T] [Module.Flat T' T]
    (p : Ideal R) (P : Ideal S) [p.IsPrime] [P.IsPrime] [P.LiesOver p]
    [IsGaloisGroup (P.inertia G) T S]
    [Algebra.HasSeparableResidueFieldsAt R S p]
    [Algebra.HasSeparableResidueFieldsAt T S (P.under T)] :
    ((P.under T).under T').ramificationIdx R = 1 := by
  have h := ramificationIdx_under_inertiaRing_eq_one (T := T) (G := G) p P
  have htower := ramificationIdx_tower (R := R) ((P.under T).under T') (P.under T)
  rw [h] at htower
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

/-- **The prime of the inertia ring below `P` is unramified over `R`.** -/
theorem isUnramifiedAt_under_inertiaRing (p : Ideal R) (P : Ideal S) [p.IsPrime]
    [P.IsPrime] [P.LiesOver p] [IsGaloisGroup (P.inertia G) T S]
    [Algebra.HasSeparableResidueFieldsAt R S p]
    [Algebra.HasSeparableResidueFieldsAt T S (P.under T)]
    [Algebra.EssFiniteType R T]
    [Algebra.HasSeparableResidueFieldsAt R T ((P.under T).under R)] :
    Algebra.IsUnramifiedAt R (P.under T) :=
  (Ideal.ramificationIdx_eq_one_iff).1 (ramificationIdx_under_inertiaRing_eq_one (G := G) p P)

end InertiaPointDescent
