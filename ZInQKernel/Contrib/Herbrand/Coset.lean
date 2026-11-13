import ZInQKernel.Contrib.Herbrand.LowerIndex

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described at
https://www.apache.org/licenses/LICENSE-2.0 .
Authors: The Tau Ceti contributors

CHANGED / PORTED FILE: the concrete coset polynomial argument from
TauCeti/NumberTheory/LocalField/LowerIndex.lean and the two small orbit-polynomial
lemmas from TauCeti/RingTheory/Invariant/Basic.lean, at
 a6027b1d24fcb935c53bd5b50d11b40991cda418,
are generalized here to the actual finite DVR tower and its supplied restriction.
Monogenicity and valuation normalization are proved, not assumed as new leaves.
-/

namespace ZInQ.Contrib.Herbrand

open IsLocalRing Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section OrbitPolynomial

variable {G B : Type*} [Group G] [Fintype G] [CommRing B] [IsDomain B] [MulSemiringAction G B]

/-- Distinct translates are roots, so their product polynomial divides every polynomial
vanishing on the orbit. -/
theorem orbit_charpoly_dvd {b : B} (hb : Function.Injective fun g : G => g • b) {f : B[X]}
    (hf : ∀ g : G, f.eval (g • b) = 0) : MulSemiringAction.charpoly G b ∣ f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact dvd_zero _
  convert (Multiset.prod_X_sub_C_dvd_iff_le_roots hf0 _).mpr
    ((Multiset.le_iff_subset (Finset.univ.nodup.map hb)).mpr fun a ha => ?_)
  · simp [MulSemiringAction.charpoly_eq]
  obtain ⟨g, _, rfl⟩ := Multiset.mem_map.mp ha
  exact (mem_roots hf0).mpr (hf g)

end OrbitPolynomial

section Evaluate

variable {G H B : Type*} [Monoid G] [Group H] [Fintype H] [CommRing B]
  [MulSemiringAction G B] [MulSemiringAction H B]

theorem eval_smul_orbit_charpoly (σ : G) (b : B) :
    (σ • MulSemiringAction.charpoly H b).eval b = ∏ τ : H, (b - σ • τ • b) := by
  simp [MulSemiringAction.charpoly_eq, Finset.smul_prod', eval_prod, smul_sub, smul_C]

end Evaluate

section AddValuation

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

theorem addVal_prod {ι : Type*} (s : Finset ι) (f : ι → B) :
    IsDiscreteValuationRing.addVal B (∏ i ∈ s, f i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal B (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons, IsDiscreteValuationRing.addVal_mul, ih]

end AddValuation

section Tower

variable {A C B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [PerfectField (ResidueField A)]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C]
  [Module.Finite A C] [Module.IsTorsionFree A C]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra C B] [IsScalarTower A C B] [Module.Finite C B] [Module.IsTorsionFree C B]
  [IsGalois (FractionRing C) (FractionRing B)]
  (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
  (hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c))

include r hr in
omit [IsDomain A] [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
  [Module.Finite A C] [Module.IsTorsionFree A C] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsScalarTower A C B] in
private theorem displacement_dvd_eval_orbit_charpoly {y : C}
    (hy : Algebra.adjoin A {y} = ⊤) (σ : B ≃ₐ[A] B) (x : B) :
    σ (algebraMap C B y) - algebraMap C B y ∣
      (σ • MulSemiringAction.charpoly (B ≃ₐ[C] B) x).eval x := by
  have : IsGaloisGroup (B ≃ₐ[C] B) C B := ringAut_isGaloisGroup C B
  set P := MulSemiringAction.charpoly (B ≃ₐ[C] B) x
  rw [← sub_zero ((σ • P).eval x), ← MulSemiringAction.eval_charpoly (B ≃ₐ[C] B) x,
    ← eval_sub, eval_eq_sum_range]
  refine Finset.dvd_sum fun n _ => Dvd.dvd.mul_right ?_ _
  obtain ⟨w, hw⟩ := Algebra.IsInvariant.isInvariant (A := C) (G := B ≃ₐ[C] B) (P.coeff n)
    (MulSemiringAction.smul_coeff_charpoly x n)
  rw [coeff_sub, coeff_smul, ← hw]
  change σ (algebraMap C B y) - algebraMap C B y ∣
    σ (algebraMap C B w) - algebraMap C B w
  rw [← hr σ y, ← hr σ w, ← map_sub, ← map_sub]
  exact map_dvd (algebraMap C B) (displacement_dvd_of_adjoin_eq_top hy (r σ) w)

omit [IsDomain A] [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
  [IsDiscreteValuationRing C] [Module.Finite A C] [Module.IsTorsionFree A C]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [IsGalois (FractionRing C) (FractionRing B)] in
private theorem eval_orbit_charpoly_dvd_displacement {x : B}
    (hx : Algebra.adjoin A {x} = ⊤) (y : C) (σ : B ≃ₐ[A] B) :
    (σ • MulSemiringAction.charpoly (B ≃ₐ[C] B) x).eval x ∣
      algebraMap C B y - σ (algebraMap C B y) := by
  obtain ⟨q, hq⟩ : ∃ q : A[X], aeval x q = algebraMap C B y := by
    rw [← AlgHom.mem_range, ← Algebra.adjoin_singleton_eq_range_aeval, hx]
    exact Algebra.mem_top
  set g := q.map (algebraMap A B) - Polynomial.C (algebraMap C B y)
  have hg : ∀ τ : B ≃ₐ[C] B, g.eval (τ • x) = 0 := fun τ => by
    rw [eval_sub, eval_C, eval_map_algebraMap, Polynomial.aeval_smul, hq,
      smul_algebraMap, sub_self]
  have hinj : Function.Injective fun τ : B ≃ₐ[C] B => τ • x :=
    generator_orbit_injective (R := A) hx
  obtain ⟨h, hh⟩ := orbit_charpoly_dvd hinj hg
  have hσg : σ • g = q.map (algebraMap A B) - Polynomial.C (σ (algebraMap C B y)) := by
    have hmap : (MulSemiringAction.toRingHom (B ≃ₐ[A] B) B σ).comp
        (algebraMap A B) = algebraMap A B :=
      RingHom.ext fun a => σ.commutes a
    rw [smul_sub, smul_C, smul_eq_map, Polynomial.map_map, hmap]
    rfl
  refine ⟨(σ • h).eval x, ?_⟩
  rw [← eval_mul, ← smul_mul', ← hh, hσg, eval_sub, eval_C, eval_map_algebraMap, hq]

include hr in
/-- Serre's exact lower-index quotient identity in the actual DVR tower.
It is proved by two divisibilities of concrete orbit-polynomial values, not assumed
as a filtration compatibility premise. -/
theorem ramificationIndex_mul_lowerIndex_restriction (σ : B ≃ₐ[A] B) :
    (ramificationIndex C B : ℕ∞) * lowerIndex A C (r σ) =
      ∑ τ : B ≃ₐ[C] B, lowerIndex A B (σ * τ.restrictScalars A) := by
  obtain ⟨x, hx⟩ := exists_dvr_adjoin_eq_top (A := A) (B := B)
  obtain ⟨y, hy⟩ := exists_dvr_adjoin_eq_top (A := A) (B := C)
  have key : IsDiscreteValuationRing.addVal B
      (σ (algebraMap C B y) - algebraMap C B y) =
      IsDiscreteValuationRing.addVal B
        ((σ • MulSemiringAction.charpoly (B ≃ₐ[C] B) x).eval x) :=
    (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr <| associated_of_dvd_dvd
      (displacement_dvd_eval_orbit_charpoly r hr hy σ x)
      (dvd_sub_comm.mp (eval_orbit_charpoly_dvd_displacement (C := C) hx y σ))
  have hlhs : (ramificationIndex C B : ℕ∞) * lowerIndex A C (r σ) =
      IsDiscreteValuationRing.addVal B (σ (algebraMap C B y) - algebraMap C B y) := by
    rw [lowerIndex_eq_addVal_of_adjoin_eq_top A C hy, ← nsmul_eq_mul,
      ← addVal_algebraMap C B, map_sub, hr]
  have hrhs : (∑ τ : B ≃ₐ[C] B, lowerIndex A B (σ * τ.restrictScalars A)) =
      IsDiscreteValuationRing.addVal B
        ((σ • MulSemiringAction.charpoly (B ≃ₐ[C] B) x).eval x) := by
    rw [eval_smul_orbit_charpoly, addVal_prod]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [lowerIndex_eq_addVal_of_adjoin_eq_top A B hx, AlgEquiv.mul_apply]
    change IsDiscreteValuationRing.addVal B (σ (τ x) - x) =
      IsDiscreteValuationRing.addVal B (x - σ (τ x))
    exact (IsDiscreteValuationRing.addVal B).map_sub_swap _ _
  exact hlhs.trans (key.trans hrhs.symm)

end Tower

end ZInQ.Contrib.Herbrand

#print axioms ZInQ.Contrib.Herbrand.ramificationIndex_mul_lowerIndex_restriction
