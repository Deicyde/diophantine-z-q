module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Noether finiteness for invariant algebras -/

@[expose] public section

namespace RC.ModelInvariants

open Polynomial

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- For a finite action on a finite-type algebra over a Noetherian ring, the invariant algebra
is of finite type. The orbit-polynomial coefficients give an intermediate finite-type algebra
over which both the original algebra and its invariant subalgebra are finite modules. -/
theorem fixedPoints_finiteType [Finite G] [IsNoetherianRing R] [Algebra.FiniteType R S] :
    Algebra.FiniteType R (FixedPoints.subalgebra R S G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R S).out
  let orbitPoly := MulSemiringAction.charpoly G (B := S)
  let coefficients := s.biUnion fun x => (orbitPoly x).support.image (orbitPoly x).coeff
  let B := Algebra.adjoin R (coefficients : Set S)
  let A := FixedPoints.subalgebra R S G
  have hBA : B ≤ A := by
    apply Algebra.adjoin_le
    intro a ha
    obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
    exact fun g => MulSemiringAction.smul_coeff_charpoly x n g
  let incl := Subalgebra.inclusion hBA
  let : Algebra B A := incl.toRingHom.toAlgebra
  let : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq' incl.comp_algebraMap
  let : IsScalarTower B A S := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => rfl)
  let hB : Algebra.FiniteType R B := Algebra.FiniteType.adjoin_of_finite coefficients.finite_toSet
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have hgen (x : S) (hx : x ∈ s) : IsIntegral B x := by
    have hcoeff (n : ℕ) : (orbitPoly x).coeff n ∈ B := by
      by_cases hn : n ∈ (orbitPoly x).support
      · exact Algebra.subset_adjoin (Finset.mem_biUnion.mpr
          ⟨x, hx, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩)
      · rw [notMem_support_iff.mp hn]
        exact zero_mem B
    have hlifts : orbitPoly x ∈ Polynomial.lifts (algebraMap B S) :=
      (lifts_iff_coeff_lifts _).2 fun n => ⟨⟨_, hcoeff n⟩, rfl⟩
    obtain ⟨p, hp, _, hmonic⟩ :=
      lifts_and_natDegree_eq_and_monic hlifts (MulSemiringAction.monic_charpoly G x)
    exact ⟨p, hmonic, by rw [← eval_map, hp, MulSemiringAction.eval_charpoly]⟩
  let : Algebra.IsIntegral B S := by
    constructor
    intro x
    have hfull : Algebra.adjoin R (s : Set S) ≤ (integralClosure B S).restrictScalars R :=
      Algebra.adjoin_le fun y hy => hgen y hy
    exact hfull (show x ∈ Algebra.adjoin R (s : Set S) by rw [hs]; exact Algebra.mem_top)
  let : Algebra.FiniteType B S := Algebra.FiniteType.of_restrictScalars_finiteType R B S
  let : Module.Finite B S := Algebra.IsIntegral.finite
  let : Module.Finite B A :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom B A S).toLinearMap Subtype.val_injective
  exact hB.trans (inferInstance : Algebra.FiniteType B A)

#print axioms fixedPoints_finiteType

end RC.ModelInvariants
