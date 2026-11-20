import Mathlib

/-! Geometric points mapping to the same point of an affine invariant-ring
quotient belong to one orbit. -/

open Polynomial

/-- Over an infinite ground field, two field-valued algebra homomorphisms
agreeing on the invariant ring differ by a group element. -/
theorem AlgHom.exists_comp_eq_of_eq_on_invariant
    {k A K G : Type*} [Field k] [Infinite k] [CommRing A] [Field K] [Algebra k A] [Algebra k K]
    [Group G] [_root_.Finite G] (ρ : G →* (A →ₐ[k] A)) (f g : A →ₐ[k] K)
    (heq : ∀ a : A, (∀ h : G, ρ h a = a) → f a = g a) :
    ∃ h : G, f = g.comp (ρ h) := by
  classical
  let _ := Fintype.ofFinite G
  by_contra! h
  let L (s : G) : A →ₗ[k] K := f.toLinearMap - (g.comp (ρ s)).toLinearMap
  have hL (s : G) : LinearMap.ker (L s) ≠ ⊤ := by
    intro hker
    have hz : L s = 0 := LinearMap.ker_eq_top.mp hker
    apply h s
    ext a
    exact sub_eq_zero.mp (congrArg (fun l : A →ₗ[k] K => l a) hz)
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun s => LinearMap.ker (L s)) hL
  have hne (s : G) : f a ≠ g (ρ s a) := by
    intro hs
    apply ha s
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr hs)
  let P : A[X] := ∏ s : G, (X - C (ρ s a))
  have hP (s : G) : P.map (ρ s).toRingHom = P := by
    simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    refine (Finset.prod_congr rfl fun t _ => ?_).trans
      (Equiv.prod_comp (Equiv.mulLeft s) (fun t : G => X - C (ρ t a)))
    change X - C (ρ s (ρ t a)) = X - C (ρ (s * t) a)
    rw [map_mul]
    rfl
  have hc (n : ℕ) (s : G) : ρ s (P.coeff n) = P.coeff n :=
    (Polynomial.coeff_map (ρ s).toRingHom n).symm.trans
      (congrArg (fun p : A[X] => p.coeff n) (hP s))
  have hmap : P.map f.toRingHom = P.map g.toRingHom := by
    ext n
    exact (Polynomial.coeff_map _ _).trans
      ((heq (P.coeff n) (hc n)).trans (Polynomial.coeff_map _ _).symm)
  have hzero : (P.map f.toRingHom).eval (f a) = 0 := by
    simp only [P, Polynomial.map_prod, Polynomial.eval_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ (1 : G)) (by simp)
  have hnonzero : (P.map g.toRingHom).eval (f a) ≠ 0 := by
    simp only [P, Polynomial.map_prod, Polynomial.eval_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_ne_zero_iff.mpr fun s _ => sub_ne_zero.mpr (hne s)
  exact hnonzero (hmap ▸ hzero)

#print axioms AlgHom.exists_comp_eq_of_eq_on_invariant
