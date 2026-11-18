import ZInQKernel.Contrib.OneProof.RC.Adelic.Patch
import ZInQKernel.Contrib.OneProof.RC.ExplicitSplit.MatrixModel
import ZInQKernel.Contrib.OneProof.RC.DivisionJoin.Order
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Models

/-!
# The level order inside the explicit order
Tex 8464–8465, 8468–8469. The construction of the global order from the
local normal forms is on-the-spot (c).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Adelic

open Eichler

variable (ell : ℕ) [Fact ell.Prime] (h : ell % 4 = 3)

def splitChart (p : Prime) (hp : p.val ≠ ell) :
    Bp p.val (-1) (-(ell : ℚ)) ≃ₐ[ℚ_[p.val]] M2 ℚ_[p.val] :=
  (ExplicitSplit.explicit_split_profile Fact.out h p.val hp).choose

theorem splitChart_maximal (p : Prime) (hp : p.val ≠ ell) :
    splitChart ell h p hp '' ((explicitOrderAt ell h).completion p.val : Set _) =
      standardLevel p.val 0 :=
  (ExplicitSplit.explicit_split_profile Fact.out h p.val hp).choose_spec

def matrixCastAlg (p : Prime) : M2 ℤ_[p.val] →ₐ[ℤ_[p.val]] M2 ℚ_[p.val] where
  __ := matrixCast p.val
  commutes' r := by
    ext i j
    by_cases hij : i = j <;> simp [matrixCast, Matrix.algebraMap_matrix_apply, hij]

def standardOrder (p : Prime) (e : ℕ) : Subalgebra ℤ_[p.val] (M2 ℚ_[p.val]) :=
  (LocalWeights.eichler p.val e).map (matrixCastAlg p)

theorem coe_standardOrder (p : Prime) (e : ℕ) :
    (standardOrder p e : Set (M2 ℚ_[p.val])) = standardLevel p.val e := rfl

private theorem standard_smul (p : Prime) (e : ℕ) {x : M2 ℚ_[p.val]}
    (hx : x ∈ standardOrder p 0) :
    (p.val : ℤ_[p.val]) ^ e • x ∈ standardOrder p e := by
  rw [← SetLike.mem_coe, coe_standardOrder, standardLevel_zero] at hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(p.val : ℤ_[p.val]) ^ e • y, ?_, map_smul (matrixCastAlg p) _ _⟩
  exact dvd_mul_right _ _

private def splitChartInt (p : Prime) (hp : p.val ≠ ell) :
    Bp p.val (-1) (-(ell : ℚ)) →ₐ[ℤ_[p.val]] M2 ℚ_[p.val] where
  __ := (splitChart ell h p hp).toRingHom
  commutes' r := (splitChart ell h p hp).commutes (r : ℚ_[p.val])

/-- The prescribed local order at every prime. At primes away from the level the exponent
is zero, and at the discriminant prime we keep the maximal order. -/
def levelLocal (N : ℕ) (p : Prime) : Subalgebra ℤ_[p.val] (Bp p.val (-1) (-(ell : ℚ))) :=
  if hp : p.val ≠ ell then
    (standardOrder p (N.factorization p.val)).comap
      (splitChartInt ell h p hp)
  else (explicitOrderAt ell h).completion p.val

theorem levelLocal_mem_split (N : ℕ) (p : Prime) (hp : p.val ≠ ell)
    (x : Bp p.val (-1) (-(ell : ℚ))) :
    x ∈ levelLocal ell h N p ↔ splitChart ell h p hp x ∈ standardOrder p (N.factorization p.val) := by
  rw [levelLocal, dite_eq_left hp]
  rfl

theorem levelLocal_le (N : ℕ) (p : Prime) :
    levelLocal ell h N p ≤ (explicitOrderAt ell h).completion p.val := by
  intro x hx
  by_cases hp : p.val ≠ ell
  · have hx' := (levelLocal_mem_split ell h N p hp x).mp hx
    obtain ⟨y, hy, he⟩ := hx'
    have hm : splitChart ell h p hp x ∈ standardLevel p.val 0 := by
      rw [standardLevel_zero]
      exact ⟨y, he⟩
    rw [← splitChart_maximal ell h p hp] at hm
    obtain ⟨z, hz, hz'⟩ := hm
    exact (splitChart ell h p hp).injective hz' ▸ hz
  · rwa [levelLocal, dite_eq_right hp] at hx

private theorem levelLocal_smul (N : ℕ) (p : Prime) {x : Bp p.val (-1) (-(ell : ℚ))}
    (hx : x ∈ (explicitOrderAt ell h).completion p.val) :
    (p.val : ℤ_[p.val]) ^ N.factorization p.val • x ∈ levelLocal ell h N p := by
  by_cases hp : p.val ≠ ell
  · apply (levelLocal_mem_split ell h N p hp _).mpr
    let f := splitChartInt ell h p hp
    change f (_ • x) ∈ _
    rw [map_smul]
    apply standard_smul
    rw [← SetLike.mem_coe, coe_standardOrder, ← splitChart_maximal ell h p hp]
    exact Set.mem_image_of_mem _ hx
  · rw [levelLocal, dite_eq_right hp]
    exact ((explicitOrderAt ell h).completion p.val).toSubmodule.smul_mem _ hx

private theorem level_patch (N : ℕ) (hN : 0 < N) :
    let A := fun p => (levelLocal ell h N p).toSubmodule
    FullLattice (intersection A) ∧ ∀ p, localLattice p.val (intersection A) = A p := by
  let s := (finite_prime_dvd hN.ne').toFinset
  refine patch_inside (explicitOrderAt ell h).full _ s (fun p => N.factorization p.val) ?_ ?_ ?_
  · intro p hp
    apply Nat.factorization_eq_zero_of_not_dvd
    simpa [s] using hp
  · intro p
    rw [← Order.completion_toSubmodule]
    exact levelLocal_le ell h N p
  · intro p x hx
    rw [← Order.completion_toSubmodule] at hx
    exact levelLocal_smul ell h N p hx

/-- The global order with the prescribed level condition inside the explicit maximal order. -/
def levelOrder (N : ℕ) (hN : 0 < N) : Order (-1) (-(ell : ℚ)) where
  ring := (⨅ p : Prime, (levelLocal ell h N p).toSubring.comap (toLocal p.val))
  full := by
    convert (level_patch ell h N hN).1 using 1
    ext x
    exact Subring.mem_iInf

theorem levelOrder_completion (N : ℕ) (hN : 0 < N) (p : Prime) :
    (levelOrder ell h N hN).completion p.val = levelLocal ell h N p := by
  apply Subalgebra.toSubmodule_injective
  rw [Order.completion_toSubmodule]
  have he : (levelOrder ell h N hN).lattice =
      intersection (fun q => (levelLocal ell h N q).toSubmodule) := by
    ext x
    exact Subring.mem_iInf
  rw [he]
  exact (level_patch ell h N hN).2 p

theorem levelOrder_le (N : ℕ) (hN : 0 < N) :
    (levelOrder ell h N hN).ring ≤ (explicitOrderAt ell h).ring := by
  intro x hx
  change x ∈ (explicitOrderAt ell h).lattice
  apply (mem_iff_all_local (explicitOrderAt ell h).full x).mpr
  intro p
  rw [← Order.completion_toSubmodule]
  exact levelLocal_le ell h N p (Subring.mem_iInf.mp hx p)

/-- At a prime not dividing the level, the completed explicit order is unchanged. -/
theorem levelOrder_completion_away (N : ℕ) (hN : 0 < N) (p : Prime) (hpN : ¬ p.val ∣ N) :
    (levelOrder ell h N hN).completion p.val = (explicitOrderAt ell h).completion p.val := by
  rw [levelOrder_completion]
  apply le_antisymm (levelLocal_le ell h N p)
  intro x hx
  simpa only [Nat.factorization_eq_zero_of_not_dvd hpN, pow_zero, one_smul] using
    levelLocal_smul ell h N p hx

theorem levelOrder_isEichler (N : ℕ) (hN : 0 < N) (hcop : N.Coprime ell) :
    IsEichler ell N (levelOrder ell h N hN) := by
  refine ⟨Fact.out, hN, hcop, ?_, ?_⟩
  · intro p hp he
    let q : Prime := ⟨p, hp.out⟩
    rw [show (levelOrder ell h N hN).completion p = levelLocal ell h N q from
      levelOrder_completion ell h N hN q, levelLocal, dite_eq_right (not_not.mpr he)]
    exact DivisionJoin.ramified_maximal ell h p he
  · intro p hp he
    let q : Prime := ⟨p, hp.out⟩
    refine ⟨splitChart ell h q he, ?_⟩
    rw [show (levelOrder ell h N hN).completion p = levelLocal ell h N q from
      levelOrder_completion ell h N hN q, ← coe_standardOrder q]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (levelLocal_mem_split ell h N q he y).mp hy
    · intro hx
      let f := splitChart ell h q he
      have hx' : x ∈ standardOrder q (N.factorization q.val) := hx
      exact ⟨f.symm x, (levelLocal_mem_split ell h N q he _).mpr (by
        change f (f.symm x) ∈ standardOrder q (N.factorization q.val)
        rwa [AlgEquiv.apply_symm_apply]), f.apply_symm_apply x⟩

#print axioms splitChart_maximal
#print axioms coe_standardOrder
#print axioms standard_smul
#print axioms levelLocal_mem_split
#print axioms levelLocal_le
#print axioms levelLocal_smul
#print axioms level_patch
#print axioms levelOrder_completion
#print axioms levelOrder_le
#print axioms levelOrder_completion_away
#print axioms levelOrder_isEichler

end ZInQ.Manuscript.RC.Adelic
