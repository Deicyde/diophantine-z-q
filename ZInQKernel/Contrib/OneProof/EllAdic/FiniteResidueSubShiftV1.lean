import ZInQKernel.Contrib.OneProof.EllAdic.FiniteResidueSchemeTowerV2

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

namespace RC53.EllAdic

/-- The difference operator on a sequence of additive groups with surjective
transition maps is surjective. The lift is constructed coordinate by coordinate. -/
theorem sequenceSubShift_surjective {A : ℕ → Type*} [∀ n, AddGroup (A n)]
    (transition : (n : ℕ) → A (n + 1) →+ A n)
    (htrans : ∀ n, Function.Surjective (transition n)) :
    Function.Surjective (fun x : (n : ℕ) → A n => fun n => x n - transition n (x (n + 1))) := by
  intro y
  let step (n : ℕ) (a : A n) : A (n + 1) := Classical.choose (htrans n (-y n + a))
  let x : (n : ℕ) → A n := Nat.rec (motive := fun n => A n) 0 step
  have hstep (n : ℕ) : transition n (x (n + 1)) = -y n + x n :=
    Classical.choose_spec (htrans n (-y n + x n))
  refine ⟨x, funext fun n => ?_⟩
  change x n - transition n (x (n + 1)) = y n
  rw [hstep]
  simp only [sub_eq_add_neg, neg_add_rev, neg_neg, add_neg_cancel_left]

/-- On every topological space the actual finite residue reductions give
a surjective product difference map. In particular, this applies to the
underlying space of each object of the small pro-étale site. -/
theorem finiteResidueSectionsSubShift_surjective (p : ℕ) (U : Type*) [TopologicalSpace U] :
    Function.Surjective
      (fun x : (n : ℕ) → LocallyConstant U (ZMod (p ^ n)) =>
        fun n => x n - locallyConstantResidueReduction p (Nat.le_succ n) U (x (n + 1))) :=
  sequenceSubShift_surjective (A := fun n => LocallyConstant U (ZMod (p ^ n)))
    (fun n => locallyConstantResidueReduction p (Nat.le_succ n) U)
    (fun n => locallyConstantResidueReduction_surjective p (Nat.le_succ n) U)

end RC53.EllAdic
