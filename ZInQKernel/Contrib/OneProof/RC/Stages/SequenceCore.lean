import Mathlib

/-! Appendix F, tex 8399–8405 and Appendix G, tex 10190–10191. Stage selection keeps
one witness and one precision offset throughout the recursion. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Stages

open Filter Topology

/-- The actual prime and its precision-dependent arithmetic data. -/
structure PrimeStage (At : ℕ → ℕ → Prop) (M : ℕ) where
  p : ℕ
  prime : Nat.Prime p
  arithmetic : At M p

/-- The sequence of actual stages, with its exclusion and precision conditions. -/
structure StageSequence (At : ℕ → ℕ → Prop) (cw : ℕ) (S : Finset ℕ) where
  stage : (i : ℕ) → PrimeStage At (cw + 1 + i)
  excluded : ∀ i, (stage i).p ∉ S
  distinct : Function.Injective (fun i => (stage i).p)

/-- Tex 8399–8405. Recursing with a growing finite exclusion set gives one sequence. -/
def stageSequence {At : ℕ → ℕ → Prop} (cw : ℕ) (S : Finset ℕ)
    (hex : ∀ M, cw < M → ∀ B : Finset ℕ, ∃ s : PrimeStage At M, s.p ∉ B) :
    StageSequence At cw S := by
  let st : (j : ℕ) → {a : PrimeStage At (cw + 1 + j) × Finset ℕ // a.1.p ∉ a.2} :=
    fun j => Nat.rec (motive := fun k =>
        {a : PrimeStage At (cw + 1 + k) × Finset ℕ // a.1.p ∉ a.2})
      (let h := hex (cw + 1) (by omega) S; ⟨(h.choose, S), h.choose_spec⟩)
      (fun k prev =>
        let B := insert prev.val.1.p prev.val.2
        let h := hex (cw + 1 + (k + 1)) (by omega) B
        ⟨(h.choose, B), h.choose_spec⟩) j
  have hs : Monotone (fun i => (st i).val.2) :=
    monotone_nat_of_le_succ (fun _ => Finset.subset_insert _ _)
  refine ⟨fun i => (st i).val.1, fun i hi => (st i).property (hs (Nat.zero_le i) hi), ?_⟩
  have hne : ∀ i j, i < j → (st i).val.1.p ≠ (st j).val.1.p := by
    intro i j hij he
    apply (st j).property
    rw [← he]
    exact hs (Nat.succ_le_of_lt hij) (Finset.mem_insert_self _ _)
  intro i j h
  rcases lt_trichotomy i j with hlt | he | hgt
  · exact (hne i j hlt h).elim
  · exact he
  · exact (hne j i hgt h.symm).elim

variable {At : ℕ → ℕ → Prop} {cw : ℕ} {S : Finset ℕ}

/-- The stage test in (3.7) and the support convention of (3.8). -/
def stageTest (q : StageSequence At cw S) (i : ℕ) (D : ℤ) : Prop :=
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  legendreSym (q.stage i).p D = 1

/-- The moving test always accepts the empty squareclass. -/
theorem stageTest_one (q : StageSequence At cw S) (i : ℕ) : stageTest q i 1 := by
  unfold stageTest
  simp

#print axioms stageSequence
#print axioms stageTest_one

end ZInQ.Manuscript.RC.Stages
