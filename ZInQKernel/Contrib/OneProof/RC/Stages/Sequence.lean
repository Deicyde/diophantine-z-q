import ZInQKernel.Contrib.OneProof.RC.Wiring.PreSpec
import ZInQKernel.Contrib.OneProof.RC.Stages.SequenceCore

/-! Appendix F, tex 8399–8405 and Appendix G, tex 10190–10191. Stage selection keeps
one witness and one precision offset throughout the recursion. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Stages

open Filter Topology ZInQ.Manuscript.RC.Wiring

variable {At : ℕ → ℕ → Prop} {cw : ℕ} {S : Finset ℕ}

/-- Set the moving fields in the Appendix F/G construction. The input carries the
fixed support and the remaining fields, including the theta coefficients and odd minimum.
The prime exclusion set may also contain primes outside the fixed support. -/
def withStages {ℓ : ℕ} (W : WData ℓ) (q : StageSequence At cw S)
    (prepared : ℤ → Prop) : WData ℓ :=
  { W with
    prepared := prepared
    stages := hyperfilter ℕ
    Mθ := fun i => cw + 1 + i
    admissible := fun i D => prepared D ∧ stageTest q i D }

/-- This construction supplies PreDataSpec, including the cut by the Legendre symbol. -/
theorem preDataSpec_withStages {ℓ : ℕ} (W : WData ℓ) (q : StageSequence At cw S)
    {prepared : ℤ → Prop} (hp : ∀ p ∈ W.S, p.Prime) (hbase : S0 ℓ ⊆ W.S)
    (hone : prepared 1) : PreDataSpec (withStages W q prepared) where
  support_prime := hp
  support_base := hbase
  stages_hyper := rfl
  stages_index := fun _ => by dsimp [withStages]; omega
  admissible_split := ⟨stageTest q, fun _ _ => Iff.rfl, stageTest_one q⟩
  prepared_one := hone

/-- The constructed precision tends to infinity along the actual ultrafilter
(the skeleton's stages_advance field). -/
theorem stages_advance_withStages {ℓ : ℕ} (W : WData ℓ) (q : StageSequence At cw S)
    (prepared : ℤ → Prop) :
    Tendsto (withStages W q prepared).Mθ
      ((withStages W q prepared).stages : Filter ℕ) atTop := by
  refine tendsto_atTop.mpr fun n => ?_
  have hn : ∀ᶠ i : ℕ in cofinite, n ≤ i := by
    rw [Nat.cofinite_eq_atTop]
    exact eventually_ge_atTop n
  change ∀ᶠ i : ℕ in (hyperfilter ℕ : Filter ℕ), n ≤ cw + 1 + i
  filter_upwards [hyperfilter_le_cofinite hn] with i hi
  omega

#print axioms withStages
#print axioms preDataSpec_withStages
#print axioms stages_advance_withStages

end ZInQ.Manuscript.RC.Stages
