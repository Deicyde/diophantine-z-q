import ZInQKernel.Contrib.OneProof.RC.Stages.AnalyticWitness
import ZInQKernel.Contrib.OneProof.RC.Stages.Sequence

/-! Install the enlarged fixed support and the actual stage fields together. -/

noncomputable section

open Filter ZInQ.Manuscript.RC.Wiring

namespace ZInQ.Manuscript.RC.Stages

/-- Install the support, genus partner, prepared test and stage fields. The
rest of the data, including the theta coefficients, is supplied by the caller. -/
def withPreparedStages {ℓ : ℕ} (W : WData ℓ) (S : Finset ℕ) (hstar : ℤ)
    {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ} (q : StageSequence At cw B) :
    WData ℓ :=
  withStages { W with S := S, hstar := hstar } q (positivePrepared S)

/-- The chosen positive squareclass filter and actual stage cut supply the
specification and the advance statement together. -/
theorem preDataSpec_preparedStages {ℓ : ℕ} (W : WData ℓ) (S : Finset ℕ) (hstar : ℤ)
    {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ} (q : StageSequence At cw B)
    (hS : ∀ p ∈ S, p.Prime) (hbase : S0 ℓ ⊆ S) :
    let V := withPreparedStages W S hstar q
    PreDataSpec V ∧ Tendsto V.Mθ (V.stages : Filter ℕ) atTop :=
  ⟨preDataSpec_withStages _ q hS hbase (positivePrepared_one hS),
    stages_advance_withStages _ q _⟩

#print axioms preDataSpec_preparedStages

end ZInQ.Manuscript.RC.Stages
