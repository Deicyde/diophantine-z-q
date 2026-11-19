import ZInQKernel.Contrib.OneProof.RC.RelativeAction.Unipotents
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Stage

/-! Apply the concrete word calculation to the supplied stage grid, without
constructing or changing any of its class weights. -/

noncomputable section

namespace ZInQ.Manuscript.RC.RelativeAction

open OldStageLaw ThetaCoeff

variable {O : Type} [CommRing O] {M : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)}
  {E : Lift S} {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)] {h : ℚ} {N : ℕ}

/-- Every integral translation has scalar one on the stage table and reference.
The only stage input in this action is integral extracted support. -/
theorem stageGrid_paired_upper (G : StageGrid E a h) (ι : O →+* ℂ)
    (ξ : (ZMod N)ˣ →* ℂˣ) (k : ℤ) :
    PairedActionAt ξ (stageGridWeight E ι a h) [.trans k] :=
  paired_upper ξ _ k (stageGrid_twist_eq G ι k)

/-- On any additive subgroup preserving the stage table, one integral depth
check at the actual old level works for all its integer multiples. -/
theorem stageGrid_paired_lower (ι : O →+* ℂ) (ξ : (ZMod N)ˣ →* ℂˣ)
    (H : AddSubgroup (Grid a)) (hfour : 4 ∣ N)
    (htrans : ∀ u ∈ H, ∀ r, stageGridWeight E ι a h (r + u) = stageGridWeight E ι a h r)
    (hdepth : ∀ s, (∀ u ∈ H, pairing u s = 1) → ∃ j : ℤ, (N : ℝ) * energy s = j)
    (k : ℤ) (hk : (N : ℤ) ∣ k) :
    PairedActionAt ξ (stageGridWeight E ι a h) (lowerWord k) := by
  apply paired_lower ξ _ H k hk hfour htrans
  intro s hs
  obtain ⟨j, hj⟩ := hdepth s hs
  obtain ⟨b, rfl⟩ := hk
  refine ⟨-b * j, ?_⟩
  push_cast
  linear_combination -((b : ℤ) : ℝ) * hj

#print axioms stageGrid_paired_upper
#print axioms stageGrid_paired_lower

end ZInQ.Manuscript.RC.RelativeAction
