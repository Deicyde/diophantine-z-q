import ZInQKernel.Contrib.OneProof.RC.EvenJoin.DistinctCuspColumns

/-! The coefficient field in the Galois print and that of the actual
newform columns are the same embedded number field. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open TauCeti

/-- The extra generator in the all-index presentation is the zero
constant coefficient of the cusp form. -/
theorem NormalizedCuspSource.attachment_field (s : NormalizedCuspSource) :
    IntermediateField.adjoin ℚ (Set.range s.coeff) = s.field := by
  letI : NeZero s.level := ⟨s.level_ne⟩
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨n, rfl⟩
    exact s.coeff_mem_field n
  · change CoefficientField s.newform ≤ _
    rw [CoefficientField_le_iff]
    intro n
    exact IntermediateField.subset_adjoin ℚ _ ⟨(n : ℕ), rfl⟩

end ZInQ.Manuscript.RC.EvenJoin
