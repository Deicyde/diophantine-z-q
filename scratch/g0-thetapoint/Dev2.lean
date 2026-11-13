import Mathlib

/-! Development: a number field containing finitely many algebraic complex numbers. -/

structure NF where
  K : Type
  [fld : Field K]
  [nf : NumberField K]

attribute [instance] NF.fld NF.nf

theorem exists_nf_of_isAlgebraic {ι : Type} [Fintype ι] (α : ι → ℂ)
    (h : ∀ i, IsAlgebraic ℚ (α i)) :
    ∃ (L : NF) (emb : L.K →+* ℂ) (z : ι → L.K), ∀ i, emb (z i) = α i := by
  set E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range α)
  haveI hfd : FiniteDimensional ℚ E := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro x ⟨i, rfl⟩
    exact (h i).isIntegral
  haveI : NumberField E := ⟨⟩
  refine ⟨⟨E⟩, E.val.toRingHom, fun i => ⟨α i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩,
    fun i => rfl⟩
