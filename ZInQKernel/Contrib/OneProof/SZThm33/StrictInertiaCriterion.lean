import ZInQKernel.Contrib.OneProof.SZThm33.StrictWeilForm

noncomputable section

open ZInQ.Contrib.AbVarBC

namespace SZRaynaud

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (w : ValuationSubring Ω) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The two-factor inertia condition over the strict henselization descends
to the original representation through the same algebraic closure. -/
theorem levelTwo_of_strictInertia
    (h : ∀ σ : Ω ≃ₐ[(GapSHPair.inertiaField (K := K) w)] Ω, PkgI2.IsInertia w σ → ∀ τ : Ω ≃ₐ[(GapSHPair.inertiaField (K := K) w)] Ω, PkgI2.IsInertia w τ →
      ∀ x : VΩ (A.baseChange (GapSHPair.inertiaField (K := K) w)) Ω ℓ,
        galVΩ (A.baseChange (GapSHPair.inertiaField (K := K) w)) ℓ τ (galVΩ (A.baseChange (GapSHPair.inertiaField (K := K) w)) ℓ σ x - x) =
          galVΩ (A.baseChange (GapSHPair.inertiaField (K := K) w)) ℓ σ x - x) :
    ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
      ∀ x : VΩ A Ω ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x := by
  intro σ hσ τ hτ x
  let σ' := overInertiaField w σ hσ
  let τ' := overInertiaField w τ hτ
  have hσ' : PkgI2.IsInertia w σ' := ReductSplit.isInertia_restrict (GapSHPair.inertiaField (K := K) w) w σ σ' (fun _ => rfl) hσ
  have hτ' : PkgI2.IsInertia w τ' := ReductSplit.isInertia_restrict (GapSHPair.inertiaField (K := K) w) w τ τ' (fun _ => rfl) hτ
  let e := intermediateRationalTateEquiv A (GapSHPair.inertiaField (K := K) w) ℓ
  obtain ⟨y, rfl⟩ := e.surjective x
  have hxy := congrArg e (h σ' hσ' τ' hτ' y)
  simpa only [e, intermediateRationalTateEquiv_action, map_sub, σ', τ',
    overInertiaField_restrictScalars] using hxy

end SZRaynaud
