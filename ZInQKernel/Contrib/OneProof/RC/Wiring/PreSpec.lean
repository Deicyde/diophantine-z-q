import ZInQKernel.Contrib.OneProof.RC.Wiring.Genus

/-!
# Theorem 5.3, Lane RC0 round 3: the definitional fields of the data as one specification

Five fields of `PreLeaves` concern only how the interface data `W` are built: the support
(`SupportSpec`), the nonprincipal ultrafilter on the stages, the indexing `M_θ ≥ θ`, `D = 1` in the
stage support, and the stage support inside the prepared filter (`PreparedGlue`). `PreDataSpec W`
states them as requirements on the construction of `W`; its body is identical, field by field, to
batch 3's `PreFieldsSpec` (PreFields), and `preFields_of_dataSpec` (PROVED) gives the five fields.
(Batch 3's file imports this lane's `Leaves.lean`, so the specification is restated here rather than
imported; the two structures are interchangeable field by field.)
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Filter

/-- **The requirements on the construction of the data** (definitions):
* `support_prime`, `support_base`: the support consists of primes and contains
  `S₀ ℓ = {2, 3} ∪ primes(ℓ)` (tex 1790–1793);
* `stages_hyper`: the ultrafilter on the stages is the hyperfilter, a nonprincipal ultrafilter (App G
  10190–10191);
* `stages_index`: the `θ`-th stage has precision `≥ θ` ((3.7) supplies arbitrarily advanced stages,
  tex 2489–2493, App F 8233, 8400–8401; any such family can be reindexed, batch 3's
  `stages_index_reindex`);
* `admissible_split`: the stage support is the prepared filter cut by a stage condition holding at
  `D = 1` (`(D/ℓ₀) = 1`; tex 2404–2410, 2586, App F 8209–8212, 8408–8429);
* `prepared_one`: the prepared filter contains one (tex 2404–2410). -/
structure PreDataSpec {ℓ : ℕ} (W : WData ℓ) : Prop where
  support_prime : ∀ p ∈ W.S, p.Prime
  support_base : S0 ℓ ⊆ W.S
  stages_hyper : W.stages = hyperfilter ℕ
  stages_index : ∀ θ : ℕ, θ ≤ W.Mθ θ
  admissible_split : ∃ T : ℕ → ℤ → Prop, (∀ θ D, W.admissible θ D ↔ W.prepared D ∧ T θ D) ∧
    ∀ θ, T θ 1
  prepared_one : W.prepared 1

/-- **The five definitional fields from the specification** (PROVED; as batch 3's
`preFields_of_spec`). -/
theorem preFields_of_dataSpec {ℓ : ℕ} (hℓ : 0 < ℓ) {W : WData ℓ} (h : PreDataSpec W) :
    SupportSpec W ∧ (W.stages : Filter ℕ) ≤ cofinite ∧ (∀ θ : ℕ, θ ≤ W.Mθ θ) ∧
      (∀ θ : ℕ, W.admissible θ 1) ∧ PreparedGlue W := by
  obtain ⟨T, hadm, hT⟩ := h.admissible_split
  refine ⟨⟨h.support_prime, h.support_base (by simp [S0]), h.support_base (by simp [S0]),
    fun p hp hpℓ => h.support_base ?_⟩, by rw [h.stages_hyper]; exact hyperfilter_le_cofinite,
    h.stages_index, fun θ => (hadm θ 1).mpr ⟨h.prepared_one, hT θ⟩,
    fun θ D hD => ((hadm θ D).mp hD).1⟩
  simp only [S0, Finset.mem_insert, Nat.mem_primeFactors]
  exact Or.inr (Or.inr ⟨hp, hpℓ, hℓ.ne'⟩)

end ZInQ.Manuscript.RC.Wiring
