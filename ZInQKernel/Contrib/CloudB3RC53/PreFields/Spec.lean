import ZInQKernel.Contrib.OneProof.RC.Wiring.Leaves
import ZInQKernel.Contrib.OneProof.RC.Wiring.NonVacuity

/-!
# The definitional fields of RC0's `PreLeaves`: exactly what the data must satisfy

RC0's `PreLeaves W` (`RC/Wiring/Leaves.lean`) has five fields that concern only how the interface
data `W : WData ℓ` is built: `support : SupportSpec W`, `stages_nonprincipal`, `stages_index`,
`one_admissible`, `prepared_glue : PreparedGlue W`. The data are themselves a field of
`RCLeaves` (`data : ∀ ℓ, ℤ → WData ℓ`), and `RCData`/`WData` are abstract structures, so none of
the five can be proved for an arbitrary `W`: each is a requirement on the construction of `W`.

This file states each requirement in constructive form and PROVES that it gives the field:

| field | tex | requirement on the construction of `W` | lemma |
|---|---|---|---|
| `support` | 1790–1793 | `W.S` consists of primes and contains `S₀ ℓ = {2, 3} ∪ primes(ℓ)` (for `ℓ > 0`) | `supportSpec_of` |
| `stages_nonprincipal` | App G 10190–10191 | `W.stages` is a nonprincipal ultrafilter, e.g. `hyperfilter ℕ` | `stages_nonprincipal_of_hyperfilter` |
| `stages_index` | 2491–2500, (3.7); App F 8233, 8400–8401 | the `θ`-th stage has precision `≥ θ`; from any family of arbitrarily advanced stages by reindexing | `stages_index_reindex` |
| `one_admissible` | 2586; App F 8209–8212 | the stage support is "`D` in the filter containing one and `(D/ℓ₀) = 1`", so contains `D = 1` | `one_admissible_of` |
| `prepared_glue` | 2404–2410, 8408–8429 | the stage support is contained in the prepared filter (`admissible θ D → prepared D`), e.g. `admissible θ D := prepared D ∧ T θ D` | `preparedGlue_of_and` |

`PreFieldsSpec W` bundles the requirements; `preFields_of_spec` gives all five fields; the
requirements are jointly satisfiable together with RC0's `PreparedSpec` (`preFieldsSpec_example`).
All statements are PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PreFields

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring Filter

variable {ℓ : ℕ}

/-! ### `support` -/

/-- **`SupportSpec`** holds as soon as the support consists of primes and contains
`S₀ ℓ = {2, 3} ∪ primes(ℓ)` (tex 1790–1793: the primes of `2N` for `E_ℓ`, as RC0 fixes them). -/
theorem supportSpec_of (hℓ : 0 < ℓ) (W : WData ℓ) (hprime : ∀ p ∈ W.S, p.Prime)
    (h0 : S0 ℓ ⊆ W.S) : SupportSpec W := by
  refine ⟨hprime, h0 (by simp [S0]), h0 (by simp [S0]), fun p hp hpℓ => h0 ?_⟩
  simp only [S0, Finset.mem_insert, Nat.mem_primeFactors]
  exact Or.inr (Or.inr ⟨hp, hpℓ, hℓ.ne'⟩)

/-! ### `stages_nonprincipal` -/

/-- **The stages are nonprincipal** when `W.stages = hyperfilter ℕ`. -/
theorem stages_nonprincipal_of_hyperfilter (W : WData ℓ) (h : W.stages = hyperfilter ℕ) :
    (W.stages : Filter ℕ) ≤ cofinite := by
  rw [h]; exact hyperfilter_le_cofinite

/-! ### `stages_index` -/

/-- **Reindexing the stages** (tex 2491–2500: (3.7) supplies arbitrarily advanced stages): for a
family of stages with precisions `prec` that are unbounded (`∀ M, ∃ θ, M ≤ prec θ`), the choice
`σ θ` of a stage of precision `≥ θ` gives a reindexed family with precision `prec (σ θ) ≥ θ`. RC0's
data must use such an indexing (with the coefficients and the stage support reindexed by the
same `σ`). -/
theorem stages_index_reindex (prec : ℕ → ℕ) (hunb : ∀ M : ℕ, ∃ θ, M ≤ prec θ) :
    ∃ σ : ℕ → ℕ, ∀ θ : ℕ, θ ≤ prec (σ θ) := by
  choose σ hσ using hunb
  exact ⟨σ, hσ⟩

/-! ### `one_admissible` and `prepared_glue` -/

/-- **`D = 1` is admissible at every stage** when the stage support is
`admissible θ D ↔ prepared D ∧ T θ D` with `prepared 1` (the filter contains one) and `T θ 1`
(`(1/ℓ₀) = 1`). -/
theorem one_admissible_of (W : WData ℓ) (T : ℕ → ℤ → Prop)
    (hadm : ∀ θ D, W.admissible θ D ↔ W.prepared D ∧ T θ D) (h1 : W.prepared 1)
    (hT : ∀ θ, T θ 1) : ∀ θ : ℕ, W.admissible θ 1 :=
  fun θ => (hadm θ 1).mpr ⟨h1, hT θ⟩

/-- **`PreparedGlue`** holds when the stage support refines the prepared filter. -/
theorem preparedGlue_of_and (W : WData ℓ) (T : ℕ → ℤ → Prop)
    (hadm : ∀ θ D, W.admissible θ D ↔ W.prepared D ∧ T θ D) : PreparedGlue W :=
  fun θ D h => ((hadm θ D).mp h).1

/-! ### The requirements together -/

/-- **The requirements on the construction of `W`** for the five definitional fields of
`PreLeaves` (see the module docstring). -/
structure PreFieldsSpec (W : WData ℓ) : Prop where
  /-- the support consists of primes -/
  support_prime : ∀ p ∈ W.S, p.Prime
  /-- the support contains `S₀ ℓ = {2, 3} ∪ primes(ℓ)` -/
  support_base : S0 ℓ ⊆ W.S
  /-- the ultrafilter on the stages is the hyperfilter (nonprincipal) -/
  stages_hyper : W.stages = hyperfilter ℕ
  /-- the `θ`-th stage has precision `≥ θ` (after reindexing, `stages_index_reindex`) -/
  stages_index : ∀ θ : ℕ, θ ≤ W.Mθ θ
  /-- the stage support is the prepared filter intersected with a stage condition `T`
  (`(D/ℓ₀) = 1` at the stage's theta prime), which holds at `D = 1` -/
  admissible_split : ∃ T : ℕ → ℤ → Prop, (∀ θ D, W.admissible θ D ↔ W.prepared D ∧ T θ D) ∧
    ∀ θ, T θ 1
  /-- the prepared filter contains one -/
  prepared_one : W.prepared 1

/-- **The five definitional fields of `PreLeaves`** from the requirements (PROVED). -/
theorem preFields_of_spec (hℓ : 0 < ℓ) {W : WData ℓ} (h : PreFieldsSpec W) :
    SupportSpec W ∧ (W.stages : Filter ℕ) ≤ cofinite ∧ (∀ θ : ℕ, θ ≤ W.Mθ θ) ∧
      (∀ θ : ℕ, W.admissible θ 1) ∧ PreparedGlue W := by
  obtain ⟨T, hadm, hT⟩ := h.admissible_split
  exact ⟨supportSpec_of hℓ W h.support_prime h.support_base,
    stages_nonprincipal_of_hyperfilter W h.stages_hyper, h.stages_index,
    one_admissible_of W T hadm h.prepared_one hT, preparedGlue_of_and W T hadm⟩

/-- The requirements are stable under RC0's substitution of `h_*` (and of `δ_o`): they do not
mention these fields. -/
theorem preFieldsSpec_withHstar {W : WData ℓ} (h : PreFieldsSpec W) (hs : ℤ) :
    PreFieldsSpec (W.withHstar hs) :=
  ⟨h.support_prime, h.support_base, h.stages_hyper, h.stages_index, h.admissible_split,
    h.prepared_one⟩

/-- **Joint satisfiability with RC0's `PreparedSpec`** (PROVED): data with support `S₀ ℓ`, the
hyperfilter, precision `θ + 3`, prepared filter `{h > 0 squarefree, h ≡ 1 mod 8, prime to S₀}`
and stage support `{1}` meet every requirement and `PreparedSpec`. -/
theorem preFieldsSpec_example (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ W : WData ℓ, PreFieldsSpec W ∧ PreparedSpec W := by
  let W : WData ℓ :=
    { toyW ℓ with
      S := S0 ℓ
      prepared := fun h => 0 < h ∧ Squarefree h ∧ h % 8 = 1 ∧ ∀ p ∈ S0 ℓ, ¬ (p : ℤ) ∣ h
      admissible := fun _ D =>
        (0 < D ∧ Squarefree D ∧ D % 8 = 1 ∧ ∀ p ∈ S0 ℓ, ¬ (p : ℤ) ∣ D) ∧ D = 1 }
  have hprime : ∀ p ∈ S0 ℓ, p.Prime := by
    intro p hp
    simp only [S0, Finset.mem_insert, Nat.mem_primeFactors] at hp
    rcases hp with rfl | rfl | ⟨hp, -⟩
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact hp
  have hone : (0 : ℤ) < 1 ∧ Squarefree (1 : ℤ) ∧ (1 : ℤ) % 8 = 1 ∧ ∀ p ∈ S0 ℓ, ¬ (p : ℤ) ∣ 1 := by
    refine ⟨one_pos, squarefree_one, rfl, fun p hp h => ?_⟩
    have := Int.eq_one_of_dvd_one (by positivity) h
    exact (hprime p hp).one_lt.ne' (by exact_mod_cast this)
  exact ⟨W, ⟨hprime, subset_rfl, rfl, fun θ => by simp [W, toyW],
    ⟨fun _ D => D = 1, fun θ D => Iff.rfl, fun _ => rfl⟩, hone⟩, fun h hh => hh⟩

end ZInQ.Contrib.CloudB3RC53.PreFields
