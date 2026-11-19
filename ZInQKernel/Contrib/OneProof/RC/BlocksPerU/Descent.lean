import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Constituents

/-! Once the normalized coefficient columns are in the chosen field,
complex spanning descends algebraically. No continuity of the comparison
embedding and no extra theorem on coefficient fields is needed for this step. -/

noncomputable section

namespace ZInQ.Manuscript.RC.BlocksPerU

open scoped Classical BigOperators

private theorem span_descends {K I : Type} [Field K] [Fintype I]
    (κ : K →+* ℂ) (v : I → ℕ → K) (a : ℕ → K)
    (ha : (fun n => κ (a n)) ∈ Submodule.span ℂ (Set.range fun i n => κ (v i n))) :
    a ∈ Submodule.span K (Set.range v) := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp ha
  let : Algebra K ℂ := κ.toAlgebra
  have hinj : Function.Injective (Algebra.linearMap K ℂ) := κ.injective
  obtain ⟨r, hr⟩ := (Algebra.linearMap K ℂ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  have hleft (k : K) : r (κ k) = k := DFunLike.congr_fun hr k
  apply (Submodule.mem_span_range_iff_exists_fun K).mpr
  refine ⟨fun i => r (c i), ?_⟩
  funext n
  have h := congrArg (fun b : ℕ → ℂ => r (b n)) hc
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, hleft] at h ⊢
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (c i)]
  change r (c i) * v i n = r (v i n • c i)
  rw [map_smul, smul_eq_mul, mul_comm]

open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {I J K L : Type} [Fintype I] [Field K] [AddCommGroup L]
    {ε : L →+ ZMod 2} {T : TypeData L ε} {N : ℕ}

/-- The characterwise spanning statement need only be given over the
complex numbers, with the columns themselves already realized over `K`. -/
def SpansOverComplex (X : Inventory I J K T N) (κ : K →+* ℂ) : Prop :=
  ∀ (m : ℕ) (hm : m ∣ N) (χ : (ZMod N)ˣ →* Kˣ) (a : ℕ → K),
    a 0 = 0 → HasWeightTwoExpansion κ hm χ a →
    (fun n => κ (a n)) ∈ Submodule.span ℂ {c |
      ∃ i, X.level i ∣ m ∧ X.χ (X.origin i) = χ ∧ (fun n => κ (X.expansion i n)) = c}

theorem spansAt_of_complex (X : Inventory I J K T N) (κ : K →+* ℂ)
    (h : SpansOverComplex X κ) : SpansAt X κ := by
  classical
  intro m hm χ a ha hf
  let S := {i : I // X.level i ∣ m ∧ X.χ (X.origin i) = χ}
  let v : S → ℕ → K := fun i => X.expansion i.val
  have hset : Set.range v =
      {c | ∃ i, X.level i ∣ m ∧ X.χ (X.origin i) = χ ∧ X.expansion i = c} := by
    ext c
    exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.property.1, i.property.2, hi⟩,
      fun ⟨i, hi, hχ, he⟩ => ⟨⟨i, hi, hχ⟩, he⟩⟩
  rw [← hset]
  apply span_descends κ
  have hset' : Set.range (fun (i : S) n => κ (v i n)) =
      {c | ∃ i, X.level i ∣ m ∧ X.χ (X.origin i) = χ ∧ (fun n => κ (X.expansion i n)) = c} := by
    ext c
    exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.property.1, i.property.2, hi⟩,
      fun ⟨i, hi, hχ, he⟩ => ⟨⟨i, hi, hχ⟩, he⟩⟩
  rw [hset']
  exact h m hm χ a ha hf

#print axioms span_descends
#print axioms spansAt_of_complex

end ZInQ.Manuscript.RC.BlocksPerU
