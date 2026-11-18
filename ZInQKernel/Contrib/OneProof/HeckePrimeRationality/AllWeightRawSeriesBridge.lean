import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightSeriesTraceClosure

/-!
# Raw class-series normalization bridge

The unscaled actual inverse-power congruence sum is realized by dividing the
genuine principal Eisenstein form by N^k. Its generated span is exactly the
same series span because the positive-level scalar is proved nonzero.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllWeightSeriesTrace

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- Actual modular form for the unscaled congruence-grid sum. -/
def rawClassForm (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ℤ) :
    _root_.ModularForm (ΓP N) (k : ℤ) := ((N : ℂ)^k)⁻¹ • seriesForm N h3 k hk a

theorem rawClassForm_apply (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a : Fin 2 → ℤ) (τ : ℍ) :
    rawClassForm N h3 k hk a τ = ∑' q : ℤ × ℤ,
      EisensteinSeries.eisSummand (k : ℤ) ![a 0+N*q.1,a 1+N*q.2] τ := by
  rw [rawClassForm,smul_apply,smul_eq_mul,seriesForm_apply,seriesValue]
  have hc : (N : ℂ)^k ≠ 0 := pow_ne_zero k (Nat.cast_ne_zero.mpr (by omega : N ≠ 0))
  exact inv_mul_cancel_left₀ hc _

theorem rawClassForm_mem (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ℤ) :
    rawClassForm N h3 k hk a ∈ seriesSpanK N h3 k hk :=
  Submodule.smul_mem _ _ (generator_mem_seriesSpanK N h3 k hk a)

/-- Exact same-span identity; no mixed-correlation statement is assumed. -/
theorem rawClassForm_span_eq (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) :
    Submodule.span ℂ (Set.range (rawClassForm N h3 k hk)) = seriesSpanK N h3 k hk := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨a,rfl⟩
    exact rawClassForm_mem N h3 k hk a
  · apply Submodule.span_le.mpr
    rintro f ⟨a,rfl⟩
    have hc : (N : ℂ)^k ≠ 0 := pow_ne_zero k (Nat.cast_ne_zero.mpr (by omega : N ≠ 0))
    have he : seriesForm N h3 k hk a = (N : ℂ)^k • rawClassForm N h3 k hk a := by
      rw [rawClassForm,smul_smul,mul_inv_cancel₀ hc,one_smul]
    rw [he]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨a,rfl⟩

/-- The raw k=3 API for later independently proved mixed-correlation bindings. -/
theorem raw_weight_three_bundle (N : ℕ) (h3 : 3 ≤ N) (a b : ℤ) :
    ∃ f : _root_.ModularForm (ΓP N) (3 : ℤ), f ∈ seriesSpanK N h3 3 (by omega) ∧
      ∀ τ : ℍ, f τ = ∑' q : ℤ × ℤ, EisensteinSeries.eisSummand (3 : ℤ) ![a+N*q.1,b+N*q.2] τ :=
  ⟨rawClassForm N h3 3 (by omega) ![a,b],rawClassForm_mem N h3 3 (by omega) ![a,b],
    rawClassForm_apply N h3 3 (by omega) ![a,b]⟩

end ZInQ.Contrib.HeckePrimeRationality.AllWeightSeriesTrace
