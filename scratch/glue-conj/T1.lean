import Mathlib

open NumberField
open scoped Pointwise

namespace GlueConj

abbrev GQ := Field.absoluteGaloisGroup ℚ
abbrev Qbar := AlgebraicClosure ℚ

instance : IsGalois ℚ (AlgebraicClosure ℚ) := {}

/-- Integral elements over `ℤ` lie in every valuation subring. -/
theorem mem_of_isIntegral (w : ValuationSubring Qbar) {y : Qbar} (hy : IsIntegral ℤ y) : y ∈ w := by
  have h1 : IsIntegral w y := IsIntegral.tower_top (A := w) hy
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  rw [← ha]; exact a.2

theorem val_le_one_of_isIntegral (w : ValuationSubring Qbar) {y : Qbar} (hy : IsIntegral ℤ y) :
    w.valuation y ≤ 1 := (w.valuation_le_one_iff y).mpr (mem_of_isIntegral w hy)

/-- **Center lemma.** Two valuation subrings of `ℚ̄` over a prime `p` with the same center on the
algebraic integers are comparable (hence equal, by symmetry). -/
theorem le_of_center (w₁ w₂ : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime)
    (hw₁ : w₁.valuation (p : Qbar) < 1)
    (hc : ∀ y : Qbar, IsIntegral ℤ y → (w₁.valuation y < 1 ↔ w₂.valuation y < 1)) :
    w₁ ≤ w₂ := by
  intro x hx
  let K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {x}
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ) x)
  haveI : NumberField K := ⟨⟩
  let ι : 𝓞 K →+* Qbar := (algebraMap K Qbar).comp (algebraMap (𝓞 K) K)
  have hint : ∀ r : 𝓞 K, IsIntegral ℤ (ι r) := fun r =>
    (RingOfIntegers.isIntegral_coe r).map (IsScalarTower.toAlgHom ℤ K Qbar)
  let f : 𝓞 K →+* w₁ :=
    { toFun := fun r => ⟨ι r, mem_of_isIntegral w₁ (hint r)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  let I : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal w₁).comap f
  have hI : ∀ r, r ∈ I ↔ w₁.valuation (ι r) < 1 := fun r =>
    (w₁.valuation_lt_one_iff (f r))
  have hpI : (p : 𝓞 K) ∈ I := by rw [hI]; simpa [ι] using hw₁
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨I, Ideal.comap_isPrime _ _, fun h => hp0 (by rw [h] at hpI; simpa using hpI)⟩
  let x' : K := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := K) x'
  have hd : ¬ w₁.valuation (ι d) < 1 := fun h' => d.2 ((hI d).mpr h')
  have hd2 : w₂.valuation (ι d) = 1 :=
    le_antisymm (val_le_one_of_isIntegral w₂ (hint d))
      (not_lt.mp fun h' => hd ((hc _ (hint d)).mpr h'))
  have hn2 := val_le_one_of_isIntegral w₂ (hint n)
  rw [← w₂.valuation_le_one_iff]
  rcases h with h | h
  · have h' : x * ι d = ι n := by
      have := congrArg (algebraMap K Qbar) h
      simpa [ι] using this
    have := congrArg w₂.valuation h'
    rw [map_mul, hd2, mul_one] at this
    rw [this]; exact hn2
  · have h' : x * ι n = ι d := by
      have := congrArg (algebraMap K Qbar) h
      simpa [ι] using this
    by_contra hx2
    push_neg at hx2
    have e2 := congrArg w₂.valuation h'
    rw [map_mul, hd2] at e2
    have hn2' : w₂.valuation (ι n) < 1 := by
      rcases lt_or_eq_of_le hn2 with h3 | h3
      · exact h3
      · rw [h3, mul_one] at e2; exact absurd e2 (ne_of_gt hx2)
    have hn1 := (hc _ (hint n)).mpr hn2'
    have e1 := congrArg w₁.valuation h'
    rw [map_mul] at e1
    have hx1 : w₁.valuation x ≤ 1 := (w₁.valuation_le_one_iff x).mpr hx
    have : w₁.valuation x * w₁.valuation (ι n) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hx1) hn1
    rw [e1] at this
    exact hd (by simpa using this)

end GlueConj
