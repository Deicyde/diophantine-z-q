import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinCoprimePrimeTrace

/-!
# Arbitrary lower-level division-Eisenstein trace closure

The two actual prime-extension orbit reductions imply invariant series-span
descent by induction on the upper positive level. Applying that descent to the
restricted actual trace proves lower-span membership for arbitrary upper series
generators and their span. No trace-preservation or classification premise occurs.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators Matrix MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure

open EisensteinWeightTwo DivisionEisensteinLevelMaps

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- Actual lower trace closure for every prime extension, with both coprime
and repeated-prime possibilities proved rather than postulated. -/
theorem trace_seriesSpan_prime (p N : ℕ) [Fact p.Prime] (hN : 0 < N)
    {f : _root_.ModularForm (ΓP (p * N)) 2}
    (hf : f ∈ seriesSpan (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) f ∈ seriesSpan N hN := by
  rcases Nat.coprime_or_dvd_of_prime (Fact.out : p.Prime) N with hcop | hpN
  · exact trace_seriesSpan_coprime_prime p N hN hcop hf
  · exact trace_seriesSpan_repeated_prime p N hN hpN hf

/-- Invariant actual series-span descent for any single prime extension. -/
theorem invariant_series_descent_prime (p N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (f : _root_.ModularForm (ΓP (p * N)) 2)
    (hf : f ∈ seriesSpan (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN))
    (hinv : ∀ γ ∈ (ΓP N), ⇑f ∣[(2 : ℤ)] γ = ⇑f) :
    ∃ g : _root_.ModularForm (ΓP N) 2, g ∈ seriesSpan N hN ∧
      restriction N (p * N) (dvd_mul_left N p) g = f := by
  exact ⟨normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) f,
    trace_seriesSpan_prime p N hN hf,
    restriction_normalizedTrace_of_invariant hN (Nat.mul_pos (Fact.out : p.Prime).pos hN)
      (dvd_mul_left N p) f hinv⟩

/-- The lower-group invariant part of the genuine upper series span comes
from the lower series span at arbitrary positive divisible levels. -/
theorem invariant_series_descent_all (M : ℕ) :
    ∀ (N : ℕ) (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M)
      (f : _root_.ModularForm (ΓP M) 2), f ∈ seriesSpan M hM →
      (∀ γ ∈ (ΓP N), ⇑f ∣[(2 : ℤ)] γ = ⇑f) →
      ∃ g : _root_.ModularForm (ΓP N) 2, g ∈ seriesSpan N hN ∧ restriction N M hNM g = f := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro N hN hM hNM f hf hinv
    by_cases hEq : N = M
    · subst N
      exact ⟨f, hf, restriction_self M f⟩
    obtain ⟨t, ht⟩ := hNM
    have ht1 : t ≠ 1 := by
      intro h1
      rw [h1, mul_one] at ht
      exact hEq ht.symm
    obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd ht1
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨u, hu⟩ := hpt
    have hu0 : 0 < u := by
      by_contra hz
      have hz0 : u = 0 := Nat.eq_zero_of_not_pos hz
      rw [hu, hz0, mul_zero, mul_zero] at ht
      exact hM.ne' ht
    let K := N * u
    have hK : 0 < K := Nat.mul_pos hN hu0
    have he : M = p * K := by
      rw [ht, hu]
      dsimp [K]
      ring
    have hKM : K < M := by
      rw [he]
      have hp2 := hp.two_le
      nlinarith
    have hNK : N ∣ K := dvd_mul_right N u
    cases he
    have hinvK : ∀ γ ∈ (ΓP K), ⇑f ∣[(2 : ℤ)] γ = ⇑f :=
      fun γ hγ => hinv γ (principal_group_le hNK hγ)
    obtain ⟨gK, hgK, heK⟩ := invariant_series_descent_prime p K hK f hf hinvK
    have hcoef : (gK : ℍ → ℂ) = (f : ℍ → ℂ) := by
      funext τ
      have h := congrArg (fun F : _root_.ModularForm (ΓP (p * K)) 2 => F τ) heK
      exact h
    have hinvN : ∀ γ ∈ (ΓP N), ⇑gK ∣[(2 : ℤ)] γ = ⇑gK := by
      intro γ hγ
      rw [hcoef]
      exact hinv γ hγ
    obtain ⟨g, hg, heG⟩ := ih K hKM N hN hK hNK gK hgK hinvN
    refine ⟨g, hg, ?_⟩
    calc restriction N (p * K) (dvd_trans hNK (dvd_mul_left K p)) g =
        restriction K (p * K) (dvd_mul_left K p) (restriction N K hNK g) :=
          (restriction_trans hNK (dvd_mul_left K p) g).symm
      _ = f := by rw [heG, heK]

/-- The actual normalized trace of every upper series-span member lies in the
lower series span for arbitrary positive divisible levels. -/
theorem trace_seriesSpan_all {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M)
    {f : _root_.ModularForm (ΓP M) 2} (hf : f ∈ seriesSpan M hM) :
    normalizedTrace N M hM f ∈ seriesSpan N hN := by
  let T := normalizedTrace N M hM f
  have hUpper : restriction N M hNM T ∈ seriesSpan M hM :=
    restriction_trace_mem_upper_seriesSpan hM hNM hf
  have hInv : ∀ γ ∈ (ΓP N), ⇑(restriction N M hNM T) ∣[(2 : ℤ)] γ = ⇑(restriction N M hNM T) :=
    fun γ hγ => T.slash_action_eq' γ hγ
  obtain ⟨g, hg, he⟩ := invariant_series_descent_all M N hN hM hNM (restriction N M hNM T) hUpper hInv
  have hEq : g = T := restriction_injective N M hNM he
  rwa [hEq] at hg

/-- The arbitrary integer upper-generator lower trace closure lemma. -/
theorem arbitrary_generator_trace_lower_mem {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M)
    (a : Fin 2 → ℤ) :
    normalizedTrace N M hM (divisionEisensteinMF M hM a) ∈ seriesSpan N hN :=
  trace_seriesSpan_all hN hM hNM (generator_mem_seriesSpan M hM a)

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure
