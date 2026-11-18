import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightSeriesPrimeTrace

/-!
# Arbitrary-level trace closure for genuine class series in every k≥3

Actual prime formulas and upper-series preservation yield invariant descent
by strong induction on the upper level. Lower membership is produced before
restriction injectivity is used to identify the actual normalized trace.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllWeightSeriesTrace
open DivisionEisensteinLevelMaps (principal_group_le)

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

theorem invariant_seriesK_prime (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (f : _root_.ModularForm (ΓP (p*N)) (k : ℤ))
    (hf : f ∈ seriesSpanK (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk)
    (hinv : ∀ γ ∈ (ΓP N), ⇑f ∣[(k : ℤ)] γ = ⇑f) :
    ∃ g : _root_.ModularForm (ΓP N) (k : ℤ), g ∈ seriesSpanK N h3 k hk ∧
      restrictionK N (p*N) k (dvd_mul_left N p) g = f := by
  exact ⟨normalizedTraceK N (p*N) k (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) f,
    traceK_prime_span p N h3 k hk hf,
    restrictionK_trace_invariant (by omega) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (dvd_mul_left N p) f hinv⟩

/-- All-level invariant descent within the independently series-defined span. -/
theorem invariant_seriesK_descent (M : ℕ) :
    ∀ (N : ℕ) (hN3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M) (k : ℕ) (hk : 3 ≤ k)
      (f : _root_.ModularForm (ΓP M) (k : ℤ)),
      f ∈ seriesSpanK M (hN3.trans (Nat.le_of_dvd hM hNM)) k hk →
      (∀ γ ∈ (ΓP N), ⇑f ∣[(k : ℤ)] γ = ⇑f) →
      ∃ g : _root_.ModularForm (ΓP N) (k : ℤ), g ∈ seriesSpanK N hN3 k hk ∧ restrictionK N M k hNM g = f := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro N hN3 hM hNM k hk f hf hinv
    have hN : 0 < N := by omega
    by_cases hEq : N = M
    · subst N
      exact ⟨f,hf,restrictionK_self M k f⟩
    obtain ⟨t,ht⟩ := hNM
    have ht1 : t ≠ 1 := by
      intro h1
      rw [h1,mul_one] at ht
      exact hEq ht.symm
    obtain ⟨p,hp,hpt⟩ := Nat.exists_prime_and_dvd ht1
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨u,hu⟩ := hpt
    have hu0 : 0 < u := by
      by_contra hz
      have hz0 : u = 0 := Nat.eq_zero_of_not_pos hz
      rw [hu,hz0,mul_zero,mul_zero] at ht
      exact hM.ne' ht
    let K := N*u
    have hK : 0 < K := Nat.mul_pos hN hu0
    have he : M = p*K := by rw [ht,hu]; dsimp [K]; ring
    have hKM : K < M := by rw [he]; have hp2 := hp.two_le; nlinarith
    have hNK : N ∣ K := dvd_mul_right N u
    have hK3 : 3 ≤ K := hN3.trans (Nat.le_of_dvd hK hNK)
    cases he
    have hinvK : ∀ γ ∈ (ΓP K), ⇑f ∣[(k : ℤ)] γ = ⇑f :=
      fun γ hγ => hinv γ (principal_group_le hNK hγ)
    obtain ⟨gK,hgK,heK⟩ := invariant_seriesK_prime p K hK3 k hk f hf hinvK
    have hcoef : (gK : ℍ → ℂ) = (f : ℍ → ℂ) := by
      funext τ
      exact congrArg (fun F : _root_.ModularForm (ΓP (p*K)) (k : ℤ) => F τ) heK
    have hinvN : ∀ γ ∈ (ΓP N), ⇑gK ∣[(k : ℤ)] γ = ⇑gK := by
      intro γ hγ
      rw [hcoef]
      exact hinv γ hγ
    obtain ⟨g,hg,heG⟩ := ih K hKM N hN3 hK hNK k hk gK hgK hinvN
    refine ⟨g,hg,?_⟩
    calc restrictionK N (p*K) k (dvd_trans hNK (dvd_mul_left K p)) g =
        restrictionK K (p*K) k (dvd_mul_left K p) (restrictionK N K k hNK g) :=
          (restrictionK_trans hNK (dvd_mul_left K p) g).symm
      _ = f := by rw [heG,heK]

/-- Every actual upper series-span member has lower trace membership for all
positive divisible levels and all weights k≥3. -/
theorem traceK_seriesSpan_all {N M : ℕ} (hN3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M)
    (k : ℕ) (hk : 3 ≤ k) {f : _root_.ModularForm (ΓP M) (k : ℤ)}
    (hf : f ∈ seriesSpanK M (hN3.trans (Nat.le_of_dvd hM hNM)) k hk) :
    normalizedTraceK N M k hM f ∈ seriesSpanK N hN3 k hk := by
  let T := normalizedTraceK N M k hM f
  have hM3 : 3 ≤ M := hN3.trans (Nat.le_of_dvd hM hNM)
  have hUpper : restrictionK N M k hNM T ∈ seriesSpanK M hM3 k hk :=
    restrictionK_trace_mem_upper hN3 hM3 hk hNM hf
  have hInv : ∀ γ ∈ (ΓP N), ⇑(restrictionK N M k hNM T) ∣[(k : ℤ)] γ = ⇑(restrictionK N M k hNM T) :=
    fun γ hγ => T.slash_action_eq' γ hγ
  obtain ⟨g,hg,he⟩ := invariant_seriesK_descent M N hN3 hM hNM k hk (restrictionK N M k hNM T) hUpper hInv
  have hEq : g = T := restrictionK_injective N M k hNM he
  rwa [hEq] at hg

/-- The arbitrary integer all-label principal-series generator trace endpoint. -/
theorem traceK_generator_all {N M : ℕ} (hN3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M)
    (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ℤ) :
    normalizedTraceK N M k hM (seriesForm M (hN3.trans (Nat.le_of_dvd hM hNM)) k hk a) ∈
      seriesSpanK N hN3 k hk :=
  traceK_seriesSpan_all hN3 hM hNM k hk (generator_mem_seriesSpanK M _ k hk a)

end ZInQ.Contrib.HeckePrimeRationality.AllWeightSeriesTrace
