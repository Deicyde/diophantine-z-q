import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightSeriesTraceCovariance
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinPrimeFiberMoves
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinCoprimeFiberMoves
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinAffineZero

/-!
# Prime-extension trace formulas for every weight at least three

Constructed integral principal-group motions compare genuine class-series
traces along complete fibres. Repeated primes give p^k/p² times a lower
generator; coprime primes give a produced lower combination divided by p²-1.
The nonprimitive prime-zero rows use actual inverse-power homogeneity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups Matrix ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllWeightSeriesTrace
open DivisionEisensteinLowerClosure

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The actual trace is equal on congruent labels related by a proved principal motion. -/
theorem traceK_motion (N M : ℕ) (hM3 : 3 ≤ M) (k : ℕ) (hk : 3 ≤ k)
    (a b c d : ℤ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N)
    (h0 : (((![a,b] ᵥ* γ.1) 0 : ℤ) : ZMod M) = c)
    (h1 : (((![a,b] ᵥ* γ.1) 1 : ℤ) : ZMod M) = d) :
    normalizedTraceK N M k (by omega) (seriesForm M hM3 k hk ![c,d]) =
      normalizedTraceK N M k (by omega) (seriesForm M hM3 k hk ![a,b]) := by
  have hv : ![(![a,b] ᵥ* γ.1) 0,(![a,b] ᵥ* γ.1) 1] = (![a,b] ᵥ* γ.1) := by
    ext i; fin_cases i <;> rfl
  have he := seriesForm_eq_of_congr M hM3 k hk _ _ c d h0 h1
  rw [hv] at he
  rw [← he]
  exact normalizedTraceK_series_SL N M hM3 k hk ![a,b] γ hγ

/-- Repeated-prime primitive rows reach every actual finite fibre point. -/
theorem repeated_point_traceK (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N) (hpN : p ∣ N)
    (k : ℕ) (hk : 3 ≤ k) (a b : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (R : Fin p × Fin p) :
    normalizedTraceK N (p*N) k (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (seriesForm (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk
        ![a+N*(R.1 : ℕ),b+N*(R.2 : ℕ)]) =
    normalizedTraceK N (p*N) k (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (seriesForm (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk ![a,b]) := by
  obtain ⟨γ,hγ,h0,h1⟩ := exists_Gamma_prime_fiber_move p N hpN a b (R.1 : ℕ) (R.2 : ℕ) hab
  exact traceK_motion N (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk
    a b _ _ γ hγ h0 h1

/-- The genuine repeated-prime primitive trace formula has factor p^k/p². -/
theorem repeated_primitive_traceK (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N) (hpN : p ∣ N)
    (k : ℕ) (hk : 3 ≤ k) (a b : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0) :
    normalizedTraceK N (p*N) k (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (seriesForm (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk ![a,b]) =
      ((p : ℂ)^k/(p : ℂ)^2) • seriesForm N h3 k hk ![a,b] := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let T := normalizedTraceK N (p*N) k (Nat.mul_pos hp (by omega))
  let F := seriesForm (p*N) (by nlinarith) k hk ![a,b]
  have hs : T (completeFiberK p N hp h3 k hk a b) = (p : ℂ)^2 • T F := by
    simp only [T,F,completeFiberK,map_sum,repeated_point_traceK p N h3 hpN k hk a b hab,
      Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
    simp only [pow_two,← Nat.cast_mul,Nat.cast_smul_eq_nsmul]
  have he : (p : ℂ)^2 • T F = (p : ℂ)^k • seriesForm N h3 k hk ![a,b] := by
    rw [← hs,normalizedTraceK_completeFiber]
  have hc : (p : ℂ)^2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hp.ne')
  have hh := congrArg (fun f : _root_.ModularForm (ΓP N) (k : ℤ) => ((p : ℂ)^2)⁻¹ • f) he
  simp only [smul_smul,inv_mul_cancel₀ hc,one_smul] at hh
  rw [hh]
  congr 1
  ring

/-- Coprime-prime nonzero fibre points have equal actual traces. -/
theorem coprime_point_traceK (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N) (hcop : Nat.Coprime p N)
    (k : ℕ) (hk : 3 ≤ k) (a b : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (R : Fin p × Fin p)
    (hR : ((a+N*(R.1 : ℕ) : ℤ) : ZMod p) ≠ 0 ∨ ((b+N*(R.2 : ℕ) : ℤ) : ZMod p) ≠ 0) :
    normalizedTraceK N (p*N) k (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (seriesForm (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk
        ![a+N*(R.1 : ℕ),b+N*(R.2 : ℕ)]) =
    normalizedTraceK N (p*N) k (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (seriesForm (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk ![a,b]) := by
  have ha : (a : ZMod N) = ((a+N*(R.1 : ℕ) : ℤ) : ZMod N) := by simp
  have hb : (b : ZMod N) = ((b+N*(R.2 : ℕ) : ℤ) : ZMod N) := by simp
  obtain ⟨γ,hγ,h0,h1⟩ := exists_Gamma_coprime_fiber_move p N hcop a b _ _ hab hR ha hb
  exact traceK_motion N (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk
    a b _ _ γ hγ h0 h1

/-- Produced coprime-prime trace formula, with no desired lower-membership input. -/
theorem coprime_primitive_traceK (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N) (hcop : Nat.Coprime p N)
    (k : ℕ) (hk : 3 ≤ k) (a b : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0) :
    ∃ c d : ℤ,
      normalizedTraceK N (p*N) k (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (seriesForm (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk ![a,b]) =
      ((p : ℂ)^2-1)⁻¹ •
        ((p : ℂ)^k • seriesForm N h3 k hk ![a,b] - seriesForm N h3 k hk ![c,d]) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨R,hR,hRu⟩ := exists_unique_affine_zero p N hcop a
  obtain ⟨S,hS,hSu⟩ := exists_unique_affine_zero p N hcop b
  obtain ⟨c,hc⟩ := hR
  obtain ⟨d,hd⟩ := hS
  let T := normalizedTraceK N (p*N) k (Nat.mul_pos hp (by omega))
  let F := seriesForm (p*N) (by nlinarith) k hk ![a,b]
  let E := seriesForm N h3 k hk ![c,d]
  let G := seriesForm N h3 k hk ![a,b]
  have hfun (Q : Fin p × Fin p) : T (seriesForm (p*N) (by nlinarith) k hk
      ![a+N*(Q.1 : ℕ),b+N*(Q.2 : ℕ)]) = T F + (if Q = (R,S) then E-T F else 0) := by
    by_cases hQ : Q = (R,S)
    · subst Q
      have he := restrictionK_generator_mul N p k h3 hp hk ![c,d]
      have hv : (fun i : Fin 2 => (p : ℤ)*(![c,d] i)) = ![(p : ℤ)*c,(p : ℤ)*d] := by
        ext i; fin_cases i <;> rfl
      rw [hv] at he
      simp only [hc,hd,↓reduceIte,T,E]
      rw [← he,normalizedTraceK_restriction]
      abel
    · have hn : ((a+N*(Q.1 : ℕ) : ℤ) : ZMod p) ≠ 0 ∨ ((b+N*(Q.2 : ℕ) : ℤ) : ZMod p) ≠ 0 := by
        by_contra hz
        push Not at hz
        have hr := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz.1
        have hs := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz.2
        exact hQ (Prod.ext (hRu Q.1 hr) (hSu Q.2 hs))
      simp only [hQ,↓reduceIte,add_zero]
      exact coprime_point_traceK p N h3 hcop k hk a b hab Q hn
  have hs : T (completeFiberK p N hp h3 k hk a b) = (p : ℂ)^2 • T F + (E-T F) := by
    rw [completeFiberK,map_sum]
    simp only [hfun,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_prod,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℂ,Nat.cast_mul,← pow_two]
    simp
  have he : ((p : ℂ)^2-1) • T F = (p : ℂ)^k • G-E := by
    apply _root_.ModularForm.ext
    intro τ
    have hh := congrArg (fun f : _root_.ModularForm (ΓP N) (k : ℤ) => f τ) hs
    rw [normalizedTraceK_completeFiber] at hh
    simp only [smul_apply,smul_eq_mul,add_apply,sub_apply,G] at hh ⊢
    linear_combination -hh
  have hp2 : (p : ℂ)^2-1 ≠ 0 := by
    have hr : (p : ℝ)^2-1 ≠ 0 := by
      have ht : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
      nlinarith
    exact_mod_cast hr
  have hh := congrArg (fun f : _root_.ModularForm (ΓP N) (k : ℤ) => ((p : ℂ)^2-1)⁻¹ • f) he
  simp only [smul_smul,inv_mul_cancel₀ hp2,one_smul] at hh
  exact ⟨c,d,hh⟩

/-- Arbitrary all-label generator closure in every prime extension and every k≥3. -/
theorem traceK_prime_generator_mem (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ℤ) :
    normalizedTraceK N (p*N) k (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (seriesForm (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk a) ∈ seriesSpanK N h3 k hk := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hv : ![a 0,a 1] = a := by ext i; fin_cases i <;> rfl
  by_cases hz : (a 0 : ZMod p) = 0 ∧ (a 1 : ZMod p) = 0
  · obtain ⟨c,hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a 0) p).mp hz.1
    obtain ⟨d,hd⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a 1) p).mp hz.2
    have he := restrictionK_generator_mul N p k h3 hp hk ![c,d]
    have hu : (fun i : Fin 2 => (p : ℤ)*(![c,d] i)) = ![(p : ℤ)*c,(p : ℤ)*d] := by
      ext i; fin_cases i <;> rfl
    rw [hu] at he
    rw [← hv,hc,hd,← he,normalizedTraceK_restriction]
    exact generator_mem_seriesSpanK N h3 k hk ![c,d]
  · have hab : (a 0 : ZMod p) ≠ 0 ∨ (a 1 : ZMod p) ≠ 0 := by tauto
    rw [← hv]
    rcases Nat.coprime_or_dvd_of_prime (Fact.out : p.Prime) N with hcop | hpN
    · obtain ⟨c,d,he⟩ := coprime_primitive_traceK p N h3 hcop k hk (a 0) (a 1) hab
      rw [he]
      apply Submodule.smul_mem
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (generator_mem_seriesSpanK N h3 k hk ![a 0,a 1]))
        (generator_mem_seriesSpanK N h3 k hk ![c,d])
    · rw [repeated_primitive_traceK p N h3 hpN k hk (a 0) (a 1) hab]
      exact Submodule.smul_mem _ _ (generator_mem_seriesSpanK N h3 k hk ![a 0,a 1])

theorem traceK_prime_span (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    {f : _root_.ModularForm (ΓP (p*N)) (k : ℤ)}
    (hf : f ∈ seriesSpanK (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk) :
    normalizedTraceK N (p*N) k (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) f ∈ seriesSpanK N h3 k hk := by
  have hle : seriesSpanK (p*N) (by have hp := (Fact.out : p.Prime).pos; nlinarith) k hk ≤
      (seriesSpanK N h3 k hk).comap (normalizedTraceK N (p*N) k (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))) := by
    apply Submodule.span_le.mpr
    rintro F ⟨a,rfl⟩
    exact traceK_prime_generator_mem p N h3 k hk a
  exact hle hf

end ZInQ.Contrib.HeckePrimeRationality.AllWeightSeriesTrace
