/-
Plan steps 3.4–3.5 (effective Dirichlet): the residue identity
`res_K = L(1, χ) · ∏_{p ∣ 2q} (1 - χ(p)/p) (1 - ε_p/p)⁻¹`, obtained from the zeta factorization
by multiplying by `s - 1` and letting `s → 1⁺`.
-/
import ZInQKernel.Progressions.IdealCount
import Mathlib

namespace ZInQ.Progressions

open NumberField Filter Topology Module

/-- The residue of `ζ` at `1`, along real `s → 1⁺`. -/
theorem tendsto_sub_one_mul_riemannZeta_ofReal_nhdsGT :
    Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * riemannZeta s) (𝓝[>] 1) (𝓝 1) := by
  have : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun s hs ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact_mod_cast (ne_of_gt hs)
  exact riemannZeta_residue_one.comp this

/-- `s ↦ L(s, χ)` tends to `L(1, χ)` along real `s → 1⁺`, for `χ ≠ 1`. -/
theorem tendsto_LFunction_ofReal_nhdsGT {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    Tendsto (fun s : ℝ ↦ DirichletCharacter.LFunction χ s) (𝓝[>] 1)
      (𝓝 (DirichletCharacter.LFunction χ 1)) := by
  have h := ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
    Complex.continuous_ofReal).tendsto 1
  simp only [Function.comp_def, Complex.ofReal_one] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- The Euler-factor quotient `(1 - a p^(-s)) (1 - b p^(-s))⁻¹` is continuous at `s = 1` along
real `s`, when `|b| ≤ 1 < p`. -/
theorem tendsto_localFactor_ofReal {p : ℕ} (hp : 1 < p) (a b : ℂ) (hb : ‖b‖ ≤ 1) :
    Tendsto (fun s : ℝ ↦ (1 - a * (p : ℂ) ^ (-(s : ℂ))) * (1 - b * (p : ℂ) ^ (-(s : ℂ)))⁻¹)
      (𝓝[>] 1) (𝓝 ((1 - a * (p : ℂ) ^ (-(1 : ℂ))) * (1 - b * (p : ℂ) ^ (-(1 : ℂ)))⁻¹)) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hc : Continuous fun s : ℝ ↦ (p : ℂ) ^ (-(s : ℂ)) :=
    Continuous.const_cpow (Complex.continuous_ofReal.neg) (Or.inl hp0)
  have hlim : Tendsto (fun s : ℝ ↦ (p : ℂ) ^ (-(s : ℂ))) (𝓝[>] 1)
      (𝓝 ((p : ℂ) ^ (-(1 : ℂ)))) := by
    have := hc.tendsto 1
    simp only [Complex.ofReal_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hne : 1 - b * (p : ℂ) ^ (-(1 : ℂ)) ≠ 0 := by
    intro h
    have h1 : ‖b * (p : ℂ) ^ (-(1 : ℂ))‖ < 1 := by
      rw [norm_mul]
      have := IdealCount.norm_natCast_cpow_neg_lt_one hp (s := 1) (by simp)
      calc ‖b‖ * ‖(p : ℂ) ^ (-(1 : ℂ))‖ ≤ 1 * ‖(p : ℂ) ^ (-(1 : ℂ))‖ := by gcongr
        _ < 1 := by rwa [one_mul]
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at h1
    exact lt_irrefl _ h1
  exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim)).mul
    ((tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim)).inv₀ hne)

variable {K : Type*} [Field K] [NumberField K]

/-- **The residue identity** (plan step 3.5). Under the hypotheses of the zeta factorization
`dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod_of_legendreSym`, and `χ ≠ 1`,
`res_K = L(1, χ) · ∏_{p ∣ 2q} (1 - χ(p) p⁻¹) (1 - ε_p p⁻¹)⁻¹`. -/
theorem dedekindZeta_residue_eq_LFunction_one_mul_prod
    (h2 : finrank ℚ K = 2) {α : 𝓞 K} {d : ℤ} (hα : α ^ 2 = d) (hd : ¬ IsSquare d) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hdq : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → ¬ (p : ℤ) ∣ d)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q → χ p = legendreSym p d) :
    (dedekindZeta_residue K : ℂ) = DirichletCharacter.LFunction χ 1 *
      ∏ p ∈ (2 * q).primeFactors,
        (1 - χ p * (p : ℂ) ^ (-(1 : ℂ))) * (1 - localEps K p * (p : ℂ) ^ (-(1 : ℂ)))⁻¹ := by
  have hq : q ≠ 0 := NeZero.ne q
  -- the right-hand side, multiplied by `s - 1`, as a function of real `s`
  have hR : Tendsto (fun s : ℝ ↦ (((s : ℂ) - 1) * riemannZeta s) *
      DirichletCharacter.LFunction χ s * ∏ p ∈ (2 * q).primeFactors,
        (1 - χ p * (p : ℂ) ^ (-(s : ℂ))) * (1 - localEps K p * (p : ℂ) ^ (-(s : ℂ)))⁻¹)
      (𝓝[>] 1) (𝓝 (1 * DirichletCharacter.LFunction χ 1 * ∏ p ∈ (2 * q).primeFactors,
        (1 - χ p * (p : ℂ) ^ (-(1 : ℂ))) * (1 - localEps K p * (p : ℂ) ^ (-(1 : ℂ)))⁻¹)) := by
    refine (tendsto_sub_one_mul_riemannZeta_ofReal_nhdsGT.mul
      (tendsto_LFunction_ofReal_nhdsGT hχ1)).mul (tendsto_finsetProd _ fun p hp ↦ ?_)
    have hp' := Nat.prime_of_mem_primeFactors hp
    exact tendsto_localFactor_ofReal hp'.one_lt _ _ (IdealCount.norm_localEps_le_one h2 hp')
  have hL := tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have heq : (fun s : ℝ ↦ ((s : ℂ) - 1) * dedekindZeta K s) =ᶠ[𝓝[>] 1]
      (fun s : ℝ ↦ (((s : ℂ) - 1) * riemannZeta s) *
      DirichletCharacter.LFunction χ s * ∏ p ∈ (2 * q).primeFactors,
        (1 - χ p * (p : ℂ) ^ (-(s : ℂ))) * (1 - localEps K p * (p : ℂ) ^ (-(s : ℂ)))⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod_of_legendreSym h2 hα hd hq χ hdq hχ hs,
      DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hs)]
    ring
  have := tendsto_nhds_unique (hL.congr' heq) hR
  rw [this, one_mul]

end ZInQ.Progressions
