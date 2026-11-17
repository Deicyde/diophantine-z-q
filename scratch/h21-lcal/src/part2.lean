
/-! # h21-lcal, part 2: the order of `L(C_d, s)` at `s = 1` is not `1` for `d ≡ 1, 3 (mod 8)` -/

namespace ZInQ.Contrib.H21Lcal

open ZInQ.Literature

/-- An analytic function symmetric about `1` (`G(2 − s) = G(s)` near `1`) does not have a simple zero at `1`. -/
theorem analyticOrderAt_ne_one_of_symm {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 1)
    (hsym : ∀ᶠ s in nhds (1 : ℂ), G (2 - s) = G s) : analyticOrderAt G 1 ≠ 1 := by
  intro h
  obtain ⟨g, hg, hg1, hfg⟩ :=
    (hG.analyticOrderAt_eq_natCast (n := 1)).mp (by rw [h]; rfl)
  have hcont : Continuous (fun s : ℂ => 2 - s) := continuous_const.sub continuous_id
  have ht : Tendsto (fun s : ℂ => 2 - s) (nhds 1) (nhds 1) := by
    have := hcont.tendsto 1
    norm_num at this
    exact this
  have hfg2 := ht.eventually hfg
  have hk : ∀ᶠ s in nhds (1 : ℂ), (s - 1) * (g s + g (2 - s)) = 0 := by
    filter_upwards [hfg, hfg2, hsym] with s h1 h2 h3
    simp only [pow_one, smul_eq_mul] at h1 h2
    rw [h1, h2] at h3
    linear_combination -h3
  have hkc : ContinuousAt (fun s => g s + g (2 - s)) 1 :=
    hg.continuousAt.add (ContinuousAt.comp_of_eq hg.continuousAt hcont.continuousAt (by norm_num))
  have hk0 : (fun s => g s + g (2 - s)) =ᶠ[nhdsWithin 1 {1}ᶜ] fun _ => (0 : ℂ) := by
    filter_upwards [nhdsWithin_le_nhds hk, self_mem_nhdsWithin] with s hs hs1
    exact (mul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr hs1)
  have hlim1 := hkc.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
  have hlim2 : Tendsto (fun s => g s + g (2 - s)) (nhdsWithin 1 {1}ᶜ) (nhds 0) :=
    tendsto_const_nhds.congr' hk0.symm
  have h0 := tendsto_nhds_unique hlim1 hlim2
  norm_num at h0
  apply hg1
  linear_combination h0

/-- **The order of `L(C_d, s)` at `s = 1` is not `1`** for squarefree `d ≡ 1, 3 (mod 8)` (root number `+1`):
from `functionalEquationPlus_proof`. -/
theorem analyticOrderAt_ne_one {d : ℕ} (hcl : d % 8 = 1 ∨ d % 8 = 3) (hsq : Squarefree d) {F : ℂ → ℂ}
    (hF : IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F) : analyticOrderAt F 1 ≠ 1 := by
  have hd0 : d ≠ 0 := hsq.ne_zero
  set N : ℕ := 32 * d ^ 2
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 32 * d ^ 2 ≠ 0)
  have : NeZero (N : ℂ) := ⟨hN⟩
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have : NeZero (2 * Real.pi : ℂ) := ⟨h2pi⟩
  set P : ℂ → ℂ := fun s => (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s
  set U : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 2}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hU1 : U ∈ nhds (1 : ℂ) := hUo.mem_nhds (by norm_num [U])
  have hPd : DifferentiableOn ℂ P U := by
    intro s hs
    have hG : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s fun m hm => by
      have : s.re = -(m : ℝ) := by rw [hm]; simp
      have h0 : (0 : ℝ) < s.re := hs.1
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact ((((differentiable_const_cpow_of_neZero (N : ℂ)).comp (differentiable_id.div_const 2)) s).mul
      (((differentiable_const_cpow_of_neZero _).comp differentiable_id.neg) s) |>.mul hG).differentiableWithinAt
  have hP : AnalyticAt ℂ P 1 := hPd.analyticAt hU1
  have hP1 : P 1 ≠ 0 := by
    simp only [P, Complex.Gamma_one, mul_one]
    exact mul_ne_zero ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hN)
      ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr h2pi)
  have hFa : AnalyticAt ℂ F 1 := hF.1.analyticAt 1
  have hΛ : AnalyticAt ℂ (P * F) 1 := hP.mul hFa
  have hsym : ∀ᶠ s in nhds (1 : ℂ), (P * F) (2 - s) = (P * F) s := by
    filter_upwards [hU1] with s hs
    have := functionalEquationPlus_proof d hcl hsq F hF s hs.1 hs.2
    simpa [completedL, P, N] using this
  have hne := analyticOrderAt_ne_one_of_symm hΛ hsym
  rw [analyticOrderAt_mul hP hFa, (analyticOrderAt_eq_zero.mpr (Or.inr hP1)), zero_add] at hne
  exact hne

end ZInQ.Contrib.H21Lcal
