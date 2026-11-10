import ZInQKernel.External.GreenTaoDense.Window
import ZInQKernel.External.GreenTaoDense.SetWeight
import ZInQKernel.External.GreenTaoDense.PrimeModulusTransference

/-!
# Green–Tao for a set of primes with frequent mass in dyadic windows

Steps 2–7 of §3 of `docs/research/gt-dense.md`. Fix `k ≥ 3` and `α = primeScale k _`. From the
window constant `c₁` set `δ = α c₁ / 192`. The transference (`HasPrimeModulusSubweightCounts`)
gives `w`, `c > 0` and a threshold. The window transfer picks a prime modulus `q` beyond every
threshold such that `A` has `(c₁/6) X / log X` elements in `(X/4, X]`, `X = W ⌊q/8⌋`. The residue
pigeonhole for `A` and the vendored Chebyshev arithmetic give `mean (wTrickedSetWeight A) ≥ δ`.
The transference gives the count `c`, the height bound gives positive off-diagonal mass, and
extraction gives the progression.
-/

namespace ZInQ.GreenTaoDense

open Submission.GreenTao Filter Finset Real

open Classical in
theorem containsAP_of_frequently_window (hT : HasPrimeModulusSubweightCounts) {A : Set ℕ}
    (hA : A ⊆ {p | p.Prime}) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hwin : ∃ᶠ Z : ℕ in atTop, c₁ * Z / Real.log Z ≤
      (((Ioc (Z / 2) Z).filter (· ∈ A)).card : ℝ)) (k : ℕ) :
    ContainsAP A k := by
  -- lengths `k ≤ 2` by truncation
  suffices h3 : ∀ k, 3 ≤ k → ContainsAP A k by
    rcases le_or_gt 3 k with hk | hk
    · exact h3 k hk
    · exact (h3 3 le_rfl).take (by omega)
  intro k hk
  set α := primeScale k standardSmoothSieveCutoff.normalizer with hαdef
  have hα : 0 < α := primeScale_pos hk standardSmoothSieveCutoff_normalizer_pos
  set c₂ := c₁ / 6 with hc₂
  have hc₂pos : 0 < c₂ := by positivity
  have hδ : 0 < α * c₂ / 32 := by positivity
  obtain ⟨w, c, hc, hev⟩ := hT k hk (α * c₂ / 32) hδ
  set W := primorial w with hWdef
  have hW : 0 < W := primorial_pos w
  obtain ⟨Mthr, hMthr⟩ := eventually_atTop.1 hev
  obtain ⟨Nh, hNh⟩ := eventually_atTop.1 (eventually_wTrickedPrimeWeight_height_pow_lt_linear α c k hc)
  obtain ⟨q, hq, hQq, hQX, hcount⟩ := exists_prime_modulus_of_frequently_window hc₁ hwin hW
    (Mthr + Nh + 2 * W + 4 * w + 16)
  obtain ⟨M, rfl⟩ : ∃ M, q = M + 1 := ⟨q - 1, by have := hq.pos; omega⟩
  -- the sampled scale is the vendored `wTrickPrimeScale`
  have hXdef : W * ((M + 1) / 8) = wTrickPrimeScale W (M + 1) := rfl
  rw [hXdef] at hQX hcount
  set X := wTrickPrimeScale W (M + 1) with hX
  have hw : w ≤ wTrickPrimeScale (primorial w) (M + 1) / 4 := by
    rw [← hWdef, ← hX]; omega
  obtain ⟨b, hb, hmean⟩ := exists_reducedResidue_setWeight_mean_lower_bound A (N := M + 1)
    hα.le hw
  rw [← hWdef, ← hX] at hmean
  -- the elements of `A` in `(X/4, X]` are the `A`-primes of the quarter interval
  have hsub : (Ioc (X / 4) X).filter (· ∈ A) ⊆ (primesInQuarterInterval X).filter (· ∈ A) := by
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    simp only [mem_filter, mem_primesInQuarterInterval]
    exact ⟨⟨hA hp.2, hp.1.1, hp.1.2⟩, hp.2⟩
  have hcount' : c₂ * (X : ℝ) / Real.log X ≤
      (#((primesInQuarterInterval X).filter (· ∈ A)) : ℝ) :=
    hcount.trans (by exact_mod_cast card_le_card hsub)
  -- the mean bound
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set α' := α * c₂ * 4 / Real.log 2 with hα'
  have hcheb := chebyshev_wTrick_lower_bound hW (N := M + 1) (α := α') (by positivity) (by omega)
    (by rw [← hX]; omega)
  rw [← hX] at hcheb
  have hL : 0 ≤ Real.log (X / 4 + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X / 4 + 1))
  have hδmean : α * c₂ / 32 ≤ mean (wTrickedSetWeight A α W b : ZMod (M + 1) → ℝ) := by
    have e1 : α' * Real.log 2 / 128 = α * c₂ / 32 := by rw [hα']; field_simp; ring
    have e2 : α' / (W : ℝ) * (Real.log 2 / 4 * (X : ℝ) / Real.log X) =
        α / (W : ℝ) * (c₂ * (X : ℝ) / Real.log X) := by rw [hα']; field_simp
    rw [e1, e2] at hcheb
    refine hcheb.trans (le_trans ?_ hmean)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hL
    exact mul_le_mul_of_nonneg_left hcount' (by positivity)
  -- transference
  have hbW : b < W := (mem_reducedResidues.mp hb).1
  have hcnt : c ≤ cyclicAPCount k (M + 1) (wTrickedSetWeight A α W b) :=
    hMthr M (by omega) hq b hb _ (wTrickedSetWeight_nonneg hα.le W b)
      (wTrickedSetWeight_le hα.le W b) hδmean
  -- height and positive mass
  have hheight := hNh (M + 1) (by omega)
  have hmass : 0 < cyclicAPOffDiagMass k (M + 1) (wTrickedSetWeight A α W b) := by
    apply cyclicAPOffDiagMass_pos_of_count_lower_height (by omega)
      (wTrickedSetWeight_nonneg hα.le W b)
      (fun x => (wTrickedSetWeight_le hα.le W b x).trans
        (wTrickedPrimeWeight_le_two_mul_alpha_mul_log hα.le hW (by omega) (by omega) x))
      _ hcnt hheight
    have : 0 ≤ Real.log ((M + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M + 1))
    positivity
  exact containsAP_of_wTrickedSetWeight_offDiagMass_pos (by omega) hα hW b hmass

end ZInQ.GreenTaoDense
