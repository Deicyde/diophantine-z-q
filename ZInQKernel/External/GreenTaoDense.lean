import ZInQKernel.Hypotheses.GreenTao
import ZInQKernel.External.GreenTaoDense.Window
import ZInQKernel.External.GreenTaoDense.Assembly

/-!
# Green–Tao, dense form: root module

Root module of task `gt-dense` (plan: `docs/research/gt-dense.md`). Step 1: the window lemma for
`ZInQ.PrimesRelUpperDensityPos`. Steps 2–6 (`SetWeight`, `PrimeModulusTransference`, `Assembly`)
and the bridge `ZInQ.greenTaoDense : ZInQ.GreenTaoDense`.
-/

namespace ZInQ.GreenTaoDense

open Filter Finset

open Classical in
/-- **The window lemma.** A set of positive relative upper density in the primes has, for infinitely
many `Z`, at least `c₁ Z / log Z` elements in `(Z/2, Z]`, for some `c₁ > 0`. -/
theorem frequently_window {A : Set ℕ} (h : ZInQ.PrimesRelUpperDensityPos A) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ᶠ Z : ℕ in atTop, c₁ * Z / Real.log Z ≤
      (((Ioc (Z / 2) Z).filter (· ∈ A)).card : ℝ) := by
  obtain ⟨c, hc, hfreq⟩ := h
  exact ⟨c * Real.log 2 / 24, by have := Real.log_pos one_lt_two; positivity,
    frequently_window_of hc hfreq⟩

/-- **Green–Tao, dense form** (`ZInQ.GreenTaoDense`), from the vendored proof of Green–Tao. -/
theorem _root_.ZInQ.greenTaoDense : ZInQ.GreenTaoDense := by
  intro A hA hd k
  obtain ⟨c₁, hc₁, hwin⟩ := frequently_window hd
  obtain ⟨a, d, hd0, h⟩ :=
    containsAP_of_frequently_window hasPrimeModulusSubweightCounts hA hc₁ hwin k
  exact ⟨a, d, hd0, h⟩

end ZInQ.GreenTaoDense
