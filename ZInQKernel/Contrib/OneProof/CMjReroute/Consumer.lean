import ZInQKernel.Contrib.OneProof.CMBranch

/-!
# The CM height bound with the class-number input of a sub-order

`CMBranch.faltingsHeight_le_bcm` bounds `h_F(E)` for a CM elliptic curve `E/L` with `End(E_{L̄}) ≅ R`,
`[L : ℚ] ≤ D`, from Fowler's Prop. 2.7 at `n = D` applied to `R` itself, which needs
`card Pic(R) ≤ [L : ℚ]` (the degree of a singular modulus). Here the same bound is proved from Fowler's
Prop. 2.7 at `n = 324` applied to any order `R₀ ⊆ R` of the same field with `card Pic(R₀) ≤ 324`:

* `conductor_dvd_of_le`: `R₀ ⊆ R` gives `f_R ∣ f_{R₀}`, so `|Δ_R| ≤ |Δ_{R₀}|` (`abs_orderDisc_le`);
* `fowler_of_le`: Fowler at `n` for `R₀` bounds `√|Δ_R|`;
* `fowler324_le`: the bound at `324` is at most the bound at `D = heightD`;
* `faltingsHeight_le_bcm_of_sub`: the consumer, without `CMjDegree`.
-/

noncomputable section

namespace HDec.CMBranch.CMjReroute

open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HDec.CMBranch
open HSyn HSyn.G0Split
open _root_.CMBranch

/-- `R₀ ⊆ R ⊆ 𝓞_k` gives `[𝓞_k : R] ∣ [𝓞_k : R₀]`. -/
theorem conductor_dvd_of_le {k : Type} [Field k] {R₀ R : Subring k} (hle : R₀ ≤ R) :
    LeafQM.AV.conductor R ∣ LeafQM.AV.conductor R₀ := by
  unfold LeafQM.AV.conductor
  exact AddSubgroup.relIndex_dvd_of_le_left _ hle

/-- `|Δ_R| ≤ |Δ_{R₀}|` for `R₀ ⊆ R` (the discriminant is `f² d_k`). -/
theorem abs_orderDisc_le {k : Type} [Field k] [NumberField k] {R₀ R : Subring k} (hle : R₀ ≤ R)
    (hR₀ : LeafQM.AV.conductor R₀ ≠ 0) : |(orderDisc R : ℝ)| ≤ |(orderDisc R₀ : ℝ)| := by
  have hd := Nat.le_of_dvd (Nat.pos_of_ne_zero hR₀) (conductor_dvd_of_le hle)
  unfold orderDisc
  push_cast
  rw [abs_mul, abs_mul, abs_pow, abs_pow]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hd) 2

/-- **Fowler for an over-order.** Fowler's Prop. 2.7 at `n` for `R₀` bounds `√|Δ_R|` for every
order `R ⊇ R₀`. -/
theorem fowler_of_le (hF : FowlerProp27) {k : Type} [Field k] [NumberField k] {R₀ R : Subring k}
    (hR₀ : IsImagQuadOrder k R₀) (hle : R₀ ≤ R) (n : ℕ) (hn : 1 ≤ n)
    (hpic : Nat.card (CommRing.Pic R₀) ≤ n) :
    Real.sqrt |(orderDisc R : ℝ)| ≤ 2 * (n : ℝ) ^ 2 * Real.exp (21000 * (n : ℝ) ^ 2) :=
  (Real.sqrt_le_sqrt (abs_orderDisc_le hle hR₀.2.2.2)).trans (hF k R₀ hR₀ n hn hpic)

/-- The bound is monotone in `n`. -/
theorem fowlerBound_mono {m n : ℕ} (h : m ≤ n) :
    2 * (m : ℝ) ^ 2 * Real.exp (21000 * (m : ℝ) ^ 2) ≤
      2 * (n : ℝ) ^ 2 * Real.exp (21000 * (n : ℝ) ^ 2) := by
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hsq : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hm0 hmn 2
  have he : Real.exp (21000 * (m : ℝ) ^ 2) ≤ Real.exp (21000 * (n : ℝ) ^ 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : 2 * (m : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by linarith
  exact mul_le_mul h2 he (Real.exp_pos _).le (by positivity)

theorem le_heightD_324 : 324 ≤ heightD := by
  have := _root_.ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  omega

/-- **`h_F(E) ≤ B_cm` from a sub-order with at most `324` classes** (the consumer of
`CMBranch.faltingsHeight_le_bcm`, with `CMjDegree` replaced by `R₀ ⊆ R`, `card Pic(R₀) ≤ 324`). -/
theorem faltingsHeight_le_bcm_of_sub (hfin : StableHeightFinite) (hF : FowlerProp27)
    (hPG : CMPotentialGood) (h62 : CMHeight62) (hRP : ReducedCMPeriod)
    {L : Type} [Field L] [NumberField L] (E : ZInQ.DefFaltings.AbVar L) (hE1 : E.dim = 1)
    {k : Type} [Field k] [NumberField k] (R R₀ : Subring k) (hR : IsImagQuadOrder k R)
    (hR₀ : IsImagQuadOrder k R₀) (hle : R₀ ≤ R) (hpic : Nat.card (CommRing.Pic R₀) ≤ 324)
    (hCM : IsCMBy E k R) :
    faltingsHeight E ≤ (heightBcm : ℝ) := by
  obtain ⟨L₁, i1, i2, i3, 𝒢, h𝒢⟩ := hPG L E hE1 k R hR hCM
  set s := Real.sqrt |(orderDisc R : ℝ)| with hs
  have hτ : ∀ σ : L₁ →+* ℂ, ∃ τ : ℂ,
      IsPeriodAt (LeafAdopt.abVarEquiv L E) (σ.comp (algebraMap L L₁)) τ ∧
        Real.sqrt 3 / 2 ≤ τ.im ∧ τ.im ≤ s / 2 :=
    fun σ => hRP L E hE1 k R hR hCM _
  choose τ hτ using hτ
  have h3 : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
  have hpos : ∀ σ, 0 < (τ σ).im := fun σ => lt_of_lt_of_le h3 (hτ σ).2.1
  have hle62 := h62 L L₁ E hE1 𝒢 h𝒢 τ (fun σ => ⟨hpos σ, (hτ σ).1⟩)
  have hterm : ∀ σ, summand62 (τ σ) ≤ Real.pi * s / 12 + 1 := by
    intro σ
    rw [summand62_eq_archSummand (hpos σ)]
    have h1 := archSummand_le (hτ σ).2.1
    have h2 : Real.pi * (τ σ).im / 6 ≤ Real.pi * (s / 2) / 6 := by
      have := mul_le_mul_of_nonneg_left (hτ σ).2.2 Real.pi_pos.le; linarith
    linarith
  have hn : (0 : ℝ) < Module.finrank ℚ L₁ := by exact_mod_cast Module.finrank_pos
  have hcard : (Finset.univ : Finset (L₁ →+* ℂ)).card = Module.finrank ℚ L₁ := by
    rw [Finset.card_univ]; exact NumberField.Embeddings.card L₁ ℂ
  have havg : (∑ σ, summand62 (τ σ)) / Module.finrank ℚ L₁ ≤ Real.pi * s / 12 + 1 := by
    rw [div_le_iff₀ hn]
    calc ∑ σ, summand62 (τ σ) ≤ ∑ _σ : L₁ →+* ℂ, (Real.pi * s / 12 + 1) :=
          Finset.sum_le_sum fun σ _ => hterm σ
      _ = (Real.pi * s / 12 + 1) * Module.finrank ℚ L₁ := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
  have hfow : s ≤ 2 * (heightD : ℝ) ^ 2 * Real.exp (21000 * (heightD : ℝ) ^ 2) :=
    (fowler_of_le hF hR₀ hle 324 (by norm_num) hpic).trans (fowlerBound_mono le_heightD_324)
  have hB := bcm_of_fowler heightD hfow
  rw [← cast_heightBcm] at hB
  have hE : (faltingsHeight E : EReal) ≤ ((heightBcm : ℝ) : EReal) := by
    rw [faltingsHeight_coe hfin]
    exact hle62.trans (EReal.coe_le_coe_iff.mpr (havg.trans hB))
  exact EReal.coe_le_coe_iff.mp hE

end HDec.CMBranch.CMjReroute
