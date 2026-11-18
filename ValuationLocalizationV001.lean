import ValuationCenterV001

/-!
# A valuation subring containing a Dedekind domain is its localization at the center

For `B` a Dedekind domain with fraction field `N` and `W` a valuation subring of `N` containing `B`
with center `P`, every element of `W` is a quotient `a / s` with `a, s ∈ B` and `s ∉ P`; conversely
every such quotient lies in `W`. This is the description of `W` as the localization `B_P`, used to
transport decomposition and inertia conditions between `W` and prime ideals of `B`.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open IsLocalRing nonZeroDivisors

variable {B N : Type*} [CommRing B] [IsDedekindDomain B] [Field N] [Algebra B N]
  [IsFractionRing B N]

theorem div_mem_of_not_mem_center (W : ValuationSubring N) (h : ∀ b : B, algebraMap B N b ∈ W)
    (a s : B) (hs : s ∉ center W h) :
    algebraMap B N a * (algebraMap B N s)⁻¹ ∈ W := by
  rw [← W.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv,
    val_eq_one_of_not_mem_center W h hs, inv_one, mul_one]
  exact (W.valuation_le_one_iff _).2 (h a)

/-- **Elements of `W` are fractions with denominator outside the center.** -/
theorem exists_eq_div_of_mem (W : ValuationSubring N) (h : ∀ b : B, algebraMap B N b ∈ W)
    {x : N} (hx : x ∈ W) :
    ∃ a s : B, s ∉ center W h ∧ x = algebraMap B N a * (algebraMap B N s)⁻¹ := by
  classical
  set P := center W h with hPdef
  have hunit : ∀ s : B, s ∉ P → W.valuation (algebraMap B N s) = 1 := fun s hs =>
    val_eq_one_of_not_mem_center W h hs
  by_cases hP : P = ⊥
  · obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    refine ⟨a, s, ?_, by rw [div_eq_mul_inv]⟩
    rw [hP, Ideal.mem_bot]
    exact nonZeroDivisors.ne_zero hs
  · have hS : P.primeCompl ≤ B⁰ := Ideal.primeCompl_le_nonZeroDivisors P
    let Bp := Localization.subalgebra.ofField N P.primeCompl hS
    have hloc : IsLocalization.AtPrime Bp P :=
      Localization.subalgebra.isLocalization_ofField N P.primeCompl hS
    have hdvr : IsDiscreteValuationRing Bp :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP Bp
    have hmem : ∀ y : Bp, ∃ a s : B, s ∉ P ∧
        (y : N) = algebraMap B N a * (algebraMap B N s)⁻¹ := by
      intro y
      obtain ⟨a, s, hs, e⟩ := y.2
      exact ⟨a, s, hs, e⟩
    rcases ValuationRing.isInteger_or_isInteger Bp x with ⟨y, hy⟩ | ⟨y, hy⟩
    · obtain ⟨a, s, hs, e⟩ := hmem y
      exact ⟨a, s, hs, hy.symm.trans e⟩
    · obtain ⟨a, s, hs, e⟩ := hmem y
      by_cases hx0 : x = 0
      · refine ⟨0, 1, ?_, by rw [hx0, map_zero, zero_mul]⟩
        exact fun h1 => (center_isPrime W h).ne_top ((Ideal.eq_top_iff_one _).2 h1)
      have hx' : x⁻¹ = algebraMap B N a * (algebraMap B N s)⁻¹ := hy.symm.trans e
      have ha : a ∉ P := by
        intro haP
        rw [hPdef, mem_center_iff] at haP
        have hv : W.valuation x⁻¹ = W.valuation (algebraMap B N a) := by
          rw [hx', Valuation.map_mul, Valuation.map_inv, hunit s hs, inv_one, mul_one]
        have hle : W.valuation x ≤ 1 := (W.valuation_le_one_iff x).2 hx
        have hpos : 0 < W.valuation x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hx0)
        have hge : 1 ≤ W.valuation x⁻¹ := by
          rw [Valuation.map_inv]
          exact one_le_inv₀ hpos |>.2 hle
        rw [hv] at hge
        exact absurd haP (not_lt.mpr hge)
      refine ⟨s, a, ha, ?_⟩
      have := congrArg (fun z => z⁻¹) hx'
      simp only [inv_inv, mul_inv] at this
      rw [this, mul_comm]

end InertiaPointDescent
