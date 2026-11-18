import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Valuation subrings containing a Dedekind domain are determined by their center

Let `B` be a Dedekind domain with fraction field `N`, and `W₁, W₂` valuation subrings of `N` containing
`B`. If an element of `B` is a nonunit of `W₁` exactly when it is a nonunit of `W₂` (same center on
`B`), then `W₁ = W₂`.

Proof: let `P` be the common center. If `P = 0`, every nonzero element of `B` is a unit in both, so
both are `N`. Otherwise the localization `B_P`, realised inside `N`, is a discrete valuation ring,
hence a valuation ring with fraction field `N`: every `x` or `x⁻¹` has the form `a / s` with `s ∉ P`.
In the first case `x ∈ W₂` because `s` is a unit of `W₂`; in the second, `x ∈ W₁` forces `a ∉ P`, so
`x = s / a ∈ W₂`.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open IsLocalRing nonZeroDivisors

variable {B N : Type*} [CommRing B] [IsDedekindDomain B] [Field N] [Algebra B N]
  [IsFractionRing B N]

/-- The center of a valuation subring containing `B`, as a prime ideal of `B`. -/
def center (W : ValuationSubring N) (h : ∀ b : B, algebraMap B N b ∈ W) : Ideal B :=
  (maximalIdeal W).comap ((algebraMap B N).codRestrict W.toSubring h)

theorem mem_center_iff (W : ValuationSubring N) (h : ∀ b : B, algebraMap B N b ∈ W) (b : B) :
    b ∈ center W h ↔ W.valuation (algebraMap B N b) < 1 := by
  unfold center
  rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

instance center_isPrime (W : ValuationSubring N) (h : ∀ b : B, algebraMap B N b ∈ W) :
    (center W h).IsPrime := by
  unfold center
  exact Ideal.comap_isPrime _ _

theorem val_eq_one_of_not_mem_center (W : ValuationSubring N) (h : ∀ b : B, algebraMap B N b ∈ W)
    {b : B} (hb : b ∉ center W h) : W.valuation (algebraMap B N b) = 1 := by
  rw [mem_center_iff] at hb
  exact le_antisymm ((W.valuation_le_one_iff _).2 (h b)) (not_lt.mp hb)

/-- One inclusion; the theorem follows by symmetry. -/
theorem le_of_center_eq (W₁ W₂ : ValuationSubring N) (h₁ : ∀ b : B, algebraMap B N b ∈ W₁)
    (h₂ : ∀ b : B, algebraMap B N b ∈ W₂) (hc : center W₁ h₁ = center W₂ h₂) : W₁ ≤ W₂ := by
  classical
  intro x hx
  set P := center W₁ h₁ with hPdef
  have hunit₂ : ∀ s : B, s ∉ P → W₂.valuation (algebraMap B N s) = 1 := by
    intro s hs
    rw [hc] at hs
    exact val_eq_one_of_not_mem_center W₂ h₂ hs
  have hunit₁ : ∀ s : B, s ∉ P → W₁.valuation (algebraMap B N s) = 1 := fun s hs =>
    val_eq_one_of_not_mem_center W₁ h₁ hs
  -- an element `a / s` with `s ∉ P` lies in `W₂`
  have hfrac : ∀ a s : B, s ∉ P →
      algebraMap B N a * (algebraMap B N s)⁻¹ ∈ W₂ := by
    intro a s hs
    rw [← W₂.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv, hunit₂ s hs, inv_one,
      mul_one]
    exact (W₂.valuation_le_one_iff _).2 (h₂ a)
  by_cases hP : P = ⊥
  · obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hs0 : s ∉ P := by
      rw [hP, Ideal.mem_bot]
      exact nonZeroDivisors.ne_zero hs
    rw [div_eq_mul_inv]
    exact hfrac a s hs0
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
      have hxy : x = (y : N) := hy.symm
      rw [hxy, e]
      exact hfrac a s hs
    · obtain ⟨a, s, hs, e⟩ := hmem y
      have hxy : x⁻¹ = (y : N) := hy.symm
      by_cases hx0 : x = 0
      · rw [hx0]
        exact W₂.zero_mem
      have hx' : x⁻¹ = algebraMap B N a * (algebraMap B N s)⁻¹ := hxy.trans e
      have ha0 : algebraMap B N a ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hx'
        exact inv_ne_zero hx0 hx'
      -- `a` is a unit of `W₁`
      have ha : a ∉ P := by
        intro haP
        rw [hPdef, mem_center_iff] at haP
        have hv : W₁.valuation x⁻¹ = W₁.valuation (algebraMap B N a) := by
          rw [hx', Valuation.map_mul, Valuation.map_inv, hunit₁ s hs, inv_one, mul_one]
        have hle : W₁.valuation x ≤ 1 := (W₁.valuation_le_one_iff x).2 hx
        have hpos : 0 < W₁.valuation x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hx0)
        have hge : 1 ≤ W₁.valuation x⁻¹ := by
          rw [Valuation.map_inv]
          exact one_le_inv₀ hpos |>.2 hle
        rw [hv] at hge
        exact absurd haP (not_lt.mpr hge)
      have hxe : x = algebraMap B N s * (algebraMap B N a)⁻¹ := by
        have := congrArg (fun z => z⁻¹) hx'
        simp only [inv_inv, mul_inv] at this
        rw [this, mul_comm]
      rw [hxe]
      exact hfrac s a ha

/-- **Valuation subrings containing a Dedekind domain with the same center are equal.** -/
theorem eq_of_center_eq (W₁ W₂ : ValuationSubring N) (h₁ : ∀ b : B, algebraMap B N b ∈ W₁)
    (h₂ : ∀ b : B, algebraMap B N b ∈ W₂) (hc : center W₁ h₁ = center W₂ h₂) : W₁ = W₂ :=
  le_antisymm (le_of_center_eq W₁ W₂ h₁ h₂ hc) (le_of_center_eq W₂ W₁ h₂ h₁ hc.symm)

end InertiaPointDescent
