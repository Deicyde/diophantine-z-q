import ValuationLocalizationV001
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.FieldTheory.Perfect

/-!
# The residue field of a discrete valuation ring of a number field is finite

Let `O` be a valuation subring of a number field `K` which is a discrete valuation ring. Then `O`
contains the ring of integers `𝓞 K` (integral elements lie in every valuation ring), its center
`P` on `𝓞 K` is a nonzero prime (otherwise `O = K`), and by the localization description every
element of `O` is `a / s` with `a, s ∈ 𝓞 K`, `s ∉ P`. Hence the residue field of `O` is covered by
the finite set of quotients of residues of `𝓞 K ⧸ P`, so it is finite, hence perfect.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open NumberField IsLocalRing

variable (K : Type*) [Field K] [NumberField K]

theorem ringOfIntegers_mem (O : ValuationSubring K) (b : 𝓞 K) : algebraMap (𝓞 K) K b ∈ O := by
  have hv : Valuation.Integers O.valuation O :=
    ⟨Subtype.val_injective, fun x => O.valuation_le_one x,
      fun r hr => ⟨⟨r, (O.valuation_le_one_iff r).1 hr⟩, rfl⟩⟩
  have h1 : IsIntegral ℤ (algebraMap (𝓞 K) K b) := RingOfIntegers.isIntegral_coe b
  have h2 : IsIntegral O (algebraMap (𝓞 K) K b) := h1.tower_top
  exact (O.valuation_le_one_iff _).1 (hv.mem_of_integral h2)

/-- **The residue field of a discrete valuation subring of a number field is finite.** -/
theorem finite_residueField (O : ValuationSubring K) [IsDiscreteValuationRing O] :
    Finite (ResidueField O) := by
  classical
  set hB := ringOfIntegers_mem K O
  set P := center O hB with hPdef
  -- the center is nonzero
  have hne : P ≠ ⊥ := by
    intro hP
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    have hinv : (ϖ : K)⁻¹ ∈ O := by
      obtain ⟨a, s, hs, e⟩ := IsFractionRing.div_surjective (A := 𝓞 K) ((ϖ : K)⁻¹)
      have hs0 : s ∉ P := by
        rw [hP, Ideal.mem_bot]
        exact nonZeroDivisors.ne_zero hs
      rw [← e, div_eq_mul_inv]
      exact div_mem_of_not_mem_center O hB a s hs0
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨⟨(ϖ : K)⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    change (ϖ : K) * (ϖ : K)⁻¹ = 1
    exact mul_inv_cancel₀ hϖ0
  have hfin : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  -- residues of integers
  let φ : 𝓞 K →+* ResidueField O :=
    (residue O).comp ((algebraMap (𝓞 K) K).codRestrict O.toSubring hB)
  have hker : ∀ b ∈ P, φ b = 0 := by
    intro b hb
    rw [hPdef, mem_center_iff] at hb
    change residue O ⟨algebraMap (𝓞 K) K b, hB b⟩ = 0
    rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact hb
  let ψ : 𝓞 K ⧸ P →+* ResidueField O := Ideal.Quotient.lift P φ hker
  let F : (𝓞 K ⧸ P) × (𝓞 K ⧸ P) → ResidueField O := fun ab => ψ ab.1 * (ψ ab.2)⁻¹
  have hF : Function.Surjective F := by
    intro r
    obtain ⟨u, rfl⟩ := residue_surjective r
    obtain ⟨a, s, hs, e⟩ := exists_eq_div_of_mem O hB u.2
    refine ⟨(Ideal.Quotient.mk P a, Ideal.Quotient.mk P s), ?_⟩
    change φ a * (φ s)⁻¹ = residue O u
    have hs1 : φ s ≠ 0 := by
      intro h0
      apply hs
      rw [mem_center_iff]
      change residue O ⟨algebraMap (𝓞 K) K s, hB s⟩ = 0 at h0
      rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h0
      exact h0
    have hmul : residue O u * φ s = φ a := by
      change residue O u * residue O ⟨algebraMap (𝓞 K) K s, hB s⟩ =
        residue O ⟨algebraMap (𝓞 K) K a, hB a⟩
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      change (u : K) * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K a
      have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
        intro h0
        apply hs1
        change residue O ⟨algebraMap (𝓞 K) K s, hB s⟩ = 0
        rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
        change O.valuation (algebraMap (𝓞 K) K s) < 1
        rw [h0, Valuation.map_zero]
        exact zero_lt_one
      rw [e, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    rw [← hmul, mul_assoc, mul_inv_cancel₀ hs1, mul_one]
  exact Finite.of_surjective F hF

/-- The residue field of a discrete valuation subring of a number field is perfect. -/
theorem perfectField_residueField (O : ValuationSubring K) [IsDiscreteValuationRing O] :
    PerfectField (ResidueField O) := by
  have := finite_residueField K O
  have : Fintype (ResidueField O) := Fintype.ofFinite _
  infer_instance

end InertiaPointDescent
