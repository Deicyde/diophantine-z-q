import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Definitions.Def_CerednikDrinfeld_ShimuraCurve
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Definitions.Def_QuaternionAlgebra_BaseChange
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Theorems.Thm_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Theorems.Thm_Padic_exists_ternary_isotropic_two_mul_iff_of_norm_eq_one
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Theorems.Thm_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Theorems.Thm_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero

/-!
# Exact ramification of the project's quaternion algebra (2,-3)

Source revision: anthropics/fermats-last-theorem
6e837e75355538c7f80bab5b956861e86c4eacc2.
The imported sources and the adapted (-1,-1) local-to-ternary proof route are
Copyright 2026 Anthropic, PBC, released under Apache-2.0; the parent-owned
AnthropicFLT vendor tree retains the upstream LICENSE and attribution.
Compatibility changes in this file: the parent's Contrib import prefix,
namespace isolation, and specialization to the actual coefficients (2,-3).

The exported predicate has exactly four explicit arguments and no extra
hypotheses. It is the upstream predicate, not a replacement definition.
`QuaternionAlgebra ℚ 2 0 (-3)` is definitionally the project's `LeafQM.B`.
The real scalar-extension witness and the two p-adic division statements are
also supplied. This bridge does not by itself discharge the moduli leaf R1fpAb.
-/

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace ZInQ.Contrib.CloudB4W28

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The homogeneous ternary form is anisotropic over the 2-adic numbers. -/
theorem ternary_anisotropic_two :
    ∀ z x y : ℚ_[2],
      z ^ 2 - (2 : ℚ_[2]) * x ^ 2 - (-3 : ℚ_[2]) * y ^ 2 = 0 →
        z = 0 ∧ x = 0 ∧ y = 0 := by
  intro z x y heq
  have h2 : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
    simpa only [Nat.cast_ofNat, one_div] using (Padic.norm_p (p := 2))
  have hneg3 : ‖(-3 : ℚ_[2])‖ = 1 := by
    rw [norm_neg]
    exact (Padic.norm_natCast_eq_one_iff (p := 2) (n := 3)).mpr (by decide)
  have h4 : ‖(4 : ℚ_[2])‖ = (1 / 4 : ℝ) := by
    calc
      ‖(4 : ℚ_[2])‖ = ‖(2 : ℚ_[2]) * 2‖ := by norm_num
      _ = ‖(2 : ℚ_[2])‖ * ‖(2 : ℚ_[2])‖ := norm_mul _ _
      _ = (1 / 4 : ℝ) := by rw [h2]; norm_num
  have hneg2 : ‖(-2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by rw [norm_neg, h2]
  have hneg4 : ‖(-4 : ℚ_[2])‖ = (1 / 4 : ℝ) := by rw [norm_neg, h4]
  have hcut : (2 : ℝ) ^ (-3 : ℤ) = (1 / 8 : ℝ) := by norm_num
  by_contra hne
  have hex : ∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (2 * (1 : ℚ_[2])) * x ^ 2 - (-3 : ℚ_[2]) * y ^ 2 = 0 := by
    exact ⟨z, x, y, hne, by simpa only [mul_one] using heq⟩
  have hcrit :=
    (Padic.exists_ternary_isotropic_two_mul_iff_of_norm_eq_one
      (1 : ℚ_[2]) (-3 : ℚ_[2]) (by exact norm_one) hneg3).mp hex
  have hleft : (-3 : ℚ_[2]) - 1 = (-4 : ℚ_[2]) := by norm_num
  have hright : 2 * (1 : ℚ_[2]) + (-3 : ℚ_[2]) - 1 = (-2 : ℚ_[2]) := by norm_num
  rcases hcrit with hc | hc
  · rw [hleft, hneg4, hcut] at hc
    norm_num at hc
  · rw [hright, hneg2, hcut] at hc
    norm_num at hc

private theorem norm_two_three : ‖(2 : ℚ_[3])‖ = 1 := by
  simpa using (Padic.norm_natCast_eq_one_iff (p := 3) (n := 2)).mpr (by decide)

private theorem square_zmod_three (t : ZMod 3) : t ^ 2 = 0 ∨ t ^ 2 = 1 := by
  fin_cases t <;> decide

/-- Reduction modulo 3 rules out a square root of 2 in the 3-adic numbers. -/
theorem nonsquare_two_three : ¬ IsSquare (2 : ℚ_[3]) := by
  rintro ⟨r, hr⟩
  have hnorm : ‖r‖ * ‖r‖ = 1 := by
    rw [← norm_mul, ← hr, norm_two_three]
  have hrle : ‖r‖ ≤ 1 := by nlinarith [norm_nonneg r]
  let R : ℤ_[3] := ⟨r, hrle⟩
  have hR : (2 : ℤ_[3]) = R * R := by
    apply PadicInt.ext
    change (2 : ℚ_[3]) = r * r
    exact hr
  have hres : (PadicInt.toZMod R) ^ 2 = (2 : ZMod 3) := by
    have hmap := congrArg (PadicInt.toZMod (p := 3)) hR
    simpa only [map_mul, map_ofNat, pow_two] using hmap.symm
  rcases square_zmod_three (PadicInt.toZMod R) with h0 | h1
  · exact (by decide : (2 : ZMod 3) ≠ 0) (hres.symm.trans h0)
  · exact (by decide : (2 : ZMod 3) ≠ 1) (hres.symm.trans h1)

/-- The odd-prime local criterion gives anisotropy at 3 after swapping x and y. -/
theorem ternary_anisotropic_three :
    ∀ z x y : ℚ_[3],
      z ^ 2 - (2 : ℚ_[3]) * x ^ 2 - (-3 : ℚ_[3]) * y ^ 2 = 0 →
        z = 0 ∧ x = 0 ∧ y = 0 := by
  intro z x y heq
  by_contra hne
  apply nonsquare_two_three
  apply
    (Padic.exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two
      3 (by decide) (-1 : ℚ_[3]) (2 : ℚ_[3]) (by simp) norm_two_three).mp
  refine ⟨z, y, x, ?_, ?_⟩
  · intro ht
    exact hne ⟨ht.1, ht.2.2, ht.2.1⟩
  · linear_combination heq

/-- In the exact upstream sense, the quaternion algebra over Q_2 is division. -/
theorem division_two : ∀ q : ℍ[ℚ_[2], 2, -3], q ≠ 0 → IsUnit q := by
  rw [QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero]
  exact
    (QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
      ℚ_[2] (2 : ℚ_[2]) (-3) (by norm_num) (by norm_num)).mpr ternary_anisotropic_two

/-- In the exact upstream sense, the quaternion algebra over Q_3 is division. -/
theorem division_three : ∀ q : ℍ[ℚ_[3], 2, -3], q ≠ 0 → IsUnit q := by
  rw [QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero]
  exact
    (QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
      ℚ_[3] (2 : ℚ_[3]) (-3) (by norm_num) (by norm_num)).mpr ternary_anisotropic_three

private theorem units_iff_anisotropic_adic (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∀ q : ℍ[ℚ, 2, -3] ⊗[ℚ] v.adicCompletion ℚ, q ≠ 0 → IsUnit q) ↔
      ∀ z x y : v.adicCompletion ℚ,
        z ^ 2 - (2 : v.adicCompletion ℚ) * x ^ 2 - (-3 : v.adicCompletion ℚ) * y ^ 2 = 0 →
          z = 0 ∧ x = 0 ∧ y = 0 := by
  have h2 : (2 : v.adicCompletion ℚ) ≠ 0 := by
    simpa only [map_ofNat] using
      (map_ne_zero (algebraMap ℚ (v.adicCompletion ℚ))).mpr
        (by norm_num : (2 : ℚ) ≠ 0)
  have hneg3 : (-3 : v.adicCompletion ℚ) ≠ 0 := by
    simpa only [map_neg, map_ofNat] using
      (map_ne_zero (algebraMap ℚ (v.adicCompletion ℚ))).mpr
        (by norm_num : (-3 : ℚ) ≠ 0)
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero]
  simpa using
    (QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
      (v.adicCompletion ℚ) (2 : v.adicCompletion ℚ) (-3) h2 hneg3)

private theorem prime_mem_iff_natGenerator (v : HeightOneSpectrum (𝓞 ℚ))
    (p : ℕ) (hp : p.Prime) :
    (p : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v = p := by
  have hmem : Rat.HeightOneSpectrum.natGenerator v ∣ p ↔ (p : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have hcast : (p : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) (p : 𝓞 ℚ) := by simp
    rw [hcast, Ideal.apply_mem_of_equiv_iff]
  rw [← hmem, Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency.types false in
private theorem anisotropic_adic_of_padic
    (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [Fact p.Prime]
    (hgen : Rat.HeightOneSpectrum.natGenerator v = p)
    (hpadic : ∀ z x y : ℚ_[p],
      z ^ 2 - (2 : ℚ_[p]) * x ^ 2 - (-3 : ℚ_[p]) * y ^ 2 = 0 →
        z = 0 ∧ x = 0 ∧ y = 0) :
    ∀ z x y : v.adicCompletion ℚ,
      z ^ 2 - (2 : v.adicCompletion ℚ) * x ^ 2 - (-3 : v.adicCompletion ℚ) * y ^ 2 = 0 →
        z = 0 ∧ x = 0 ∧ y = 0 := by
  have hidx : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := by
    change Rat.HeightOneSpectrum.natGenerator v = p
    exact hgen
  cases hidx
  let e : v.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv
  intro z x y heq
  have heq' : (e z) ^ 2 - (2 : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) * (e x) ^ 2 -
      (-3 : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) * (e y) ^ 2 = 0 := by
    simpa only [map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero]
      using congrArg e heq
  obtain ⟨hz, hx, hy⟩ := hpadic (e z) (e x) (e y) heq'
  exact ⟨e.injective (hz.trans (map_zero e).symm),
    e.injective (hx.trans (map_zero e).symm), e.injective (hy.trans (map_zero e).symm)⟩

/-- A nontrivial local zero exists at every rational finite place away from 2 and 3. -/
theorem ternary_isotropic_away (v : HeightOneSpectrum (𝓞 ℚ))
    (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) (h3 : (3 : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (2 : v.adicCompletion ℚ) * x ^ 2 - (-3 : v.adicCompletion ℚ) * y ^ 2 = 0 := by
  have hn : ((-3 : ℤ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro hn
    have hn' : -(3 : 𝓞 ℚ) ∈ v.asIdeal := by simpa using hn
    exact h3 (v.asIdeal.neg_mem_iff.mp hn')
  simpa using
    (Rat.exists_ternary_isotropic_adicCompletion_of_intCast_notMem 2 (-3) v h2
      (by simpa using h2) hn)

/-- The exact FLT predicate for the project's B, with no remaining hypotheses. -/
theorem isIndefiniteRamifiedExactlyAt_two_neg_three :
    QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt (2 : ℚ) (-3 : ℚ) 2 3 := by
  refine ⟨Or.inl (by norm_num), fun v => ?_⟩
  rw [units_iff_anisotropic_adic]
  constructor
  · intro haniso
    by_contra hmem
    obtain ⟨h2, h3⟩ := not_or.mp hmem
    obtain ⟨z, x, y, hne, heq⟩ := ternary_isotropic_away v h2 h3
    exact hne (haniso z x y heq)
  · rintro (h2 | h3)
    · exact anisotropic_adic_of_padic v 2
        ((prime_mem_iff_natGenerator v 2 Nat.prime_two).mp h2) ternary_anisotropic_two
    · exact anisotropic_adic_of_padic v 3
        ((prime_mem_iff_natGenerator v 3 Nat.prime_three).mp h3) ternary_anisotropic_three

/-- An actual real splitting of the scalar extension of the project's quaternion algebra. -/
theorem split_real :
    Nonempty ((ℝ ⊗[ℚ] QuaternionAlgebra ℚ 2 0 (-3)) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℝ) := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  obtain ⟨e⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero
    ℝ (by norm_num) (2 : ℝ) (-3) (by norm_num) (by norm_num)
    (Real.sqrt 2) 1 0 0
    (by rintro ⟨_, h1, _, _⟩; exact one_ne_zero h1)
    (by rw [hsqrt]; norm_num)
  let e0 : (ℝ ⊗[ℚ] QuaternionAlgebra ℚ 2 0 (-3)) ≃ₐ[ℝ] QuaternionAlgebra ℝ 2 0 (-3) :=
    QuaternionAlgebra.baseChange (by norm_num) (by norm_num) (by norm_num)
  exact ⟨e0.trans e⟩

end ZInQ.Contrib.CloudB4W28

end
