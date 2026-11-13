import ZInQKernel.HDecomp.QM.Leaves
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

noncomputable section

namespace Pi0X6

open NumberField LeafQM LeafQM.AV

/-! ## The closed facts for `k₃ = ℚ(√−3) = ℚ(ζ₃)` -/

abbrev K3 := CyclotomicField 3 ℚ

instance : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : IsCyclotomicExtension {3} ℚ K3 := CyclotomicField.isCyclotomicExtension 3 ℚ

theorem hζ3 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K3) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K3

local notation "ζ₃" => IsCyclotomicExtension.zeta 3 ℚ K3

theorem zeta3_sq : ζ₃ ^ 2 + ζ₃ + 1 = 0 := by
  have h := hζ3.pow_eq_one
  have h1 : ζ₃ ≠ 1 := hζ3.ne_one (by norm_num)
  have : (ζ₃ - 1) * (ζ₃ ^ 2 + ζ₃ + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h3 | h3
  · exact (h1 (sub_eq_zero.1 h3)).elim
  · exact h3

instance : NumberField.IsTotallyComplex K3 :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) K3 (by norm_num)

theorem finrank_K3 : Module.finrank ℚ K3 = 2 := by
  rw [IsCyclotomicExtension.finrank K3 (Polynomial.cyclotomic.irreducible_rat (n := 3) (by norm_num))]
  decide

/-- `√−3 = 2ζ₃ + 1`. -/
theorem sqrt3_sq : (2 * ζ₃ + 1) ^ 2 = (((-3 : ℚ)) : K3) := by
  push_cast; linear_combination 4 * zeta3_sq

/-- `ζ₃ ∈ 𝓞 ℚ(ζ₃)`. -/
def zInt : 𝓞 K3 := hζ3.toInteger

theorem alg_zInt : algebraMap (𝓞 K3) K3 zInt = ζ₃ := rfl

theorem zInt_sq : zInt ^ 2 = -zInt - 1 := by
  apply RingOfIntegers.coe_injective
  rw [map_pow, map_sub, map_neg, map_one, alg_zInt]
  linear_combination zeta3_sq

/-- `1, ζ₃` are independent over `ℤ`. -/
theorem coord_eq_zero (a b : ℤ) (h : (a : 𝓞 K3) + (b : 𝓞 K3) * zInt = 0) : a = 0 ∧ b = 0 := by
  have hK := congrArg (algebraMap (𝓞 K3) K3) h
  rw [map_add, map_mul, alg_zInt, map_intCast, map_intCast, map_zero] at hK
  have hb : b = 0 := by
    by_contra hb
    have hb' : ((b : ℚ) : K3) ≠ 0 := by exact_mod_cast hb
    have hζ : ζ₃ = ((-(a : ℚ) / b : ℚ) : K3) := by
      push_cast
      field_simp
      linear_combination hK
    have := zeta3_sq
    rw [hζ] at this
    have h' : ((-(a : ℚ) / b) ^ 2 + (-(a : ℚ) / b) + 1 : ℚ) = 0 := by exact_mod_cast this
    nlinarith [sq_nonneg (-(a : ℚ) / b + 1 / 2)]
  refine ⟨?_, hb⟩
  rw [hb] at hK
  simp at hK
  exact_mod_cast hK

/-- Every element of `𝓞 ℚ(ζ₃)` is `a + bζ₃`. -/
theorem exists_coord (y : 𝓞 K3) : ∃ a b : ℤ, y = (a : 𝓞 K3) + (b : 𝓞 K3) * zInt := by
  let pb := hζ3.integralPowerBasis
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval y
  have hdim : pb.dim = 2 := by
    simp only [pb, IsPrimitiveRoot.integralPowerBasis_dim]; decide
  have hf1 : f.natDegree ≤ 1 := by omega
  obtain ⟨a, b, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hf1
  refine ⟨b, a, ?_⟩
  rw [hf]
  simp only [map_add, map_mul, Polynomial.aeval_X,
    IsPrimitiveRoot.integralPowerBasis_gen, pb, zInt, eq_intCast, map_intCast]
  ring

theorem coord_eq (a b c d : ℤ)
    (h : (a : 𝓞 K3) + (b : 𝓞 K3) * zInt = (c : 𝓞 K3) + (d : 𝓞 K3) * zInt) : a = c ∧ b = d := by
  have := coord_eq_zero (a - c) (b - d) (by push_cast; linear_combination h)
  omega

theorem dvd_iff_coord (n a b : ℤ) :
    (n : 𝓞 K3) ∣ (a : 𝓞 K3) + (b : 𝓞 K3) * zInt ↔ n ∣ a ∧ n ∣ b := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, d, rfl⟩ := exists_coord y
    have := coord_eq a b (n * c) (n * d) (by rw [hy]; push_cast; ring)
    exact ⟨⟨c, this.1⟩, ⟨d, this.2⟩⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    exact ⟨(c : 𝓞 K3) + (d : 𝓞 K3) * zInt, by push_cast; ring⟩

theorem not_prime_three_O3 : ¬ Prime (3 : 𝓞 K3) := by
  intro h
  -- `λ = ζ − 1`, `λ² = −3ζ`
  have hl : (3 : 𝓞 K3) ∣ (zInt - 1) * (zInt - 1) :=
    ⟨-zInt, by linear_combination zInt_sq⟩
  have h1 := h.dvd_or_dvd hl
  have h2 : ¬ ((3 : ℤ) : 𝓞 K3) ∣ ((-1 : ℤ) : 𝓞 K3) + ((1 : ℤ) : 𝓞 K3) * zInt := by
    rw [dvd_iff_coord]; omega
  apply h2
  have e : ((-1 : ℤ) : 𝓞 K3) + ((1 : ℤ) : 𝓞 K3) * zInt = zInt - 1 := by push_cast; ring
  rw [e]
  rcases h1 with h1 | h1 <;> exact_mod_cast h1

theorem parity_lemma : ∀ a b c d : ZMod 2, a * c - b * d = 0 → a * d + b * c - b * d = 0 →
    (a = 0 ∧ b = 0) ∨ (c = 0 ∧ d = 0) := by decide

theorem prime_two_O3 : Prime (2 : 𝓞 K3) := by
  refine ⟨two_ne_zero, ?_, ?_⟩
  · intro hu
    have : ((2 : ℤ) : 𝓞 K3) ∣ ((1 : ℤ) : 𝓞 K3) + ((0 : ℤ) : 𝓞 K3) * zInt := by
      have : (2 : 𝓞 K3) ∣ 1 := hu.dvd
      push_cast; simpa using this
    rw [dvd_iff_coord] at this; omega
  · intro x y hxy
    obtain ⟨a, b, rfl⟩ := exists_coord x
    obtain ⟨c, d, rfl⟩ := exists_coord y
    have hprod : ((a : 𝓞 K3) + (b : 𝓞 K3) * zInt) * ((c : 𝓞 K3) + (d : 𝓞 K3) * zInt) =
        ((a * c - b * d : ℤ) : 𝓞 K3) + ((a * d + b * c - b * d : ℤ) : 𝓞 K3) * zInt := by
      push_cast; linear_combination (b : 𝓞 K3) * d * zInt_sq
    rw [hprod, show (2 : 𝓞 K3) = ((2 : ℤ) : 𝓞 K3) by norm_num, dvd_iff_coord] at hxy
    rw [show (2 : 𝓞 K3) = ((2 : ℤ) : 𝓞 K3) by norm_num, dvd_iff_coord, dvd_iff_coord]
    obtain ⟨h1, h2⟩ := hxy
    have e : ∀ n : ℤ, (2 : ℤ) ∣ n ↔ ((n : ZMod 2) = 0) := fun n => by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num
    simp only [e] at h1 h2 ⊢
    push_cast at h1 h2
    exact parity_lemma _ _ _ _ h1 h2

theorem inertCount6_K3 : inertCount6 K3 = 1 := by
  unfold inertCount6
  have h2 : (Ideal.span {(2 : 𝓞 K3)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact prime_two_O3
  have h3 : ¬ (Ideal.span {(3 : 𝓞 K3)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact not_prime_three_O3
  simp [h2, h3]

/-- `R₃ = 𝓞 ℚ(ζ₃)` as a subring. -/
abbrev R3 : Subring K3 := (integralClosure ℤ K3).toSubring

theorem conductor_R3 : conductor R3 = 1 := AddSubgroup.relIndex_self _

theorem pic_R3 : Nat.card (CommRing.Pic R3) = 1 := by
  have e : 𝓞 K3 ≃+* R3 := RingEquiv.refl _
  have : IsPrincipalIdealRing (𝓞 K3) := IsCyclotomicExtension.Rat.three_pid K3
  have : IsPrincipalIdealRing R3 := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  have : Subsingleton (CommRing.Pic R3) := inferInstance
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩

end Pi0X6
