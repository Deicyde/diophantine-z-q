import ZInQKernel.Contrib.TYZGenus.RingClass
import ZInQKernel.RouteK.Redei.FourRank
open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory

namespace ZInQ.Contrib.TYZGenus.RingClass

open ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei

section Arith
variable {d : ℕ} [NeZero d]

theorem sqrtNeg_eq : sqrtNeg d = omegaO d := rfl

theorem sqrtNeg_mul_self : sqrtNeg d * sqrtNeg d = -(d : 𝓞 (QNeg d)) := omegaO_sq d

theorem coe_sqrtNeg : ((sqrtNeg d : 𝓞 (QNeg d)) : QNeg d) = QuadraticAlgebra.omega := rfl

/-- `2 re z ∈ ℤ` for `z ∈ 𝓞_K`. -/
theorem exists_two_re (z : 𝓞 (QNeg d)) : ∃ m : ℤ, 2 * (z : QNeg d).re = m := by
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := d)
  refine exists_int_of_coe_eq_algebraMap (z + σ • z) _ ?_
  have h1 : ((z + σ • z : 𝓞 (QNeg d)) : QNeg d) = (z : QNeg d) + star (z : QNeg d) := by
    rw [← conj_apply σ hσ]
    simp [RingOfIntegers.coe_eq_algebraMap]
  rw [h1, ← QuadraticAlgebra.algebraMap_trace_eq_add_star, QuadraticAlgebra.trace_def]
  simp

/-- `re² + d im² ∈ ℤ` for `z ∈ 𝓞_K`; it is the norm. -/
theorem normZ_eq_re_im (z : 𝓞 (QNeg d)) :
    ((Algebra.norm ℤ z : ℤ) : ℚ) = (z : QNeg d).re ^ 2 + d * (z : QNeg d).im ^ 2 := by
  rw [← algNorm_coe, algNorm_eq d, QuadraticAlgebra.norm_def]
  ring

theorem normZ_unit (u : (𝓞 (QNeg d))ˣ) : Algebra.norm ℤ (u : 𝓞 (QNeg d)) = 1 := by
  have h := IsUnit.map (Algebra.norm ℤ) u.isUnit
  rcases Int.isUnit_iff.1 h with h | h
  · exact h
  · have := normZ_nonneg (n := d) (u : 𝓞 (QNeg d)); omega

/-- For `d ≡ 5 (mod 8)` the units of `𝓞_{K_d}` are `±1`. -/
theorem unit_eq (hd : d % 8 = 5) (u : (𝓞 (QNeg d))ˣ) :
    (u : 𝓞 (QNeg d)) = 1 ∨ (u : 𝓞 (QNeg d)) = -1 := by
  obtain ⟨m, hm⟩ := exists_two_re (u : 𝓞 (QNeg d))
  obtain ⟨k, hk⟩ := exists_two_re ((u : 𝓞 (QNeg d)) * sqrtNeg d)
  have hN := normZ_eq_re_im (u : 𝓞 (QNeg d))
  rw [normZ_unit] at hN
  set x := ((u : 𝓞 (QNeg d)) : QNeg d).re
  set y := ((u : 𝓞 (QNeg d)) : QNeg d).im
  have hre : (((u : 𝓞 (QNeg d)) * sqrtNeg d : 𝓞 (QNeg d)) : QNeg d).re = -(d : ℚ) * y := by
    simp [RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg, y]
  rw [hre] at hk
  have hd0 : (0 : ℤ) < d := by have := NeZero.ne d; omega
  have hZ : (d : ℤ) * m ^ 2 + k ^ 2 = 4 * d := by
    have : (d : ℚ) * (m : ℚ) ^ 2 + (k : ℚ) ^ 2 = 4 * d := by
      rw [← hm, ← hk]; linear_combination (4 * (d : ℚ)) * hN.symm
    exact_mod_cast this
  have hm2 : m ^ 2 ≤ 4 := by
    by_contra h; push Not at h; nlinarith [sq_nonneg k]
  have hmlo : -2 ≤ m := by nlinarith [sq_nonneg (m + 2)]
  have hmhi : m ≤ 2 := by nlinarith [sq_nonneg (m - 2)]
  have hd8 : ((d : ℕ) : ZMod 8) = 5 := by
    rw [← ZMod.natCast_mod, hd]; rfl
  have hd32 : ((d : ℕ) : ZMod 32) = 5 ∨ ((d : ℕ) : ZMod 32) = 13 ∨ ((d : ℕ) : ZMod 32) = 21 ∨
      ((d : ℕ) : ZMod 32) = 29 := by
    rw [← ZMod.natCast_mod]
    have h32 : d % 32 = 5 ∨ d % 32 = 13 ∨ d % 32 = 21 ∨ d % 32 = 29 := by omega
    rcases h32 with h | h | h | h <;> rw [h] <;> simp
  have k3 : ∀ a : ZMod 8, a ^ 2 ≠ 3 * 5 := by decide
  have k4 : ∀ a b : ZMod 32, (b = 5 ∨ b = 13 ∨ b = 21 ∨ b = 29) → a ^ 2 ≠ 4 * b := by decide
  have hu : ∀ e : ℚ, (e = 1 ∨ e = -1) → x = e → y = 0 →
      (u : 𝓞 (QNeg d)) = 1 ∨ (u : 𝓞 (QNeg d)) = -1 := by
    rintro e (rfl | rfl) hx hy
    · left; apply RingOfIntegers.ext; ext
      · change x = _; rw [hx]; simp only [map_neg, map_one, QuadraticAlgebra.re_neg]; rfl
      · change y = _; rw [hy]; simp only [map_neg, map_one, QuadraticAlgebra.im_neg, neg_zero]; rfl
    · right; apply RingOfIntegers.ext; ext
      · change x = _; rw [hx]; simp only [map_neg, map_one, QuadraticAlgebra.re_neg]; rfl
      · change y = _; rw [hy]; simp only [map_neg, map_one, QuadraticAlgebra.im_neg, neg_zero]; rfl
  have hk0 : ∀ mm : ℤ, (mm = 2 ∨ mm = -2) → m = mm → k = 0 := by
    rintro mm (rfl | rfl) rfl <;> nlinarith [sq_nonneg k]
  rcases (show m = -2 ∨ m = -1 ∨ m = 0 ∨ m = 1 ∨ m = 2 by omega) with h | h | h | h | h
  · have hkz := hk0 _ (Or.inr rfl) h
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne d
    refine hu (-1) (Or.inr rfl) ?_ ?_
    · rw [h] at hm; push_cast at hm; linarith
    · rw [hkz] at hk; push_cast at hk
      have : (d : ℚ) * y = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hdq
  · exfalso
    have : k ^ 2 = 3 * (d : ℤ) := by subst h; linarith
    have h8 := congrArg (fun t : ℤ => (t : ZMod 8)) this
    push_cast at h8; rw [hd8] at h8; exact k3 _ h8
  · exfalso
    have : k ^ 2 = 4 * (d : ℤ) := by subst h; linarith
    have h32 := congrArg (fun t : ℤ => (t : ZMod 32)) this
    push_cast at h32; exact k4 _ _ hd32 h32
  · exfalso
    have : k ^ 2 = 3 * (d : ℤ) := by subst h; linarith
    have h8 := congrArg (fun t : ℤ => (t : ZMod 8)) this
    push_cast at h8; rw [hd8] at h8; exact k3 _ h8
  · have hkz := hk0 _ (Or.inl rfl) h
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne d
    refine hu 1 (Or.inl rfl) ?_ ?_
    · rw [h] at hm; push_cast at hm; linarith
    · rw [hkz] at hk; push_cast at hk
      have : (d : ℚ) * y = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hdq
theorem alpha_mul_conj : alpha d * (3 - 2 * sqrtNeg d) + 4 * (-(2 + (d : 𝓞 (QNeg d)))) = 1 := by
  unfold alpha; linear_combination (-4 : 𝓞 (QNeg d)) * sqrtNeg_mul_self (d := d)

theorem alpha_sq : alpha d ^ 2 = (((9 - 4 * d : ℤ)) : 𝓞 (QNeg d)) + 4 * (3 * sqrtNeg d) := by
  unfold alpha; push_cast; linear_combination (4 : 𝓞 (QNeg d)) * sqrtNeg_mul_self (d := d)

end Arith

theorem natCast_mul_mem_conductor (K : Type) [Field K] [NumberField K] (f : ℕ) [NeZero f]
    (y : 𝓞 K) : (f : 𝓞 K) * y ∈ (conductorOrder K f).conductor := by
  rw [NumberFieldOrder.mem_conductor_iff]
  intro z
  exact ⟨0, y * z, by simp only [map_mul, map_natCast, Int.cast_zero, zero_add]; ring⟩

section Sigma
variable {d : ℕ} [NeZero d]

theorem alphaIdeal_mem :
    Ideal.span {alpha d} ∈ integralIdealsPrimeTo (O4 d).conductorModulus := by
  rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff_sup_eq_top,
    conductorModulus_finitePart]
  have key := alpha_mul_conj (d := d)
  refine ⟨?_, ?_⟩
  · intro h
    rw [Ideal.span_singleton_eq_bot] at h
    rw [h, zero_mul, zero_add] at key
    have h1 : ((4 * (-(2 + (d : ℤ))) : ℤ) : 𝓞 (QNeg d)) = ((1 : ℤ) : 𝓞 (QNeg d)) := by
      push_cast; exact key
    have := intCast_injective (n := d) h1
    omega
  · rw [Ideal.eq_top_iff_one, ← key]
    refine Ideal.add_mem _ (Ideal.mem_sup_left
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))) (Ideal.mem_sup_right ?_)
    simpa using natCast_mul_mem_conductor (QNeg d) 4 (-(2 + (d : 𝓞 (QNeg d))))

theorem sigmaClass_eq : sigmaClass d = (O4 d).picClass ⟨_, alphaIdeal_mem⟩ := by
  unfold sigmaClass; rw [dite_eq_left alphaIdeal_mem]

theorem sigmaClass_sq : sigmaClass d ^ 2 = 1 := by
  rw [sigmaClass_eq, ← map_pow, picClass_eq_one_iff]
  refine ⟨alpha d ^ 2, ?_, ?_⟩
  · rw [mem_toRingOfIntegers, alpha_sq]
    exact ⟨9 - 4 * d, 3 * sqrtNeg d, by simp only [map_add, map_mul, map_intCast, map_ofNat]; push_cast; ring⟩
  · rw [SubmonoidClass.coe_pow, Ideal.span_singleton_pow]

/-- `±(3 + 2√−d) ∉ ℤ + 4𝓞_K` for `d ≡ 5 (mod 8)`. -/
theorem not_mem_O4 (hd : d % 8 = 5) (s : ℤ) (hs : s = 1 ∨ s = -1) (a : ℤ) (z : 𝓞 (QNeg d)) :
    (s : QNeg d) * ((alpha d : 𝓞 (QNeg d)) : QNeg d) ≠ a + 4 * (z : QNeg d) := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  simp [alpha, RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg, map_ofNat, QuadraticAlgebra.re_ofNat,
    QuadraticAlgebra.im_ofNat] at him
  obtain ⟨j, hj⟩ := exists_two_re z
  have hN := normZ_eq_re_im z
  have hz2 : (z : QNeg d).im ^ 2 = 1 / 4 := by
    rcases hs with rfl | rfl <;> push_cast at him <;> nlinarith
  have h4 : (j : ℚ) ^ 2 + d = 4 * (Algebra.norm ℤ z : ℤ) := by
    rw [← hj, hN, hz2]; ring
  have h4' : j ^ 2 + (d : ℤ) = 4 * Algebra.norm ℤ z := by exact_mod_cast h4
  have hm := congrArg (fun t : ℤ => (t : ZMod 4)) h4'
  push_cast at hm
  have hd4 : ((d : ℕ) : ZMod 4) = 1 := by
    rw [← ZMod.natCast_mod, show d % 4 = 1 by omega]; rfl
  rw [hd4, show (4 : ZMod 4) = 0 from rfl, zero_mul] at hm
  generalize (j : ZMod 4) = b at hm
  revert b; decide

theorem sigmaClass_ne_one (hd : d % 8 = 5) : sigmaClass d ≠ 1 := by
  rw [sigmaClass_eq]
  intro h
  rw [picClass_eq_one_iff] at h
  obtain ⟨β, hβ, hJ⟩ := h
  rw [Ideal.span_singleton_eq_span_singleton] at hJ
  obtain ⟨u, hu⟩ := hJ
  rw [mem_toRingOfIntegers] at hβ
  obtain ⟨a, z, hz⟩ := hβ
  rw [← hu] at hz
  rcases unit_eq hd u with h1 | h1 <;> rw [h1] at hz
  · exact not_mem_O4 hd 1 (Or.inl rfl) a z (by simpa using hz)
  · exact not_mem_O4 hd (-1) (Or.inr rfl) a z (by simpa using hz)

theorem orderOf_sigmaClass (hd : d % 8 = 5) : orderOf (sigmaClass d) = 2 :=
  orderOf_eq_prime sigmaClass_sq (sigmaClass_ne_one hd)

end Sigma

end ZInQ.Contrib.TYZGenus.RingClass
#print axioms ZInQ.Contrib.TYZGenus.RingClass.orderOf_sigmaClass
