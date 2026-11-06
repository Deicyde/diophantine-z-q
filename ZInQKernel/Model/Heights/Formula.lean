import ZInQKernel.Model.Heights.XHeight

/-!
# The height of a fraction in `ℤ[√2]`

Blueprint: `model/heights/x-height-formula.md`.

For `a, b ∈ ℤ[s]`, `b ≠ 0`, with greatest common divisor `g`,
`h(a/b) = ½ (log max(|σ₊a|, |σ₊b|) + log max(|σ₋a|, |σ₋b|) - log |N(g)|)`.

The two infinite places of `K₀` are `w₊ = |σ₊(·)|` and `w₋ = |σ₋(·)|`, both real: they are distinct
and their multiplicities add up to `[K₀ : ℚ] = 2`. At the finite places, the maximum of
`|a|_v, |b|_v` for coprime `a, b` has product `1`: this is Mathlib's
`absNorm_mul_finprod_finitePlace_eq_one` for the unit ideal `(a, b) = 𝓞 K₀`.
-/

namespace ZInQ

open NumberField Height QuadraticAlgebra

/-! ### The infinite places of `K₀` -/

/-- `σ₊` as a complex embedding. -/
noncomputable def cembPlus : K0 →+* ℂ := Complex.ofRealHom.comp K0.embPlus
/-- `σ₋` as a complex embedding. -/
noncomputable def cembMinus : K0 →+* ℂ := Complex.ofRealHom.comp K0.embMinus

/-- The infinite place `w₊ = |σ₊(·)|`. -/
noncomputable def wPlus : InfinitePlace K0 := InfinitePlace.mk cembPlus
/-- The infinite place `w₋ = |σ₋(·)|`. -/
noncomputable def wMinus : InfinitePlace K0 := InfinitePlace.mk cembMinus

theorem wPlus_apply (x : K0) : wPlus x = |K0.embPlus x| := by
  rw [wPlus, InfinitePlace.apply, cembPlus, RingHom.comp_apply, Complex.ofRealHom_eq_coe,
    Complex.norm_real, Real.norm_eq_abs]

theorem wMinus_apply (x : K0) : wMinus x = |K0.embMinus x| := by
  rw [wMinus, InfinitePlace.apply, cembMinus, RingHom.comp_apply, Complex.ofRealHom_eq_coe,
    Complex.norm_real, Real.norm_eq_abs]

theorem one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem wPlus_ne_wMinus : wPlus ≠ wMinus := by
  intro h
  have := congrArg (fun w : InfinitePlace K0 => w epsilon) h
  simp only [wPlus_apply, wMinus_apply, K0.embPlus_apply, K0.embMinus_apply, epsilon,
    Rat.cast_one, one_mul] at this
  have h1 := one_lt_sqrt_two
  rw [abs_of_pos (by linarith), abs_of_neg (by linarith)] at this
  linarith

open Classical in
/-- The infinite places of `K₀` are exactly `w₊ ≠ w₋`, both of multiplicity one. -/
theorem infinitePlace_K0 :
    (Finset.univ : Finset (InfinitePlace K0)) = {wPlus, wMinus} ∧ wPlus.mult = 1 ∧
      wMinus.mult = 1 := by
  classical
  have hsum : ∑ v : InfinitePlace K0, v.mult = 2 := by
    rw [InfinitePlace.sum_mult_eq, finrank_K0]
  set S : Finset (InfinitePlace K0) := {wPlus, wMinus}
  have hS : S ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_sdiff hS, Finset.sum_pair wPlus_ne_wMinus] at hsum
  have hcard : (Finset.univ \ S).card • 1 ≤ ∑ v ∈ Finset.univ \ S, v.mult :=
    Finset.card_nsmul_le_sum _ _ _ fun v _ => InfinitePlace.mult_pos
  rw [smul_eq_mul, mul_one] at hcard
  have h1 : 0 < wPlus.mult := InfinitePlace.mult_pos
  have h2 : 0 < wMinus.mult := InfinitePlace.mult_pos
  refine ⟨?_, by omega, by omega⟩
  have : (Finset.univ \ S).card = 0 := by omega
  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at this
  exact Finset.Subset.antisymm this hS

open Classical in
theorem prod_infinitePlace_K0 {M : Type*} [CommMonoid M] (g : InfinitePlace K0 → M) :
    ∏ v : InfinitePlace K0, g v ^ v.mult = g wPlus * g wMinus := by
  obtain ⟨hu, h1, h2⟩ := infinitePlace_K0
  rw [hu, Finset.prod_pair wPlus_ne_wMinus, h1, h2, pow_one, pow_one]

/-! ### Elements of `ℤ[s]` in the ring of integers -/

theorem isIntegral_toK0 (z : Zs) : IsIntegral ℤ (Zs.toK0 z) :=
  (Algebra.IsIntegral.isIntegral z).map Zs.toK0.toIntAlgHom

/-- `ℤ[s] → 𝓞 K₀`. -/
noncomputable def toOK (z : Zs) : 𝓞 K0 :=
  ⟨Zs.toK0 z, (mem_integralClosure_iff ℤ K0).mpr (isIntegral_toK0 z)⟩

@[simp] theorem coe_toOK (z : Zs) : ((toOK z : 𝓞 K0) : K0) = Zs.toK0 z := rfl

theorem iSup_fin_two_real (g : Fin 2 → ℝ) : ⨆ i, g i = max (g 0) (g 1) := by
  apply le_antisymm
  · exact ciSup_le fun i => by fin_cases i <;> simp
  · exact max_le (le_ciSup (Finite.bddAbove_range g) 0) (le_ciSup (Finite.bddAbove_range g) 1)

/-- For coprime `a, b ∈ ℤ[s]`, `∏_{v finite} max(|a|_v, |b|_v) = 1`. -/
theorem finprod_finitePlace_eq_one {a b : Zs} (hab : IsCoprime a b) :
    ∏ᶠ v : FinitePlace K0, ⨆ i, v (![Zs.toK0 a, Zs.toK0 b] i) = 1 := by
  have hne : ![toOK a, toOK b] ≠ 0 := by
    intro h
    have ha : toOK a = 0 := congrFun h 0
    have hb : toOK b = 0 := congrFun h 1
    have ha' : a = 0 := Zs.toK0_injective (by simpa using congrArg (fun z : 𝓞 K0 => (z : K0)) ha)
    have hb' : b = 0 := Zs.toK0_injective (by simpa using congrArg (fun z : 𝓞 K0 => (z : K0)) hb)
    subst ha' hb'
    exact not_isCoprime_zero_zero hab
  have h := absNorm_mul_finprod_finitePlace_eq_one hne
  have hspan : Ideal.span (Set.range ![toOK a, toOK b]) = ⊤ := by
    obtain ⟨u, v, huv⟩ := hab
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 K0) = toOK u * toOK a + toOK v * toOK b := by
      apply RingOfIntegers.ext
      show ((1 : 𝓞 K0) : K0) = ((toOK u : K0) * (toOK a : K0) + (toOK v : K0) * (toOK b : K0))
      simp only [coe_toOK]
      rw [← map_mul, ← map_mul, ← map_add, huv, map_one]; rfl
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, rfl⟩))
  rw [hspan, Ideal.absNorm_top, Nat.cast_one, one_mul] at h
  rw [← h]
  congr 1; ext v; congr 1; ext i; fin_cases i <;> rfl

/-! ### The formula -/

/-- For coprime `a, b ∈ ℤ[s]` (`b ≠ 0`): the multiplicative height of `a / b` (relative to `K₀`) is
`max(|σ₊a|, |σ₊b|) · max(|σ₋a|, |σ₋b|)`. -/
theorem mulHeight₁_div_of_isCoprime {a b : Zs} (hab : IsCoprime a b) :
    mulHeight₁ (Zs.toK0 a / Zs.toK0 b) =
      max |K0.embPlus (Zs.toK0 a)| |K0.embPlus (Zs.toK0 b)| *
        max |K0.embMinus (Zs.toK0 a)| |K0.embMinus (Zs.toK0 b)| := by
  have hne : ![Zs.toK0 a, Zs.toK0 b] ≠ 0 := by
    intro h
    have ha : Zs.toK0 a = 0 := congrFun h 0
    have hb : Zs.toK0 b = 0 := congrFun h 1
    rw [← map_zero Zs.toK0] at ha hb
    rw [Zs.toK0_injective ha, Zs.toK0_injective hb] at hab
    exact not_isCoprime_zero_zero hab
  rw [mulHeight₁_div_eq_mulHeight, NumberField.mulHeight_eq hne, finprod_finitePlace_eq_one hab, mul_one,
    prod_infinitePlace_K0, iSup_fin_two_real, iSup_fin_two_real]
  simp [wPlus_apply, wMinus_apply]

theorem max_abs_pos_of_isCoprime (σ : K0 →+* ℝ) {a b : Zs} (hab : IsCoprime a b) :
    0 < max |σ (Zs.toK0 a)| |σ (Zs.toK0 b)| := by
  rcases eq_or_ne b 0 with rfl | hb
  · have ha : IsUnit a := isCoprime_zero_right.mp hab
    have : a ≠ 0 := ha.ne_zero
    have : σ (Zs.toK0 a) ≠ 0 := by
      rw [map_ne_zero, Ne, ← map_zero Zs.toK0]; exact fun h => this (Zs.toK0_injective h)
    exact lt_max_of_lt_left (abs_pos.mpr this)
  · have : σ (Zs.toK0 b) ≠ 0 := by
      rw [map_ne_zero, Ne, ← map_zero Zs.toK0]; exact fun h => hb (Zs.toK0_injective h)
    exact lt_max_of_lt_right (abs_pos.mpr this)

/-- `|N(g)| = |σ₊ g| · |σ₋ g|`. -/
theorem abs_norm_eq (g : Zs) :
    |((QuadraticAlgebra.norm g : ℤ) : ℝ)| = |K0.embPlus (Zs.toK0 g)| * |K0.embMinus (Zs.toK0 g)| := by
  rw [← abs_mul, ← K0.norm_eq_embPlus_mul_embMinus, Zs.norm_toK0]; push_cast; rfl

theorem max_abs_mul (x y z : ℝ) : max |x * y| |x * z| = |x| * max |y| |z| := by
  simp only [abs_mul]
  exact (mul_max_of_nonneg _ _ (abs_nonneg _)).symm

/-- **The height of a fraction.** For `a, b ∈ ℤ[s]` with `b ≠ 0` and a greatest common divisor
`g` of `a` and `b` (a common divisor divisible by every common divisor):
`h(a/b) = ½ (log max(|σ₊a|, |σ₊b|) + log max(|σ₋a|, |σ₋b|) - log |N(g)|)`. -/
theorem hK0_div (a b : Zs) (hb : b ≠ 0) (g : Zs) (hga : g ∣ a) (hgb : g ∣ b)
    (hg : ∀ d, d ∣ a → d ∣ b → d ∣ g) :
    hK0 (Zs.toK0 a / Zs.toK0 b) =
      (Real.log (max |K0.embPlus (Zs.toK0 a)| |K0.embPlus (Zs.toK0 b)|) +
        Real.log (max |K0.embMinus (Zs.toK0 a)| |K0.embMinus (Zs.toK0 b)|) -
        Real.log |((QuadraticAlgebra.norm g : ℤ) : ℝ)|) / 2 := by
  obtain ⟨a', rfl⟩ := hga
  obtain ⟨b', rfl⟩ := hgb
  have hg0 : g ≠ 0 := by rintro rfl; apply hb; rw [zero_mul]
  have hcop : IsCoprime a' b' := by
    apply IsRelPrime.isCoprime
    intro d hda hdb
    have h1 : g * d ∣ g := hg _ (mul_dvd_mul_left g hda) (mul_dvd_mul_left g hdb)
    obtain ⟨e, he⟩ := h1
    have : g * 1 = g * (d * e) := by rw [mul_one, ← mul_assoc]; exact he
    exact IsUnit.of_mul_eq_one (b := e) (mul_left_cancel₀ hg0 this).symm
  have hG : Zs.toK0 g ≠ 0 := by
    rw [Ne, ← map_zero Zs.toK0]; exact fun h => hg0 (Zs.toK0_injective h)
  have hdiv : Zs.toK0 (g * a') / Zs.toK0 (g * b') = Zs.toK0 a' / Zs.toK0 b' := by
    rw [map_mul, map_mul, mul_div_mul_left _ _ hG]
  rw [hK0, hdiv, logHeight₁_eq_log_mulHeight₁, mulHeight₁_div_of_isCoprime hcop]
  simp only [map_mul]
  rw [max_abs_mul, max_abs_mul, abs_norm_eq]
  have hp := max_abs_pos_of_isCoprime K0.embPlus hcop
  have hm := max_abs_pos_of_isCoprime K0.embMinus hcop
  have hgp : 0 < |K0.embPlus (Zs.toK0 g)| := abs_pos.mpr ((map_ne_zero _).mpr hG)
  have hgm : 0 < |K0.embMinus (Zs.toK0 g)| := abs_pos.mpr ((map_ne_zero _).mpr hG)
  rw [Real.log_mul hp.ne' hm.ne', Real.log_mul hgp.ne' hp.ne', Real.log_mul hgm.ne' hm.ne',
    Real.log_mul hgp.ne' hgm.ne']
  ring

/-- For coprime `a, b ∈ ℤ[s]`: `exp(2 h(a/b)) = max(|σ₊a|, |σ₊b|) · max(|σ₋a|, |σ₋b|)`. -/
theorem exp_two_mul_hK0_div_of_isCoprime {a b : Zs} (hab : IsCoprime a b) :
    Real.exp (2 * hK0 (Zs.toK0 a / Zs.toK0 b)) =
      max |K0.embPlus (Zs.toK0 a)| |K0.embPlus (Zs.toK0 b)| *
        max |K0.embMinus (Zs.toK0 a)| |K0.embMinus (Zs.toK0 b)| := by
  rw [hK0, mul_div_cancel₀ _ two_ne_zero, logHeight₁_eq_log_mulHeight₁,
    Real.exp_log (by linarith [one_le_mulHeight₁ (Zs.toK0 a / Zs.toK0 b)]),
    mulHeight₁_div_of_isCoprime hab]

/-- For coprime `a, b ∈ ℤ[s]`:
`h(a/b) = ½ (log max(|σ₊a|, |σ₊b|) + log max(|σ₋a|, |σ₋b|))`. -/
theorem hK0_div_of_isCoprime {a b : Zs} (hab : IsCoprime a b) :
    hK0 (Zs.toK0 a / Zs.toK0 b) =
      (Real.log (max |K0.embPlus (Zs.toK0 a)| |K0.embPlus (Zs.toK0 b)|) +
        Real.log (max |K0.embMinus (Zs.toK0 a)| |K0.embMinus (Zs.toK0 b)|)) / 2 := by
  rw [hK0, logHeight₁_eq_log_mulHeight₁, mulHeight₁_div_of_isCoprime hab,
    Real.log_mul (max_abs_pos_of_isCoprime _ hab).ne' (max_abs_pos_of_isCoprime _ hab).ne']

/-- For a rational number `r`, `h(r) = log max(|num r|, den r)`. -/
theorem hK0_ratCast (r : ℚ) : hK0 (r : K0) = Real.log (max |(r.num : ℝ)| (r.den : ℝ)) := by
  have hcop : IsCoprime (r.num : Zs) (r.den : Zs) := by
    obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr (by
      show Nat.gcd r.num.natAbs (r.den : ℤ).natAbs = 1; simpa using r.reduced)
    refine ⟨u, v, ?_⟩
    have := congrArg (Int.cast : ℤ → Zs) huv
    push_cast at this
    exact this
  have hr : (r : K0) = Zs.toK0 (r.num : Zs) / Zs.toK0 (r.den : Zs) := by
    rw [map_intCast, map_natCast, ← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div,
      Rat.num_div_den]
  rw [hr, hK0_div_of_isCoprime hcop]
  simp only [map_intCast, map_natCast, Nat.abs_cast]
  ring

end ZInQ
