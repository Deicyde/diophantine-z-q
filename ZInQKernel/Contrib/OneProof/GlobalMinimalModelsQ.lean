import ZInQKernel.Contrib.OneProof.MillerRankMinimal

set_option autoImplicit false

open WeierstrassCurve NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero

namespace ZInQ.Manuscript.GlobalMinimalAux

/-! ## Generic facts on integral Weierstrass equations -/

/-- An integral variable change over the base ring preserves integrality. -/
private theorem isIntegral_baseChange_smul {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    {W : WeierstrassCurve K} (hW : IsIntegral R W) (C : VariableChange R) :
    IsIntegral R (C.baseChange K • W) := by
  obtain ⟨W₀, rfl⟩ := hW.integral
  exact ⟨⟨C • W₀, (map_variableChange W₀ C (algebraMap R K))⟩⟩

/-- A pure scaling whose inverse scale is integral preserves integrality. -/
private theorem isIntegral_scale {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    {W : WeierstrassCurve K} (hW : IsIntegral R W) (D : VariableChange K)
    (hr : D.r = 0) (hs : D.s = 0) (ht : D.t = 0) (k : R)
    (hk : algebraMap R K k = ↑D.u⁻¹) : IsIntegral R (D • W) := by
  obtain ⟨W₀, rfl⟩ := hW.integral
  refine isIntegral_of_exists_lift R ⟨k * W₀.a₁, ?_⟩ ⟨k ^ 2 * W₀.a₂, ?_⟩ ⟨k ^ 3 * W₀.a₃, ?_⟩
    ⟨k ^ 4 * W₀.a₄, ?_⟩ ⟨k ^ 6 * W₀.a₆, ?_⟩ <;>
  simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, hr, hs, ht, hk, baseChange]

section UIntegral

open Polynomial

variable {R : Type*} [CommRing R] [IsIntegrallyClosed R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] {W W' : WeierstrassCurve K} [IsIntegral R W]
  [IsIntegral R W'] {CK : VariableChange K} (hCK : CK • W = W') {u : R}
  (hu : algebraMap R K u = CK.u)

include hCK hu

private theorem r_integral : ∃ r : R, algebraMap R K r = CK.r := by
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 4 - C (integralModel R W).b₄ * X ^ 2 -
    C (u ^ 6 * (integralModel R W').b₆ + 2 * (integralModel R W).b₆) * X -
    C ((integralModel R W).b₈ - u ^ 8 * (integralModel R W').b₈), by monicity!, ?_⟩
  simp [map_ofNat, hu, ← hCK, integralModel_b₄_eq, integralModel_b₆_eq,
    integralModel_b₈_eq, variableChange_b₆, variableChange_b₈]
  ring1

private theorem s_integral : ∃ s : R, algebraMap R K s = CK.s := by
  rcases r_integral hCK hu with ⟨r, hr⟩
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 2 + C (integralModel R W).a₁ * X +
    C (u ^ 2 * (integralModel R W').a₂ - (integralModel R W).a₂ - 3 * r), by monicity!, ?_⟩
  simp [map_ofNat, hu, hr, ← hCK, integralModel_a₁_eq, integralModel_a₂_eq,
    variableChange_a₂]
  ring1

private theorem t_integral : ∃ t : R, algebraMap R K t = CK.t := by
  rcases r_integral hCK hu with ⟨r, hr⟩
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 2 +
    C ((integralModel R W).a₃ + r * (integralModel R W).a₁) * X +
    C (u ^ 6 * (integralModel R W').a₆ - (integralModel R W).a₆ - r * (integralModel R W).a₄
      - r ^ 2 * (integralModel R W).a₂ - r ^ 3), by monicity!, ?_⟩
  simp [hu, hr, ← hCK, integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq,
    integralModel_a₄_eq, integralModel_a₆_eq, variableChange_a₆]
  ring1

end UIntegral

/-! ## The rational prime attached to a height-one prime of `𝓞 ℚ` -/

section Place

private theorem exp_inv_pow (n : ℕ) :
    (WithZero.exp (-1 : ℤ))⁻¹ ^ n = (WithZero.exp (-(n : ℤ)))⁻¹ := by
  rw [inv_pow, ← WithZero.exp_nsmul]
  simp

private theorem exists_generator (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ π : ℤ, Ideal.span {(π : 𝓞 ℚ)} = v.asIdeal := by
  let e := Rat.ringOfIntegersEquiv
  let J : Ideal ℤ := Ideal.comap e.symm v.asIdeal
  refine ⟨Submodule.IsPrincipal.generator J, ?_⟩
  have h1 : ((Submodule.IsPrincipal.generator J : ℤ) : 𝓞 ℚ) =
      e.symm (Submodule.IsPrincipal.generator J) :=
    (eq_intCast e.symm _).symm
  calc
    _ = Ideal.map e.symm (Ideal.span {Submodule.IsPrincipal.generator J}) := by
      rw [Ideal.map_span, Set.image_singleton, h1]
    _ = v.asIdeal := by
      rw [Ideal.span_singleton_generator]
      exact Ideal.map_comap_of_surjective e.symm e.symm.surjective v.asIdeal

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝕆" => HeightOneSpectrum.adicCompletionIntegers ℚ v

private theorem valued_algebraMap (x : ℚ) :
    Valued.v (algebraMap ℚ 𝕂 x) = v.valuation ℚ x := by
  simp only [algebraMap_adicCompletion, Algebra.algebraMap_self, Function.comp_apply,
    RingHom.id_apply, valuedAdicCompletion_eq_valuation']

private theorem algebraMap_mem_iff (x : ℚ) : algebraMap ℚ 𝕂 x ∈ 𝕆 ↔ v.valuation ℚ x ≤ 1 := by
  rw [mem_adicCompletionIntegers, valued_algebraMap]

private theorem valuation_intCast_le (n : ℤ) : v.valuation ℚ (n : ℚ) ≤ 1 := by
  rw [← map_intCast (algebraMap (𝓞 ℚ) ℚ) n]
  exact v.valuation_le_one _

private theorem w_le_of_valued_le {x y : 𝕂} (hy : y ≠ 0) (h : Valued.v x ≤ Valued.v y) :
    (IsDiscreteValuationRing.maximalIdeal 𝕆).valuation 𝕂 x ≤
      (IsDiscreteValuationRing.maximalIdeal 𝕆).valuation 𝕂 y := by
  have hvy : 0 < Valued.v y := pos_iff_ne_zero.mpr ((Valued.v.ne_zero_iff).mpr hy)
  have hwy : 0 < (IsDiscreteValuationRing.maximalIdeal 𝕆).valuation 𝕂 y :=
    pos_iff_ne_zero.mpr (((IsDiscreteValuationRing.maximalIdeal 𝕆).valuation 𝕂).ne_zero_iff.mpr hy)
  have hdiv : Valued.v (x / y) ≤ 1 := by rw [map_div₀, div_le_one₀ hvy]; exact h
  have hw : (IsDiscreteValuationRing.maximalIdeal 𝕆).valuation 𝕂
      (algebraMap 𝕆 𝕂 ⟨x / y, hdiv⟩) ≤ 1 :=
    valuation_le_one (K := 𝕂) (IsDiscreteValuationRing.maximalIdeal 𝕆) _
  change (IsDiscreteValuationRing.maximalIdeal 𝕆).valuation 𝕂 (x / y) ≤ 1 at hw
  rwa [map_div₀, div_le_one₀ hwy] at hw

variable {π : ℤ} (hπ : Ideal.span {(π : 𝓞 ℚ)} = v.asIdeal)
include hπ

private theorem gen_ne_zero : (π : 𝓞 ℚ) ≠ 0 := by
  intro h
  apply v.ne_bot
  rw [← hπ, h]
  exact Ideal.span_singleton_eq_bot.mpr rfl

private theorem gen_ne_zero' : (π : ℚ) ≠ 0 := by
  intro h0
  exact gen_ne_zero hπ (by rw [Int.cast_eq_zero.mp h0, Int.cast_zero])

private theorem two_le_natAbs : 2 ≤ π.natAbs := by
  have h0 : π ≠ 0 := by rintro rfl; exact gen_ne_zero hπ (by simp)
  have h1 : π.natAbs ≠ 1 := by
    intro h1
    have hu : IsUnit (π : 𝓞 ℚ) := by
      simpa using (Int.isUnit_iff_natAbs_eq.mpr h1).map (Int.castRingHom (𝓞 ℚ))
    apply v.isPrime.ne_top
    rw [← hπ]
    exact Ideal.span_singleton_eq_top.mpr hu
  have := Int.natAbs_ne_zero.mpr h0
  omega

private theorem valuation_gen : v.valuation ℚ (π : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [← map_intCast (algebraMap (𝓞 ℚ) ℚ) π, valuation_of_algebraMap]
  exact v.intValuation_singleton (gen_ne_zero hπ) hπ.symm

private theorem exists_int_of_valuation (n : ℤ) (i : ℕ)
    (h : v.valuation ℚ ((π : ℚ)⁻¹ ^ i * n) ≤ 1) : ∃ m : ℤ, (m : ℚ) = (π : ℚ)⁻¹ ^ i * n := by
  have hπ0 := gen_ne_zero' hπ
  rw [map_mul, map_pow, map_inv₀, valuation_gen hπ, exp_inv_pow,
    inv_mul_le_iff₀ WithZero.exp_pos, mul_one] at h
  have h' : v.intValuation (n : 𝓞 ℚ) ≤ WithZero.exp (-(i : ℤ)) := by
    rwa [← map_intCast (algebraMap (𝓞 ℚ) ℚ) n, valuation_of_algebraMap] at h
  rw [intValuation_le_pow_iff_mem, ← hπ, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at h'
  obtain ⟨a, ha⟩ := h'
  refine ⟨Rat.ringOfIntegersEquiv a, ?_⟩
  have hn : (n : ℚ) = algebraMap (𝓞 ℚ) ℚ a * (π : ℚ) ^ i := by
    rw [← map_intCast (algebraMap (𝓞 ℚ) ℚ) n, ← ha, map_mul, map_pow, map_intCast]
  rw [Rat.ringOfIntegersEquiv_apply_coe, hn, inv_pow, mul_comm, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hπ0), mul_one]

private theorem exists_int_approx {x : 𝕂} (hx : x ∈ 𝕆) (N : ℕ) :
    ∃ m : ℤ, ((m : 𝕂) - x) * ((π : 𝕂)⁻¹) ^ N ∈ 𝕆 := by
  have hπ0 := gen_ne_zero' hπ
  have hϖ : (π : 𝕂) = algebraMap ℚ 𝕂 π := (map_intCast _ _).symm
  have hϖ0 : (π : 𝕂) ≠ 0 := by rw [hϖ]; exact (map_ne_zero _).mpr hπ0
  have hϖmem : (π : 𝕂) ∈ 𝕆 := by rw [hϖ, algebraMap_mem_iff]; exact valuation_intCast_le π
  have hopen : IsOpen {z : 𝕂 | (z - x) * ((π : 𝕂)⁻¹) ^ N ∈ 𝕆} :=
    (Valued.isOpen_valuationSubring 𝕂).preimage
      ((continuous_id.sub continuous_const).mul continuous_const)
  obtain ⟨y, hy⟩ := (denseRange_algebraMap (K := ℚ) (v := v)).exists_mem_open hopen
    ⟨x, by simp⟩
  have hy' : (algebraMap ℚ 𝕂 y - x) * ((π : 𝕂)⁻¹) ^ N ∈ 𝕆 := hy
  have hyR : algebraMap ℚ 𝕂 y ∈ 𝕆 := by
    have : algebraMap ℚ 𝕂 y = x + ((algebraMap ℚ 𝕂 y - x) * ((π : 𝕂)⁻¹) ^ N) * (π : 𝕂) ^ N := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hϖ0, one_pow, mul_one]; ring
    rw [this]
    exact add_mem hx (mul_mem hy' (pow_mem hϖmem N))
  rw [algebraMap_mem_iff] at hyR
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hyR
    (Units.mk0 (WithZero.exp (-(N : ℤ))) WithZero.exp_ne_zero)
  refine ⟨Rat.ringOfIntegersEquiv a, ?_⟩
  have hm : ((Rat.ringOfIntegersEquiv a : ℤ) : 𝕂) = algebraMap ℚ 𝕂 (algebraMap (𝓞 ℚ) ℚ a) := by
    rw [← Rat.ringOfIntegersEquiv_apply_coe, map_intCast]
  have key : (algebraMap ℚ 𝕂 (algebraMap (𝓞 ℚ) ℚ a) - algebraMap ℚ 𝕂 y) *
      ((π : 𝕂)⁻¹) ^ N ∈ 𝕆 := by
    have : (algebraMap ℚ 𝕂 (algebraMap (𝓞 ℚ) ℚ a) - algebraMap ℚ 𝕂 y) * ((π : 𝕂)⁻¹) ^ N =
        algebraMap ℚ 𝕂 ((algebraMap (𝓞 ℚ) ℚ a - y) * ((π : ℚ)⁻¹) ^ N) := by
      rw [hϖ, map_mul, map_sub, map_pow, map_inv₀]
    rw [this, algebraMap_mem_iff, map_mul, map_pow, map_inv₀, valuation_gen hπ, exp_inv_pow]
    have hlt : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ a - y) < WithZero.exp (-(N : ℤ)) := by
      simpa using ha
    exact mul_inv_le_one_of_le₀ hlt.le zero_le
  have : (((Rat.ringOfIntegersEquiv a : ℤ) : 𝕂) - x) * ((π : 𝕂)⁻¹) ^ N =
      (algebraMap ℚ 𝕂 (algebraMap (𝓞 ℚ) ℚ a) - algebraMap ℚ 𝕂 y) * ((π : 𝕂)⁻¹) ^ N +
        (algebraMap ℚ 𝕂 y - x) * ((π : 𝕂)⁻¹) ^ N := by
    rw [hm]; ring
  rw [this]
  exact add_mem key hy'

/-- Improvement at a non-minimal place: a rational change with `u = π` keeps the
equation integral over `ℤ`. -/
private theorem local_improve (W : WeierstrassCurve ℚ) (hW : IsIntegral ℤ W)
    (hmin : ¬ IsMinimal 𝕆 (W.baseChange 𝕂)) :
    ∃ U : VariableChange ℚ, (U.u : ℚ) = π ∧ IsIntegral ℤ (U • W) := by
  have hπ0 := gen_ne_zero' hπ
  have hϖ : (π : 𝕂) = algebraMap ℚ 𝕂 π := (map_intCast _ _).symm
  have hϖ0 : (π : 𝕂) ≠ 0 := by rw [hϖ]; exact (map_ne_zero _).mpr hπ0
  have hϖmem : (π : 𝕂) ∈ 𝕆 := by rw [hϖ, algebraMap_mem_iff]; exact valuation_intCast_le π
  have hvϖ : Valued.v (π : 𝕂) = WithZero.exp (-1 : ℤ) := by
    rw [hϖ, valued_algebraMap, valuation_gen hπ]
  -- the completed equation is integral
  have hWp : IsIntegral 𝕆 (W.baseChange 𝕂) := by
    obtain ⟨W₀, rfl⟩ := hW.integral
    refine isIntegral_of_exists_lift 𝕆 ⟨W₀.a₁, ?_⟩ ⟨W₀.a₂, ?_⟩ ⟨W₀.a₃, ?_⟩ ⟨W₀.a₄, ?_⟩
      ⟨W₀.a₆, ?_⟩ <;> simp [baseChange]
  -- an improving change of variables over the completion
  have h1 : IsIntegral 𝕆 ((1 : VariableChange 𝕂) • W.baseChange 𝕂) := by rwa [one_smul]
  obtain ⟨C, hC, hnle⟩ : ∃ C : VariableChange 𝕂, IsIntegral 𝕆 (C • W.baseChange 𝕂) ∧
      ¬ valuation_Δ_aux 𝕆 (C • W.baseChange 𝕂) ≤
        valuation_Δ_aux 𝕆 ((1 : VariableChange 𝕂) • W.baseChange 𝕂) := by
    by_contra! h
    exact hmin ⟨⟨h1, fun ⦃C⦄ hC _ => h C hC⟩⟩
  have hlt0 := lt_of_not_ge hnle
  have hlt : (valuation_Δ_aux 𝕆 ((1 : VariableChange 𝕂) • W.baseChange 𝕂) : ℤᵐ⁰) <
      (valuation_Δ_aux 𝕆 (C • W.baseChange 𝕂) : ℤᵐ⁰) := hlt0
  have := hWp
  have := hC
  rw [one_smul, valuation_Δ_aux_eq_of_isIntegral 𝕆 (W.baseChange 𝕂),
    valuation_Δ_aux_eq_of_isIntegral 𝕆 (C • W.baseChange 𝕂)] at hlt
  have hΔ0 : (W.baseChange 𝕂).Δ ≠ 0 := by
    intro h0
    rw [variableChange_Δ, h0, mul_zero] at hlt
    exact lt_irrefl _ hlt
  have hv : Valued.v (W.baseChange 𝕂).Δ < Valued.v (C • W.baseChange 𝕂).Δ := by
    by_contra! hle
    exact (not_le.mpr hlt) (w_le_of_valued_le hΔ0 hle)
  have hscale : Valued.v (C • W.baseChange 𝕂).Δ =
      Valued.v (↑C.u⁻¹ : 𝕂) ^ 12 * Valued.v (W.baseChange 𝕂).Δ := by
    rw [variableChange_Δ, map_mul, map_pow]
  have hu_inv : 1 < Valued.v (↑C.u⁻¹ : 𝕂) := by
    by_contra! h
    have : Valued.v (C • W.baseChange 𝕂).Δ ≤ Valued.v (W.baseChange 𝕂).Δ := by
      rw [hscale]; exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le h)
    exact not_le.mpr hv this
  have hu1 : Valued.v (C.u : 𝕂) < 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀] at hu_inv
    by_contra! h
    exact not_le.mpr hu_inv (inv_le_one_of_one_le₀ h)
  have huϖ : Valued.v (C.u : 𝕂) ≤ Valued.v (π : 𝕂) := by
    rw [hvϖ]
    have hne : Valued.v (C.u : 𝕂) ≠ 0 := (Valued.v.ne_zero_iff).mpr C.u.ne_zero
    have heq := WithZero.exp_log hne
    have hlog : WithZero.log (Valued.v (C.u : 𝕂)) < 0 := by
      rw [← WithZero.exp_lt_exp, WithZero.exp_zero, heq]; exact hu1
    rw [← heq, WithZero.exp_le_exp]
    omega
  -- replace `u` by `π`
  have hCu0 : (C.u : 𝕂) ≠ 0 := C.u.ne_zero
  let D : VariableChange 𝕂 := ⟨Units.mk0 ((π : 𝕂) / C.u) (div_ne_zero hϖ0 hCu0), 0, 0, 0⟩
  let C' : VariableChange 𝕂 := ⟨Units.mk0 (π : 𝕂) hϖ0, C.r, C.s, C.t⟩
  have hC'eq : C' = D * C := by
    ext <;> simp [C', D, VariableChange.mul_def, div_mul_cancel₀ _ hCu0]
  have hk : (C.u : 𝕂) / π ∈ 𝕆 := by
    rw [mem_adicCompletionIntegers, map_div₀, div_le_one₀ (by rw [hvϖ]; exact WithZero.exp_pos)]
    exact huϖ
  have hC' : IsIntegral 𝕆 (C' • W.baseChange 𝕂) := by
    rw [hC'eq, mul_smul]
    refine isIntegral_scale hC D rfl rfl rfl ⟨_, hk⟩ ?_
    show (C.u : 𝕂) / π = ((π : 𝕂) / C.u)⁻¹
    rw [inv_div]
  have := hC'
  have hu' : algebraMap 𝕆 𝕂 (π : 𝕆) = (C'.u : 𝕂) := by simp [C']
  obtain ⟨r, hr⟩ := r_integral (W := W.baseChange 𝕂) (rfl : C' • W.baseChange 𝕂 = _) hu'
  obtain ⟨s, hs⟩ := s_integral (W := W.baseChange 𝕂) (rfl : C' • W.baseChange 𝕂 = _) hu'
  obtain ⟨t, ht⟩ := t_integral (W := W.baseChange 𝕂) (rfl : C' • W.baseChange 𝕂 = _) hu'
  have hrmem : C.r ∈ 𝕆 := by
    have := r.2; rwa [show (r : 𝕂) = C.r from hr] at this
  have hsmem : C.s ∈ 𝕆 := by
    have := s.2; rwa [show (s : 𝕂) = C.s from hs] at this
  have htmem : C.t ∈ 𝕆 := by
    have := t.2; rwa [show (t : 𝕂) = C.t from ht] at this
  -- integer approximations
  obtain ⟨mr, hmr⟩ := exists_int_approx hπ hrmem 2
  obtain ⟨ms, hms⟩ := exists_int_approx hπ hsmem 1
  have htmem' : C.t + ((mr : 𝕂) - C.r) * ((π : 𝕂)⁻¹) ^ 2 * C.s * (π : 𝕂) ^ 2 ∈ 𝕆 :=
    add_mem htmem (mul_mem (mul_mem hmr hsmem) (pow_mem hϖmem 2))
  obtain ⟨mt, hmt⟩ := exists_int_approx hπ htmem' 3
  let E₀ : VariableChange 𝕆 := ⟨1, ⟨_, hmr⟩, ⟨_, hms⟩, ⟨_, hmt⟩⟩
  let U : VariableChange ℚ := ⟨Units.mk0 (π : ℚ) hπ0, mr, ms, mt⟩
  have hUE : U.baseChange 𝕂 = E₀.baseChange 𝕂 * C' := by
    refine VariableChange.ext (Units.ext ?_) ?_ ?_ ?_
    · simp [U, E₀, C', VariableChange.baseChange, VariableChange.mul_def]
    · simp [U, E₀, C', VariableChange.baseChange, VariableChange.mul_def]
      field_simp
      ring
    · simp [U, E₀, C', VariableChange.baseChange, VariableChange.mul_def]
      field_simp
      ring
    · simp [U, E₀, C', VariableChange.baseChange, VariableChange.mul_def]
      field_simp
      ring
  have hUW : IsIntegral 𝕆 ((U • W).baseChange 𝕂) := by
    have : (U • W).baseChange 𝕂 = E₀.baseChange 𝕂 • (C' • W.baseChange 𝕂) := by
      rw [← mul_smul, ← hUE]; exact (map_variableChange W U (algebraMap ℚ 𝕂)).symm
    rw [this]; exact isIntegral_baseChange_smul hC' E₀
  -- descend to `ℤ`
  let S : VariableChange ℚ := ⟨Units.mk0 (π : ℚ) hπ0, 0, 0, 0⟩
  let T₀ : VariableChange ℤ := ⟨1, mr, ms, mt⟩
  have hST : U = S * T₀.baseChange ℚ := by
    ext <;> simp [U, S, T₀, VariableChange.mul_def, VariableChange.baseChange]
  obtain ⟨W₁, hW₁⟩ := (isIntegral_baseChange_smul hW T₀).integral
  refine ⟨U, rfl, ?_⟩
  have hUW' : U • W = S • W₁.baseChange ℚ := by rw [hST, mul_smul, hW₁]
  rw [hUW'] at hUW ⊢
  have key : ∀ (i : ℕ) (n : ℤ) (x : ℚ), x = (π : ℚ)⁻¹ ^ i * n →
      (∃ r : 𝕆, algebraMap 𝕆 𝕂 r = algebraMap ℚ 𝕂 x) → ∃ m : ℤ, algebraMap ℤ ℚ m = x := by
    rintro i n x rfl ⟨r, hr⟩
    have hx : algebraMap ℚ 𝕂 ((π : ℚ)⁻¹ ^ i * n) ∈ 𝕆 := by rw [← hr]; exact r.2
    rw [algebraMap_mem_iff] at hx
    obtain ⟨m, hm⟩ := exists_int_of_valuation hπ n i hx
    exact ⟨m, by simpa using hm⟩
  have := hUW
  refine isIntegral_of_exists_lift ℤ
    (key 1 W₁.a₁ _ ?_ ⟨_, integralModel_a₁_eq 𝕆 ((S • W₁.baseChange ℚ).baseChange 𝕂)⟩)
    (key 2 W₁.a₂ _ ?_ ⟨_, integralModel_a₂_eq 𝕆 ((S • W₁.baseChange ℚ).baseChange 𝕂)⟩)
    (key 3 W₁.a₃ _ ?_ ⟨_, integralModel_a₃_eq 𝕆 ((S • W₁.baseChange ℚ).baseChange 𝕂)⟩)
    (key 4 W₁.a₄ _ ?_ ⟨_, integralModel_a₄_eq 𝕆 ((S • W₁.baseChange ℚ).baseChange 𝕂)⟩)
    (key 6 W₁.a₆ _ ?_ ⟨_, integralModel_a₆_eq 𝕆 ((S • W₁.baseChange ℚ).baseChange 𝕂)⟩) <;>
  simp [S, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, baseChange]

end Place



/-! ## Global descent -/

private theorem exists_integral (E : WeierstrassCurve ℚ) :
    ∃ U : VariableChange ℚ, IsIntegral ℤ (U • E) := by
  obtain ⟨d, hd_def⟩ : ∃ d : ℕ, d = E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den :=
    ⟨_, rfl⟩
  have hd : (d : ℚ) ≠ 0 := by simp [hd_def]
  have hint : ∀ (x : ℚ) (j : ℕ), x.den ∣ d →
      ∃ m : ℤ, algebraMap ℤ ℚ m = (d : ℚ) ^ (j + 1) * x := by
    rintro x j ⟨c, hc⟩
    refine ⟨(d : ℤ) ^ j * c * x.num, ?_⟩
    rw [algebraMap_int_eq, eq_intCast]
    push_cast
    rw [← Rat.mul_den_eq_num, hc]
    push_cast
    ring
  let U : VariableChange ℚ := ⟨Units.mk0 (d : ℚ)⁻¹ (inv_ne_zero hd), 0, 0, 0⟩
  have d1 : E.a₁.den ∣ d := hd_def ▸ dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _) _
  have d2 : E.a₂.den ∣ d := hd_def ▸ dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) _
  have d3 : E.a₃.den ∣ d := hd_def ▸ dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  have d4 : E.a₄.den ∣ d := hd_def ▸ dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have d6 : E.a₆.den ∣ d := hd_def ▸ dvd_mul_left _ _
  refine ⟨U, isIntegral_of_exists_lift ℤ ?_ ?_ ?_ ?_ ?_⟩
  · obtain ⟨m, hm⟩ := hint E.a₁ 0 d1
    exact ⟨m, by rw [hm]; simp [U, variableChange_a₁]⟩
  · obtain ⟨m, hm⟩ := hint E.a₂ 1 d2
    exact ⟨m, by rw [hm]; simp [U, variableChange_a₂]⟩
  · obtain ⟨m, hm⟩ := hint E.a₃ 2 d3
    exact ⟨m, by rw [hm]; simp [U, variableChange_a₃]⟩
  · obtain ⟨m, hm⟩ := hint E.a₄ 3 d4
    exact ⟨m, by rw [hm]; simp [U, variableChange_a₄]⟩
  · obtain ⟨m, hm⟩ := hint E.a₆ 5 d6
    exact ⟨m, by rw [hm]; simp [U, variableChange_a₆]⟩

private theorem exists_int_Δ {X : WeierstrassCurve ℚ} (hX : IsIntegral ℤ X) :
    ∃ δ : ℤ, (δ : ℚ) = X.Δ := by
  have := hX
  obtain ⟨δ, h⟩ := Δ_integral_of_isIntegral ℤ X
  exact ⟨δ, by simpa using h⟩

end ZInQ.Manuscript.GlobalMinimalAux

namespace ZInQ.Manuscript.RankModel

open ZInQ.Manuscript.GlobalMinimalAux in
/-- Every elliptic curve over `ℚ` has a global minimal Weierstrass model
(Silverman, AEC VIII.8.3, for `K = ℚ`). -/
theorem globalMinimalModelsQ : GlobalMinimalModelsQ := by
  intro E hE
  classical
  have hex : ∃ n : ℕ, ∃ U : VariableChange ℚ, IsIntegral ℤ (U • E) ∧
      ∃ δ : ℤ, (δ : ℚ) = (U • E).Δ ∧ δ.natAbs = n := by
    obtain ⟨U, hU⟩ := exists_integral E
    obtain ⟨δ, hδ⟩ := exists_int_Δ hU
    exact ⟨_, U, hU, δ, hδ, rfl⟩
  obtain ⟨U, hU, δ, hδ, hδn⟩ := Nat.find_spec hex
  refine ⟨U, hU, fun p => ?_⟩
  by_contra hmin
  obtain ⟨π, hπ⟩ := exists_generator p
  obtain ⟨U', hU'u, hU'⟩ := local_improve hπ (U • E) hU hmin
  rw [← mul_smul] at hU'
  obtain ⟨δ', hδ'⟩ := exists_int_Δ hU'
  have hle := Nat.find_min' hex ⟨U' * U, hU', δ', hδ', rfl⟩
  rw [← hδn] at hle
  have hπ0 := gen_ne_zero' hπ
  have hrel : (δ : ℚ) = (π : ℚ) ^ 12 * δ' := by
    rw [hδ', hδ, mul_smul, variableChange_Δ (U • E) U', Units.val_inv_eq_inv_val, hU'u,
      ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hπ0, one_pow, one_mul]
  have hrel' : δ = π ^ 12 * δ' := by exact_mod_cast hrel
  have := hE
  have hδ0 : δ ≠ 0 := by
    intro h0
    have hne : (U • E).Δ ≠ 0 := (U • E).isUnit_Δ.ne_zero
    rw [← hδ, h0, Int.cast_zero] at hne
    exact hne rfl
  have h2 := two_le_natAbs hπ
  have habs : δ.natAbs = π.natAbs ^ 12 * δ'.natAbs := by
    rw [hrel', Int.natAbs_mul, Int.natAbs_pow]
  have hδ'0 : δ'.natAbs ≠ 0 := by
    intro h
    rw [h, mul_zero] at habs
    exact hδ0 (Int.natAbs_eq_zero.mp habs)
  have hpow : 2 ^ 12 ≤ π.natAbs ^ 12 := Nat.pow_le_pow_left h2 12
  have h1 : 1 ≤ δ'.natAbs := Nat.one_le_iff_ne_zero.mpr hδ'0
  nlinarith

end ZInQ.Manuscript.RankModel
